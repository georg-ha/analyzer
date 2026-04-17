open Batteries
open GoblintCil
open Analyses
open GobConfig

(* Defined similarly to IntDomain.BISet but with top and other helper functions *)
module IntTopSet = 
struct
  module IntTopName: SetDomain.ToppedSetNames = 
  struct
    let topname = "IntTop"
  end

  include SetDomain.ToppedSet (IntOps.BigIntOps) (IntTopName)

  let get_set man v = 
    let lval_for v =
      match v.vtype with
      | TPtr _ -> (Mem (Lval (Var v, NoOffset)), NoOffset)
      | _ -> (Var v, NoOffset)
    in
    let of_opt_list = function
      | None -> bot ()
      | Some l -> of_list l
    in
    match man.ask (Queries.EvalInt (Lval(lval_for v))) with 
    | `Bot -> bot ()
    | `Top -> top ()
    | `Lifted(x) -> of_opt_list @@ IntDomain.IntDomTuple.to_incl_list x
end

module Variables =
struct
  include CilType.Varinfo
  let show x =
    if RichVarinfo.BiVarinfoMap.Collection.mem_varinfo x then
      let description = RichVarinfo.BiVarinfoMap.Collection.describe_varinfo x in
      "(" ^ x.vname ^ ", " ^ description ^ ")"
    else x.vname
  let pretty () x = Pretty.text (show x)
  type group = Global | Local | Parameter | Temp [@@deriving ord, show { with_path = false }]
  let to_group = function
    | x when x.vglob -> Global
    | x when x.vdecl.line = -1 -> Temp
    | x when Cilfacade.is_varinfo_formal x -> Parameter
    | _ -> Local
  let name () = "variables"
  let printXml f x = BatPrintf.fprintf f "<value>\n<data>\n%s\n</data>\n</value>\n" (XmlUtil.escape (show x))
end

module EnumVarMap = MapDomain.MapBot (Variables) (IntTopSet)

let has_enum_type v =
  let rec aux = function
    | TEnum _ -> true
    | TNamed( x, _ )-> aux x.ttype
    | TPtr(x, _) -> aux x
    | _ ->  false 
  in aux v.vtype

let get_fundec = function
  | MyCFG.Statement s -> Cilfacade.find_stmt_fundec s
  | MyCFG.Function f | MyCFG.FunctionEntry f -> f


let get_enum_vars fdec = 
  let get_globals ()=  
    let file = !Cilfacade.current_file in
    List.filter_map (function
        | GVar (v, _, _) | GVarDecl (v, _) -> Some v
        | _ -> None
      ) file.globals  
  in
  fdec.sformals @ fdec.slocals @ (get_globals ()) 
  |> List.filter has_enum_type

(* __attribute__((annotate("enum-sensitive"))) *)
let is_annotated v = 
  let is_enum_sensitive_attribute (Attr(name, params)) = 
    name = "annotate" && 
    (List.exists (fun p -> match p with 
         | AStr(n) -> n = "enum-sensitive"
         | _ -> false) params)
  in List.exists is_enum_sensitive_attribute v.vattr

module type TargetSelection = sig
  val get: fundec -> varinfo list
end

module AnnotatedOnly: TargetSelection = struct
  let get fdec = List.filter is_annotated (get_enum_vars fdec)
end

module ExhaustiveSelection : TargetSelection = struct
  let get fdec = 
    let vars = get_enum_vars fdec in
    let annotated_vars = List.filter is_annotated vars in 
    if (not @@ List.is_empty annotated_vars) then 
      annotated_vars 
    else
      vars
end

module DefaultSelection : TargetSelection = struct
  module VSet = Set.Make(CilType.Varinfo)

  class varCollector (found: varinfo list ref) = object
    inherit nopCilVisitor
    method! vlval lval =
      (match lval with
       | (Var v, _) when has_enum_type v -> found := v :: !found
       | _ -> ());
      DoChildren
  end

  let get fdec =
    let mentioned = ref VSet.empty in

    (* Helper to run the visitor on an expression and collect results *)
    let collect_from_expr exp =
      let found = ref [] in
      ignore (visitCilExpr (new varCollector found) exp);
      List.iter (fun v -> mentioned := VSet.add v !mentioned) !found
    in

    List.iter (fun stmt ->
        match stmt.skind with
        | If (cond, _, _, _, _) ->
          collect_from_expr cond
        (* Collect from function call arguments *)
        | Instr instrs ->
          List.iter (fun instr ->
              match instr with
              | Call (_, _, args, _, _) ->
                List.iter collect_from_expr args
              | _ -> ()
            ) instrs
        | _ -> ()
      ) fdec.sallstmts;

    let result = VSet.elements !mentioned in
    result
end

module Cached (Selection: TargetSelection) : TargetSelection = struct
  (* Use the functions svar.vid as keys. Using the fundec itself causes memory errors *)
  let cache: (int, varinfo list) Hashtbl.t = Hashtbl.create 5

  let get fdec =
    let key = fdec.svar.vid in
    match Hashtbl.find_opt cache key with 
    | Some l -> l
    | None -> 
      let l = Selection.get fdec in
      Hashtbl.add cache key l;
      Printf.printf "For %s: Found %d vars\n%!" fdec.svar.vname (List.length l);
      l
end

let get_strategy () : (module TargetSelection) =
  let m: (module TargetSelection) = match get_string "ana.enum_sens.strategy" with 
    | "exhaustive" -> (module ExhaustiveSelection)
    | "annotated_only" -> (module AnnotatedOnly)
    | "default" -> (module DefaultSelection)
    | _ -> assert false
  in if get_bool "ana.enum_sens.cache" then
    let module M = (val m: TargetSelection) in
    (module Cached(M))
  else m


module M (Spec: Spec)
  : Spec
    with module G = Spec.G
     and module C = Spec.C
     and module V = Spec.V
= struct
  module G = Spec.G
  module C = Spec.C
  module V = Spec.V
  module P = UnitP


  module D = struct
    module E = Lattice.Prod (EnumVarMap) (Spec.D)
    module J = SetDomain.Joined (E)

    module R = struct
      include EnumVarMap

      type elt = E.t

      let of_elt ((m, _): elt) = m
    end

    include DisjointDomain.ProjectiveSet (E) (J) (R)

    let name () = "ValueSensitive"

    let printXml f x =
      let print_one (s, x) =
        BatPrintf.fprintf f "\n<path>%a%a</path>" 
          EnumVarMap.printXml s
          Spec.D.printXml x
      in
      iter print_one x
  end

  module Targets = (val get_strategy ())

  let name () = "ValueSensitive2("^Spec.name ()^")"
  let get_mappings man = 
    let vars = Targets.get (get_fundec man.node) in
    EnumVarMap.empty ()
    |> EnumVarMap.add_list (List.map (fun v -> v, (IntTopSet.get_set man v)) vars)

  let convert man (s, x) =
    let rec man' = { man with ask   = (fun (type a) (q: a Queries.t) -> Spec.query man' q)
                            ; local = x
                            ; split = (man.split % (fun x -> D.singleton (s, x))) }
    in
    man'

  let equal_except_targets man vars (m1, x1) (m2, x2) =
    let same_keys =
      List.for_all (fun v ->
          match EnumVarMap.find_opt v m1, EnumVarMap.find_opt v m2 with
          | None, None | Some _, Some _ -> true
          | _ -> false   
        ) vars
    in if not same_keys then false
    else
      let erase x m =
        List.fold_left (fun acc_x v ->
            let tmp = Cil.makeVarinfo false "valsens2_typ" 
                (match v.vtype with TPtr(t,_) | t -> t)
            in
            let lval = match v.vtype with
              | TPtr _ -> (Mem (Lval (Var v, NoOffset)), NoOffset)
              | _      -> (Var v, NoOffset)
            in
            let man' = convert man (m, acc_x) in
            Spec.assign man' lval (Lval (Var tmp, NoOffset))
          ) x vars
      in
      if Spec.D.equal (erase x1 m1) (erase x2 m2) then true else false

  let map man f g =
    let vars = Targets.get (get_fundec man.node) in
    let h (m, x) xs =
      try
        let man' = convert man (m, x) in
        let x' = g (f man') in
        let m' = 
          let queried = get_mappings (convert man (m, x')) in
          List.fold_left (fun acc v ->
              match EnumVarMap.find_opt v queried with
              | Some s when not (IntTopSet.is_bot s) && not (IntTopSet.is_top s) ->
                EnumVarMap.add v s acc
              | _ ->
                acc
            ) m vars
        in
        let new_el = (m', x') in

        let exception Found of (EnumVarMap.t * Spec.D.t) in
        let match_opt =
          try
            D.fold (fun old_el _ ->
                if equal_except_targets man vars new_el old_el then
                  raise (Found old_el)
              ) xs ();
            None
          with Found old_el ->
            Some old_el
        in
        match match_opt with
        | Some ((old_m, old_x) as old_el) ->
          let xs_removed = D.remove old_el xs in
          let joined_m = EnumVarMap.join m' old_m in
          let joined_x = Spec.D.join x' old_x in
          D.add (joined_m, joined_x) xs_removed
        | None ->
          D.add new_el xs

      with Deadcode -> xs
    in
    let d = D.fold h man.local (D.empty ()) in
    if D.is_bot d then raise Deadcode else d

  let fold' man f g h a =
    let k (m, x) a =
      try h a @@ g @@ f @@ convert man (m, x)
      with Deadcode -> a
    in
    D.fold k man.local a

  let context man fd l =
    if D.cardinal l <> 1 then
      failwith "ValueSensitive2.context must be called with a singleton set."
    else
      let (_, x) as el = D.choose l in
      Spec.context (convert man el) fd x

  let query man (type a) (q: a Queries.t) : a Queries.result =
    let module Result = (val Queries.Result.lattice q) in
    fold' man Spec.query identity (fun x f -> Result.join x (f q)) (Result.bot ())

  type marshal = Spec.marshal
  let init = Spec.init
  let finalize = Spec.finalize

  let startcontext () = Spec.startcontext ()
  let startstate v = D.singleton (EnumVarMap.empty (), Spec.startstate v)
  let morphstate v d = D.map (fun (m, x) -> m, Spec.morphstate v x) d
  let exitstate v = D.singleton (EnumVarMap.empty (), Spec.exitstate v)

  let assign man l e    = map man Spec.assign  (fun h -> h l e)
  let vdecl man v       = map man Spec.vdecl   (fun h -> h v)
  let body   man f      = map man Spec.body    (fun h -> h f)
  let return man e f    = map man Spec.return  (fun h -> h e f)
  let branch man e tv   = map man Spec.branch  (fun h -> h e tv)
  let asm man           = map man Spec.asm     identity
  let skip man          = map man Spec.skip    identity
  let special man l f a = map man Spec.special (fun h -> h l f a)
  let sync man reason   = map man Spec.sync    (fun h -> h reason)

  let event man e oman =
    let (m, fd1) = D.choose oman.local in
    map man Spec.event (fun h -> h e (convert oman (m, fd1)))

  let threadenter man ~multiple lval f args =
    let g xs ys = (List.map (fun y -> D.singleton (EnumVarMap.empty (), y)) ys) @ xs in
    fold' man (Spec.threadenter ~multiple) (fun h -> h lval f args) g []

  let threadspawn man ~multiple lval f args fman =
    let fd1 = D.choose fman.local in
    map man (Spec.threadspawn ~multiple) (fun h -> h lval f args (convert fman fd1))

  let enter man l f a =
    let g xs ys = (List.map (fun (x, y) -> D.singleton (EnumVarMap.empty (), x), D.singleton (EnumVarMap.empty (), y)) ys) @ xs in
    fold' man Spec.enter (fun h -> h l f a) g []

  let paths_as_set man =
    D.elements man.local 
    |> List.map D.singleton

  let combine_env man l fe f a fc d f_ask =
    assert (D.cardinal man.local = 1);
    let (m, cd) = D.choose man.local in
    let k (callee_m, x) y =
      try
        let r = Spec.combine_env (convert man (m, cd)) l fe f a fc x f_ask in
        (* Recompute the enum map from the combined result state,
           but also bring in callee's enum knowledge *)
        let merged_m = EnumVarMap.join m callee_m in
        D.add (merged_m, r) y
      with Deadcode -> y
    in
    let d = D.fold k d (D.bot ()) in
    if D.is_bot d then raise Deadcode else d

  let combine_assign man l fe f a fc d f_ask =
    assert (D.cardinal man.local = 1);
    let (m, cd) = D.choose man.local in
    let k (callee_m, x) y =
      try
        let r = Spec.combine_assign (convert man (m, cd)) l fe f a fc x f_ask in
        let merged_m = EnumVarMap.join m callee_m in
        D.add (merged_m, r) y
      with Deadcode -> y
    in
    let d = D.fold k d (D.bot ()) in
    if D.is_bot d then raise Deadcode else d
end
