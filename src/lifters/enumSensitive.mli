open Analyses

module M (Spec : Spec)
  : Spec
    with module G = Spec.G
     and module C = Spec.C
     and module V = Spec.V