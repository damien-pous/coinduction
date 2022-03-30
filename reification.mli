val apply :
  [ `Accumulate of EConstr.t * Names.Id.t
  | `By_symmetry
  | `Coinduction ] ->
  Proofview.Goal.t -> unit Proofview.tactic

val find_candidate :
  Proofview.Goal.t -> unit Proofview.tactic
