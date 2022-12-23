val apply :
  Names.Id.t ->
  [ `PTower of EConstr.t
  | `By_symmetry ] ->
  Proofview.Goal.t -> unit Proofview.tactic
