(* cf. documentation in .ml file *)

val apply :
  Names.Id.t ->
  [ `PTower of EConstr.t
  | `By_symmetry ] ->
  Proofview.Goal.t -> unit Proofview.tactic

val abstract :
  (EConstr.t * EConstr.t) option ->
  Proofview.Goal.t -> unit Proofview.tactic
