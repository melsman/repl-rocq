From Stdlib Require Import List.
From Repl Require Import Names.
Import ListNotations.
Definition first := {| count := 1; refs := [Bound 0] |}.
Definition second := {| count := 1; refs := [External 1; Bound 0] |}.
Definition third := {| count := 1; refs := [External 1; Bound 0] |}.
(* Even if second's initialiser raises, its name remains allocated. *)
Example names_after_exception : extend (extend (extend [] first) second) third = [1;2;3].
Proof. reflexivity. Qed.
Example second_well_formed : wf (extend [] first) second.
Proof. repeat constructor. Qed.
Example second_links : links (extend [] first) second [1;2].
Proof. apply link_progress. exact second_well_formed. Qed.
Example session_names_unique :
  NoDup (extend (extend (extend [] first) second) third).
Proof. repeat apply no_duplicate_names. constructor. Qed.
Example opening_changes_only_local_names :
  map (open_ref 2) (refs second) = [1;2] /\
  map (open_ref 3) (refs second) = [1;3].
Proof. split; reflexivity. Qed.
Print Assumptions no_duplicate_names.
Print Assumptions alpha_open.
