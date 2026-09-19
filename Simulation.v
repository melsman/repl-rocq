From Stdlib Require Import List.
From Repl Require Import Names.
Import ListNotations.

Section Models.
Context {SB DB Store CB Heap Decl Value : Type}.
Variable addS : SB -> SB -> SB.
Variable addD : DB -> DB -> DB.
(* commit opens the jointly bound compilation-basis contribution at base b,
   then implements C + C'. The code is opened at that same b. *)
Variable contribution : Type.
Variable commit : CB -> contribution -> nat -> CB.
Record source := Src { static : SB; dynamic : DB; store : Store }.
Record target := Tgt { basis : CB; loaded : list nat; heap : Heap }.
Inductive outcome := Rejected | Returned | Raised (v : Value).
Inductive result := Normal (delta : DB) | Exception (v : Value).
Variable elaborate : SB -> Decl -> option SB -> Prop.
Variable evaluate : DB -> Store -> Decl -> result -> Store -> Prop.
Variable compile : CB -> Decl -> option (contribution * object) -> Prop.
Variable execute : object -> nat -> list nat -> Heap -> outcome -> Heap -> Prop.

(* An opened declaration package. None is the empty basis contribution;
   Some contains both contributions. Existential type-name opening remains
   abstract in elaborate, as before; no runtime symbol names are used here. *)
Record declaration_result := DeclResult {
  delta : option (SB * DB);
  reported : outcome;
  resulting_store : Store
}.

Inductive process : source -> Decl -> declaration_result -> Prop :=
| PReject : forall bs bd s d, elaborate bs d None ->
    process (Src bs bd s) d (DeclResult None Rejected s)
| PNormal : forall bs bd s d bs' bd' s',
    elaborate bs d (Some bs') -> evaluate bd s d (Normal bd') s' ->
    process (Src bs bd s) d (DeclResult (Some (bs',bd')) Returned s')
| PException : forall bs bd s d bs' v s',
    elaborate bs d (Some bs') -> evaluate bd s d (Exception v) s' ->
    process (Src bs bd s) d (DeclResult None (Raised v) s').

Definition apply_result (q : source) (p : declaration_result) : source :=
  match delta p with
  | None => Src (static q) (dynamic q) (resulting_store p)
  | Some (bs',bd') =>
      Src (addS (static q) bs') (addD (dynamic q) bd') (resulting_store p)
  end.

Inductive interpret : source -> Decl -> outcome -> source -> Prop :=
| IApply : forall q d p, process q d p ->
    interpret q d (reported p) (apply_result q p).

Lemma rejection_result : forall q d p, process q d p ->
  reported p = Rejected -> delta p = None /\ resulting_store p = store q.
Proof. intros q d p HP. destruct HP; simpl; intros Hout; try discriminate; auto. Qed.

Lemma exception_result : forall q d p v, process q d p ->
  reported p = Raised v -> delta p = None /\
    static (apply_result q p) = static q /\
    dynamic (apply_result q p) = dynamic q.
Proof. intros q d p v HP. destruct HP; simpl; intros Hout; try discriminate; auto. Qed.

Inductive compiled : target -> Decl -> outcome -> target -> Prop :=
| CReject : forall c ns h d, compile c d None ->
    compiled (Tgt c ns h) d Rejected (Tgt c ns h)
| CNormal : forall c ns h d c' o ns' h',
    compile c d (Some (c',o)) -> links ns o ns' ->
    execute o (fresh ns) ns' h Returned h' ->
    compiled (Tgt c ns h) d Returned (Tgt (commit c c' (fresh ns)) ns' h')
| CException : forall c ns h d c' o ns' v h',
    compile c d (Some (c',o)) -> links ns o ns' ->
    execute o (fresh ns) ns' h (Raised v) h' ->
    compiled (Tgt c ns h) d (Raised v) (Tgt c ns' h').

Theorem compiled_preserves_names : forall k d a k',
  compiled k d a k' -> NoDup (loaded k) -> NoDup (loaded k').
Proof.
  intros k d a k' H. destruct H; simpl; intros Hn; try assumption;
    eapply link_safety; eassumption.
Qed.

(* Semantic validity of a FIXED compilation result, in every realisation
   of its input basis. It is independent of the compilation relation. *)
Variable represents : source -> target -> Prop.
Definition correct_result (c : CB) (d : Decl) (c' : contribution) (o : object) :=
  forall bs bd s ns h, represents (Src bs bd s) (Tgt c ns h) ->
  wf ns o /\
  (forall bs' bd' s',
    elaborate bs d (Some bs') -> evaluate bd s d (Normal bd') s' ->
    exists h', execute o (fresh ns) (extend ns o) h Returned h' /\
      represents (Src (addS bs bs') (addD bd bd') s')
        (Tgt (commit c c' (fresh ns)) (extend ns o) h')) /\
  (forall bs' v s',
    elaborate bs d (Some bs') -> evaluate bd s d (Exception v) s' ->
    exists h', execute o (fresh ns) (extend ns o) h (Raised v) h' /\
      represents (Src bs bd s') (Tgt c (extend ns o) h')).

(* The declaration-level compiler correctness theorem to instantiate. *)
Hypothesis compiler_correct : forall c d c' o,
  compile c d (Some (c',o)) -> correct_result c d c' o.

(* Existence is a separate, static obligation; it does not quantify over
   heaps or assume that evaluation terminates. *)
Variable static_agrees : CB -> SB -> Prop.
Hypothesis represents_static : forall bs bd s c ns h,
  represents (Src bs bd s) (Tgt c ns h) -> static_agrees c bs.
Hypothesis compilation_exists : forall c bs d bs',
  static_agrees c bs -> elaborate bs d (Some bs') ->
  exists c' o, compile c d (Some (c',o)).
Hypothesis rejection_correct : forall c bs d,
  static_agrees c bs -> elaborate bs d None -> compile c d None.

Theorem compiled_result_links : forall bs bd s c ns h d c' o,
  represents (Src bs bd s) (Tgt c ns h) ->
  compile c d (Some (c',o)) -> NoDup ns ->
  links ns o (extend ns o) /\ NoDup (extend ns o).
Proof.
  intros bs bd s c ns h d c' o HR HC HN.
  destruct (compiler_correct c d c' o HC bs bd s ns h HR) as [HW _].
  split; [apply link_progress; exact HW|apply no_duplicate_names; exact HN].
Qed.

Lemma compilation_total : forall bs bd s c ns h d bs',
  represents (Src bs bd s) (Tgt c ns h) ->
  elaborate bs d (Some bs') ->
  exists c' o, compile c d (Some (c',o)) /\ wf ns o.
Proof.
  intros bs bd s c ns h d bs' HR HE.
  assert (HA : static_agrees c bs) by (eapply represents_static; exact HR).
  destruct (compilation_exists c bs d bs' HA HE) as [c' [o HC]].
  exists c', o. split; [exact HC|].
  exact (proj1 (compiler_correct c d c' o HC bs bd s ns h HR)).
Qed.

Lemma normal_correct : forall bs bd s c ns h d bs' bd' s' c' o,
  represents (Src bs bd s) (Tgt c ns h) ->
  elaborate bs d (Some bs') -> evaluate bd s d (Normal bd') s' ->
  compile c d (Some (c',o)) -> wf ns o ->
  exists h', execute o (fresh ns) (extend ns o) h Returned h' /\
    represents (Src (addS bs bs') (addD bd bd') s')
      (Tgt (commit c c' (fresh ns)) (extend ns o) h').
Proof.
  intros bs bd s c ns h d bs' bd' s' c' o HR HE HV HC HW.
  destruct (compiler_correct c d c' o HC bs bd s ns h HR) as [_ [HN _]].
  exact (HN bs' bd' s' HE HV).
Qed.
Lemma exception_correct : forall bs bd s c ns h d bs' v s' c' o,
  represents (Src bs bd s) (Tgt c ns h) ->
  elaborate bs d (Some bs') -> evaluate bd s d (Exception v) s' ->
  compile c d (Some (c',o)) -> wf ns o ->
  exists h', execute o (fresh ns) (extend ns o) h (Raised v) h' /\
    represents (Src bs bd s') (Tgt c (extend ns o) h').

Proof.
  intros bs bd s c ns h d bs' v s' c' o HR HE HV HC HW.
  destruct (compiler_correct c d c' o HC bs bd s ns h HR) as [_ [_ HX]].
  exact (HX bs' v s' HE HV).
Qed.

Theorem declaration_simulation : forall q d p, process q d p ->
  forall k, represents q k -> NoDup (loaded k) ->
  exists k', compiled k d (reported p) k' /\
    represents (apply_result q p) k' /\ NoDup (loaded k').
Proof.
  intros q d p HP. destruct HP; intros [c ns h] HR Hnames; simpl.
  - exists (Tgt c ns h). split.
    + constructor. eapply rejection_correct; [eapply represents_static; exact HR|exact H].
    + split; assumption.
  - destruct (compilation_total _ _ _ _ _ _ _ _ HR H) as [c' [o [HC HW]]].
    destruct (normal_correct _ _ _ _ _ _ _ _ _ _ _ _ HR H H0 HC HW) as [h' [HE HR']].
    eexists. split.
    + eapply CNormal; [exact HC|apply link_progress; exact HW|exact HE].
    + split; [exact HR'|simpl; apply no_duplicate_names; exact Hnames].
  - destruct (compilation_total _ _ _ _ _ _ _ _ HR H) as [c' [o [HC HW]]].
    destruct (exception_correct _ _ _ _ _ _ _ _ _ _ _ _ HR H H0 HC HW) as [h' [HE HR']].
    eexists. split.
    + eapply CException; [exact HC|apply link_progress; exact HW|exact HE].
    + split; [exact HR'|simpl; apply no_duplicate_names; exact Hnames].
Qed.

Theorem step_simulation : forall q d a q', interpret q d a q' ->
  forall k, represents q k -> NoDup (loaded k) ->
  exists k', compiled k d a k' /\ represents q' k' /\ NoDup (loaded k').
Proof.
  intros q d a q' Hstep. destruct Hstep.
  eapply declaration_simulation; exact H.
Qed.

Inductive session {State : Type} (step : State -> Decl -> outcome -> State -> Prop)
  : State -> list (Decl * outcome) -> State -> Prop :=
| Empty : forall q, session step q [] q
| More : forall q d a q' rest q'', step q d a q' ->
    session step q' rest q'' -> session step q ((d,a)::rest) q''.

Theorem session_simulation : forall q trace q', session interpret q trace q' ->
  forall k, represents q k -> NoDup (loaded k) ->
  exists k', session compiled k trace k' /\ represents q' k' /\ NoDup (loaded k').
Proof.
  intros q trace q' H. induction H; intros k HR HN.
  - exists k. split; [constructor|split; assumption].
  - destruct (step_simulation _ _ _ _ H k HR HN) as [k' [HS [HR' HN']]].
    destruct (IHsession k' HR' HN') as [k'' [HT [HR'' HN'']]].
    exists k''. split; [econstructor; eassumption|split; assumption].
Qed.
End Models.
Print Assumptions session_simulation.
Print Assumptions compiled_preserves_names.

Print Assumptions compiled_result_links.

Print Assumptions declaration_simulation.
