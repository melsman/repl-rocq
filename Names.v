From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Bound indices stand for the names existentially bound over an object
   and its compilation-basis contribution. External names remain rigid. *)
Inductive reference := External (name : nat) | Bound (index : nat).
Record object := { count : nat; refs : list reference }.
Definition wf (ns : list nat) (o : object) :=
  Forall (fun r => match r with External n => In n ns
                             | Bound i => i < count o end) (refs o).
Definition fresh (ns : list nat) := S (fold_right Nat.max 0 ns).
Definition open_ref b r := match r with External n => n | Bound i => b+i end.
Definition exports b o := seq b (count o).
Definition extend ns o := ns ++ exports (fresh ns) o.

Lemma below_fresh : forall ns n, In n ns -> n < fresh ns.
Proof.
  intros ns n H. unfold fresh.
  assert (n <= fold_right Nat.max 0 ns).
  { induction ns as [|x ns IH]; simpl in *; [contradiction|].
    destruct H as [<-|H]; [apply Nat.le_max_l|].
    specialize (IH H). eapply Nat.le_trans; [exact IH|apply Nat.le_max_r]. }
  lia.
Qed.
Lemma exports_fresh : forall ns o n,
  In n (exports (fresh ns) o) -> ~ In n ns.
Proof.
  intros ns o n H Hn. unfold exports in H. apply in_seq in H.
  pose proof (below_fresh ns n Hn). lia.
Qed.
Lemma nodup_app : forall (xs ys : list nat),
  NoDup xs -> NoDup ys ->
  (forall n, In n xs -> ~ In n ys) -> NoDup (xs ++ ys).
Proof.
  intros xs ys Hx Hy Hd. induction Hx; simpl; [exact Hy|].
  constructor.
  - intro Hn. apply in_app_or in Hn. destruct Hn as [Hn|Hn].
    + contradiction.
    + eapply (Hd x); [left; reflexivity|exact Hn].
  - apply IHHx. intros n Hn. apply Hd. right; exact Hn.
Qed.
Theorem no_duplicate_names : forall ns o,
  NoDup ns -> NoDup (extend ns o).
Proof.
  intros ns o H. unfold extend. apply nodup_app.
  - exact H.
  - apply seq_NoDup.
  - intros n Hn Hnew. exact (exports_fresh ns o n Hnew Hn).
Qed.
Theorem resolution : forall ns o, wf ns o ->
  Forall (fun r => In (open_ref (fresh ns) r) (extend ns o)) (refs o).
Proof.
  intros ns o H. unfold wf in H. apply Forall_forall. intros r Hin. rewrite Forall_forall in H. specialize (H r Hin).
  rename H into Hr.
  destruct r as [n|i]; simpl in *; unfold extend; apply in_or_app.
  - left; exact Hr.
  - right. unfold exports. apply in_seq. unfold fresh. lia.
Qed.
Inductive links ns o : list nat -> Prop :=
| Link : (forall n, In n (exports (fresh ns) o) -> ~ In n ns) ->
    NoDup (exports (fresh ns) o) ->
    Forall (fun r => In (open_ref (fresh ns) r) (extend ns o)) (refs o) ->
    links ns o (extend ns o).
Theorem link_progress : forall ns o, wf ns o -> links ns o (extend ns o).
Proof. intros. constructor; [apply exports_fresh|apply seq_NoDup|apply resolution; assumption]. Qed.
Theorem link_safety : forall ns o ns',
  NoDup ns -> links ns o ns' -> NoDup ns'.
Proof. intros ns o ns' H Hl. inversion Hl; subst. apply no_duplicate_names; assumption. Qed.

(* Capture-free change of opening: both bases are above all external names. *)
Definition rename b b' n := if n <? b then n else b' + (n-b).
Theorem alpha_open : forall ns o b b', wf ns o ->
  (forall n, In n ns -> n < b) ->
  map (fun r => rename b b' (open_ref b r)) (refs o) =
  map (open_ref b') (refs o).
Proof.
  intros ns o b b' Hwf Hb. unfold wf in Hwf. apply map_ext_in. intros [n|i] Hr.
  - rewrite Forall_forall in Hwf. specialize (Hwf (External n) Hr).
    simpl in Hwf. unfold open_ref, rename.
    assert ((n <? b) = true) by (apply Nat.ltb_lt; apply Hb; assumption).
    rewrite H. reflexivity.
  - unfold open_ref, rename.
    assert ((b+i <? b) = false) by (apply Nat.ltb_ge; lia).
    rewrite H. f_equal. lia.
Qed.
