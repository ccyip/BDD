From stdpp Require Import prelude fin_maps natmap.
From Hammer Require Import Tactics.

(** * Ite expression *)

Inductive Ite : Set :=
| var : nat -> Ite
| lit : bool -> Ite
| ite : Ite -> Ite -> Ite -> Ite
.

Coercion var : nat >-> Ite.
Coercion lit : bool >-> Ite.

Instance Ite_eq : EqDecision Ite.
solve_decision.
Defined.

(** * Specification of Normalization *)

Inductive norm : Ite -> Prop :=
| NVar x : norm (var x)
| NLit l : norm (lit l)
| NIte x a b :
  norm a ->
  norm b ->
  a <> b ->
  norm (ite (var x) a b)
.

Fixpoint interp (m : nat -> bool) (e : Ite) : bool :=
  match e with
  | var x => m x
  | lit b => b
  | ite c a b =>
      if interp m c
      then interp m a
      else interp m b
  end.

(** * Normalization Procedure *)
(** Assume [c], [a] and [b] are in normal form. *)
Fixpoint combine (c a b : Ite) : Ite :=
  match c with
  | var x =>
      if decide (a = b)
      then a
      else ite x a b
  | lit l => if l then a else b
  | ite c' a' b' =>
      let a' := combine a' a b in
      let b' := combine b' a b in
      if decide (a' = b')
      then a'
      else ite c' a' b'
  end.

Fixpoint normalize (e : Ite) : Ite :=
  match e with
  | ite c a b =>
      combine (normalize c) (normalize a) (normalize b)
  | _ => e
  end.

(** * Theorems about normalization *)

(** ** Normalization *)

Lemma combine_normal c a b :
  norm c ->
  norm a ->
  norm b ->
  norm (combine c a b).
Proof.
  induction 1; intros; simpl; try case_split; auto using norm.
Qed.

Theorem normalize_normal e :
  norm (normalize e).
Proof.
  induction e; simpl; auto using norm, combine_normal.
Qed.

(** ** Correctness *)

Lemma combine_correctness m c a b :
  norm c ->
  interp m (combine c a b) = if interp m c
                             then interp m a
                             else interp m b.
Proof.
  induction 1; simpl;
    try case_decide; subst; auto;
    hauto.
Qed.

Theorem correctness m e :
  interp m (normalize e) = interp m e.
Proof.
  induction e; simpl; auto.
  rewrite combine_correctness by auto using normalize_normal.
  qauto.
Qed.

(** * Specification of Simplification *)

(** Assume everything is in normal form from now on. *)

Inductive not_appear_in : nat -> Ite -> Prop :=
| AVar x y : x <> y -> not_appear_in x (var y)
| ALit b x : not_appear_in x (lit b)
| AIte y a b x :
  x <> y ->
  not_appear_in x a ->
  not_appear_in x b ->
  not_appear_in x (ite (var y) a b)
.

Inductive simplified : Ite -> Prop :=
| SVar x : simplified (var x)
| SLit l : simplified (lit l)
| SIte x a b :
  not_appear_in x a ->
  not_appear_in x b ->
  simplified (ite (var x) a b)
.

(** * Simplification Procedure *)

Fixpoint simplify_ (m : natmap bool) (e : Ite) : Ite :=
  match e with
  | var x =>
      match m !! x with
      | Some b => lit b
      | None => var x
      end
  | lit l => lit l
  | ite (var x) a b =>
      match m !! x with
      | Some true => simplify_ m a
      | Some false => simplify_ m b
      | None =>
          let a' := simplify_ (<[x:=true]>m) a in
          let b' := simplify_ (<[x:=false]>m) b in
          if decide (a' = b')
          then a'
          else ite (var x) a' b'
      end
  (* Bogus *)
  | _ => false
  end.

Definition simplify := simplify_ ∅.

(** * Theorems about Simplification *)

(** ** Simplification *)

Lemma simplify_not_appear m e x b :
  norm e ->
  not_appear_in x (simplify_ (<[x:=b]>m) e).
Proof.
  intros H. revert m x b.
  induction H; intros; simpl; auto using not_appear_in.
  - case_split; auto using not_appear_in.
    select (_ !! _ = _) (fun H => apply lookup_insert_None in H).
    qauto ctrs: not_appear_in.
  - case_split. qauto.
    select (_ !! _ = _) (fun H => apply lookup_insert_None in H).
    simp_hyps.
    case_decide.
    by rewrite insert_commute by auto.
    econstructor; auto;
      by rewrite insert_commute by auto.
Qed.

Lemma simplify_simplified_ m e :
  norm e ->
  simplified (simplify_ m e).
Proof.
  intros H. revert m.
  induction H; intros; simpl; auto using simplified.
  qauto ctrs: simplified.
  case_split; try qauto.
  case_decide; auto using simplified, simplify_not_appear.
Qed.

Theorem simplify_simplified e :
  norm e ->
  simplified (simplify e).
Proof.
  eauto using simplify_simplified_.
Qed.

(** ** Normalization *)

Lemma simplify_norm_ m e :
  norm e ->
  norm (simplify_ m e).
Proof.
  intros H. revert m.
  induction H; intros; simpl; auto using norm.
  qauto ctrs: norm.
  case_split. qauto.
  case_decide; auto.
  econstructor; eauto.
Qed.

Theorem simplify_norm e :
  norm e ->
  norm (simplify e).
Proof.
  eauto using simplify_norm_.
Qed.

(** ** Correctness *)

Definition consistent (m : nat -> bool) (p : natmap bool) :=
  forall x b, p !! x = Some b -> m x = b.

Lemma insert_consistent m p x' b' :
  consistent m p ->
  m x' = b' ->
  consistent m (<[x':=b']>p).
Proof.
  intros; subst.
  hnf. intros.
  select (_ !! _ = Some _)
           (fun H => eapply lookup_insert_Some in H);
    intuition eauto.
Qed.

Lemma empty_consistent m :
  consistent m ∅.
Proof.
  hnf. intros. simplify_map_eq.
Qed.

Lemma simplify_correct_ m p e :
  norm e ->
  consistent m p ->
  interp m (simplify_ p e) = interp m e.
Proof.
  intros H Hc. revert p Hc.
  induction H; intros; simpl; auto.
  case_split; simpl; qauto unfold: consistent.
  case_split.
  select (_ !! _ = _) (fun H => apply Hc in H). qauto.
  case_decide; simpl;
    (case_match;
     [| try select (simplify_ _ _ = simplify_ _ _)
            (fun H => rewrite H) ]);
    (* Apply induction hypothesis. *)
    match goal with
    | IH : forall _, _ -> interp _ _ = ?e |- _ = ?e =>
        apply IH
    end;
    auto using insert_consistent.
Qed.

Theorem simplify_correct m e :
  norm e ->
  interp m (simplify e) = interp m e.
Proof.
  eauto using simplify_correct_, empty_consistent.
Qed.

(** * Examples *)

Module examples.

Definition m (n : nat) : bool :=
  match n with
  | 1 => false
  | 2 => true
  | 3 => false
  | 4 => true
  | 5 => false
  | 6 => true
  | 7 => false
  | _ => false
  end.

Definition e1 :=
  ite (ite 1 true false) (ite 1 3 4) (ite 5 1 7).

Compute (normalize e1).
Compute simplify (normalize e1).

Compute interp m e1.
Compute interp m (normalize e1).

Definition e2 :=
  ite 1 1 true.

Compute (normalize e2).
Compute simplify (normalize e2).

Compute interp m e2.
Compute interp m (normalize e2).

End examples.
