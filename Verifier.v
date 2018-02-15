Require Import Bool.
Require Import Program.
Require Import Packages.
Require Import MSetProperties.
Module Import PAux := MSetAux.Aux PackageSet.
Import PackageSet.
Import Package.
Import Facts.
Import Props.
Module CAux := MSetAux.Aux ConflictSet.

(* verifier *)

Inductive install_reason: Type :=
| conflict: list Package.t -> list Package.t -> install_reason
| broken_dependency: list Package.t -> install_reason.

Inductive install_response: Type :=
| affirmatif: PackageSet.t -> install_response
| negatif: install_reason -> install_response.

Parameter install_function: 
  PackageSet.t -> ConflictSet.t -> Package.t -> install_response.

Program Definition check_abundance (R: PackageSet.t)
  (I: PackageSet.t | I [<=] R): bool :=
if (bool_dec (PackageSet.fold (fun p_id v =>
    satisfied_pkg_bool I p_id && v
  ) I true) true) then
  true
else
  false.

Lemma if_bool_dec_true: forall b: bool, Is_true (if (bool_dec b true) then true else false) <-> Is_true b.
Proof.
  intros. elim b. simpl. reflexivity. simpl. reflexivity.
Qed.

Lemma if_bool_dec_false: forall b: bool, Is_true (if (bool_dec b false) then true else false) <-> ~Is_true b.
Proof.
  intros. elim b. simpl. tauto. simpl. tauto.
Qed.

Program Lemma ab: forall R (I: PackageSet.t | I [<=] R), abundant (`I) <-> Is_true (check_abundance R I).
Proof.
  intros. 
  split. intros. 
  unfold check_abundance. rewrite if_bool_dec_true.
  apply Is_true_eq_left. apply <- fold_forall_and. 
  unfold For_all. intros. apply Is_true_eq_true. apply -> spb_ok.
    apply H. apply H0.
  intros. unfold satisfied_pkg_bool. rewrite (Dep_compat_eq a b H0). reflexivity.
  intros.
  assert (For_all (fun x => satisfied_pkg_bool (`I) x = true) (`I)).
  apply -> fold_forall_and. unfold check_abundance in H. 
  rewrite if_bool_dec_true in H. apply Is_true_eq_true. apply H.
  intros. unfold satisfied_pkg_bool. rewrite (Dep_compat_eq a b H0). reflexivity.
  unfold abundant. unfold For_all. intros. apply <- spb_ok.
  apply Is_true_eq_left. apply H0. apply H1.
Qed.

Program Lemma check_abundance_eq: forall (R: PackageSet.t) I I',
  (`I) [=] (`I') -> check_abundance R I = check_abundance R I'.
Proof.
  intros. apply eq_bool_prop_intro. rewrite <- ab. rewrite <- ab.
  split. 
    intros. apply (abundant_eq (`I) (`I') H H0).
    intros. apply (abundant_eq (`I') (`I) (PackageSet.eq_sym H) H0).
Qed.

Program Definition check_peace (C: ConflictSet.t)
  (I: PackageSet.t): bool :=
if (bool_dec (ConflictSet.fold (fun c v =>
   concerned_bool I c || v
) C false) false) then
  true
else
  false.

Lemma negb_true: forall a: bool, negb a = true <-> a = false.
Proof.
  intros. elim a.
    simpl. split. intros. inversion H. intros. inversion H.
    simpl. tauto.
Qed.

Program Lemma pc: forall C I, peaceful I C <-> Is_true (check_peace C I).
Proof.
  intros. split.
  intros. unfold check_peace. rewrite if_bool_dec_false. 
  apply negb_prop_elim. apply Is_true_eq_left. rewrite negb_true.
  apply <- CAux.fold_forall_or. unfold ConflictSet.For_all.
    intros. unfold peaceful in H. apply not_true_is_false. intro. 
   unfold ConflictSet.For_all in H. apply (H x). apply H0. 
   apply <- concerned_ok. apply Is_true_eq_left. apply H1.
   intros. destruct a. destruct b. simpl. unfold Conflict.eq in H0. simpl in H0. destruct H0.
   rewrite H0. rewrite H1. reflexivity.
  intros. unfold peaceful.
 unfold check_peace in H. rewrite if_bool_dec_false in H. 
 assert (ConflictSet.For_all (fun c => concerned_bool I c = false) C).
    apply -> CAux.fold_forall_or. apply not_true_is_false.
    intro. apply H. apply Is_true_eq_left. apply H0.
  intros. unfold concerned_bool. destruct a. destruct b.
  unfold Conflict.eq in H0. simpl in H0. destruct H0. rewrite H0.
  rewrite H1. reflexivity.
  unfold ConflictSet.For_all. intros. intro.
  apply eq_true_false_abs with (concerned_bool I x). apply Is_true_eq_true.
  apply -> concerned_ok. apply H2.
  unfold ConflictSet.For_all in H0. apply H0. apply H1.
Qed.

Program Lemma check_peace_eq: forall (C: ConflictSet.t) I I',
  I [=] I' -> check_peace C I = check_peace C I'.
Proof.
  intros. apply eq_bool_prop_intro. rewrite <- pc. rewrite <- pc.
  split.
    intros. apply (peaceful_eq C I I' H H0).
    intros. apply (peaceful_eq C I' I (PackageSet.eq_sym H) H0).
Qed.

(* positive: an install set. *)
(* negative: a non-install reasion. *)
Function valid_response (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t) 
  (resp: install_response): Prop :=
  match resp with
  | affirmatif X => is_install_set p R C X
  | negatif Rn => is_good_reason Rn
  end.

(* our installer returns a solution: verify that this set is either
 * empty, or it is an install set (no false positives) *)
(* Checking for false negatives comes down to re-doing a SAT check... *)
Definition verify (p: Package.t) (R: PackageSet.t) (C: ConflictSet.t)
  (r: install_response): bool :=
match r with
| yes I => t
| no x => false
end.


Unset Implicit Arguments.