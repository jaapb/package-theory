Require Export PkgCone.
Require Import Arith.
Require Import Decidable.
(* Require Import ListAux. *)
(* Require Import FSetDecide. *)

Module CProps := Properties ConflictSet.
Module CFacts := CProps.FM.

Section A.

Definition is_conjunctive (a: PackageSet.t) :=
  exists p: Package.t, a [=] (singleton p). 

Lemma conjunctive_dec: forall a: PackageSet.t,
   { is_conjunctive a } + { ~ is_conjunctive a }.
Proof.
  intros. elim (eq_nat_dec (cardinal a) 1).
    intros H. left. 
      elim cardinal_singleton with a. intros. exists x. apply H0. apply H.
    intros H. right.
      intro. apply H. elim H0. intros. rewrite H1. apply singleton_cardinal.
Qed.

Definition is_conjunctive_bool (a: PackageSet.t): bool :=
  if conjunctive_dec a then true else false.

Variable Dependencies: Package.t -> list PackageSet.t.
Axiom Dep_compat_eq: forall p q: Package.t, Package.eq p q -> Dependencies p = Dependencies q.
Axiom Dep_2: forall (x: Package.t) (p q: PackageSet.t),
  List.In p (Dependencies x) -> p [=] q -> List.In q (Dependencies x).

Definition satisfied_pkg (S: PackageSet.t) (p: Package.t): Prop :=
  forall d: PackageSet.t, List.In d (Dependencies p) ->
  exists p': Package.t, In p' (inter S d).

Definition satisfied_pkg_bool (S: PackageSet.t) (p: Package.t): bool :=
  forallb (fun d => exists_ (fun p' => true) (inter S d))
    (Dependencies p).

Theorem spb_ok: forall (S: PackageSet.t) (p: Package.t),
  satisfied_pkg S p <-> Is_true (satisfied_pkg_bool S p).
Proof.
  intros. split.
  (* Prop -> bool *) intros. unfold satisfied_pkg_bool. apply Is_true_eq_left.
    rewrite forallb_forall. intros. apply exists_1.
      simpl_relation.
      unfold Exists. unfold satisfied_pkg in H. elim (H x). intros. exists x0.
      split.
      apply H1. trivial. apply H0.
  (* bool -> Prop *) intros. unfold satisfied_pkg. intros.
  unfold satisfied_pkg_bool in H. 
    elim (forallb_forall (fun d => exists_ (fun _ => true) (inter S d)) (Dependencies p)). 
    intros. cut (Exists (fun _ => true = true) (inter S d)).
      intros. unfold Exists in H3. elim H3. intros. destruct H4. exists x. apply H4.
    apply exists_2. simpl_relation. 
    apply H1. apply Is_true_eq_true. apply H. apply H0.  
Qed.

Lemma satisfied_dec: forall (S: PackageSet.t) (p: Package.t),
  {satisfied_pkg S p} + {~satisfied_pkg S p}.
Proof.
  intros. case_eq (satisfied_pkg_bool S p).
    intros. left. apply <- spb_ok. apply Is_true_eq_left. apply H.
    intros. right. intro. apply (eq_true_false_abs (satisfied_pkg_bool S p)).
      apply Is_true_eq_true. apply -> spb_ok. apply H0.
      apply H.
Qed.
 
Theorem satisfied_union1: 
  forall (S S': PackageSet.t) (p: Package.t),
    satisfied_pkg S p -> satisfied_pkg (union S S') p.
Proof.
  intros. unfold satisfied_pkg. intros. unfold satisfied_pkg in H.
  destruct (H d H0). exists x. apply inter_3. apply union_2.
  apply inter_1 with d. apply H1.
  apply inter_2 with S. apply H1.
Qed.
  
Theorem satisfied_union2:
  forall (S S': PackageSet.t) (p: Package.t),
    satisfied_pkg S' p -> satisfied_pkg (union S S') p.
Proof.
  intros. unfold satisfied_pkg. intros. unfold satisfied_pkg in H.
  destruct (H d H0). exists x. apply inter_3. apply union_3.
  apply inter_1 with d. apply H1.
  apply inter_2 with S'. apply H1.
Qed.

Theorem satisfied_subset:
  forall (S S': PackageSet.t) (p: Package.t),
     S [<=] S' -> satisfied_pkg S p -> satisfied_pkg S' p.
Proof.
  intros. unfold satisfied_pkg. intros. unfold satisfied_pkg in H0.
  destruct (H0 d H1). exists x.
    apply inter_3.
      apply H. apply inter_1 with d. apply H2.
      apply inter_2 with S. apply H2.
Qed. 
    
Definition abundant (S: PackageSet.t): Prop :=
  PackageSet.For_all (satisfied_pkg S) S.

Add Morphism abundant with signature eq ==> iff as abundant_m.
Proof.
  intros. unfold abundant. unfold For_all.
  split.
    intros. apply satisfied_subset with x. rewrite H. reflexivity.
    apply H0. rewrite H. apply H1. 
    intros. apply satisfied_subset with y. rewrite H. reflexivity.
    apply H0. rewrite <- H. apply H1.
Qed. 
 
Lemma abundant_dec: forall S: PackageSet.t,
  {abundant S} + {~abundant S}.
Proof.
  intros. unfold abundant. apply Forall_dec. intros. destruct (satisfied_dec S c).
    left. apply s. right. apply n.
  unfold compat_P. simpl_relation.
    destruct (H0 d). rewrite <- (Dep_compat_eq y). apply H1. symmetry. apply H.
    exists x0. apply H2.
Qed.
 
(* If two package sets are abundant, their union is, too *)
Theorem abundant_union:
   forall (S S': PackageSet.t),
     abundant S -> abundant S' -> abundant (PackageSet.union S S'). 
Proof.
  intros. unfold abundant. unfold PackageSet.For_all. intros. 
  elim union_iff with S S' x. intros. elim H2. 
    intros. apply satisfied_union1. apply H. apply H4.
    intros. apply satisfied_union2. apply H0. apply H4.
  apply H1.
Qed.


Definition concerned (S: PackageSet.t) (c: Package.t * Package.t): Prop :=
  let (p, q) := c in (In p S) /\ (In q S).

Add Morphism concerned with signature PackageSet.eq ==> Conflict.eq ==> iff as concerned_m.
Proof.
  intros. destruct x0. destruct y0. destruct H0. compute in H0. compute in H1. split.
    unfold concerned. intros. destruct H2. split. 
      rewrite <- H0. rewrite <- H. apply H2.
      rewrite <- H1. rewrite <- H. apply H3.
    unfold concerned. intros. destruct H2. split.
      rewrite H0. rewrite H. apply H2.
      rewrite H1. rewrite H. apply H3.
Qed.
    
Definition concerned_bool (S: PackageSet.t) (c: Package.t * Package.t): bool :=
  let (p, q) := c in PackageSet.mem p S && PackageSet.mem q S.

Theorem concerned_dec:
  forall (S: PackageSet.t) (c: Package.t * Package.t),
  {concerned S c} + {~concerned S c}.
Proof.
  intros. unfold concerned. destruct c. apply and_sum.
    elim Props.In_dec with t0 S.
       intros. left. apply a.
       intros. right. apply b. 
    elim Props.In_dec with t1 S. 
       intros. left. apply a.
       intros. right. apply b.
Qed.

Theorem concerned_ok: forall (S: PackageSet.t) (c: Package.t * Package.t),
  concerned S c <-> Is_true (concerned_bool S c).
Proof.
  intros. destruct c. split.
    intros. unfold concerned in H. destruct H.
    unfold concerned_bool. apply andb_prop_intro. split.
      apply Is_true_eq_left. apply mem_1. apply H.
      apply Is_true_eq_left. apply mem_1. apply H0.
    intros. elim (andb_prop_elim (PackageSet.mem t0 S) (PackageSet.mem t1 S)). intros. split.
      apply mem_2. apply Is_true_eq_true. apply H0.
      apply mem_2. apply Is_true_eq_true. apply H1.
    apply H.
Qed.

Definition peaceful (S: PackageSet.t) (C: ConflictSet.t): Prop :=
  ConflictSet.For_all (fun c => ~(concerned S c)) C.

Add Morphism peaceful with signature eq ==> ConflictSet.eq ==> iff as peaceful_m.
Proof.
  intros. unfold peaceful. unfold ConflictSet.For_all. split.
    intros. destruct x1. intro. apply (H1 (t0, t1)). rewrite H0. apply H2.
    rewrite H. apply H3.
    intros. destruct x1. intro. apply (H1 (t0, t1)). rewrite <- H0. apply H2.
    rewrite <- H. apply H3.
Qed.

Lemma compat_p_concerned: forall S: PackageSet.t, 
   compat_P ConflictSet.E.eq (fun c : ConflictSet.elt => ~ concerned S c).
Proof.
  intros. unfold compat_P. simpl_relation. apply H0. unfold ConflictSet.E.eq in H. elim H. intros. compute in H2. compute in H3. unfold concerned. elim H1. intros. split.
  apply In_1 with t0. symmetry. apply H2. apply H4. 
  apply In_1 with t1. symmetry. apply H3. apply H5.
Qed.

Theorem peaceful_dec:
   forall (S: PackageSet.t) (C: ConflictSet.t),
     {peaceful S C} + {~peaceful S C}.
Proof.
  intros. unfold peaceful. apply CAux.Forall_dec. intros. destruct (not_sum (concerned_dec S c)).
    left. apply n. right. apply n. apply compat_p_concerned.
Qed.
 
Theorem peaceful_subset: forall (S1 S2: PackageSet.t) (C: ConflictSet.t),  
  S1 [<=] S2 -> peaceful S2 C -> peaceful S1 C.
Proof.
  unfold peaceful. unfold ConflictSet.For_all. unfold concerned. intros. intro. 
  apply (H0 x).  
     apply H1.
     destruct x. destruct H2. split. 
       apply H. apply H2.  apply H. apply H3.
Qed.
 
(* if a repository is not peaceful, this is caused by two packages in conflict *)
Lemma blame_package: forall (I: PackageSet.t) (C: ConflictSet.t),
   ~peaceful I C ->
    ConflictSet.Exists (fun c => concerned I c) C.
Proof.
  intros. unfold peaceful in H. cut (ConflictSet.Exists (fun c => ~~concerned I c) C). 
    intros. elim H0. intros. destruct H1. exists x. split.
      apply H1.  
      apply not_not. destruct (concerned_dec I x). left. apply c. right. apply n. apply H2.
    apply CAux.not_forall_exists.  
    apply compat_p_concerned.
    intros. apply not_sum. apply concerned_dec.
    apply H.
Qed.

(* If two repositories are peaceful, but their union is not, there
 * must be a conflict between them *)    
Theorem not_peaceful_conflict:
  forall (S S': PackageSet.t) (C: ConflictSet.t),
  (peaceful S C) -> (peaceful S' C) -> ~(peaceful (union S S') C) ->
    Exists (fun p => Exists (fun q => ConflictSet.In (p, q) C) S') S.
Proof.
  intros.
  assert (ConflictSet.Exists (fun c => concerned (union S S') c) C).
  apply blame_package. apply H1.
  elim H2. intros. destruct x.
     decompose [and] H3. unfold concerned in H5. elim H5. intros. 
     elim Facts.union_iff with S S' t0. intros. elim H8.
        intros. elim Facts.union_iff with S S' t1. intros. elim H11.   
          intros. absurd (~(peaceful S C)). intro. apply H14. apply H. unfold peaceful. intro. elim H14 with (t0,t1). apply H4. unfold concerned. split. apply H10. apply H13.
          intros. exists t0. split. apply H10. exists t1. split. apply H13. apply H4. apply H7.
        intros. elim Facts.union_iff with S S' t1. intros. elim H11. 
          intros. exists t1. split. apply H13. exists t0. split. apply H10. apply conflicts_sym. apply H4.
          intros. absurd (~(peaceful S' C)). intro. apply H14. apply H0. intro. elim H14 with (t0, t1). apply H4. split. apply H10. apply H13. apply H7.
   apply H6.
Qed.
             
Definition healthy (S: PackageSet.t) (C: ConflictSet.t): Prop :=
  abundant S /\ peaceful S C.

Add Morphism healthy with signature eq ==> ConflictSet.eq ==> iff as healthy_m.
Proof.
  intros. unfold healthy. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma healthy_dec: forall (S: PackageSet.t) (C: ConflictSet.t),
  {healthy S C} + {~healthy S C}.
Proof.
  intros. unfold healthy. apply and_sum. apply abundant_dec. apply peaceful_dec.
Qed.

Lemma empty_healthy: forall (S: PackageSet.t) (C: ConflictSet.t),
  Empty S -> healthy S C.
Proof.
  intros. split. 
    unfold abundant. unfold For_all. intros. absurd (In x S). apply H. apply H0.
    unfold peaceful. unfold ConflictSet.For_all. intros. intro. 
    unfold concerned in H1. destruct x. destruct H1.
      absurd (In t0 S). apply H. apply H1.
Qed.

Definition is_install_set (p: Package.t) (R: PackageSet.t) (C: ConflictSet.t) (I: PackageSet.t) :=
  I [<=] R /\ In p I /\ healthy I C.

Definition installable (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t) :=
  exists I: PackageSet.t, is_install_set p R C I.

Definition co_installable (R: PackageSet.t) (C: ConflictSet.t) (S: PackageSet.t) :=
  exists I: PackageSet.t, I [<=] R /\ S [<=] I /\ healthy I C.

Lemma inst_coinst: forall (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t),
  installable R C p <-> co_installable R C (singleton p).
Proof.
  intros. split. 
    intros. destruct H. destruct H. destruct H0.
    exists x. split. apply H. split. unfold Subset. intros. rewrite <- (singleton_1 H2). apply H0.
    apply H1. 
    intros. destruct H. destruct H. destruct H0.
    exists x. split. apply H. split. unfold Subset in H0. apply (H0 p). apply singleton_2. reflexivity.
    apply H1.
Qed.

Definition direct_normal_dependency (p: Package.t) (q: Package.t) :=
  direct_dependency Dependencies (fun x => true) p q.

Definition direct_conjunctive_dependency (p: Package.t) (q: Package.t) :=
  direct_dependency Dependencies is_conjunctive_bool p q.

Lemma conj_dep_is_dep:
  forall p q, direct_conjunctive_dependency p q -> direct_normal_dependency p q.
Proof.
  intros. destruct H. destruct H. unfold direct_normal_dependency. unfold direct_dependency.
  exists x. split.
    apply H.
    rewrite filter_In in H0. destruct H0.
    rewrite filter_In. split.
      apply H0.
      trivial.
Qed.

Definition normal_dependency_path (p q: Package.t)
  (l: list (Package.t)): Prop :=
  dependency_path Dependencies (fun a => true) p q l.

Definition conjunctive_dependency_path (p q: Package.t)
  (l: list (Package.t)): Prop :=
  dependency_path Dependencies is_conjunctive_bool p q l.

Lemma conj_dp_is_dp: forall p q l,
  conjunctive_dependency_path p q l -> normal_dependency_path p q l.
Proof.
  intros. functional induction (dependency_path Dependencies (fun a => true) p q l).
    simpl in H. apply conj_dep_is_dep. exact H.
    simpl in H. destruct H. split.
       apply conj_dep_is_dep. assumption.
       apply IHP. assumption.
Qed.

Definition normal_dependency (p q: Package.t): Prop :=
  dependency Dependencies (fun a => true) p q.

Definition conjunctive_dependency (R: PackageSet.t) (p q: Package.t): Prop :=
  dependency Dependencies is_conjunctive_bool p q.

Definition normal_cone (R: PackageSet.t) (S: PackageSet.t | S [<=] R):=
  cone Dependencies (fun a => true) R S.

(* If a set is co-installable, it will also be co-installable in
 * its (normal) dependency cone. *)
Theorem installable_in_cone:
  forall (R: PackageSet.t) (C: ConflictSet.t) (P: PackageSet.t | P [<=] R),
  co_installable R C (proj1_sig P) ->
  co_installable (normal_cone R (exist (fun v => v [<=] R) (proj1_sig P) (proj2_sig P))) C (proj1_sig P). 
Proof.
  intros R C P H. destruct H as [I H0]. destruct H0. destruct H0. destruct P as [P HP]. simpl in H0. simpl. 
  exists (inter I (normal_cone R (exist (fun v => v[<=]R) P HP))).
  split.
    apply inter_subset_2.
    split. unfold Subset. intros. apply inter_3. apply H0. apply H2.
    unfold normal_cone. apply cone_subset. apply H2.
    (* healthy *) destruct H1 as [Hab Hpcf]. split. 
       (* abundant *) intros x Hx d Hd. 
       destruct (Hab x (inter_1 Hx) d Hd) as [d' Hd']. exists d'.
         apply inter_3. apply inter_3. apply (inter_1 Hd'). 
         destruct (cone_dep Dependencies (fun _ => true) R (exist (fun v => v [<=] R) P HP) x).
           apply (inter_2 Hx). 
           apply dep_cone. exists x. split. apply H1. exists nil. split. apply HP. apply H1.
           split. apply H. apply (inter_1 Hd'). exists d. split.
           apply (inter_2 Hd'). rewrite filter_In. split. apply Hd. trivial.
           destruct H1 as [x' [Hx' Hdep]]. apply dep_cone. exists x'.
           split. apply Hx'. destruct Hdep. exists (x0 ++ (x::nil)).
             apply dp_split. apply H1. simpl. split. apply H. apply (inter_1 Hx).
             split. apply H. apply (inter_1 Hd').
             unfold direct_dependency. exists d. split. apply (inter_2 Hd').
             rewrite filter_In. split. apply Hd. trivial. apply (inter_2 Hd'). 
       (* peaceful *) intros c Hc Hb. 
         apply (Hpcf c). apply Hc. 
         destruct c. split. apply (inter_1 (proj1 Hb)). apply (inter_1 (proj2 Hb)).
Qed.

Theorem conjunctive_always_installed:
  forall R C p q I,
    conjunctive_dependency R p q ->
    is_install_set p R C I ->
    In q I.
Proof.
  intros. destruct H. destruct H0. destruct H1. destruct H2. unfold abundant in H2. unfold For_all in H2.
  functional induction (dependency_path Dependencies is_conjunctive_bool p q x).
  (* q is a direct conjunctive dependency of p *)  
    destruct H. destruct H. rewrite filter_In in H4. destruct H4. 
    elim (H2 p H1 x). generalize H5. clear H5. unfold is_conjunctive_bool. 
    destruct conjunctive_dec. intros. 
      unfold is_conjunctive in i. destruct i. clear H5. 
      apply In_1 with x0. apply singleton_1.
      assert (In x0 (singleton x1)). rewrite <- H7. apply (inter_2 H6).
      rewrite <- (singleton_1 H5). rewrite <- H7. apply H.  
      apply (inter_1 H6). 
      intros. inversion H5.    
    apply H4.
  (* q is a direct conjunctive dependency of h *)
  destruct H. apply IHP. apply H4. 
  destruct H. destruct H. rewrite filter_In in H5. destruct H5.
  destruct (H2 p H1 x). apply H5.
  generalize H6. clear H6. unfold is_conjunctive_bool.
  destruct conjunctive_dec. intros. clear H6.
    unfold is_conjunctive in i. destruct i. 
    apply In_1 with x0. apply singleton_1. 
    assert (In x0 (singleton x1)). rewrite <- H6. apply (inter_2 H7).
    rewrite <- (singleton_1 H8). rewrite <- H6. apply H.
    apply (inter_1 H7).
    intros. inversion H6.
Qed.

(* If a package conjunctively depends on a package that is not installable,
 * then it is not installable itself *)
Theorem not_installable_conjunctive: forall (R: PackageSet.t) (C: ConflictSet.t)
  (p q: Package.t),
  ~installable R C q -> conjunctive_dependency R p q -> ~installable R C p.
Proof.
  intros. intro. apply H. 
  elim H1. intros. destruct H2. destruct H3. exists x. split.
   apply H2.
   split.
     apply conjunctive_always_installed with R C p. apply H0.
     split. apply H2. split. apply H3. apply H4. 
     apply H4.
Qed.

(* strong dependencies *)
Definition strong_dep (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t) (q: Package.t) :=
  (exists N: PackageSet.t, is_install_set p R C N) /\
  forall I: PackageSet.t, I [<=] R -> In p I /\ healthy I C -> In q I.

Theorem strong_dep_trans:
  forall (R: PackageSet.t) (C: ConflictSet.t) (p q r: Package.t),
    strong_dep R C p q /\ strong_dep R C q r -> strong_dep R C p r.
Proof.
  intros. elim H. intros. 
  unfold strong_dep. split.
    unfold strong_dep in H0. destruct H0. apply H0.
    intros. destruct H3. apply H1. apply H2. split.
      apply H0. apply H2. split.
        exact H3.
        exact H4.
      exact H4.
Qed.

Definition strong_dep_neg (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t) (q: Package.t) :=
  (exists N: PackageSet.t, is_install_set p R C N) /\
  ~exists I: (PackageSet.t), I [<=] R /\ In p I /\ healthy I C /\ ~In q I.

Theorem strong_dep_pos_neg:
  forall (R: PackageSet.t) (C: ConflictSet.t) (p q: Package.t), 
    strong_dep R C p q -> strong_dep_neg R C p q.
Proof.
  intros. unfold strong_dep_neg. unfold strong_dep in H. destruct H. split.
    apply H.
    intro. elim H1. intros.  
    destruct H2. destruct H3. destruct H4.
    apply H5. apply H0. apply H2. split. apply H3. apply H4. 
Qed.

Theorem strong_dep_neg_pos:
  forall (R: PackageSet.t) (C: ConflictSet.t) (p q: Package.t),
     strong_dep_neg R C p q -> strong_dep R C p q.
Proof.
  intros. unfold strong_dep_neg in H. unfold strong_dep. destruct H. split.
    apply H.     
    intro I. elim (In_dec q I).  
    intros. exact a. 
    intros. destruct H2. intros. elim H0. exists I. split.
      exact H1.
      split.
        exact H2.
        split.
          exact H3.
          exact b.
Qed.

Theorem conjunctive_strong_dep: forall R C p q,
  conjunctive_dependency R p q -> installable R C p ->
  strong_dep R C p q.
Proof.
  intros R C p q Hconj Hinst. unfold strong_dep. split.
    elim Hinst. intros I HI. exists I. apply HI. 
    intros I HR HI. apply (conjunctive_always_installed R C p q I Hconj).
    split. apply HR. apply HI.
Qed.
 
(* strong conflict *)
Definition strong_conflict (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t) (q: Package.t) :=
  installable R C p /\ installable R C q /\
  ~exists I: PackageSet.t, healthy I C /\ In p I /\ In q I.

(* if there is a strong conflict, ... *)
Theorem scp: forall (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t | In p R) (q: Package.t | In q R),
  strong_conflict R C (proj1_sig p) (proj1_sig q) ->
  ConflictSet.Exists (fun c =>
     match c with
       (c1,c2) => (E.eq (proj1_sig p) c1 \/ normal_dependency (proj1_sig p) c1) /\
                       (E.eq (proj1_sig q) c2 \/ normal_dependency (proj1_sig q) c2)
     end) C.
Proof.
  intros R C pp qq H. destruct pp as [p Hp]. destruct qq as [q Hq]. unfold strong_conflict in H. destruct H. destruct H0.
  assert (installable (normal_cone R (exist (fun v => v [<=] R) (singleton p) (s_ss Hp))) C p). 
    elim (installable_in_cone R C (exist (fun v => v [<=] R) (singleton p) (s_ss Hp))). simpl. intros. exists x.
    destruct H2. destruct H3. split. apply H2. split. unfold Subset in H3. apply H3. apply singleton_2. reflexivity. 
    apply H4. simpl. apply -> inst_coinst. apply H.
  assert (installable (normal_cone R (exist (fun v => v [<=] R) (singleton q) (s_ss Hq))) C q).
    elim (installable_in_cone R C (exist (fun v => v [<=] R) (singleton q) (s_ss Hq))). simpl. intros. exists x.
    destruct H3. destruct H4. split. apply H3. split. unfold Subset in H4. apply H4. apply singleton_2. reflexivity. 
    apply H5. simpl. apply -> inst_coinst. apply H0. 
  unfold installable in H2. elim H2. intros P H4. destruct H4. destruct H5. destruct H6. unfold installable in H3. elim H3. intros Q H8. destruct H8. destruct H9. destruct H10.
  assert (abundant (union P Q)). apply abundant_union. apply H6. apply H10.
  assert (~peaceful (union P Q) C). intro. apply H1. exists (union P Q). split. 
     split. apply H12. apply H13. split. apply union_2. apply H5. apply union_3. apply H9.
  elim (not_peaceful_conflict P Q C H7 H11).
  intros p' H14. destruct H14. destruct H15 as [q' Hq']. destruct Hq' as [Hq' HC]. 
  exists (p', q'). split. apply HC. split.
    simpl. elim (cone_dep Dependencies (fun a => true) R (exist (fun v => v [<=] R) (singleton p) (s_ss Hp)) p'). 
      intros. simpl in H15. left. apply singleton_1. apply H15.
      intros. simpl in H15. right. destruct H15. 
      apply <- (dependency_compat_eq Dependencies (fun _ => true) p x p').
      apply dependency_in_dependency with R. apply H15.
      apply singleton_1. apply H15.
      apply H4. apply H14.
    simpl. elim (cone_dep Dependencies (fun a => true) R (exist (fun v => v [<=] R) (singleton q) (s_ss Hq)) q'). 
      intros. simpl in H15. left. apply singleton_1. apply H15.
      intros. simpl in H15. right. destruct H15. 
      apply <- (dependency_compat_eq Dependencies (fun _ => true) q x q').
      apply dependency_in_dependency with R. apply H15.
      apply singleton_1. apply H15.
      apply H8. apply Hq'.
 apply H13.    
Qed.

Variable ReverseDependencies: Package.t -> list PackageSet.t.
Axiom RevDep: forall (f: t -> bool) (p q: Package.t),
  In p (dependency_function Dependencies f q) <->
  In q (dependency_function ReverseDependencies f p). 

(* direct predecessors of p in R *)
Definition reverse_dependency_function (f: t -> bool) (p: Package.t): PackageSet.t :=
  dependency_function ReverseDependencies f p.

Lemma rdf: forall f p p',
  Package.eq p p' -> reverse_dependency_function f p [=] reverse_dependency_function f p'.
Proof.
  intros. 
    split. 
      intros. apply -> RevDep. rewrite <- H. apply <- RevDep. apply H0.
      intros. apply -> RevDep. rewrite -> H. apply <- RevDep. apply H0.
Qed.
    
Lemma pred_ok: forall (f: t -> bool) (p q: Package.t),
  direct_dependency Dependencies f p q <->
  In p (reverse_dependency_function f q).
Proof.
  intros. split.
    intros. unfold reverse_dependency_function. apply -> RevDep. apply direct_dependency_depfunc. apply H.
    intros. apply depfunc_direct_dependency. apply <- RevDep. apply H.
Qed.      

End A.

Section C.

Variable Dependencies: Package.t -> list PackageSet.t.

(* a dependency function that discounts 'superfluous' dependencies
 * in the style of "Depends: a, a | b" *)
Definition NoSupDependencies (R: PackageSet.t) (p: Package.t): list (PackageSet.t) :=
  List.filter (fun dep => negb (existsb (fun a => strict_subset a dep) (Dependencies p))) (Dependencies p).

Lemma NSD_subset_D: forall (R d: PackageSet.t) (p: Package.t),
  List.In d (NoSupDependencies R p) -> List.In d (Dependencies p).
Proof.
  intros. unfold NoSupDependencies in H. rewrite filter_In in H. destruct H.
  apply H.
Qed.

Definition find_smallest_subdep (l: list PackageSet.t) (d: PackageSet.t): PackageSet.t :=
  List.fold_left (fun acc d' =>
    if strict_subset d' acc then d' else acc
  ) l d.

Lemma smallest_subdep_is_subset:
  forall l d, find_smallest_subdep l d [<=] d.
Proof.
  intros. unfold find_smallest_subdep. generalize d. clear d. induction l.
    simpl. reflexivity.
    simpl. intros. case_eq (strict_subset a d).
      intros. apply strict_subset_weak. apply strict_subset_trans_subset2 with a. apply (IHl a).
        apply strict_subset_2. apply H. 
      intros. apply (IHl d). 
Qed.

Lemma smallest_subdep_in_list:
  forall l d, find_smallest_subdep l d = d \/ List.In (find_smallest_subdep l d) l.
Proof.
  intros. generalize d. clear d. induction l.
    simpl. left. reflexivity.
    simpl. simpl in IHl. intros. 
      case_eq (strict_subset a d). intros.
      elim (IHl a).
        intros. right. left. symmetry. apply H0.
        intros. right. right. apply H0.
      intros. elim (IHl d). 
        intros. left. apply H0. 
        intros. right. right. apply H0.
Qed.
     
Lemma ss_ok: forall (l: list PackageSet.t) (d: PackageSet.t), (* List.In d l -> *)
  ~exists d': PackageSet.t, List.In d' l /\ d' [<] (find_smallest_subdep l d).
Proof.
  intros (* l dd *). (* destruct dd. simpl. *) generalize d. clear d. induction l.
    intros. intro. destruct H. destruct H. simpl in H. contradiction.
    intros. intro. destruct H. destruct H. elim H. clear H. 
      intros. simpl in H0. rewrite H in H0. clear H. case_eq (strict_subset x d).
        intros. rewrite H in H0. apply (strict_subset_not_subset H0).
        apply smallest_subdep_is_subset. 
       intros. rewrite H in H0. apply eq_true_false_abs with (strict_subset x d). 
       apply strict_subset_1. apply strict_subset_trans_subset1 with (find_smallest_subdep l d). apply H0.
       apply smallest_subdep_is_subset. apply H.
    clear H. intros. simpl in H0.
    elim (IHl (if strict_subset a d then a else d)). 
      exists x. split. apply H. apply H0.
Qed.  
  
Lemma NSD_installability:
  forall (R: PackageSet.t) (C: ConflictSet.t) (p: Package.t), In p R ->
 (installable Dependencies R C p <-> installable (NoSupDependencies R) R C p). 
Proof.
  intros. unfold installable. split. 
    intros. destruct H0. destruct H0. destruct H1. 
    exists x. split.
      apply H0. split.
      apply H1. unfold healthy. split. destruct H2. unfold abundant. unfold abundant in H2.
      unfold satisfied_pkg. unfold For_all. intros. unfold satisfied_pkg in H2.
      unfold For_all in H2. destruct (H2 x0 H4 d). unfold NoSupDependencies in H5.
      rewrite filter_In in H5.
        destruct H5. apply H5. exists x1. apply H6. unfold healthy in H2.
        destruct H2. apply H3.
    intros. destruct H0. destruct H0. destruct H1.
    exists x. split.
      apply H0. split.
      apply H1. unfold healthy. split. destruct H2. unfold abundant. unfold abundant in H2.
      unfold satisfied_pkg in H2. unfold For_all in H2. 
      unfold satisfied_pkg. unfold For_all.
      intros. destruct (H2 x0 H4 (find_smallest_subdep (Dependencies x0) d)). 
      unfold NoSupDependencies. rewrite filter_In. split. 
      elim (smallest_subdep_in_list (Dependencies x0) d). 
        intros. rewrite H6. apply H5. trivial.
      apply eq_true_not_negb. intro. rewrite existsb_exists in H6. destruct H6.
      destruct H6. apply (ss_ok (Dependencies x0) d). exists x1. split.
        apply H6.
        apply strict_subset_2. apply H7.
      exists x1. apply inter_3. 
         apply (inter_1 H6). 
         apply (smallest_subdep_is_subset (Dependencies x0)).
         apply (inter_2 H6).
    unfold healthy in H2. destruct H2. apply H3. 
Qed.

(* Triangles. *)

Definition is_triangle (R: PackageSet.t) (c: Conflict.t): Prop :=
  let (c1, c2) := c in
  exists t,
    (exists d, List.In d (Dependencies t) /\ In c1 d /\ In c2 d /\
     (forall d', (exists t', List.In d' (Dependencies t')) /\ (In c1 d' \/ In c2 d') ->
      d [=] d')).

Definition beq_pkg (a: Package.t) (b: Package.t): bool :=
  if eq_dec a b then true else false.

Lemma beq_pkg_eq: forall a b: Package.t, beq_pkg a b = true <-> Package.eq a b.
Proof.
  intros a b. unfold beq_pkg. split.
    elim (eq_dec a b). intros. apply a0. intros. inversion H.
    elim (eq_dec a b). intros. trivial. intros. contradiction.
Qed.

(* Definition triangle_parts_ok (R: PackageSet.t) (C: ConflictSet.t) (f: t -> bool) (c: Conflict.t): Prop :=
  let (c1, c2) := c in
    For_all (fun p => co_installable (NoSupDependencies R) R C (add c1 (singleton p)) /\
      co_installable (NoSupDependencies R) R C (add c2 (singleton p))) (reverse_dependency_function (NoSupDependencies R) R f c1). *)

Definition only_triangles (R: PackageSet.t) (C: ConflictSet.t) (f: t -> bool) (A: PackageSet.t | A [<=] R) := 
  ConflictSet.For_all (fun c => concerned
    (cone (NoSupDependencies R) f R A) c ->
     is_triangle R c (* /\ triangle_parts_ok R C c *)) C.

(* the packages to remove from (union A B) to make I co-installable
 * all packages involved in a transconflict *)
Definition packages_to_remove (R: PackageSet.t) (C: ConflictSet.t) (A: PackageSet.t) (B: PackageSet.t) :=
  PackageSet.filter (fun p =>
    ConflictSet.exists_ (fun c => let (c1, c2) := c in
      PackageSet.mem c1 A && PackageSet.mem c2 B && beq_pkg p c1
    ) C
  ) (union A B).

(* Lemma compat_bool_1: forall R y,
  compat_bool Package.eq
    (fun p' : elt =>
     direct_dependency_bool (NoSupDependencies R) is_conjunctive_bool R p' y).
Proof.
  intros. unfold compat_bool. intros. apply eq_true_iff_eq. split.
    intros. apply Is_true_eq_true. apply -> dd_ok. apply -> direct_dependency_m.
    apply <- dd_ok. apply Is_true_eq_left. apply H0. reflexivity. apply H. reflexivity.
    intros. apply Is_true_eq_true. apply -> dd_ok. apply <- direct_dependency_m.
    apply <- dd_ok. apply Is_true_eq_left. apply H0. reflexivity. apply H. reflexivity.
Qed. *)

Lemma compat_bool_2: forall A1 Ax a, compat_bool (fun x0 y : Package.t * Package.t =>
      Package.eq (fst x0) (fst y) /\ Package.eq (snd x0) (snd y))
      (fun c : ConflictSet.elt =>
         let (c1, c2) := c in
         PackageSet.mem c1 A1 && PackageSet.mem c2 Ax &&
         beq_pkg a c1).
Proof.
  intros. unfold compat_bool. simpl_relation. apply eq_true_iff_eq. split. 
    intros. symmetry in H1. elim (andb_true_eq _ _ H1). clear H1. intros.
    apply <- andb_true_iff. split. rewrite <- H. rewrite <- H0. symmetry. apply H1.
    apply <- beq_pkg_eq. transitivity t2. 
      apply -> beq_pkg_eq. symmetry. apply H2.
      apply H.
    intros. symmetry in H1. elim (andb_true_eq _ _ H1). clear H1. intros.
    apply <- andb_true_iff. split. rewrite H. rewrite H0. symmetry. apply H1.
    apply <- beq_pkg_eq. transitivity t0.
      apply -> beq_pkg_eq. symmetry. apply H2.
      symmetry. apply H.
Qed.

Lemma compat_bool_3: forall C A1 Ax, compat_bool Package.eq (fun p : elt =>
  ConflictSet.exists_
    (fun c : ConflictSet.elt =>
     let (c1, c2) := c in
       PackageSet.mem c1 A1 && PackageSet.mem c2 Ax && beq_pkg p c1) C).
Proof.
  intros. unfold compat_bool. simpl_relation. apply eq_true_iff_eq. split.
    intros. rewrite <- (CFacts.exists_iff _ (compat_bool_2 A1 Ax y)). 
    rewrite <- (CFacts.exists_iff _ (compat_bool_2 A1 Ax x)) in H0. destruct H0. destruct H0. 
    exists x0. split. 
      apply H0.
      destruct x0. symmetry in H1. destruct (andb_true_eq _ _ H1). clear H1.
      destruct (andb_true_eq _ _ H2). clear H2.
        apply <- andb_true_iff. split. apply <- andb_true_iff. split.
          symmetry. apply H1.
          symmetry. apply H4. 
        apply <- beq_pkg_eq. transitivity x.
          symmetry. apply H.
          apply -> beq_pkg_eq. symmetry. apply H3.
    intros. rewrite <- (CFacts.exists_iff _ (compat_bool_2 A1 Ax x)).
      rewrite <- (CFacts.exists_iff _ (compat_bool_2 A1 Ax y)) in H0. destruct H0. destruct H0.
      exists x0. split.
        apply H0.
        destruct x0. symmetry in H1. destruct (andb_true_eq _ _ H1). clear H1.
        destruct (andb_true_eq _ _ H2). clear H2.
          apply <- andb_true_iff. split. apply <- andb_true_iff. split.
            symmetry. apply H1.
            symmetry. apply H4.
          apply <- beq_pkg_eq. transitivity y.
            apply H.
            apply -> beq_pkg_eq. symmetry. apply H3.
Qed.

Lemma triangles_ok:
  forall (R: PackageSet.t) (C: ConflictSet.t) (a: PackageSet.t | a [<=] R),
    (* installable separately *)
    (For_all (fun a => installable (NoSupDependencies R) R C a) (proj1_sig a)) ->
    only_triangles R C (fun _ => true) a ->
    ~ConflictSet.Exists (fun c => let (c1, c2) := c in In c1 (proj1_sig a) \/ In c2 (proj1_sig a)) C ->
    co_installable (NoSupDependencies R) R C (proj1_sig a).
Proof.
  intros R C aa. destruct aa as [a Ha]. simpl. intros Hsep Htri Hcc. 
  unfold co_installable. unfold For_all in Hsep. 
  induction a using set_induction.
    (* case 1: a is empty *)
    exists empty. split. apply subset_empty. split. rewrite (empty_is_empty_1 H).
    reflexivity. split. unfold abundant. unfold For_all. intros. absurd (In x empty).
    intro. apply -> empty_iff. apply H1. apply H0.
    unfold peaceful. unfold ConflictSet.For_all. intros. unfold concerned. 
    destruct x. intro. destruct H1. absurd (In t0 empty).
    intro. apply -> empty_iff. apply H3. apply H1.
    (* case 2: a1 is OK, now x *)
    (* a1 is minimally installable, its install set is A1, subset of the cone of a1. *)
    assert (a1 [<=] R) as Ha1. unfold Subset. intros. apply Ha. elim (H0 a). intros. apply H3. right. apply H1. 
    elim (installable_in_cone (NoSupDependencies R) R C (exist (fun v => v [<=] R) a1 Ha1)).
    simpl. intros A1 X. destruct X as [HA1_1 [HA1_2 [HA1_A HA1_P]]]. 
    assert (A1 [<=] R) as HA1. unfold Subset. intros. 
    apply (cone_subset_R (NoSupDependencies R) (fun _ => true) R (exist (fun v => v [<=] R) a1 Ha1)).
    apply HA1_1. apply H1.
    (* x is installable, its install set is AX, subset of the cone of (singleton x) *)
    assert (In x R) as Hx. unfold Subset. apply Ha. elim (H0 x). intros. apply H2. left. reflexivity.
    elim (installable_in_cone (NoSupDependencies R) R C (exist (fun v => v [<=] R) (singleton x) (s_ss Hx))).
    simpl. intros Ax X. destruct X as [HAx_1 [HAx_2 [HAx_A HAx_P]]].
    assert (Ax [<=] R) as HAx. unfold Subset. intros. 
    apply (cone_subset_R (NoSupDependencies R) (fun _ => true) R (exist (fun v => v [<=] R) (singleton x) (s_ss Hx))).
    apply HAx_1. apply H1.
    (* as an installation set, we take the union of A and B without ... *)
    exists (diff (union A1 Ax) (packages_to_remove R C A1 Ax)). split.
      (* this union is a subset of R. *)         
      apply subset_diff. apply (union_subset_3 HA1 HAx). 
      (* a2 is a subset of this union. *)
      split. unfold Subset. intros. apply <- diff_iff. split.
        elim (proj1 (iff_and (H0 a)) H1).
          intros. apply union_3. apply HAx_2. apply singleton_2. apply H2.
          intros. apply union_2. apply HA1_2. apply H2.
        intro. unfold packages_to_remove in H2. rewrite (filter_iff (union A1 Ax) a (compat_bool_3 C A1 Ax)) in H2. 
        destruct H2. rewrite <- (CFacts.exists_iff C (compat_bool_2 A1 Ax a)) in H3. 
        destruct H3. destruct H3. destruct x0. symmetry in H4. destruct (andb_true_eq _ _ H4). 
        clear H4. destruct (andb_true_eq _ _ H5). clear H5.
        apply Hcc. exists (t0, t1). split.
          apply H3. left. apply In_1 with a. apply -> beq_pkg_eq. symmetry. apply H6. apply H1.
      split. 
        (* this union is abundant *)
        unfold abundant. unfold For_all. intros. unfold satisfied_pkg. intros.
        rewrite diff_iff in H1. destruct H1. 
        (* d has to be satisfied somewhere...let's say by x1 *)
        elim (abundant_union (NoSupDependencies R) A1 Ax HA1_A HAx_A x0 H1 d).
          intros x1 Hx1.
          (* Suppose x1 is involved in a conflict and part of A, then we use x2. *)
          elim (In_dec x1 (packages_to_remove R C A1 Ax)). 
            intros. unfold packages_to_remove in a. rewrite (filter_iff (union A1 Ax) x1 (compat_bool_3 C A1 Ax)) in a.
            destruct a. rewrite <- (CFacts.exists_iff C (compat_bool_2 A1 Ax x1)) in H5.
            destruct H5. destruct H5. destruct x2. symmetry in H6. destruct (andb_true_eq _ _ H6).
            clear H6. destruct (andb_true_eq _ _ H7). clear H7.
          destruct (Htri (t0, t1) H5). unfold concerned. split.
            apply (cone_of_subset_is_subset _ _ R (exist (fun v => v [<=] R) a1 Ha1)).
            simpl. unfold Subset. intros. elim (H0 a). intros. apply H11. right. apply H7.
            apply HA1_1. apply <- mem_iff. symmetry. apply H6.
            apply (cone_of_subset_is_subset _ _ R (exist (fun v => v [<=] R) (singleton x) (s_ss Hx))).
            simpl. unfold Subset. intros. elim (H0 a). intros. apply H11. left. apply singleton_1. apply H7.
            apply HAx_1. apply <- mem_iff. symmetry. apply H9.
          destruct H7. destruct H7. destruct H10. destruct H11. 
          assert (x3 [=] d). apply H12.
            split. exists x0. unfold NoSupDependencies in H2. rewrite filter_In in H2. destruct H2.
            apply H2. left. apply In_1 with x1. apply -> beq_pkg_eq. symmetry. apply H8. apply (inter_2 Hx1).
          exists t1. apply inter_3. 
            apply <- diff_iff. split. 
            apply union_3. apply <- mem_iff. symmetry. apply H9.
            intro. unfold packages_to_remove in H14. rewrite (filter_iff (union A1 Ax) t1 (compat_bool_3 C A1 Ax)) in H14.
            destruct H14. rewrite <- (CFacts.exists_iff C (compat_bool_2 A1 Ax t1)) in H15.
            destruct H15. destruct H15. destruct x4. symmetry in H16. destruct (andb_true_eq _ _ H16).
            clear H16. destruct (andb_true_eq _ _ H17). 
            apply (HAx_P (t2, t3) H15). split. apply In_1 with t1.
              apply -> beq_pkg_eq. symmetry. apply H18.
              apply <- mem_iff. symmetry. apply H9.
              apply <- mem_iff. symmetry. apply H19.
              rewrite <- H13. apply H11.
          intros. exists x1. apply inter_3.
            apply <- diff_iff. split.
            apply (inter_1 Hx1). apply b. apply (inter_2 Hx1). apply H2.
        (* this union is peaceful. *)
        unfold peaceful. unfold ConflictSet.For_all. intros. destruct x0. intro.
        (* (t0, t1) has to be a transconflict, because A1 and Ax are already pcf. *)
        unfold concerned in H2. destruct H2. rewrite diff_iff in H2. destruct H2.
        rewrite diff_iff in H3. destruct H3. destruct (union_1 H2). destruct (union_1 H3). 
          apply (HA1_P (t0, t1)). apply H1. split. apply H6. apply H7.
          apply H4. unfold packages_to_remove. rewrite (filter_iff (union A1 Ax) t0 (compat_bool_3 C A1 Ax)).
          split. apply H2. rewrite <- (CFacts.exists_iff C (compat_bool_2 A1 Ax t0)).
          exists (t0, t1). split. apply H1.
          apply andb_true_intro. split. apply andb_true_intro. split.
            apply -> mem_iff. apply H6. apply -> mem_iff. apply H7.
          apply <- beq_pkg_eq. reflexivity.
        destruct (union_1 H3).
          apply H5. unfold packages_to_remove. rewrite (filter_iff (union A1 Ax) t1 (compat_bool_3 C A1 Ax)).
          split. apply H3. rewrite <- (CFacts.exists_iff C (compat_bool_2 A1 Ax t1)).
          exists (t1, t0). split. apply conflicts_sym. apply H1.
          apply andb_true_intro. split. apply andb_true_intro. split.
            apply -> mem_iff. apply H7. apply -> mem_iff. apply H6.
          apply <- beq_pkg_eq. reflexivity.
          apply (HAx_P (t0, t1)). apply H1. split. apply H6. apply H7.
        (* x is installable, duh. *)
        elim (Hsep x). intros. exists x0. destruct H1. destruct H2. split.
          apply H1. split. simpl. unfold Subset. intros. apply In_1 with x.
          apply singleton_1. apply H4. apply H2. apply H3.
        elim (H0 x). intros. apply H2. left. reflexivity.
        (* a1 *)
        elim (IHa1 Ha1). intros. destruct H1. destruct H2.
        exists x0. split. apply H1. split. apply H2. apply H3.
        intros. apply (Hsep x0). elim (H0 x0). intros. apply H3. right. apply H1.
        unfold only_triangles. unfold ConflictSet.For_all.  intros. 
        apply Htri. apply H1. unfold concerned in H2. destruct x0. destruct H2.
        unfold concerned. split.
        apply (cone_of_subset_is_subset _ _ R (exist (fun v => v [<=] R) a1 Ha1)).
          simpl. unfold Subset. intros. destruct (H0 a). apply H6. right. apply H4.
          apply H2.
        apply (cone_of_subset_is_subset _ _ R (exist (fun v => v [<=] R) a1 Ha1)).
          simpl. unfold Subset. intros. destruct (H0 a). apply H6. right. apply H4.
          apply H3.
        intro. apply Hcc. destruct H1. exists x0. destruct H1. split.
          apply H1. 
          destruct x0. destruct H2.
            left. destruct (H0 t0). apply H4. right. apply H2.
            right. destruct (H0 t1). apply H4. right. apply H2.
Qed. 

End C.
                   
Unset Implicit Arguments.
