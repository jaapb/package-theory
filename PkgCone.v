Require Export List.
Require Export PkgDefinitions.
Require Import Decidable.
Require Import Arith.
Require Import Max.
Require Import BoolEq.
Require Import FunInd.
Require Import Omega.

Section dep_cone_stuff.
(* Variable R: PackageSet.t. *)

Variable Dependencies: Package.t -> list PackageSet.t.
Axiom Dep_compat_eq: forall p q: Package.t, Package.eq p q ->
  Dependencies p = Dependencies q.
Axiom no_self_dep: forall p: Package.t,
  ~ exists d, In p d /\ List.In d (Dependencies p).

Variable dep_filter: PackageSet.t -> bool.
Axiom dep_filter_eq: forall p q: PackageSet.t,
  PackageSet.eq p q -> dep_filter p = dep_filter q.
Lemma eqb_trans: forall a b c: bool,
  Is_true (Bool.eqb a b) -> Is_true (Bool.eqb b c) -> Is_true (Bool.eqb a c).
Proof.
  intros. rewrite (eqb_eq a b H). apply H0.
Qed. 

Add Morphism dep_filter with signature PackageSet.eq ==> Logic.eq 
  as dep_filter_m.
Proof.
  intros. apply dep_filter_eq. apply H.
Qed.

Definition dependency_function (p: Package.t): PackageSet.t :=
  (List.fold_left (fun alt acc =>
    union alt acc
  ) (List.filter dep_filter (Dependencies p)) empty).

Definition direct_dependency (p: Package.t) (q: Package.t) :=
  exists d: PackageSet.t, In q d /\
  List.In d (List.filter dep_filter (Dependencies p)).

Add Morphism direct_dependency with signature Package.eq ==> Package.eq ==> iff
  as direct_dependency_m.
Proof.
  intros. unfold direct_dependency. split.
    intros. destruct H1. destruct H1. 
      rewrite filter_In in H2. destruct H2. exists x1. split.
        rewrite <- H0. apply H1.
        rewrite filter_In. split. 
          rewrite <- (Dep_compat_eq _ _ H). apply H2.
          apply H3.
      intros. destruct H1. destruct H1. 
      rewrite filter_In in H2. destruct H2. exists x1. split.
        rewrite H0. apply H1.
        rewrite filter_In. split. 
          rewrite (Dep_compat_eq _ _ H). apply H2.
           apply H3.
Qed.

(* characteristic for dependency function *)
Lemma direct_dependency_depfunc: forall (p: Package.t) (q: Package.t),
  direct_dependency p q -> In q (dependency_function p).
Proof.
  intros. destruct H. destruct H. unfold dependency_function.
  induction (List.filter dep_filter (Dependencies p)).
    contradiction.
    simpl. elim H0. 
      intros. apply fold_left_init. intros. apply union_subset_1.
        rewrite (empty_union_1). rewrite H1. apply H. apply empty_is_empty_2.
        reflexivity.
      intros. apply fold_left_init2 with empty. intros. apply union_subset_4.
        apply H2. apply union_subset_1. 
      apply IHl. apply H1.
Qed.

Lemma depfunc_direct_dependency: forall (p: Package.t) (q: Package.t),
  In q (dependency_function p) -> direct_dependency p q.
Proof.
  intros. unfold dependency_function in H. unfold direct_dependency. 
  induction (List.filter dep_filter (Dependencies p)) (* as [] _eqn *).
    simpl in H. absurd (In q empty). rewrite empty_iff. auto. apply H.
    simpl in H. elim (fold_in _ _ _ union_1 H).
      (*1*) intros. rewrite empty_union_1 in H0. exists a. split. apply H0. left. trivial.
      apply empty_is_empty_2. reflexivity.
      (*2*) intros. destruct H0. destruct H0. exists x. split. apply H1. right.
      apply H0. 
Qed.

Add Morphism dependency_function with signature
  Package.eq ==> PackageSet.eq as dependency_function_m.
Proof.
  intros. split.
    intros. apply direct_dependency_depfunc. rewrite <- H.
      apply depfunc_direct_dependency. apply H0.
    intros. apply direct_dependency_depfunc. rewrite H.
      apply depfunc_direct_dependency. apply H0.
Qed.
    
Definition direct_dependency_bool (p q: Package.t) :=
  existsb 
     (mem q)
     (List.filter dep_filter (Dependencies p)).

Lemma dd_ok: forall (p q: Package.t),
  direct_dependency p q <-> Is_true (direct_dependency_bool p q).
Proof.
  intros. split.
    intros. destruct H. destruct H. unfold direct_dependency_bool. 
    apply Is_true_eq_left. 
    destruct (existsb_exists (mem q) (List.filter dep_filter (Dependencies p))). 
      apply H2. exists x. split.
      exact H0. apply mem_1. exact H.
    intros. unfold direct_dependency. unfold direct_dependency_bool in H.
    destruct (existsb_exists (mem q) (List.filter dep_filter (Dependencies p))).
    destruct H0. apply Is_true_eq_true. apply H. destruct H0.
    exists x. split.
      apply mem_2. apply H2.
      apply H0. 
Qed.

Function rev_dependency_path (p q: Package.t)
  (l: list (Package.t)) { struct l }: Prop :=
  match l with
  | nil => direct_dependency p q 
  | h::t => rev_dependency_path p h t /\ direct_dependency h q
  end.

Function rev_dependency_path_in (R: PackageSet.t) (p q: Package.t)
  (l: list (Package.t)) { struct  l}: Prop :=
  match l with
  | nil => In p R /\ In q R /\ direct_dependency p q
  | h::t => In q R /\ rev_dependency_path_in R p h t /\ direct_dependency h q
  end.

Function dependency_path (p q: Package.t) (l: list Package.t)
  { struct l }: Prop :=
  match l with
  | nil => direct_dependency p q
  | h::t => direct_dependency p h /\ dependency_path h q t
  end.

Function dependency_path_in (R: PackageSet.t) (p q: Package.t)
  (l: list (Package.t)) { struct l }: Prop :=
  match l with
  | nil => In p R /\ In q R /\ direct_dependency p q
  | h::t => In p R /\ direct_dependency p h /\ dependency_path_in R h q t 
  end.

Theorem dp_in_dp: forall R p q l,
  dependency_path_in R p q l -> dependency_path p q l.
Proof.
  intros R p q l Hdpi. functional induction (dependency_path_in R p q l).
    simpl. apply Hdpi.
    simpl. split.
      apply Hdpi. apply IHP. apply Hdpi.
Qed.

Function dependency_path_bool (p q: Package.t)
  (l: list (Package.t)) { struct l }: bool :=
  match l with
  | nil => direct_dependency_bool p q
  | h::t => direct_dependency_bool p h && dependency_path_bool h q t
  end.

Theorem dp_ok: 
  forall (p q: Package.t) (l: list (Package.t)),
   dependency_path p q l <-> Is_true (dependency_path_bool p q l).
Proof.
  intros. split.
    intros. functional induction (dependency_path p q l).
      apply -> dd_ok. apply H.
      simpl. apply andb_prop_intro. split.
        apply -> dd_ok. apply H.
        apply IHP. apply H.
    intros. functional induction (dependency_path_bool p q l).
      apply <- dd_ok. apply H.
      simpl. destruct (andb_prop_elim _ _ H). split.
        apply <- dd_ok. apply H0.
        apply IHb. apply H1.
Qed.

Definition dependency (p q: Package.t): Prop :=
  exists l: list (Package.t), dependency_path p q l.

Definition dependency_in (R: PackageSet.t) (p q: Package.t): Prop :=
  exists l: list (Package.t), dependency_path_in R p q l.

Definition rev_dependency_in (R: PackageSet.t) (p q: Package.t): Prop :=
  exists l: list (Package.t), rev_dependency_path_in R p q l.

Lemma dp_R: forall R p q l,
  dependency_path_in R p q l -> In q R.
Proof.
  intros R p q l H. functional induction (dependency_path_in R p q l).
    apply H.
    apply IHP. apply H.
Qed.

Lemma rev_dp_R: forall R p q l,
  rev_dependency_path_in R p q l -> In p R.
Proof.
  intros R p q l H. functional induction (rev_dependency_path_in R p q l).
    apply H.
    apply IHP. apply H.
Qed.

Lemma dp_split: forall R p q r l l',
  dependency_path_in R p q l -> dependency_path_in R q r l' ->
  dependency_path_in R p r (l++(q::l')).
Proof.
  intros. functional induction (dependency_path_in R p q l).
    destruct H. simpl. functional induction (dependency_path_in R q r l').
      destruct H0. split. apply H. split. apply H1. simpl. split. apply H0.
        apply H2.
      destruct H0. destruct H2. simpl. split. apply H. split. apply H1. split.
        apply H0. split. apply H2. apply H3.
    destruct H. destruct H1. simpl. functional induction (dependency_path_in R q r l').
      destruct H0. split. apply H. split. apply H1. apply IHP. apply H2. split.
        apply H0. apply H3.
      destruct H0. destruct H3. split. apply H. split. apply H1. apply IHP.
        apply H2. split. apply H0. split. apply H3. apply H4.
Qed.

Lemma rev_dp_split: forall R p q r l l',
  rev_dependency_path_in R p q l -> rev_dependency_path_in R q r l' ->
  rev_dependency_path_in R p r (l'++(q::l)).
Proof.
  intros. functional induction (rev_dependency_path_in R p q l).
    destruct H. simpl. functional induction (rev_dependency_path_in R q r l').
      destruct H0. split. apply H2. split. simpl. split. apply H. apply H1.
        apply H2.
      destruct H0. destruct H2. simpl. split. apply H0. split. apply IHP.
        apply H2. apply H3.
    destruct H. destruct H1. functional induction (rev_dependency_path_in R q r l').
      destruct H0. split. apply H3. split. simpl. split. apply H. split.
        apply H1. apply H2. apply H3.
      destruct H0. destruct H3. simpl. split. apply H0. split. apply IHP0.
        apply H3. intros. simpl in IHP. apply IHP. apply H5. split. apply H0.
        split. apply H6. apply H4. apply H4.
Qed.
      
Lemma dep_other_dep: forall R p q,
  rev_dependency_in R p q <-> dependency_in R p q.
Proof.
  intros. split.
    intros. destruct H as [l Hl]. exists (rev l).
    functional induction (rev_dependency_path_in R p q l).
      simpl. exact Hl.
      simpl. destruct Hl as [Hq [Hrdpi Hdd]].
    apply dp_split. apply IHP. apply Hrdpi. simpl. split.
      apply dp_R with p (rev t0). apply IHP. apply Hrdpi. split. apply Hq.
      apply Hdd.
  intros. destruct H as [l Hl]. exists (rev l).
  functional induction (dependency_path_in R p q l).
    simpl. exact Hl.
    simpl. destruct Hl as [Hq [Hdd Hdpi]].
  apply rev_dp_split. simpl. split. apply Hq. split.
    apply rev_dp_R with q (rev t0). apply IHP. apply Hdpi. apply Hdd.
    apply IHP. apply Hdpi. 
Qed.      

Lemma dependency_in_R: forall R p q,
  rev_dependency_in R p q -> In q R.
Proof.
  intros R p q Hdep. unfold dependency_in in Hdep. destruct Hdep as [l Hdp].
  functional induction (dependency_path_in R p q l). 
    destruct Hdp. apply H0.
    simpl in Hdp. destruct Hdp as [Hq _]. assumption.
Qed.

Lemma dependency_in_dependency: forall R p q,
  dependency_in R p q -> dependency p q.
Proof.
  intros R p q Hdpi. unfold dependency_in in Hdpi. destruct Hdpi as [l Hdpi].
  functional induction (dependency_path_in R q p l).
    simpl in Hdpi. exists nil. simpl. apply Hdpi.
    simpl in Hdpi. destruct Hdpi as [_ [Hdd Hdpi]].
      exists (h::t0). simpl. split.
        apply Hdd.
        apply dp_in_dp with R. apply Hdpi.
Qed. 
      
Lemma dependency_compat_eq: forall p q x,
  Package.eq p q -> (dependency p x <-> dependency q x).
Proof.
  intros. unfold dependency. split.
    intros. destruct H0. exists x0. generalize x H0. clear H0 x. destruct x0.
      intros. simpl. simpl in H0. rewrite <- H. apply H0.
      intros. simpl. split. elim H0. intros. rewrite <- H. apply H1. 
      destruct H0. apply H1.
    intros. destruct H0. exists x0. generalize x H0. clear H0 x. destruct x0.
      intros. simpl. simpl in H0. rewrite H. apply H0.
      intros. simpl. split. elim H0. intros. rewrite H. apply H1. 
      destruct H0. apply H1.
Qed.

Add Morphism dependency with signature Package.eq ==> Package.eq ==> iff
  as dependency_m.
Proof.
  intros. unfold dependency. split.
    intros. destruct H1.
      exists x1. generalize y H H1. clear H1 H y.
      functional induction (dependency_path x x0 x1).
        intros. simpl. rewrite <- H. rewrite <- H0. apply H1.
        intros. simpl. split.
          rewrite <- H. apply H1.
          apply (IHP H0 h (Package.eq_refl h)). apply H1. 
    intros. destruct H1.
      exists x1. generalize x H H1. clear H1 H x.
      functional induction (dependency_path y y0 x1).
        intros. simpl. rewrite H. rewrite H0. apply H1.
        intros. simpl. split.
          rewrite H. apply H1.
          apply (IHP H0 h (Package.eq_refl h)). apply H1.
Qed.      
       
Theorem dependency_trans:
  forall (p q r: Package.t), dependency p q -> dependency q r -> dependency p r.
Proof.
  intros p q r Hpq Hqr. destruct Hpq as [l Hl].
  functional induction (dependency_path p q l).
    destruct Hqr as [l' Hl']. functional induction (dependency_path q r l').
      exists (p0::nil). split. apply Hl. apply Hl'.
      exists (p0::h::t0). split. apply Hl. apply Hl'.
   destruct Hl as [Hph Hhq]. destruct (IHP Hhq Hqr). 
     exists (h::x). split. apply Hph. apply H. 
Qed.

Definition dependencies (P: PackageSet.t): PackageSet.t :=
  fold (fun p acc =>
   union (dependency_function p) acc
  ) P P.

Lemma dependencies_compat_eq: 
   compat_op E.eq Equal (fun p acc => union (dependency_function p) acc).
Proof.
  unfold compat_op. simpl_relation. rewrite H0. rewrite H.
  reflexivity.
Qed.
    
Lemma dependencies_transpose:
   transpose Equal (fun p acc => union (dependency_function p) acc). 
Proof.
  intros. unfold transpose. intros. split.
     intros. elim (union_1 H).
        intros. apply union_3. apply union_2. apply H0.
        intros. elim (union_1 H0). 
           intros. apply union_2. apply H1.
           intros. apply union_3. apply union_3. apply H1.
     intros. elim (union_1 H).
        intros. apply union_3. apply union_2. apply H0.
        intros. elim (union_1 H0). 
           intros. apply union_2. apply H1. 
           intros. apply union_3. apply union_3. apply H1.
Qed.

(* characteristic functions *)
Lemma dependencies_dependency:
  forall (q: Package.t) (P: PackageSet.t),
  In q (dependencies P) -> In q P \/ Exists (fun p => direct_dependency p q) P.
Proof.
  intros q P H. unfold dependencies in H. induction P using set_induction.
    rewrite (Props.fold_1 _ (s:=P) _ _ H0) in H. left. apply H.
    rewrite (Props.fold_2 _ (s:=P1) _ dependencies_compat_eq dependencies_transpose H0 H1) in H.  
    simpl in H. elim (union_1 H).
      (*1*) intros. right. exists x. split. 
      elim (H1 x). intros. apply H4. left. reflexivity.
      apply depfunc_direct_dependency. apply H2.
      (*2*) intros. assert (P2 [=] add x P1). apply -> Add_Equal. apply H1.
      rewrite (fold_init dependencies_compat_eq _ H3) in H2.
        rewrite (fold_init_add _ _ _ dependencies_compat_eq dependencies_transpose) in H2.
      destruct (add_inv H2).
        left. apply (H1 q). left. apply H4.
        destruct (IHP1 H4).
          left. destruct (H1 q). apply H7. right. apply H5.
          right. destruct H5. destruct H5. exists x0. split. destruct (H1 x0).
            apply H8. right. apply H5. apply H6.
        intros. rewrite union_sym. rewrite (union_sym _ P). apply union_add.
        intros. rewrite H4. reflexivity.
Qed.
             
Lemma dependency_dependencies:
  forall (q: Package.t) (P: PackageSet.t),
  Exists (fun p => direct_dependency p q) P -> In q (dependencies P).
Proof.
  intros q P H. destruct H. destruct H. unfold dependencies. 
  induction P using set_induction.
    absurd (In x P). apply H1. apply H.
    assert (P2 [=] add x0 P1). apply -> Add_Equal. apply H2.
    rewrite (fold_init dependencies_compat_eq _ H3).
    rewrite (fold_init_add _ _ _ dependencies_compat_eq dependencies_transpose).
    apply <- add_iff. right. 
    rewrite (fold_equal _ dependencies_compat_eq dependencies_transpose _ H3). 
    rewrite (fold_add _ dependencies_compat_eq dependencies_transpose).
    destruct (H2 x). destruct (H4 H). 
      apply union_2. rewrite H6. apply direct_dependency_depfunc. apply H0.
      apply union_3. apply IHP1. apply H6.
    apply H1.
    intros. rewrite union_sym. rewrite (union_sym _ P). apply union_add.
    intros. rewrite H4. reflexivity.
Qed.

Lemma dependencies_monotone: forall (P: PackageSet.t) ,
  P [<=] dependencies P.
Proof.
  intros. unfold Subset. intros. unfold dependencies. 
  apply (fold_in_init dependencies_compat_eq dependencies_transpose). 
    intros. apply union_subset_2. apply H.
Qed.

Lemma dependencies_subset: forall (P Q: PackageSet.t), P [<=] Q -> dependencies P [<=] dependencies Q.
Proof.
  intros. unfold Subset. intros. destruct (dependencies_dependency a P H0). 
    apply dependencies_monotone. apply H. apply H1.
    destruct H1 as [x [Hx1 Hx2]]. apply dependency_dependencies. exists x. split. apply H. apply Hx1. apply Hx2.
Qed. 
       
Add Morphism dependencies with signature
  PackageSet.eq ==> PackageSet.eq as dependencies_m.
Proof.
  intros. split. 
    intros. destruct (dependencies_dependency _ _ H0).
      apply dependencies_monotone. rewrite <- H. apply H1.
      destruct H1. destruct H1. apply dependency_dependencies. exists x0. split.
        rewrite <- H. apply H1. 
        apply H2.
    intros. destruct (dependencies_dependency _ _ H0).
      apply dependencies_monotone. rewrite H. apply H1.
      destruct H1. destruct H1. apply dependency_dependencies. exists x0. split.
        rewrite  H. apply H1. 
        apply H2.    
Qed.

Lemma bla3: forall n a b: nat, n >= b -> b > a -> n - b < n - a.
Proof.
  intros. omega.
Qed.

Require Import Recdef.

Variable R: PackageSet.t.

Function cone (P: {x : PackageSet.t | x [<=] R})
  { measure (fun x => cardinal R - cardinal (proj1_sig P)) P }: PackageSet.t :=
  if equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)
  then (proj1_sig P)
  else
    cone (exist (fun v => v [<=] R) (inter R (dependencies (proj1_sig P)))
    (fun a => inter_subset_1 (s:=R) (s':=dependencies (proj1_sig P)) (a:=a))).
Proof.
  intros. destruct P as [P HP]. simpl. simpl in teq. 
  apply bla3. apply subset_cardinal. apply inter_subset_1.
  apply strict_subset_cardinal. split.
    apply inter_subset_3. apply HP. apply dependencies_monotone.
    intro. apply eq_true_false_abs with (equal (inter R (dependencies P)) P).
      apply -> equal_iff. symmetry. apply H.
      apply teq.
Qed.

Lemma iter_cone_monotone: forall P n,
  iter ({x : t | x [<=] R} -> t) n cone_F (fun v => proj1_sig v) P [<=]
  iter ({x : t | x [<=] R} -> t) (S n) cone_F (fun v => proj1_sig v) P.
Proof.
  intros P n H. generalize P. clear P. induction n.
    intros P H0. simpl. simpl in H0. unfold cone_F.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
      intros Heq. rewrite <- (proj2 (iff_and (equal_iff (inter R (dependencies (proj1_sig P))) (proj1_sig P))) Heq).
      apply inter_3.
        apply (proj2_sig P). apply H0.
        apply dependencies_monotone. apply H0.
      intros Hneq. simpl. apply inter_3.
        apply (proj2_sig P). apply H0.
        apply dependencies_monotone. apply H0.
   intros P Hn. replace (iter ({x : t | x [<=] R} -> t) (S (S n)) cone_F (fun v => proj1_sig v) P) with
     (cone_F (iter ({x : t | x [<=] R} -> t) (S n) cone_F (fun v => proj1_sig v)) P).
   simpl iter in Hn. unfold cone_F at 1. unfold cone_F at 1 in Hn.
   case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
     intros. rewrite H0 in Hn. apply Hn.
     intros. rewrite H0 in Hn. clear H0. apply IHn. apply Hn.
   trivial.
Qed.

Lemma iter_cone_expanding:
  forall P k n, k <= n ->
  iter ({x | x [<=] R} -> t) k cone_F (fun v => proj1_sig v) P [<=]
  iter ({x | x [<=] R} -> t) n cone_F (fun v => proj1_sig v) P.
Proof.
  intros. induction n.
    replace k with 0. simpl. reflexivity. apply le_n_O_eq. assumption.
    elim (le_lt_or_eq _ _ H). 
      intros. transitivity (iter ({x : t | x [<=] R} -> t) n cone_F (fun v => proj1_sig v) P).
      apply IHn. apply lt_n_Sm_le. apply H0. apply iter_cone_monotone.
      intros. rewrite H0. reflexivity.
Qed.

Lemma dep_path_iter: forall P p q n,
  In p (proj1_sig P) -> dependency_path_in R p q n ->
  In q (iter ({x | x [<=] R} -> t) (S (length n)) cone_F (fun v => proj1_sig v) P).
Proof.
  intros P p q n Hp Hdpi. generalize P Hp. clear Hp P.
  functional induction (dependency_path_in R p q n).
    intros P Hp. simpl. unfold cone_F.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
      intros. rewrite <- (proj2 (iff_and (equal_iff (inter R (dependencies (proj1_sig P))) (proj1_sig P))) H).
      apply inter_3. apply Hdpi. apply dependency_dependencies. exists p.
        split. apply Hp. apply Hdpi.
      intros. apply inter_3. apply Hdpi. apply dependency_dependencies. exists p.
        split. apply Hp. apply Hdpi.
    intros P Hp. simpl. unfold cone_F at 1.
    assert (In q (cone_F (iter ({x | x [<=] R} -> t) (length t1) cone_F (fun v => proj1_sig v)) (exist (fun v => v [<=] R) (inter R (dependencies (proj1_sig P)))
     (fun a => inter_subset_1 (a:=a))))).
      apply IHP. apply Hdpi. simpl. apply inter_3. 
      destruct Hdpi as [_ [Hdd Hodpi]]. destruct t1. simpl in Hodpi. apply Hodpi. 
        simpl in Hodpi. apply Hodpi.
      apply dependency_dependencies. exists p. split. apply Hp. apply Hdpi. 
      case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)).
        intros. unfold cone_F at 1 in H. simpl in H. 
        replace (equal (inter R (dependencies (inter R (dependencies (proj1_sig P))))) (inter R (dependencies (proj1_sig P)))) with true in H.
          rewrite (proj2 (iff_and (equal_iff (inter R (dependencies (proj1_sig P))) (proj1_sig P))) H0) in H. apply H.
          rewrite (proj2 (iff_and (equal_iff (inter R (dependencies (proj1_sig P))) (proj1_sig P))) H0).
          symmetry. apply H0.
        intros. apply H.
Qed.

Lemma not_lt_le: forall a b: nat, ~a < b -> b <= a.
Proof.
  intros a b. omega.
Qed.

Lemma cone_subset: forall (P: PackageSet.t | P [<=] R),
  (proj1_sig P) [<=] cone P.
Proof.
  intros. unfold Subset. intros q Hq.
  unfold cone. destruct cone_terminate. destruct e. 
  rewrite <- (H (S x0) (lt_n_Sn x0) (fun v => proj1_sig v)).
    simpl. unfold cone_F at 1.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
      intros. apply Hq.
      intros. apply iter_cone_expanding with 0. apply le_O_n.
      simpl. apply inter_3.
        apply (proj2_sig P). apply Hq.
        apply dependencies_monotone. apply Hq.
Qed.

Lemma dep_cone: forall (P: PackageSet.t | P [<=] R) q,
  Exists (fun p => dependency_in R p q) (proj1_sig P) -> In q (cone P).
Proof.
  intros P q H.
  destruct H as [p [Hp Hdi]]. destruct Hdi as [l Hdpi].
  functional induction (dependency_path_in R p q l).
    destruct Hdpi as [_ [Hq Hdd]].
    unfold cone. destruct cone_terminate. destruct e.
    rewrite <- (H (S x0) (lt_n_Sn x0) (fun v => proj1_sig v)). clear H.
    apply iter_cone_expanding with 1. apply  le_n_S. apply le_O_n. 
    simpl. unfold cone_F.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
      intros. rewrite <- (proj2 (iff_and (equal_iff (inter R (dependencies (proj1_sig P))) (proj1_sig P))) H).
        apply inter_3. apply Hq. apply dependency_dependencies. exists p. split.
          apply Hp. apply Hdd.
        intros. apply inter_3. apply Hq. apply dependency_dependencies. exists p.
          split. apply Hp. apply Hdd.
    destruct Hdpi as [Hq [Hdpi Hdd]]. 
    (* unfold cone in IHP0. destruct cone_terminate in IHP0. destruct e. *)
    unfold cone. destruct cone_terminate. destruct e as [y Hy].
    destruct (dec_lt y (S (length (h::t1)))).
      rewrite <- (Hy (S (length (h::t1))) H (fun v => proj1_sig v)).
        clear H Hy y.
      apply dep_path_iter with p. apply Hp. simpl. split. 
      apply (proj2_sig P). apply Hp. split. apply Hdpi. apply Hdd.    
      rewrite <- (Hy (S y) (lt_n_Sn y) (fun v => proj1_sig v)).
      apply iter_cone_expanding with (S (length (h::t1))).
      apply le_trans with y. apply not_lt_le. apply H. apply le_n_Sn.  
      apply dep_path_iter with p. apply Hp. simpl. split.
      apply (proj2_sig P). apply Hp. split. apply Hdpi. apply Hdd.
Qed.

Lemma cone_dep: forall P q, In q (cone P) ->
   In q (proj1_sig P) \/ Exists (fun p => dependency_in R p q) (proj1_sig P). 
Proof. 
  intros P q. intros H. unfold cone in H. destruct cone_terminate in H.
    destruct e.
  rewrite <- (H0 (S x0) (lt_n_Sn x0) (fun v => proj1_sig v)) in H. clear H0.
  generalize P H. clear H P. induction x0. 
    intros P H. simpl in H. unfold cone_F in H.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)). 
      intros Heq. rewrite Heq in H. left. apply H.
      intros Hneq. rewrite Hneq in H. simpl in H.
      destruct (dependencies_dependency _ _ (inter_2 H)).
        left. apply H0.
        right. destruct H0 as [p Hp]. exists p. split. apply Hp. exists nil.
          simpl. split.
        apply (proj2_sig P). apply Hp. split. apply (inter_1 H). apply Hp.
    intros P H. simpl in H. unfold cone_F in H.
    case_eq (equal (inter R (dependencies (proj1_sig P))) (proj1_sig P)).
      intros Heq. rewrite Heq in H. left. apply H.
      intros Hneq. rewrite Hneq in H. destruct (IHx0 (exist (fun v => v [<=] R)
        (inter R (dependencies (proj1_sig P)))
        (fun a => inter_subset_1 (a:=a)))). apply H.
      clear Hneq H. simpl in H0. 
        destruct (dependencies_dependency _ _ (inter_2 H0)).
          left. apply H.
          right. destruct H as [p Hp]. exists p. split. apply Hp. exists nil.
            simpl. split.
          apply (proj2_sig P). apply Hp. split. apply (inter_1 H0). apply Hp.
        right. destruct H0 as [p Hp]. simpl in Hp. destruct Hp as [Hdd Hodpi].
          destruct (dependencies_dependency _ _(inter_2 Hdd)).
          exists p. split. apply H0. apply Hodpi.
      clear Hneq H. destruct H0. destruct H.
      exists x1. split. apply H. destruct Hodpi.
        exists (p::x2). simpl. split. 
        apply (proj2_sig P). apply H. split. apply H0. apply H1.
Qed.

Lemma cone_subset_R: forall (P: PackageSet.t | P [<=] R),
  cone P [<=] R.
Proof.
  intros. intros a H. destruct (cone_dep P a H).
    apply (proj2_sig P). apply H0.
    destruct H0. destruct H0. 
    destruct H1. apply (dp_R _ _ _ _ H1).
Qed.
 
Lemma cone_of_subset_is_subset: forall (P1: PackageSet.t | P1 [<=] R)
  (P2: PackageSet.t | P2 [<=] R),
  (proj1_sig P1) [<=] (proj1_sig P2) -> cone P1 [<=] cone P2.
Proof.
  destruct P1 as [P1 HP1]. destruct P2 as [P2 HP2]. simpl. intros. unfold Subset.
  intros. elim (cone_dep (exist (fun v => v [<=] R) P1 HP1) a H0).
    intros. apply cone_subset. apply H. apply H1.
    intros. apply dep_cone. destruct H1. exists x. split. apply H. apply H1.
      apply H1.
Qed.

End dep_cone_stuff.
