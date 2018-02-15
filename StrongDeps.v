Set Implicit Arguments.

Require Import Decidable.
Require Import Arith.
Require Import Program.
Require Import Packages.
Require Import MGraph.
Require Import Verifier.
Require Import Classical_Prop.

Module Import DepGraph := DiGraph PackageSet.
Import PackageSet.
Import PAux.Props.
Module Import PAux := Aux PackageSet.

Definition conj_cone_of (R: PackageSet.t) (P: PackageSet.t | P [<=] R): PackageSet.t :=
  cone_of Dependencies is_conjunctive_bool R P.

Lemma add_edge_vinv: forall g v v' v'',
  IsVertex v (add_edge (v', v'') g) ->
  IsVertex v g \/ Package.eq v v' \/ Package.eq v v''.
Proof.
  intros. elim (Package.eq_dec v v'). 
    intros. right. left. apply a.
    intros. elim (Package.eq_dec v v'').
      intros. right. right. apply a.
    intros. left. apply add_edge_v4 with v' v''.
      apply b.
      apply b0. 
      apply H. 
Qed.

Lemma add_edge_inv: forall g e e',
  IsEdge e' (add_edge e g) ->
  IsEdge e' g \/ Edges.E.eq e e'.
Proof.
  intros. elim (Edges.E.eq_dec e e'). 
    intros. right. apply a.
    intros. left. apply add_edge_3 with e. intro.  apply b. apply Edge.eq_sym. apply H0. apply H. 
Qed.

Lemma cpl: forall p,
  compat_op Package.eq DepGraph.eq
           (fun (p' : elt) (acc : DepGraph.t) =>
            if Props.Dec.F.eq_dec p p' then acc else add_edge (p, p') acc).
Proof.
  intros. unfold compat_op. intros. 
  elim (Props.Dec.F.eq_dec p x). 
    elim (Props.Dec.F.eq_dec p x'). 
      intros. apply H0.
      intros. absurd (~Package.eq p x'). intro. apply H1.
      rewrite <- H. apply a. apply b.
    elim (Props.Dec.F.eq_dec p x'). 
      intros. absurd (~Package.eq p x). intro. apply H1. 
      rewrite H. apply a. apply b.
      intros. split.
        intros. split. intros. elim (add_edge_vinv H1). 
        intros. rewrite H0 in H2. apply add_edge_v1. apply H2.
      intros. elim H2. 
        intros. rewrite H3. apply add_edge_v2.
        intros. rewrite H3. rewrite H. apply add_edge_v3.
      intros. elim (add_edge_vinv H1). 
        intros. rewrite <- H0 in H2. apply add_edge_v1. apply H2.
      intros. elim H2.
        intros. rewrite H3. apply add_edge_v2.
        intros. rewrite H3. rewrite <- H. apply add_edge_v3.
      intros. assert (Edges.E.eq (p,x) (p,x')).
        split.
          simpl. reflexivity.
          simpl. apply H.
        split.
          intros. elim (add_edge_inv H2).
            intros. apply add_edge_2. rewrite <- H0. apply H3.
            intros. apply add_edge_1. rewrite <- H1. apply H3.
          intros. elim (add_edge_inv H2). 
            intros. apply add_edge_2. rewrite H0. apply H3.
            intros. apply add_edge_1. rewrite H1. apply H3.
Qed.

Lemma tpl: forall p,
  transpose DepGraph.Equal
    (fun (p' : elt) (acc : DepGraph.t) =>
    if Props.Dec.F.eq_dec p p' then acc else add_edge (p, p') acc).
Proof.
  intros. unfold transpose. intros.
  split.
    intros.
      elim (Props.Dec.F.eq_dec p x).
         elim (Props.Dec.F.eq_dec p y).
           intros. reflexivity.
           intros. reflexivity.
         elim (Props.Dec.F.eq_dec p y).  
           intros. reflexivity.
           intros. split.
             intros. elim (add_edge_vinv H). 
             intros. elim (add_edge_vinv H0).
             intros. apply add_edge_v1. apply add_edge_v1. apply H1.
             intros. elim H1. 
               intros. rewrite H2. apply add_edge_v1. apply add_edge_v2.
               intros. rewrite H2. apply add_edge_v3.
             intros. elim H0.
             intros. rewrite H1. apply add_edge_v2.
             intros. rewrite H1. apply add_edge_v1. apply add_edge_v3.
             intros. elim (add_edge_vinv H).
             intros. elim (add_edge_vinv H0).
             intros. apply add_edge_v1. apply add_edge_v1. apply H1.
             intros. elim H1. 
               intros. rewrite H2. apply add_edge_v1. apply add_edge_v2.
               intros. rewrite H2. apply add_edge_v3. 
             intros. elim H0.
             intros. rewrite H1. apply add_edge_v2.
             intros. rewrite H1. apply add_edge_v1. apply add_edge_v3.
  intros. elim (Props.Dec.F.eq_dec p x). 
    elim (Props.Dec.F.eq_dec p y). 
      intros. reflexivity.
      intros. reflexivity.
    elim (Props.Dec.F.eq_dec p y). 
      intros. reflexivity.
      intros. split.
        intros. elim (add_edge_inv H). 
          intros. elim (add_edge_inv H0). 
            intros. apply add_edge_2. apply add_edge_2. apply H1.
            intros. apply add_edge_1. apply H1.
          intros. apply add_edge_2. apply add_edge_1. apply H0.
        intros. elim (add_edge_inv H). 
          intros. elim (add_edge_inv H0). 
            intros. apply add_edge_2. apply add_edge_2. apply H1.
            intros. apply add_edge_1. apply H1.
          intros. apply add_edge_2. apply add_edge_1. apply H0.
Qed.
              
Lemma bla: forall p q P,
  (* In p P -> *)
  IsEdge (p, q) (PackageSet.fold (fun p' acc => if Package.eq_dec p p' then acc else add_edge (p, p') acc) P DepGraph.empty) -> ~Package.eq p q.
Proof.
  intros. induction P using set_induction.
  rewrite (fold_1 DepGraph.EqualSetoid) in H. intro. apply empty_edge with (p, q). apply H.
    apply H0.
  rewrite (fold_2 DepGraph.EqualSetoid _ (cpl p) (tpl p) H0 H1) in H.
  elim (Package.eq_dec x q).
  intros. generalize H. clear H. elim (Props.Dec.F.eq_dec p x). 
    intros. apply (IHP1 H).
    intros. intro. apply b. rewrite a. rewrite H2. reflexivity.
    intros. generalize H. clear H. elim (Props.Dec.F.eq_dec p x). 
    intros. apply (IHP1 H). 
    intros. apply IHP1. apply add_edge_3 with (p, x). intro. apply b. inversion H2. 
    simpl in H4. symmetry. apply H4. apply H.
Qed.

Lemma bla2: forall (f: Package.t -> DepGraph.t -> DepGraph.t) Z p q,
  (compat_op Package.eq DepGraph.Equal f) ->
  (transpose DepGraph.Equal f) ->
  (forall x g p q, IsEdge (p, q) (f x g) -> IsEdge (p, q) g \/ Package.eq x q) ->
  IsEdge (p, q) (fold f Z DepGraph.empty) ->
  Exists (fun s => Package.eq s  q) Z.
Proof.
  intros. induction Z using set_induction.
   rewrite (fold_1 DepGraph.EqualSetoid) in H2. absurd (IsEdge (p, q) DepGraph.empty). 
     apply empty_edge. apply H2. apply H3.
   rewrite (fold_2 DepGraph.EqualSetoid _ H H0 H3 H4) in H2.
   elim H1 with x (fold f Z1 DepGraph.empty) p q. intros.
     elim (IHZ1 H5). intros. exists x0. destruct H6. split.
     elim (H4 x0). intros. apply H9. right. apply H6.
     apply H7.
     intros. unfold Exists. exists x. split. elim (H4 x). intros.
     apply H7. left. reflexivity. apply H5.
   apply H2.
Qed.   

Lemma not_empty_add:
  forall S: PackageSet.t, ~Empty S ->
    exists x: Package.t, exists S': PackageSet.t,
      ~In x S' /\ Add x S' S.
Proof.
  intros. induction S using set_induction.
  absurd (Empty S). apply H. apply H0.
  exists x S1. split. apply H0. apply H1.
Qed.

Lemma bla3: forall p v S,
  ~Package.eq p v -> In v S ->  
  IsEdge (p, v) (fold (fun p' acc => if Props.Dec.F.eq_dec p p' then acc else add_edge (p, p') acc)
     S DepGraph.empty).
Proof.
  intros. induction S using set_induction.
  rewrite (fold_1 DepGraph.EqualSetoid). 
    absurd (In v S). apply H1. apply H0. apply H1.
  rewrite (fold_2 DepGraph.EqualSetoid _ (cpl p) (tpl p) H1 H2). 
  elim (H2 v). intros. elim (H3 H0). intros.
    elim (Package.eq_dec p x).
      intros. absurd (Package.eq p x). 
      intro. apply H. rewrite a. exact H5.
      exact a.
      intros. apply add_edge_1. unfold Edge.eq. split. simpl. reflexivity. simpl. apply H5.
    intros. elim (Package.eq_dec p x).
      intros. apply IHS1. apply H5.
      intros. apply add_edge_2. apply IHS1. apply H5.
Qed.
 
Program Definition add_conj_edges
  (R: PackageSet.t) (p: Package.t | In p R):
  { G: DepGraph.t | 
    forall v: DepGraph.vertex, DepGraph.IsEdge (p, v) G <-> 
    conjunctive_dependency R p v /\ ~Package.eq p v } :=
PackageSet.fold (fun p' acc =>
  if Package.eq_dec p p' then acc else DepGraph.add_edge (p, p') acc
) (conj_cone_of (exist (fun P => P [<=] R) (singleton p) (PkgDefinitions.PAux.s_ss (proj2_sig p)))) DepGraph.empty.
Obligation 1.
  split.
  (* edge -> cjd *) intros.
     split. elim (cone_in_dep Dependencies is_conjunctive_bool R (exist (fun x => In x R) p H) v). 
     trivial.
     (* p = v; absurd because of fold cond *) intros. simpl in H1.
       absurd (Package.eq p v). apply bla with (conj_cone_of (exist (fun P => P [<=] R) (singleton p) (PkgDefinitions.PAux.s_ss (proj2_sig (exist (fun p => In p R) p H))))).
       apply H0. apply H1.
     simpl. simpl in H0. elim bla2 with
      (fun p' acc => if Props.Dec.F.eq_dec p p' then acc else add_edge (p, p') acc)
      (conj_cone_of (exist (fun P => P [<=] R) (singleton p) (PkgDefinitions.PAux.s_ss H)))
      p v.
     intros. destruct H1. rewrite <- H2. unfold conj_cone_of in H1. apply H1.
     apply cpl.
     apply tpl.
     intros x g p0 q. elim (Props.Dec.F.eq_dec p x). 
       intros. left. apply H1.
       intros. elim (add_edge_inv H1).
         intros. left. apply H2.
         intros. destruct H2. simpl in H3. right. apply H3.
     apply H0.
     apply (bla H0).  
   (* cjd -> edge *) intros. simpl.
   destruct H0. apply bla3.
   apply H1.
   apply (dep_in_cone Dependencies is_conjunctive_bool R (exist (fun x => In x R) p H) v H0). 
Qed.

Program Lemma cpb_trim: forall R C, compat_bool Package.eq (fun p => negb (is_empty ((verify R C p (install_function R C p))))).
Proof.
  intros. unfold compat_bool. intros.
  apply eq_bool_prop_intro. split.
    intros. apply negb_prop_intro. intro.
    elim (negb_prop_elim (is_empty (proj1_sig (verify R C x (install_function R C x))))).
    apply H0.
    apply Is_true_eq_left. apply is_empty_1. rewrite (verify_eq R C H (install_function_eq R C x y)).
    apply is_empty_2. apply Is_true_eq_true. apply H1.
    intros. apply negb_prop_intro. intro.
    elim (negb_prop_elim (is_empty (proj1_sig (verify R C y (install_function R C y))))).
    apply H0.
    apply Is_true_eq_left. apply is_empty_1. rewrite (verify_eq R C (Package.eq_sym H) (install_function_eq R C y x)).
    apply is_empty_2. apply Is_true_eq_true. apply H1.
Qed.
        
Program Definition trim (R: PackageSet.t) (C: ConflictSet.t):
  { Rt: PackageSet.t | forall p: Package.t,
    In p Rt -> exists I, I [<=] R /\ is_install_set p R C I } :=
  PackageSet.filter (fun p => negb (is_empty (verify R C p (install_function R C p)))) R.
Obligation 1.
  assert (~Empty (proj1_sig `(verify R C p (install_function R C p)))). 
  intro. apply (negb_prop_elim (is_empty (proj1_sig `(verify R C p (install_function R C p))))). 
    apply Is_true_eq_left. apply (filter_2 (cpb_trim R C) H).
    apply Is_true_eq_left. apply is_empty_1. apply H0.
    exists (proj1_sig (verify R C p (install_function R C p))).
    split.
    elim (verify R C p (install_function R C p)). simpl.
    intros. elim p0. intros. rewrite (empty_is_empty_1 H1). apply subset_empty. 
    intros. unfold is_install_set in H1. destruct H1. destruct H2. apply H2.
    generalize H0. clear H0. elim (verify R C p (install_function R C p)). simpl. 
    intros. elim p0. intros. contradiction.
    intros. apply H1.
Qed.

Module EAux := Aux DepGraph.Edges.

Program Definition create_graph_strong_deps 
  (R: PackageSet.t) (C: ConflictSet.t):
  { G: DepGraph.t |
     forall (p q: DepGraph.vertex), DepGraph.IsEdge (p, q) G <->
     strong_dep R C p q /\ ~Package.eq p q } :=
  PackageSet.fold (fun p_id acc => 
     let is := verify R C p_id (install_function R C p_id) in
     if (empty_dec is) then
       acc
     else 
       PackageSet.fold (fun p' acc' =>
         if (IsEdge_dec (p_id, p') acc') then
           acc
         else
           (if (bool_dec (strong_dep_function R C p_id p') true) then
              add_edge (p_id, p') acc'
            else
              acc'
           ) 
       ) is acc
  ) (trim R C) DepGraph.empty.
Obligation 1.
  induction R using set_induction.
    (* R is empty *) assert (Empty (proj1_sig (trim R C))).
      intro. intro. apply (H a). apply (filter_1 (cpb_trim R C)). apply H0.
    rewrite (fold_1 _ DepGraph.empty _ H0). split.
      intros. absurd (IsEdge (p, q) DepGraph.empty). apply empty_edge. apply H1.
      intros. absurd (strong_dep R C p q).
        intro. destruct H2. elim H2. intros. absurd (is_install_set p R C x). 
          intro. destruct H5. destruct H6. unfold Subset in H6. apply (H p). apply H6. apply H5.
          apply H4. destruct H1. apply H1.
(*    (* R = R2 = R1 + x *) assert (~In x (proj1_sig (trim R1 C))). 
        intro. apply H. apply (filter_1 (cpb_trim R1 C)). apply H1. *)
    rewrite (fold_2 (x:=x) (s:=proj1_sig (trim R1 C)) (s':=proj1_sig (trim R2 C))). 
      split. elim (empty_dec (proj1_sig (verify R2 C x (install_function R2 C x)))).
      intros. split. split. 
    
           
      
      
Unset Implicit Arguments.
 