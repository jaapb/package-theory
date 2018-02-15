Set Implicit Arguments.

Require Import Decidable.
Require Import Bool.
Require Import Arith.
Require Export MSetInterface.
Require Export MSetProperties.
(* Require Export Iteration. *)

Module Aux (M: S).

Import M.

Module Props := Properties M.
Import Props.
Module Facts := Props.FM.
Import Facts.

Theorem compat_bool_mem: forall S: M.t, compat_bool E.eq (fun q => mem q S).
Proof.
  intros. unfold compat_bool. simpl_relation. elim Props.In_dec with x S. 
    intros. replace (mem x S) with true. replace (mem y S) with true. reflexivity.
      symmetry. apply mem_1. apply In_1 with x. apply H. apply a.
      symmetry. apply mem_1. apply a.
    intros. replace (mem x S) with false. replace (mem y S) with false. reflexivity.
      symmetry. apply not_true_is_false. intro. apply b. apply In_1 with y. symmetry. apply H. apply mem_2. apply H0.
      symmetry. apply not_true_is_false. intro. apply b. apply mem_2. apply H0.
Qed.

Theorem compat_bool_and: forall (S: M.t) (f g: M.E.t -> bool),
   compat_bool E.eq f -> compat_bool E.eq g -> compat_bool E.eq (fun q => f q && g q).
Proof.
   intros. unfold compat_bool. simpl_relation. 
     elim (H x y H1). elim (H0 x y H1). reflexivity.
Qed.

Theorem compat_bool_existsb: forall (f: E.t -> M.t -> bool) (l: list (M.t)),
  (forall S: M.t, compat_bool E.eq (fun p => f p S)) -> compat_bool E.eq (fun p => existsb (f p) l).
Proof.
  intros. unfold compat_bool. simpl_relation.
  induction l. 
     simpl. trivial.
     simpl. apply eq_bool_prop_intro. split.
        intros. apply orb_prop_intro. elim (orb_prop_elim (f x a) (existsb (f x) l)).
           intros. left. rewrite (H a y x). apply H2. symmetry. apply H0.
           intros. right. rewrite <- IHl. apply H2.  
           apply H1.
        intros. apply orb_prop_intro. elim (orb_prop_elim (f y a) (existsb (f y) l)).
            intros. left. rewrite (H a x y). apply H2. apply H0.
            intros. right. rewrite IHl. apply H2.
           apply H1.
Qed.

Lemma and_sum: forall A B, ({A} + {~A}) -> ({B} + {~B}) ->
  {A /\ B} + {~(A /\ B)}.
Proof.
  intros. destruct H. destruct H0.
    left. split. apply a. apply b.
    right. intro. apply n. apply (proj2 H).
    right. intro. apply n. apply (proj1 H).
Qed.

Lemma not_sum: forall A, ({A} + {~A}) -> 
  {~A} + {~~A}.
Proof.
  intros. destruct H. 
    right. intro. apply H. apply a.
    left. apply n.
Qed.

Theorem Forall_dec: forall (S: M.t) (P: M.E.t -> Prop),
   (forall c: M.E.t, (P c) + {~P c}) -> compat_P E.eq P ->
   {For_all (fun c => P c) S} + {~For_all (fun c => P c) S}.
Proof.
  intros. induction S using Props.set_induction. 
    left. unfold For_all. intros. absurd (In x S). apply H0. apply H1. 
    elim IHS1.
      intros. elim (X x). intros. left. unfold For_all. intros. elim H1 with x0. intros. elim (H3 H2).
        intros. apply H with x. apply H5. apply a0.
        intros. apply a. apply H5.  
      intros. right. intro. apply b. apply H2. elim H1 with x. intros. apply H4. left. apply E.eq_equiv.
   intros. right. intro. apply b. unfold For_all. intros. apply H2. elim H1 with x0.
   intros. apply H5. right. apply H3.
Qed.

Theorem Exists_dec: forall (S: M.t) (P: M.E.t -> Prop),
  (forall c: M.E.t, {P c} + {~P c}) -> compat_P E.eq P ->
  {Exists (fun c => P c) S} + {~Exists (fun c => P c) S}.
Proof.
  intros. induction S using Props.set_induction.
    right. intro. unfold Exists in H1. destruct H1 as [x [Hx1 Hx2]]. apply (H0 x). apply Hx1.
    destruct IHS1. 
      left. destruct e. exists x0. split. apply H1. right. apply (proj1 H2). apply (proj2 H2).
      destruct (X x).
        left. exists x. split. apply H1. left. reflexivity. apply p.
        right. intro. destruct H2. destruct (proj1 (H1 x0) (proj1 H2)).
          apply n0. apply H with x0. symmetry. apply H3. apply (proj2 H2).
          apply n. exists x0. split. apply H3. apply (proj2 H2).
Qed.

Theorem not_forall_exists: forall P f, compat_P E.eq f ->
    (forall c, {f c} + {~f c}) -> ~For_all f P ->
    Exists (fun c => ~f c) P.
Proof.
   intros P f H H0 H1. induction P using set_induction.
     elim H1. unfold For_all. intros. absurd (In x P). apply H2. apply H3.
     elim (H0 x).
       intros. elim IHP1. intros. destruct H4. exists x0. split.
         elim (H3 x0). intros. apply H7. right. apply H4. apply H5.
       intro. apply H1. unfold For_all. intros. elim (H3 x0). 
         intros. elim (H6 H5). 
           intros. apply H with x. apply H8. apply a. apply H4.
       intros. exists x. split.
         elim (H3 x). intros. apply H5. left. reflexivity. 
         apply b.
Qed. 

Theorem forall_not_exists: forall P f, 
   For_all (fun c => ~f c) P ->
   ~Exists f P.
Proof.
  intros. unfold Exists. induction P using set_induction.
    intro. destruct H1. destruct H1. absurd (In x P). apply H0. apply H1.
    intro. destruct H2. destruct H2. apply (H x0). apply H2. apply H3.
Qed.
        
Definition monotone (f: M.t -> M.t) :=
  forall P: M.t, P [<=] f P.

Definition StrictSubset (S S': M.t) :=
   S [<=] S' /\ ~(S [=] S').
Notation "S [<] T" := (StrictSubset S T) (at level 70, no associativity).

Add Morphism StrictSubset with signature M.eq ==> M.eq ==> iff as StrictSubset_m.
Proof.
  intros. split. 
    intros. destruct H1. split. rewrite <- H. rewrite <- H0. apply H1.
    intro. apply H2. rewrite H. rewrite H0. apply H3.
    intros. destruct H1. split. rewrite H. rewrite H0. apply H1.
    intro. apply H2. rewrite <- H. rewrite <- H0. apply H3.
Qed.
 
Definition strict_subset (S S': M.t): bool :=
  subset S S' && negb (equal S S').

Lemma strict_subset_1: forall S S', StrictSubset S S' -> strict_subset S S' = true.
Proof.
  intros. destruct H. unfold strict_subset. apply <- andb_true_iff. split.
    apply subset_1. apply H.
    apply eq_true_not_negb. intro. apply H0. apply equal_2. apply H1.
Qed.

Lemma strict_subset_2: forall S S', strict_subset S S' = true -> StrictSubset S S'.
Proof.
  intros. symmetry in H. destruct (andb_true_eq _ _ H). split.
    apply subset_2. symmetry. apply H0.
    intro. apply negb_prop_elim with (equal S S'). apply Is_true_eq_right. apply H1.
    apply Is_true_eq_left. apply equal_1. apply H2.
Qed.
 
Theorem empty_no_subset: forall S E: M.t, Empty E -> ~(S [<] E).
Proof.
  intros. intro. destruct H0. apply H1. split.
     intros. apply H0. apply H2.
     intros. absurd (In a E). apply H. apply H2.
Qed.

Theorem not_empty_subset: forall S: M.t, ~(Empty S) -> (exists S': M.t, S' [<] S).
Proof.
  intros. induction S using set_induction.
    absurd (~Empty S). intro. apply H1. apply H0. apply H.
    exists S1. split.
      unfold Subset. intros. elim (H1 a). intros. apply H4. right. apply H2.
      intro. apply H0. elim (H1 x). intros. rewrite H2. apply H4. left. reflexivity.
Qed.

Theorem strict_subset_trans
: forall S S' S'': M.t, S [<] S' -> S' [<] S'' -> S [<] S''.
Proof.
  intros. destruct H. destruct H0. split. apply subset_trans with S'. apply H. apply H0.
  intro. assert (S' [<=] S). intro. intros. rewrite (H3 a). apply H0. apply H4.
  assert (S [=] S'). apply subset_antisym. apply H. apply H4. apply H1. apply H5. 
Qed.

Lemma remove_equal2: forall (s: M.elt) (S: M.t), In s S -> ~(remove s S [=] S).
Proof.
  intro s. induction S using set_induction.
    intros. absurd (In s S). apply H. apply H0.
    intros. elim (H0 s). intros. intro. apply (remove_1 (x:=s) (y:=s) (s:=S2)). apply E.eq_equiv.
    elim (H4 s). intros. apply H6. apply H1.
Qed.
 
Lemma remove_transpose: transpose Equal remove.
Proof.
  unfold transpose. intros. split.
    intros. apply remove_2. intro. rewrite remove_iff in H. destruct H. rewrite remove_iff in H.
     destruct H. apply H2. apply H0.
     apply remove_2. intro. rewrite remove_iff in H. destruct H. apply H1. apply H0.
     apply remove_3 with y. apply remove_3 with x. apply H.
    intros. apply remove_2. intro. rewrite remove_iff in H. destruct H. rewrite remove_iff in H. 
     destruct H. apply H2. apply H0.
     apply remove_2. intro. rewrite remove_iff in H. destruct H. apply H1. apply H0.
     apply remove_3 with x. apply remove_3 with y. apply H.
Qed.

Theorem not_empty_exists: forall S: M.t, ~Empty S -> exists a: M.elt, In a S. 
Proof.
  induction S using set_induction.
  intros. elim H0. apply H. intros. exists x. elim H0 with x. intros. apply H3. left. apply E.eq_equiv.
Qed.

Lemma empty_dec:
  forall S: M.t, { Empty S } + { ~Empty S }.
Proof.
  intros. induction S using set_induction.
    left. apply H.
    right. elim (H0 x). intros. intro. absurd (~In x S2). intro. apply H4. apply H2. left. apply E.eq_equiv. apply H3.
Qed.

Lemma elements_empty:
   forall S: M.t, Empty S -> forall a: elt, ~List.In a (elements S).
Proof.
  intros. intro. apply (H a). apply elements_2. apply In_InA. intros. apply E.eq_equiv. apply H0.
Qed.

Theorem add_strict_subset: forall (S1 S2: M.t), (exists x: M.elt, ~In x S1 /\ Add x S1 S2) -> S1 [<] S2.
Proof.
 intros. elim H. intros. destruct H0. split.
     unfold Subset. intros. elim (H1 a). intros. apply H4. right. apply H2.
     intro. apply H0. rewrite (H2 x). elim (H1 x). intros. apply H4. left. apply E.eq_equiv.
Qed.

Theorem strict_subset_equal_or_subset: forall P Q: M.t, P [<=] Q -> P [<] Q \/ P [=] Q.
Proof.
   intros. elim (M.eq_dec P Q). intros. right. apply a.
   intros. left. split.  apply H. apply b.
Qed.
 
Lemma strict_subset_trans_subset1: forall P Q R: M.t, P [<] Q -> Q [<=] R -> P [<] R.
Proof.
  intros. destruct H. split.
     apply subset_trans with Q. apply H. apply H0.
     intro. apply H1. apply subset_antisym. apply H. rewrite H2. apply H0. 
Qed.

Lemma strict_subset_trans_subset2: forall P Q R: M.t, P [<=] Q -> Q [<] R -> P [<] R.
Proof.
  intros. destruct H0. split.
    apply subset_trans with Q. apply H. apply H0. 
    intro. apply H1. apply subset_antisym. apply H0. rewrite <- H2. apply H.
Qed.

Lemma strict_subset_irrefl:
  forall S S', S [<] S' -> ~(S' [<] S).
Proof.
  intros. destruct H.
  intro. destruct H1. apply H0. split. 
    intro. apply H. apply H3. intro. apply H1. apply H3. 
Qed.

Lemma strict_subset_weak:
  forall S S', S [<] S' -> S [<=] S'.
Proof.
  intros. destruct H. apply H.
Qed.

Lemma strict_subset_not_subset:
  forall S S', S [<] S' -> ~S' [<=] S.
Proof.
  intros. intro. destruct H. apply H1. split. apply H. apply H0. 
Qed.

Lemma add_inv:
  forall (P: M.t) (x y: M.elt), In x (add y P) -> M.E.eq y x \/ In x P.
Proof.
  intros. elim (M.E.eq_dec y x).  
    intros. left. apply a.
    intros. right. apply add_3 with y. intro. apply b. apply H0.
    apply H.
Qed.

Lemma add_eq:
  forall (P Q R: M.t) (x: M.elt), P [=] Q -> Add x P R -> Add x Q R.
Proof.
  intros. split.
    intros. elim (H0 y). intros. rewrite <- H. apply H2. apply H1.
     intros. rewrite <- H in H1. elim (H0 y). intros. apply H3. apply H1. 
Qed.

Lemma included_add: forall (X A: M.t) (x: M.elt),
  X [<=] (add x A) -> X [<=] A \/ exists A', X [=] add x A' /\ A' [<=] A.
Proof.
   intros. elim (In_dec x X). 
      intros. right. exists (remove x X). split.
        rewrite add_remove. reflexivity. apply a.
        unfold Subset. intros. assert (~(E.eq x a0)).
        intro. apply (remove_1 H1 H0).
        apply (add_3 H1). apply H. apply remove_3 with x. apply H0.
   intros. left. unfold Subset. intros. apply add_3 with x. intro. apply b. rewrite H1. apply H0.
   apply H. apply H0. 
Qed. 


Theorem strict_subset_induction:  
   forall P : t -> Prop,
     (forall X Y: t, X [=] Y -> (P X <-> P Y)) ->
     (forall X: t,
         (forall Y: t, Y [<] X -> P Y) -> P X) ->
     forall X: t, P X.
Proof.
   intros P Heq H X. generalize P Heq H. clear H Heq P.
   induction X using set_induction.
     intros P Heq H0. apply H0. intros. absurd (Y [<] X). apply empty_no_subset. apply H. apply H1.
     intros P Heq H3. cut (forall Y:t, Y [<=] (add x X1) -> P Y).
        intros. apply H1. apply subset_equal. rewrite <- Add_Equal. apply H0.
        generalize H. apply IHX1. intros. split.
          intros. apply H2. intro. apply H4. rewrite <- H1. assumption. rewrite H1. apply H5.
          intros. apply H2. rewrite <- H1. apply H4. rewrite <- H1. apply H5.
        intros X H5 L Y H6. apply H3.
        intros Y0 H7. elim strict_subset_trans_subset1 with Y0 Y (add x X). 
           intros H2 H4. elim (included_add H2).
             intros H14. elim strict_subset_equal_or_subset with Y0 X.
                 intros H9. apply H5 with Y0. apply H9. intro. apply L. apply H14.  apply H1. apply subset_add_2. apply subset_refl.
                 intros H9. rewrite (Heq Y0 X). apply H3.
                 intros Y1 H8. elim H8.
                   intros H10 H11. apply H5 with Y1. apply H8. intro. apply L. apply H10. apply H1.
                   apply subset_add_2. apply subset_refl.
                   apply H9. apply H14.
              intros H14. elim H14. intros A' E. elim E. intros H15 H16. clear E H14.
              elim strict_subset_equal_or_subset with A' X. 
                 intro H8. apply H5 with (Y := A'). apply H8. intro. apply L. destruct H8. apply H8. apply H1.
                 apply subset_equal. apply H15. 
                 intros H8. elim H7.
                    intros H9 H10. elim H10. rewrite <- H8 in H6. rewrite <- H15 in H6. apply subset_antisym. apply H9. apply H6.
                    apply H16. apply H7. apply H6.  
Qed.

Theorem wf_strict_subset: well_founded StrictSubset.
Proof.
   intro. apply strict_subset_induction.
      intros. split. intros. split. intros. apply Acc_inv with X. apply H0. destruct H1. split. 
         rewrite H. apply H1. rewrite H. apply H2.
      intros. split. intros. apply Acc_inv with Y. apply H0. destruct H1. split.
         rewrite <- H. apply H1. rewrite <- H. apply H2.
      intros. split.  apply H.
Qed.

Lemma subset_add:
   forall P Q: t, P [<=] Q -> forall x: elt, add x P [<=] add x Q.
Proof.
  intros. unfold Subset. intros.
     elim add_inv with P a x. 
     intros. apply add_1. apply H1.
     intros. apply add_2. apply H. apply H1.
     apply H0.
Qed.

Lemma subset_inter:
  forall P Q R: t, P [<=] Q -> inter R P [<=] inter R Q.
Proof.
  intros. unfold Subset. intros.
    apply inter_3.
      apply inter_1 with P. apply H0.
      apply H. apply inter_2 with R. apply H0.
Qed.

(* Function iter (n: nat) (C: M.t -> M.t) (g: M.t) {struct n}: M.t :=
  match n with
  | O => g
  | S n' => C (iter n' C g)
  end.

Theorem equal_iter_equal: forall f, (forall P Q, P [=] Q -> f P [=] f Q) -> forall (P Q: M.t) (n: nat),
  P [=] Q -> iter n f P [=] iter n f Q.
Proof.
  intros. induction n.
      simpl. apply H0.
      simpl. apply H. apply IHn. 
Qed.
  
Theorem iter_subset: forall f R, (forall P, f P [<=] R) -> forall P, P [<=] R -> forall (n: nat), iter n f P [<=] R.
Proof.
  intros. induction n.
     simpl. apply H0.
     simpl. apply H. 
Qed.

Theorem iter_equal_always_equal:
  forall f, (forall P Q, P [=] Q -> f P [=] f Q) -> forall (P: t) (n: nat), iter n f P [=] iter (S n) f P -> forall k: nat, iter n f P [=] iter (n+k) f P.
Proof.
   intros. induction k.
       intros. rewrite plus_0_r. reflexivity.
       rewrite <- plus_Snm_nSm. rewrite H0. simpl. apply H. apply IHk.
Qed. *)

 
Theorem subset_dec: forall P Q: M.t, {P [<=] Q} + {~P [<=] Q}.
Proof.
  intros. induction P using set_induction.
     left. rewrite (empty_is_empty_1 H). apply subset_empty.
     elim IHP1. 
        intros. elim (In_dec x Q).
           intros. left. rewrite Add_Equal in H0. rewrite H0. unfold Subset. intros. 
              elim (add_inv H1).
                 intros. rewrite <- H2. apply a0.
                 apply a.
  intros. right. intro. apply b. apply H1. elim (H0 x). intros. apply H3. left. reflexivity.
  intros. right. intro. apply b. unfold Subset. intros. apply H1. elim (H0 a). intros. apply H4. right. apply H2.
Qed.

Theorem strict_subset_dec: forall P Q: M.t, {P [<] Q} + {~P [<] Q}.
Proof.
  intros. unfold StrictSubset.
  elim (subset_dec P Q). 
    intros. elim (M.eq_dec P Q). 
      intros. right. intro. destruct H. apply H0. apply a0.
      intros. left. split. apply a. apply b.
    intros. right. intro. destruct H. apply b. apply H.
Qed.

Theorem strict_subset_difference: forall P Q: M.t, P [<] Q -> exists x: M.elt, In x Q /\ ~In x P.
Proof.
   intros. destruct H. elim (not_and (P [<=] Q) (Q [<=] P)). intros.
      absurd (~(P [<=] Q)). intro. apply H1. apply H. apply H1.
      intros. unfold Subset in H1. elim not_forall_exists with Q (fun a => In a P).
      intros. destruct H2. exists x. split. apply H2. apply H3.
      unfold compat_P. simpl_relation. rewrite <- H2. apply H3.
      intros. elim In_dec with c P. intros. left. apply a. intros. right. apply b.
      unfold For_all. intro. apply H1. intros. apply not_not. elim In_dec with a P. left. apply a0. intros. right. apply b.
      intro. apply H4. apply H2. apply H3. 
      elim (subset_dec P Q). intros. left. apply a. intros. right. apply b. 
      intro. apply H0. destruct H1. apply subset_antisym. apply H1. apply H2.
Qed.

Theorem strict_subset_cardinal: forall P Q: M.t, P [<] Q -> cardinal P < cardinal Q.
Proof.
  intros. elim H. intros.
  induction P using set_induction.
     rewrite (empty_is_empty_1 H2). rewrite empty_cardinal. apply neq_O_lt. intro. apply H1.
     assert (Empty Q). apply cardinal_inv_1. symmetry. apply H3. rewrite (empty_is_empty_1 H4). apply empty_is_empty_1. apply H2.
     elim (strict_subset_difference H). intros. destruct H4. 
     apply subset_cardinal_lt with x0.
        apply H0. 
        apply H4.
        apply H5.
Qed.
 
Lemma fold_left_init:
  forall (f: M.t -> M.t -> M.t), (forall x (P: M.t), P [<=] f P x) -> forall (Q: M.t) l (q: M.elt), In q Q -> In q (fold_left f l Q).
Proof.
  intros. generalize l Q H0. clear H0 Q l. induction l.
    simpl. trivial.
    simpl. intros. apply IHl. apply H. apply H0.
Qed.


Theorem fold_left_init2: forall P Q l (f: M.t -> M.t -> M.t), (forall x P Q, P [<=] Q -> f P x [<=] f Q x) -> P [<=] Q -> fold_left f l P [<=] fold_left f l Q.
Proof.
  intros. generalize P Q H0. clear H0 Q P. induction l.
     simpl. trivial.
     simpl. intros. apply IHl. apply H. apply H0.
Qed.

Theorem fold_left_init_equal: forall P Q l (f: M.t -> M.t -> M.t), (forall x P Q, P [=] Q -> f P x [=] f Q x) -> P [=] Q -> fold_left f l P [=] fold_left f l Q.
Proof.
  intros. generalize P Q H0. clear H0 Q P. induction l.
    simpl. trivial.
    simpl. intros. apply IHl. apply H. apply H0.
Qed.

Theorem fold_left_init3: forall (A B: Set) (x: B) (l: list A) (f: A -> B) i,
  List.In x i ->
  List.In x (fold_left (fun acc r => (f r)::acc) l i).
Proof.
  intros. generalize x i H. clear H i x. induction l.
    intros. simpl. apply H. 
    intros. simpl. apply IHl. simpl. right. apply H.
Qed.

Theorem fold_left_init4: forall (A B: Set) (x y: B) (f: A -> B) i j l, 
  (forall n, List.In n i -> List.In n j) ->
  List.In x (fold_left (fun acc r => (f r)::acc) l i) ->
  List.In x (fold_left (fun acc r => (f r)::acc) l j).
Proof.
  intros. generalize H. clear H. generalize i j H0. clear H0 j i. induction l.
  intros. simpl. simpl in H0. apply H. apply H0.
  intros. simpl. simpl in H0. apply (IHl (f a::i)).
  apply H0. intros. simpl. elim H1.
    intros. left. apply H2. right. apply H. apply H2.
Qed.

Theorem fold_left_in: forall (A B: Set) (p: A) (l: list A) (f: A -> B) i,
  (forall x y, x = y -> f x = f y) ->
  List.In p l ->
  List.In (f p) (fold_left (fun acc r => (f r)::acc) l i).
Proof.
  intros. induction l. 
    absurd (List.In p nil). apply in_nil. apply H0.
    simpl. elim H0. 
      intros. apply fold_left_init3. simpl. left. apply H. apply H1.
      intros. apply fold_left_init4 with i. apply (f p). intros. right. apply H2. 
      apply IHl. apply H1.
Qed.
   
Theorem fold_in: forall (f: M.t -> M.t -> M.t) (l: list M.t) (a: M.t) (x: M.elt), (forall P Q x, In x (f P Q) -> In x P \/ In x Q) -> In x (fold_left f l a) -> In x a \/ exists z: M.t, List.In z l /\ In x z.
Proof.
  intros. generalize a H0. clear H0 a. induction l.
    simpl. intros. left. assumption.
    simpl. intros. 
      elim (IHl (f a0 a)).
        intros. elim (H a0 a x).
          intros. left. exact H2.
          intros. right. exists a. split. left. reflexivity. exact H2.
        exact H1.
        intros. right. elim H1. intros. destruct H2. exists x0. split. right. exact H2. exact H3.  
        exact H0.
Qed.

Theorem fold_init_subset: forall f, compat_op E.eq Equal f -> transpose Equal f -> (forall x P Q, P [<=] Q -> f x P [<=] f x Q) -> forall (R: M.t) (P Q: M.t), P [<=] Q -> fold f R P [<=] fold f R Q.
Proof.
  intros f H H0 H1. induction R using set_induction.
     intros P Q H3. rewrite (Props.fold_1 _ (s:=R)). rewrite (Props.fold_1 _ (s:=R)). apply H3. apply H2. apply H2.
     intros P Q H4.
        rewrite (Props.fold_2 _ (s:=R1) (s':=R2) (x:=x) P H H0 H2 H3).
        rewrite (Props.fold_2 _ (s:=R1) (s':=R2) (x:=x) Q H H0 H2 H3).
        intro. intros H5. apply (H1 x (fold f R1 P)). apply IHR1. apply H4. apply H5.
Qed.

Theorem fold_in_init: forall f, compat_op E.eq Equal f -> transpose Equal f -> (forall x P, P [<=] f x P) -> forall R P, P [<=] fold f R P.
Proof.
  intros. induction R using set_induction.
     rewrite (fold_equal _ H H0 P (empty_is_empty_1 H2)). rewrite fold_empty. apply subset_equal. reflexivity.
     rewrite Add_Equal in H3. rewrite (fold_equal _ H H0 P H3). rewrite (fold_add _ H H0). apply subset_trans with (fold f R1 P). apply IHR1. apply H1. apply H2.
Qed.

Theorem fold_init_add: forall f P Q x, compat_op E.eq Equal f -> transpose Equal f -> (forall x x0 P, f x (add x0 P) [=] add x0 (f x P)) -> (forall x P Q, P [=] Q -> f x P [=] f x Q) -> fold f P (add x Q) [=] add x (fold f P Q).
Proof.
  intros. induction P using set_induction.
    rewrite (fold_equal _ H H0 Q (empty_is_empty_1 H3)).
    rewrite (fold_empty). 
    rewrite (fold_equal _ H H0 (add x Q) (empty_is_empty_1 H3)).
    rewrite (fold_empty).
    reflexivity.
   rewrite (fold_2 _ (s:=P1) (s':=P2) (x:=x0) (add x Q) H H0 H3 H4). 
   rewrite (fold_2 _ (s:=P1) (s':=P2) (x:=x0) Q H H0 H3 H4). 
  rewrite (H2 x0 (fold f P1 (add x Q)) (add x (fold f P1 Q))). rewrite H1. reflexivity. apply IHP1.
Qed.
     
Lemma inter_repetitive: forall P Q, inter P (inter P Q) [=] inter P Q.
Proof.
  intros. split.
    intros. apply inter_3.
      apply inter_1 with (inter P Q). apply H.
      apply inter_2 with P. apply inter_2 with P. apply H.
    intros. apply inter_3. 
       apply inter_1 with Q. apply H.
       apply H.
Qed.

Theorem cardinal_singleton: forall S, cardinal S = 1 -> exists x, S [=] singleton x.
Proof.
  intros. elim cardinal_inv_2 with S 0.
    intros. exists x. induction S using set_induction.
      absurd (In x S). apply H0. apply p.
      rewrite Add_Equal in H1. rewrite H1 in H. 
      assert (cardinal S1 = 0). apply eq_add_S. rewrite <- H. rewrite add_cardinal_2. reflexivity. apply H0. assert (Empty S1). rewrite cardinal_Empty. apply H2. rewrite (empty_is_empty_1 H3) in H1. rewrite <- (singleton_equal_add x0) in H1.
      assert (E.eq x0 x). apply singleton_1. rewrite H1 in p. apply p.
      rewrite H1. rewrite H4. reflexivity.
      apply H.
Qed.

Lemma fold_forall_and: forall (c: M.t) (f: E.t -> bool),
  (forall a b, E.eq a b -> (f a) = (f b)) -> 
  (fold (fun a b => f a && b) c true = true <-> For_all (fun x => f x = true) c).
Proof.
  intros. split.
  unfold For_all. intros. 
  induction c using set_induction.
    (* empty *) absurd (In x c). apply H2. apply H1.
    (* x0 c1 *) elim (andb_true_iff (f x0) (fold (fun a b => f a && b) c1 true)).
      intros. elim H4. intros.
      elim (H3 x). intros. elim (H8 H1). intros. rewrite <- (H x0 x H10). apply H6.
      intros. apply IHc1. apply H7. apply H10.
      rewrite fold_2 in H0. apply H0.
      split. 
        apply flip_Reflexive. apply flip_Symmetric. apply eq_equivalence. apply flip_Transitive. apply eq_equivalence.
        simpl_relation. apply eq_true_iff_eq. split.
          intros. rewrite (H x1 y H6). apply H7.
          intros. rewrite <- (H x1 y H6).  apply H7.
      unfold transpose. intros. unfold Basics.flip. apply eq_true_iff_eq. split. 
        intros. apply Is_true_eq_true.
        elim (andb_true_iff (f y) (f x1 && z)). intros. elim (H7 H6). intros.
        elim (andb_true_iff (f x1) z). intros. elim (H11 H10). intros.
        apply andb_prop_intro. split. apply Is_true_eq_left. apply H13. apply andb_prop_intro. 
        split. apply Is_true_eq_left. apply H9. apply Is_true_eq_left. apply H14.
        intros. apply Is_true_eq_true.
        elim (andb_true_iff (f x1) (f y && z)). intros. elim (H7 H6). intros.
        elim (andb_true_iff (f y) z). intros. elim (H11 H10). intros.
        apply andb_prop_intro. split. apply Is_true_eq_left. apply H13. apply andb_prop_intro.
        split. apply Is_true_eq_left. apply H9. apply Is_true_eq_left. apply H14.
      apply H2.
      apply H3.
  intros. unfold For_all in H0. induction c using set_induction.
  rewrite Props.fold_1. trivial. apply eq_equivalence. apply H1.
  rewrite Props.fold_2. apply Is_true_eq_true. apply andb_prop_intro. split.
    apply Is_true_eq_left. apply (H0 x). elim (H2 x). intros. apply H4. left. reflexivity.
    apply Is_true_eq_left. apply IHc1. intros. apply H0.
    elim (H2 x0). intros. apply H5. right. apply H3.
    apply eq_equivalence.
    simpl_relation. rewrite (H x0 y). reflexivity. apply H3.
    unfold transpose. intros. apply eq_true_iff_eq. split.
    intros.
    elim (andb_true_iff (f x0) (f y && z)). intros. elim (H4 H3). intros.
    elim (andb_true_iff (f y) z). intros. elim (H8 H7). intros.
    apply Is_true_eq_true. apply andb_prop_intro. split. apply Is_true_eq_left. apply H10.
    apply andb_prop_intro. split. apply Is_true_eq_left. apply H6. apply Is_true_eq_left. apply H11.
    intros.
    elim (andb_true_iff (f y) (f x0 && z)). intros. elim (H4 H3). intros.
    elim (andb_true_iff (f x0) z). intros. elim (H8 H7). intros.
    apply Is_true_eq_true. apply andb_prop_intro. split. apply Is_true_eq_left. apply H10.
    apply andb_prop_intro. split. apply Is_true_eq_left. apply H6. apply Is_true_eq_left. apply H11.
    apply H1.
    apply H2.
Qed. 

Lemma fold_forall_or: forall (c: M.t) (f: E.t -> bool),
  (forall a b, E.eq a b -> (f a) = (f b)) -> 
  (fold (fun a b => f a || b) c false = false <-> For_all (fun x => f x = false) c).
Proof.
  intros. split. 
  unfold For_all. intros. 
  induction c using set_induction.
    (* empty *) absurd (In x c). apply H2. apply H1.
    (* x0 c1 *) rewrite fold_2 in H0. elim (orb_false_elim (f x0) (fold (fun a b => f a || b) c1 false)).
      elim (H3 x). intros. elim (H4 H1). intros. rewrite <- (H x0 x H8). apply H6.
      intros. apply IHc1. apply H7. apply H8. apply H0.
      split. apply flip_Reflexive. apply flip_Symmetric. apply eq_equivalence. apply flip_Transitive. apply eq_equivalence.
      simpl_relation. rewrite (H x1 y H4). reflexivity.
      unfold transpose. intros. unfold Basics.flip. apply eq_true_iff_eq. split.
        intros. elim (orb_true_elim (f y) (f x1 || z)).
          intros. rewrite a. rewrite orb_true_l. rewrite orb_true_r. reflexivity. 
          intros. elim (orb_true_elim (f x1) z). 
            intros. rewrite a. rewrite orb_true_l. reflexivity.
            intros. rewrite b0. rewrite orb_true_r. rewrite orb_true_r. reflexivity.
            apply b. apply H4.
        intros. elim (orb_true_elim (f x1) (f y || z)).
          intros. rewrite a. rewrite orb_true_l. rewrite orb_true_r. reflexivity. 
          intros. elim (orb_true_elim (f y) z). 
            intros. rewrite a. rewrite orb_true_l. reflexivity.
            intros. rewrite b0. rewrite orb_true_r. rewrite orb_true_r. reflexivity.
            apply b. apply H4.
        apply H2.
        apply H3.
  intros. unfold For_all in H0. induction c using set_induction.
    rewrite Props.fold_1. reflexivity. apply eq_equivalence. apply H1.
    rewrite Props.fold_2. apply orb_false_intro.
      apply (H0 x). elim (H2 x). intros. apply H4. left. reflexivity.
      apply IHc1. intros. apply H0. elim (H2 x0). intros. apply H5. right.
      apply H3.
      apply eq_equivalence.
      simpl_relation. rewrite (H x0 y H3). reflexivity.
      unfold transpose. intros. apply eq_true_iff_eq. split.
        intros. elim (orb_true_elim (f x0) (f y || z)).
          intros. rewrite a. rewrite orb_true_l. rewrite orb_true_r. reflexivity. 
          intros. elim (orb_true_elim (f y) z).
            intros. rewrite a. rewrite orb_true_l. reflexivity.
            intros. rewrite b0. rewrite orb_true_r. rewrite orb_true_r. reflexivity.
          apply b. apply H3.
        intros. elim (orb_true_elim (f y) (f x0 || z)).
          intros. rewrite a. rewrite orb_true_l. rewrite orb_true_r. reflexivity. 
          intros. elim (orb_true_elim (f x0) z).
            intros. rewrite a. rewrite orb_true_l. reflexivity.
            intros. rewrite b0. rewrite orb_true_r. rewrite orb_true_r. reflexivity.
          apply b. apply H3.
    apply H1. apply H2.
Qed.

Theorem union_subset_6: forall A B C D: t,
  A [<=] B -> C [<=] D -> union A C [<=] union B D.
Proof.
  intros. induction A using set_induction.
    induction B using set_induction.
    rewrite (empty_union_1 _ H1). rewrite (empty_union_1 _ H2).
    apply H0.
    rewrite (empty_union_1 _ H1). apply subset_trans with (union B1 D). 
    apply subset_trans with (union A C). apply union_subset_2. apply IHB1. rewrite (empty_is_empty_1 H1). apply subset_empty.
    apply union_subset_4. unfold Subset. intros. elim (H3 a). intros. apply H6. right. apply H4.  
    rewrite Add_Equal in H2. rewrite H2. rewrite union_add. 
    apply subset_add_3. apply union_2. apply H. rewrite H2. apply add_1. apply E.eq_equiv.
    apply IHA1. apply subset_trans with A2. unfold Subset. intros.
    rewrite H2. apply add_2. apply H3. 
    apply H.
Qed.

Theorem subset_add_1: forall (x: elt) (A B: t),
  A [<=] B -> add x A [<=] add x B.
Proof.
  intros. unfold Subset. intros.
  elim (add_inv H0).
    intros. apply add_1. apply H1.
    intros. apply add_2. apply H. apply H1.
Qed.

Lemma lt_not_eq: forall n m: nat, n < m -> n <> m.
Proof.
  double induction n m.
  intros. inversion H.
  intros. discriminate.
  intros. discriminate.
  intros. injection. apply H0. apply lt_S_n. apply H1.
Qed.
  
Lemma cardinal_subset_equal:
  forall P R: t,
  cardinal P = cardinal R ->
  P [<=] R ->
  P [=] R.
Proof.
  intros. split.
    intros. apply H0. apply H1.
    intros. 
       apply not_not. elim (In_dec a P). intros. left. assumption. right. assumption.
       intro. apply (lt_not_eq (subset_cardinal_lt H0 H1 H2)). apply H.
Qed.

Lemma s_ss: forall (p: elt) (R: t), In p R -> singleton p [<=] R.
Proof.
  intros.  unfold Subset. intros. assert (E.eq p a). apply singleton_1. apply H0. rewrite <- H1. apply H.
Qed.

Lemma not_empty_element:
  forall S: t, ~Empty S -> exists e: elt, In e S.
Proof.
  intros. induction S using set_induction.
  absurd (Empty S). apply H. apply H0.
  exists x. elim (H1 x). intros. apply H3. left. apply E.eq_equiv.
Qed.

Lemma filter_add_1:
  forall R1 R2 x f, compat_bool E.eq f -> Add x R1 R2 -> f x = false \/ Add x (filter f R1) (filter f R2).
Proof.
  intros. elim (bool_dec (f x) true).
    intros. right. intro. elim (H0 y). intros. split. 
    intros.
      elim (H1 (filter_1 H H3)).  
      intros. left. assumption.
      intros. right. apply (filter_3 H). apply H4. apply (filter_2 H H3).
    intros. apply (filter_3 H).
      apply H2. elim H3.
      intros. left. assumption.
      intros. right. apply (filter_1 H H4).
    elim (H3). intros. rewrite <- (H x). assumption. apply H4.
    intros. apply (filter_2 H H4).
  intros. left. apply not_true_is_false. apply b.
Qed.

Lemma filter_add_2:
  forall R1 R2 x f, compat_bool E.eq f -> Add x R1 R2 -> In x (filter f R2) -> In x (filter f R1) \/ f x = true.
Proof.
  intros.
  elim (H0 x). intros. 
    elim (H2 (filter_1 H H1)).
    intros. right. apply (filter_2 H H1).
    intros. left. apply (filter_3 H H4). apply (filter_2 H H1). 
Qed.

Lemma empty_nor_singleton:
  forall P x, In x P -> cardinal P <> 1 -> exists y, In y P /\ ~E.eq x y.
Proof.
  intros. 
  elim (cardinal_inv_2b (s:=P)). intros. 
  elim (cardinal_inv_2b (s:=remove x P)). intros. exists x1. 
  rewrite remove_iff in p0. apply p0.
    intro. apply H0. transitivity (S (cardinal (remove x P))).
        symmetry. apply remove_cardinal_1. apply H. 
        rewrite H1. trivial.
   intro. apply (cardinal_inv_1 H1 H).
Qed.

Section SetList.
Parameter equiv_set: list E.t -> M.t.

Axiom equiv_set_1: forall x l, List.In x l -> In x (equiv_set l).
Axiom equiv_set_2: forall x l, In x (equiv_set l) -> List.In x l.
End SetList.

End Aux.
