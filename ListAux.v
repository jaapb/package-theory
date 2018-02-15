Set Implicit Arguments.

Require Export List.
(*Require Export TheoryList.*)
Require Import Bool.
Require Import Classical_Prop.
Require Import Arith.
Require Import FunInd.

Section ListAux.

Variable A: Type.
Parameter Aeq_dec: forall a a': A, { a = a' } + { a <> a' }.

Lemma In_not_empty:
  forall l: list A,
  (exists a: A, In a l) -> l <> nil.
Proof.
  intros. induction l.
    destruct H. absurd (In x nil). apply in_nil. apply H.
    discriminate.
Qed.

(*Lemma mem_In:
  forall (e: A) (l: list A),
  mem Aeq_dec e l = true <-> In e l.
Proof.
  intros. induction l. 
    simpl. split. intros. inversion H. intros. contradiction.
    simpl. split.
      elim (Aeq_dec e a). 
        intros. left. symmetry. assumption.
        intros. right. apply IHl. apply H.
      intros. elim (Aeq_dec e a). intros. trivial.
        intros. elim H. 
           intros. contradiction b. symmetry. assumption.
           intros. apply <- IHl. apply H0.
Qed.*)

Lemma length_nil: forall (l: list A), length l = 0 -> l = nil.
Proof.
  destruct l.
    reflexivity.
    inversion 1.
Qed.
  

Lemma length_1:
  forall (l: list A), length l = 1 -> exists a: A, l = a::nil.
Proof.
  intros. destruct l.
    inversion H.
      assert (l = nil). 
      destruct l. trivial. discriminate. 
    exists a. rewrite H0. trivial.
Qed.
          
Lemma fold_left_or:
  forall (b: bool) (l: list A) (f: A -> bool),
  fold_left (fun acc i => f i || acc) l b = true ->
  b = true \/ (exists n, In n l /\ f n = true).
Proof.
  intros. induction l. 
    simpl in H. left. apply H.
    simpl in H. destruct b. 
      left. trivial.
      right. rewrite orb_false_r in H. 
        elim (bool_dec (f a) true).
          intros. exists a. split. simpl. left. trivial. apply a0.
          intros. rewrite (not_true_is_false (f a) b) in H. elim (IHl H).
            intros. inversion H0. 
            intros. elim H0. intros. destruct H1.
              exists x. split. simpl. right. apply H1. apply H2. 
Qed.

Lemma fold_left_or_true: 
  forall (A: Set) (l: list A) (f: A -> bool),
  fold_left (fun acc i => f i || acc) l true = true.
Proof.
  intros. induction l.
    simpl. trivial.
    simpl. rewrite orb_true_r. apply IHl. 
Qed.

Lemma fold_left_or_true2:
  forall (b: bool) (A: Set) (l: list A) (f: A -> bool),
  b = true \/ (exists n, In n l /\ f n = true) ->
  fold_left (fun acc i => f i || acc) l b = true.
Proof.
  intros. induction l.
    elim H. 
      intros. rewrite H0. apply fold_left_or_true.
      intros. destruct H0. destruct H0. absurd (In x nil). apply in_nil. apply H0.
    elim H. 
      intros. rewrite H0. apply fold_left_or_true.
      intros. simpl. destruct H0. destruct H0. elim H0.
        intros. rewrite <- H2 in H1. rewrite H1. rewrite orb_true_l. apply fold_left_or_true.
        intros. elim (f a). rewrite orb_true_l. apply fold_left_or_true.
        apply IHl. right. exists x. split. apply H2. apply H1.
Qed.

Lemma fold_left_or_false:
  forall (b: bool) (A: Set) (l: list A) (f: A -> bool),
  fold_left (fun acc i => f i || acc) l b = false ->
  b = false /\ forall n, In n l -> f n = false.
Proof.
  intros. induction l.
    split.
      simpl in H. apply H.
      intros. simpl in H0. contradiction.
    simpl in H. split.
      destruct b. rewrite orb_true_r in H. elim (IHl H). 
        intros. inversion H.
        rewrite fold_left_or_true. trivial.
        trivial.
      intros. 
        intros. elim (bool_dec (f a) false).
          intros. rewrite a0 in H. rewrite orb_false_l in H.
            elim (IHl H). intros.  
            elim H0. intros. rewrite <- H3. assumption.
            apply H2.
          intros. replace (f a) with true in H. rewrite fold_left_or_true in H. inversion H.
          symmetry. apply not_false_is_true. assumption.
Qed.

Lemma fold_left_or_false2:
  forall (b: bool) (A: Set) (l: list A) (f: A -> bool),
  b = false /\ (forall n, In n l -> f n = false) ->
  fold_left (fun acc i => f i || acc) l b = false.
Proof.
  intros. destruct H. induction l.
    simpl. apply H.
    simpl. rewrite H. rewrite orb_false_r. elim (bool_dec (f a) false). 
      intros. rewrite a0. rewrite H in IHl. rewrite IHl. trivial.
      intros. apply H0. simpl. right. apply H1.
      intros. absurd (f a = true). intro. apply eq_true_false_abs with (f a).
        apply H1. apply H0. simpl. left. trivial.
        apply (not_false_is_true _ b0).
Qed.

Lemma fold_left_and_false:
  forall (l: list A) (f: A -> bool),
  fold_left (fun acc i => f i && acc) l false = false.
Proof.
  intros. induction l.
    simpl. trivial.
    simpl. rewrite andb_false_r. apply IHl.
Qed.
 
Lemma fold_left_and:
  forall (b: bool) (l: list A) (f: A -> bool),
  fold_left (fun acc i => f i && acc) l b = true ->
  b = true /\ (forall n, In n l -> f n = true).
Proof.
  intros. induction l.
    simpl in H. split. apply H. intros. simpl in H0. contradiction.
    simpl in H. elim (bool_dec (f a) true). 
      intros. rewrite a0 in H. rewrite andb_true_l in H. elim (IHl H).
      intros. split.
        apply H0.
        intros. elim H2. 
          intros. rewrite <- H3. apply a0.
          intros. apply H1. apply H3.
      intros. rewrite (not_true_is_false (f a) b0) in H. rewrite andb_false_l in H. 
      rewrite fold_left_and_false in H. inversion H.
Qed.      

Lemma fold_left_and2:
  forall (b: bool) (l: list A) (f: A -> bool),
  b = true /\ (forall n, In n l -> f n = true) ->
  fold_left (fun acc i => f i && acc) l b = true.
Proof.
  intros. induction l.
    simpl. destruct H. apply H.
    simpl. destruct H. 
    rewrite H. rewrite andb_true_r. rewrite H in IHl. elim (H0 a). 
       elim (f a). apply IHl. split. trivial. intros. apply H0. simpl. right. apply H1.
       apply fold_left_and_false.
    simpl. left. trivial.
Qed.

Fixpoint flatten (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | h::t => h++(flatten t)
  end.

Lemma flatten_1:
  forall (x: A) (ll: list (list A)), In x (flatten ll) ->
    exists l: list A, In x l /\ In l ll.
Proof.
  intros. induction ll.
    simpl in H. contradiction.
    simpl in H. elim (in_app_or a (flatten ll) x).
      intros. exists a. split. apply H0. simpl. left. trivial.
      intros. elim (IHll H0). intros. destruct H1. exists x0. split.
      apply H1. simpl. right. apply H2.
    apply H.
Qed.

Lemma flatten_2:
  forall (x: A) (l: list A) (ll: list (list A)),
  In x l -> In l ll -> In x (flatten ll).
Proof.
  intros. induction ll.
    simpl in H0. contradiction.
    simpl in H0. simpl. apply in_or_app. elim H0.
      intros. left. rewrite H1. apply H.
      intros. right. apply IHll. apply H1.
Qed.

Lemma flatten_empty:
  forall (l: list (list A)), flatten l = nil ->
  l = nil \/ forall x: (list A), In x l -> x = nil.
Proof.
  intros. induction l.
    left. trivial.
    simpl in H. elim (app_eq_nil _ _ H). intros. right. intros. elim H2.
      intros. transitivity a. symmetry. apply H3. apply H0.
      intros. elim (IHl H1).
        intros. absurd (In x l). rewrite H4. apply in_nil. apply H3.
        intros. apply H4. apply H3.
Qed.

Fixpoint partition (f: A -> bool) (l: list A): list A * list A :=
  match l with
  | nil => (nil, nil)
  | h::t =>
    if (f h) then (h::(fst (partition f t)), snd (partition f t))
    else (fst (partition f t), h::snd (partition f t))
  end.

Lemma partition_l: forall  (f: A -> bool) (l: list A) (x: A),
  In x (fst (partition f l)) -> f x = true.
Proof.
  intros f l x. induction l.
    simpl. contradiction.
    simpl. elim (bool_dec (f a) true).
      intros. rewrite a0 in H. simpl in H. elim H. 
        intros. rewrite <- H0. apply a0.
        intros. apply (IHl H0).
      intros. rewrite (not_true_is_false (f a) b) in H.
        simpl in H. apply (IHl H).
Qed. 
      
Lemma partition_r: forall  (f: A -> bool) (l: list A) (x: A),
  In x (snd (partition f l)) -> f x = false.
Proof.
  intros f l x. induction l.
    simpl. contradiction.
    simpl. elim (bool_dec (f a) true).
      intros. rewrite a0 in H. simpl in H. apply (IHl H).
      intros. rewrite (not_true_is_false (f a) b) in H.
        simpl in H. elim H.
          intros. rewrite <- H0. apply not_true_is_false. apply b.
          intros. apply (IHl H0).
Qed.  

Lemma partition_r_inv: forall (f: A -> bool) (l: list A) (x: A),
  In x (snd (partition f l)) -> In x l.
Proof.
  intros f l x. induction l.
    simpl. trivial.
    simpl. elim (bool_dec (f a) true). 
      intros. rewrite a0 in H. simpl in H. right. apply (IHl H).
      intros. rewrite (not_true_is_false (f a) b) in H. simpl in H. elim H.
        intros. left. apply H0.
        intros. right. apply IHl. apply H0.
Qed.

Lemma l_partition: forall (f: A -> bool) (l: list A) (x: A),
  In x l -> f x = true -> In x (fst (partition f l)).
Proof.
  intros. induction l.
    contradiction.
    elim H.
      intros. simpl. rewrite <- H1 in H0. rewrite H0. simpl. left. apply H1.
      intros. simpl. elim (bool_dec (f a) true). 
        intros. rewrite a0. simpl. right. apply IHl. apply H1.
        intros. rewrite (not_true_is_false _ b). simpl. apply IHl. apply H1.
Qed.
 
Lemma r_partition: forall (f: A -> bool) (l: list A) (x: A),
  In x l -> f x = false -> In x (snd (partition f l)).
Proof.
  intros. induction l.
    contradiction.
    elim H.
      intros. simpl. rewrite <- H1 in H0. rewrite H0. simpl. left. apply H1.
      intros. simpl. elim (bool_dec (f a) true). 
        intros. rewrite a0. simpl. apply IHl. apply H1.
        intros. rewrite (not_true_is_false _ b). simpl. right. apply IHl. apply H1.
Qed.

Lemma partition_orig: forall (f: A -> bool) (l: list A) (x: A),
  In x (fst (partition f l)) \/ In x (snd (partition f l)) -> In x l.
Proof.
  intros. induction l.
    elim H. simpl. contradiction. simpl. contradiction.
    elim H.
      simpl. elim (f a). intros. simpl in H0. elim H0.
        intros. left. apply H1.
        intros. right. apply IHl. left. apply H1.
      simpl. intros. right. apply IHl. left. apply H0.
      simpl. elim (f a). intros. simpl in H0. right. apply IHl. right. apply H0.
      simpl. intros. elim H0.
        intros. left. apply H1.
        intros. right. apply IHl. right. apply H1.
Qed.

Lemma app_eq_empty: forall (x l: list A),
   x ++ l = x -> l = nil.
Proof.
  intros. induction x.
    simpl in H. apply H.
    inversion H.  apply IHx. apply H1. 
Qed.

Lemma filter_eq: forall f l, (forall a: A, In a l -> f a = true) -> filter f l = l.
Proof.
  intros. induction l.
    simpl. trivial.
    simpl. replace (f a) with true. 
       rewrite IHl. trivial.
       intros. apply H. simpl. right. apply H0.
       symmetry. apply H. simpl. left. trivial.
Qed.

Lemma last_In: forall (y:list A) (z:A), y <> nil -> In (last y z) y.
Proof.
  intros. induction y.
    contradiction H. trivial.
    simpl. destruct y. left. trivial. right. apply IHy. discriminate.
Qed.  

Lemma last_In2: forall (y:list A) (z:A), In (last y z) (z::y).
Proof.
  intros. simpl. destruct y.
    simpl. left. reflexivity.
    right. apply last_In. discriminate.
Qed.

Lemma last_irrelevant: forall (l: list A) x y, l <> nil -> last l x = last l y.
Proof.
   intros. induction l.
     contradiction H. trivial.
     destruct l. 
       simpl. trivial.
       change (last (a::a0::l) x) with (last (a0::l) x).
       change (last (a::a0::l) y) with (last (a0::l) y).
       apply IHl.
       discriminate. 
Qed.

Lemma nth_last: forall (l: list A) (x:nat), S x = length l -> forall q, nth x l q = last l q.
Proof.
  intros. generalize x H. clear H x. induction l. 
    intros x H. inversion H. 
    intros x H.
      destruct x. simpl nth. simpl in H. inversion H. symmetry in H1. rewrite (length_nil l H1).
      simpl. reflexivity.
      simpl in H. inversion H. simpl nth. rewrite (IHl x H1). destruct l.
        inversion H. 
        simpl. reflexivity.
Qed.
   
Lemma removelast_cons: forall (h: A) (l: list A), l <> nil -> removelast (h::l) = h::removelast l.
Proof.
  intros. destruct l.
    absurd (nil <> (nil (A:=A))). intro. apply H0. trivial. apply H.
    change (removelast (h::a::l)) with (h::(removelast (a::l))). reflexivity.
Qed.
    
Lemma incl_nil: forall (q: list A), incl (nil (A:=A)) q.
Proof.
  intros. unfold incl. intros. contradiction.
Qed.

Lemma incl_app: forall (x y l: list A), incl x l -> incl y l -> incl (x++y) l.
Proof.
  intros. unfold incl. intros. destruct (in_app_or x y a H1).
    apply (H a H2).
    apply (H0 a H2).
Qed.

(*Fixpoint inclb (k g: list A): bool :=
  List.fold_left (fun acc ke =>
    mem Aeq_dec ke g && acc
  ) k true.

(* Require Import Setoid. *)
Lemma inclb_incl: forall (k g: list A), Is_true (inclb k g) <-> incl k g.
Proof.
  intros. split.
    intros. assert (inclb k g = true). apply Is_true_eq_true. apply H. clear H.
    unfold inclb in H0. unfold incl. generalize g H0. clear H0 g. case k.
      intros. absurd (In a nil). simpl. intro. apply H1. apply H.
      intros. elim H. 
        intros. simpl in H0. elim (fold_left_and _ _ _ H0). 
        intros. rewrite <- H1. rewrite andb_true_iff in H2. destruct H2.
        apply -> mem_In. apply H2.
      intros. elim (fold_left_and _ _ _ H0).
        intros. apply -> mem_In. apply H3. apply H. 
    intros. unfold inclb. generalize g H. clear H g. case k. 
      intros. simpl. trivial.
      intros. apply Is_true_eq_left. apply fold_left_and2. split.
        reflexivity.
        intros. unfold incl in H. apply <- mem_In. apply H. apply H0. 
Qed.*)

Lemma In_nth: forall (p: A) (l: list A), In p l -> exists n: nat, n < length l /\ forall q, p = nth n l q.
Proof.
  intros. induction l.
    contradiction.
    destruct H.
      exists O. simpl. split. apply lt_0_Sn. symmetry. apply H.
      destruct (IHl H). destruct H0.
        exists (S x). split. simpl. apply lt_n_S. apply H0. simpl. apply H1.
Qed.

Lemma firstn_nil: forall n, firstn n nil = (nil (A:=A)).
Proof.
  intros. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma firstn_all: forall (l: list A), firstn (length l) l = l.
Proof.
  intros. induction l.
    simpl. trivial.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma skipn_nil: forall n, skipn n nil = (nil (A:=A)).
Proof.
  intros. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma skipn_all: forall (l: list A), skipn (length l) l = nil.
Proof.
  intros. induction l.
    simpl. reflexivity.
    simpl. apply IHl.
Qed.

Lemma skipn_nth: forall (l: list A) x, x < length l -> forall p q, q = nth x l p -> q::skipn (S x) l = skipn x l.
Proof.
  intros. generalize x H H0. clear H0 H x.  induction l.
    intros. absurd (x < length (nil (A:=A))). apply (lt_n_O x). apply H.
    intros. simpl skipn. destruct x. simpl. simpl in H0. rewrite H0. reflexivity.
    rewrite IHl. simpl. reflexivity. simpl in H. apply lt_S_n. apply H.
    apply H0.
Qed.

Function direct_sublist (l': list A) (l: list A) { struct l' }: Prop :=
  match l' with
  | nil => True 
  | h'::t' => match l with
              | nil => False
              | h::t => if Aeq_dec h h' then direct_sublist t' t else False
              end
  end.

Lemma direct_sublist_refl: forall (l: list A), direct_sublist l l.
Proof.
  intros. induction l.
    simpl. trivial.
    simpl. destruct (Aeq_dec a a).
      apply IHl.
      apply n. reflexivity.
Qed.

Lemma direct_sublist_nil: forall (l: list A), direct_sublist l nil -> l = nil.
Proof.
  intros. destruct l.
    reflexivity.
    simpl in H. contradiction.
Qed.

Lemma direct_sublist_cons: forall (l' l: list A) (h: A), direct_sublist l' l -> direct_sublist (h::l') (h::l).
Proof.
  intros. simpl. destruct (Aeq_dec h h).
    apply H.
    apply n. reflexivity.
Qed.

Lemma direct_sublist_prop: forall l' l, direct_sublist l' l <-> (firstn (length l') l) = l'.
Proof.
  intros. split.
    intros. functional induction (direct_sublist l' l).
      simpl. reflexivity. 
      contradiction.
      simpl. rewrite (IHP H). reflexivity.
      contradiction.
    intros. functional induction (direct_sublist l' l). 
      trivial.
      simpl in H. inversion H.
      apply IHP. inversion H. rewrite H1. apply H1. 
      apply _x. simpl in H. inversion H. trivial.
Qed.

Lemma direct_sublist_incl: forall l' l (x: A), In x l' -> direct_sublist l' l -> In x l.
Proof.
  intros. functional induction (direct_sublist l' l).
    contradiction.
    contradiction.
    destruct H. 
      left. apply H.
      right. apply (IHP H H0).
    contradiction.
Qed.

Function sublist (l': list A) (l: list A) { struct l }: Prop :=
  match l with
  | nil => l' = nil
  | h::t => direct_sublist l' l \/ sublist l' t
  end.

Lemma sublist_nil: forall (l: list A), sublist nil l.
Proof.
  destruct l. 
    simpl. reflexivity.
    simpl. left. trivial.
Qed.

Lemma sublist_refl: forall (l: list A), sublist l l.
Proof.
  destruct l.
    apply sublist_nil.
    simpl. destruct (Aeq_dec a a).
      left. apply direct_sublist_refl.
      left. apply n. reflexivity.
Qed.
      
Lemma direct_sublist_sublist: forall (l' l: list A),
  direct_sublist l' l -> sublist l' l.
Proof.
  intros. functional induction (direct_sublist l' l).
    apply sublist_nil. 
    contradiction.
    simpl. destruct (Aeq_dec h' h').
      left. apply H.
      left. apply n. reflexivity.
    contradiction.
Qed.
        
Lemma sublist_prop: forall l' l, sublist l' l <-> exists n: nat, firstn (length l') (skipn n l) = l'.  
Proof.
  intros. split.
    intros. functional induction (sublist l' l).
      exists 0. simpl. reflexivity.
      destruct H.
        exists 0. simpl. apply -> (direct_sublist_prop l' (h::t)). apply H.
        destruct (IHP H). exists (S x). simpl. apply H0.
    intros. functional induction (sublist l' l). 
      destruct H. rewrite (skipn_nil x) in H. rewrite (firstn_nil (length l')) in H. symmetry. apply H.
      destruct H. destruct x.
        simpl in H. left. apply <- (direct_sublist_prop l' (h::t)). apply H.
        simpl in H. right. apply IHP. exists x. apply H.  
Qed.

Lemma sublist_incl: forall l' l (x: A), In x l' -> sublist l' l -> In x l.
Proof.
  intros. functional induction (sublist l' l).
    contradiction.
    destruct H0.
      apply (direct_sublist_incl _ _ _ H H0).
      right. apply (IHP H0).
Qed.

Lemma sublist_removelast: forall l' l, sublist l' l -> sublist (removelast l') l.
Proof.
  intros. functional induction (sublist l' l).
    simpl. trivial.
    simpl. destruct H.
      left. clear IHP. functional induction (direct_sublist l' (h::t)).
        simpl. trivial.
        contradiction.
        destruct (Aeq_dec h' h').
          destruct t'. simpl removelast. trivial.
          rewrite removelast_cons.
          apply direct_sublist_cons. apply IHP. apply H. discriminate.
        absurd (h' <> h'). intro. apply H0. trivial. apply n.
        contradiction.
      right. apply (IHP H).
Qed.

Lemma sublist_skipn: forall l n, sublist (skipn n l) l.
Proof.
  intros. apply <- sublist_prop.
  exists n. 
    apply firstn_all.
Qed.

Lemma bla: forall l, l <> nil -> forall (a: A) q, last (a::l) q = last l q.
Proof.
  intros. induction l.
    contradiction H. trivial.
    simpl last. trivial.
Qed.
 
Lemma last_skipn: forall (l: list A) n (q: A), n < length l -> In (last l q) (skipn n l).
Proof.
  intros l n q. generalize l. clear l. induction n. 
    intros l H. simpl skipn. apply last_In. intro. apply (lt_n_O 0). rewrite H0 in H. apply H.
    intros l H. destruct l.
      absurd (S n < length (nil (A:=A))). apply lt_n_O. apply H.
      simpl skipn. rewrite bla. apply IHn. 
       simpl in H. apply lt_S_n. apply H.
       intro. simpl in H. rewrite H0 in H. apply lt_n_O with n. apply lt_S_n. apply H. 
Qed.  
    
End ListAux.