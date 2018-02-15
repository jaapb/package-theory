Set Implicit Arguments.

Require Import ListAux.
Require Export MSetAux.
Require Import Coq.Structures.OrdersEx.
Require Import Arith.

Module Type DiGraph (Vertices: S).
Import Vertices.

Module Edge := PairOrderedType Vertices.E Vertices.E.
Declare Module Edges : MSetInterface.S with Module E := Edge.

Parameter t: Type.
Parameter IsVertex: Vertices.elt -> t -> Prop.
Parameter IsEdge: Vertices.elt -> Vertices.elt -> t -> Prop.

Axiom IsVertex_dec: forall v g, {IsVertex v g} + {~IsVertex v g}.
Axiom IsEdge_dec: forall v v' g, {IsEdge v v' g} + {~IsEdge v v' g}.

Definition Equal g g' :=
  (forall v: Vertices.elt, IsVertex v g <-> IsVertex v g') /\
  (forall v v': Vertices.elt, IsEdge v v' g <-> IsEdge v v' g').
Definition Subgraph g g' :=
  (forall v: Vertices.elt, IsVertex v g -> IsVertex v g') /\
  (forall v v': Vertices.elt, IsEdge v v' g -> IsEdge v v' g').

Parameter empty: t.

Parameter is_empty: t -> bool.

Parameter mem_vertex: Vertices.elt -> t -> bool.
Parameter mem_edge: Vertices.elt -> Vertices.elt -> t -> bool.

Parameter vertices: t -> Vertices.t.
Parameter edges: t -> Edges.t.

Parameter add_vertex: Vertices.elt -> t -> t.
Parameter add_edge: Vertices.elt -> Vertices.elt -> t -> t.

Definition eq : t -> t -> Prop := Equal.
Declare Instance IsV_compat : Proper (Vertices.E.eq==>eq==>iff) IsVertex.
Declare Instance IsE_compat : Proper (Vertices.E.eq==>Vertices.E.eq==>eq==>iff) IsEdge.

Parameter eq_dec : forall s s', { eq s s' } + { ~ eq s s' }.
Parameter eq_refl : forall g, eq g g.
Parameter eq_sym : forall g g', eq g g' -> eq g' g.
Parameter eq_trans : forall g g' g'', eq g g' -> eq g' g'' -> eq g g''.

Instance eq_equiv: Equivalence eq := Build_Equivalence t eq eq_refl eq_sym eq_trans.
Section Spec.

Variables v v' v'' v''': Vertices.elt.
(* Variables e e': edge. *)
Variable g g' g'': t.

Parameter IsVertex_1: Vertices.E.eq v v' -> IsVertex v g -> IsVertex v' g.
Parameter IsEdge_1: Edges.E.eq (v, v') (v'', v''') -> IsEdge v v' g -> IsEdge v'' v''' g.

Parameter edge_vertex: IsEdge v v' g -> IsVertex v g /\ IsVertex v' g.

Parameter empty_vertex: ~IsVertex v empty.
Parameter empty_edge: ~IsEdge v v' empty.

Parameter is_empty_1: ~IsVertex v g -> ~IsEdge v v' g -> is_empty g = true.
Parameter is_empty_2: is_empty g = true -> ~IsVertex v g /\ ~IsEdge v v' g.

Parameter mem_vertex_spec: mem_vertex v g = true <-> IsVertex v g.
Parameter mem_edge_spec: mem_edge v v' g = true <-> IsEdge v v' g.

Parameter vertices_spec: In v (vertices g) <-> IsVertex v g.
Parameter edges_spec: Edges.In (v, v') (edges g) <-> IsEdge v v' g.

Parameter add_vertex_1: Vertices.E.eq v v' -> IsVertex v' (add_vertex v g).
Parameter add_vertex_2: IsVertex v' g -> IsVertex v' (add_vertex v g).
Parameter add_vertex_3: ~Vertices.E.eq v v' -> IsVertex v' (add_vertex v g) -> IsVertex v' g.

Parameter add_edge_1: Edges.E.eq (v, v') (v'', v''') -> IsEdge v'' v''' (add_edge v v' g).
Parameter add_edge_2: IsEdge v'' v''' g -> IsEdge v'' v''' (add_edge v v' g).
Parameter add_edge_3: ~Edges.E.eq (v, v') (v'', v''') -> IsEdge v v' (add_edge v'' v''' g) -> IsEdge v v' g.

Parameter add_edge_v1: IsVertex v g -> IsVertex v (add_edge v' v'' g).
Parameter add_edge_v2: IsVertex v (add_edge v v' g).
Parameter add_edge_v3: IsVertex v' (add_edge v v' g).
Parameter add_edge_v4: ~Vertices.E.eq v v' -> ~Vertices.E.eq v v'' ->
  IsVertex v (add_edge v' v'' g) -> IsVertex v g.

End Spec.

Definition vertex := Vertices.elt.

Add Relation vertex Vertices.E.eq
  as VertexSetoid.

Add Relation Edges.elt Edge.eq
  as EdgeSetoid.

Add Relation t Equal
  as EqualSetoid.

Add Morphism IsVertex with signature Vertices.E.eq ==> Equal ==> iff as IsVertex_m.
Proof.
  intros. destruct H0. split.
     intro. apply IsVertex_1 with x. apply H. rewrite <- (H0 x). apply H2. 
     intro. apply IsVertex_1 with y. symmetry. apply H. rewrite (H0 y). apply H2.
Qed.

Add Morphism IsEdge with signature Vertices.E.eq ==> Vertices.E.eq ==> Equal ==> iff as IsEdge_m.
Proof.
  intros. split.
     intro. apply IsEdge_1 with x x0. split. apply H. apply H0.
       rewrite <- H1. apply H2.
     intro. apply IsEdge_1 with y y0. split. symmetry. apply H. symmetry. apply H0.
       rewrite H1. apply H2.
Qed.

Add Morphism mem_edge with signature Vertices.E.eq ==> Vertices.E.eq ==> Equal ==> Logic.eq as mem_edge_m.
Proof.
  intros. apply eq_true_iff_eq. split.
    intros. apply <- mem_edge_spec. rewrite <- H. rewrite <- H0. rewrite <- H1.
    apply -> mem_edge_spec. apply H2.
    intros. apply <- mem_edge_spec. rewrite H. rewrite H0. rewrite H1.
    apply -> mem_edge_spec. apply H2.
Qed.

Add Morphism Subgraph with signature Equal ==> Equal ==> iff as Subgraph_m.
Proof.
  intros. destruct H. destruct H0. split.
    intros. destruct H3. split. 
      intros. rewrite <- (H0 v). apply H3. rewrite (H v). apply H5.  
      intros. rewrite <- (H2 v v'). apply H4. rewrite (H1 v v'). apply H5.
    intros. destruct H3. split.
      intros. rewrite (H0 v). apply H3. rewrite <- (H v). apply H5.
      intros. rewrite (H2 v v'). apply H4. rewrite <- (H1 v v'). apply H5.
Qed.

End DiGraph.

Module MGraphFacts (Import Vertices: S) (Import G: DiGraph Vertices).
Module Import VAux := Aux Vertices.

Function is_path' (g: t) (p: vertex) (l: list vertex) { struct l }: Prop :=
  match l with
  | nil => IsVertex p g
  | h::t => IsEdge p h g /\ is_path' g h t
  end.

Definition is_path (g: t) (l: list vertex) :=
  match l with
  | nil => True
  | h::t => is_path' g h t
  end.

Lemma is_path_cons: forall (g: t) (l: list vertex) (q: vertex),
  is_path g l -> IsEdge q (hd q l) g -> is_path g (q::l).
Proof.
  intros. simpl. destruct l.
      simpl. apply (proj2 (edge_vertex H0)).
      simpl. split. apply H0. apply H.
Qed.

Lemma direct_sublist_is_path: forall (g: t) (l' l: list vertex),
  direct_sublist l' l -> is_path g l -> is_path g l'.
Proof. 
  intros. functional induction (direct_sublist l' l).
    auto.
    contradiction.
    simpl. simpl in H0. destruct t0. 
      simpl in H0. rewrite (direct_sublist_nil t' H). apply H0.
      destruct t'.
        simpl. apply (edge_vertex (proj1 H0)).
        simpl in H. split.
          destruct (Aeq_dec v v0). rewrite <- e. apply (proj1 H0). contradiction.
          apply IHP. simpl. destruct (Aeq_dec v v0). apply H. contradiction.
        apply (proj2 H0).
    contradiction. 
Qed.   

Lemma is_path_red: forall g x l, is_path g (x::l) -> is_path g l. 
Proof.
  intros. induction l. 
    simpl. trivial. 
    apply H.
Qed.
        
Lemma sublist_is_path: forall (g: t) (l' l: list vertex),
  sublist l' l -> is_path g l -> is_path g l'.
Proof.
  intros. functional induction (sublist l' l).
    auto.
    destruct H. 
      apply (direct_sublist_is_path g l' (h::t0) H H0). 
      apply (IHP H (is_path_red g h t0 H0)).
Qed.

Function is_path_from_to (g: G.t) (l: list vertex) (p q: vertex) { struct l }: Prop :=
  match l with
  | nil => IsEdge p q g
  | h::t => IsEdge p h g /\ is_path_from_to g t h q
  end.  

Lemma ipft_app: forall g l l' p a q,
  is_path_from_to g l p a -> is_path_from_to g l' a q -> is_path_from_to g (l++(a::l')) p q.
Proof.
  intros. functional induction (is_path_from_to g l p a).
    simpl. split. apply H. apply H0.
    simpl. split. 
      apply (proj1 H).
      apply IHP. apply (proj2 H). apply H0.
Qed.

Lemma subpath_from_to: forall (g: G.t) (l: list vertex) (p q a: vertex),
  is_path_from_to g l p q -> List.In a l ->
  exists l': list vertex, sublist l' l /\ is_path_from_to g l' a q.
Proof.
  intros. functional induction (is_path_from_to g l p a).
    contradiction.
    destruct H0.
      simpl in H. exists t0. split.
        apply <- sublist_prop. exists 1. simpl. apply firstn_all.
        rewrite <- H0. apply (proj2 H).
      simpl in H. destruct (IHP (proj2 H) H0).
      exists x. split.
        simpl. right. apply (proj1 H1). 
        apply (proj2 H1).
Qed.
     
Definition connected g p q :=
  exists l, is_path_from_to g l p q.
     
Definition is_cycle (g: G.t) (l: list vertex): Prop :=
  match l with
  | nil => False
  | h::t => IsEdge (last t h) h g /\ is_path' g h t
  end.

Lemma cycle_is_path: forall g l, is_cycle g l -> is_path g l.
Proof.
  intros. destruct l.
    simpl. trivial. 
    simpl. simpl in H. apply (proj2 H).
Qed.

Lemma bla: forall g l p q, is_path g (p::l) -> List.In q l ->
  exists l', direct_sublist l' l /\ is_path_from_to g l' p q.
Proof.
  intros. simpl in H. functional induction (is_path' g p l).
    contradiction.
    destruct H0. 
      exists nil. split.
        simpl. trivial.
        simpl. rewrite <- H0. apply (proj1 H).
      destruct (IHP (proj2 H) H0).
        exists (h::x). destruct H1. split.
          apply direct_sublist_cons. apply H1. 
          simpl. split.
            apply (proj1 H).
            apply H2.
Qed.
 
Lemma path_stuff: forall g l p q, is_path g l -> List.In p l -> List.In q l ->
  Vertices.E.eq p q \/ exists l', sublist l' l /\
     (is_path_from_to g l' p q \/ is_path_from_to g l' q p).
Proof.
  intros. induction l. 
    (* l = nil *) contradiction.
    (* l = v::_ *) destruct H0. 
      (* l = p::_ *) destruct l.
        (* l = [p] *) destruct H1.
          (* p = q *) left. rewrite <- H0. rewrite <- H1. reflexivity.
          (* ... *) contradiction.
        (* l = p::v0::_ *) destruct (Vertices.E.eq_dec a q). 
           left. rewrite <- H0. apply e. 
           right. destruct (bla g (v::l) p q).
             rewrite <- H0. apply H. destruct H1.
               absurd (Vertices.E.eq a q). apply n. rewrite H1. reflexivity.
               apply H1.
             exists x. destruct H2. split. simpl. right. left. apply H2. left. apply H3.
     (* l = v::_ *) destruct H1.
       destruct (bla g l q p).
         rewrite <- H1. apply H.
         apply H0.
         right. exists x. destruct H2. split. simpl. right. apply direct_sublist_sublist. apply H2. right. apply H3.
     destruct IHl. 
       apply is_path_red with a. apply H. apply H0. apply H1. left. apply H2. right.
       destruct H2. exists x. destruct H2. split.
         simpl. right. apply H2.
         apply H3.
Qed.

Lemma cycle_is_cyclic: forall g l p q, is_cycle g l -> List.In p l -> List.In q l ->
  Vertices.E.eq p q \/ (exists l', incl l' l /\ is_path_from_to g l' q p).
Proof.
  intros. destruct l.
    contradiction.
    destruct (path_stuff g (v::l) p q (cycle_is_path g (v::l) H) H0 H1).
      left. apply H2.
      destruct H2 as [pq [Hpq [Hp | Hp]]].
        destruct H0. destruct H1.
          (* hd, hd *) left. rewrite <- H0. rewrite <- H1. reflexivity.
          (* hd, tl *) destruct (In_nth q l H1). destruct H2. 
            (* either q is the last one, or not *)
            destruct (le_lt_or_eq _ _ (lt_le_S _ _ H2)).
              destruct (bla g (skipn (S x) l) q (last l q)).
              rewrite (H3 v). rewrite (skipn_nth l H2 v). apply sublist_is_path with l. apply sublist_skipn.
              apply (is_path_red _ _ _ (cycle_is_path _ _ H)). trivial. 
              apply (last_skipn _ _ H4).
              right. exists (x0++(last l q::nil)). split.
                apply incl_app. apply incl_tl. unfold incl. intros. 
                apply sublist_incl with (skipn (S x) l).
                apply (direct_sublist_incl x0 _ _ H6 (proj1 H5)). apply sublist_skipn.
                apply incl_cons. right. apply last_In. intro. apply (lt_n_O (S x)). rewrite H6 in H4. apply H4.
                apply incl_nil.
             apply ipft_app. apply (proj2 H5). simpl.
               replace (last l q) with (last l v). rewrite <- H0. apply (proj1 H).
               apply last_irrelevant. intro. apply (lt_n_O (S x)). rewrite H6 in H4. apply H4.
             right. exists nil. split. apply incl_nil. simpl. rewrite (H3 v). rewrite (nth_last _ H4).
             rewrite <- H0. apply (proj1 H).
         destruct H1.
         (* tl, hd *) destruct (bla g l q p). 
           rewrite <- H1. apply (cycle_is_path _ _ H). apply H0.
           right. exists x. split. apply incl_tl. unfold incl. intros. apply (direct_sublist_incl x _ _ H3 (proj1 H2)).
           apply (proj2 H2).           
         (* tl, tl *)
           destruct (bla g l v p).
             apply (cycle_is_path _ _ H). apply H0. 
           destruct (In_nth q l H1). destruct H3.
            (* either q is the last one, or not *)
            destruct (le_lt_or_eq _ _ (lt_le_S _ _ H3)).
              destruct (bla g (skipn (S x0) l) q (last l q)).
              rewrite (H4 v). rewrite (skipn_nth l H3 v). apply sublist_is_path with l. apply sublist_skipn.
              apply (is_path_red _ _ _ (cycle_is_path _ _ H)). trivial. 
              apply (last_skipn _ _ H5).
              right. exists (x1++(last l q::v::nil)++x). split.
                apply incl_app. apply incl_tl. unfold incl. intros.
                apply sublist_incl with (skipn (S x0) l).
                apply (direct_sublist_incl x1 _ _ H7 (proj1 H6)). apply sublist_skipn.
                apply incl_cons. right. apply last_In. intro. apply (lt_n_O (S x0)). rewrite H7 in H5. apply H5.
                apply incl_cons. left. reflexivity. apply incl_tl. unfold incl. intros.
                apply direct_sublist_incl with x. apply H7. apply (proj1 H2).
              apply ipft_app. apply (proj2 H6). simpl. split.
                replace (last l q) with (last l v). apply (proj1 H). apply last_irrelevant.
                intro. apply (lt_n_O (S x0)). rewrite H7 in H5. apply H5.
                apply (proj2 H2).
              right. exists (v::x). split. apply incl_cons. left. reflexivity. apply incl_tl. unfold incl. intros. apply direct_sublist_incl with x. apply H6. apply (proj1 H2).
              rewrite (H4 v). rewrite (nth_last _ H5). simpl. split.
                apply (proj1 H). apply (proj2 H2).
  right. exists pq. split.
    unfold incl. intros. apply sublist_incl with pq. apply H2. apply Hpq.
    apply Hp.
Qed.

Definition is_clique (g: G.t) (V: Vertices.t): Prop :=
  Vertices.For_all (fun v =>
    Vertices.For_all (fun v' =>
     ~Vertices.E.eq v v' -> IsEdge v v' g)
    V)
  V.

Definition is_maximal_clique (g: G.t) (V: Vertices.t): Prop :=
  is_clique g V /\ ~exists V', is_clique g V' /\ V [<] V'.

Definition pred (g: G.t) (v: vertex): Vertices.t :=
  filter (fun v' => mem_edge v' v g) (vertices g).

Lemma cpt_pred: forall g (v: vertex),
  Proper (Vertices.E.eq ==> Logic.eq) (fun v' => mem_edge v' v g).
Proof.
  intros. compute. intros. rewrite H. reflexivity.
Qed.
        
Lemma cpt_pred_empty: forall g,
  Proper (Vertices.E.eq ==> Logic.eq)
    (fun x : elt => Vertices.is_empty (pred g x)).
Proof.
  intros. compute. intros. apply eq_true_iff_eq. split.
    intros. apply <- is_empty_spec. intro. intro.
    apply (proj1 (iff_and (is_empty_spec _)) H0 a).
      apply filter_spec. apply cpt_pred. rewrite H.
      apply (proj1 (iff_and (filter_spec (vertices g) a (cpt_pred g y))) H1).
    intros. apply <- is_empty_spec. intro. intro.
      apply (proj1 (iff_and (is_empty_spec _)) H0 a).
      apply filter_spec. apply cpt_pred. rewrite <- H.
      apply (proj1 (iff_and (filter_spec (vertices g) a (cpt_pred g x))) H1). 
Qed.

Lemma pred_spec: forall g v v',
  In v' (pred g v) <-> IsEdge v' v g.
Proof.
  intros. split.
    intros. apply -> mem_edge_spec. unfold pred in H. 
    apply (proj1 (iff_and (filter_spec (vertices g) v' (cpt_pred g v))) H). 
    intros. unfold pred. apply <- (filter_spec (vertices g) v' (cpt_pred g v)). split.
      apply <- vertices_spec. apply (proj1 (edge_vertex H)).
      apply mem_edge_spec. apply H.
Qed.

Definition succ (g: G.t) (v: vertex): Vertices.t :=
  filter (fun v' => mem_edge v v' g) (vertices g).

Lemma cpt_succ: forall g (v: vertex),
  Proper (Vertices.E.eq ==> Logic.eq) (fun v' => mem_edge v v' g).
Proof.
  intros. unfold Proper. compute. intros. apply eq_true_iff_eq. split.
    intros. apply <- mem_edge_spec. rewrite <- H. apply -> mem_edge_spec. apply H0.
    intros. apply <- mem_edge_spec. rewrite H. apply -> mem_edge_spec. apply H0.
Qed.

Lemma succ_spec: forall g v v',
  In v' (succ g v) <-> IsEdge v v' g.
Proof. 
  intros. split. 
    intros. apply -> mem_edge_spec. unfold succ in H.
    apply (proj1 (iff_and (filter_spec (vertices g) v' (cpt_succ g v))) H). 
    intros. unfold succ. apply <- (filter_spec (vertices g) v' (cpt_succ g v)). split.
      apply <- vertices_spec. apply (proj2 (edge_vertex H)).
      apply mem_edge_spec. apply H.
Qed.

End MGraphFacts.

Unset Implicit Arguments.
