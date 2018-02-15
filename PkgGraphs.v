Require Import MGraph.
Require Import Packages.

Parameter R: PackageSet.t.
Parameter C: ConflictSet.t.
Parameter Dependencies: Package.t -> list PackageSet.t.

Declare Module PkgGraph: DiGraph PackageSet.
Import PkgGraph.

Module PkgFacts := MGraphFacts PackageSet PkgGraph.
Import PkgFacts.
Module PkgAux := Aux PackageSet.

Parameter sdg: PkgGraph.t.

Axiom sdg_edge: forall p p', IsEdge p p' sdg <-> strong_dep Dependencies R C p p'.

Definition is_lift (S: PackageSet.t) (l: list Package.t) :=
  forall s, In s S <-> List.In s l.

Lemma sdg_transitive: forall p q, connected sdg p q -> IsEdge p q sdg.
Proof.
  intros. unfold connected in H. destruct H as [l Hl]. 
  functional induction (is_path_from_to sdg l p q).
    apply Hl.
    apply <- sdg_edge. apply strong_dep_trans with h. split.
      apply -> sdg_edge. apply (proj1 Hl).
      apply -> sdg_edge. apply (IHP (proj2 Hl)).
Qed.
          
(* lemma 3.12 *)
Lemma cycle_is_clique: forall l, is_cycle sdg l -> is_clique sdg (PkgAux.equiv_set l).
Proof.
  intros. unfold is_clique. unfold For_all. intros x Hx x' Hx' Hneq.
  elim (path_stuff sdg l x x' (cycle_is_path _ _ H) (PkgAux.equiv_set_2 Hx) (PkgAux.equiv_set_2 Hx')).
    intros. absurd (Package.eq x x'). apply Hneq. apply H0.
    intros. destruct H0 as [p [Hinc [Hf | Hf]]]. 
      apply sdg_transitive. exists p. apply Hf.
      apply sdg_transitive. destruct (cycle_is_cyclic sdg l x' x H (PkgAux.equiv_set_2 Hx') (PkgAux.equiv_set_2 Hx)).
        absurd (Package.eq x x'). apply Hneq. apply (Package.eq_sym H0).
        destruct H0. exists x0. apply (proj2 H0). 
Qed.

(* the collapse graph is the detransed decycled version of sdg with start *)
Inductive clp_node: Type :=
  start: clp_node
| collapse: Package.t -> PackageSet.t -> clp_node. (* at least one node *)

Declare Module Clp: OrderedType with Definition t := clp_node.
Declare Module CollapseSet: MSetInterface.S with Module E := Clp.
Declare Module FlowGraph: DiGraph CollapseSet.
Module FGFacts := MGraphFacts CollapseSet FlowGraph.

Parameter fg: FlowGraph.t.

Axiom collapse_start: FlowGraph.IsVertex start fg.
(* Axiom collapse_vertex_1a: forall p ps,
  FlowGraph.IsVertex (collapse p ps) fg -> For_all (fun x => IsVertex x sdg) (add p ps).
Axiom collapse_vertex_1b: forall p,
  IsVertex p sdg -> exists ps, In p ps /\ FlowGraph.IsVertex (collapse ps) fg.
Axiom collapse_vertex_2: forall ps,
  FlowGraph.IsVertex (collapse ps) fg <-> is_maximal_clique sdg ps. *)
Axiom collapse_edge_start: forall p ps,
  For_all (fun v => Empty (pred sdg v)) (add p ps) ->
  FlowGraph.IsEdge start (collapse p ps) fg.
(* Axiom collapse_edge_1a: forall ps ps', FlowGraph.IsEdge (collapse ps) (collapse ps') fg ->
  exists p, In p ps /\ exists p', In p' ps /\ connected sdg p p'. *)
Axiom collapse_edge_1b: forall p ps p' ps', 
  Exists (fun v => Exists (fun v' => IsEdge v v' sdg) (add p' ps')) (add p ps) ->
  FlowGraph.IsEdge (collapse p ps) (collapse p' ps') fg.
Axiom collapse_detrans: forall p q r, 
  FlowGraph.IsEdge p q fg -> FlowGraph.IsEdge q r fg -> ~FlowGraph.IsEdge p r fg.

(* lemma 3.16 *)
Lemma reachable_from_start: forall p ps, FlowGraph.IsVertex (collapse p ps) fg ->
  FGFacts.connected fg start (collapse p ps).
Proof.
  intros. case_eq (for_all (fun v => PackageSet.is_empty (pred sdg v)) (add p ps)).
    (* if all predecessors of p/ps are empty, we're done *)
    intros. exists nil. apply collapse_edge_start. unfold For_all. intros. 
    apply is_empty_spec. apply (for_all_2 (cpt_pred_empty sdg) H0 H1).
    (* but if not, then we must do something more complicated *)
     
   
    
      
    


