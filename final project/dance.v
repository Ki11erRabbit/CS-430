From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ProofIrrelevance.

Definition partner: Type := nat.
Definition partner_ring: Type := list partner.


Fixpoint partner_ring_eqb (ring1 ring2: partner_ring) : bool :=
  match ring1, ring2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | (x :: xs), (y :: ys) => if x =? y then partner_ring_eqb xs ys else false
  end.

Definition partner_ring_eq_dec (ring1 ring2: partner_ring) := list_eq_dec Nat.eq_dec.


Theorem partner_ring_equal_to_self: forall (ring : partner_ring),
  partner_ring_eqb ring ring = true.
Proof.
  intros ring.
  induction ring.
  - reflexivity.
  - simpl. 
    Search (_ =? _).
    rewrite eqb_refl.
    apply IHring.
Qed.

Record dance_ring := make_dance_ring_internal {
  inner_ring : partner_ring;
  outer_ring : partner_ring;
  ring_well_formed : length inner_ring = length outer_ring
}.

Definition make_dance_ring (n: nat) : dance_ring.
Proof.
  (* Build the two rings *)
  set (inner := seq 0 n).           (* [0; 1; 2; ...; n-1] *)
  set (outer := seq 0 n).           (* [n; n+1; ...; 2n-1] *)
  
  (* Create the record *)
  refine (make_dance_ring_internal inner outer _).
  
  (* Prove they have equal length *)
  unfold inner, outer.
  repeat rewrite length_seq.
  reflexivity.
Defined.

Definition dance_ring_swap (ring : dance_ring) : dance_ring.
Proof.
  destruct ring as [inner_ring outer_ring proof].
  refine (make_dance_ring_internal outer_ring inner_ring _).
  symmetry in proof.
  apply proof.
Defined.


Definition dance_ring_length (ring: dance_ring) : nat :=
  length (inner_ring ring).

Definition dance_ring_eqb (ring1 ring2: dance_ring) : bool :=
  partner_ring_eqb (inner_ring ring1) (inner_ring ring2) && partner_ring_eqb (outer_ring ring1) (outer_ring ring2).

Definition dance_ring_eq_dec (ring1 ring2: dance_ring) : { ring1 = ring2 } + { ring1 <> ring2 }.
Proof.
  destruct ring1 as [inner1 outer1 H1].
  destruct ring2 as [inner2 outer2 H2].
  
  (* First decide if inner rings are equal *)
  destruct (list_eq_dec Nat.eq_dec inner1 inner2) as [H_inner | H_inner].
  - (* inner1 = inner2 *)
    destruct (list_eq_dec Nat.eq_dec outer1 outer2) as [H_outer | H_outer].
    + (* outer1 = outer2 *)
      (* Both components equal, so records are equal *)
      left.
      subst inner2. subst outer2.
      (* Now need to show the proofs are equal *)
      (* Use proof irrelevance *)
      f_equal.
      apply proof_irrelevance.
    + (* outer1 <> outer2 *)
      right.
      intro H_contra.
      injection H_contra as H_i H_o.
      contradiction.
  - (* inner1 <> inner2 *)
    right.
    intro H_contra.
    injection H_contra as H_i H_o.
    contradiction.
Defined.

Lemma make_dance_ring_eq: forall inner outer (H1 H2: length inner = length outer),
  make_dance_ring_internal inner outer H1 = make_dance_ring_internal inner outer H2.
Proof.
  intros.
  f_equal.
  apply proof_irrelevance.
Qed.

Inductive movement : Type :=
| InnerMoveForwardOne
| InnerMoveBackwardOne
| OuterMoveForwardOne
| OuterMoveBackwardOne
| SwapInnerOuter.


Definition partner_ring_forward_one (ring : partner_ring) : partner_ring :=
  match ring with 
  | [] => []
  | x :: rest => rest ++ [x]
  end.

Definition partner_ring_backward_one (ring: partner_ring) : partner_ring :=
  match (rev ring) with 
  | [] => []
  | x :: rest => x :: (rev rest)
  end.

Theorem partner_ring_backward_one_moves_to_front : forall (p: partner) (ring: partner_ring),
  partner_ring_backward_one (ring ++ [p]) = p :: ring.
Proof.
  intros p ring.
  unfold partner_ring_backward_one.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem partner_ring_forward_one_preserves_length : forall (ring : partner_ring),
  length ring = length (partner_ring_forward_one ring).
Proof.
  intros ring.
  destruct ring.
  - simpl. reflexivity.
  - simpl. Search (length (_ ++ [_])).
    rewrite last_length.
    reflexivity.
Qed.

Theorem partner_ring_backward_one_preserves_length : forall (ring : partner_ring),
  length ring = length (partner_ring_backward_one ring).
Proof.
  intros ring.
  destruct ring as [| p ring'] using rev_ind.
  - (* ring = [] *)
    simpl. reflexivity.
  - (* ring = ring' ++ [p] *)
    unfold partner_ring_backward_one.
    rewrite rev_app_distr.
    simpl.
    rewrite length_rev.
    rewrite length_app.
    simpl.
    rewrite length_rev.
    Search (_ + 1).
    rewrite add_1_r.
    reflexivity.
Qed.

Lemma dance_ring_eq : forall (inner1 inner2 outer1 outer2 : partner_ring)
  (H1 : length inner1 = length outer1)
  (H2 : length inner2 = length outer2),
  inner1 = inner2 -> outer1 = outer2 ->
  make_dance_ring_internal inner1 outer1 H1 = make_dance_ring_internal inner2 outer2 H2.
Proof.
  intros inner1 inner2 outer1 outer2 H1 H2 Hinner Houter.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.
  

Definition dance_ring_move (movement : movement) (ring: dance_ring) : dance_ring.
Proof.
  destruct ring as [inner_ring outer_ring ring_well_formed].
  destruct movement.
  - refine (make_dance_ring_internal (partner_ring_forward_one inner_ring) outer_ring _).
    rewrite <- partner_ring_forward_one_preserves_length.
    apply ring_well_formed.
  - refine (make_dance_ring_internal (partner_ring_backward_one inner_ring) outer_ring _).
    rewrite <- partner_ring_backward_one_preserves_length.
    apply ring_well_formed.
  - refine (make_dance_ring_internal inner_ring (partner_ring_forward_one outer_ring) _).
    rewrite <- partner_ring_forward_one_preserves_length.
    apply ring_well_formed.
  - refine (make_dance_ring_internal inner_ring (partner_ring_backward_one outer_ring) _).
    rewrite <- partner_ring_backward_one_preserves_length.
    apply ring_well_formed.
  - refine (make_dance_ring_internal outer_ring inner_ring _).
    symmetry in ring_well_formed.
    apply ring_well_formed.
Defined.


Theorem dance_ring_inner_move_forward_one : forall (p_inner : partner) (ring_inner ring_outer : partner_ring) 
(Hin: length (p_inner :: ring_inner) = length ring_outer) 
(Hout: length (ring_inner ++ [p_inner]) = length ring_outer) 
(Hinner_eq: length (p_inner :: ring_inner) = length (ring_inner ++ [p_inner])),
  dance_ring_move InnerMoveForwardOne (make_dance_ring_internal (p_inner :: ring_inner) ring_outer Hin) = (make_dance_ring_internal (ring_inner ++ [p_inner]) ring_outer Hout).
Proof.
  intros p_inner ring_inner ring_outer Hin Hout Hinner_eq.
  unfold dance_ring_move.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem dance_ring_inner_move_backward_one : forall (p_inner : partner) (ring_inner ring_outer : partner_ring) 
(Hin: length (ring_inner ++ [p_inner]) = length ring_outer) 
(Hout: length (p_inner :: ring_inner) = length ring_outer) 
(Hinner_eq: length (ring_inner ++ [p_inner]) = length (p_inner :: ring_inner)),
  dance_ring_move InnerMoveBackwardOne (make_dance_ring_internal (ring_inner ++ [p_inner]) ring_outer Hin) = 
  (make_dance_ring_internal (p_inner :: ring_inner) ring_outer Hout).
Proof.
  intros p_inner ring_inner ring_outer Hin Hout Hinner_eq.
  unfold dance_ring_move; simpl.
  apply dance_ring_eq.
  - apply partner_ring_backward_one_moves_to_front.
  - reflexivity.
Qed.


Theorem dance_ring_outer_move_forward_one : forall (p_outer : partner) (ring_inner ring_outer : partner_ring) 
(Hin: length ring_inner = length (p_outer :: ring_outer)) 
(Hout: length ring_inner = length (ring_outer ++ [p_outer])) 
(Hinner_eq: length (p_outer :: ring_outer) = length (ring_outer ++ [p_outer])),
  dance_ring_move OuterMoveForwardOne (make_dance_ring_internal ring_inner (p_outer :: ring_outer) Hin) = (make_dance_ring_internal ring_inner (ring_outer ++ [p_outer]) Hout).
Proof.
  intros p_outer ring_inner ring_outer Hin Hout Hinner_eq.
  unfold dance_ring_move.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem dance_ring_outer_move_backward_one : forall (p_outer : partner) (ring_inner ring_outer : partner_ring) 
(Hin: length ring_inner = length (ring_outer ++ [p_outer])) 
(Hout: length ring_inner = length (p_outer :: ring_outer)) 
(Hinner_eq: length (ring_outer ++ [p_outer]) = length (p_outer :: ring_outer)),
  dance_ring_move OuterMoveBackwardOne (make_dance_ring_internal ring_inner (ring_outer ++ [p_outer]) Hin) = 
  (make_dance_ring_internal ring_inner (p_outer :: ring_outer) Hout).
Proof.
  intros p_inner ring_inner ring_outer Hin Hout Hinner_eq.
  unfold dance_ring_move; simpl.
  apply dance_ring_eq.
  - reflexivity.
  - apply partner_ring_backward_one_moves_to_front.
Qed.

Theorem outer_inner_swap : forall (ring_inner ring_outer : partner_ring)
  (Hin : length ring_inner = length ring_outer)
  (Hout : length ring_outer = length ring_inner),
  dance_ring_move SwapInnerOuter (make_dance_ring_internal ring_inner ring_outer Hin) = (make_dance_ring_internal ring_outer ring_inner Hout).
Proof.
  intros ring_inner ring_outer Hin Hout.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem movement_preserves_length : forall (ring : dance_ring) (movement: movement),
  dance_ring_length ring = dance_ring_length (dance_ring_move movement ring).
Proof.
  intros ring movement.
  destruct ring as [inner_ring outer_ring ring_well_formed].
  destruct movement; unfold dance_ring_move, dance_ring_length; simpl; try reflexivity.
  - rewrite partner_ring_forward_one_preserves_length. reflexivity.
  - rewrite partner_ring_backward_one_preserves_length. reflexivity.
  - apply ring_well_formed.
Qed.


Fixpoint apply_dance_n (ring : dance_ring) (n : nat) (dance : dance_ring -> dance_ring) :=
  match n with
  | O => ring
  | S n' => apply_dance_n (dance ring) n' dance
  end.


(* This is missing two line movements but since they undo each other I think it is fine to ignore them. *)
Definition korobushka_one (ring: dance_ring) : dance_ring :=
  (dance_ring_move SwapInnerOuter 
    (dance_ring_move InnerMoveBackwardOne 
      (dance_ring_move OuterMoveForwardOne 
        (dance_ring_move SwapInnerOuter ring)))).

(*
Theorem korobushka_shifts_one : forall (p_inner p_outer_start p_outer_end : partner) (ring_inner ring_outer : partner_ring),
  (korobushka_one ((p_inner :: ring_inner), (p_outer_start :: (ring_outer ++ [p_outer_end])))) = ((ring_inner ++ [p_inner]),(p_outer_end :: p_outer_start :: ring_outer)).
Proof.
  intros p_inner p_outer_start p_outer_end ring_inner ring_outer.
  simpl.
  unfold korobushka_one.
  rewrite outer_inner_swap.
  rewrite outer_move_forward_one.
  unfold dance_ring_move.
  rewrite <- partner_ring_backward_one_moves_to_front.
  simpl.
  unfold partner_ring_backward_one.
  simpl.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  simpl.
  reflexivity.
Qed.
*)

Lemma korobushka_shifts_one : forall (p_inner p_outer_start p_outer_end : partner) (ring_inner ring_outer : partner_ring) (H1: length (p_inner :: ring_inner) = length (p_outer_start :: (ring_outer ++ [p_outer_end]))) (H2: length (ring_inner ++ [p_inner]) = length (p_outer_end :: p_outer_start :: ring_outer)) (Heq1: length (p_inner :: ring_inner) = length (ring_inner ++ [p_inner])) (Heq2: length (p_outer_start :: (ring_outer ++ [p_outer_end])) = length (p_outer_end :: p_outer_start :: ring_outer)),
  (korobushka_one (make_dance_ring_internal (p_inner :: ring_inner) (p_outer_start :: (ring_outer ++ [p_outer_end])) H1)) = (make_dance_ring_internal (ring_inner ++ [p_inner]) (p_outer_end :: p_outer_start :: ring_outer) H2). 
Proof.
  intros.
  unfold korobushka_one.
  rewrite outer_inner_swap.

Lemma korobushka_n_rotation: forall (inner outer: partner_ring) (n: nat) (H: length inner = length outer),
  n = length inner ->
  apply_dance_n (make_dance_ring_internal inner outer H) n korobushka_one = 
  (make_dance_ring_internal inner outer H).
Proof.
  intros inner.
  induction inner as [| p_inner inner IHinner]; intros outer n Hlen_eq Hlen; destruct outer as [| p_outer outer].
  - simpl in Hlen_eq. simpl in Hlen.
    subst. simpl. reflexivity.
  - simpl in Hlen.
    simpl in Hlen_eq.
    subst.
    simpl.
    reflexivity.
  - simpl in Hlen_eq.
    simpl in Hlen.
    subst.
    simpl.
    discriminate.
  - simpl in Hlen.
    simpl in Hlen_eq.
    subst.
    simpl.


Theorem korobushka_n_start_eq_end: forall (ring: dance_ring) (n: nat),
  n = (dance_ring_length ring) -> (apply_dance_n ring n korobushka_one) = ring.
Proof.
  intros ring n.
  intros H.
  induction n.
  - simpl. reflexivity.
  - unfold dance_ring_length in H, IHn.
      


    




Definition anis_waltz_one (ring: dance_ring) : dance_ring :=
  (dance_ring_move InnerMoveBackwardOne 
    (dance_ring_move OuterMoveForwardOne 
      (dance_ring_move SwapInnerOuter 
        (dance_ring_move InnerMoveBackwardOne 
          (dance_ring_move InnerMoveBackwardOne 
            (dance_ring_move SwapInnerOuter 
              (dance_ring_move InnerMoveForward 
                (dance_ring_move InnerMoveForward ring)))))))).
