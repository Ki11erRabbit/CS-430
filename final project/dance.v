From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Definition partner: Type := nat.
Definition partner_ring: Type := list partner.
Definition dance_ring: Type := (partner_ring * partner_ring).

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


Fixpoint make_dance_ring (size : nat) (ring : dance_ring) : dance_ring :=
  match size, ring with 
  | O, (inner, outer) => (0 :: inner, 0 ::outer)
  | S size', (inner, outer) => make_dance_ring size' ((size :: inner), (size :: outer))
  end.

Definition dance_ring_length (ring: dance_ring) : nat :=
  match ring with
  | (x, _) => length x
  end.

Definition dance_ring_eqb (ring1 ring2: dance_ring) : bool :=
  match ring1, ring2 with
  | (x1, y1), (x2, y2) => partner_ring_eqb x1 x2 && partner_ring_eqb y1 y2
  end.

Definition dance_ring_eq_dec (ring1 ring2: dance_ring) : { ring1 = ring2 } + { ring1 <> ring2 }.
  decide equality; apply list_eq_dec; apply Nat.eq_dec.
Defined.


Theorem dance_ring_equal_to_self: forall (ring : dance_ring),
  dance_ring_eqb ring ring = true.
Proof.
  intros ring.
  destruct ring.
  simpl.
  rewrite partner_ring_equal_to_self.
  rewrite partner_ring_equal_to_self.
  reflexivity.
Qed.


Inductive movement : Type :=
| InnerMoveForwardOne
| InnerMoveBackwardOne
| InnerMoveForwardTwo
| InnerMoveBackwardTwo
| OuterMoveForwardOne
| OuterMoveBackwardOne
| OuterMoveForwardTwo
| OuterMoveBackwardTwo
| SwapInnerOuter.


Definition partner_ring_forward_one (ring : partner_ring) : partner_ring :=
  match ring with 
  | [] => []
  | x :: rest => rest ++ [x]
  end.

Definition partner_ring_forward_two (ring : partner_ring) : partner_ring :=
  partner_ring_forward_one (partner_ring_forward_one ring).

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


Definition partner_ring_backward_two (ring: partner_ring) : partner_ring :=
  partner_ring_backward_one (partner_ring_backward_one ring).


Definition move_dance_ring (movement : movement) (ring: dance_ring) : dance_ring :=
  match movement, ring with 
  | InnerMoveForwardOne, (inner, outer) => ((partner_ring_forward_one inner), outer)
  | InnerMoveBackwardOne, (inner, outer) => ((partner_ring_backward_one inner), outer)
  | InnerMoveForwardTwo, (inner, outer) => ((partner_ring_forward_two inner), outer)
  | InnerMoveBackwardTwo, (inner, outer) => ((partner_ring_backward_two inner), outer)
  | OuterMoveForwardOne, (inner, outer) => (inner, (partner_ring_forward_one outer))
  | OuterMoveBackwardOne, (inner, outer) => (inner, (partner_ring_backward_one outer))
  | OuterMoveForwardTwo, (inner, outer) => (inner, (partner_ring_forward_two outer))
  | OuterMoveBackwardTwo, (inner, outer) => (inner, (partner_ring_backward_two outer))
  | SwapInnerOuter, (inner, outer) => (outer, inner)
  end. 

Theorem inner_move_forward_one : forall (p_inner : partner) (ring_inner ring_outer : partner_ring),
  move_dance_ring InnerMoveForwardOne ((p_inner :: ring_inner), ring_outer) = ((ring_inner ++ [p_inner]), ring_outer).
Proof.
  intros p_inner ring_inner.
  destruct ring_inner.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem inner_move_backward_one : forall (p_inner : partner) (ring_inner ring_outer : partner_ring),
  move_dance_ring InnerMoveBackwardOne ((ring_inner ++ [p_inner]), ring_outer) = ((p_inner :: ring_inner), ring_outer).
Proof.
  intros p_inner ring_inner ring_outer.
  simpl.
  rewrite partner_ring_backward_one_moves_to_front.
  reflexivity.
Qed.



Fixpoint apply_dance_n (ring : dance_ring) (n : nat) (dance : dance_ring -> dance_ring) :=
  match n with
  | O => ring
  | S n' => apply_dance_n (dance ring) n' dance
  end.


Definition anis_waltz_one (ring: dance_ring) : dance_ring :=
  (move_dance_ring InnerMoveBackwardOne 
    (move_dance_ring OuterMoveForwardOne 
      (move_dance_ring SwapInnerOuter 
        (move_dance_ring InnerMoveBackwardTwo 
          (move_dance_ring SwapInnerOuter 
            (move_dance_ring InnerMoveBackwardTwo ring)))))).

(* This is missing two line movements but since they undo each other I think it is fine to ignore them. *)
Definition korobushka_one (ring: dance_ring) : dance_ring :=
  (move_dance_ring SwapInnerOuter 
    (move_dance_ring InnerMoveBackwardOne 
      (move_dance_ring OuterMoveForwardOne 
        (move_dance_ring SwapInnerOuter ring)))).

Theorem korobushka_shifts_one : forall (p_inner p_outer_start p_outer_end : partner) (ring_inner ring_outer : partner_ring),
  (dance_ring_eqb (korobushka_one ((p_inner :: ring_inner), (p_outer_start :: (ring_outer ++ [p_outer_end])))) ((ring_inner ++ [p_inner]),(p_outer_end :: p_outer_start :: ring_outer))) = true.
Proof.
  intros p_inner p_outer_start p_outer_end ring_inner ring_outer.
  simpl.
  induction ring_inner; induction ring_outer.
  - simpl. rewrite eqb_refl. rewrite eqb_refl. rewrite eqb_refl. reflexivity.
  - simpl. rewrite eqb_refl. simpl.

Theorem korobushka_n_start_eq_end: forall (ring: dance_ring) (n: nat),
  n = (dance_ring_length ring) -> (dance_ring_eqb (apply_dance_n ring n korobushka_one) ring) = true.
Proof.
  intros ring n.
  intros H.
  induction n.
  - simpl. rewrite dance_ring_equal_to_self. reflexivity.
  - simpl. rewrite <- IHn.
    + 
    +  


