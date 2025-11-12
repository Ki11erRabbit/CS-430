From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Definition partner: Type := nat.
Definition partner_ring: Type := list nat.
Definition dance_ring: Type := (partner_ring * partner_ring).


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
  | (x1, y1), (x2, y2) => if (list_eq_dec Nat.eq_dec x1 x2) then (if (list_eq_dec Nat.eq_dec y1 y2) then true else false) else false
  end.


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


Theorem korobushka_n_start_eq_end: forall (ring: dance_ring) (n: nat),
  n = (dance_ring_length ring) -> (dance_ring_eqb (apply_dance_n ring n korobushka_one) ring) = true.
Proof


