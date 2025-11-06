Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.

Parameter Sigma : Set.

Inductive RE : Set :=
| REemptyset : RE
| REemptystring: RE
| REchar (c : Sigma) : RE
| REconcat : RE -> RE -> RE
| REstar : RE -> RE
| REdisj : RE -> RE -> RE
| REconj : RE -> RE -> RE
| REneg : RE -> RE.

Definition string := list Sigma.

Definition lang := string -> Prop.


Inductive restar (l: lang) : lang (* string -> Prop *) :=
| Star0 : restar l []
| StarS : forall s0 s1, l s0 -> restar l s1 -> restar l (s0 ++ s1).

(* 2 *)
Fixpoint re_interp (re : RE) : lang :=
  match re with
  | REemptyset => fun (s : string) => False
  | REemptystring => fun (s: string) => s = []
  | REchar c => fun s => s = [c]
  | REconcat re0 re1 => fun s => exists s0 s1, s = s0 ++ s1 /\ re_interp re0 s0 /\ re_interp re1 s1
  | REstar re' => restar (re_interp re') (* fun s => restar (re_interp re') s *)
  | REdisj re0 re1 => fun s => re_interp re0 s \/ re_interp re1 s
  | REconj re0 re1 => fun s => re_interp re0 s /\ re_interp re1 s
  | REneg re => fun s => ~ re_interp re s
  end.


Definition deriv (c: Sigma) (l: lang) : lang :=
  fun s => l (cons c s).

(* lang contains empty string *)
Fixpoint nullable (re :RE) : bool :=
  match re with
  | REemptyset => false
  | REemptystring => true
  | REchar _ => false
  | REconcat re0 re1 => (nullable re0) && (nullable re1)
  | REstar _ => true
  | REdisj re0 re1 => nullable re0 || nullable re1
  | REconj re0 re1 => nullable re0 && nullable re1
  | REneg re => negb (nullable re)
  end.

Theorem nullable_correct : forall re,
  nullable re = true <-> re_interp re [].
Proof.
  induction re.
  - admit.
  - split; simpl; intros; reflexivity.
  - split; simpl; intros; discriminate.
  - split; destruct IHre1; destruct IHre2.
    + simpl. intros.
      exists []. exists [].
      simpl.
      admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - split; destruct IHre; destruct (nullable re).
    + simpl. intros. apply H0 in H.
      * admit

