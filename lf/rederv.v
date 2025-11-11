Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.

Parameter Sigma : Set.
Parameter eq_sigma_dec : forall (c0 c1 : Sigma), { c0 = c1 } + { c0 <> c1 }.

Inductive RE : Set :=
| REemptyset : RE
| REemptystring: RE
| REchar (c : Sigma) : RE
| REconcat : RE -> RE -> RE
| REstar : RE -> RE
| REdisj : RE -> RE -> RE
| REconj : RE -> RE -> RE
| REneg : RE -> RE.

Definition disj (re0 re1 : RE) : RE :=
  match re0, re1 with
  | REemptyset, _ => re1
  | _, REemptyset => re0
  | _, _ => REdisj re0 re1
  end.


Check REdisj REemptyset REemptystring.

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
      * admit.
      * admit.
    + admit.
    + admit.
    + admit.
Admitted.

Definition v (re : RE) : RE := if nullable re then REemptystring else REemptyset.

Definition conj (re0 re1 : RE) : RE :=
  match re0, re1 with
  | REemptyset, _ => REemptyset
  | _, REemptyset => REemptyset
  | REemptystring, _ => REemptystring
  | _, REemptystring => REemptystring
  | _, _ => REconj re0 re1
  end.

Definition concat (re0 re1 : RE) : RE :=
  match re0, re1 with
  | REemptyset, _ => REemptyset
  | _, REemptyset => REemptyset
  | REemptystring, _ => re1
  | _, REemptystring => re0
  | _, _ => REconcat re0 re1
  end.

Fixpoint rederiv (c : Sigma) (re: RE) : RE :=
  match re with
  | REemptyset => REemptyset
  | REemptystring => REemptyset
  | REchar c' => if eq_sigma_dec c c' then REemptystring else REemptyset
  | REconcat re0 re1 => disj (concat (rederiv c re0) re1) (concat (v re0) (rederiv c re1))
  | REstar re' => concat (rederiv c re') (REstar re')
  | REdisj re0 re1 => disj (rederiv c re0) (rederiv c re1)
  | REconj re0 re1 => conj (rederiv c re0) (rederiv c re1)
  | REneg re' => REneg (rederiv c re')
  end.

Definition lang_equiv (l0 l1 : lang) := forall (s : string),
  l0 s <-> l1 s.

(* deriv lang correspond and related through our meaning function *)
Theorem deriv_equiv_rederiv : forall (c : Sigma) (re : RE),
  deriv c (re_interp re) = re_interp (rederiv c re).
Proof.
  intros.
  unfold deriv.
  unfold re_interp.
