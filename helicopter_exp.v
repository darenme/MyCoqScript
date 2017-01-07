Require Import Reals.

Open Scope R_scope.

Definition Real := R.

(* declare variables in exp-flaring rule. *)
(* 
   Hl02 is the acceleration of the trace of exp-flaring.
   qieta is the constant of time.
   Hd2 is the dropping acceleration.
   deltaHl0 is the difference of H(the initial height) and Hxt(the hanging height).
   K is the time that the height of helicopter drop to the hanging height.
*)
Variables Hl02 qieta Hd2 : Real.

Variables deltaHl0 K : Real.

Definition tm1 := Hl02 - deltaHl0 / (qieta * qieta) .
Definition tm2 := Hd2 -  K * K / 2.
Definition tm3 := Hl02 - Hd2.

(* assumptions of this deduction. *)
Axiom e1 : tm1 = 0.
Axiom e2 : tm2 = 0.
Axiom e3 : tm3 = 0.
Axiom e5 : 0 <= K * K.
Axiom e6 : 0 < qieta * qieta.
Axiom e7 : 0 <= K * K / 2.
Axiom e8 : 0 <= sqrt (deltaHl0 / (qieta * qieta)).
Axiom e9 : 0 <= deltaHl0 / (qieta * qieta).

Definition tm5 :=  K * K / 2.
Definition tm6 := Hd2.
Definition tm7 := Hl02.


Lemma eq0_eq : forall y z, y-z = 0 -> y = z.
intros.
apply sym_eq.
apply Rminus_diag_uniq_sym.
assumption.
Qed.

Lemma  tm5_eq_tm6 : tm5 = tm6.
apply sym_eq.
apply eq0_eq.
unfold tm5;unfold tm6.
apply e2.
Qed.

Lemma  tm6_eq_tm7 : tm6 = tm7.
apply sym_eq.
apply eq0_eq.
unfold tm6;unfold tm7.
apply e3.
Qed.


Lemma tm5_eq : tm5  = deltaHl0 /(qieta * qieta) .
apply eq0_eq.
rewrite tm5_eq_tm6.
rewrite tm6_eq_tm7.
apply e1.
Qed.

Lemma two_eq_two : INR 2 = 2.
auto.
Qed.

Lemma zero_less_than_inr_two : (0 < INR 2).
apply lt_0_INR.
auto.
Qed.

(* real number 2 is not equal to real number 0. *)
Lemma zero_less_than_two : 0<2.
rewrite <- two_eq_two.
apply zero_less_than_inr_two.
Qed.

Lemma l1 : sqrt (K * K) / sqrt 2 = sqrt(K*K / 2).
apply sym_eq.
apply sqrt_div.
apply e5.
apply zero_less_than_two.
Qed.

Lemma l2 : sqrt(deltaHl0) / sqrt(qieta * qieta) = sqrt( deltaHl0 / (qieta * qieta)).
apply sym_eq.
apply sqrt_div_alt.
apply e6.
Qed.

Lemma l3 : K * K / 2 = tm5.
unfold tm5.
ring.
Qed.

Lemma l4 : K * K / 2 = deltaHl0 / (qieta * qieta).
rewrite l3.
rewrite tm5_eq.
ring.
Qed.

(*
Lemma l5 : forall K, 0 <= K -> 0 <= K * K / 2.
intros.
*)

Theorem final_result : 0 <= (deltaHl0) -> 0 <= K -> 0 <> qieta -> sqrt(K * K) / sqrt(2) = sqrt(deltaHl0) / sqrt(qieta * qieta).
intros.
rewrite l1.
rewrite l2.
apply sqrt_lem_1.
(*this step should from (0 <= K) reach (0 <= K * K / 2) *)
apply e7.
(*
this step should from (0 <> qieta) reach 
(0 <= sqrt (deltaHl0 / (qieta * qieta))) 
*)
apply e8.
rewrite l4.
apply sqrt_sqrt.
(*this step should from (0 <= K) reach (0 <= K * K / 2) *)
apply e9.
Qed.
