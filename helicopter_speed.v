Require Import Reals.
Require Import Nsatz.

Open Scope R_scope.

Definition Real := R.

(* declare variables in speed auto-transition rule. *)
(* 
   u0 is the speed at the start of auto-transition.
   ud1 is the minus-acceleration that we expected.
   u is the initial speed.
   tf is the time that speed decreases to zero.
   ts is the time that the height of helicopter drop to the hanging height.
   H0 is the height at the start of dropping;
   Hxt is the height at the end of first stage in dropping;
   Hd2 is the accelerate speed during first stage dropping;
*)
Variables u0 ud1 tf : Real.

Variables ts H0 Hxt Hd2 : Real.

Definition u := u0 - ud1*tf.
Definition tm21 := Hxt - H0 + /2 * Hd2 * ts * ts.

(* assumptions of this deduction. *)
Axiom e02 : u = 0.
Axiom e03 : 0 <= / Hd2 * 2 * (H0 - Hxt).
Axiom e04 : 0 <= ts.
Axiom e21 : tm21 = 0.
Axiom e31 : tf = ts.


Lemma eq0_eq : forall y z, y-z = 0 -> y = z.
intros.
apply sym_eq.
apply Rminus_diag_uniq_sym.
assumption.
Qed.

Lemma result_1_f1 : tf * ud1 = u0 - u.
unfold u.
ring.
Qed.

Lemma mul_2_div : forall (r x y: R), r<>0 -> x * r = y -> x = y * / r.
intros.
rewrite <- H1.
rewrite Rinv_r_simpl_l.
auto.
assumption.
Qed.

Theorem result_1 : ud1 <> 0 -> u0 * /ud1 = tf.
intros.
apply sym_eq.
apply mul_2_div.
apply H.
rewrite result_1_f1.
rewrite e02.
ring.
Qed.

Lemma result_2_f1_f2 : H0 - Hxt = /2 * ts * ts * Hd2 - tm21.
unfold tm21.
ring.
Qed.


Lemma result_2_f1_f1 : / Hd2 * 2 * (H0 - Hxt) = (H0 - Hxt) * / Hd2 * 2.
ring.
Qed.

Lemma result_2_f1_f3 : (/ 2 * ts * ts * Hd2 - tm21) * / Hd2 * 2 = / 2 * ts * ts * Hd2 * / Hd2 * 2 - tm21 * / Hd2 * 2.
ring.
Qed.

Lemma result_2_f1_f4_f1 : / 2 * ts * ts * Hd2 * / Hd2 * 2 = (2 * / 2) * ts * ts * (Hd2 * / Hd2).
ring.
Qed.

Axiom e05 : Hd2 <> 0.

Lemma result_2_f1_f4_f2 : Hd2 * / Hd2 = 1.
apply Rinv_r.
apply e05.
Qed.

Lemma inr_two_not_zero : (INR 2 <> 0).
apply not_0_INR.
auto.
Qed.

Lemma two_eq_two : INR 2 = 2.
auto.
Qed.

(* real number 2 is not equal to real number 0. *)
Lemma two_not_zero : 2<>0.
rewrite <- two_eq_two.
apply inr_two_not_zero.
Qed.

Lemma result_2_f1_f4_f3 : 2 * / 2  = 1.
apply Rinv_r.
apply two_not_zero.
Qed.

Lemma result_2_f1_f4 : / 2 * ts * ts * Hd2 * / Hd2 * 2 = ts * ts.
rewrite result_2_f1_f4_f1.
rewrite result_2_f1_f4_f2.
rewrite result_2_f1_f4_f3.
ring.
Qed.

Lemma result_2_f1 : sqrt (/ Hd2 * 2 * (H0 - Hxt)) = ts.
apply sqrt_lem_1.
apply e03.
apply e04.
rewrite result_2_f1_f1.
rewrite result_2_f1_f2.
rewrite result_2_f1_f3.
rewrite result_2_f1_f4.
rewrite e21.
ring.
Qed.

Theorem result_2 : Hd2 <> 0 -> sqrt(/Hd2 * 2*(H0 - Hxt)) = ts.
apply Rmult_eq_reg_l.
rewrite result_2_f1.
ring.
Qed.

Theorem final_result : ud1 <> 0 -> Hd2 <> 0 -> u0 * /ud1  = sqrt(/Hd2 * 2*(H0 - Hxt)).
intros.
rewrite result_1.
rewrite result_2.
apply e31.
assumption.
assumption.
Qed.