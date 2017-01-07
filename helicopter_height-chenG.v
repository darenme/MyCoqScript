Require Import Reals.
Require Import Nsatz.

Open Scope R_scope.

Definition Real := R.

(* declare variables in height drop rule. *)
(* 
   H0 is the height at the start of dropping;
   H is the height at the end of first stage in dropping;
   Hd1 is the speed during dropping of first stage;
   Hd2 is the accelerate speed during first stage dropping;
   t is the time in dropping.
*)
Variables H0 Hd2 t : R.

Definition H := H0 - /2 * Hd2 * t * t.

(* speed of helicopter during dropping. *)
Definition Hd1 := Hd2 * t.

(* the height of drop at first stage. *)
Definition deltaH := H0 - H.

(* INR 2 is the injection of the natural number 2 into R. *)

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

Lemma zero_less_than_inr_two : (0 < INR 2).
apply lt_0_INR.
auto.
Qed.

(* real number 2 is not equal to real number 0. *)
Lemma zero_less_than_two : 0<2.
rewrite <- two_eq_two.
apply zero_less_than_inr_two.
Qed.

Lemma two_larger_than_zero : 2>0.
apply Rlt_gt.
apply zero_less_than_two.
Qed.

Lemma two_not_eq_zero : 2<>0.
apply Rgt_not_eq.
apply two_larger_than_zero.
Qed.

Lemma two_times_r : forall r, r>0 -> 2*r > 0.
intros.
apply Rmult_gt_0_compat.
apply two_larger_than_zero.
assumption.
Qed.

Lemma drop_height_aux :  (H0 - H) * (2 * Hd2) = Hd1 * Hd1 .
unfold H.
unfold Hd1.
ring_simplify. (* simplify expressions on a ring *)
rewrite Rinv_r.
ring.
apply two_not_zero.
Qed.

Lemma mul_2_div : forall (r x y: R), r<>0 -> x * r = y -> x = y * / r.
intros.
rewrite <- H2.
rewrite Rinv_r_simpl_l.
auto.
assumption.
Qed.

Lemma div_div : forall x y, x / y = x * /y.
auto.
Qed.

Lemma mul_2_div1 : forall (r x y: R), r<>0 -> x * r = y -> x = y / r.
intros.
rewrite div_div.
apply mul_2_div.
auto.
assumption.
Qed.

(* lemma for computing deltaH. *)
Lemma drop_height : Hd2 > 0 -> H0 - H = Hd1 * Hd1 / (2 * Hd2).
intro.
apply mul_2_div.
apply Rgt_not_eq.
apply two_times_r.
assumption.
apply drop_height_aux.
Qed.
