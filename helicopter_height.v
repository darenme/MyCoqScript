Require Import Reals.

Open Scope R_scope.

Definition Real := R.

(* function parameter *)
Variable s : Real.

(* constant *)
Parameter H H0 Hd1 Hd2 : Real.

(* variables *)
Parameter t deltaH K : Real.

(* functions from s to real. *)
Variables Um Im Om Tm : Real -> Real.

Definition tm1 := H0 - H - /2 * Hd2 * t * t.
Definition tm2 := Hd1 - Hd2 * t.
(* 
Definition tm3 := (Tm s) * (Lm *s + Rm).
Definition tm4 := (Um s) * Kt - Kt * Ke * (Om s) - (Lm * s + Rm) * (Jm * s + Bm) * (Om s).
*)
(* assumptions of this deduction. *)
Axiom e1 : tm1 = 0.
Axiom e2 : tm2 = 0.
Axiom e3 : 2 * Hd2 <> 0.
Axiom e4 : 2 <> 0.

Definition tm5 := H0 - H.

Lemma eq0_eq : forall y z, y-z = 0 -> y = z.
intros.
apply sym_eq.
apply Rminus_diag_uniq_sym.
assumption.
Qed.

(* move Ke * (Om s) in tm1 to the  right of  = *)
Lemma tm5_eq : tm5  = /2 * Hd2 * t * t.
apply eq0_eq.
apply e1.
Qed.

Definition tm7 :=  Hd2 * t * t.

Lemma tm5_puls_tm7 : tm5 = /2 * tm7.
unfold tm7.
rewrite tm5_eq.
ring.
Qed.

Definition tm6 :=  Hd1.

Lemma tm6_eq : tm6  = Hd2 * t.
apply eq0_eq.
apply e2.
Qed.

Lemma l1 : 2 * Hd2 * (/ (2 * Hd2) * (tm6 * tm6)) = (2 * Hd2) * / (2 * Hd2) * (tm6 * tm6).
apply sym_eq.
apply Rmult_assoc.
Qed.


Lemma l2 : 2 * Hd2 * / (2 * Hd2) = 1.
apply Rinv_r.
apply e3.
Qed.


Lemma l3 : 2 * Hd2 * tm5 =  2 * tm5 * Hd2.
ring.
Qed.

Lemma l3_1 : 2 * (/ 2 * tm7) = 2 * /2 * tm7.
apply sym_eq.
apply Rmult_assoc.
Qed.

Lemma l3_2 : 2 * / 2 = 1.
apply Rinv_r.
apply e4.
Qed.



Theorem final_result : (2 * Hd2) <> 0 -> tm5 =  / (2 * Hd2) * (tm6 * tm6).
apply Rmult_eq_reg_l.
rewrite l1.
rewrite l2.
rewrite l3.
rewrite tm5_puls_tm7.
rewrite l3_1.
rewrite l3_2.
unfold tm7.
rewrite tm6_eq.
ring.
Qed.