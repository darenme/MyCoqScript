Require Import Reals.

Open Scope R_scope.

Definition Real := R.

(* function parameter *)
Variable s : Real.

(* constant *)
Parameter Kt Bm Ke : Real.

(* variables *)
Parameter Rm Lm Jm : Real.

(* functions from s to real. *)
Variables Um Im Om Tm : Real -> Real.

Definition tm1 := (Um s) - Rm * (Im s) - Lm * s * (Im s) - Ke * (Om s).
Definition tm2 := Kt * (Im s) - Jm * s * (Om s) - Bm * (Om s) - (Tm s).
Definition tm3 := (Tm s) * (Lm *s + Rm).
Definition tm4 := (Um s) * Kt - Kt * Ke * (Om s) - (Lm * s + Rm) * (Jm * s + Bm) * (Om s).

(* assumptions of this deduction. *)
Axiom e1 : tm1 = 0.
Axiom e2 : tm2 = 0.
Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Axiom e3 : (Lm *s + Rm) <> 0.

Definition tm5 :=  ((Um s) - Rm * (Im s) - (Lm * s) * (Im s)).

Lemma eq0_eq : forall y z, y-z = 0 -> y = z.
intros.
apply sym_eq.
apply Rminus_diag_uniq_sym.
assumption.
Qed.

(* move Ke * (Om s) in tm1 to the  right of  = *)
Lemma tm5_eq : tm5  = Ke * (Om s).
apply eq0_eq.
apply e1.
Qed.


Definition tm6 :=  ((Um s) - (Rm + Lm * s) * (Im s)).

Lemma  tm6_eq_tm5 : tm6 = tm5.
unfold tm5; unfold tm6.
ring.
Qed.

Lemma tm6_eq : tm6 = Ke * (Om s).
rewrite tm6_eq_tm5.
apply tm5_eq.
Qed.


Lemma tm5_eq0 : tm5 - Ke * (Om s) = 0.
apply e1.
Qed.

Definition tm7:= (Rm + Lm * s) * (Im s).

Definition tm8:= (Um s)-Ke * (Om s).

Lemma  tm8_tm7_eq : tm8 - tm7 = tm5 - Ke * (Om s).
unfold tm7; unfold tm8; unfold tm5.
ring.
Qed.

Lemma tm8_eq_tm7 : tm8 = tm7.
apply eq0_eq.
rewrite tm8_tm7_eq.
apply tm5_eq0.
Qed.

Definition tm9 := tm7 * Kt.
Definition tm10 := tm8 * Kt.

Lemma tm9_eq_tm10 : tm10 = tm9.
unfold tm9; unfold tm10.
rewrite tm8_eq_tm7.
ring.
Qed.

Definition tm11:= (Jm * s + Bm) * (Om s) + (Tm s).

Definition tm12:= Kt * (Im s).

Lemma tm11_tm12_eq : tm12 - tm11 = tm2.
unfold tm11; unfold tm12; unfold tm2.
ring.
Qed.

Lemma tm11_eq_tm12 : tm12 = tm11.
apply eq0_eq.
rewrite tm11_tm12_eq.
apply e2.
Qed.


Definition tm13:= tm11*(Rm + Lm * s).

Definition tm14:= tm12*(Rm + Lm * s).

Lemma tm13_eq_tm14 : tm13 = tm14.
unfold tm13; unfold tm14.
rewrite tm11_eq_tm12.
ring.
Qed.

Lemma tm13_eq_tm9 : tm13 = tm9.
rewrite tm13_eq_tm14.
unfold tm14; unfold tm9.
unfold tm12; unfold tm7.
ring.
Qed.

Lemma tm13_eq_tm10 : tm13 = tm10.
rewrite tm13_eq_tm9.
apply sym_eq.
apply tm9_eq_tm10.
Qed.

Lemma tm3_tm13_eq0 : tm3 = tm13 - (Jm * s + Bm) * (Om s) * (Rm + Lm * s).
unfold tm3; unfold tm13.
unfold tm11.
ring.
Qed.

Lemma tm4_tm10_eq0 : tm4 = tm10 - (Jm * s + Bm) * (Om s) * (Rm + Lm * s).
unfold tm4; unfold tm10.
unfold tm8.
ring.
Qed.

Lemma tm3_eq_tm4 : tm3 = tm4.
rewrite tm3_tm13_eq0.
rewrite tm4_tm10_eq0.
rewrite tm13_eq_tm10.
ring.
Qed.

Lemma tm4_eq_tm3 : tm4 = tm3.
apply sym_eq.
apply tm3_eq_tm4.
Qed.

Lemma l2 : (Lm *s + Rm) * / (Lm * s + Rm)  = 1.
apply Rinv_r.
apply e3.
Qed.

Lemma l3 : (Lm * s + Rm) * (/ (Lm * s + Rm) * tm4) = (Lm * s + Rm) * / (Lm * s + Rm) * tm4.
apply sym_eq.
apply Rmult_assoc.
Qed.

Theorem final_result : (Lm *s + Rm) <> 0 -> Tm s = / (Lm *s + Rm) * tm4.
apply Rmult_eq_reg_l.
rewrite l3.
rewrite l2.
rewrite tm4_eq_tm3.
unfold tm3.
ring.
Qed.
