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

Lemma tm3_eq_tm4 : tm3 = tm4.
apply nsatz.
