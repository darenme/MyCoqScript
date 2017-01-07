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

Definition H t := H0 - /2 * Hd2 * t * t.

(* speed of helicopter during dropping. *)
Definition Hd1 t := Hd2 * t.

(* the height of drop at first stage. *)
Definition deltaH t := H0 - H t.

(* lemma for computing deltaH. *)
Lemma drop_height : Hd2 > 0 -> H0 - H t = Hd1 t * Hd1 t / (2 * Hd2).
intro.
unfold H.
unfold Hd1.
field.
apply Rgt_not_eq.
assumption.
Qed.

(* the time requied for reaching the height Hxt. *)
Variable ts : R.
Definition Hxt := H ts.

Lemma Hxt_ts : Hxt = H0 - /2 * Hd2 * ts * ts.
unfold Hxt.
trivial.
Qed.

Lemma ts_sqr : Hd2 <> 0 -> /Hd2 * 2*(H0 - Hxt) = ts * ts.
intro; unfold Hxt; unfold H.
field.
assumption.
Qed.

