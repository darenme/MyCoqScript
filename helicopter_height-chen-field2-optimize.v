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

(* 这里只定义了变量Hd2,Hd1可以通过关键字Definition由Hd2得到 *)
Variables H0 Hd2 t : R.

(* 这里直接说H是个函数,自变量是t,这样也行吗? *)
Definition H t := H0 - /2 * Hd2 * t * t.

(* speed of helicopter during dropping. *)
Definition Hd1 t := Hd2 * t.

(* the height of drop at first stage. *)
(* H是一个函数,自变量是t? *)
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

(* 这里是说Hxt的值是一个函数吗??这步是关键 *)
Definition Hxt := H ts.

Lemma Hxt_ts : Hxt = H0 - /2 * Hd2 * ts * ts.
unfold Hxt.
(* 这个命令是什么?怎么这么强? *)
trivial.
Qed.

Lemma ts_sqr : Hd2 <> 0 -> /Hd2 * 2*(H0 - Hxt) = ts * ts.
intro.
unfold Hxt.
unfold H.
(* field和trivial的区别是什么? *)
field.
assumption.
Qed.

