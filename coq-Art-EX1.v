(* 要导入Reals才能使用Z_scope *)
Require Import Reals.
Open Scope Z_scope.


(* 2.3.2 section和局部变量 *)
Section binomial_def.
 Variables a b : Z.
 Definition binomial z:Z := a*z + b.
 Print binomial.
 Section trinomial_def.
  Variable c:Z.
  Definition trinomial z:Z := (binomial z)*z +c.
  Print trinomial.
 End trinomial_def.
 Print trinomial.
End binomial_def.
Print binomial.
Print trinomial.
 
Definition p1 : Z->Z := binomial 5 (-3).
Definition p2 : Z->Z := trinomial 1 0 (-1).
Definition p3 := trinomial 1 (-2) 1.

(* 2.5.1 Set大类 *)
Check Z.
Check ((Z->Z)->nat->nat).
Check Set.
Check Type.
