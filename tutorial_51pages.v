(*************************

(* 第一章 *)

(* 1.1 *)
Section Declaration.
  Variable n : nat.
  Hypothesis Pos_n : (gt n 0).
  Check gt.
  Check gt n.
  Check gt n 1.
End Declaration.

Definition one := (S O).
Definition two := S (S O).
Definition three := S (S (S O)).
Definition double (m:nat) := plus m m.
Parameter n : nat.
Definition add_n (m:nat) := plus m n.

Check (forall m:nat, gt m 0).

Reset Initial.


(* 1.2 *)
Section Minimal_Logic.
Variable A B C : Prop.
Check (A->B).

(* 第一种证明法 *)
Goal (A->B->C)->(A->B)->A->C.
intros H.
intros H' HA.
apply H.
exact HA.
apply H'.
assumption.
Save trivial_lemma.

(* 第二种证明法 *)
Lemma distr_impl : (A->B->C)->(A->B)->A->C.
intros.
apply H; [assumption | apply H0; assumption].
Save.

(* 第三种证明法 *)
Lemma distr_impl_auto : (A->B->C)->(A->B)->A->C.
auto.
Abort.

Inspect 3.


(* 1.3 *)
Variable A B C : Prop.
Lemma and_commutative : A/\B -> B/\A.
intros.
(* break H into its components *)
elim H.
(* tactic split is just an abbreviation for apply conj *)
split.
apply H1.
apply H0.
Restart.
(* auto succeeded here because it knows as a hint the 
conjunction introduction operator conj *)
intro H; elim H; auto.
Qed.

(* conjunction introduction operator conj *)
Check conj.

Lemma or_commutative : A\/B -> B\/A.
intro H; elim H.
intro HA.
clear H.
right.
trivial.
intro HB.
clear H.
left.
trivial.
Qed.

(* tauto能直接证明 *)
Lemma or_commutative_tauto : A\/B -> B\/A.
tauto.
Qed.

Print or_commutative_tauto.

(* a more complex example for tauto *)
Lemma distr_and : A -> B /\ C -> (A -> B) /\ (A -> C).
tauto.
Qed.

(* Peirce's lemma will failed in coq's logic *)
Lemma Peirce : ((A -> B) -> A) -> A.
try tauto.
Abort.


(* double negation Peirce's lemma the double negation 
 * of a proposition is equivalent to this proposition
 * in coq
 *)
Lemma NNPeirce : ~ ~ (((A -> B) -> A) -> A).
tauto.
Qed.

Require Import Classical.

(* now can prove a classical low *)
Check NNPP.
Lemma Peirce : ((A -> B) -> A) -> A.
apply NNPP; tauto.
Qed.

(* 
  1. Every non-scottish member wears red socks
  2. Every member wears a kilt(短裙) or doesn’t wear red socks
  3. The married members don’t go out on Sunday
  4. A member goes out on Sunday if and only if he is Scottish
  5. Every member who wears a kilt is Scottish and married
  6. Every scottish member wears a kilt 
*)
Section club.
  Variables Scottish RedSocks WearKilt Married GoOutSunday : Prop.
  Hypothesis rule1 : ~ Scottish -> RedSocks.
  Hypothesis rule2 : WearKilt /\ ~ RedSocks.
  Hypothesis rule3 : Married -> ~ GoOutSunday.
  Hypothesis rule4 : GoOutSunday <-> Scottish.
  Hypothesis rule5 : WearKilt -> Scottish /\ Married.
  Hypothesis rule6 : Scottish -> WearKilt.
  (* Lemma写在这儿,执行到这儿的时候为什么就能成为一个
   * 以上面的定义为条件的待证目标?
   *)
  Lemma NoMember : False.
  tauto.
  Qed.
End club.

Check NoMember.
*************************)

(* 1.4 *)
Reset Initial.

Section Predicate_claculus.
  Variable D : Set.
  Variable R : D -> D -> Prop.
  Section R_sym_trans.
    (* 假设自反和传递性 *)
    Hypothesis R_symmetric : forall x y:D, R x y -> R y x.
    Hypothesis R_transitive : forall x y z:D, R x y -> R y z -> R x z.
    Lemma refl_if : forall x:D, (exists y, R x y) -> R x x.
    intros x x_Rlinked.
    (* elim在这里的用法? *)
    elim x_Rlinked.
    intros y Rxy.
    apply R_transitive with y.
    (* 用下面注释中的4步也能证明
    apply Rxy.
    apply R_symmetric.
    apply Rxy.
    Qed
    *)
    assumption.
    apply R_symmetric; assumption.
    Qed.
  End R_sym_trans.
  Variable P : D -> Prop.
  Variable d : D.
  Lemma weird : (forall x:D, P x) -> exists a, P a.
  intro UnivP.
  exists d; trivial.
  Qed.







