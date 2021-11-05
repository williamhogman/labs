From mathcomp
     Require Import ssreflect.


Inductive True : Prop := I : True.

Theorem trueistrue: True. Proof. exact: I. Qed.

Theorem imp_trans: forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> A B C.
  move=> H1 H2.
  move=> a.
  apply: H2.
  apply: H1.
  exact: a.
Qed.

Theorem all_imp_dist A (P Q: A -> Prop):
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z.
  move=> H1 H2 Hq.
  apply H1.
  apply H2.
Qed.


Module Connectives.
  Variables P Q R: Prop.
  Goal P -> R -> P /\ R.
  Proof. move=> p r. apply: conj=>//. Qed.

  Goal P /\ Q -> Q.
    case.
    done.
  Qed.

  Locate "_ \/ _".
  Print or.

  Goal Q -> P \/ Q \/ R.
    move => q.
      by right; left.
  Qed.

  Goal P \/ Q -> Q \/ P.
    case=>x.
      by right.
        by left.
  Qed.

  Locate "~ _".

  Print not.

  Theorem contraP: (P -> Q) -> (~Q -> ~P).
    move=> H Hq.
    move /H.
    move /Hq.
    done.
  Qed.

Theorem ex_imp_ex A (S T: A -> Prop):
  (exists a: A, S a) -> (forall x: A, S x -> T x) -> exists b: A, T b.
Proof.
  case=> a Hs Hst.
  exists a.
  apply: Hst.
  trivial.
Qed.


  
