Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Import List.ListNotations.

Theorem LK_Interpol: forall (G1 G2 D1 D2 : list prop),
G1 ++ G2 ⇒ D1 ++ D2 -> (exists (c : prop), G1 ⇒ D1 ++ c /\ G2 ++ c ⇒ D1).
intros. induction H.
- admit.
- destruct IHLK as [c [H' H'']]. 
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK1 as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK1 as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
- destruct IHLK1 as [c [H' H'']].
    exists c. split.
    + apply H'.
    + apply H''.
Admitted.