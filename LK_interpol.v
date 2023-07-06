Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Import List.ListNotations.

Theorem LK_Interpol: forall (G1 G2 D1 D2 : list prop),
G1 ++ G2 ⇒ D1 ++ D2 -> (exists (c : prop), G1 ⇒ D1 ++ c /\ G2 ++ c ⇒ D1).
intros. induction H.
- admit.
- exists a. split.
    +