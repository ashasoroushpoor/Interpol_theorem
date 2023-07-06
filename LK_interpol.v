Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Import List.ListNotations.

Theorem LK_Interpol: forall (G1 G2 D1 D2 : list prop) n,
G1 ++ G2 ⇒ D1 ++ D2 >< n -> (exists (c : prop) m1 m2, G1 ⇒ c :: D1 >< m1 /\ c :: G2 ⇒ D1 >< m2).
intros G1 G2 D1 D2. induction n; intros H; inversion H.
- destruct G1, G2, D1, D2;
    simpl in *;
    try discriminate;
    inversion H0;
    inversion H1;
    subst.
Admitted.