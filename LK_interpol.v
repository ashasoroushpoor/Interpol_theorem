Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import Finset.
Require Import Formula.
Import List.ListNotations.

Coercion bool_to_Prop (b : bool) : Prop := b = true.


Fixpoint In_prop (x : atom)(P : prop)  : bool :=
    match P with
    | Var a => a =? x
    | Bot => false
    | Top => false
    | Disj p1 p2 => (In_prop x p1) || (In_prop x p2)
    | Conj p1 p2 => (In_prop x p1) || (In_prop x p2)
    | LDiv p1 p2 => (In_prop x p1) || (In_prop x p2)
    end.
Fixpoint In_list_prop (x : atom)(l : list prop) : bool :=
    match l with
    | nil => false
    | p :: l' => (In_prop x p) || (In_list_prop x l')
    end.
(* Lemma list_dest_app: forall {X : Type}(l : list X),
l = nil \/ (exists (x: X) (l' : list X), l = l' ++ [x]).
Admitted. *)
Search (_ ∩ _).
Theorem LK_Interpol: forall n (G1 G2 D1 D2 : list prop),
G1 ++ G2 ⇒ D1 ++ D2 >< n -> 
(exists (c : prop) m1 m2, G1 ⇒ c :: D1 >< m1 /\ c :: G2 ⇒ D2 >< m2
(* /\ lil (atom_lista c) (list_intersect (atom_list(G1 ++ G2)) (atom_list(D1 ++ D2)))). *)
(* /\ (forall (x : atom), (In_prop x c) -> ((In_list_prop x (G1 ++ G2) /\ In_list_prop x (D1 ++ D2))))). *)
/\ (atoms_of c) ⊆ ( (atoms_of_list (G1 ++ G2)) ∩ (atoms_of_list (D1 ++ D2)))).

 induction n; intros G1 G2 D1 D2 H; inversion H.
    - admit.
    (* destruct G1, G2, D1, D2.
        + discriminate.
        + discriminate.
        + discriminate.
        + discriminate.
        + discriminate.
        + inversion H0. inversion H1.
        exists (p ∨ ¬ p), 5, 1. repeat split.
            * apply (LKrC [] [] (p ∨ ¬ p) 4).
            apply (LKr1O [] [p ∨ ¬ p] p (¬ p) 3).
            apply (LKrE [] [] [] (p ∨ ¬ p) (p) 2).
            simpl.
            apply (LKr2O [] [p] p (¬ p) 1).
            apply (LKrN [] [p] (p) 0).
            apply (LKA p ).
            * rewrite <- H3. rewrite <- H5. 
            apply (LKlW [p] [p] (p ∨ ¬ p) 0).
            apply (LKA p).
            * rewrite <- H3.
            unfold In_prop in H2. simpl in H2.
            rewrite Bool.orb_false_r in H2.
            rewrite Bool.orb_diag in H2.
            simpl.
            rewrite Bool.orb_false_r.
            apply H2.
            * rewrite <- H3.
            unfold In_prop in H2. simpl in H2.
            rewrite Bool.orb_false_r in H2.
            rewrite Bool.orb_diag in H2.
            simpl.
            rewrite Bool.orb_false_r.
            apply H2.
        + inversion H0. inversion H1. rewrite app_nil_r in H6.
        exists (¬ p), 1, 1. repeat split.
            * rewrite <- H5. rewrite <- H6. simpl. 
            apply (LKrN [] [p] p 0).
            apply (LKA p).
            * rewrite <- H3.
            apply (LKlN [p] [] p 0).
            apply (LKA p).
            * simpl.
            rewrite Bool.orb_false_r.
            rewrite <- H3.
            unfold In_prop in H2. simpl in H2. rewrite Bool.orb_false_r in H2.
            apply H2.
            * simpl.
            rewrite Bool.orb_false_r.
            rewrite <- H3.
            unfold In_prop in H2. simpl in H2. rewrite Bool.orb_false_r in H2.
            apply H2.
        + inversion H1. destruct D1.
            * inversion H4.
            * inversion H4.
        + discriminate.
        + inversion H0. inversion H1. rewrite app_nil_r in H4.
        exists p, 0, 0. repeat split.
            * rewrite <- H3. rewrite <- H4. apply (LKA p).
            * rewrite <- H5. apply (LKA p).
            * rewrite <- H3.
            simpl.
            rewrite Bool.orb_false_r.
            apply H2.
            * rewrite <- H3.
            simpl.
            rewrite Bool.orb_false_r.
            apply H2.
        + inversion H0. inversion H1. rewrite app_nil_r in H4. rewrite app_nil_r in H6.
        exists (p ∧ ¬ p), 1, 5. repeat split.
            * rewrite <- H5. rewrite <- H3. rewrite <- H4. rewrite <- H6.
            apply (LKrW [p] [p] (p ∧ ¬ p) 0).
            apply (LKA p).
            * apply (LKlC [] [] (p ∧ ¬ p) 4).
            apply (LKl1A [p ∧ ¬ p] [] p (¬ p) 3).
            apply (LKlE [] [] [] (p ∧ ¬ p) (p) 2). simpl.
            apply (LKl2A [p] [] p (¬ p) 1).
            apply (LKlN [p] [] (p) 0).
            apply (LKA p).
            * rewrite <- H3.
            unfold In_prop in H2. simpl in H2.
                rewrite Bool.orb_false_r in H2.
                rewrite Bool.orb_diag in H2.
                simpl.
                rewrite Bool.orb_false_r.
                apply H2.
            * rewrite <- H3.
            unfold In_prop in H2. simpl in H2.
                rewrite Bool.orb_false_r in H2.
                rewrite Bool.orb_diag in H2.
                simpl.
                rewrite Bool.orb_false_r.
                apply H2.
        + inversion H1. destruct D1.
            *inversion H4.
            * inversion H4.
        + inversion H0. destruct G1.
            * inversion H4.
            * inversion H4.
        + inversion H0. destruct G1.
            * inversion H4.
            * inversion H4.
        + inversion H0. destruct G1.
            * inversion H4.
            * inversion H4.
        + inversion H0. destruct G1.
            * inversion H4.
            * inversion H4. *)
    - admit.
    (* destruct D1, D2; simpl in *; try discriminate; try inversion H1; subst; simpl in *. 
        + 
        rewrite <- app_nil_l in H3.
        specialize (IHn G1 G2 [] (D2) H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1, (S m2). repeat split.
            * apply IH1.
            * apply (LKrW (c :: G2) D2 p m2). apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. apply H0.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. rewrite app_nil_l in H2.
            rewrite H2. rewrite Bool.orb_true_r. reflexivity.
        + 
        specialize (IHn G1 G2 D1 [] H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (S (S m1)), m2. repeat split.
            * apply (LKrE G1 [] D1 p c (S m1)). simpl.
            apply (LKrW G1 (c :: D1) p m1).
            apply IH1.
            * apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. apply H0.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0.
            rewrite H2. rewrite Bool.orb_true_r. reflexivity.
        +
        specialize (IHn G1 G2 D1 (p0 :: D2) H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (S (S m1)), m2. repeat split.
            * apply (LKrE G1 [] D1 p c (S m1)). simpl.
            apply (LKrW G1 (c :: D1) p m1).
            apply IH1.
            * apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. apply H0.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0.
            rewrite H2. rewrite Bool.orb_true_r. reflexivity. *)
    - admit.
    (* destruct G1, G2; simpl in *; try discriminate; try inversion H1; subst; simpl in *. 
        +
        (* rewrite <- app_nil_l in H3. *)
        specialize (IHn [] G2 D1 (D2) H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1, (S(S m2)). repeat split.
            * apply IH1.
            * apply (LKlE [] G2 D2 p c (S m2)). simpl.
            apply (LKlW (c :: G2) D2 p m2).
            apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. 
            simpl in H0. rewrite H0. rewrite Bool.orb_true_r. reflexivity.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0.
            apply H3.
        + 
        specialize (IHn G1 [] D1 (D2) H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (S m1), m2. repeat split.
            * apply (LKlW G1 (c :: D1) p m1).
            apply IH1.
            * apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. 
            rewrite H0. rewrite Bool.orb_true_r. reflexivity.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0.
            apply H3.
        +
        specialize (IHn G1 (p0 :: G2) D1 D2 H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (S m1), m2. repeat split.
            * apply (LKlW G1 (c :: D1) p m1).
            apply IH1.
            * apply IH2.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0. 
            rewrite H0. rewrite Bool.orb_true_r. reflexivity.
            * specialize (IH3 x) as H'. apply H' in H0. destruct H0.
            apply H3. *)
    - admit.  
     (* specialize (IHn G1 G2 D (a :: b :: D') H3) as H'.
    destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    destruct D2 as [ | a' D2']; try destruct D2'; simpl in *; try discriminate.
        + apply (app_inv_head ) in H1. inversion H1.
        + inversion H1.
    specialize (IHn G1 G2 D1 D2 H2) as H'.
    simpl in H1. inversion H1. rewrite  H6 in H3.
        specialize (IHn G1 G2 D1 D2 H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (S (S m1)) , (S m2). repeat split.
            * apply (LKrE G1 [] D1 p c (S m1)).
             apply (LKrW G1 (c :: D1) p m1).
             apply IH1.
             * apply (LKrW (c :: G2) D1 p).
             apply IH2.
             * specialize (IH3 x) as H'. apply H' in H4. destruct H4. apply H4.
             * specialize (IH3 x) as H'. apply H' in H4. destruct H4. simpl in H5.
             unfold In_list_prop. rewrite H7. rewrite Bool.orb_true_r. reflexivity. *)
    - admit.
    -admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - subst. destruct D1, D2; inversion H2; subst.
        + specialize (IHn1 G1 G2 [] (a :: D2) H4) as H6. destruct H6 as [c0 [m1 [m2 [H6 [H6' H7]]]]].
        specialize  (IHn2 G1 G2 [] (b :: D2) H5) as H8. destruct H8 as [c1 [m1' [m2' [H8 [H8' H9]]]]].
        exists (c0 ∧ c1), ( m1 ≍ m1'), ( (☉ m2) ≍ (☉ m2')). repeat split.
            * constructor 8. apply H6. apply H8.
            * constructor 8.
                ** constructor 9. apply H6'.
                ** constructor 10. apply H8'.
            * simpl. simpl in H9. simpl in H7.
            apply (incl_union_inter_add).
                ** apply H7.
                ** apply H9.
        + simpl in *. 
        specialize (IHn1 G1 G2 (a :: D1) [] H4) as H6. destruct H6 as [c0 [m1 [m2 [H6 [H6' H7]]]]].
        specialize  (IHn2 G1 G2 (b :: D1) [] H5) as H8. destruct H8 as [c1 [m1' [m2' [H8 [H8' H9]]]]].
        exists (c0 ∨ c1), 
        (☉ ((☉ ☉ m1) ≍ (☉ ☉ m1'))),
        (m2 ≍ m2'). repeat split.
            * apply (LKrE G1 [] D1 (a ∧ b) (c0 ∨ c1) ((☉ ☉ m1) ≍ (☉ ☉ m1'))).
            simpl. constructor 8.
                ** apply (LKrE G1 [] D1 (c0 ∨ c1) (a) (☉ m1)).
                simpl. constructor 11. apply H6.
                ** apply (LKrE G1 [] D1 (c0 ∨ c1) (b) (☉ m1')).
                simpl. constructor 12. apply H8.
            * constructor 13.
                ** apply H6'.
                ** apply H8'.
            * simpl. simpl in H9. simpl in H7.
            apply (incl_union_inter_add).
                ** apply H7.
                ** apply H9.
        + simpl in *. 
        specialize (IHn1 G1 G2 (a :: D1) (p0 :: D2 ) H4) as H6. destruct H6 as [c0 [m1 [m2 [H6 [H6' H7]]]]].
        specialize  (IHn2 G1 G2 (b :: D1) (p0 :: D2 ) H5) as H8. destruct H8 as [c1 [m1' [m2' [H8 [H8' H9]]]]].
        exists (c0 ∨ c1), 
        (☉ ((☉ ☉ m1) ≍ (☉ ☉ m1'))),
        (m2 ≍ m2'). repeat split.
            * apply (LKrE G1 [] D1 (a ∧ b) (c0 ∨ c1) ((☉ ☉ m1) ≍ (☉ ☉ m1'))).
            simpl. constructor 8.
                ** apply (LKrE G1 [] D1 (c0 ∨ c1) (a) (☉ m1)).
                simpl. constructor 11. apply H6.
                ** apply (LKrE G1 [] D1 (c0 ∨ c1) (b) (☉ m1')).
                simpl. constructor 12. apply H8.
            * constructor 13.
                ** apply H6'.
                ** apply H8'.
            * simpl. simpl in H9. simpl in H7.
            apply (incl_union_inter_add).
                ** apply H7.
                ** apply H9.
    -

Admitted.