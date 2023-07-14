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

Lemma exchg_partition: forall {X : Type} (D D' D1 D2 : list X) (a b : X),
D ++ a :: b :: D' = D1 ++ D2 ->
(
    ( D2 = D ++ a :: b :: D' /\ D1 = [])
    \/ (exists D3, D2 = D3 ++ a :: b :: D' /\ D = D1 ++ D3)
    \/ (D1 = D /\ D2 = a :: b :: D')
    \/ (D1 = D ++ [a]) /\ D2 = b :: D'
    \/ (D1 = D ++ [a; b] /\ D2 = D')
    \/ (exists D3, D1 = D ++ a :: b :: D3 /\ D' = D3 ++ D2)
    \/ (D1 = D ++ a :: b :: D' /\ D2 = [])
).
Proof.
    (* intros. 
    generalize dependent D2.
    induction D1.
    - intros. left. split.
        + symmetry. simpl in H. apply H.
        + reflexivity.
    - destruct IHD1 as [[H1 H1'] | [[D3 [H1 H1']] | [[H1 H1'] | [[H1 H1']| [[H1 H1'] | [[D3 [H1 H1']] | [H1 H1'] ]]]]]].
        + simpl in H. *)
    Admitted.

Lemma app_cons_2: forall {X: Type} (l : list X) (a : X),
[a] ++ l = a :: l.
Proof.
    intros. simpl. reflexivity.
Qed.

(* Theorem x: forall (X Y Z : Prop), X \/ (Y \/ Z) -> (X \/ Y) \/ Z
.
Proof.
    intros. destruct H as [x | [y | z]].
    -
Qed. *)
Lemma intersection_mem_double: forall n s1 s2, 
n ∈ (s1 ∩ s2) -> n ∈ s2 /\ n ∈ s1.
Proof.
    intros. split.
        - apply intersection_mem in H. auto.
        - rewrite intersection_comm in H. apply intersection_mem in H.
        auto.
Qed.
Lemma mem_union_double:forall n s1 s2, 
n ∈ s1 \/ n ∈ s2-> n ∈ (s1 ∪ s2).
Proof. intros. destruct H.
    - apply mem_union. apply H.
    - rewrite union_comm. apply mem_union. apply H.
Qed.
Lemma incl_intersect_app_union: forall a b c d,
a ⊆ b ∩ (d) -> a ⊆ b ∩ (c ∪ d).
Proof. 
    intros. apply mem_incl. intros. rewrite mem_incl in H.
    pose proof (H n H0). apply intersection_mem_double in H1. destruct H1.
    apply mem_intersection. split.
        - auto.
        - rewrite union_comm. apply mem_union. auto.
Qed.
    
Theorem LK_Interpol_strong: forall n (G1 G2 D1 D2 : list prop),
G1 ++ G2 ⇒ D1 ++ D2 >< n -> 
(exists (c : prop) m1 m2, G1 ⇒ c :: D1 >< m1 /\ c :: G2 ⇒ D2 >< m2
(* /\ lil (atom_lista c) (list_intersect (atom_list(G1 ++ G2)) (atom_list(D1 ++ D2)))). *)
(* /\ (forall (x : atom), (In_prop x c) -> ((In_list_prop x (G1 ++ G2) /\ In_list_prop x (D1 ++ D2))))). *)
/\ (atoms_of c) ⊆ ( (atoms_of_list (G1 ++ G2)) ∩ (atoms_of_list (D1 ++ D2)))).

 induction n; intros G1 G2 D1 D2 H; inversion H.
    -  destruct G1, G2, D1, D2; try discriminate; simpl in *; inversion H0; inversion H1; subst; try (rewrite app_nil_r in *).
        + exists (p1 ∨ ¬ p1), (☉ (☉ (☉ (☉ (☉ leaf))))), (☉ leaf). repeat split.
            * constructor 6. constructor 11. 
            apply (LKrE [] [] [] (p1 ∨ ¬ p1) (p1) (☉ (☉ leaf))). simpl.
            constructor 12. constructor 14. constructor 1.
            * constructor 3. constructor 1.
            * simpl. rewrite union_idr. 
            rewrite union_refl. rewrite intersection_refl.
            apply incl_reflexive.
        + subst.
        exists (¬ p1), (☉ leaf), (☉ leaf). repeat split.
            * constructor 14. apply H.
            * constructor 15. apply H.
            * simpl. rewrite union_idr. rewrite intersection_refl.
            apply incl_reflexive.
        + destruct D1; inversion H6.
        + subst. exists p1, leaf, leaf. repeat split.
            * constructor 1.
            * constructor 1.
            * rewrite union_idr. rewrite intersection_refl.
            apply incl_reflexive.
        + subst; simpl in *.
        exists (p1 ∧ ¬ p1), (☉ leaf), (☉ (☉ (☉ (☉ (☉ leaf))))). repeat split.
            * constructor 2. constructor 1.
            * constructor 7. constructor 9.
            apply (LKlE [] [] [] (p1 ∧ ¬ p1) (p1) (☉ (☉ leaf))). simpl.
            constructor 10. constructor 15. constructor 1.
            * simpl. rewrite union_idr. 
            rewrite union_refl. rewrite intersection_refl.
            apply incl_reflexive.
        + destruct D1; inversion H6.
        + destruct G1; inversion H4.
        + destruct G1; inversion H4.
        + destruct G1; inversion H4.
    - destruct D1, D2; simpl in *; try discriminate; try inversion H1; subst; simpl in *.
        + rewrite <- app_nil_l in H3.
        specialize (IHn G1 G2 [] (D2) H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1, (☉ m2). repeat split.
            * apply IH1.
            * constructor 2. apply IH2.
            * apply incl_union_inter_absorb. simpl in IH3. auto.
        + specialize (IHn G1 G2 D1 [] H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ (☉ m1)), m2. repeat split.
            * apply (LKrE G1 [] D1 p c (☉ m1)). simpl.
            constructor 2. apply IH1.
            * apply IH2.
            * apply incl_union_inter_absorb. auto.
        + specialize (IHn G1 G2 D1 (p0 :: D2) H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ (☉ m1)), m2. repeat split.
            * apply (LKrE G1 [] D1 p c (☉ m1)).
            constructor 2. apply IH1.
            * apply IH2.
            * apply incl_union_inter_absorb. auto.
    - destruct G1, G2; simpl in *; try discriminate; try inversion H1; subst; simpl in *. 
        + specialize (IHn [] G2 D1 (D2) H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1, (☉ (☉ m2)). repeat split.
            * apply IH1.
            * apply (LKlE [] G2 D2 p c (☉ m2)). simpl.
            constructor 3. apply IH2.
            * apply incl_union_absorb_inter. auto.
        + specialize (IHn G1 [] D1 (D2) H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2. repeat split.
            * constructor 3. apply IH1.
            * apply IH2.
            * apply incl_union_absorb_inter. auto.
        + specialize (IHn G1 (p0 :: G2) D1 D2 H2) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2. repeat split.
            * constructor 3. apply IH1.
            * apply IH2.
            * apply incl_union_absorb_inter. auto.
    - apply exchg_partition in H1. 
    destruct H1 as [[H1 H1'] | [[D3 [H1 H1']] | [[H1 H1'] | [[H1 H1']| [[H1 H1'] | [[D3 [H1 H1']] | [H1 H1'] ]]]]]].
        --  
        specialize (IHn G1 G2 [] (D ++ a :: b :: D') H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c,m1 ,(☉ m2). repeat split.
            + subst. apply H6.
            + subst. constructor  4. apply H6'.
            + simpl. rewrite (atoms_list_app D (b :: a :: D')).
            simpl. rewrite (union_assoc (^V b) (^V a) (atoms_of_list D')).
            rewrite (union_comm (^V b) (^V a) ).
            simpl in H7. rewrite (atoms_list_app D (a :: b :: D')) in H7. 
            simpl in H7. rewrite (union_assoc (^V a) (^V b) (atoms_of_list D')) in H7. apply H7.
        -- rewrite H1' in H3. rewrite <- app_assoc in H3.
        specialize (IHn G1 G2 D1 (D3 ++ a :: b :: D') H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c, m1, (☉ m2). repeat split.
            + apply H6.
            + rewrite H1. constructor 4. apply H6'.
            + rewrite (atoms_list_app D (b :: a :: D')). 
            rewrite H1'. rewrite (atoms_list_app D1 D3).
            rewrite <- union_assoc. simpl. rewrite (union_assoc (^V b) (^V a) (atoms_of_list D')).
            rewrite (union_comm (^V b) (^V a) ).
            rewrite (atoms_list_app D1  (D3 ++ a :: b :: D')) in H7.
            rewrite (atoms_list_app D3 (a :: b :: D')) in H7. 
            simpl in H7. rewrite (union_assoc (^V a) (^V b) (atoms_of_list D')) in H7. apply H7.
        --
        specialize (IHn G1 G2 D (a :: b :: D') H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c, m1, (☉ m2). repeat split.
            + rewrite H1. apply H6.
            + rewrite H1'. rewrite <- app_nil_l. constructor 4. simpl. apply H6'.
            + admit.
        -- rewrite app_cons in H3. rewrite app_cons in H3. 
        rewrite app_assoc in H3. rewrite app_assoc in H3. rewrite <- (app_assoc D [a] [b]) in H3.
        specialize (IHn G1 G2 (D ++ [a] ++ [b]) (D') H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        rewrite app_comm_cons in H6.
        apply LKr_partition_mid_l in H6. destruct H6 as [m' H6].
        rewrite app_assoc in H6. rewrite (app_cons [a] D c) in H6.
        rewrite <- app_assoc in H6.
        simpl in H6.
        apply (LKr2O G1 (c :: D ++ [b]) c a m') in H6.
        apply (LKrE G1 [] (D ++ [b]) (c ∨ a) c (☉ m')) in H6.
        simpl in H6.
        apply (LKr1O G1 (c ∨ a :: D ++ [b]) c a (☉ (☉ m'))) in H6.
        apply (LKrC G1 (D ++ [b]) (c ∨ a) (☉ (☉ (☉ m')))) in H6.

        specialize (LKA a) as H6''.
        specialize (LKl_app_list [a] G2 [a] leaf H6'') as H8.
        destruct H8 as [m3 H8].
        apply LKl_cons_app in H8. destruct H8 as [m'' H8].

        apply (LKrW (c :: G2) (D') a m2) in H6'.
        apply (LKr_app_list ([a] ++ G2) [a] D' m'') in H8.
        destruct H8 as [m4 H8]. apply (LK_cons_app ([a] ++ G2) [a] D' m4) in H8.
        destruct H8 as [m5 H8]. simpl in H8.
        specialize (LKlO G2 (a :: D') c a (☉ m2) m5 H6' H8) as H9.
        exists (c ∨ a) , (☉ (☉ (☉ (☉ m')))), (☉ m2 ≍ m5). 
        repeat split.
            + rewrite H1. apply H6.
            + rewrite H1'. apply H9.
            + simpl. admit.
            (* rewrite exchg_atoms_of_list.
            replace (D ++ a :: b :: D') with ((D ++ [a] ++ [b]) ++
            D').
            apply H7. *)
        -- replace (D ++ a :: b :: D') with ((D ++ a :: b) ++ D') in H3. 
        specialize (IHn G1 G2 (D ++ a :: b) (D') H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c, (☉ m1), m2. repeat split.
            + rewrite H1. apply (LKrE G1 (c::D) [] a b m1). simpl. apply H6.
            + rewrite H1'. apply H6'.
            + rewrite exchg_atoms_of_list. 
            rewrite <- app_assoc in H7. simpl in H7. auto.
            + rewrite <- app_assoc. simpl. reflexivity.
        -- rewrite H1' in H3. rewrite app_comm_cons in H3. rewrite app_comm_cons in H3. rewrite app_assoc in H3.
        specialize (IHn G1 G2 (D ++ a :: b :: D3) (D2) H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c, (☉ m1), m2. repeat split.
            + subst. apply (LKrE G1 (c::D) D3 a b m1). simpl. apply H6.
            +subst. apply H6'.
            + rewrite exchg_atoms_of_list.
            replace ((D ++ a :: b :: D3) ++ D2) with (D ++ a :: b :: D') in H7.
            auto.
            {rewrite <- app_assoc. simpl. rewrite H1'. reflexivity. }
        -- rewrite <- app_nil_r in H3.
        specialize (IHn G1 G2 (D ++ a :: b :: D') [] H3) as H'.
        destruct H' as [c [m1 [m2 [H6 [H6' H7]]]]].
        exists c, (☉ m1), m2. repeat split.
            + subst. apply (LKrE G1 (c::D) D' a b m1). apply H6.
            + subst. apply H6'.
            + rewrite exchg_atoms_of_list. rewrite app_nil_r in H7.
            auto.
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
    - admit.
    - admit.

Admitted.
