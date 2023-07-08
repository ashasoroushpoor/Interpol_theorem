Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Import List.ListNotations.

(* Fixpoint np_occur (a : atom) (P : prop): bool :=
    match P with
    | Var a' => if (a =? a') then true else false
    | _ => false
    end. *)
Fixpoint atom_lista (P : prop) : list atom :=
    match P with
    | Var a => [a]
    | Bot => []
    | Top => []
    | Disj p1 p2 => (atom_lista p1) ++ (atom_lista p2)
    | Conj p1 p2 => (atom_lista p1) ++ (atom_lista p2)
    | LDiv p1 p2 => (atom_lista p1) ++ (atom_lista p2)
    end.
Fixpoint atom_list (l : list prop) : list atom :=
    match l with
    |nil => []
    |p :: l' => (atom_lista p) ++ (atom_list l')
    end.
    (* Print In.
    Compute in_dec PeanoNat.Nat.eq_dec 1 [1 ; 2].
    Search List.In. *)
    (* Print in_dec.
    Print List.existsb. *)
    Print fold_left.
Definition list_intersect (l1 l2 : list atom) : list atom :=
    List.filter (fun n => List.existsb (Nat.eqb n) l2) l1.
Definition foreach {T : Type} (l : list T) (P : T -> bool) :=
        fold_left andb (map P l) true = true.
(* list_in_list *)
Definition lil (l1 l2 : list atom) :=
    foreach l1 (fun n => List.existsb (Nat.eqb n) l2).
Compute lil [1 ; 2] [1 ; 2 ; 3].
Compute lil [1 ; 2] [1 ; 3].
Compute lil [1 ; 2] [2; 3; 1].
Compute lil [] [1].

Inductive lilprop : (list atom) -> (list atom) -> Prop :=
| lilnil : forall (l : list atom), lilprop [] l
| lilS : forall (a : atom) (l1 l2 : list atom),
lilprop (remove PeanoNat.Nat.eq_dec a l1) (remove PeanoNat.Nat.eq_dec a l2) -> lilprop l1 l2.

Lemma lil_empty: forall (l : list atom),
lil [] l.
Proof.
    intros. induction l.
    - unfold lil. simpl. unfold foreach. simpl. reflexivity.
    - unfold lil. unfold foreach. simpl. reflexivity.
Qed.

Print filter.
Lemma In_exist: forall (l : list nat) (n : nat),
In n l <-> (List.existsb (Nat.eqb n) l) = true.
Proof.
    intros.
    specialize (existsb_exists (Nat.eqb n) l) as H'.
    destruct H' as [H0 H1].
    split.
    - intros. apply H1. exists n. split.
        + apply H.
        + apply Nat.eqb_refl.
    - intros. apply H0 in H. destruct H. destruct H. apply EqNat.beq_nat_true in H2.
    subst. apply H.
    Qed.

Lemma foreach_def_false:forall {T : Type} (l : list T) (P : T -> bool) (a : T),
P a = false -> fold_left andb (map P (l)) false = false.
Proof.
    intros. induction l.
    - simpl. reflexivity.
    - unfold fold_left. unfold map. simpl. apply IHl.
Qed. 
Lemma foreach_app_false: forall {T : Type} (l : list T) (P : T -> bool) (a : T),
P a = false -> ~ (foreach (a :: l) P).
Proof.
    intros.
    unfold "~". intros. unfold foreach in H0. unfold fold_left in H0. 
    unfold map in H0.
    rewrite H in H0. simpl in H0.
    apply (foreach_def_false l P) in H as H1.
    unfold foreach in H1. unfold fold_left in H1. 
    unfold map in H1.
    simpl in H1.
    rewrite H1 in H0. discriminate.
Qed.
Lemma forallb_foreach: forall {T : Type} (l : list T) (P : T -> bool),
forallb P l = true <-> foreach l P.
Proof.
    intros. split.
    - intros. unfold foreach.
    induction l.
        + simpl. reflexivity.
        + specialize H as H0. rewrite forallb_forall in H. specialize (H a) as H'.
        unfold In in H'. pose proof ( H' (or_introl (eq_refl a))) as H''.
        unfold fold_left. unfold map. simpl. rewrite H''.
        simpl in H0. rewrite H'' in H0. simpl in H0. 
        apply IHl in H0. apply H0.
    - intros. induction l.
        + simpl. reflexivity.
        + 
            destruct (P a) eqn: E.
            ++ simpl. rewrite E. simpl.
            unfold foreach in H. unfold map in H. unfold fold_left in H.
            rewrite E in H. simpl in H. apply IHl in H. apply H.
            ++ simpl. rewrite E. simpl.
            specialize (foreach_app_false l P a E) as E'. apply E' in H.
            exfalso. apply H.
Qed.
Lemma foreach_forall: forall {T : Type} (l : list T) (P : T -> bool),
(foreach l P) <-> (forall (x : T), (In x l -> P x = true)).
Proof. intros. split.
    - intros. apply forallb_foreach in H. rewrite forallb_forall in H.
    specialize (H x). apply H in H0. apply H0.
    - intros. rewrite <- forallb_forall in H. rewrite forallb_foreach in H.
    apply H.
Qed.

Lemma lil_In: forall (l1 l2 : list nat), lil l1 l2 <-> 
(forall (x : nat), (In x l1) -> (In x l2)).
Proof.
    intros. split.
    - intros. unfold lil in H. rewrite foreach_forall in H.
    specialize (H x) as H'. apply H' in H0.
    rewrite <- In_exist in H0. apply H0.
    - intros. unfold lil. apply foreach_forall.
    intros. apply In_exist.
    apply (H x). apply H0.
Qed.

(* Lemma inter_split: forall (l1 l2 : list nat) (x : nat),
In x (list_intersect l1 l2) -> (In x l1) /\ (In x l2).
Proof.
    intros. unfold list_intersect in H.
    induction l2.
    - simpl in H.
    induction l1.
        + split.
            * simpl in H. exfalso. apply H.
            * simpl in H. exfalso. apply H.
        + split.
            * unfold In in H. simpl in H. apply IHl1 in H.
            unfold In. right. apply H.
            * unfold In in H. simpl in H. apply IHl1 in H.
            destruct H. apply H0.
    - destruct l1.
        + admit.
        +
    unfold filter in H. unfold In in H. simpl in H.  
    induction l1.
        + admit.
        + unfold In in H. unfold filter in H. simpl in H. destruct (a0 =? a) eqn: E.
            * simpl in H. destruct H.
                ** admit.
                ** fold (filter (fun n : nat => existsb (Nat.eqb n) (l2))) in H.
    induction l1.
        + exfalso. simpl in H. apply H.
        + unfold filter in H. simpl in H. destruct (a0 =? a) eqn: E. 
            * apply (EqNat.beq_nat_true a0 a) in E as E'. simpl in H. destruct H.
                ** split.
                    {
                        unfold In.
                        rewrite H. left. reflexivity. 
                    }
                    {
                        unfold In.
                        rewrite <- E'. rewrite H. left. reflexivity. 
                    }
                ** apply IHl1 in H.
                    {
                        admit.
                    }
                    {
                        intros.
                    } *)

(* Lemma inter_app_l : forall (l1 l2 : list atom) (a : atom),
(list_intersect l1 (a :: l2)) = a :: (list_intersect l1 l2)
\/ (list_intersect l1 (a :: l2)) = (list_intersect l1 l2).
Proof.
    intros. induction l1. generalize dependent l2.
    - right. simpl. reflexivity.
    - destruct IHl1.
        + left. unfold list_intersect. simpl. destruct (a0 =? a) eqn: E.
            ++ simpl. apply EqNat.beq_nat_true in E. subst.
            unfold list_intersect in H. simpl in H.
Lemma lil_inter_app_r : forall (l1 l2 l3 :list atom) (a : atom),
lil l1 (list_intersect l2 l3) -> lil l1 (list_intersect l2 (a :: l3)).
Proof.
    intros. induction l1.
    - apply lil_empty. *)

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
Theorem LK_Interpol: forall n (G1 G2 D1 D2 : list prop),
G1 ++ G2 ⇒ D1 ++ D2 >< n -> 
(exists (c : prop) m1 m2, G1 ⇒ c :: D1 >< m1 /\ c :: G2 ⇒ D1 >< m2
(* /\ lil (atom_lista c) (list_intersect (atom_list(G1 ++ G2)) (atom_list(D1 ++ D2)))). *)
/\ (forall (x : atom), (In_prop x c) -> ((In_list_prop x (G1 ++ G2) /\ In_list_prop x (D1 ++ D2)))))
induction n; intros G1 G2 D1 D2 H; inversion H.
    - admit.
    - destruct D1.
        + simpl in H1. simpl in H. rewrite <- H1 in H.
        Search ([] ++ _).
        rewrite <- app_nil_l in H3.
        specialize (IHn G1 G2 [] D H3) as H'.
        destruct H' as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1, m2. repeat split.
            * apply IH1.
            * apply IH2.
            * simpl in IH3.

Admitted.