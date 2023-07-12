Require Import Lang.
Require Import List.
Import List.ListNotations.
   

Coercion list_to_prop (P : prop) : (list prop) := [P].
(* Reserved Notation "G1 +' G2 ⇒ D1 +'' D2 >< n" (no associativity, at level 61). (* 21d2 *) *)
Reserved Notation "G ⇒ p >< n" (no associativity, at level 61). (* 21d2 *)
Inductive Node : Type :=
|leaf : Node
|onen: Node -> Node
|twon: Node -> Node -> Node.

Notation "☉ M" := (onen M) (no associativity, at level 65).
Notation "M1 ≍ M2" := (twon M1 M2 )(no associativity, at level 66). 

(* Inductive LK : Node -> list prop -> list prop -> list prop -> list prop -> Prop :=
(* Axiom : A |- A *)
| LKA: forall p : prop, p +' [] ⇒ p +'' [] >< leaf
(* Structral Rules *)
(* Weakening *)
|LKrW: forall G1 G2 D1 D2 (a: prop) n, G1 +' G2 ⇒ D1 +'' D2 >< n-> G1 +' G2 ⇒ a :: D1 +'' D2 >< onen n
|LKlW: forall G1 G2 D1 D2 (a: prop) n, G1 +' G2 ⇒ D1 +'' D2 >< n -> a :: G1 +' G2  ⇒ D1 +'' D2 >< onen n
(* Exchange *)
|LKrE: forall G1 G2 D1 D2 (a b : prop) n, G1 +' G2 ⇒ (a :: b :: D1) +'' D2 >< n -> 
        G1 +' G2 ⇒ (b :: a :: D1) +'' D2 >< onen n
|LKlE: forall G1 G2 D1 D2 (a b : prop) n, (a :: b :: G1) +' G2 ⇒ D1 +'' D2 >< n ->
        (b :: a :: G1) +' G2 ⇒ D1 +'' D2 >< onen n
(* Contraction *)
|LKrC: forall G1 G2 D1 D2 (a : prop) n, G1 +' G2 ⇒ (a :: a :: D1) +'' D2 >< n -> G1 +' G2 ⇒ (a :: D1) +'' D2 >< onen n
|LKlC: forall G1 G2 D1 D2 (a : prop) n, a :: a :: G1 +' G2  ⇒ D1 +'' D2 >< n -> a :: G1 +' G2 ⇒ D1 +'' D2 >< onen n
(* Logical Rules *)
(* Conjunction *)
|LKrA: forall G1 G2 D1 D2 (a b: prop) m n,
G1 +' G2 ⇒ a :: D1 +'' D2 >< m-> G1 +' G2⇒ b :: D1 +'' D2 >< n -> G1 +' G2 ⇒ (a ∧ b) :: D1 +'' D2  >< twon m n
|LKl1A: forall G1 G2 D1 D2 (a b : prop) n,
a :: G1 +' G2 ⇒ D1 +'' D2 >< n -> (a ∧ b) :: G1 +' G2 ⇒ D1 +'' D2 >< onen n
|LKl2A: forall G1 G2 D1 D2 (a b : prop) n,
b :: G1 +' G2 ⇒ D1 +'' D2 >< n -> (a ∧ b) :: G1 +' G2 ⇒ D1 +'' D2 >< onen n
(* Disjunction *)
|LKr1O: forall G1 G2 D1 D2 (a b : prop) n,
G1 +' G2 ⇒ a :: D1 +'' D2 >< n -> G1 +' G2 ⇒ (a ∨ b) :: D1 +'' D2 >< onen n
|LKr2O: forall G1 G2 D1 D2 (a b : prop) n,
G1 +' G2 ⇒ b :: D1 +'' D2 >< n -> G1 +' G2 ⇒ (a ∨ b) :: D1 +'' D2 >< onen n
|LKlO: forall G1 G2 D1 D2 (a b : prop) m n,
a :: G1 +' G2 ⇒ D1 +'' D2 >< m -> b :: G1 +' G2 ⇒ D1 +'' D2 >< n -> (a ∨ b) :: G1 +' G2  ⇒ D1 +'' D2 >< twon m n
(* Negation *)
|LKrN: forall G1 G2 D1 D2 (a : prop) n, a :: G1 +' G2 ⇒ D1 +'' D2 >< n -> G1 +' G2 ⇒ (¬ a) :: D1 +'' D2 >< onen n
|LKlN: forall G1 G2 D1 D2 (a : prop) n, G1 +' G2 ⇒ a :: D1 +'' D2 >< n -> (¬ a) :: G1 +' G2  ⇒ D1 +'' D2 >< onen n
(* Implication *)
|LKrI: forall G1 G2 D1 D2 (a b : prop) n, a :: G1 +' G2  ⇒ b :: D1 +'' D2 >< n ->
        G1 +' G2 ⇒ (a ⊃ b) :: D1 +'' D2 >< onen n
|LKlI: forall G1 G2 D1 D2 (a b : prop) m n,
        G1 +' G2 ⇒ a :: D1 +'' D2 >< m -> b :: G1 +' G2 ⇒ D1 +'' D2 >< n->
        (a ⊃ b) :: G1 +' G2 ⇒ D1 +'' D2 >< twon m n
where "G1 +' G2 ⇒ D1 +'' D2 >< n" := (LK n G1 G2 D1 D2). *)


Inductive LK : Node -> list prop -> list prop -> Prop :=
(* Axiom : A |- A *)
(*1*)
| LKA: forall p : prop, p ⇒ p >< leaf
(* Structral Rules *)
(* Weakening *)
(*2*)
|LKrW: forall G D (a: prop) n, G ⇒ D >< n-> G ⇒ a :: D >< ☉n
(*3*)
|LKlW: forall G D (a: prop) n, G ⇒ D >< n -> a :: G  ⇒ D >< ☉ n
(* Exchange *)
(*4*)
|LKrE: forall G D D' (a b : prop) n, G ⇒ D ++ (a :: b :: D') >< n -> 
        G ⇒ D ++ (b :: a :: D') >< ☉ n
(*5*)
|LKlE: forall G G' D (a b : prop) n, G ++ (a :: b :: G') ⇒ D >< n ->
        G ++ (b :: a :: G') ⇒ D >< ☉ n
(* Contraction *)
(*6*)
|LKrC: forall G D (a : prop) n, G ⇒ a :: a :: D >< n -> G ⇒ a :: D >< ☉ n
(*7*)
|LKlC: forall G D (a : prop) n, a :: a :: G  ⇒ D >< n -> a :: G ⇒ D >< ☉ n
(* Logical Rules *)
(* Conjunction *)
(*8*)
|LKrA: forall G D (a b: prop) m n,
G ⇒ a :: D >< m-> G ⇒ b :: D >< n -> G ⇒ (a ∧ b) :: D  >< (m ≍ n)
(*9*)
|LKl1A: forall G D (a b : prop) n,
a :: G ⇒ D >< n -> (a ∧ b) :: G ⇒ D >< ☉ n
(*10*)
|LKl2A: forall G D (a b : prop) n,
b :: G ⇒ D >< n -> (a ∧ b) :: G ⇒ D >< ☉ n
(* Disjunction *)
(*11*)
|LKr1O: forall G D (a b : prop) n,
G ⇒ a :: D >< n -> G ⇒ (a ∨ b) :: D >< ☉ n
(*12*)
|LKr2O: forall G D (a b : prop) n,
G ⇒ b :: D >< n -> G ⇒ (a ∨ b) :: D >< ☉ n
(*13*)
|LKlO: forall G D (a b : prop) m n,
a :: G ⇒ D >< m -> b :: G ⇒ D >< n -> (a ∨ b) :: G  ⇒ D >< (m ≍ n)
(* Negation *)
(*14*)
|LKrN: forall G D (a : prop) n, a :: G ⇒ D >< n -> G ⇒ (¬ a) :: D >< ☉ n
(*15*)
|LKlN: forall G D (a : prop) n, G ⇒ a :: D >< n -> (¬ a) :: G  ⇒ D >< ☉ n
(* Implication *)
(*16*)
|LKrI: forall G D (a b : prop) n, a :: G  ⇒ b :: D >< n ->
        G ⇒ (a ⊃ b) :: D >< ☉ n
(*17*)
|LKlI: forall G D (a b : prop) m n,
        G ⇒ a :: D >< m -> b :: G ⇒ D >< n->
        (a ⊃ b) :: G ⇒ D >< (m ≍ n)
where "G ⇒ p >< n" := (LK n G p).



Lemma LKr_app_list: forall G D D' m,
G ⇒ D >< m -> (exists m', G ⇒ D' ++ D >< m').
Proof.
    intros. induction D'.
    - exists m. simpl. apply H.
    - destruct IHD' as [m' H']. exists (☉ m').
    rewrite <- app_comm_cons. constructor 2. apply H'.
Qed.

Lemma app_cons: forall {X : Type}(l l' : list X) (a : X),
l ++ a :: l' = l ++ [a] ++ l'.
Proof.
    intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.
Lemma LKr_partition_mid_atom_r: forall G D D' a m,
G ⇒ D ++ a :: D' >< m -> (exists m', G ⇒ D ++ D' ++ a >< m').
Proof.
    intros. generalize dependent D. generalize dependent m. induction D'.
    - intros. simpl. exists m. apply H.
    - intros. specialize (IHD' (☉ m) (D ++ [a0])) as H'.
    apply (LKrE G D D' a a0 m) in H.
    rewrite app_cons in H. rewrite app_assoc in H.
    apply H' in H as H0. destruct H0 as [m' H0].
    rewrite app_assoc in H0. rewrite <- (app_assoc D [a0] D') in H0.
    rewrite <- app_cons in H0. rewrite <- app_assoc in H0.
    exists m'. apply H0.
Qed.

Lemma LKr_partition_mid_atom_l: forall G D D' a m,
G ⇒ D ++ a :: D' >< m -> (exists m', G ⇒ a :: D ++ D' >< m').
Proof.
    intros. generalize dependent D'. generalize dependent m.
    induction D using rev_ind.
    - intros. exists m. subst. simpl. simpl in H. apply H.
    - intros. rewrite <- app_assoc in H. rewrite <- app_cons in H.
    apply (LKrE G D D' x a m) in H.
    specialize (IHD (☉ m) (x :: D') H) as H'. destruct H' as [m' H'].
    exists m'. rewrite <- app_assoc. rewrite <- app_cons. apply H'.
Qed.

Lemma LKr_partition_mid_l: forall G D D' D'' m,
G ⇒ D'' ++ D ++ D' >< m -> (exists m', G ⇒ D ++ D'' ++ D' >< m').
Proof.
    intros. 
    generalize dependent D'.
    generalize dependent D''.
    induction D.
    - intros. simpl. simpl in H. exists m. apply H. 
    - intros. rewrite app_assoc in H. rewrite app_cons in H.
    rewrite app_assoc in H. rewrite <- app_assoc in H.
    specialize (IHD (D'' ++ a :: []) D' H) as H'. destruct H' as [m' H'].
    rewrite <- app_assoc in H'. rewrite <- app_cons in H'. rewrite app_assoc in H'.
    apply (LKr_partition_mid_atom_l) in H'.
    destruct H' as [m'' H']. rewrite <- app_assoc in H'.
    exists m''.
    rewrite <- (app_nil_l (a :: D)). rewrite app_cons. simpl. apply H'.
Qed.

Lemma LKr_partition_mid_r: forall G D D' D'' m,
G ⇒ D'' ++ D ++ D' >< m -> (exists m', G ⇒ D'' ++ D' ++ D >< m').
Proof.
    intros. 
    generalize dependent D'.
    generalize dependent D''.
    induction D using rev_ind.
    - intros. rewrite app_nil_r. simpl in H. exists m. apply H. 
    - intros. rewrite <- app_assoc in H. 
    specialize (IHD D'' ([x] ++ D') H) as H'. destruct H' as [m' H'].
    rewrite <- app_assoc in H'. apply LKr_partition_mid_atom_r in H'.
    destruct H' as [m'' H'].
    exists m''. rewrite <- app_assoc in H'. apply H'.
Qed.
Lemma LK_cons_app: forall G D D' m,
 G ⇒ D' ++ D >< m -> (exists m', G ⇒ D ++ D' >< m').
Proof.
        intros.
        rewrite <- app_nil_l in H. apply LKr_partition_mid_r in H. apply H.
Qed.
Lemma LKr_weak_l: forall G D a m,
 G ⇒ D >< m -> (exists m', G ⇒ D ++ [a] >< m').
Proof.
        intros. 
        apply (LKrW G D a m) in H. 
        rewrite <- app_nil_l in H. rewrite app_cons in H.
        apply LKr_partition_mid_r in H. destruct H as [m' H]. simpl in H.
        exists m'. apply H.
Qed.


Lemma LKl_app_list: forall G G' D m,
G ⇒ D >< m -> (exists m', G' ++ G ⇒ D >< m').
Proof.
    Admitted.
Lemma LKl_partition_mid_atom_r: forall G G' D a m,
G ++ a :: G' ⇒ D  >< m -> (exists m', G ++ G' ++ a ⇒ D  >< m').
Proof.
    Admitted.

Lemma LKl_partition_mid_atom_l: forall G G' D a m,
G ++ a :: G' ⇒ D >< m -> (exists m', a :: G ++ G' ⇒ D >< m').
Proof.
    Admitted.

Lemma LKl_partition_mid_l: forall G G' G'' D m,
G'' ++ G ++ G' ⇒ D >< m -> (exists m', G ++ G'' ++ G' ⇒ D  >< m').
Proof.
    Admitted.

Lemma LKl_partition_mid_r: forall G G' G'' D m,
G'' ++ G ++ G' ⇒ D >< m -> (exists m', G'' ++ G' ++ G ⇒ D >< m').
Proof.
    Admitted.
Lemma LKl_cons_app: forall G G' D m,
 G' ++ G ⇒ D >< m -> (exists m', G ++ G' ⇒ D >< m').
Proof.
    Admitted.


Lemma mp : forall p q : prop, exists n, (p ⊃ q)::p ⇒ q >< n.
Proof.
  intros p q.
  (* (☉ ☉ leaf) ≍ (☉ ☉ leaf) *)
  exists ((☉ ☉ leaf) ≍ (☉ ☉ leaf)). 
  (* apply (LKlE [] [] q p (p ⊃ q)). simpl.
  apply (LKlE [] [] q p ) *)
  apply (LKlI p q p q (onen (onen leaf)) (onen (onen leaf))).
  - apply (LKrE p [] [] q p (onen leaf)). simpl. apply (LKrW p p q leaf). apply (LKA p).
  - apply (LKlE [] [] q p q (onen leaf)). simpl. apply (LKlW q q p leaf). apply (LKA q).
Qed.

Lemma cut : forall (G G' D D' : list prop) (a : prop) m n,
G ⇒ a :: D >< m -> G' ++ a ⇒ D' >< n -> exists r, G ++ G' ⇒ D ++ D' >< r.
Admitted.

(* Lemma deduction_r : forall (p q : prop) (n : Node), exists (m : Node),p ⇒ q >< n -> [] ⇒ p ⊃ q >< m.
Proof.
    intros.
    exists (onen n).
    intros.
    apply (LKrI [] [] p q n).
    apply H.
Qed. 


Lemma deduction_l : forall (p q : prop), (exists (n : Node), [] ⇒ p ⊃ q >< n) -> exists (m : Node), p ⇒ q >< m .
intros. destruct H as [n H]. specialize (mp p q) as H'. destruct H' as [m H']. apply (cut [] [p] [] [q] (p ⊃ q) n (onen m)).
    + apply H.
    + apply (LKlE [] [] q (p ⊃ q) p m). simpl. apply H'. 
    Qed. *)