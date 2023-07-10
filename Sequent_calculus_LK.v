Require Import Lang.
Require Import List.
Import List.ListNotations.


Coercion list_to_prop (P : prop) : (list prop) := [P].
Reserved Notation "G ⇒ p >< n" (no associativity, at level 61). (* 21d2 *)

Inductive Node : Type :=
|leaf : Node
|one: Node -> Node
|two: Node -> Node -> Node.

Inductive LK : Node -> list prop -> list prop -> Prop :=
(* Axiom : A |- A *)
| LKA: forall p : prop, p ⇒ p >< leaf
(* Structral Rules *)
(* Weakening *)
|LKrW: forall G D (a: prop) n, G ⇒ D >< n-> G ⇒ a :: D >< one n
|LKlW: forall G D (a: prop) n, G ⇒ D >< n -> a :: G  ⇒ D >< one n
(* Exchange *)
|LKrE: forall G D D' (a b : prop) n, G ⇒ D ++ (a :: b :: D') >< n -> 
        G ⇒ D ++ (b :: a :: D') >< one n
|LKlE: forall G G' D (a b : prop) n, G ++ (a :: b :: G') ⇒ D >< n ->
        G ++ (b :: a :: G') ⇒ D >< one n
(* Contraction *)
|LKrC: forall G D (a : prop) n, G ⇒ a :: a :: D >< n -> G ⇒ a :: D >< one n
|LKlC: forall G D (a : prop) n, a :: a :: G  ⇒ D >< n -> a :: G ⇒ D >< one n
(* Logical Rules *)
(* Conjunction *)
|LKrA: forall G G' D D' (a b: prop) m n,
G ⇒ a :: D >< m-> G' ⇒ b :: D' >< n -> G ++ G' ⇒ (a ∧ b) :: D ++ D' >< two m n
|LKl1A: forall G D (a b : prop) n,
a :: G ⇒ D >< n -> (a ∧ b) :: G ⇒ D >< one n
|LKl2A: forall G D (a b : prop) n,
b :: G ⇒ D >< n -> (a ∧ b) :: G ⇒ D >< one n
(* Disjunction *)
|LKr1O: forall G D (a b : prop) n,
G ⇒ a :: D >< n -> G ⇒ (a ∨ b) :: D >< one n
|LKr2O: forall G D (a b : prop) n,
G ⇒ b :: D >< n -> G ⇒ (a ∨ b) :: D >< one n
|LKlO: forall G G' D D' (a b : prop) m n,
a :: G ⇒ D >< m -> b :: G' ⇒ D' >< n -> (a ∨ b) :: G ++ G'  ⇒ D ++ D' >< two m n
(* Negation *)
|LKrN: forall G D (a : prop) n, a :: G ⇒ D >< n -> G ⇒ (¬ a) :: D >< one n
|LKlN: forall G D (a : prop) n, G ⇒ a :: D >< n -> (¬ a) :: G  ⇒ D >< one n
(* Implication *)
|LKrI: forall G D (a b : prop) n, a :: G  ⇒ b :: D >< n ->
        G ⇒ (a ⊃ b) :: D >< one n
|LKlI: forall G G' D D' (a b : prop) m n,
        G ⇒ a :: D >< m -> b :: G' ⇒ D' >< n->
        (a ⊃ b) :: G ++ G' ⇒ D ++ D' >< two m n
where "G ⇒ p >< n" := (LK n G p).



Lemma mp : forall p q : prop, exists n, (p ⊃ q)::p ⇒ q >< n.
Proof.
  intros p q.
  exists (two leaf leaf). 
  (* apply (LKlE [] [] q p (p ⊃ q)). simpl.
  apply (LKlE [] [] q p ) *)
  apply (LKlI p [] [] q p q leaf leaf).
  - apply (LKA p).
  - apply (LKA q).
Qed.

Lemma cut : forall (G G' D D' : list prop) (a : prop) m n,
G ⇒ a :: D >< m -> G' ++ a ⇒ D' >< n -> exists r, G ++ G' ⇒ D ++ D' >< r.
Admitted.

Lemma deduction_r : forall (p q : prop) (n : Node), exists (m : Node),p ⇒ q >< n -> [] ⇒ p ⊃ q >< m.
Proof.
    intros.
    exists (one n).
    intros.
    apply (LKrI [] [] p q n).
    apply H.
Qed. 


Lemma deduction_l : forall (p q : prop), (exists (n : Node), [] ⇒ p ⊃ q >< n) -> exists (m : Node), p ⇒ q >< m .
intros. destruct H as [n H]. specialize (mp p q) as H'. destruct H' as [m H']. apply (cut [] [p] [] [q] (p ⊃ q) n (one m)).
    + apply H.
    + apply (LKlE [] [] q (p ⊃ q) p m). simpl. apply H'. 
    Qed.