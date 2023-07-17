Require Import Lang.
Require Import Sequent_calculus_LK.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import Finset.
Require Import Formula.
Require Import Sequent_Calculus_LK_set.
Require Import BinNat BinNatDef BinPos BinPosDef.
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

Theorem LK_Interpol_strong: forall n (G1 G2 D1 D2 : finset),
G1 ∪ G2 ⤑ D1 ∪ D2 >< n -> G1 ∩ G2 = ∅ -> D1 ∩ D2 = ∅-> 
(exists (c : prop) m1 m2, G1 ⤑ {{c}} ∪ D1 >< m1 /\ {{c}} ∪ G2 ⤑ D2 >< m2).
(* /\ lil (atom_lista c) (list_intersect (atom_list(G1 ++ G2)) (atom_list(D1 ++ D2)))). *)
(* /\ (forall (x : atom), (In_prop x c) -> ((In_list_prop x (G1 ++ G2) /\ In_list_prop x (D1 ++ D2))))). *)
(* /\ (atoms_of c) ⊆ ( (atoms_of_list (G1 ++ G2)) ∩ (atoms_of_list (D1 ++ D2)))). *)
Proof.
    induction n; intros G1 G2 D1 D2 H Hg Hd; inversion H.
    - admit.
    -