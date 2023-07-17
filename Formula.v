Require Import Lang.
Require Import Finset.
Require Import List.
Require Import Sequent_Calculus_LK_set.
Require Import BinNat BinNatDef BinPos BinPosDef.
Include BinNatDef.N.
Import List.ListNotations.

Fixpoint weight (p : prop) : nat :=
match p with
  | p1 ∧ p2 => S ((weight p1) + (weight p2))
  | p1 ∨ p2 => S ((weight p1) + (weight p2))
  | p1 ⊃ p2 => S ((weight p1) + (weight p2))
  | _ => S O
  end.

Fixpoint atoms_of (p : prop) : finset :=
  match p with
  | ^x_a => {{a}}
  | p1 ∧ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ∨ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | p1 ⊃ p2 => (atoms_of p1) ∪ (atoms_of p2)
  | _ => ∅
  end.
Notation "^V" := atoms_of.

Fixpoint atoms_num (p : prop) : nat :=
  match p with
    | ^x__ => 1
    | p1 ∧ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ∨ p2 => (atoms_num p1) + (atoms_num p2)
    | p1 ⊃ p2 => (atoms_num p1) + (atoms_num p2)
    | _ => 0
    end.
  
Fixpoint atoms_of_list (l : list prop) : finset :=
  match l with
  | nil => ∅
  | p :: l' => (atoms_of p) ∪ (atoms_of_list l')
  end.

Fixpoint atoms_num_list (l : list prop) : nat :=
    match l with
    | nil => 0
    | p :: l' => (atoms_num p) + (atoms_num_list l')
    end.

Fixpoint weight_list (l : list prop) : nat :=
    match l with
    | nil => 0
    | p :: l' => (weight p) + (weight_list l')
    end.

Lemma atoms_list_app: forall l l',
atoms_of_list(l ++ l') = atoms_of_list(l) ∪ atoms_of_list(l').
Proof.
  intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. rewrite union_assoc.
    reflexivity.
Qed.

Lemma exchg_atoms_of_list: forall D D' a b,
atoms_of_list (D ++ a :: b :: D') = atoms_of_list (D ++ b :: a :: D').
Proof.
    intros. induction D.
        - simpl. rewrite union_assoc. 
        rewrite (union_comm (^V a) (^V b)). rewrite union_assoc.
        reflexivity.
        - simpl. rewrite IHD. reflexivity.
Qed.
Fixpoint atoms_of_pos (p: positive) (n : nat): finset :=
    match p with
        | xH => atoms_of(nat_to_prop(n))
        | xO p' => atoms_of_pos p' (S n)
        | xI p' => atoms_of(nat_to_prop(n)) ∪ (atoms_of_pos p' (S n))
    end.
Definition atoms_of_set (s: finset): finset :=
    match s with
    | ∅ => ∅
    | pos p => atoms_of_pos p 0 
    end.

Lemma pos_size_le_0: forall p, Pos.size_nat p <= 0 -> False.
    Proof. intros.
    induction p; apply Le.le_n_0_eq in H; discriminate.
Qed.
Lemma atoms_pos_double: forall n m p1 p2, 
Pos.size_nat p1 <= n -> 
atoms_of_pos (Pos.lor p1 p2) m = (atoms_of_pos p1 m) ∪ (atoms_of_pos p2 m).
Proof.
    intros. generalize dependent m. induction n.
    - exfalso. apply pos_size_le_0 in H. assumption.
    - intros. destruct p1.
Lemma atoms_pos_union: forall p1 p2, atoms_of_pos (Pos.lor p1 p2) 0 = (atoms_of_pos p1 0) ∪ (atoms_of_pos p2 0).
Proof.
    

Lemma atoms_set_union: forall s1 s2, atoms_of_set (s1 ∪ s2) = (atoms_of_set s1) ∪ (atoms_of_set s2).
Proof.
    intros. induction s1.
        - simpl. reflexivity.
        - induction p.
            + simpl. admit.
            + simpl.
Qed.

(* 
Require Import BinNat BinNatDef BinPos BinPosDef.
Fixpoint partition {T : Type} (l : list T) (mask : N) : list T :=
  match (l, mask) with
  | (_, 0%N) => []
  | ([], _) => []
  | (h :: t, pos p) => match p with
                      | xH => [h]
                      | xO p => partition t p
                      | xI p => h :: (partition t p)
                      end
  end.

Fixpoint partition_list {T : Type} (l : list T) (mask : N) : list (list T) :=
  match (l, mask) with
  ([], _) => [[]]
  (_, 0%N) => [[]]
  (h :: t, pos p) => match p with
                    | xH => [[h]]
                    | xO p => 
  end.

Compute (partition_list [2;3;4;5]).


Fixpoint E0 (a : atom) (G : list prop) (mask : nat) : prop :=
  match G with
  | [] => 1
  | [^x_b] => if PeanoNat.Nat.eqb a b then ⊤ else ^x_b
  | (p ∧ q) :: G => (E0 a (p :: G) mask) ∧ (E0 a (p :: G) mask)
  | (p ∨ q) :: G => (E0 a (p :: G) mask) ∨ (E0 a (p :: G) mask)
  | (p ⊗ q) :: G => E0 a (p :: q :: G) mask
  | _ => 0
  end.


Fixpoint E1 (a : atom) (G : list prop) (mask : nat) : prop :=
  match (BinNatDef.of_nat mask) with
  | 0%N =>  *)