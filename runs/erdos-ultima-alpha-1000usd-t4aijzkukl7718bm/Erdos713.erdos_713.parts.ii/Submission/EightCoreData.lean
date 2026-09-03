import FormalConjecturesUtil
import Submission.UpToExpandingRegularization

/-! Explicit finite certificates for four-by-four bipartite matrices. -/
namespace Erdos713EightCore
set_option Elab.async false
open SimpleGraph Finset

abbrev Rows := Fin 4 → Fin 16

def bit (r : Rows) (i j : Fin 4) : Bool := (r i).val.testBit j.val

def rowCount (r : Rows) (i : Fin 4) : ℕ :=
  (bit r i 0).toNat + (bit r i 1).toNat + (bit r i 2).toNat + (bit r i 3).toNat

def colCount (r : Rows) (j : Fin 4) : ℕ :=
  (bit r 0 j).toNat + (bit r 1 j).toNat + (bit r 2 j).toNat + (bit r 3 j).toNat

def Good (r : Rows) : Prop :=
  (∀ i : Fin 4, 2 ≤ rowCount r i) ∧ (∀ j : Fin 4, 2 ≤ colCount r j)
instance (r : Rows) : Decidable (Good r) := inferInstanceAs (Decidable (_ ∧ _))

def Sorted (r : Rows) : Prop := r 0 ≤ r 1 ∧ r 1 ≤ r 2 ∧ r 2 ≤ r 3
instance (r : Rows) : Decidable (Sorted r) := inferInstanceAs (Decidable (_ ∧ _))

def permutation : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

lemma permutation_bijective : ∀ k, Function.Bijective (permutation k) := by decide

noncomputable def permEquiv (k : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (permutation k) (permutation_bijective k)

def representative : Fin 32 → Rows :=
  ![![3, 3, 12, 12], ![3, 5, 10, 12], ![3, 3, 12, 13], ![3, 5, 9, 14], ![3, 5, 10, 13], ![3, 3, 12, 15], ![3, 3, 13, 14], ![3, 5, 9, 15], ![3, 5, 10, 15], ![3, 5, 11, 14], ![3, 5, 14, 14], ![3, 7, 12, 13], ![3, 3, 13, 15], ![3, 5, 11, 15], ![3, 5, 14, 15], ![3, 7, 12, 15], ![3, 7, 13, 14], ![3, 13, 13, 14], ![3, 3, 15, 15], ![3, 5, 15, 15], ![3, 7, 13, 15], ![3, 12, 15, 15], ![3, 13, 13, 15], ![3, 13, 14, 15], ![7, 11, 13, 14], ![3, 7, 15, 15], ![3, 13, 15, 15], ![7, 11, 13, 15], ![3, 15, 15, 15], ![7, 11, 15, 15], ![7, 15, 15, 15], ![15, 15, 15, 15]]

abbrev Certificate := Fin 32 × Bool × Fin 24 × Fin 24

def certificate (r : Rows) : Certificate :=
  match (r 0).val, (r 1).val, (r 2).val, (r 3).val with
  | 3, 3, 12, 12 => (0, false, 0, 0)
  | 3, 3, 12, 13 => (2, false, 0, 0)
  | 3, 3, 12, 14 => (2, false, 0, 6)
  | 3, 3, 12, 15 => (5, false, 0, 0)
  | 3, 3, 13, 13 => (5, true, 17, 16)
  | 3, 3, 13, 14 => (6, false, 0, 0)
  | 3, 3, 13, 15 => (12, false, 0, 0)
  | 3, 3, 14, 14 => (5, true, 16, 16)
  | 3, 3, 14, 15 => (12, false, 0, 6)
  | 3, 3, 15, 15 => (18, false, 0, 0)
  | 3, 5, 9, 14 => (3, false, 0, 0)
  | 3, 5, 9, 15 => (7, false, 0, 0)
  | 3, 5, 10, 12 => (1, false, 0, 0)
  | 3, 5, 10, 13 => (4, false, 0, 0)
  | 3, 5, 10, 14 => (4, false, 2, 7)
  | 3, 5, 10, 15 => (8, false, 0, 0)
  | 3, 5, 11, 12 => (4, false, 7, 2)
  | 3, 5, 11, 13 => (8, true, 21, 16)
  | 3, 5, 11, 14 => (9, false, 0, 0)
  | 3, 5, 11, 15 => (13, false, 0, 0)
  | 3, 5, 12, 14 => (4, false, 8, 13)
  | 3, 5, 12, 15 => (8, false, 6, 2)
  | 3, 5, 13, 14 => (9, false, 6, 2)
  | 3, 5, 13, 15 => (13, false, 6, 2)
  | 3, 5, 14, 14 => (10, false, 0, 0)
  | 3, 5, 14, 15 => (14, false, 0, 0)
  | 3, 5, 15, 15 => (19, false, 0, 0)
  | 3, 6, 9, 12 => (1, false, 2, 1)
  | 3, 6, 9, 13 => (4, false, 2, 1)
  | 3, 6, 9, 14 => (4, false, 0, 6)
  | 3, 6, 9, 15 => (8, false, 2, 1)
  | 3, 6, 10, 13 => (3, false, 0, 6)
  | 3, 6, 10, 15 => (7, false, 0, 6)
  | 3, 6, 11, 12 => (4, false, 7, 8)
  | 3, 6, 11, 13 => (9, false, 0, 6)
  | 3, 6, 11, 14 => (8, true, 19, 16)
  | 3, 6, 11, 15 => (13, false, 0, 6)
  | 3, 6, 12, 13 => (4, false, 8, 15)
  | 3, 6, 12, 15 => (8, false, 6, 8)
  | 3, 6, 13, 13 => (10, false, 0, 6)
  | 3, 6, 13, 14 => (9, false, 7, 8)
  | 3, 6, 13, 15 => (14, false, 0, 6)
  | 3, 6, 14, 15 => (13, false, 6, 8)
  | 3, 6, 15, 15 => (19, false, 0, 6)
  | 3, 7, 9, 12 => (4, false, 13, 4)
  | 3, 7, 9, 13 => (8, true, 15, 10)
  | 3, 7, 9, 14 => (9, false, 2, 1)
  | 3, 7, 9, 15 => (13, false, 2, 1)
  | 3, 7, 10, 12 => (4, false, 13, 10)
  | 3, 7, 10, 13 => (9, false, 2, 7)
  | 3, 7, 10, 14 => (8, true, 13, 10)
  | 3, 7, 10, 15 => (13, false, 2, 7)
  | 3, 7, 11, 12 => (10, true, 16, 21)
  | 3, 7, 11, 13 => (14, true, 17, 21)
  | 3, 7, 11, 14 => (14, true, 16, 21)
  | 3, 7, 11, 15 => (19, true, 16, 21)
  | 3, 7, 12, 12 => (2, false, 16, 16)
  | 3, 7, 12, 13 => (11, false, 0, 0)
  | 3, 7, 12, 14 => (11, false, 0, 6)
  | 3, 7, 12, 15 => (15, false, 0, 0)
  | 3, 7, 13, 13 => (15, true, 23, 17)
  | 3, 7, 13, 14 => (16, false, 0, 0)
  | 3, 7, 13, 15 => (20, false, 0, 0)
  | 3, 7, 14, 14 => (15, true, 22, 17)
  | 3, 7, 14, 15 => (20, false, 0, 6)
  | 3, 7, 15, 15 => (25, false, 0, 0)
  | 3, 9, 12, 14 => (4, false, 8, 19)
  | 3, 9, 12, 15 => (8, false, 6, 4)
  | 3, 9, 13, 14 => (9, false, 6, 4)
  | 3, 9, 13, 15 => (13, false, 6, 4)
  | 3, 9, 14, 14 => (10, false, 0, 1)
  | 3, 9, 14, 15 => (14, false, 0, 1)
  | 3, 9, 15, 15 => (19, false, 0, 1)
  | 3, 10, 12, 13 => (4, false, 8, 21)
  | 3, 10, 12, 15 => (8, false, 6, 10)
  | 3, 10, 13, 13 => (10, false, 0, 7)
  | 3, 10, 13, 14 => (9, false, 7, 10)
  | 3, 10, 13, 15 => (14, false, 0, 7)
  | 3, 10, 14, 15 => (13, false, 6, 10)
  | 3, 10, 15, 15 => (19, false, 0, 7)
  | 3, 11, 12, 12 => (2, false, 16, 22)
  | 3, 11, 12, 13 => (11, false, 0, 1)
  | 3, 11, 12, 14 => (11, false, 0, 7)
  | 3, 11, 12, 15 => (15, false, 0, 1)
  | 3, 11, 13, 13 => (15, true, 17, 17)
  | 3, 11, 13, 14 => (16, false, 0, 1)
  | 3, 11, 13, 15 => (20, false, 0, 1)
  | 3, 11, 14, 14 => (15, true, 16, 17)
  | 3, 11, 14, 15 => (20, false, 0, 7)
  | 3, 11, 15, 15 => (25, false, 0, 1)
  | 3, 12, 12, 15 => (5, false, 8, 16)
  | 3, 12, 13, 14 => (10, true, 0, 3)
  | 3, 12, 13, 15 => (15, false, 8, 16)
  | 3, 12, 14, 15 => (15, false, 8, 17)
  | 3, 12, 15, 15 => (21, false, 0, 0)
  | 3, 13, 13, 14 => (17, false, 0, 0)
  | 3, 13, 13, 15 => (22, false, 0, 0)
  | 3, 13, 14, 14 => (17, false, 3, 6)
  | 3, 13, 14, 15 => (23, false, 0, 0)
  | 3, 13, 15, 15 => (26, false, 0, 0)
  | 3, 14, 14, 15 => (22, false, 0, 6)
  | 3, 14, 15, 15 => (26, false, 0, 6)
  | 3, 15, 15, 15 => (28, false, 0, 0)
  | 5, 5, 10, 10 => (0, false, 0, 2)
  | 5, 5, 10, 11 => (2, false, 0, 2)
  | 5, 5, 10, 14 => (2, false, 0, 12)
  | 5, 5, 10, 15 => (5, false, 0, 2)
  | 5, 5, 11, 11 => (5, true, 11, 16)
  | 5, 5, 11, 14 => (6, false, 0, 2)
  | 5, 5, 11, 15 => (12, false, 0, 2)
  | 5, 5, 14, 14 => (5, true, 10, 16)
  | 5, 5, 14, 15 => (12, false, 0, 12)
  | 5, 5, 15, 15 => (18, false, 0, 2)
  | 5, 6, 9, 10 => (1, false, 2, 3)
  | 5, 6, 9, 11 => (4, false, 2, 3)
  | 5, 6, 9, 14 => (4, false, 0, 12)
  | 5, 6, 9, 15 => (8, false, 2, 3)
  | 5, 6, 10, 11 => (4, false, 8, 9)
  | 5, 6, 10, 13 => (4, false, 6, 14)
  | 5, 6, 10, 15 => (8, false, 8, 9)
  | 5, 6, 11, 11 => (10, false, 0, 12)
  | 5, 6, 11, 12 => (3, false, 1, 12)
  | 5, 6, 11, 13 => (9, false, 1, 12)
  | 5, 6, 11, 14 => (9, false, 7, 14)
  | 5, 6, 11, 15 => (14, false, 0, 12)
  | 5, 6, 12, 15 => (7, false, 0, 12)
  | 5, 6, 13, 14 => (8, true, 18, 16)
  | 5, 6, 13, 15 => (13, false, 0, 12)
  | 5, 6, 14, 15 => (13, false, 6, 14)
  | 5, 6, 15, 15 => (19, false, 0, 12)
  | 5, 7, 9, 10 => (4, false, 13, 5)
  | 5, 7, 9, 11 => (8, true, 9, 10)
  | 5, 7, 9, 14 => (9, false, 2, 3)
  | 5, 7, 9, 15 => (13, false, 2, 3)
  | 5, 7, 10, 10 => (2, false, 16, 10)
  | 5, 7, 10, 11 => (11, false, 0, 2)
  | 5, 7, 10, 12 => (4, false, 19, 16)
  | 5, 7, 10, 13 => (10, true, 10, 15)
  | 5, 7, 10, 14 => (11, false, 16, 11)
  | 5, 7, 10, 15 => (15, false, 0, 2)
  | 5, 7, 11, 11 => (15, true, 21, 17)
  | 5, 7, 11, 12 => (9, false, 4, 13)
  | 5, 7, 11, 13 => (14, true, 11, 15)
  | 5, 7, 11, 14 => (16, false, 0, 2)
  | 5, 7, 11, 15 => (20, false, 0, 2)
  | 5, 7, 12, 14 => (8, true, 7, 10)
  | 5, 7, 12, 15 => (13, false, 2, 13)
  | 5, 7, 13, 14 => (14, true, 10, 21)
  | 5, 7, 13, 15 => (19, true, 10, 21)
  | 5, 7, 14, 14 => (15, true, 20, 17)
  | 5, 7, 14, 15 => (20, false, 0, 12)
  | 5, 7, 15, 15 => (25, false, 0, 2)
  | 5, 9, 10, 14 => (4, false, 8, 18)
  | 5, 9, 10, 15 => (8, false, 6, 5)
  | 5, 9, 11, 14 => (9, false, 6, 5)
  | 5, 9, 11, 15 => (13, false, 6, 5)
  | 5, 9, 14, 14 => (10, false, 0, 3)
  | 5, 9, 14, 15 => (14, false, 0, 3)
  | 5, 9, 15, 15 => (19, false, 0, 3)
  | 5, 10, 10, 13 => (2, false, 8, 20)
  | 5, 10, 10, 15 => (5, false, 8, 10)
  | 5, 10, 11, 12 => (4, false, 20, 23)
  | 5, 10, 11, 13 => (11, false, 4, 3)
  | 5, 10, 11, 14 => (10, true, 2, 3)
  | 5, 10, 11, 15 => (15, false, 8, 10)
  | 5, 10, 12, 15 => (8, false, 12, 16)
  | 5, 10, 13, 14 => (11, false, 2, 13)
  | 5, 10, 13, 15 => (15, false, 2, 3)
  | 5, 10, 14, 15 => (15, false, 8, 11)
  | 5, 10, 15, 15 => (21, false, 0, 2)
  | 5, 11, 11, 12 => (10, false, 4, 13)
  | 5, 11, 11, 13 => (15, true, 11, 9)
  | 5, 11, 11, 14 => (17, false, 0, 2)
  | 5, 11, 11, 15 => (22, false, 0, 2)
  | 5, 11, 12, 14 => (9, false, 13, 16)
  | 5, 11, 12, 15 => (14, false, 2, 13)
  | 5, 11, 13, 14 => (16, false, 2, 3)
  | 5, 11, 13, 15 => (20, false, 2, 3)
  | 5, 11, 14, 14 => (17, false, 3, 12)
  | 5, 11, 14, 15 => (23, false, 0, 2)
  | 5, 11, 15, 15 => (26, false, 0, 2)
  | 5, 12, 14, 15 => (13, false, 6, 16)
  | 5, 12, 15, 15 => (19, false, 0, 13)
  | 5, 13, 14, 14 => (15, true, 10, 17)
  | 5, 13, 14, 15 => (20, false, 0, 13)
  | 5, 13, 15, 15 => (25, false, 0, 3)
  | 5, 14, 14, 15 => (22, false, 0, 12)
  | 5, 14, 15, 15 => (26, false, 0, 12)
  | 5, 15, 15, 15 => (28, false, 0, 2)
  | 6, 6, 9, 9 => (0, false, 16, 4)
  | 6, 6, 9, 11 => (2, false, 0, 8)
  | 6, 6, 9, 13 => (2, false, 0, 14)
  | 6, 6, 9, 15 => (5, false, 0, 8)
  | 6, 6, 11, 11 => (5, true, 5, 16)
  | 6, 6, 11, 13 => (6, false, 0, 8)
  | 6, 6, 11, 15 => (12, false, 0, 8)
  | 6, 6, 13, 13 => (5, true, 4, 16)
  | 6, 6, 13, 15 => (12, false, 0, 14)
  | 6, 6, 15, 15 => (18, false, 0, 8)
  | 6, 7, 9, 9 => (2, false, 16, 4)
  | 6, 7, 9, 10 => (4, false, 19, 11)
  | 6, 7, 9, 11 => (11, false, 16, 4)
  | 6, 7, 9, 12 => (4, false, 19, 17)
  | 6, 7, 9, 13 => (11, false, 16, 5)
  | 6, 7, 9, 14 => (10, true, 4, 15)
  | 6, 7, 9, 15 => (15, false, 0, 8)
  | 6, 7, 10, 11 => (8, true, 3, 10)
  | 6, 7, 10, 13 => (9, false, 2, 9)
  | 6, 7, 10, 15 => (13, false, 2, 9)
  | 6, 7, 11, 11 => (15, true, 19, 17)
  | 6, 7, 11, 12 => (9, false, 4, 15)
  | 6, 7, 11, 13 => (16, false, 0, 8)
  | 6, 7, 11, 14 => (14, true, 5, 15)
  | 6, 7, 11, 15 => (20, false, 0, 8)
  | 6, 7, 12, 13 => (8, true, 1, 10)
  | 6, 7, 12, 15 => (13, false, 2, 15)
  | 6, 7, 13, 13 => (15, true, 18, 17)
  | 6, 7, 13, 14 => (14, true, 4, 15)
  | 6, 7, 13, 15 => (20, false, 0, 14)
  | 6, 7, 14, 15 => (19, true, 4, 21)
  | 6, 7, 15, 15 => (25, false, 0, 8)
  | 6, 9, 9, 14 => (2, false, 8, 18)
  | 6, 9, 9, 15 => (5, false, 8, 4)
  | 6, 9, 10, 13 => (4, false, 14, 20)
  | 6, 9, 10, 15 => (8, false, 12, 11)
  | 6, 9, 11, 12 => (4, false, 20, 22)
  | 6, 9, 11, 13 => (10, true, 8, 3)
  | 6, 9, 11, 14 => (11, false, 4, 9)
  | 6, 9, 11, 15 => (15, false, 8, 4)
  | 6, 9, 12, 15 => (8, false, 12, 17)
  | 6, 9, 13, 14 => (11, false, 4, 15)
  | 6, 9, 13, 15 => (15, false, 8, 5)
  | 6, 9, 14, 15 => (15, false, 2, 9)
  | 6, 9, 15, 15 => (21, false, 6, 4)
  | 6, 10, 11, 13 => (9, false, 6, 11)
  | 6, 10, 11, 15 => (13, false, 6, 11)
  | 6, 10, 13, 13 => (10, false, 0, 9)
  | 6, 10, 13, 15 => (14, false, 0, 9)
  | 6, 10, 15, 15 => (19, false, 0, 9)
  | 6, 11, 11, 12 => (10, false, 4, 15)
  | 6, 11, 11, 13 => (17, false, 0, 8)
  | 6, 11, 11, 14 => (15, true, 5, 9)
  | 6, 11, 11, 15 => (22, false, 0, 8)
  | 6, 11, 12, 13 => (9, false, 13, 17)
  | 6, 11, 12, 15 => (14, false, 2, 15)
  | 6, 11, 13, 13 => (17, false, 3, 14)
  | 6, 11, 13, 14 => (16, false, 4, 9)
  | 6, 11, 13, 15 => (23, false, 0, 8)
  | 6, 11, 14, 15 => (20, false, 2, 9)
  | 6, 11, 15, 15 => (26, false, 0, 8)
  | 6, 12, 13, 15 => (13, false, 6, 17)
  | 6, 12, 15, 15 => (19, false, 0, 15)
  | 6, 13, 13, 14 => (15, true, 4, 9)
  | 6, 13, 13, 15 => (22, false, 0, 14)
  | 6, 13, 14, 15 => (20, false, 2, 15)
  | 6, 13, 15, 15 => (26, false, 0, 14)
  | 6, 14, 15, 15 => (25, false, 0, 9)
  | 6, 15, 15, 15 => (28, false, 0, 8)
  | 7, 7, 9, 9 => (5, true, 9, 0)
  | 7, 7, 9, 10 => (10, false, 16, 18)
  | 7, 7, 9, 11 => (15, true, 15, 1)
  | 7, 7, 9, 12 => (10, false, 16, 19)
  | 7, 7, 9, 13 => (15, true, 9, 1)
  | 7, 7, 9, 14 => (17, false, 12, 4)
  | 7, 7, 9, 15 => (22, false, 12, 4)
  | 7, 7, 10, 10 => (5, true, 3, 0)
  | 7, 7, 10, 11 => (15, true, 13, 1)
  | 7, 7, 10, 12 => (10, false, 16, 21)
  | 7, 7, 10, 13 => (17, false, 12, 10)
  | 7, 7, 10, 14 => (15, true, 3, 1)
  | 7, 7, 10, 15 => (22, false, 12, 10)
  | 7, 7, 11, 11 => (21, true, 16, 0)
  | 7, 7, 11, 12 => (17, false, 18, 16)
  | 7, 7, 11, 13 => (23, true, 21, 16)
  | 7, 7, 11, 14 => (23, true, 19, 16)
  | 7, 7, 11, 15 => (26, true, 22, 22)
  | 7, 7, 12, 12 => (5, true, 1, 0)
  | 7, 7, 12, 13 => (15, true, 7, 1)
  | 7, 7, 12, 14 => (15, true, 1, 1)
  | 7, 7, 12, 15 => (22, false, 12, 16)
  | 7, 7, 13, 13 => (21, true, 10, 0)
  | 7, 7, 13, 14 => (23, true, 18, 16)
  | 7, 7, 13, 15 => (26, true, 20, 22)
  | 7, 7, 14, 14 => (21, true, 4, 0)
  | 7, 7, 14, 15 => (26, true, 18, 22)
  | 7, 7, 15, 15 => (28, true, 18, 16)
  | 7, 9, 9, 14 => (6, false, 8, 4)
  | 7, 9, 9, 15 => (12, false, 8, 4)
  | 7, 9, 10, 12 => (3, false, 9, 18)
  | 7, 9, 10, 13 => (9, false, 9, 18)
  | 7, 9, 10, 14 => (9, false, 15, 20)
  | 7, 9, 10, 15 => (14, false, 8, 18)
  | 7, 9, 11, 12 => (9, false, 11, 19)
  | 7, 9, 11, 13 => (14, true, 9, 3)
  | 7, 9, 11, 14 => (16, false, 8, 4)
  | 7, 9, 11, 15 => (20, false, 8, 4)
  | 7, 9, 12, 14 => (9, false, 15, 22)
  | 7, 9, 12, 15 => (14, false, 8, 19)
  | 7, 9, 13, 14 => (16, false, 8, 5)
  | 7, 9, 13, 15 => (20, false, 8, 5)
  | 7, 9, 14, 14 => (17, false, 9, 18)
  | 7, 9, 14, 15 => (23, false, 6, 4)
  | 7, 9, 15, 15 => (26, false, 6, 4)
  | 7, 10, 10, 13 => (6, false, 8, 10)
  | 7, 10, 10, 15 => (12, false, 8, 10)
  | 7, 10, 11, 12 => (9, false, 11, 21)
  | 7, 10, 11, 13 => (16, false, 8, 10)
  | 7, 10, 11, 14 => (14, true, 3, 3)
  | 7, 10, 11, 15 => (20, false, 8, 10)
  | 7, 10, 12, 13 => (9, false, 15, 23)
  | 7, 10, 12, 15 => (14, false, 8, 21)
  | 7, 10, 13, 13 => (17, false, 9, 20)
  | 7, 10, 13, 14 => (16, false, 10, 11)
  | 7, 10, 13, 15 => (23, false, 6, 10)
  | 7, 10, 14, 15 => (20, false, 8, 11)
  | 7, 10, 15, 15 => (26, false, 6, 10)
  | 7, 11, 11, 12 => (17, false, 21, 22)
  | 7, 11, 11, 13 => (23, true, 15, 4)
  | 7, 11, 11, 14 => (23, true, 13, 4)
  | 7, 11, 11, 15 => (26, true, 16, 18)
  | 7, 11, 12, 12 => (6, false, 16, 16)
  | 7, 11, 12, 13 => (16, false, 16, 16)
  | 7, 11, 12, 14 => (16, false, 16, 17)
  | 7, 11, 12, 15 => (23, false, 12, 16)
  | 7, 11, 13, 13 => (23, true, 9, 0)
  | 7, 11, 13, 14 => (24, false, 0, 0)
  | 7, 11, 13, 15 => (27, false, 0, 0)
  | 7, 11, 14, 14 => (23, true, 3, 0)
  | 7, 11, 14, 15 => (27, false, 0, 6)
  | 7, 11, 15, 15 => (29, false, 0, 0)
  | 7, 12, 12, 15 => (12, false, 8, 16)
  | 7, 12, 13, 14 => (14, true, 1, 3)
  | 7, 12, 13, 15 => (20, false, 8, 16)
  | 7, 12, 14, 15 => (20, false, 8, 17)
  | 7, 12, 15, 15 => (26, false, 6, 16)
  | 7, 13, 13, 14 => (23, true, 7, 4)
  | 7, 13, 13, 15 => (26, true, 10, 18)
  | 7, 13, 14, 14 => (23, true, 1, 0)
  | 7, 13, 14, 15 => (27, false, 0, 12)
  | 7, 13, 15, 15 => (29, false, 0, 2)
  | 7, 14, 14, 15 => (26, true, 4, 18)
  | 7, 14, 15, 15 => (29, false, 0, 8)
  | 7, 15, 15, 15 => (30, false, 0, 0)
  | 9, 9, 14, 14 => (5, true, 8, 16)
  | 9, 9, 14, 15 => (12, false, 0, 18)
  | 9, 9, 15, 15 => (18, false, 0, 4)
  | 9, 10, 12, 15 => (7, false, 0, 18)
  | 9, 10, 13, 14 => (8, true, 12, 16)
  | 9, 10, 13, 15 => (13, false, 0, 18)
  | 9, 10, 14, 15 => (13, false, 6, 20)
  | 9, 10, 15, 15 => (19, false, 0, 18)
  | 9, 11, 12, 14 => (8, true, 6, 10)
  | 9, 11, 12, 15 => (13, false, 2, 19)
  | 9, 11, 13, 14 => (14, true, 8, 21)
  | 9, 11, 13, 15 => (19, true, 8, 21)
  | 9, 11, 14, 14 => (15, true, 14, 17)
  | 9, 11, 14, 15 => (20, false, 0, 18)
  | 9, 11, 15, 15 => (25, false, 0, 4)
  | 9, 12, 14, 15 => (13, false, 6, 22)
  | 9, 12, 15, 15 => (19, false, 0, 19)
  | 9, 13, 14, 14 => (15, true, 8, 17)
  | 9, 13, 14, 15 => (20, false, 0, 19)
  | 9, 13, 15, 15 => (25, false, 0, 5)
  | 9, 14, 14, 15 => (22, false, 0, 18)
  | 9, 14, 15, 15 => (26, false, 0, 18)
  | 9, 15, 15, 15 => (28, false, 0, 4)
  | 10, 10, 13, 13 => (5, true, 2, 16)
  | 10, 10, 13, 15 => (12, false, 0, 20)
  | 10, 10, 15, 15 => (18, false, 0, 10)
  | 10, 11, 12, 13 => (8, true, 0, 10)
  | 10, 11, 12, 15 => (13, false, 2, 21)
  | 10, 11, 13, 13 => (15, true, 12, 17)
  | 10, 11, 13, 14 => (14, true, 2, 15)
  | 10, 11, 13, 15 => (20, false, 0, 20)
  | 10, 11, 14, 15 => (19, true, 2, 21)
  | 10, 11, 15, 15 => (25, false, 0, 10)
  | 10, 12, 13, 15 => (13, false, 6, 23)
  | 10, 12, 15, 15 => (19, false, 0, 21)
  | 10, 13, 13, 14 => (15, true, 2, 9)
  | 10, 13, 13, 15 => (22, false, 0, 20)
  | 10, 13, 14, 15 => (20, false, 2, 21)
  | 10, 13, 15, 15 => (26, false, 0, 20)
  | 10, 14, 15, 15 => (25, false, 0, 11)
  | 10, 15, 15, 15 => (28, false, 0, 10)
  | 11, 11, 12, 12 => (5, true, 0, 0)
  | 11, 11, 12, 13 => (15, true, 6, 1)
  | 11, 11, 12, 14 => (15, true, 0, 1)
  | 11, 11, 12, 15 => (22, false, 12, 22)
  | 11, 11, 13, 13 => (21, true, 8, 0)
  | 11, 11, 13, 14 => (23, true, 12, 16)
  | 11, 11, 13, 15 => (26, true, 14, 22)
  | 11, 11, 14, 14 => (21, true, 2, 0)
  | 11, 11, 14, 15 => (26, true, 12, 22)
  | 11, 11, 15, 15 => (28, true, 12, 16)
  | 11, 12, 12, 15 => (12, false, 8, 22)
  | 11, 12, 13, 14 => (14, true, 0, 3)
  | 11, 12, 13, 15 => (20, false, 8, 22)
  | 11, 12, 14, 15 => (20, false, 8, 23)
  | 11, 12, 15, 15 => (26, false, 6, 22)
  | 11, 13, 13, 14 => (23, true, 6, 4)
  | 11, 13, 13, 15 => (26, true, 8, 18)
  | 11, 13, 14, 14 => (23, true, 0, 0)
  | 11, 13, 14, 15 => (27, false, 0, 18)
  | 11, 13, 15, 15 => (29, false, 0, 4)
  | 11, 14, 14, 15 => (26, true, 2, 18)
  | 11, 14, 15, 15 => (29, false, 0, 10)
  | 11, 15, 15, 15 => (30, false, 0, 1)
  | 12, 12, 15, 15 => (18, false, 0, 16)
  | 12, 13, 14, 15 => (19, true, 0, 21)
  | 12, 13, 15, 15 => (25, false, 0, 16)
  | 12, 14, 15, 15 => (25, false, 0, 17)
  | 12, 15, 15, 15 => (28, false, 0, 16)
  | 13, 13, 14, 14 => (21, true, 0, 0)
  | 13, 13, 14, 15 => (26, true, 6, 22)
  | 13, 13, 15, 15 => (28, true, 6, 16)
  | 13, 14, 14, 15 => (26, true, 0, 18)
  | 13, 14, 15, 15 => (29, false, 0, 16)
  | 13, 15, 15, 15 => (30, false, 0, 3)
  | 14, 14, 15, 15 => (28, true, 0, 16)
  | 14, 15, 15, 15 => (30, false, 0, 9)
  | 15, 15, 15, 15 => (31, false, 0, 0)
  | _, _, _, _ => (0, false, 0, 0)

def permuted (r : Rows) (flip : Bool) (p q : Fin 24) (i j : Fin 4) : Bool :=
  if flip then bit r (permutation q j) (permutation p i)
  else bit r (permutation p i) (permutation q j)

def Correct (r : Rows) (c : Certificate) : Prop :=
  ∀ i j : Fin 4, bit (representative c.1) i j = permuted r c.2.1 c.2.2.1 c.2.2.2 i j
instance (r : Rows) (c : Certificate) : Decidable (Correct r c) :=
  inferInstanceAs (Decidable (∀ i j : Fin 4, _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_0 : ∀ b c d : Fin 16,
    Sorted ![0,b,c,d] → Good ![0,b,c,d] →
      Correct ![0,b,c,d] (certificate ![0,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_1 : ∀ b c d : Fin 16,
    Sorted ![1,b,c,d] → Good ![1,b,c,d] →
      Correct ![1,b,c,d] (certificate ![1,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_2 : ∀ b c d : Fin 16,
    Sorted ![2,b,c,d] → Good ![2,b,c,d] →
      Correct ![2,b,c,d] (certificate ![2,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_3 : ∀ b c d : Fin 16,
    Sorted ![3,b,c,d] → Good ![3,b,c,d] →
      Correct ![3,b,c,d] (certificate ![3,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_4 : ∀ b c d : Fin 16,
    Sorted ![4,b,c,d] → Good ![4,b,c,d] →
      Correct ![4,b,c,d] (certificate ![4,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_5 : ∀ b c d : Fin 16,
    Sorted ![5,b,c,d] → Good ![5,b,c,d] →
      Correct ![5,b,c,d] (certificate ![5,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_6 : ∀ b c d : Fin 16,
    Sorted ![6,b,c,d] → Good ![6,b,c,d] →
      Correct ![6,b,c,d] (certificate ![6,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_7 : ∀ b c d : Fin 16,
    Sorted ![7,b,c,d] → Good ![7,b,c,d] →
      Correct ![7,b,c,d] (certificate ![7,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_8 : ∀ b c d : Fin 16,
    Sorted ![8,b,c,d] → Good ![8,b,c,d] →
      Correct ![8,b,c,d] (certificate ![8,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_9 : ∀ b c d : Fin 16,
    Sorted ![9,b,c,d] → Good ![9,b,c,d] →
      Correct ![9,b,c,d] (certificate ![9,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_10 : ∀ b c d : Fin 16,
    Sorted ![10,b,c,d] → Good ![10,b,c,d] →
      Correct ![10,b,c,d] (certificate ![10,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_11 : ∀ b c d : Fin 16,
    Sorted ![11,b,c,d] → Good ![11,b,c,d] →
      Correct ![11,b,c,d] (certificate ![11,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_12 : ∀ b c d : Fin 16,
    Sorted ![12,b,c,d] → Good ![12,b,c,d] →
      Correct ![12,b,c,d] (certificate ![12,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_13 : ∀ b c d : Fin 16,
    Sorted ![13,b,c,d] → Good ![13,b,c,d] →
      Correct ![13,b,c,d] (certificate ![13,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_14 : ∀ b c d : Fin 16,
    Sorted ![14,b,c,d] → Good ![14,b,c,d] →
      Correct ![14,b,c,d] (certificate ![14,b,c,d]) := by
  intro b
  fin_cases b <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma certificate_correct_15 : ∀ b c d : Fin 16,
    Sorted ![15,b,c,d] → Good ![15,b,c,d] →
      Correct ![15,b,c,d] (certificate ![15,b,c,d]) := by
  intro b
  fin_cases b <;> decide

lemma certificate_correct : ∀ r : Rows, Sorted r → Good r → Correct r (certificate r) := by
  have ht : ∀ a b c d : Fin 16, Sorted ![a,b,c,d] → Good ![a,b,c,d] →
      Correct ![a,b,c,d] (certificate ![a,b,c,d]) := by
    intro a
    fin_cases a
    · exact certificate_correct_0
    · exact certificate_correct_1
    · exact certificate_correct_2
    · exact certificate_correct_3
    · exact certificate_correct_4
    · exact certificate_correct_5
    · exact certificate_correct_6
    · exact certificate_correct_7
    · exact certificate_correct_8
    · exact certificate_correct_9
    · exact certificate_correct_10
    · exact certificate_correct_11
    · exact certificate_correct_12
    · exact certificate_correct_13
    · exact certificate_correct_14
    · exact certificate_correct_15
  intro r hs hg
  have hr : r = ![r 0,r 1,r 2,r 3] := by ext i; fin_cases i <;> rfl
  rw [hr] at hs hg ⊢
  exact ht _ _ _ _ hs hg

#print axioms certificate_correct
end Erdos713EightCore
