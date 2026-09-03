import Submission.TriangleHit

/-!
An exact finite obstruction to a convex strengthening of triangle-hitting:
the K4-free Paley graph on 17 vertices has no unit-vector assignment for
which every triangle has sum of pairwise inner products at most -1.
This does not settle Erdős 595 or obstruct the weaker minimum-edge condition.
-/

open SimpleGraph Set
open scoped BigOperators

namespace Erdos595Paley

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def adjacent (a b : Fin 17) : Prop :=
  (a.val + 17 - b.val) % 17 ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)

instance : DecidableRel adjacent := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))

private theorem adj_symm : ∀ a b, adjacent a b → adjacent b a := by decide +kernel
private theorem adj_irrefl : ∀ a, ¬adjacent a a := by decide +kernel

def G : SimpleGraph (Fin 17) where
  Adj := adjacent
  symm := fun a b h => adj_symm a b h
  loopless := adj_irrefl

private theorem no_four_0 : ∀ b c d : Fin 17,
    ¬(adjacent 0 b ∧ adjacent 0 c ∧ adjacent 0 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_1 : ∀ b c d : Fin 17,
    ¬(adjacent 1 b ∧ adjacent 1 c ∧ adjacent 1 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_2 : ∀ b c d : Fin 17,
    ¬(adjacent 2 b ∧ adjacent 2 c ∧ adjacent 2 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_3 : ∀ b c d : Fin 17,
    ¬(adjacent 3 b ∧ adjacent 3 c ∧ adjacent 3 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_4 : ∀ b c d : Fin 17,
    ¬(adjacent 4 b ∧ adjacent 4 c ∧ adjacent 4 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_5 : ∀ b c d : Fin 17,
    ¬(adjacent 5 b ∧ adjacent 5 c ∧ adjacent 5 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_6 : ∀ b c d : Fin 17,
    ¬(adjacent 6 b ∧ adjacent 6 c ∧ adjacent 6 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_7 : ∀ b c d : Fin 17,
    ¬(adjacent 7 b ∧ adjacent 7 c ∧ adjacent 7 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_8 : ∀ b c d : Fin 17,
    ¬(adjacent 8 b ∧ adjacent 8 c ∧ adjacent 8 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_9 : ∀ b c d : Fin 17,
    ¬(adjacent 9 b ∧ adjacent 9 c ∧ adjacent 9 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_10 : ∀ b c d : Fin 17,
    ¬(adjacent 10 b ∧ adjacent 10 c ∧ adjacent 10 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_11 : ∀ b c d : Fin 17,
    ¬(adjacent 11 b ∧ adjacent 11 c ∧ adjacent 11 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_12 : ∀ b c d : Fin 17,
    ¬(adjacent 12 b ∧ adjacent 12 c ∧ adjacent 12 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_13 : ∀ b c d : Fin 17,
    ¬(adjacent 13 b ∧ adjacent 13 c ∧ adjacent 13 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_14 : ∀ b c d : Fin 17,
    ¬(adjacent 14 b ∧ adjacent 14 c ∧ adjacent 14 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_15 : ∀ b c d : Fin 17,
    ¬(adjacent 15 b ∧ adjacent 15 c ∧ adjacent 15 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four_16 : ∀ b c d : Fin 17,
    ¬(adjacent 16 b ∧ adjacent 16 c ∧ adjacent 16 d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel

private theorem no_four : ∀ a b c d : Fin 17,
    ¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by
  intro a
  fin_cases a
  · exact no_four_0
  · exact no_four_1
  · exact no_four_2
  · exact no_four_3
  · exact no_four_4
  · exact no_four_5
  · exact no_four_6
  · exact no_four_7
  · exact no_four_8
  · exact no_four_9
  · exact no_four_10
  · exact no_four_11
  · exact no_four_12
  · exact no_four_13
  · exact no_four_14
  · exact no_four_15
  · exact no_four_16

#check no_four
end Erdos595Paley
