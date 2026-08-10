import FormalConjectures.Util.ProblemImports

open Finset Nat

-- Finite residue fact: every quadruple mod 16 with square sum 14 can be transformed
-- by signed permutation or one Hadamard step to target residues mod 8. This ignores positivity.
example (a b c d : ZMod 16)
    (h : a^2 + b^2 + c^2 + d^2 = (14 : ZMod 16)) :
    ∃ A B C D : ZMod 16,
      A^2 + B^2 + C^2 + D^2 = (14 : ZMod 16) ∧
      ((A : ZMod 8) = 0 ∧ (B : ZMod 8) = 1 ∧ (C : ZMod 8) = 6 ∧ (D : ZMod 8) = 5) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num at h ⊢
