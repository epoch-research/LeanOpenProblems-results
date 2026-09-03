import FormalConjecturesUtil

/-!
A failed encoding candidate, not a disproof of the conjecture.

These four monic polynomials have all lower coefficients divisible by 3,
and their constant coefficients are 3 modulo 9. Their norm-sum difference
is a nonzero polynomial, but it vanishes at the proposed integer base 27.
-/

namespace Erdos773

lemma eisenstein_encoding_identity (X : ℤ) :
    (X ^ 3 + 3 * X ^ 2 + 12 * X + 21) ^ 2 +
      (X ^ 3 + 15 * X ^ 2 + 12) ^ 2 -
      (X ^ 3 + 12 * X ^ 2 + 15 * X + 21) ^ 2 -
      (X ^ 3 + 6 * X ^ 2 + 15 * X + 12) ^ 2 =
      18 * X * (X - 27) * (X ^ 2 + X + 1) := by ring

lemma eisenstein_encoding_collision :
    (22215 : ℕ) ^ 2 + 30630 ^ 2 = 28857 ^ 2 + 24474 ^ 2 := by norm_num

lemma eisenstein_encoding_not_sidon :
    ¬ IsSidon ({22215 ^ 2, 30630 ^ 2, 28857 ^ 2, 24474 ^ 2} : Set ℕ) := by
  intro h
  have he := h (22215 ^ 2) (by simp) (28857 ^ 2) (by simp)
    (30630 ^ 2) (by simp) (24474 ^ 2) (by simp) eisenstein_encoding_collision
  norm_num at he

#print axioms eisenstein_encoding_not_sidon

end Erdos773
