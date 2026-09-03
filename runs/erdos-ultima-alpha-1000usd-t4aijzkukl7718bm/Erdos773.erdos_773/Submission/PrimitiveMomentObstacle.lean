import FormalConjecturesUtil

/-!
A primitive collision in a single class of the first three binary digit moments.
This rules out repairing that particular construction merely by excluding
quadruples with a nontrivial common divisor. It is not a disproof of Erdős 773.

The construction combines two points in the same rational rotation plane:
  (3,11,7,9) and (1,21,9,19).
Multiplication by suitably chosen Mersenne numbers equalizes digit moments;
coprime choices of their exponents allow the combined quadruple to be primitive.
-/

namespace Erdos773

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

lemma common_rotation_plane_identity (u v : ℤ) :
    (3 * u + v) ^ 2 + (11 * u + 21 * v) ^ 2 =
      (7 * u + 9 * v) ^ 2 + (9 * u + 19 * v) ^ 2 := by
  ring

private def binaryMoment120 (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 120, if n.testBit j then j ^ k else 0

lemma primitive_three_binary_moment_collision :
    ∃ a b c d : ℕ,
      0 < a ∧ a < c ∧ a < d ∧
      Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 ∧
      a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 ∧
      (∀ n ∈ ({a, b, c, d} : Finset ℕ),
        (binaryMoment120 n 0, binaryMoment120 n 1, binaryMoment120 n 2) =
          (60, 3443, 266793)) ∧
      ¬ IsSidon ({a ^ 2, b ^ 2, c ^ 2, d ^ 2} : Set ℕ) := by
  let a : ℕ := 30165485455999515870343350773219455
  let b : ℕ := 110606780005331597846652322470038123
  let c : ℕ := 70386132730665552282875524740678775
  let d : ℕ := 90496456367998584216008547367258477
  refine ⟨a, b, c, d, by norm_num [a], by norm_num [a, c],
    by norm_num [a, d], ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [a, b, c, d]
  · decide
  · intro h
    have he := h (a ^ 2) (by simp) (c ^ 2) (by simp)
      (b ^ 2) (by simp) (d ^ 2) (by norm_num [a, b, c, d])
    norm_num [a, b, c, d] at he

#print axioms primitive_three_binary_moment_collision

end Erdos773
