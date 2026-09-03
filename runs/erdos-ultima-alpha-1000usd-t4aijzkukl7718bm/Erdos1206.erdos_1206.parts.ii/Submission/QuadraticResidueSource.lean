import FormalConjecturesUtil

/-!
An exact counterexample to one arithmetic-symbol candidate, not to the
positive-density Sidon conjecture.
-/

namespace Erdos1206.QuadraticResidueSource

/-- Numbers with a prime factor larger than their cofactor, for which that
cofactor is a quadratic nonresidue. Since the modulus is prime, the Jacobi
symbol here is the Legendre symbol. -/
def nonresidueSource : Set ℕ :=
  {n | ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ m < p ∧ n = p*m ∧
    jacobiSym (m : ℤ) p = -1}

lemma arithmetic_certificate :
    Nat.Prime 35977 ∧
    jacobiSym 26711 35977 = -1 ∧
    jacobiSym 31469 35977 = -1 ∧
    jacobiSym 32009 35977 = -1 ∧
    jacobiSym 35543 35977 = -1 := by
  norm_num

lemma counterexample_membership :
    960981647 ∈ nonresidueSource ∧
    1132160213 ∈ nonresidueSource ∧
    1151587793 ∈ nonresidueSource ∧
    1278730511 ∈ nonresidueSource := by
  obtain ⟨hp,h₁,h₂,h₃,h₄⟩ := arithmetic_certificate
  refine ⟨?_,?_,?_,?_⟩
  · exact ⟨35977,26711,hp,by norm_num,by norm_num,by norm_num,h₁⟩
  · exact ⟨35977,31469,hp,by norm_num,by norm_num,by norm_num,h₂⟩
  · exact ⟨35977,32009,hp,by norm_num,by norm_num,by norm_num,h₃⟩
  · exact ⟨35977,35543,hp,by norm_num,by norm_num,by norm_num,h₄⟩

/-- This particular nonperiodic source is not already cube-Sidon. The theorem
does not exclude Sidon subsets of it and makes no density assertion. -/
theorem nonresidueSource_not_cubeSidon :
    ¬ IsSidon ((fun n : ℕ => n^3) '' nonresidueSource) := by
  intro h
  obtain ⟨h₁,h₂,h₃,h₄⟩ := counterexample_membership
  have he : (960981647 : ℕ)^3 + 1278730511^3 =
      1132160213^3 + 1151587793^3 := by norm_num
  have hh := h _ ⟨960981647,h₁,rfl⟩ _ ⟨1132160213,h₂,rfl⟩
    _ ⟨1278730511,h₄,rfl⟩ _ ⟨1151587793,h₃,rfl⟩ he
  norm_num at hh

#print axioms arithmetic_certificate
#print axioms nonresidueSource_not_cubeSidon
end Erdos1206.QuadraticResidueSource
