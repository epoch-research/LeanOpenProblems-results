import FormalConjecturesUtil

/-! A nonnegative quadratic coverage energy. This is a generic finite lemma,
not a claim that a zero-energy odd covering has been found. -/
namespace Erdos7PairCoverEnergy
open scoped BigOperators
set_option autoImplicit false

lemma nat_energy_nonneg (k : ℕ) : 0 ≤ ((k : ℚ)-1)*((k : ℚ)-2)/2 := by
  rcases k with _ | k
  · norm_num
  rcases k with _ | k
  · norm_num
  have hk : (2 : ℚ) ≤ ((k+1+1 : ℕ) : ℚ) := by exact_mod_cast (show 2 ≤ k+1+1 by omega)
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)

/-- Any zero value of the quadratic lies at count1 or count2. -/
lemma energy_eq_zero (k : ℕ) : ((k : ℚ)-1)*((k : ℚ)-2)/2=0 ↔ k=1 ∨ k=2 := by
  constructor
  · intro h
    have hmul : ((k : ℚ)-1)*((k : ℚ)-2)=0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h
    · left; exact_mod_cast (show (k : ℚ)=1 by linarith)
    · right; exact_mod_cast (show (k : ℚ)=2 by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Positive weights and zero total energy force coverage at every point. -/
theorem zero_energy_cover {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (hw : ∀ x, 0 < w x) (K : Ω → ℕ)
    (hz : (∑ x, w x*(((K x : ℚ)-1)*((K x : ℚ)-2)/2))=0) :
    ∀ x, K x=1 ∨ K x=2 := by
  intro x
  have hn : ∀ x : Ω, 0 ≤ w x*(((K x : ℚ)-1)*((K x : ℚ)-2)/2) :=
    fun x => mul_nonneg (hw x).le (nat_energy_nonneg _)
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hn x)).mp hz x (Finset.mem_univ _)
  apply (energy_eq_zero (K x)).mp
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hw x))

#print axioms nat_energy_nonneg
#print axioms zero_energy_cover
end Erdos7PairCoverEnergy
