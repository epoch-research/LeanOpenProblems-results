import Submission.CompetingCoverVariance
import Submission.StretchedQuadraticVoid
import Submission.PrimeCountingLower

/-!
The exceptional singleton-survivor probability is also stretched-exponentially
small at quadratic scale. A fresh prime larger than the interval converts a
singleton into a full cover with probability exactly 1/p. This is a probability
bound, not a worst-case quadratic Jacobsthal theorem.
-/
namespace Erdos970.CoverFibers
open Finset Real Erdos970.GapAverages

lemma concentrated_iff_singleton_of_large (U : Finset ℕ) (m p : ℕ)
    (hUm : U ⊆ range m) (hmp : m ≤ p) : Concentrated U p ↔ U.card = 1 := by
  constructor
  · intro hc
    have hle : U.card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      exact (show x ≡ y [MOD p] from hc.2 x hx y hy).eq_of_lt_of_lt
        ((mem_range.mp (hUm hx)).trans_le hmp) ((mem_range.mp (hUm hy)).trans_le hmp)
    have hpos := card_pos.mpr hc.1
    omega
  · exact fun hc => concentrated_of_card_one U hc p

lemma concentratedFraction_eq_singleton (P : Finset ℕ) (p m : ℕ) (hmp : m ≤ p) :
    concentratedFraction P p m = singletonFraction P m := by
  classical
  unfold concentratedFraction singletonFraction
  congr 1
  funext r
  simp only [concentrated_iff_singleton_of_large (phaseSurvivors P m r) m p
    (filter_subset _ _) hmp]

/-- Any large fresh prime converts singleton phases into covers with exact
conditional probability 1/p. Dropping the old cover term gives this bound. -/
theorem singletonFraction_le_new_cover (P : Finset ℕ) (p m : ℕ)
    (hp0 : 0 < p) (hp : p ∉ P) (hmp : m ≤ p) :
    singletonFraction P m ≤ (p : ℝ) * coveredFraction (insert p P) m := by
  have he := coveredFraction_insert P p hp0 hp m
  rw [concentratedFraction_eq_singleton P p m hmp] at he
  have h0 : 0 ≤ coveredFraction P m := by
    unfold coveredFraction phaseMean
    apply div_nonneg
    · exact sum_nonneg (fun r _ => by split_ifs <;> norm_num)
    · positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hh : singletonFraction P m / p ≤ coveredFraction (insert p P) m := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hpR).mp hh

/-- Polynomially bounded supply of a fresh prime at least m. -/
lemma exists_bounded_fresh_prime (P : Finset ℕ) (k m : ℕ) (hPk : P.card ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ∉ P ∧ m ≤ p ∧ p ≤ 256 * (m + k + 1) ^ 2 := by
  classical
  let f : ℕ → ℕ := fun i => Nat.nth Nat.Prime (m + i)
  have hi : Function.Injective f := by
    intro a b hab
    have he := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
    omega
  have hex : ∃ i ∈ range (k + 1), f i ∉ P := by
    by_contra h
    push_neg at h
    have hs : (range (k + 1)).image f ⊆ P := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact h i hi
    have hc := card_le_card hs
    rw [card_image_of_injective _ hi, card_range] at hc
    omega
  obtain ⟨i, hi, hip⟩ := hex
  have hik := mem_range.mp hi
  refine ⟨f i, Nat.prime_nth_prime _, hip, ?_, ?_⟩
  · have hh := Nat.add_two_le_nth_prime (m + i)
    dsimp [f]
    omega
  · have hb : f i ≤ 256 * (m + i + 1) ^ 2 := by
      exact_mod_cast PrimeCountingLower.nth_prime_quadratic (m + i)
    exact hb.trans (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (by omega) 2))

/-- One spare prime in the existing stretched void estimate suffices to
control singleton phases, at the cost of an explicit polynomial prefactor. -/
theorem singletonFraction_quadratic_stretched (k : ℕ)
    (hk : exposureThreshold ^ 16 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPk : P.card + 1 ≤ k) :
    singletonFraction P (k ^ 2) ≤
      (256 * (k ^ 2 + k + 1) ^ 2 : ℕ) *
        exp (-((k : ℝ) ^ ((3 : ℝ) / 4) / 32)) := by
  obtain ⟨p, hpp, hpP, hkp, hcap⟩ := exists_bounded_fresh_prime P k (k ^ 2) (by omega)
  have hPp : ∀ q ∈ insert p P, q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hpp
    · exact hP q hq
  have hcard : (insert p P).card ≤ k := by rw [card_insert_of_notMem hpP]; exact hPk
  calc
    _ ≤ (p : ℝ) * coveredFraction (insert p P) (k ^ 2) :=
      singletonFraction_le_new_cover P p (k ^ 2) hpp.pos hpP hkp
    _ ≤ (p : ℝ) * exp (-((k : ℝ) ^ ((3 : ℝ) / 4) / 32)) :=
      mul_le_mul_of_nonneg_left (coveredFraction_quadratic_stretched k hk
        (insert p P) hPp hcard) (Nat.cast_nonneg p)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) (exp_pos _).le

/-- The aggregate variance bound with its singleton exception explicitly
controlled. It remains an averaged estimate over candidate primes. -/
theorem competing_concentration_quadratic (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (k : ℕ)
    (hk : exposureThreshold ^ 16 ≤ k) (hPk : P.card + 1 ≤ k)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → k ^ 2 ≤ p * q)
    (hsize : ∀ p ∈ R, ((k ^ 2 : ℕ) : ℝ) / p + 1 ≤
      ((k ^ 2 : ℕ) : ℝ) * density P / 2) :
    (∑ p ∈ R, concentratedFraction P p (k ^ 2)) ≤
      4 * (1 - density P) / (((k ^ 2 : ℕ) : ℝ) * density P) +
      (R.card : ℝ) * ((256 * (k ^ 2 + k + 1) ^ 2 : ℕ) *
        exp (-((k : ℝ) ^ ((3 : ℝ) / 4) / 32))) := by
  have hk0 : 0 < k := by omega
  have h := concentratedFraction_sum_le_half_mean P R hP hR (k ^ 2)
    (Nat.pow_pos hk0) hprod hsize
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (singletonFraction_quadratic_stretched k hk P hP hPk) (Nat.cast_nonneg R.card)))

#print axioms singletonFraction_le_new_cover
#print axioms exists_bounded_fresh_prime
#print axioms singletonFraction_quadratic_stretched
#print axioms competing_concentration_quadratic
end Erdos970.CoverFibers
