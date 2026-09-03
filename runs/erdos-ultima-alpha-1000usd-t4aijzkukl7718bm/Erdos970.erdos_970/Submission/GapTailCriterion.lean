import Submission.GapPhaseMoments

/-! A conditional bridge from phase tail estimates to worst-case interval bounds.
No exponential tail estimate is proved or assumed as an axiom in this file. -/
namespace Erdos970.GapAverages
open Finset Real

lemma point_zero_of_hit (P : Finset ℕ) (x : ℕ) (r : Phase P)
    (p : P) (hp : x % p.val = (r p).val) : point P x r = 0 := by
  classical
  unfold point
  apply prod_eq_zero (mem_univ p)
  simp [hp]

lemma count_zero_of_cover (P : Finset ℕ) (m : ℕ) (r : Phase P)
    (h : ∀ x < m, ∃ p : P, x % p.val = (r p).val) :
    intervalCount P m r = 0 := by
  apply sum_eq_zero
  intro x hx
  obtain ⟨p, hp⟩ := h x (mem_range.mp hx)
  exact point_zero_of_hit P x r p hp

/-- One exceptional phase already has mass equal to the reciprocal prime product. -/
lemma reciprocal_le_coveredFraction {P : Finset ℕ} {m : ℕ} {r : Phase P}
    (hr : intervalCount P m r = 0) :
    1 / (∏ p : P, (p.val : ℝ)) ≤ coveredFraction P m := by
  classical
  have hsum : (1 : ℝ) ≤ ∑ s : Phase P, if intervalCount P m s = 0 then 1 else 0 := by
    have hh := single_le_sum
      (s := (univ : Finset (Phase P)))
      (f := fun s => if intervalCount P m s = 0 then (1 : ℝ) else 0)
      (fun s _ => by dsimp only; split_ifs <;> norm_num) (mem_univ r)
    simpa only [hr, if_true] using hh
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- The logarithm of the phase-space cardinality is the sum of log primes. -/
lemma log_phase_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    log (∏ p : P, (p.val : ℝ)) = ∑ p ∈ P, log (p : ℝ) := by
  rw [log_prod (fun p _ => by exact_mod_cast (hP p.val p.property).ne_zero)]
  exact sum_attach P (fun p : ℕ => log (p : ℝ))

/-- If a cover exists, any exponential tail exponent is bounded by the
logarithm of the phase-space size. The tail estimate is an explicit hypothesis. -/
theorem exponent_le_log_product_of_cover {P : Finset ℕ} {m : ℕ} {b : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (htail : coveredFraction P m ≤ exp (-b))
    (r : Phase P) (hr : intervalCount P m r = 0) :
    b ≤ ∑ p ∈ P, log (p : ℝ) := by
  have hN : 0 < ∏ p : P, (p.val : ℝ) := prod_pos
    (fun p _ => by exact_mod_cast (hP p.val p.property).pos)
  have hh := (reciprocal_le_coveredFraction hr).trans htail
  have hl := log_le_log (by positivity : 0 < 1 / ∏ p : P, (p.val : ℝ)) hh
  rw [log_div (by norm_num) hN.ne', log_one, log_exp, log_phase_product P hP] at hl
  linarith

/-- A sufficiently strong tail estimate rules out every exceptional phase,
not merely most of them. This does not assert the needed estimate. -/
theorem survivor_of_exponential_tail {P : Finset ℕ} {m : ℕ} {b : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (htail : coveredFraction P m ≤ exp (-b))
    (hb : (∑ p ∈ P, log (p : ℝ)) < b) (r : ℕ → ℕ) :
    ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  let s : Phase P := fun p => ⟨r p.val % p.val,
    Nat.mod_lt _ (hP p.val p.property).pos⟩
  have hs : intervalCount P m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hbad x hx
    exact ⟨⟨p, hp⟩, hxp⟩
  exact hb.not_ge (exponent_le_log_product_of_cover hP htail s hs)

/-- If all selected primes are at most B, a tail exponent greater than
k*log B suffices. Large primes must be dealt with before using this cap. -/
theorem survivor_of_exponential_tail_of_cap {P : Finset ℕ} {m k : ℕ} {b B : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hk : P.card ≤ k) (hB : 1 ≤ B)
    (hcap : ∀ p ∈ P, (p : ℝ) ≤ B)
    (htail : coveredFraction P m ≤ exp (-b)) (hb : (k : ℝ) * log B < b)
    (r : ℕ → ℕ) : ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  apply survivor_of_exponential_tail hP htail _ r
  apply lt_of_le_of_lt _ hb
  calc
    _ ≤ ∑ _p ∈ P, log B := sum_le_sum (fun p hp =>
      log_le_log (by exact_mod_cast (hP p hp).pos) (hcap p hp))
    _ = (P.card : ℝ) * log B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (log_nonneg hB)

#print axioms reciprocal_le_coveredFraction
#print axioms survivor_of_exponential_tail
#print axioms survivor_of_exponential_tail_of_cap
end Erdos970.GapAverages
