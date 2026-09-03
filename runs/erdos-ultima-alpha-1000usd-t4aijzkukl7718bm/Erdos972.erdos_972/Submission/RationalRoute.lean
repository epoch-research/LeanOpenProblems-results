import FormalConjecturesUtil
/-! A conditional route through a uniform finite estimate for rational slopes. -/
namespace Erdos972RationalRoute

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊α * p⌋₊}

lemma finite_rat_num_den_bounded (D : ℕ) (L U : ℤ) :
    {r : ℚ | r.den ≤ D ∧ L ≤ r.num ∧ r.num ≤ U}.Finite := by
  have hf := ((Set.finite_Icc L U).prod (Set.finite_Iic D)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ) / z.2)
  apply hf.subset
  intro r hr
  exact ⟨(r.num, r.den), ⟨⟨hr.2.1, hr.2.2⟩, hr.1⟩, Rat.num_div_den r⟩

lemma finite_good_approximants_bounded_den {α : ℝ} (hα : 1 < α) (D : ℕ) :
    {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ 2 ∧ r.den ≤ D}.Finite := by
  apply (finite_rat_num_den_bounded D 0 ⌈(α + 1) * D⌉).subset
  intro r hr
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hsmall : |α - r| < 1 := by
    have hsq : (1 : ℝ) ≤ (r.den : ℝ) ^ 2 := by nlinarith
    exact hr.1.trans_le ((div_le_one (by positivity)).mpr hsq)
  have hrlo : (0 : ℝ) < r := by linarith [(abs_lt.mp hsmall).2]
  have hrhi : (r : ℝ) < α + 1 := by linarith [(abs_lt.mp hsmall).1]
  have hnum : (r.num : ℝ) = (r : ℝ) * r.den := by
    exact_mod_cast (Rat.mul_den_eq_num r).symm
  refine ⟨hr.2, Rat.num_nonneg.mpr (by exact_mod_cast hrlo.le), ?_⟩
  have hb : (r.num : ℝ) ≤ (α + 1) * D := by
    rw [hnum]
    exact (mul_le_mul_of_nonneg_right hrhi.le (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr.2) (by linarith))
  exact_mod_cast hb.trans (Int.le_ceil _)

lemma exists_good_approximant_large_den {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (D : ℕ) :
    ∃ r : ℚ, |α - r| < 1 / (r.den : ℝ) ^ 2 ∧ D < r.den := by
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hI
  obtain ⟨r, hr, hn⟩ :=
    (hi.diff (finite_good_approximants_bounded_den hα D)).nonempty
  refine ⟨r, hr, ?_⟩
  by_contra h
  exact hn ⟨hr, Nat.le_of_not_gt h⟩

lemma transfer_prime_pair {α : ℝ} {r : ℚ} {p q : ℕ}
    (ha : |α - r| < 1 / (r.den : ℝ) ^ 2)
    (hb : 8 * (p : ℝ) ≤ (r.den : ℝ) ^ 2)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hlo : (q : ℝ) + 1 / 4 < (r : ℝ) * p)
    (hhi : (r : ℝ) * p < (q : ℝ) + 3 / 4) : p ∈ primeSet α := by
  have hden : (0 : ℝ) < (r.den : ℝ) ^ 2 := by positivity
  have ham := (lt_div_iff₀ hden).mp ha
  have heb : |α - r| * (p : ℝ) < 1 / 8 := by
    have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg (α - r))
    nlinarith
  have he : |α * p - (r : ℝ) * p| < 1 / 8 := by
    simpa only [← sub_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ p from Nat.cast_nonneg p)] using heb
  have hf : ⌊α * p⌋₊ = q := by
    apply (Nat.floor_eq_iff' hq.ne_zero).mpr
    obtain ⟨he₁, he₂⟩ := abs_lt.mp he
    constructor <;> linarith
  exact ⟨hp, by simpa only [hf] using hq⟩

/-- A sufficient finite arithmetic estimate. This is a hypothesis here, not a proved result. -/
def RationalPrimeEstimate : Prop :=
  ∀ A : ℝ, 1 < A → ∃ B : ℕ, ∀ r : ℚ,
    1 < (r : ℝ) → (r : ℝ) < A → B < r.den →
      ∃ p q : ℕ, r.den ≤ p ∧ 8 * (p : ℝ) ≤ (r.den : ℝ) ^ 2 ∧
        Nat.Prime p ∧ Nat.Prime q ∧
        (q : ℝ) + 1 / 4 < (r : ℝ) * p ∧ (r : ℝ) * p < (q : ℝ) + 3 / 4

lemma conjecture_of_rational_prime_estimate (hE : RationalPrimeEstimate) :
    ∀ α > 1, Irrational α → (primeSet α).Infinite := by
  intro α hα hI
  obtain ⟨B, hB⟩ := hE (α + 1) (by linarith)
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / (α - 1))
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨r, ha, hden⟩ := exists_good_approximant_large_den hα hI (max B (max D N))
  have hBr : B < r.den := lt_of_le_of_lt (le_max_left _ _) hden
  have hDr : D < r.den := lt_of_le_of_lt ((le_max_left D N).trans (le_max_right B _)) hden
  have hNr : N < r.den := lt_of_le_of_lt ((le_max_right D N).trans (le_max_right B _)) hden
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hdpos : (0 : ℝ) < (r.den : ℝ) ^ 2 := by positivity
  have hdlarge : 1 / (α - 1) < (r.den : ℝ) ^ 2 := by
    have hcast : (D : ℝ) < r.den := Nat.cast_lt.mpr hDr
    nlinarith
  have hsmall : |α - r| < α - 1 := by
    apply ha.trans
    apply (div_lt_iff₀ hdpos).mpr
    have ht := (div_lt_iff₀ (sub_pos.mpr hα)).mp hdlarge
    nlinarith
  have hrlo : 1 < (r : ℝ) := by linarith [(abs_lt.mp hsmall).2]
  have hrhi : (r : ℝ) < α + 1 := by
    have hsmall' : |α - r| < 1 :=
      ha.trans_le ((div_le_one hdpos).mpr (by nlinarith))
    linarith [(abs_lt.mp hsmall').1]
  obtain ⟨p, q, hdp, hbound, hp, hq, hlo, hhi⟩ := hB r hrlo hrhi hBr
  exact ⟨p, transfer_prime_pair ha hbound hp hq hlo hhi, hNr.trans_le hdp⟩

#print axioms conjecture_of_rational_prime_estimate
end Erdos972RationalRoute
