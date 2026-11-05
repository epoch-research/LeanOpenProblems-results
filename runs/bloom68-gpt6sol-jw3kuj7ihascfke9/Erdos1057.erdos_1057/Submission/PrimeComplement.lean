import Submission.LowLambdaSharper
import Submission.FactorBound

/-!
# A divisor bound for Carmichael numbers with a prime complementary factor

If `n = a * p` is Carmichael and `p` is prime, Korselt's necessary
congruence says that `p - 1 ∣ a - 1`. Thus, for each `a ≥ 2`, the prime
factor `p` is among the numbers `d + 1` with `d ∣ a - 1`. This gives a
summatory-divisor bound for the subfamily with `a` bounded by `B`, including
when `B` is the prime-cutoff block bound for small Carmichael-function values.
The bound concerns only numbers admitting such a *prime* complementary factor.
-/

namespace Erdos1057

/-- Low-`λ` Carmichael numbers up to `X` having a factorization `n = a * p`
with `p` prime, `p ≤ a`, and `a ≤ B`. -/
def primeComplementCarmichaels (X H B : ℕ) : Set ℕ :=
  {n | n ∈ lowLambdaCarmichaels X H ∧
    ∃ a p : ℕ, p.Prime ∧ n = a * p ∧ p ≤ a ∧ a ≤ B}

/-- Counting the possible pairs `(a, p - 1)`, with `p - 1 ∣ a - 1`.
The index starts at `a = 2`: if `a = 1`, then `n` would be prime. -/
theorem primeComplementCarmichaels_card_le_divisor_sum (X H B : ℕ) :
    (primeComplementCarmichaels X H B).ncard ≤
      ∑ a ∈ Finset.Ioc 1 B, (a - 1).divisors.card := by
  classical
  let s : Finset ℕ := (Finset.Ioc 1 B).biUnion fun a =>
    (a - 1).divisors.image (fun d => a * (d + 1))
  have hcover : primeComplementCarmichaels X H B ⊆ (s : Set ℕ) := by
    intro n hn
    obtain ⟨⟨hnC, _, _⟩, a, p, hp, hnfac, _, haB⟩ := hn
    have hn1 : 1 < n := (hnC 1 (by omega) (by simp)).2.2
    have hnprime : ¬n.Prime := (hnC 1 (by omega) (by simp)).2.1
    have ha2 : 2 ≤ a := by
      have ha0 : a ≠ 0 := by
        intro h0
        have : n = 0 := by simpa [h0] using hnfac
        omega
      have ha1 : a ≠ 1 := by
        intro h1
        have hnp : n = p := by simpa [h1] using hnfac
        exact hnprime (hnp ▸ hp)
      omega
    have hdiv : p - 1 ∣ a - 1 :=
      isCarmichael_cofactor_constraint hnC hp (hnfac.trans (Nat.mul_comm a p))
    have hdmem : p - 1 ∈ (a - 1).divisors :=
      Nat.mem_divisors.mpr ⟨hdiv, by omega⟩
    change n ∈ s
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_Ioc.mpr ⟨by omega, haB⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p - 1, hdmem, ?_⟩
    rw [Nat.sub_add_cancel hp.one_le]
    exact hnfac.symm
  calc
    (primeComplementCarmichaels X H B).ncard ≤ s.card := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
    _ ≤ ∑ a ∈ Finset.Ioc 1 B,
        ((a - 1).divisors.image (fun d => a * (d + 1))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Ioc 1 B, (a - 1).divisors.card :=
      Finset.sum_le_sum fun a _ => Finset.card_image_le

/-- Shift from cofactors `a` to the positive integers `a - 1`. -/
private theorem primeComplement_divisor_sum_le (B : ℕ) :
    (∑ a ∈ Finset.Ioc 1 B, (a - 1).divisors.card) ≤
      ∑ t ∈ Finset.Ioc 0 B, t.divisors.card := by
  classical
  have hsub : (Finset.Ioc 1 B).image (fun a => a - 1) ⊆ Finset.Ioc 0 B := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_Ioc.mpr (by
      have ha' := Finset.mem_Ioc.mp ha
      omega)
  calc
    ∑ a ∈ Finset.Ioc 1 B, (a - 1).divisors.card =
        ∑ t ∈ (Finset.Ioc 1 B).image (fun a => a - 1), t.divisors.card := by
      rw [Finset.sum_image (by
        intro a ha a' ha' heq
        change a ∈ Finset.Ioc 1 B at ha
        change a' ∈ Finset.Ioc 1 B at ha'
        have ha2 := (Finset.mem_Ioc.mp ha).1
        have ha'2 := (Finset.mem_Ioc.mp ha').1
        change a - 1 = a' - 1 at heq
        omega)]
    _ ≤ ∑ t ∈ Finset.Ioc 0 B, t.divisors.card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

/-- The summatory-divisor estimate, following the divisor-sum identity used
in `Submission.FactorBound`. -/
private theorem primeComplement_sum_card_divisors_le (B : ℕ) :
    ((∑ t ∈ Finset.Ioc 0 B, t.divisors.card : ℕ) : ℝ) ≤
      (B : ℝ) * (1 + Real.log (B : ℝ)) := by
  have hsum : (∑ t ∈ Finset.Ioc 0 B, t.divisors.card) =
      (∑ t ∈ Finset.Ioc 0 B, (B / t : ℕ)) := by
    simpa only [ArithmeticFunction.sigma_zero_apply] using
      (ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div B)
  have hharm : (∑ t ∈ Finset.Ioc 0 B, (t : ℝ)⁻¹) = (harmonic B : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  calc
    ((∑ t ∈ Finset.Ioc 0 B, t.divisors.card : ℕ) : ℝ) =
        ((∑ t ∈ Finset.Ioc 0 B, (B / t : ℕ) : ℕ) : ℝ) := by rw [hsum]
    _ = ∑ t ∈ Finset.Ioc 0 B, ((B / t : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ t ∈ Finset.Ioc 0 B, (B : ℝ) / (t : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.cast_div_le
    _ = (B : ℝ) * (∑ t ∈ Finset.Ioc 0 B, (t : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [div_eq_mul_inv]
    _ = (B : ℝ) * (harmonic B : ℝ) := by rw [hharm]
    _ ≤ (B : ℝ) * (1 + Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log B) (Nat.cast_nonneg B)

/-- Uniform logarithmic bound for the prime-complement subfamily. -/
theorem primeComplementCarmichaels_card_le_log (X H B : ℕ) :
    ((primeComplementCarmichaels X H B).ncard : ℝ) ≤
      (B : ℝ) * (1 + Real.log (B : ℝ)) := by
  calc
    ((primeComplementCarmichaels X H B).ncard : ℝ) ≤
        ((∑ a ∈ Finset.Ioc 1 B, (a - 1).divisors.card : ℕ) : ℝ) := by
      exact_mod_cast primeComplementCarmichaels_card_le_divisor_sum X H B
    _ ≤ ((∑ t ∈ Finset.Ioc 0 B, t.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast primeComplement_divisor_sum_le B
    _ ≤ (B : ℝ) * (1 + Real.log (B : ℝ)) :=
      primeComplement_sum_card_divisors_le B

/-- With `B ≤ X`, one can replace `log B` by `log X`. -/
theorem primeComplementCarmichaels_card_le_log_X (X H B : ℕ) (hBX : B ≤ X) :
    ((primeComplementCarmichaels X H B).ncard : ℝ) ≤
      (B : ℝ) * (1 + Real.log (X : ℝ)) := by
  have hlog : Real.log (B : ℝ) ≤ Real.log (X : ℝ) := by
    by_cases hB : B = 0
    · simpa only [hB, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg X
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hB))
        (by exact_mod_cast hBX)
  exact (primeComplementCarmichaels_card_le_log X H B).trans
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg B))

/-- The instance with the prime-factor cutoff associated to `λ(n) ≤ H`. -/
theorem primeComplementCarmichaels_cutoff_card_le_divisor_sum (X H : ℕ) :
    (primeComplementCarmichaels X H (primeCutoffBlockBound X (H + 1))).ncard ≤
      ∑ a ∈ Finset.Ioc 1 (primeCutoffBlockBound X (H + 1)),
        (a - 1).divisors.card :=
  primeComplementCarmichaels_card_le_divisor_sum X H _

/-- The logarithmic estimate with the low-`λ` prime-factor cutoff. -/
theorem primeComplementCarmichaels_cutoff_card_le_log_X (X H : ℕ) :
    ((primeComplementCarmichaels X H (primeCutoffBlockBound X (H + 1))).ncard : ℝ) ≤
      (primeCutoffBlockBound X (H + 1) : ℝ) * (1 + Real.log (X : ℝ)) :=
  primeComplementCarmichaels_card_le_log_X X H _
    (primeCutoffBlockBound_le_X X (H + 1))

end Erdos1057
