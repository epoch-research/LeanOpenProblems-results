import FormalConjecturesUtil

/-!
Uniform subpower bounds for the number of Gaussian prime-factor submultisets.
This is an arithmetic ingredient for collision codegree estimates, not a
settlement of the square-Sidon conjecture.
-/
namespace Erdos773.GaussianDivisorBound
open Finset Filter UniqueFactorizationMonoid
set_option maxHeartbeats 1000000

noncomputable local instance : NormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- The nonnegative integral Gaussian norm. -/
def gNorm : GaussianInt →* ℕ :=
  Int.natAbsHom.toMonoidHom.comp (Zsqrtd.normMonoidHom : GaussianInt →* ℤ)

lemma gNorm_eq (z : GaussianInt) : gNorm z = z.norm.natAbs := rfl

lemma gNorm_associated {z w : GaussianInt} (h : Associated z w) : gNorm z = gNorm w := by
  exact congrArg Int.natAbs (Zsqrtd.norm_eq_of_associated (by norm_num) h)

lemma gNorm_prime {z : GaussianInt} (hz : Prime z) : 2 ≤ gNorm z := by
  have h0 : gNorm z ≠ 0 := by
    simpa [gNorm_eq, GaussianInt.norm_eq_zero] using hz.ne_zero
  have h1 : gNorm z ≠ 1 := fun h => hz.not_unit (Zsqrtd.norm_eq_one_iff.mp h)
  omega

/-- A finite box containing all Gaussian integers of norm less than K. -/
def normBox (K : ℕ) : Finset GaussianInt :=
  ((Icc (-(K : ℤ)) K) ×ˢ (Icc (-(K : ℤ)) K)).image (fun p => ⟨p.1, p.2⟩)

lemma mem_normBox {K : ℕ} {z : GaussianInt} (h : gNorm z < K) : z ∈ normBox K := by
  have hnorm : z.re ^ 2 + z.im ^ 2 < (K : ℤ) := by
    have hh : (gNorm z : ℤ) < K := by exact_mod_cast h
    rw [gNorm_eq, GaussianInt.abs_natCast_norm] at hh
    simpa [Zsqrtd.norm, pow_two] using hh
  have hK : (0 : ℤ) ≤ K := by positivity
  have hre : -(K : ℤ) ≤ z.re ∧ z.re ≤ K := by
    constructor <;> nlinarith [sq_nonneg z.im, sq_nonneg (z.re + K), sq_nonneg (z.re - K)]
  have him : -(K : ℤ) ≤ z.im ∧ z.im ≤ K := by
    constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.im + K), sq_nonneg (z.im - K)]
  exact mem_image.mpr ⟨(z.re,z.im), mem_product.mpr ⟨mem_Icc.mpr hre,mem_Icc.mpr him⟩, rfl⟩

/-- The ordinary divisor-function proof applies to Gaussian prime factors:
there are finitely many factors with small norm, and all others absorb the
linear exponent-count cost into an arbitrarily small power of their norm. -/
theorem factor_submultisets_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ z : GaussianInt, z ≠ 0 →
      ((Iic (normalizedFactors z)).card : ℝ) ≤ C * (gNorm z : ℝ) ^ δ := by
  classical
  let b : ℝ := 2 ^ δ
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + 1 / (b - 1)
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ 1 / (b - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcb : c * (b - 1) = b := by
    dsimp [c]
    field_simp [show b - 1 ≠ 0 by linarith]
    ring
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ c * b ^ e := by
    have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ b) e
    calc
      (e : ℝ) + 1 ≤ c + (e : ℝ) * b := by
        nlinarith [mul_nonneg (Nat.cast_nonneg e) (le_of_lt (sub_pos.mpr hb))]
      _ = c * (1 + (e : ℝ) * (b - 1)) := by
        rw [mul_add, mul_one, ← mul_left_comm, hcb]
      _ ≤ c * b ^ e := mul_le_mul_of_nonneg_left hber hcpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ≥ K, (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    exact eventually_atTop.mp
      (tendsto_atTop.mp ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop) 2)
  refine ⟨c ^ (normBox K).card, pow_pos hcpos _, fun z hz => ?_⟩
  let s := normalizedFactors z
  have hfactor (p : GaussianInt) (hp : p ∈ s.toFinset) :
      ((s.count p + 1 : ℕ) : ℝ) ≤
        (if gNorm p < K then c else 1) * ((gNorm p : ℝ) ^ δ) ^ s.count p := by
    have hp2 : (2 : ℝ) ≤ gNorm p := by
      exact_mod_cast gNorm_prime (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp))
    by_cases hpk : gNorm p < K
    · rw [if_pos hpk]
      calc
        ((s.count p + 1 : ℕ) : ℝ) = (s.count p : ℝ) + 1 := by push_cast; rfl
        _ ≤ c * b ^ s.count p := hsmall _
        _ ≤ c * ((gNorm p : ℝ) ^ δ) ^ s.count p := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpk, one_mul]
      calc
        ((s.count p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s.count p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := s.count p)))
        _ ≤ ((gNorm p : ℝ) ^ δ) ^ s.count p :=
          pow_le_pow_left₀ (by norm_num) (hK _ (by omega)) _
  have hcoeff : (∏ p ∈ s.toFinset, if gNorm p < K then c else 1) ≤ c ^ (normBox K).card := by
    have hcard : (s.toFinset.filter (fun p => gNorm p < K)).card ≤ (normBox K).card :=
      card_le_card (fun p hp => mem_normBox (mem_filter.mp hp).2)
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hc hcard
  have hprod : (∏ p ∈ s.toFinset, (gNorm p : ℝ) ^ s.count p) = gNorm z := by
    have hh : (∏ p ∈ s.toFinset, gNorm p ^ s.count p) = gNorm z := by
      rw [← Finset.prod_multiset_map_count, ← map_multiset_prod]
      exact gNorm_associated (prod_normalizedFactors hz)
    exact_mod_cast hh
  have hrpow : (∏ p ∈ s.toFinset, ((gNorm p : ℝ) ^ δ) ^ s.count p) = (gNorm z : ℝ) ^ δ := by
    calc
      _ = ∏ p ∈ s.toFinset, ((gNorm p : ℝ) ^ s.count p) ^ δ := by
        apply prod_congr rfl
        intro p hp
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),
          ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm δ]
      _ = (∏ p ∈ s.toFinset, (gNorm p : ℝ) ^ s.count p) ^ δ :=
        Real.finset_prod_rpow _ _ (by intros; positivity) _
      _ = _ := by rw [hprod]
  change ((Iic s).card : ℝ) ≤ _
  calc
    _ = ∏ p ∈ s.toFinset, ((s.count p + 1 : ℕ) : ℝ) := by rw [Multiset.card_Iic, Nat.cast_prod]
    _ ≤ ∏ p ∈ s.toFinset, (if gNorm p < K then c else 1) * ((gNorm p : ℝ) ^ δ) ^ s.count p :=
      prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ s.toFinset, if gNorm p < K then c else 1) * (gNorm z : ℝ) ^ δ := by
      rw [prod_mul_distrib, hrpow]
    _ ≤ c ^ (normBox K).card * (gNorm z : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg _) δ)

#print axioms factor_submultisets_subpower
end Erdos773.GaussianDivisorBound
