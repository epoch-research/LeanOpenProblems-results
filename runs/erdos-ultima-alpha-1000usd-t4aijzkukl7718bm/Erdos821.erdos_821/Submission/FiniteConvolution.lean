import Submission.VaughanIdentity

/-!
# Finite convolution sums and Vaughan's identity

Finite divisor convolutions are reindexed as hyperbolic rectangular sums.
All endpoints, including zero, are included.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

lemma sum_divisorsAntidiagonal_Icc {E : Type*} [AddCommMonoid E]
    (F : ℕ × ℕ → E) {R N : ℕ} (hRN : R ≤ N) :
    (∑ k ∈ Icc 1 R, ∑ d ∈ k.divisorsAntidiagonal, F d) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m * n ≤ R then F (m, n) else 0 := by
  classical
  rw [Finset.sum_sigma', ← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_bij (fun z _ => z.2)
  · intro z hz
    obtain ⟨hk, hd⟩ := Finset.mem_sigma.mp hz
    have hm := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hd)
    have hn := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hd)
    have hp := Nat.mem_divisorsAntidiagonal.mp hd
    have hm0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd
    have hn0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd
    simp only [mem_filter, mem_product, mem_Icc] at hk ⊢
    omega
  · intro z hz w hw hzw
    have hz' := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hz).2
    have hw' := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hw).2
    have h : z.1 = w.1 := by rw [← hz'.1, ← hw'.1, hzw]
    cases z with | mk k d =>
      cases w with | mk l e =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at hzw ⊢
        exact ⟨h, hzw⟩
  · intro d hd
    obtain ⟨hd, hmn⟩ := mem_filter.mp hd
    obtain ⟨hm, hn⟩ := mem_product.mp hd
    obtain ⟨hm, hmN⟩ := mem_Icc.mp hm
    obtain ⟨hn, hnN⟩ := mem_Icc.mp hn
    refine ⟨⟨d.1 * d.2, d⟩, ?_, rfl⟩
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨by nlinarith, hmn⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩
  · intro z hz
    rfl

lemma sum_convolution_weighted {S : Type*} [Semiring S]
    (f g : ArithmeticFunction S) (w : ℕ → S) {R N : ℕ} (hRN : R ≤ N) :
    (∑ k ∈ Icc 1 R, (f * g) k * w k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m * n ≤ R then (f m * g n) * w (m * n) else 0 := by
  calc
    _ = ∑ k ∈ Icc 1 R, ∑ d ∈ k.divisorsAntidiagonal, (f d.1 * g d.2) * w (d.1 * d.2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [(Nat.mem_divisorsAntidiagonal.mp hd).1]
    _ = _ := sum_divisorsAntidiagonal_Icc _ hRN

lemma sum_convolution_Icc {S : Type*} [Semiring S] (f g : ArithmeticFunction S) (N : ℕ) :
    (∑ k ∈ Icc 1 N, (f * g) k) =
      ∑ m ∈ Icc 1 N, f m * ∑ n ∈ Icc 1 (N / m), g n := by
  have h := sum_convolution_weighted f g (fun _ => 1) (le_refl N)
  simp only [mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := mem_Icc.mp hm; omega
  have heq : (Icc 1 N).filter (fun n => m * n ≤ N) = Icc 1 (N / m) := by
    ext n
    simp only [mem_filter, mem_Icc, ← Nat.le_div_iff_mul_le hm0, mul_comm m n]
    have hh := Nat.div_le_self N m
    omega
  rw [← Finset.sum_filter, heq, Finset.mul_sum]

noncomputable def twistedArithmeticSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q)

lemma twistedArithmeticSum_add {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) (N : ℕ) :
    twistedArithmeticSum χ (f + g) N = twistedArithmeticSum χ f N + twistedArithmeticSum χ g N := by
  simp only [twistedArithmeticSum, ArithmeticFunction.add_apply, Complex.ofReal_add,
    add_mul, Finset.sum_add_distrib]

lemma twistedArithmeticSum_sub {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) (N : ℕ) :
    twistedArithmeticSum χ (f - g) N = twistedArithmeticSum χ f N - twistedArithmeticSum χ g N := by
  simp only [twistedArithmeticSum, (show ∀ n, (f - g) n = f n - g n from fun n => rfl), Complex.ofReal_sub,
    sub_mul, Finset.sum_sub_distrib]

lemma twistedArithmeticSum_convolution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) {R N : ℕ} (hRN : R ≤ N) :
    twistedArithmeticSum χ (f * g) R =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m * n ≤ R then ((f m : ℂ) * (g n : ℂ)) * χ ((m * n : ℕ) : ZMod q) else 0 := by
  calc
    _ = ∑ k ∈ Icc 1 R, ∑ d ∈ k.divisorsAntidiagonal,
        ((f d.1 : ℂ) * (g d.2 : ℂ)) * χ ((d.1 * d.2 : ℕ) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [(Nat.mem_divisorsAntidiagonal.mp hd).1]
    _ = _ := sum_divisorsAntidiagonal_Icc _ hRN

noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * χ (n : ZMod q), by simp⟩

lemma characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (f g : ArithmeticFunction ℝ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext k
  change (((f * g) k : ℝ) : ℂ) * χ (k : ZMod q) = _
  simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← (Nat.mem_divisorsAntidiagonal.mp hd).1, Nat.cast_mul, map_mul]
  change (f d.1 : ℂ) * (g d.2 : ℂ) * (χ d.1 * χ d.2) = _
  unfold characterTwist
  simp only [ArithmeticFunction.coe_mk]
  ring

lemma twistedArithmeticSum_convolution_quotient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) (N : ℕ) :
    twistedArithmeticSum χ (f * g) N =
      ∑ m ∈ Icc 1 N, ((f m : ℂ) * χ (m : ZMod q)) * twistedArithmeticSum χ g (N / m) := by
  change (∑ k ∈ Icc 1 N, characterTwist χ (f * g) k) = _
  rw [characterTwist_mul, sum_convolution_Icc]
  rfl

/-- Vaughan's identity after twisting and truncating the sum. -/
theorem twisted_vaughan_identity {q : ℕ} (χ : DirichletCharacter ℂ q) (U V N : ℕ) :
    twistedArithmeticSum χ vonMangoldt N =
      twistedArithmeticSum χ (shortPart vonMangoldt U) N +
      twistedArithmeticSum χ (shortPart (μ : ArithmeticFunction ℝ) V * log) N -
      twistedArithmeticSum χ (vaughanTypeI U V * (ζ : ArithmeticFunction ℝ)) N +
      twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) N := by
  have h := congrArg (fun f => twistedArithmeticSum χ f N) (vaughan_identity_typeI_typeII U V)
  simpa only [twistedArithmeticSum_add, twistedArithmeticSum_sub] using h

end Erdos821.AnalyticSieve
