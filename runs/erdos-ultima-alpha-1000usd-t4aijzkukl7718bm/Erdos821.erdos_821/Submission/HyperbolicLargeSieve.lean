import Submission.FourierCutoff

/-!
# Hyperbolic cutoffs for the bilinear large sieve

Rounded logarithms encode the integer condition `m * n ≤ R` exactly.
The finite Fourier completion then gives a logarithmic-loss bilinear
large sieve. This remains an upper bound, not a smooth-prime lower bound.
-/

open scoped BigOperators
open Finset

namespace Erdos821.AnalyticSieve

noncomputable def logCode (N : ℕ) (n : ℤ) : ℕ :=
  ⌈4 * ((N : ℝ) + 1) * Real.log n⌉₊

noncomputable def logCutoff (N R : ℕ) : ℕ :=
  ⌊4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1)⌋₊

def hyperbolicModulus (N : ℕ) : ℕ := 16 * (N + 1) ^ 2

lemma hyperbolicModulus_ge_two (N : ℕ) : 2 ≤ hyperbolicModulus N := by
  unfold hyperbolicModulus
  have h : 0 < (N + 1) ^ 2 := by positivity
  omega

lemma scaled_log_gap (R : ℕ) (hR : 0 < R) :
    4 + 4 * ((R : ℝ) + 1) * Real.log R ≤
      4 * ((R : ℝ) + 1) * Real.log ((R : ℝ) + 1) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hRp : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hR' hRp)
  rw [Real.log_div hR'.ne' hRp.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (R : ℝ) + 1)
  have heq : ((R : ℝ) + 1) * ((R : ℝ) / ((R : ℝ) + 1) - 1) = -1 := by
    field_simp
    ring
  rw [heq] at hh
  nlinarith

lemma scaled_log_gap_uniform {N R : ℕ} (hR : 0 < R) (hRN : R ≤ N) :
    4 + 4 * ((N : ℝ) + 1) * Real.log R ≤
      4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1) := by
  have h := scaled_log_gap R hR
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hnr : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hg : Real.log R ≤ Real.log ((R : ℝ) + 1) := Real.log_le_log hr (by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr hnr) (sub_nonneg.mpr hg)
  nlinarith

lemma logCode_condition {N R : ℕ} (hRN : R ≤ N) {m n : ℤ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    logCode N m + logCode N n < logCutoff N R ↔ m * n ≤ R := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hmlog : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hnlog : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hK : 0 < 4 * ((N : ℝ) + 1) := by positivity
  have hcut : 0 ≤ 4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1) := by
    apply mul_nonneg hK.le
    exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) R])
  by_cases hR : R = 0
  · subst R
    have hp : (0 : ℤ) < m * n := mul_pos (by omega) (by omega)
    simp only [logCutoff, Nat.cast_zero, zero_add, Real.log_one, mul_zero, Nat.floor_zero,
      Nat.not_lt_zero, false_iff, not_le]
    exact hp
  · have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR
    have hlogs : Real.log ((m : ℝ) * n) = Real.log m + Real.log n :=
      Real.log_mul hmpos.ne' hnpos.ne'
    have hc₁ := Nat.le_ceil (4 * ((N : ℝ) + 1) * Real.log m)
    have hc₂ := Nat.le_ceil (4 * ((N : ℝ) + 1) * Real.log n)
    have hc₁' := Nat.ceil_lt_add_one (mul_nonneg hK.le hmlog)
    have hc₂' := Nat.ceil_lt_add_one (mul_nonneg hK.le hnlog)
    have ht := Nat.floor_le hcut
    have ht' := Nat.lt_floor_add_one (4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1))
    constructor
    · intro h
      by_contra hh
      have hp : (R : ℤ) + 1 ≤ m * n := by omega
      have hp' : (R : ℝ) + 1 ≤ (m : ℝ) * n := by exact_mod_cast hp
      have hlog := Real.log_le_log (by positivity : 0 < (R : ℝ) + 1) hp'
      rw [hlogs] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hK.le
      have h' : (logCode N m : ℝ) + logCode N n < logCutoff N R := by exact_mod_cast h
      change (⌈4 * ((N : ℝ) + 1) * Real.log m⌉₊ : ℝ) +
        (⌈4 * ((N : ℝ) + 1) * Real.log n⌉₊ : ℝ) <
          (⌊4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1)⌋₊ : ℝ) at h'
      nlinarith
    · intro h
      have hp' : (m : ℝ) * n ≤ R := by exact_mod_cast h
      have hlog := Real.log_le_log (mul_pos hmpos hnpos) hp'
      rw [hlogs] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hK.le
      have hgap := scaled_log_gap_uniform (Nat.pos_of_ne_zero hR) hRN
      have h' : (logCode N m : ℝ) + logCode N n < logCutoff N R := by
        change (⌈4 * ((N : ℝ) + 1) * Real.log m⌉₊ : ℝ) +
          (⌈4 * ((N : ℝ) + 1) * Real.log n⌉₊ : ℝ) <
            (⌊4 * ((N : ℝ) + 1) * Real.log ((R : ℝ) + 1)⌋₊ : ℝ)
        nlinarith
      exact_mod_cast h' 

lemma logCode_lt {N : ℕ} {n : ℤ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (logCode N n : ℝ) < 4 * ((N : ℝ) + 1) * N + 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have h := Nat.ceil_lt_add_one (mul_nonneg
    (by positivity : 0 ≤ 4 * ((N : ℝ) + 1)) (Real.log_nonneg hn'))
  have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4 * ((N : ℝ) + 1))
  have hm' := mul_le_mul_of_nonneg_left hnN' (by positivity : 0 ≤ 4 * ((N : ℝ) + 1))
  unfold logCode
  nlinarith

lemma logCode_add_lt_modulus {N : ℕ} {m n : ℤ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    logCode N m + logCode N n < hyperbolicModulus N := by
  have hm' := logCode_lt hm hmN
  have hn' := logCode_lt hn hnN
  have h : (logCode N m : ℝ) + logCode N n < (hyperbolicModulus N : ℝ) := by
    unfold hyperbolicModulus
    push_cast
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]
  exact_mod_cast h

lemma logCutoff_le_modulus {N R : ℕ} (hRN : R ≤ N) :
    logCutoff N R ≤ hyperbolicModulus N := by
  have hr0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnr : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < (R : ℝ) + 1)
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4 * ((N : ℝ) + 1))
  have hm' := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ 4 * ((N : ℝ) + 1))
  have hf := Nat.floor_le (mul_nonneg (by positivity : 0 ≤ 4 * ((N : ℝ) + 1))
    (Real.log_nonneg (by linarith : 1 ≤ (R : ℝ) + 1)))
  have h : (logCutoff N R : ℝ) ≤ (hyperbolicModulus N : ℝ) := by
    unfold logCutoff hyperbolicModulus
    push_cast
    nlinarith [sq_nonneg (N : ℝ)]
  exact_mod_cast h

instance hyperbolicModulus_neZero (N : ℕ) : NeZero (hyperbolicModulus N) :=
  ⟨by have := hyperbolicModulus_ge_two N; omega⟩

noncomputable def logResidue (N : ℕ) (n : ℤ) : ZMod (hyperbolicModulus N) :=
  (logCode N n : ZMod (hyperbolicModulus N))

lemma logResidue_condition {N R : ℕ} (hRN : R ≤ N) {m n : ℤ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    (logResidue N m + logResidue N n).val < logCutoff N R ↔ m * n ≤ R := by
  unfold logResidue
  rw [← Nat.cast_add, ZMod.val_natCast_of_lt (logCode_add_lt_modulus hm hmN hn hnN)]
  exact logCode_condition hRN hm hn

lemma log_hyperbolicModulus_le (N : ℕ) :
    Real.log (hyperbolicModulus N) ≤ 4 + 2 * Real.log ((N : ℝ) + 1) := by
  have h2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  unfold hyperbolicModulus
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, h16]
  norm_num
  linarith

/-- A hyperbolic bilinear large sieve, uniformly for `R ≤ N` and positive
integer inputs bounded by `N`. -/
theorem hyperbolic_bilinear_large_sieve
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y)
    (N R : ℕ) (hRN : R ≤ N)
    (hAN : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) (hBN : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0‖) ≤
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  have h := bilinear_interval_cutoff_large_sieve (hyperbolicModulus_ge_two N)
    M Q hQ hM C hC A B a b X Y hX hY hA hB (logResidue N) (logResidue N)
    (logCutoff N R) (logCutoff_le_modulus hRN)
  have heq (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) :
      (∑ m ∈ A, ∑ n ∈ B, if (logResidue N m + logResidue N n).val < logCutoff N R then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0) =
      ∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R then
        (a m * b n) * χ ((m * n : ℤ) : ZMod (q : ℕ)) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    simp only [logResidue_condition hRN (hAN m hm).1 (hAN m hm).2 (hBN n hn).1 (hBN n hn).2]
  simp only [heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [log_hyperbolicModulus_le N]

end Erdos821.AnalyticSieve
