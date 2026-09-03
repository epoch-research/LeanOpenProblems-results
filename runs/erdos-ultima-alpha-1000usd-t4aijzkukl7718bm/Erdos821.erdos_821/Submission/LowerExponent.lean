import Submission.Work
import Submission.Sieve

/-!
# Recovering exponent lost in the smooth-prime pigeonhole construction

This is an improved fixed-exponent lower bound, not a settlement of Erdős 821.
No new analytic estimate for the distribution of shifted primes is used.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma general_smooth_prime_counting_margin (t a b L : ℕ)
    (hbt : b + 4 ≤ t) (hba : b + 3 ≤ a) (hat : a ≤ t)
    (hL : 1 ≤ L) (htL : t ≤ L) :
    (t * L * 2 ^ ((b + 1) * L) + 1) ^ (2 ^ (b * L)) *
        2 ^ ((a - b - 2) * L * 2 ^ ((b + 1) * L)) <
      (2 ^ (a * L)).choose (2 ^ ((b + 1) * L)) := by
  let k := 2 ^ ((b + 1) * L)
  let y := 2 ^ (b * L)
  have hL0 : 0 < L := by omega
  have hk : 0 < k := by dsimp [k]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hLp : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have htp : t ≤ 2 ^ L := htL.trans hLp
  have hsmall : t * L * k ≤ 2 ^ ((b + 3) * L) := by
    calc
      t * L * k ≤ 2 ^ L * 2 ^ L * 2 ^ ((b + 1) * L) :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul htp hLp)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; ring
  have hbase : t * L * k + 1 ≤ 2 ^ (t * L) := by
    calc
      t * L * k + 1 ≤ 2 ^ ((b + 3) * L) + 2 ^ ((b + 3) * L) :=
        Nat.add_le_add hsmall (Nat.one_le_pow _ _ (by decide))
      _ = 2 ^ ((b + 3) * L + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ ((b + 4) * L) := Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L hbt)
  have hky : k = 2 ^ L * y := by
    dsimp [k, y]
    rw [← pow_add]
    congr 1
    ring
  have hdim : (t * L * k + 1) ^ y < 2 ^ (L * k) := by
    calc
      (t * L * k + 1) ^ y ≤ (2 ^ (t * L)) ^ y := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((t * L) * y) := (pow_mul _ _ _).symm
      _ < _ := by
        apply Nat.pow_lt_pow_right (by decide)
        rw [hky]
        have hgap : t < 2 ^ L := htL.trans_lt Nat.lt_two_pow_self
        have h := Nat.mul_lt_mul_of_pos_right hgap (Nat.mul_pos hL0 hy)
        nlinarith
  have hcount : 2 ^ (((a - b - 1) * L) * k) ≤ (2 ^ (a * L)).choose k := by
    apply two_pow_mul_le_choose
    dsimp [k]
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have hcoeff : b + 1 + (a - b - 1) = a := by omega
    nlinarith
  calc
    (t * L * k + 1) ^ y * 2 ^ ((a - b - 2) * L * k) <
        2 ^ (L * k) * 2 ^ ((a - b - 2) * L * k) :=
      Nat.mul_lt_mul_of_pos_right hdim (by positivity)
    _ = 2 ^ (((a - b - 1) * L) * k) := by
      rw [← pow_add]
      congr 1
      have hcoeff : a - b - 2 + 1 = a - b - 1 := by omega
      rw [← hcoeff]
      ring
    _ ≤ _ := hcount

lemma large_g_of_general_dyadic_smooth_primes (t a b L : ℕ)
    (hbt : b + 4 ≤ t) (hba : b + 3 ≤ a) (hat : a ≤ t)
    (hL : 1 ≤ L) (htL : t ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ (b * L)))
    (hcard : 2 ^ (a * L) ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 2 ^ (t * L * 2 ^ ((b + 1) * L)) ∧
      (2 ^ ((a - b - 2) * L * 2 ^ ((b + 1) * L)) : ℝ) < (g n : ℝ) := by
  apply large_g_of_smooth_shifted_primes P (t * L) (2 ^ (b * L))
    (2 ^ ((b + 1) * L)) _ (by positivity) hP
  exact_mod_cast (general_smooth_prime_counting_margin t a b L hbt hba hat hL htL).trans_le
    (Nat.choose_le_choose (2 ^ ((b + 1) * L)) hcard)

lemma infinite_g_gt_of_general_dyadic_density (t a b : ℕ)
    (hbt : b + 4 ≤ t) (hba : b + 3 ≤ a) (hat : a ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (b * L))) ∧
      2 ^ (a * L) ≤ P.card) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((a - b - 2 : ℕ) / (t : ℝ))}.Infinite := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hE : 0 < a - b - 2 := by omega
  have hδ : 0 < ((a - b - 2 : ℕ) : ℝ) / t :=
    div_pos (by exact_mod_cast hE) htR
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup g
  obtain ⟨L, hLM, P, hP, hcard⟩ := H (max 1 (max t C))
  have hL : 1 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hCL : C ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLM)
  let k := 2 ^ ((b + 1) * L)
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨n, hn, hnle, hg⟩ := large_g_of_general_dyadic_smooth_primes t a b L
    hbt hba hat hL htL P hP hcard
  have hCB : (C : ℝ) ≤ (2 : ℝ) ^ ((a - b - 2) * L * k) := by
    have hLB : L ≤ (a - b - 2) * L * k := by
      have hEk : 1 ≤ (a - b - 2) * k := Nat.mul_pos hE hk
      nlinarith
    exact_mod_cast hCL.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) hLB))
  have hexp : ((t * L * k : ℕ) : ℝ) * (((a - b - 2 : ℕ) : ℝ) / t) =
      (((a - b - 2) * L * k : ℕ) : ℝ) := by
    simp only [Nat.cast_mul]
    field_simp
  have hpow : (n : ℝ) ^ (((a - b - 2 : ℕ) : ℝ) / t) ≤
      (2 : ℝ) ^ ((a - b - 2) * L * k) := by
    calc
      (n : ℝ) ^ (((a - b - 2 : ℕ) : ℝ) / t) ≤
          ((2 : ℝ) ^ (t * L * k)) ^ (((a - b - 2 : ℕ) : ℝ) / t) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnle) hδ.le
      _ = (2 : ℝ) ^ (((t * L * k : ℕ) : ℝ) * (((a - b - 2 : ℕ) : ℝ) / t)) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp, Real.rpow_natCast]
  refine ⟨n, hpow.trans_lt hg, ?_⟩
  by_contra h
  have hnmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hgC : (g n : ℝ) ≤ C := by exact_mod_cast (Finset.le_sup (f := g) hnmem)
  exact (not_lt_of_ge (hgC.trans hCB)) hg


/-- The elementary sieve estimate is valid at every sufficiently large scale,
not merely at an unspecified unbounded sequence of scales. -/
lemma Sieve.exists_eventual_fixed_smooth_shifted_prime_density :
    ∃ t : ℕ, 6 ≤ t ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨u, hu⟩ := exists_nat_gt (max 1
    (8192 * Sieve.totientRatioAverageConstant * (1 + 5 * Real.log 2) / (Real.log 2) ^ 2))
  have hu1 : (1 : ℝ) < u := (le_max_left _ _).trans_lt hu
  have hu0 : 0 < u := by exact_mod_cast (show (0 : ℝ) < u by linarith)
  have huC : 8192 * Sieve.totientRatioAverageConstant * (1 + 5 * Real.log 2) ≤
      (u : ℝ) * (Real.log 2) ^ 2 :=
    ((div_lt_iff₀ (sq_pos_of_pos hc)).mp ((le_max_right _ _).trans_lt hu)).le
  refine ⟨128 * u, by omega, max 4 (1536 * u), ?_⟩
  intro L hL
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL
  have hLu : 1536 * u ≤ L := (le_max_right _ _).trans hL
  let P := ((2 ^ (128 * u * L) + 1).primesBelow).filter
    (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * u - 5) * L)))
  refine ⟨P, ?_, Sieve.smooth_shifted_primes_dyadic_count u L hu0 hL4 hLu huC⟩
  intro p hp
  obtain ⟨hpQ, hpS⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
  exact ⟨hprime, by omega, hpS⟩

lemma infinite_g_gt_of_scaled_eventual_weak_density (t m : ℕ) (ht : 6 ≤ t) (hm : 1 ≤ m)
    (L₀ : ℕ) (H : ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((4 * (m : ℝ) - 2) / ((t : ℝ) * m))}.Infinite := by
  have hgap : (t - 1) * m = (t - 5) * m + 4 * m := by
    have hcoeff : t - 1 = (t - 5) + 4 := by omega
    rw [hcoeff]
    ring
  have hgap' : t * m = (t - 5) * m + 5 * m := by
    have hcoeff : t = (t - 5) + 5 := by omega
    conv_lhs => rw [hcoeff]
    ring
  have hinf := infinite_g_gt_of_general_dyadic_density (t * m) ((t - 1) * m) ((t - 5) * m)
    (by omega) (by omega) (by omega) (by
      intro M
      let L := max M L₀
      have hLM : M ≤ L := le_max_left _ _
      have hL₀ : L₀ ≤ m * L := (le_max_right M L₀).trans (by nlinarith : L ≤ m * L)
      obtain ⟨P, hP, hcard⟩ := H (m * L) hL₀
      exact ⟨L, hLM, P, by simpa only [mul_assoc] using hP,
        by simpa only [mul_assoc] using hcard⟩)
  have hnat : (t - 1) * m - (t - 5) * m - 2 = 4 * m - 2 := by omega
  have hnum : (((t - 1) * m - (t - 5) * m - 2 : ℕ) : ℝ) = 4 * (m : ℝ) - 2 := by
    rw [hnat, Nat.cast_sub (by omega : 2 ≤ 4 * m)]
    push_cast
    rfl
  simpa only [hnum, Nat.cast_mul] using hinf

/-- Scaling the same weak density estimate removes its fixed integer counting
loss. It reaches every exponent below `4/t`, not exponents near one. -/
lemma infinite_g_gt_of_eventual_weak_density (t : ℕ) (ht : 6 ≤ t)
    (L₀ : ℕ) (H : ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card)
    (δ : ℝ) (hδ : 0 < δ) (hδt : δ < 4 / (t : ℝ)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hprod : δ * t < 4 := (lt_div_iff₀ htR).mp hδt
  have hgap : 0 < 4 - (t : ℝ) * δ := by nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (4 - (t : ℝ) * δ) + 1)
  have hmR : (1 : ℝ) < m := by have := div_pos (by norm_num : (0 : ℝ) < 2) hgap; linarith
  have hm1 : 1 ≤ m := by exact_mod_cast hmR.le
  have hmpos : (0 : ℝ) < m := by linarith
  have hprod' : 2 < (4 - (t : ℝ) * δ) * m := by
    have h := (div_lt_iff₀ hgap).mp (show 2 / (4 - (t : ℝ) * δ) < m by linarith)
    simpa only [mul_comm] using h
  have hexp : δ ≤ (4 * (m : ℝ) - 2) / ((t : ℝ) * m) := by
    apply (le_div_iff₀ (mul_pos htR hmpos)).mpr
    nlinarith
  have hinf := infinite_g_gt_of_scaled_eventual_weak_density t m ht hm1 L₀ H
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans_lt hn.1

/-- An unconditional improvement of the previously recorded `2/t` exponent
from the same fixed-scale sieve input. The parameter `t` is still fixed. -/
theorem exists_fixed_scale_improved_exponents :
    ∃ t : ℕ, 6 ≤ t ∧ ∀ δ : ℝ, 0 < δ → δ < 4 / (t : ℝ) →
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  obtain ⟨t, ht, L₀, H⟩ := Sieve.exists_eventual_fixed_smooth_shifted_prime_density
  exact ⟨t, ht, fun δ hδ hδt => infinite_g_gt_of_eventual_weak_density t ht L₀ H δ hδ hδt⟩

namespace Sieve

set_option maxHeartbeats 2000000 in
lemma smooth_shifted_primes_dyadic_full_count (u L : ℕ) (hu : 0 < u)
    (hL : 4 ≤ L) (hLu : 1536 * u ≤ L)
    (huC : 8192 * totientRatioAverageConstant * (1 + 5 * Real.log 2) ≤
      (u : ℝ) * (Real.log 2) ^ 2) :
    2 ^ (128 * u * L) ≤ 2 * (128 * u * L) *
      ((((2 ^ (128 * u * L) + 1).primesBelow).filter
        (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * u - 5) * L)))).card + 1) := by
  let t := 128 * u
  let X := 2 ^ (t * L)
  let A := 2 ^ (5 * L)
  let Y := 2 ^ ((t - 5) * L)
  let b := 2 ^ ((t - 1) * L)
  let J := u * L
  let Q := (X + 1).primesBelow
  let P := Q.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y)
  let R := Q.filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)
  have ht : 128 ≤ t := by dsimp [t]; omega
  have hL0 : 0 < L := by omega
  have hJ : 0 < J := Nat.mul_pos hu hL0
  have hTL : 0 < t * L := Nat.mul_pos (by omega) hL0
  have hXY : X = A * Y := by
    dsimp [X, A, Y]
    rw [← pow_add]
    congr 1
    have : t - 5 + 5 = t := by omega
    nlinarith
  have hXb : X = 2 ^ L * b := by
    dsimp [X, b]
    rw [← pow_add]
    congr 1
    have : t - 1 + 1 = t := by omega
    nlinarith
  have hAX : A ≤ X := by
    dsimp [A, X]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L (by omega))
  have hscale : 12 * (t * L) ≤ 2 ^ L := by
    calc
      12 * (t * L) ≤ L ^ 2 := by dsimp [t]; nlinarith
      _ ≤ _ := sq_le_two_pow L hL
  have hXscale : 12 * (t * L) * b ≤ X := by
    rw [hXb]
    exact Nat.mul_le_mul_right b hscale
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hTR : (0 : ℝ) < (t * L : ℕ) := by exact_mod_cast hTL
  have hK : 0 < totientRatioAverageConstant := Real.exp_pos _
  have hH : (harmonic A : ℝ) ≤ (1 + 5 * Real.log 2) * L := by
    have h := harmonic_le_one_add_log A
    have hlogA : Real.log (A : ℝ) = (5 * (L : ℝ)) * Real.log 2 := by
      dsimp [A]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      rfl
    rw [hlogA] at h
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    nlinarith
  have hmain : 16 * totientRatioAverageConstant * X * (harmonic A : ℝ) /
      ((J : ℝ) * Real.log 2) ^ 2 ≤ (X : ℝ) / (4 * (t * L : ℕ)) := by
    have hden : 0 < ((J : ℝ) * Real.log 2) ^ 2 :=
      sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) hc)
    calc
      _ ≤ 16 * totientRatioAverageConstant * X * ((1 + 5 * Real.log 2) * L) /
          ((J : ℝ) * Real.log 2) ^ 2 := by
        apply div_le_div_of_nonneg_right ?_ hden.le
        exact mul_le_mul_of_nonneg_left hH (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hTR)).mpr
        have h := mul_le_mul_of_nonneg_right huC
          (show 0 ≤ (X : ℝ) * (u : ℝ) * (L : ℝ) ^ 2 by positivity)
        dsimp [J, t]
        push_cast
        convert h using 1 <;> ring
  have herrorN : A * (2 ^ (64 * J) + 2 ^ (16 * J) + 1) ≤ 3 * b := by
    have hp16 : 2 ^ (16 * J) ≤ 2 ^ (64 * J) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp1 : 1 ≤ 2 ^ (64 * J) := Nat.one_le_pow _ _ (by decide)
    have hpow : A * 2 ^ (64 * J) ≤ b := by
      dsimp [A, J, b]
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      have hcoef : 64 * u + 5 ≤ t - 1 := by dsimp [t]; omega
      nlinarith
    nlinarith
  have herror : (A : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) ≤
      (X : ℝ) / (4 * (t * L : ℕ)) := by
    have h1 : (A : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) ≤ 3 * (b : ℝ) := by
      exact_mod_cast herrorN
    apply h1.trans
    apply (le_div_iff₀ (mul_pos (by norm_num) hTR)).mpr
    have h := (Nat.cast_le (α := ℝ)).mpr hXscale
    push_cast at h ⊢
    nlinarith
  have hrough : (R.card : ℝ) ≤ (X : ℝ) / (2 * (t * L : ℕ)) := by
    have hb := rough_shifted_prime_explicit_bound X A Y J (by dsimp [Y]; positivity)
      hXY.le hAX hJ
    calc
      (R.card : ℝ) ≤ _ := hb
      _ ≤ (X : ℝ) / (4 * (t * L : ℕ)) + (X : ℝ) / (4 * (t * L : ℕ)) :=
        add_le_add hmain herror
      _ = _ := by ring
  have hpartition : P.card + R.card = Q.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hprime : X ≤ (t * L) * (Q.card + 1) := by
    have h := dyadic_prime_count_lower (t * L - 1)
    rwa [Nat.sub_add_cancel (show 1 ≤ t * L from hTL)] at h
  have hprimeR : (X : ℝ) ≤ ((t * L : ℕ) : ℝ) * ((P.card : ℝ) + (R.card : ℝ) + 1) := by
    rw [← hpartition] at hprime
    exact_mod_cast hprime
  have hr := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hTR)).mp hrough
  have hfinal : (X : ℝ) ≤ 2 * ((t * L : ℕ) : ℝ) * ((P.card : ℝ) + 1) := by
    nlinarith
  exact_mod_cast hfinal

end Sieve

lemma Sieve.exists_eventual_full_smooth_shifted_prime_density :
    ∃ t : ℕ, 6 ≤ t ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ (t * L) ≤ 2 * (t * L) * (P.card + 1) := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨u, hu⟩ := exists_nat_gt (max 1
    (8192 * Sieve.totientRatioAverageConstant * (1 + 5 * Real.log 2) / (Real.log 2) ^ 2))
  have hu1 : (1 : ℝ) < u := (le_max_left _ _).trans_lt hu
  have hu0 : 0 < u := by exact_mod_cast (show (0 : ℝ) < u by linarith)
  have huC : 8192 * Sieve.totientRatioAverageConstant * (1 + 5 * Real.log 2) ≤
      (u : ℝ) * (Real.log 2) ^ 2 :=
    ((div_lt_iff₀ (sq_pos_of_pos hc)).mp ((le_max_right _ _).trans_lt hu)).le
  refine ⟨128 * u, by omega, max 4 (1536 * u), ?_⟩
  intro L hL
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL
  have hLu : 1536 * u ≤ L := (le_max_right _ _).trans hL
  let P := ((2 ^ (128 * u * L) + 1).primesBelow).filter
    (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * u - 5) * L)))
  refine ⟨P, ?_, Sieve.smooth_shifted_primes_dyadic_full_count u L hu0 hL4 hLu huC⟩
  intro p hp
  obtain ⟨hpQ, hpS⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
  exact ⟨hprime, by omega, hpS⟩


/-- Retaining the logarithmic denominator in the sieve count permits the
counting exponent at the fixed smoothness scale to approach one. -/
lemma infinite_g_gt_of_scaled_eventual_full_density (t m : ℕ) (ht : 6 ≤ t) (hm : 1 ≤ m)
    (L₀ : ℕ) (H : ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ (t * L) ≤ 2 * (t * L) * (P.card + 1)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((5 * (m : ℝ) - 3) / ((t : ℝ) * m))}.Infinite := by
  have hgap : t * m = (t - 5) * m + 5 * m := by
    have hcoeff : t = (t - 5) + 5 := by omega
    conv_lhs => rw [hcoeff]
    ring
  have hinf := infinite_g_gt_of_general_dyadic_density (t * m) (t * m - 1) ((t - 5) * m)
    (by omega) (by omega) (by omega) (by
      intro M
      let L := max M (max L₀ (max 4 (2 * (t * m) + 1)))
      have hLM : M ≤ L := le_max_left _ _
      have hL₀ : L₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
      have hL4 : 4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hLbig : 2 * (t * m) + 1 ≤ L :=
        (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hL₀' : L₀ ≤ m * L := hL₀.trans (by nlinarith : L ≤ m * L)
      obtain ⟨P, hP, hcard⟩ := H (m * L) hL₀'
      refine ⟨L, hLM, P, by simpa only [mul_assoc] using hP, ?_⟩
      have hsmall : 2 * (t * m * L) < 2 ^ L := by
        calc
          2 * (t * m * L) < L ^ 2 := by nlinarith
          _ ≤ _ := Sieve.sq_le_two_pow L hL4
      have hX : 2 ^ (t * (m * L)) = 2 ^ L * 2 ^ ((t * m - 1) * L) := by
        rw [← pow_add]
        congr 1
        have htpos : 1 ≤ t * m := by nlinarith
        have hcoeff : t * m - 1 + 1 = t * m := by omega
        nlinarith
      by_contra h
      have hPsmall : P.card + 1 ≤ 2 ^ ((t * m - 1) * L) := by omega
      have hle := hcard.trans (Nat.mul_le_mul_left (2 * (t * (m * L))) hPsmall)
      rw [hX] at hle
      have hpos : 0 < 2 ^ ((t * m - 1) * L) := by positivity
      have hbad : 2 ^ L ≤ 2 * (t * (m * L)) := Nat.le_of_mul_le_mul_right hle hpos
      exact (not_le_of_gt hsmall) (by simpa only [mul_assoc] using hbad))
  have hnat : t * m - 1 - (t - 5) * m - 2 = 5 * m - 3 := by omega
  have hnum : ((t * m - 1 - (t - 5) * m - 2 : ℕ) : ℝ) = 5 * (m : ℝ) - 3 := by
    rw [hnat, Nat.cast_sub (by omega : 3 ≤ 5 * m)]
    push_cast
    rfl
  simpa only [hnum, Nat.cast_mul] using hinf

lemma infinite_g_gt_of_eventual_full_density (t : ℕ) (ht : 6 ≤ t)
    (L₀ : ℕ) (H : ∀ L : ℕ, L₀ ≤ L → ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ (t * L) ≤ 2 * (t * L) * (P.card + 1))
    (δ : ℝ) (hδ : 0 < δ) (hδt : δ < 5 / (t : ℝ)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hprod : δ * t < 5 := (lt_div_iff₀ htR).mp hδt
  have hgap : 0 < 5 - (t : ℝ) * δ := by nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (3 / (5 - (t : ℝ) * δ) + 1)
  have hmR : (1 : ℝ) < m := by have := div_pos (by norm_num : (0 : ℝ) < 3) hgap; linarith
  have hm1 : 1 ≤ m := by exact_mod_cast hmR.le
  have hmpos : (0 : ℝ) < m := by linarith
  have hprod' : 3 < (5 - (t : ℝ) * δ) * m := by
    have h := (div_lt_iff₀ hgap).mp (show 3 / (5 - (t : ℝ) * δ) < m by linarith)
    simpa only [mul_comm] using h
  have hexp : δ ≤ (5 * (m : ℝ) - 3) / ((t : ℝ) * m) := by
    apply (le_div_iff₀ (mul_pos htR hmpos)).mpr
    nlinarith
  have hinf := infinite_g_gt_of_scaled_eventual_full_density t m ht hm1 L₀ H
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans_lt hn.1

/-- The same unconditional sieve gives every exponent strictly below `5/t`
for one fixed `t`. This recovers the full difference between the counting
and smoothness exponents of that input, but does not give exponents approaching one. -/
theorem exists_fixed_scale_full_exponents :
    ∃ t : ℕ, 6 ≤ t ∧ ∀ δ : ℝ, 0 < δ → δ < 5 / (t : ℝ) →
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  obtain ⟨t, ht, L₀, H⟩ := Sieve.exists_eventual_full_smooth_shifted_prime_density
  exact ⟨t, ht, fun δ hδ hδt => infinite_g_gt_of_eventual_full_density t ht L₀ H δ hδ hδt⟩

#print axioms infinite_g_gt_of_general_dyadic_density

#print axioms exists_fixed_scale_improved_exponents
#print axioms Sieve.smooth_shifted_primes_dyadic_full_count
#print axioms Sieve.exists_eventual_full_smooth_shifted_prime_density
#print axioms infinite_g_gt_of_scaled_eventual_full_density
#print axioms exists_fixed_scale_full_exponents

end Erdos821
