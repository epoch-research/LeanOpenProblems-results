import FormalConjectures.Util.ProblemImports
import Submission.ZetaReg

open Complex Real Finset

noncomputable section

lemma inv_sq_le_sub_inv {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) ^ 2)⁻¹ ≤ ((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hk)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 2) hk), Nat.cast_one]
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hdiff : ((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹ = ((k : ℝ) * ((k : ℝ) - 1))⁻¹ := by
    rw [hcast, inv_sub_inv hkm.ne' hk0.ne']
    field
  rw [hdiff, pow_two]
  refine (inv_le_inv₀ (mul_pos hk0 hk0) (mul_pos hk0 hkm)).mpr ?_
  nlinarith

lemma telescope_inv {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 2 N, (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) = (1 : ℝ) - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp
  | succ N hN ih =>
    have h2 : 2 ≤ N + 1 := Nat.succ_le_succ hN
    rw [sum_Icc_succ_top h2, ih]
    simp

lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n : ℝ) ^ 2)⁻¹ ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hsplit : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k; simp [mem_Icc]; omega
  have : 1 ∉ Icc 2 N := by simp [mem_Icc]
  rw [hsplit, sum_insert this]
  simp only [Nat.cast_one, one_pow, inv_one]
  have hrest : ∑ n ∈ Icc 2 N, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
    refine le_trans (sum_le_sum fun n hn => inv_sq_le_sub_inv (mem_Icc.mp hn).1) ?_
    rw [telescope_inv hN]
    have : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    linarith
  linarith [hrest]

lemma sum_range_inv_sq_le_two (N : ℕ) :
    ∑ n ∈ range N, ((n + 1 : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hmap :
      ∑ n ∈ range N, ((n + 1 : ℝ) ^ 2)⁻¹ =
        ∑ n ∈ Icc 1 N, ((n : ℝ) ^ 2)⁻¹ := by
    refine sum_nbij' (fun n => n + 1) (fun n => n - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_range, mem_Icc] at hn ⊢
      exact ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_iff.mpr hn⟩
    · intro n hn
      simp only [mem_Icc, mem_range] at hn ⊢
      exact Nat.sub_lt_right_of_lt_add hn.1 (Nat.lt_succ_of_le hn.2)
    · intro n hn
      exact Nat.add_sub_cancel n 1
    · intro n hn
      simp only [mem_Icc] at hn
      exact Nat.sub_add_cancel hn.1
    · intro n hn
      simp
  rw [hmap]
  exact sum_inv_sq_le_two N

lemma tsum_inv_sq_le_two :
    ∑' n : ℕ, ((n + 1 : ℝ) ^ 2)⁻¹ ≤ 2 :=
  tsum_le_of_sum_range_le (fun _ => by positivity) sum_range_inv_sq_le_two

lemma summable_inv_sq :
    Summable fun n : ℕ => ((n + 1 : ℝ) ^ 2)⁻¹ := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) (2 : ℝ)).mpr (by norm_num)
  refine h.congr fun n => ?_
  have habs : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
  simp [habs, one_div]

lemma norm_inv_cpow_eq {n : ℕ} (s : ℂ) :
    ‖(1 / ((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℝ) ^ s.re)⁻¹ := by
  have hn : 0 < n + 1 := Nat.succ_pos n
  rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]
  simp

lemma norm_inv_cpow_le_inv_sq {n : ℕ} {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(1 / ((n + 1 : ℕ) : ℂ) ^ s)‖ ≤ ((n + 1 : ℝ) ^ 2)⁻¹ := by
  rw [norm_inv_cpow_eq]
  have hn1 : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.succ_pos n)
  have hpow : (n + 1 : ℝ) ^ (2 : ℝ) ≤ (n + 1 : ℝ) ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hpos : 0 < (n + 1 : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hinv : ((n + 1 : ℝ) ^ s.re)⁻¹ ≤ ((n + 1 : ℝ) ^ (2 : ℝ))⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hpos hpow) hpos).mpr hpow
  have hcast : (n + 1 : ℝ) ^ (2 : ℝ) = (n + 1 : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, Nat.cast_two]
  rwa [hcast] at hinv

lemma norm_zeta_of_re_ge_two {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hs
  have hrep := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hterm : ∀ n : ℕ, ‖(1 / (n + 1 : ℂ) ^ s)‖ ≤ ((n + 1 : ℝ) ^ 2)⁻¹ := by
    intro n
    have heq : (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact norm_inv_cpow_le_inv_sq (n := n) hs
  have hbound := tsum_of_norm_bounded summable_inv_sq.hasSum hterm
  rw [hrep]
  exact le_trans hbound tsum_inv_sq_le_two

end
