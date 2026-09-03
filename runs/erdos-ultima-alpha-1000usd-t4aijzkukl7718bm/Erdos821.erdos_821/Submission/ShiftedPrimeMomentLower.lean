import Submission.ShiftedPrimeMomentPole

/-!
# Cofinal unconditional lower bounds for shifted-prime divisor moments

The lower bound exceeds every fixed multiple of X/log X. It does not
supply the higher logarithmic order needed for the smooth-prime argument.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

/-- An elementary Abelian upper bound from a uniform linear bound on
nonnegative partial sums. Dyadic blocks avoid any Tauberian hypothesis. -/
lemma dirichlet_le_of_linear_sum (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hS : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, f n) ≤ C*N)
    (s : ℝ) (hs : 1 < s) (hser : Summable (fun n : ℕ => f n/(n : ℝ)^s)) :
    (∑' n : ℕ, f n/(n : ℝ)^s) ≤ 2*C/(1-(2 : ℝ)^(1-s)) := by
  let g : ℕ → ℝ := fun n => f n/(n : ℝ)^s
  let r : ℝ := (2 : ℝ)^(1-s)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : ∀ n, 0 ≤ g n := fun n => div_nonneg (hf n) (by positivity)
  have hb (j : ℕ) : (∑ n ∈ Finset.Ico (2^j) (2^(j+1)), g n) ≤ 2*C*r^j := by
    have hpow : (0 : ℝ) < (2^j : ℕ) := by positivity
    calc
      _ ≤ (∑ n ∈ Finset.Ico (2^j) (2^(j+1)), f n)/((2^j : ℕ) : ℝ)^s := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_left (hf n) (by positivity)
        exact Real.rpow_le_rpow hpow.le (by exact_mod_cast (Finset.mem_Ico.mp hn).1) (by linarith)
      _ ≤ (C*((2^(j+1) : ℕ) : ℝ))/((2^j : ℕ) : ℝ)^s := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply le_trans _ (hS (2^(j+1)))
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hn
          exact Finset.mem_Icc.mpr ⟨(Nat.one_le_pow _ _ (by decide)).trans h1,h2.le⟩
        · exact fun n _ _ => hf n
      _ = _ := by
        push_cast
        rw [_root_.pow_succ, ← Real.rpow_natCast_mul (by norm_num)]
        dsimp [r]
        rw [← Real.rpow_mul_natCast (by norm_num), sub_mul, one_mul, Real.rpow_sub (by norm_num)]
        simp only [Real.rpow_natCast]
        rw [mul_comm (s : ℝ) (j : ℝ)]
        ring
  have he (J : ℕ) : (∑ n ∈ Finset.range (2^J), g n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2^j) (2^(j+1)), g n := by
    induction J with
    | zero => simp [g,hf0]
    | succ J ih =>
      rw [← Finset.sum_range_add_sum_Ico g (Nat.pow_le_pow_right (by decide) (Nat.le_succ J)),
        ih, Finset.sum_range_succ]
  apply hser.tsum_le_of_sum_range_le
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range (2^N), g n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono Nat.lt_two_pow_self.le)
        (fun n _ _ => hg n)
    _ = _ := he N
    _ ≤ ∑ j ∈ Finset.range N, 2*C*r^j := Finset.sum_le_sum (fun j _ => hb j)
    _ ≤ ∑' j : ℕ, 2*C*r^j :=
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (2*C)).sum_le_tsum _
        (fun j _ => by positivity)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; rfl

lemma normalized_dirichlet_le_of_linear_sum (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hS : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, f n) ≤ C*N)
    (s : ℝ) (hs : s ∈ Set.Ioc (1 : ℝ) 2) (hser : Summable (fun n : ℕ => f n/(n : ℝ)^s)) :
    (s-1)*(∑' n : ℕ, f n/(n : ℝ)^s) ≤ 4*C/Real.log 2 := by
  let r : ℝ := (2 : ℝ)^(1-s)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hs.1])
  have hlo : (1/2 : ℝ) ≤ r := by
    calc
      _ = (2 : ℝ)^(-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hs.2])
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : -Real.log r = (s-1)*Real.log 2 := by dsimp [r]; rw [Real.log_rpow (by norm_num)]; ring
  have hlog := Real.one_sub_inv_le_log_of_pos hr
  have hlin : (s-1)*Real.log 2 ≤ 2*(1-r) := by
    have hbound : r⁻¹-1 ≤ 2*(1-r) := by
      apply (mul_le_mul_iff_left₀ hr).mp
      simp only [sub_mul, inv_mul_cancel₀ hr.ne']
      nlinarith [mul_nonneg (show 0 ≤ 2*r-1 by linarith) (show 0 ≤ 1-r by linarith)]
    linarith
  have hb := mul_le_mul_of_nonneg_left (dirichlet_le_of_linear_sum f hf hf0 C hC hS s hs.1 hser)
    (by linarith [hs.1] : 0 ≤ s-1)
  apply hb.trans
  change (s-1)*(2*C/(1-r)) ≤ _
  apply (le_div_iff₀ hlog2).mpr
  have h := mul_le_mul_of_nonneg_left (a := 2*C/(1-r)) hlin
    (div_nonneg (by positivity) (sub_nonneg.mpr hr1.le))
  convert h using 1 <;> field_simp [sub_ne_zero.mpr hr1.ne']
  all_goals ring

lemma sum_primeMomentWeight_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, primeMomentWeight k n) ≤ Real.log X*shiftedPrimeMoment k X := by
  have he : (∑ n ∈ Finset.Icc 1 X, primeMomentWeight k n) + nonprimeMangoldtMoment k X =
      shiftedMangoldtMoment k X := by
    rw [← sum_nonprimeMomentWeight, ← Finset.sum_add_distrib]
    simp only [momentWeight_add, shiftedMangoldtMoment]
  have h := mangoldtMoment_le_primeMoment_add_nonprime k X
  linarith

/-- The average shifted-prime divisor weight exceeds every fixed constant
along arbitrarily large cutoffs. No logarithmic growth rate is supplied. -/
theorem frequently_shiftedPrimeMoment_gt (k : ℕ) (A : ℝ) :
    ∃ᶠ X : ℕ in atTop, A*(X : ℝ) < Real.log X*shiftedPrimeMoment (k+2) X := by
  by_contra h
  have he : ∀ᶠ X : ℕ in atTop, Real.log X*shiftedPrimeMoment (k+2) X ≤ A*(X : ℝ) := by
    simpa only [not_lt] using not_frequently.mp h
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  let f := primeMomentWeight (k+2)
  let D : ℝ := ∑ n ∈ Finset.Icc 1 B, f n
  let C : ℝ := max 0 (max A D)
  have hC : 0 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hsum (X : ℕ) : (∑ n ∈ Finset.Icc 1 X, f n) ≤ C*(X : ℝ) := by
    by_cases hBX : B ≤ X
    · exact ((sum_primeMomentWeight_le (k+2) X).trans (hB X hBX)).trans
        (mul_le_mul_of_nonneg_right hAC (Nat.cast_nonneg X))
    by_cases hX : X = 0
    · subst X
      simp
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    calc
      _ ≤ D := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
        (fun n _ _ => primeMomentWeight_nonneg _ _)
      _ ≤ C := hDC
      _ ≤ _ := le_mul_of_one_le_right hC hX1
  have hup : ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*shiftedPrimeDirichlet (k+2) s ≤ 4*C/Real.log 2 := by
    have htwo : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 :=
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [eventually_mem_nhdsWithin,htwo] with s hs hs2
    apply normalized_dirichlet_le_of_linear_sum f (primeMomentWeight_nonneg _) (by simp [f,primeMomentWeight])
      C hC hsum s ⟨hs,hs2.le⟩ (shiftedPrimeDirichlet_summable (k+1) s hs)
  have hlo := (tendsto_shiftedPrimeDirichlet_residue k).eventually (eventually_gt_atTop (4*C/Real.log 2))
  obtain ⟨s,hs1,hs2⟩ := (hup.and hlo).exists
  exact hs1.not_gt hs2

end Erdos821.HigherDivisors
