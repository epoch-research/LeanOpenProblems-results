import Submission.Sublinear

/-!
# Rankin bounds for smooth integers and inverse-totient fibers

Auxiliary estimates only. Savings by powers of a logarithm do not constitute
an upper bound by a fixed power below one, and do not disprove Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821
open Sieve

noncomputable def smoothRankinConstant (s u : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ (-s))⁻¹ * ∑' a : ℕ, (a : ℝ) ^ (-u)

lemma smoothRankinConstant_nonneg {s u : ℝ} (hs : 0 < s) :
    0 ≤ smoothRankinConstant s u := by
  have hr : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact mul_nonneg (inv_nonneg.mpr (by linarith))
    (tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _))

lemma smooth_euler_product_le_rankin (y : ℕ) (hy : 0 < y)
    (s u : ℝ) (hs : 0 < s) (hsu : s ≤ u) (hu : 1 < u) :
    (∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹) ≤
      Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := by
  let c : ℝ := (1 - (2 : ℝ) ^ (-s))⁻¹
  have hr : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc : 0 ≤ c := inv_nonneg.mpr (by linarith)
  have hsum : Summable (fun a : ℕ => (a : ℝ) ^ (-u)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hpoint (p : ℕ) (hp : p ∈ y.primesBelow) :
      0 < 1 - (p : ℝ) ^ (-s) ∧
        (1 - (p : ℝ) ^ (-s))⁻¹ ≤ Real.exp (c * (p : ℝ) ^ (-s)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have hpR : (0 : ℝ) < p := by linarith
    have hpr : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hz : 0 < 1 - (p : ℝ) ^ (-s) := by linarith
    refine ⟨hz, ?_⟩
    calc
      (1 - (p : ℝ) ^ (-s))⁻¹ = 1 + (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)) := by
        field_simp
        ring
      _ ≤ 1 + c * (p : ℝ) ^ (-s) := by
        apply add_le_add_right
        dsimp [c]
        rw [mul_comm, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hpR.le _) (by linarith) (by linarith)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (c * (p : ℝ) ^ (-s))
  have hsum_bound : (∑ p ∈ y.primesBelow, (p : ℝ) ^ (-s)) ≤
      (y : ℝ) ^ (u - s) * ∑' a : ℕ, (a : ℝ) ^ (-u) := by
    calc
      (∑ p ∈ y.primesBelow, (p : ℝ) ^ (-s)) ≤
          ∑ p ∈ y.primesBelow, (y : ℝ) ^ (u - s) * (p : ℝ) ^ (-u) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos
        have hpy : (p : ℝ) ≤ y := by exact_mod_cast (Nat.mem_primesBelow.mp hp).1.le
        calc
          (p : ℝ) ^ (-s) = (p : ℝ) ^ (u - s) * (p : ℝ) ^ (-u) := by
            rw [← Real.rpow_add hpR]
            congr 1
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hpR.le hpy (sub_nonneg.mpr hsu)) (Real.rpow_nonneg hpR.le _)
      _ = (y : ℝ) ^ (u - s) * ∑ p ∈ y.primesBelow, (p : ℝ) ^ (-u) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) hsum)
        (Real.rpow_nonneg (Nat.cast_nonneg y) _)
  calc
    (∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹) ≤
        ∏ p ∈ y.primesBelow, Real.exp (c * (p : ℝ) ^ (-s)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (hpoint p hp).1.le
      · intro p hp
        exact (hpoint p hp).2
    _ = Real.exp (c * ∑ p ∈ y.primesBelow, (p : ℝ) ^ (-s)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (c * ((y : ℝ) ^ (u - s) * ∑' a : ℕ, (a : ℝ) ^ (-u))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum_bound hc)
    _ = _ := by congr 1; dsimp [smoothRankinConstant, c]; ring

lemma card_smooth_family_le_rankin (S : Finset ℕ) (M y : ℕ)
    (hM : 0 < M) (hy : 0 < y) (s u : ℝ) (hs : 0 < s) (hsu : s ≤ u) (hu : 1 < u)
    (hS : ∀ m ∈ S, m ≤ M ∧ m ∈ Nat.smoothNumbers y) :
    (S.card : ℝ) ≤ (M : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := by
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ) ^ (-s)
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [Nat.cast_mul]
      exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) }
  have hsmall {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ) ^ (-s)‖ < 1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hind := hasSum_subtype_iff_indicator.mp
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hsmall y).2
  have hsum : (∑ m ∈ S, (m : ℝ) ^ (-s)) ≤
      ∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹ := by
    calc
      (∑ m ∈ S, (m : ℝ) ^ (-s)) = ∑ m ∈ S, (Nat.smoothNumbers y).indicator f m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (Set.indicator_of_mem (hS m hm).2 f).symm
      _ ≤ ∑' m, (Nat.smoothNumbers y).indicator f m :=
        Summable.sum_le_tsum _ (fun m _ => Set.indicator_nonneg
          (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _) _) hind.summable
      _ = _ := hind.tsum_eq
  calc
    (S.card : ℝ) = ∑ _m ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ S, (M : ℝ) ^ s * (m : ℝ) ^ (-s) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (hS m hm).2.1
      calc
        (1 : ℝ) = (m : ℝ) ^ s * (m : ℝ) ^ (-s) := by
          rw [← Real.rpow_add hmR, add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hmR.le
          (by exact_mod_cast (hS m hm).1) hs.le) (Real.rpow_nonneg hmR.le _)
    _ = (M : ℝ) ^ s * ∑ m ∈ S, (m : ℝ) ^ (-s) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M : ℝ) ^ s * ∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (smooth_euler_product_le_rankin y hy s u hs hsu hu)
      (Real.rpow_nonneg (Nat.cast_nonneg M) _)

lemma bounded_totient_fiber_card_le_rankin (S : Finset ℕ) (n M y : ℕ) (hM : 0 < M) (hy : 0 < y)
    (s u : ℝ) (hs : 0 < s) (hsu : s ≤ u) (hu : 1 < u)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M ∧ Nat.totient m = n) :
    (S.card : ℝ) ≤ 3 * (M : ℝ) / y + (M : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := by
  let A := S.filter (fun m => m ∈ Nat.smoothNumbers y)
  let B := S.filter (fun m => ∃ d : ℕ, y ≤ d ∧ d ^ 2 ∣ m)
  let D := S.filter (fun m => ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p ∣ m ∧ ¬p ^ 2 ∣ m)
  have hsub : S ⊆ A ∪ (B ∪ D) := by
    intro m hm
    by_cases hsm : m ∈ Nat.smoothNumbers y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hsm⟩)
    · have hnot : ¬∀ p : ℕ, p.Prime → p ∣ m → p < y := by
        simpa only [Nat.mem_smoothNumbers'] using hsm
      push_neg at hnot
      obtain ⟨p, hp, hpm, hyp⟩ := hnot
      apply Finset.mem_union_right
      by_cases hp2m : p ^ 2 ∣ m
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, p, hyp, hp2m⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, p, hp, hyp, hpm, hp2m⟩)
  have hA : (A.card : ℝ) ≤ (M : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := by
    apply card_smooth_family_le_rankin A M y hM hy s u hs hsu hu
    intro m hm
    obtain ⟨hmS, hmSm⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).2.1, hmSm⟩
  have hB : (B.card : ℝ) ≤ 2 * (M : ℝ) / y := by
    apply card_large_square_divisor_le B M y hy
    intro m hm
    obtain ⟨hmS, hmD⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, (hS m hmS).2.1, hmD⟩
  have hD : (D.card : ℝ) ≤ (M : ℝ) / y := by
    apply card_fiber_large_prime_once_le D n M y hy
    intro m hm
    obtain ⟨hmS, hmD⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, (hS m hmS).2.1, (hS m hmS).2.2, hmD⟩
  have hcard : S.card ≤ A.card + (B.card + D.card) :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hcardR : (S.card : ℝ) ≤ (A.card : ℝ) + (B.card + D.card) := by exact_mod_cast hcard
  have hAR : (A.card : ℝ) ≤ (M : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := hA
  calc
    (S.card : ℝ) ≤ (A.card : ℝ) + (B.card + D.card) := hcardR
    _ ≤ (M : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) + (2 * (M : ℝ) / y + M / y) :=
      add_le_add hAR (add_le_add hB hD)
    _ = _ := by ring

lemma g_le_linear_coeff_rankin (n A y : ℕ) (hn : 0 < n) (hA : 0 < A) (hy : 0 < y)
    (s u : ℝ) (hs : 0 < s) (hsu : s ≤ u) (hu : 1 < u) :
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n +
      ((A * n : ℕ) : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) := by
  let S := (finite_totient_fiber n).toFinset
  let L := S.filter (fun m => m ≤ A * n)
  let H := S.filter (fun m => ¬m ≤ A * n)
  have hphi : ∀ m ∈ S, Nat.totient m = n := fun m hm => (finite_totient_fiber n).mem_toFinset.mp hm
  have hL := bounded_totient_fiber_card_le_rankin L n (A * n) y (Nat.mul_pos hA hn) hy s u hs hsu hu (by
    intro m hm
    obtain ⟨hmS, hmB⟩ := Finset.mem_filter.mp hm
    refine ⟨Nat.totient_pos.mp ?_, hmB, hphi m hmS⟩
    rwa [hphi m hmS])
  have hH := totient_fiber_tail_card_le H n (A * n) hn (Nat.mul_pos hA hn) (by
    intro m hm
    obtain ⟨hmS, hmB⟩ := Finset.mem_filter.mp hm
    exact ⟨by omega, hphi m hmS⟩)
  have hsub : S ⊆ L ∪ H := by
    intro m hm
    by_cases h : m ≤ A * n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, h⟩)
  have hcard : S.card ≤ L.card + H.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hScard : S.card = g n := (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  rw [hScard] at hcard
  have hcardR : (g n : ℝ) ≤ (L.card : ℝ) + H.card := by exact_mod_cast hcard
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  calc
    (g n : ℝ) ≤ (3 * ((A * n : ℕ) : ℝ) / y + ((A * n : ℕ) : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s))) +
        4 * totientRatioAverageConstant * (n : ℝ) ^ 2 / ((A * n : ℕ) : ℝ) :=
      hcardR.trans (add_le_add hL hH)
    _ = _ := by
      have hcast : ((A * n : ℕ) : ℝ) = (A : ℝ) * n := Nat.cast_mul A n
      rw [hcast]
      field_simp
      <;> ring



lemma eventually_pow_mul_exp_sqrt_le_exp (r : ℕ) (C b : ℝ) (hC : 0 ≤ C) (hb : 0 < b) :
    ∀ᶠ L : ℕ in atTop,
      (L : ℝ) ^ r * Real.exp (C * (L : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.exp (b * L) := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop r (half_pos hb)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (C ^ 2 / (b / 2) ^ 2)
  filter_upwards [hpoly, eventually_ge_atTop N] with L hpolyL hLN
  have hp : (L : ℝ) ^ r ≤ Real.exp (b / 2 * L) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ r),
      Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] using hpolyL
  have hC2 : C ^ 2 ≤ (L : ℝ) * (b / 2) ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (half_pos hb))).mp
    exact hN.le.trans (by exact_mod_cast hLN)
  have hroot : C * Real.sqrt (L : ℝ) ≤ b / 2 * L := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    have hmul := mul_le_mul_of_nonneg_right hC2 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    apply (sq_le_sq₀ (mul_nonneg hC (Real.sqrt_nonneg _)) (by positivity)).mp
    nlinarith
  rw [← Real.sqrt_eq_rpow]
  calc
    (L : ℝ) ^ r * Real.exp (C * Real.sqrt (L : ℝ)) ≤
        Real.exp (b / 2 * L) * Real.exp (b / 2 * L) :=
      mul_le_mul hp (Real.exp_le_exp.mpr hroot) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- At any fixed logarithmic power, the cutoff scale may grow while the
smooth part of the fiber is still absorbed into the error term. -/
theorem g_le_div_pow_of_two_pow_le (r : ℕ) (hr : 1 ≤ r) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ n : ℕ, 2 ^ L ≤ n →
      (g n : ℝ) ≤ (4 * totientRatioAverageConstant + 4) * n / (L : ℝ) ^ r := by
  let e : ℝ := 1 / (8 * (r : ℝ))
  let s : ℝ := 1 - e
  let u : ℝ := 1 + e
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e < 1 := by
    dsimp [e]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hsu : s ≤ u := by dsimp [s, u]; linarith
  have hu : 1 < u := by dsimp [u]; linarith
  let C := smoothRankinConstant s u
  have hC : 0 ≤ C := smoothRankinConstant_nonneg hs
  have hb : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    (eventually_pow_mul_exp_sqrt_le_exp (2 * r) C (e * Real.log 2) hC hb)
  refine ⟨max 1 L₀, ?_⟩
  intro L hL n hn
  have hLpos : 0 < L := by have := (le_max_left 1 L₀).trans hL; omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hnpos : 0 < n := (pow_pos (by decide : 0 < (2 : ℕ)) L).trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let A : ℕ := L ^ r
  let y : ℕ := L ^ (2 * r)
  have hA : 0 < A := pow_pos hLpos r
  have hy : 0 < y := pow_pos hLpos (2 * r)
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hyA : (y : ℝ) = (A : ℝ) ^ 2 := by
    dsimp [y, A]
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  have hyscale : (y : ℝ) ^ (u - s) = (L : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp [y]
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg L)]
    congr 1
    dsimp [u, s, e]
    push_cast
    field_simp
    ring
  have hAs : (A : ℝ) ^ s ≤ A := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hA : (1 : ℝ) ≤ A) hs1
  have hbudget : (L : ℝ) ^ (2 * r) * Real.exp (C * (L : ℝ) ^ (1 / 2 : ℝ)) ≤ (n : ℝ) ^ e := by
    calc
      _ ≤ Real.exp ((e * Real.log 2) * L) := hL₀ L ((le_max_right 1 L₀).trans hL)
      _ = ((2 : ℝ) ^ L) ^ e := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) he.le
  have hsmall : ((A * n : ℕ) : ℝ) ^ s * Real.exp (C * (y : ℝ) ^ (u - s)) ≤ (n : ℝ) / A := by
    apply (le_div_iff₀ hAR).mpr
    rw [Nat.cast_mul, Real.mul_rpow hAR.le hnR.le, hyscale]
    calc
      (A : ℝ) ^ s * (n : ℝ) ^ s * Real.exp (C * (L : ℝ) ^ (1 / 2 : ℝ)) * A ≤
          (A : ℝ) * (n : ℝ) ^ s * Real.exp (C * (L : ℝ) ^ (1 / 2 : ℝ)) * A := by
        gcongr
      _ = (n : ℝ) ^ s * ((L : ℝ) ^ (2 * r) * Real.exp (C * (L : ℝ) ^ (1 / 2 : ℝ))) := by
        have hpow : (L : ℝ) ^ (2 * r) = (A : ℝ) ^ 2 := by simpa only [y, Nat.cast_pow] using hyA
        rw [hpow]
        ring
      _ ≤ (n : ℝ) ^ s * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg hnR.le _)
      _ = n := by rw [← Real.rpow_add hnR, show s + e = 1 by dsimp [s]; ring, Real.rpow_one]
  calc
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n +
        ((A * n : ℕ) : ℝ) ^ s * Real.exp (C * (y : ℝ) ^ (u - s)) :=
      g_le_linear_coeff_rankin n A y hnpos hA hy s u hs hsu hu
    _ ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n + (n : ℝ) / A :=
      add_le_add_right hsmall _
    _ = (4 * totientRatioAverageConstant + 4) * n / (A : ℝ) := by
      rw [hyA]
      field_simp
      ring
    _ = _ := by rw [show (A : ℝ) = (L : ℝ) ^ r by dsimp [A]; push_cast; rfl]

/-- The inverse-totient multiplicity admits a saving by every fixed positive
integer power of the binary logarithm. This is not a fixed power saving in `n`. -/
theorem eventually_g_le_div_log_pow (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ (4 * totientRatioAverageConstant + 4) * n / (Nat.log 2 n : ℝ) ^ r := by
  obtain ⟨L₀, hL₀⟩ := g_le_div_pow_of_two_pow_le r hr
  filter_upwards [eventually_ge_atTop (2 ^ L₀), eventually_ge_atTop 1] with n hn hn1
  exact hL₀ (Nat.log 2 n) (Nat.le_log_of_pow_le (by decide) hn) n
    (Nat.pow_log_le_self 2 (by omega))


lemma tendsto_nat_log_two_atTop : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro L
  exact ⟨2 ^ L, fun n hn => Nat.le_log_of_pow_le (by decide) hn⟩

/-- Any fixed power of the binary logarithm times `g(n)` is still `o(n)`.
This upper bound remains compatible with Erdős 821. -/
theorem g_mul_log_pow_isLittleO_id (r : ℕ) :
    (fun n : ℕ => (g n : ℝ) * (Nat.log 2 n : ℝ) ^ r) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  let K : ℝ := 4 * totientRatioAverageConstant + 4
  have hlog : Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_log_two_atTop
  filter_upwards [eventually_g_le_div_log_pow (r + 1) (by omega),
    hlog.eventually_ge_atTop (max 1 (K / c))] with n hg hnL
  have hL1 : (1 : ℝ) ≤ Nat.log 2 n := (le_max_left _ _).trans hnL
  have hL : (0 : ℝ) < Nat.log 2 n := by linarith
  have hK : K ≤ c * (Nat.log 2 n : ℝ) := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hnL)
    simpa only [mul_comm] using h
  have hmul : (g n : ℝ) * (Nat.log 2 n : ℝ) ^ (r + 1) ≤ K * n :=
    (le_div_iff₀ (pow_pos hL (r + 1))).mp hg
  have hmain : (g n : ℝ) * (Nat.log 2 n : ℝ) ^ r ≤ c * n := by
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      (g n : ℝ) * (Nat.log 2 n : ℝ) ^ r * (Nat.log 2 n : ℝ) =
          (g n : ℝ) * (Nat.log 2 n : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
      _ ≤ K * n := hmul
      _ ≤ (c * (Nat.log 2 n : ℝ)) * n := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg n)
      _ = _ := by ring
  simpa only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (g n : ℝ) * (Nat.log 2 n : ℝ) ^ r),
    Real.norm_natCast] using hmain

theorem tendsto_g_mul_log_pow_div_self (r : ℕ) :
    Tendsto (fun n : ℕ => ((g n : ℝ) * (Nat.log 2 n : ℝ) ^ r) / n) atTop (nhds 0) :=
  (g_mul_log_pow_isLittleO_id r).tendsto_div_nhds_zero

#print axioms card_smooth_family_le_rankin
#print axioms g_le_linear_coeff_rankin
#print axioms g_le_div_pow_of_two_pow_le
#print axioms eventually_g_le_div_log_pow
#print axioms g_mul_log_pow_isLittleO_id
#print axioms tendsto_g_mul_log_pow_div_self

end Erdos821
