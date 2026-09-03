import Submission.BinaryNormBound
import Submission.Spec

/-! A uniform upper bound for the full quartic representation count. -/
namespace Erdos322Research

private lemma le_fourth_root {x n : ℕ} (h : x ^ 4 ≤ n) : x ≤ n.sqrt.sqrt := by
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  convert h using 1; ring

private lemma fourth_root_box_bound {n : ℕ} (hn : 0 < n) :
    ((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  let r := n.sqrt.sqrt
  have hr : 0 < r := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hn)
  have hr4 : r ^ 4 ≤ n := by
    have h1 := Nat.sqrt_le n.sqrt
    have h2 := Nat.sqrt_le n
    calc
      r ^ 4 = (r * r) ^ 2 := by ring
      _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ n := by simpa [pow_two] using h2
  have hnr : (0 : ℝ) ≤ n := by positivity
  have hr4r : (r : ℝ) ^ 4 ≤ n := by exact_mod_cast hr4
  have hr2r : (r : ℝ) ^ 2 ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnr]
    convert hr4r using 1; ring
  have hbox : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := by
    have hle : r + 1 ≤ 2 * r := by omega
    have hpow := Nat.pow_le_pow_left hle 2
    have hcast : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r : ℕ) : ℝ) ^ 2 := by exact_mod_cast hpow
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hcast
  calc
    ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := hbox
    _ ≤ 4 * Real.sqrt n := by gcongr
    _ = 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]

private def quarticReps (n : ℕ) : Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ ∑ i, (a i : ℕ) ^ 4 = n)

private def firstPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 0 : ℕ), (a 1 : ℕ))

private def lastSquaredPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 2 : ℕ) ^ 2, (a 3 : ℕ) ^ 2)

private lemma firstPair_image_bound {n : ℕ} (hn : 0 < n) :
    (((quarticReps n).image firstPair).card : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  classical
  have hsubset : (quarticReps n).image firstPair ⊆
      Finset.range (n.sqrt.sqrt + 1) ×ˢ Finset.range (n.sqrt.sqrt + 1) := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    simp only [quarticReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have h0 : (a 0 : ℕ) ^ 4 ≤ n := by
      exact (Finset.single_le_sum (f := fun i : Fin 4 ↦ (a i : ℕ) ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)).trans_eq ha
    have h1 : (a 1 : ℕ) ^ 4 ≤ n := by
      exact (Finset.single_le_sum (f := fun i : Fin 4 ↦ (a i : ℕ) ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)).trans_eq ha
    simp only [Finset.mem_product, Finset.mem_range, firstPair]
    exact ⟨by have := le_fourth_root h0; omega, by have := le_fourth_root h1; omega⟩
  have hcard : ((quarticReps n).image firstPair).card ≤ (n.sqrt.sqrt + 1) ^ 2 := by
    simpa [pow_two] using Finset.card_le_card hsubset
  exact (by exact_mod_cast hcard : (((quarticReps n).image firstPair).card : ℝ) ≤
    ((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 2).trans (fourth_root_box_bound hn)

private lemma quartic_fiber_bound (n : ℕ) (q : ℕ × ℕ) :
    ((quarticReps n).filter (fun a ↦ firstPair a = q)).card ≤
      (binaryNormSolutions 1 (n - q.1 ^ 4 - q.2 ^ 4)).card := by
  classical
  apply Finset.card_le_card_of_injOn lastSquaredPair
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, quarticReps,
      Finset.mem_univ, true_and] at ha
    have h0 : (a 0 : ℕ) = q.1 := congrArg Prod.fst ha.2
    have h1 : (a 1 : ℕ) = q.2 := congrArg Prod.snd ha.2
    have hsum := ha.1
    simp only [Fin.sum_univ_four, h0, h1] at hsum
    apply (mem_binaryNormSolutions (by decide) _).mpr
    change ((a 2 : ℕ) ^ 2) ^ 2 + 1 * ((a 3 : ℕ) ^ 2) ^ 2 = _
    norm_num only [one_mul, ← pow_mul]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have h0 := congrArg Prod.fst (ha.2.trans hb.2.symm)
    have h1 := congrArg Prod.snd (ha.2.trans hb.2.symm)
    have h2 := congrArg Prod.fst hab
    have h3 := congrArg Prod.snd hab
    have ha0 : (a 0 : ℕ) = (b 0 : ℕ) := h0
    have ha1 : (a 1 : ℕ) = (b 1 : ℕ) := h1
    have ha2 : (a 2 : ℕ) = (b 2 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h2
    have ha3 : (a 3 : ℕ) = (b 3 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h3
    funext i
    apply Fin.ext
    fin_cases i <;> assumption

/-- An elementary uniform bound for all quartic representations. The exponent
`1/2 + ε` is not small enough to settle the conjecture. -/
theorem quartic_count_upper_half (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (Erdos322.representationCount 4 n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε : ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial_general_up_to (by decide : 0 < 1) ε hε
  refine ⟨4 * C * (2 : ℝ) ^ ε, by positivity, fun n hn ↦ ?_⟩
  let S := quarticReps n
  let I := S.image firstPair
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n + 1 : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * (n : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnr.le]
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
  have hfiber (q : ℕ × ℕ) (hq : q ∈ I) :
      (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) ≤ C * (n + 1 : ℝ) ^ ε := by
    have hcard : (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) ≤
        (binaryNormSolutions 1 (n - q.1 ^ 4 - q.2 ^ 4)).card := by
      exact_mod_cast quartic_fiber_bound n q
    exact hcard.trans (hbound n (n - q.1 ^ 4 - q.2 ^ 4) (by omega))
  calc
    (Erdos322.representationCount 4 n : ℝ) =
        ∑ q ∈ I, (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image firstPair S
    _ ≤ ∑ q ∈ I, C * (n + 1 : ℝ) ^ ε := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ) * (C * (n + 1 : ℝ) ^ ε) := by simp
    _ ≤ (4 * (n : ℝ) ^ (1 / 2 : ℝ)) * (C * ((2 : ℝ) ^ ε * (n : ℝ) ^ ε)) := by
      exact mul_le_mul (firstPair_image_bound hn) (mul_le_mul_of_nonneg_left hpow hC.le)
        (by positivity) (by positivity)
    _ = (4 * C * (2 : ℝ) ^ ε) * (n : ℝ) ^ (1 / 2 + ε : ℝ) := by
      rw [Real.rpow_add hnr]
      ring


/-- Exponents larger than `1/2` cannot witness the quartic conjecture. -/
theorem quartic_large_exponents_finite {c : ℝ} (hc : 1 / 2 < c) :
    {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Finite := by
  let δ : ℝ := (c - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C,hC,hbound⟩ := quartic_count_upper_half δ hδ
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop C)
  apply (Set.finite_Iio (max N 1)).subset
  intro n hn
  by_contra hnot
  have hlarge : max N 1 ≤ n := by simpa only [Set.mem_Iio, not_lt] using hnot
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdom := hN n (by omega)
  have hp : (n : ℝ) ^ δ * (n : ℝ) ^ (1 / 2 + δ) = (n : ℝ) ^ c := by
    rw [← Real.rpow_add hnr]
    congr 1
    dsimp [δ]
    ring
  have hle : (Erdos322.representationCount 4 n : ℝ) ≤ (n : ℝ) ^ c := by
    calc
      (Erdos322.representationCount 4 n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + δ) := hbound n hnpos
      _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 / 2 + δ) :=
        mul_le_mul_of_nonneg_right hdom (by positivity)
      _ = (n : ℝ) ^ c := hp
  exact not_lt_of_ge hle hn

theorem quartic_peak_exponent_le_half {c : ℝ}
    (h : {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Infinite) : c ≤ 1 / 2 := by
  by_contra hnot
  exact h (quartic_large_exponents_finite (lt_of_not_ge hnot))

end Erdos322Research
