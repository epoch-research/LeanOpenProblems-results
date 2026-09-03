import FormalConjecturesUtil

/-!
Near-linear subsets of the squares with no three-term arithmetic progression.
This removes three-value Sidon obstructions, not four-value obstructions.
-/
namespace Erdos773.APFreeExtraction

open Finset Filter
set_option maxHeartbeats 1000000

/-- A reflected translate of a large progression-free interval set meets any
finite interval subset in at least the expected number of elements. -/
lemma reflected_extraction (L : ℕ) (hL : 0 < L)
    (S T : Finset ℕ) (hS : S ⊆ range L) (hT : T ⊆ range L)
    (hfree : ThreeAPFree (T : Set ℕ)) :
    ∃ B ⊆ S, ThreeAPFree (B : Set ℕ) ∧
      (S.card : ℝ) * T.card / (2 * L) ≤ B.card := by
  classical
  let F : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have hmaps : ∀ p ∈ S ×ˢ T, F p ∈ range (2 * L) := by
    intro p hp
    obtain ⟨hs, ht⟩ := mem_product.mp hp
    have hs' := mem_range.mp (hS hs)
    have ht' := mem_range.mp (hT ht)
    apply mem_range.mpr
    dsimp [F]
    omega
  have hpos : (0 : ℝ) < 2 * L := by positivity
  have havg : (range (2 * L)).card •
      ((S.card : ℝ) * T.card / (2 * L)) ≤ (S ×ˢ T).card := by
    simp only [card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, card_product]
    rw [mul_div_cancel₀ _ hpos.ne']
  obtain ⟨k, hk, hcard⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
      (nonempty_range_iff.mpr (by omega)) havg
  let U := (S ×ˢ T).filter (fun p => F p = k)
  let B := U.image Prod.fst
  have hBinj : Set.InjOn Prod.fst (U : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    apply Prod.ext he
    dsimp [F] at hp' hq'
    omega
  have hBcard : B.card = U.card := card_image_of_injOn hBinj
  have hmem {a : ℕ} (ha : a ∈ B) : ∃ t ∈ T, a + t = k := by
    obtain ⟨⟨s,t⟩, hp, he⟩ := mem_image.mp ha
    obtain ⟨hp, hf⟩ := mem_filter.mp hp
    refine ⟨t, (mem_product.mp hp).2, ?_⟩
    dsimp [F] at hf
    simpa only [Prod.fst] using he ▸ hf
  refine ⟨B, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
    exact (mem_product.mp (mem_filter.mp hp).1).1
  · intro a ha b hb c hc he
    obtain ⟨ta, hta, hea⟩ := hmem ha
    obtain ⟨tb, htb, heb⟩ := hmem hb
    obtain ⟨tc, htc, hec⟩ := hmem hc
    have ht : ta + tc = tb + tb := by omega
    have heq := hfree hta htb htc ht
    omega
  · rw [hBcard]
    exact hcard

/-- An explicit progression-free extraction bound valid for every finite
subset of an interval. -/
theorem behrend_extraction (L : ℕ) (hL : 0 < L)
    (S : Finset ℕ) (hS : S ⊆ range L) :
    ∃ B ⊆ S, ThreeAPFree (B : Set ℕ) ∧
      (S.card : ℝ) / 2 * Real.exp (-4 * Real.sqrt (Real.log L)) ≤ B.card := by
  obtain ⟨T, hT, hTc, hfree⟩ := rothNumberNat_spec L
  obtain ⟨B, hB, hBF, hBC⟩ := reflected_extraction L hL S T hS hT hfree
  refine ⟨B, hB, hBF, le_trans ?_ hBC⟩
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hr := Behrend.roth_lower_bound (N := L)
  rw [← hTc] at hr
  have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg S.card)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mpr
  nlinarith only [hm]

/-- In particular, three-root square collisions can be excluded at a subpower
cost. The four-distinct-root collisions are not excluded. -/
theorem square_ap_free_finite (N : ℕ) :
    ∃ B ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2),
      ThreeAPFree (B : Set ℕ) ∧
      (N : ℝ) / 2 * Real.exp (-4 * Real.sqrt (Real.log (N ^ 2 + 1 : ℕ))) ≤
        B.card := by
  let S := (Icc 1 N).image (fun n : ℕ => n ^ 2)
  have hS : S ⊆ range (N ^ 2 + 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hnN := (mem_Icc.mp hn).2
    apply mem_range.mpr
    nlinarith
  have hcard : S.card = N := by
    rw [card_image_of_injective _ (by
      intro a b h
      dsimp at h
      nlinarith : Function.Injective (fun n : ℕ => n ^ 2))]
    simp
  obtain ⟨B, hB, hBF, hBC⟩ := behrend_extraction (N ^ 2 + 1) (by omega) S hS
  rw [hcard] at hBC
  exact ⟨B, hB, hBF, hBC⟩

/-- In a three-AP-free set, a nontrivial repeated pair sum has four distinct
entries. -/
lemma four_distinct_of_collision {B : Set ℕ} (hB : ThreeAPFree B)
    {a b c d : ℕ} (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B)
    (he : a + b = c + d)
    (hnt : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hab : a ≠ b := by
    intro hh
    have hca := hB hc ha hd (by omega)
    exact hnt (Or.inl ⟨hca.symm, by omega⟩)
  have hcd : c ≠ d := by
    intro hh
    have hac := hB ha hc hb (by omega)
    exact hnt (Or.inl ⟨hac, by omega⟩)
  refine ⟨hab, ?_, ?_, ?_, ?_, hcd⟩ <;>
    intro hh <;> apply hnt <;> omega

#print axioms square_ap_free_finite

/-- The AP-free subsets of the squares have the conjectured near-linear
exponent. This assertion is weaker than the square-Sidon conjecture. -/
theorem square_ap_free_near_linear (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∃ B ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2),
        ThreeAPFree (B : Set ℕ) ∧ (N : ℝ) ^ (1 - ε) ≤ B.card := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hlog.eventually_ge_atTop (2 * Real.log 2 / ε),
    hlog.eventually_ge_atTop (192 / ε ^ 2)] with N hN hlog1 hlog2
  obtain ⟨B, hB, hBF, hBC⟩ := square_ap_free_finite N
  refine ⟨B, hB, hBF, le_trans ?_ hBC⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ Real.log ((N : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith)
  have hlogle : Real.log ((N : ℝ) ^ 2 + 1) ≤ 3 * Real.log N := by
    have harg : (N : ℝ) ^ 2 + 1 ≤ (N : ℝ) ^ 3 := by
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    have hh := Real.log_le_log (by positivity : 0 < (N : ℝ) ^ 2 + 1) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hl1 : 2 * Real.log 2 ≤ ε * Real.log N := by
    have hh := (div_le_iff₀ hε).mp hlog1
    nlinarith only [hh]
  have hl2 : 192 ≤ ε ^ 2 * Real.log N := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hlog2
    nlinarith only [hh]
  have hroot : Real.sqrt (Real.log ((N : ℝ) ^ 2 + 1)) ≤ ε * Real.log N / 8 := by
    have hs := Real.sq_sqrt hL0
    have hm := mul_le_mul_of_nonneg_right hl2 hl0
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith only [hs, hm, hlogle]
  have hexp : (1 - ε) * Real.log N ≤
      Real.log N - Real.log 2 - 4 * Real.sqrt (Real.log ((N : ℝ) ^ 2 + 1)) := by
    nlinarith only [hroot, hl1]
  rw [Real.rpow_def_of_pos hN0]
  push_cast
  calc
    _ ≤ Real.exp (Real.log N - Real.log 2 -
        4 * Real.sqrt (Real.log ((N : ℝ) ^ 2 + 1))) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hexp]
    _ = (N : ℝ) / 2 * Real.exp (-4 * Real.sqrt (Real.log ((N : ℝ) ^ 2 + 1))) := by
      rw [sub_eq_add_neg (Real.log N - Real.log 2), Real.exp_add,
        Real.exp_sub, Real.exp_log hN0, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

#print axioms square_ap_free_near_linear

#print axioms four_distinct_of_collision

end Erdos773.APFreeExtraction
