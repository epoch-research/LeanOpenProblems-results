import Submission.QuantitativeSquareSieve

/-!
A consequence of the already established upper bound: constant-loss quadratic
amplification is impossible. This does not disprove Erdős 773.
-/

namespace Erdos773.Amplification
open Filter Finset
set_option maxHeartbeats 1000000

lemma cube_le_two_pow (m : ℕ) (hm : 10 ≤ m) : m ^ 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ (2 : ℕ)]
    have h : (m + 1) ^ 3 ≤ 2 * m ^ 3 := by nlinarith [sq_nonneg (m - 2 : ℤ)]
    omega

lemma linear_square_le_two_pow (A m : ℕ)
    (hm : max 10 ((A + 3) ^ 2) ≤ m) : (A * m + 3) ^ 2 ≤ 2 ^ m := by
  have hm10 : 10 ≤ m := le_trans (le_max_left _ _) hm
  have hmA : (A + 3) ^ 2 ≤ m := le_trans (le_max_right _ _) hm
  calc
    (A * m + 3) ^ 2 ≤ ((A + 3) * m) ^ 2 :=
      Nat.pow_le_pow_left (by nlinarith) 2
    _ = (A + 3) ^ 2 * m ^ 2 := by ring
    _ ≤ m * m ^ 2 := Nat.mul_le_mul_right _ hmA
    _ = m ^ 3 := by ring
    _ ≤ 2 ^ m := cube_le_two_pow m hm10

lemma no_constant_density_gain (f : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hpos : ∀ N : ℕ, 1 ≤ N → 0 < f N)
    (hupper : ∀ k N : ℕ, 2 ^ (k + 3) ^ 2 ≤ N → f N ≤ 2 * r ^ k) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop, c * f N ≤ f (N ^ 2) := by
  rintro ⟨c, hc, he⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  let B := max N₀ 2
  have hB2 : 2 ≤ B := le_max_right _ _
  have hBpos : 0 < B := by omega
  have hB1 : 1 ≤ B := by omega
  have hBN (m : ℕ) : B ≤ B ^ (2 ^ m) := by
    calc
      B = B ^ 1 := by simp
      _ ≤ B ^ (2 ^ m) := Nat.pow_le_pow_right hBpos (Nat.one_le_pow m 2 (by decide))
  have hiter (m : ℕ) : c ^ m * f B ≤ f (B ^ (2 ^ m)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hn : N₀ ≤ B ^ (2 ^ m) := (le_max_left _ _).trans (hBN m)
      have hg := hN₀ _ hn
      have hp := mul_le_mul_of_nonneg_left ih hc.le
      have heq : B ^ (2 ^ (m + 1)) = (B ^ (2 ^ m)) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [heq]
      calc
        _ = c * (c ^ m * f B) := by rw [pow_succ]; ring
        _ ≤ c * f (B ^ (2 ^ m)) := hp
        _ ≤ _ := hg
  obtain ⟨A, hA⟩ := exists_pow_lt_of_lt_one hc hr1
  have hrA : 0 ≤ r ^ A / c := div_nonneg (pow_nonneg hr0 _) hc.le
  have hrAc : r ^ A / c < 1 := (div_lt_one hc).mpr hA
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrA hrAc
  have hfB := hpos B hB1
  have hs : ∀ᶠ m : ℕ in atTop, (r ^ A / c) ^ m < f B / 2 :=
    ht.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < f B / 2))
  obtain ⟨m, hm, hsmall⟩ := (eventually_ge_atTop (max 10 ((A + 3) ^ 2)) |>.and hs).exists
  have hthresh : 2 ^ (A * m + 3) ^ 2 ≤ B ^ (2 ^ m) := by
    calc
      _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by decide) (linear_square_le_two_pow A m hm)
      _ ≤ _ := Nat.pow_le_pow_left hB2 _
  have hu := hupper (A * m) (B ^ (2 ^ m)) hthresh
  have hl := (hiter m).trans hu
  have hscaled := mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr (pow_nonneg hc.le m))
  have hcne : c ^ m ≠ 0 := (pow_pos hc m).ne'
  have hcancel : c ^ m * f B * (c ^ m)⁻¹ = f B := by field_simp
  have hright : 2 * r ^ (A * m) * (c ^ m)⁻¹ = 2 * (r ^ A / c) ^ m := by
    rw [pow_mul, div_pow]
    ring
  rw [hcancel, hright] at hscaled
  linarith

noncomputable def squareMax (N : ℕ) : ℝ :=
  Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))

lemma squareMax_pos (N : ℕ) (hN : 1 ≤ N) : 0 < squareMax N := by
  have hsub : ({1} : Finset ℕ) ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2) := by
    intro x hx
    have hx1 : x = 1 := by simpa using hx
    subst x
    exact mem_image.mpr ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩, by simp⟩
  have hs : IsSidon (({1} : Finset ℕ) : Set ℕ) := by
    intro a ha b hb c hc d hd he
    simp only [mem_coe, mem_singleton] at ha hb hc hd
    subst a; subst b; subst c; subst d
    simp
  have hmem : ({1} : Finset ℕ) ∈
      (((Icc 1 N).image (fun n : ℕ => n ^ 2)).powerset.filter
        (fun S : Finset ℕ => IsSidon (S : Set ℕ))) := mem_filter.mpr ⟨mem_powerset.mpr hsub, hs⟩
  have hcard := Finset.le_sup (f := Finset.card) hmem
  have hn : 1 ≤ Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) := by
    simpa only [Finset.card_singleton] using hcard
  have hn' : (1 : ℝ) ≤ squareMax N := by
    dsimp [squareMax]
    exact_mod_cast hn
  linarith

/-- No fixed positive constant can support this proposed amplification law
at every sufficiently large scale. This is not the negation of Erdős 773. -/
theorem no_constant_quadratic_amplification :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c * N * squareMax N ≤ squareMax (N ^ 2) := by
  let f : ℕ → ℝ := fun N => squareMax N / N
  have hr0 : 0 ≤ Real.sqrt (3 / 4) := Real.sqrt_nonneg _
  have hrsq : Real.sqrt (3 / 4) ^ 2 = (3 / 4 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr1 : Real.sqrt (3 / 4) < 1 := by nlinarith
  have hp (N : ℕ) (hN : 1 ≤ N) : 0 < f N := by
    exact div_pos (squareMax_pos N hN) (by exact_mod_cast (show 0 < N by omega))
  have hu (k N : ℕ) (hN : 2 ^ (k + 3) ^ 2 ≤ N) :
      f N ≤ 2 * Real.sqrt (3 / 4) ^ k := by
    have hn : 0 < N := (Nat.pow_pos (by decide : 0 < (2 : ℕ))).trans_le hN
    apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < N)).mpr
    exact square_sidon_quantitative_upper k N hN
  intro h
  apply no_constant_density_gain f (Real.sqrt (3 / 4)) hr0 hr1 hp hu
  obtain ⟨c, hc, hrec⟩ := h
  refine ⟨c, hc, ?_⟩
  filter_upwards [hrec, eventually_ge_atTop 1] with N hN hn
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  dsimp [f]
  rw [Nat.cast_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hn0)).mpr
  calc
    c * (squareMax N / N) * (N : ℝ) ^ 2 = c * N * squareMax N := by
      field_simp
    _ ≤ _ := hN

/-- Arbitrarily large scales violate each proposed fixed-constant gain. -/
theorem frequently_small_quadratic_gain (c : ℝ) (hc : 0 < c) :
    ∃ᶠ N : ℕ in atTop, squareMax (N ^ 2) < c * N * squareMax N := by
  have hn : ¬ ∀ᶠ N : ℕ in atTop,
      c * N * squareMax N ≤ squareMax (N ^ 2) := by
    intro h
    exact no_constant_quadratic_amplification ⟨c, hc, h⟩
  simpa only [not_le] using Filter.not_eventually.mp hn

#print axioms no_constant_quadratic_amplification
#print axioms frequently_small_quadratic_gain
end Erdos773.Amplification
