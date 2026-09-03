import FormalConjecturesUtil

set_option maxHeartbeats 1000000

namespace Erdos773

lemma short_interval_sidon (L m : ℕ) (hL : m ^ 2 < L) :
    IsSidon ((Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc L (L + m)) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc d hd he
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_Icc] at ha hb hc hd
  obtain ⟨a, ⟨haL, ham⟩, rfl⟩ := ha
  obtain ⟨b, ⟨hbL, hbm⟩, rfl⟩ := hb
  obtain ⟨c, ⟨hcL, hcm⟩, rfl⟩ := hc
  obtain ⟨d, ⟨hdL, hdm⟩, rfl⟩ := hd
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le haL
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hbL
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hcL
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hdL
  have hx : x ≤ m := by omega
  have hy : y ≤ m := by omega
  have hz : z ≤ m := by omega
  have hw : w ≤ m := by omega
  have hx2 : x ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hx 2
  have hy2 : y ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hy 2
  have hz2 : z ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hz 2
  have hw2 : w ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hw 2
  have hs : x + z = y + w := by
    rcases lt_trichotomy (x + z) (y + w) with h | h | h
    · have hh := Nat.mul_le_mul_left (2 * L) (Nat.succ_le_of_lt h)
      nlinarith
    · exact h
    · have hh := Nat.mul_le_mul_left (2 * L) (Nat.succ_le_of_lt h)
      nlinarith
  have he' : (L + x : ℤ) ^ 2 + (L + z : ℤ) ^ 2 =
      (L + y : ℤ) ^ 2 + (L + w : ℤ) ^ 2 := by exact_mod_cast he
  have hs' : (x : ℤ) + z = y + w := by exact_mod_cast hs
  have hw' : (w : ℤ) = x + z - y := by omega
  have hp : ((x : ℤ) - y) * ((x : ℤ) - w) = 0 := by
    rw [hw'] at he' ⊢
    nlinarith only [he']
  rcases mul_eq_zero.mp hp with hp | hp
  · have hxy : x = y := by exact_mod_cast (sub_eq_zero.mp hp)
    have hzw : z = w := by omega
    simp [hxy, hzw]
  · have hxw : x = w := by exact_mod_cast (sub_eq_zero.mp hp)
    have hzy : z = y := by omega
    simp [hxw, hzy]

lemma short_interval_card_bound (m N : ℕ) (hN : m ^ 2 + m + 1 ≤ N) :
    m + 1 ≤ Finset.maxSidonSubsetCard
      (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) := by
  let B := Finset.image (fun n : ℕ => n ^ 2)
    (Finset.Icc (m ^ 2 + 1) (m ^ 2 + 1 + m))
  have hB : IsSidon (B : Set ℕ) := short_interval_sidon (m ^ 2 + 1) m (by omega)
  have hsub : B ⊆ Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N) := by
    apply Finset.image_subset_image
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hcard : B.card = m + 1 := by
    dsimp [B]
    rw [Finset.card_image_of_injective]
    · rw [Nat.card_Icc]
      omega
    · intro a b hab
      nlinarith
  rw [← hcard]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hB⟩)

lemma sqrt_card_bound (N : ℕ) :
    Nat.sqrt N ≤ Finset.maxSidonSubsetCard
      (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) := by
  by_cases h : Nat.sqrt N = 0
  · simp [h]
  · have hk : 1 ≤ Nat.sqrt N := by omega
    have hm : Nat.sqrt N - 1 + 1 = Nat.sqrt N := by omega
    have hsq := Nat.sqrt_le' N
    have hN : (Nat.sqrt N - 1) ^ 2 + (Nat.sqrt N - 1) + 1 ≤ N := by
      nlinarith
    simpa [hm] using short_interval_card_bound (Nat.sqrt N - 1) N hN

lemma conjecture_for_epsilon_gt_half (ε : ℝ) (hε : 1 / 2 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) := by
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (ε - 1 / 2))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < ε - 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [Filter.tendsto_atTop.mp ht 2, Filter.eventually_ge_atTop 1] with N hN hpos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk : (1 : ℝ) ≤ Nat.sqrt N := by
    exact_mod_cast (Nat.sqrt_pos.mpr (show 0 < N by omega))
  have hsqrt : Real.sqrt (N : ℝ) ≤ 2 * Nat.sqrt N := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsq : (N : ℝ) ≤ (Nat.sqrt N : ℝ) * Nat.sqrt N + Nat.sqrt N + Nat.sqrt N := by
        exact_mod_cast Nat.sqrt_le_add N
      nlinarith [sq_nonneg ((Nat.sqrt N : ℝ) - 1)]
  have hp : (N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (ε - 1 / 2) = Real.sqrt N := by
    rw [← Real.rpow_add hNpos, Real.sqrt_eq_rpow]
    congr 1
    ring
  have hprod := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hNpos.le (1 - ε))
  have hbound : (N : ℝ) ^ (1 - ε) ≤ Nat.sqrt N := by
    nlinarith only [hp, hprod, hsqrt]
  exact hbound.trans (by exact_mod_cast sqrt_card_bound N)

#print axioms conjecture_for_epsilon_gt_half

end Erdos773
