import FormalConjecturesUtil

set_option maxHeartbeats 1000000

namespace Erdos773

lemma wider_interval_sidon (L m : ℕ) (hL : m ^ 2 < 4 * L) :
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
  have hx' : (x : ℤ) ≤ m := by exact_mod_cast hx
  have hy' : (y : ℤ) ≤ m := by exact_mod_cast hy
  have hz' : (z : ℤ) ≤ m := by exact_mod_cast hz
  have hw' : (w : ℤ) ≤ m := by exact_mod_cast hw
  have hL' : (m : ℤ) ^ 2 < 4 * L := by exact_mod_cast hL
  have he' : (L + x : ℤ) ^ 2 + (L + z : ℤ) ^ 2 =
      (L + y : ℤ) ^ 2 + (L + w : ℤ) ^ 2 := by exact_mod_cast he
  have hs' : (x : ℤ) + z = y + w := by
    rcases lt_trichotomy ((x : ℤ) + z) (y + w) with h | h | h
    · have hh := mul_le_mul_of_nonneg_left (show (x : ℤ) + z + 1 ≤ y + w by omega)
        (show 0 ≤ 2 * (L : ℤ) by positivity)
      have hx2 := mul_le_mul_of_nonneg_left hx' (show 0 ≤ (x : ℤ) by positivity)
      have hz2 := mul_le_mul_of_nonneg_left hz' (show 0 ≤ (z : ℤ) by positivity)
      have hs2 : ((x : ℤ) + z) ^ 2 ≤ ((y : ℤ) + w) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h.le 2
      nlinarith only [he', hL', hh, hx2, hz2, hs2,
        sq_nonneg ((y : ℤ) - w), sq_nonneg ((x : ℤ) + z - m)]
    · exact h
    · have hh := mul_le_mul_of_nonneg_left (show (y : ℤ) + w + 1 ≤ x + z by omega)
        (show 0 ≤ 2 * (L : ℤ) by positivity)
      have hy2 := mul_le_mul_of_nonneg_left hy' (show 0 ≤ (y : ℤ) by positivity)
      have hw2 := mul_le_mul_of_nonneg_left hw' (show 0 ≤ (w : ℤ) by positivity)
      have hs2 : ((y : ℤ) + w) ^ 2 ≤ ((x : ℤ) + z) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h.le 2
      nlinarith only [he', hL', hh, hy2, hw2, hs2,
        sq_nonneg ((x : ℤ) - z), sq_nonneg ((y : ℤ) + w - m)]
  have hs : x + z = y + w := by exact_mod_cast hs'
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


lemma sqrt_add_one_card_bound (N : ℕ) (hN : 4 ≤ N) :
    Nat.sqrt N + 1 ≤ Finset.maxSidonSubsetCard
      (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) := by
  let m := Nat.sqrt N
  let L := N - m
  have hm : 2 ≤ m := Nat.le_sqrt.mpr hN
  have hmN : m ≤ N := Nat.sqrt_le_self N
  have hLm : L + m = N := Nat.sub_add_cancel hmN
  have hsq : m ^ 2 ≤ N := Nat.sqrt_le' N
  have hm2 : 2 * m ≤ m ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_le_mul_left m hm
  have hL : m ^ 2 < 4 * L := by nlinarith only [hLm, hsq, hm, hm2]
  have hLpos : 1 ≤ L := by omega
  let B := Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc L (L + m))
  have hB : IsSidon (B : Set ℕ) := wider_interval_sidon L m hL
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
  change m + 1 ≤ _
  rw [← hcard]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hB⟩)

lemma conjecture_for_epsilon_ge_half (ε : ℝ) (hε : 1 / 2 ≤ ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 4] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (1 - ε) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsqrt : Real.sqrt (N : ℝ) ≤ Nat.sqrt N + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn := Nat.sqrt_le_add N
      have hn' : (N : ℝ) ≤ (Nat.sqrt N : ℝ) * Nat.sqrt N + Nat.sqrt N + Nat.sqrt N := by
        exact_mod_cast hn
      nlinarith only [hn']
  exact hpow.trans (hsqrt.trans (by exact_mod_cast sqrt_add_one_card_bound N hN))

#print axioms conjecture_for_epsilon_ge_half

end Erdos773
