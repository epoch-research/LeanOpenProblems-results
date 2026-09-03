import FormalConjecturesUtil

/-! Elementary bounds for integers with bounded largest prime factor. -/

open Filter
open scoped Topology

namespace Erdos371Exploration

lemma bounded_maxPrimeFac_square_cover {K n : ℕ} (hn : Nat.maxPrimeFac n ≤ K) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ (K + 1) ^ (K + 1) ∧ b ^ 2 * a = n := by
  by_cases hn0 : n = 0
  · exact ⟨1, 0, by omega, Nat.one_le_pow _ _ (by omega), by simp [hn0]⟩
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hadvd : a ∣ n := hab ▸ dvd_mul_left a (b ^ 2)
  have hple (p : ℕ) (hp : p ∈ a.primeFactors) : p ≤ K := by
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (Nat.le_maxPrimeFac hn0 hpp (hpd.trans hadvd)).trans hn
  have hsub : a.primeFactors ⊆ Finset.range (K + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (by have := hple p hp; omega)
  have haB : a ≤ (K + 1) ^ (K + 1) := by
    calc
      a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree ha).symm
      _ ≤ ∏ _p ∈ a.primeFactors, (K + 1) := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun p hp => by have := hple p hp; omega)
      _ = (K + 1) ^ a.primeFactors.card := by simp
      _ ≤ (K + 1) ^ (K + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        simpa using Finset.card_le_card hsub
  exact ⟨a, b, Nat.pos_of_ne_zero ha.ne_zero, haB, hab⟩

lemma bounded_maxPrimeFac_count (K N : ℕ) :
    ((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card ≤
      ((K + 1) ^ (K + 1) + 1) * (Nat.sqrt N + 1) := by
  classical
  let B := (K + 1) ^ (K + 1)
  let F := ((Finset.range (B + 1)).product (Finset.range (Nat.sqrt N + 1))).image
    (fun ab : ℕ × ℕ => ab.2 ^ 2 * ab.1)
  have hsub : (Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K) ⊆ F := by
    intro n hn
    obtain ⟨hnN, hnK⟩ := Finset.mem_filter.mp hn
    obtain ⟨a, b, ha, haB, hab⟩ := bounded_maxPrimeFac_square_cover hnK
    have hsq : b ^ 2 ≤ N := by
      have hle : b ^ 2 ≤ b ^ 2 * a := by
        simpa using Nat.mul_le_mul_left (b ^ 2) (show 1 ≤ a from ha)
      have hnlt := Finset.mem_range.mp hnN
      omega
    have hbs : b ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hsq
    apply Finset.mem_image.mpr
    refine ⟨(a, b), ?_, hab⟩
    change (a, b) ∈ (Finset.range (B + 1)).product (Finset.range (Nat.sqrt N + 1))
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by dsimp [B]; omega), Finset.mem_range.mpr (by omega)⟩
  calc
    ((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card ≤ F.card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.range (B + 1)).product (Finset.range (Nat.sqrt N + 1))).card :=
      Finset.card_image_le
    _ = _ := by simp [B]

lemma bounded_maxPrimeFac_partialDensity (K N : ℕ) :
    {n | Nat.maxPrimeFac n ≤ K}.partialDensity Set.univ N =
      (((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card : ℝ) / N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  congr 2
  have he : {n | Nat.maxPrimeFac n ≤ K} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => Nat.maxPrimeFac n ≤ K)) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma bounded_maxPrimeFac_hasDensity_zero (K : ℕ) :
    {n | Nat.maxPrimeFac n ≤ K}.HasDensity 0 := by
  let C : ℝ := ((K + 1) ^ (K + 1) + 1 : ℕ)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n / n) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto (fun n : ℕ => C * (Real.sqrt n + 1) / n) atTop (𝓝 0) := by
    simpa [mul_div_assoc, add_div] using
      (tendsto_const_nhds.mul (hsqrt.add tendsto_one_div_atTop_nhds_zero_nat) :
        Tendsto (fun n : ℕ => C * (Real.sqrt n / n + 1 / n)) atTop (𝓝 (C * (0 + 0))))
  rw [Set.HasDensity]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    unfold Set.partialDensity
    positivity
  · intro n
    change {m | Nat.maxPrimeFac m ≤ K}.partialDensity Set.univ n ≤ C * (Real.sqrt n + 1) / n
    rw [bounded_maxPrimeFac_partialDensity]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hc : (((Finset.range n).filter (fun m => Nat.maxPrimeFac m ≤ K)).card : ℝ) ≤
        C * (Nat.sqrt n + 1) := by
      dsimp [C]
      exact_mod_cast bounded_maxPrimeFac_count K n
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
    linarith [Real.nat_sqrt_le_real_sqrt (a := n)]

lemma density_zero_of_subset {S T : Set ℕ} (hsub : S ⊆ T) (hT : T.HasDensity 0) :
    S.HasDensity 0 := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
  · intro n
    unfold Set.partialDensity
    positivity
  · intro n
    change (S.partialDensity Set.univ n : ℝ) ≤ T.partialDensity Set.univ n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hc : (S ∩ Set.univ ∩ Set.Iio n).ncard ≤ (T ∩ Set.univ ∩ Set.Iio n).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_left (Set.Iio n)
        (Set.inter_subset_inter_left Set.univ hsub))
    exact Nat.cast_le.mpr hc

/-- A fixed finite modulus recovers the value of the largest prime factor
only on a density-zero set. -/
lemma fixed_gcd_cutoff_agreement_zero {Q : ℕ} (hQ : 0 < Q) :
    {n | Nat.maxPrimeFac (Nat.gcd n Q) = Nat.maxPrimeFac n}.HasDensity 0 := by
  apply density_zero_of_subset _ (bounded_maxPrimeFac_hasDensity_zero Q)
  intro n hn
  change Nat.maxPrimeFac n ≤ Q
  rw [← hn]
  exact Nat.maxPrimeFac_le.trans (Nat.gcd_le_right n hQ)

/-- Multiplication by any fixed positive integer leaves the largest prime factor
unchanged outside a density-zero set. -/
lemma fixed_mul_maxPrimeFac_changes_zero {m : ℕ} (hm : 0 < m) :
    {n | Nat.maxPrimeFac (m * n) ≠ Nat.maxPrimeFac n}.HasDensity 0 := by
  apply density_zero_of_subset _ (bounded_maxPrimeFac_hasDensity_zero (Nat.maxPrimeFac m))
  intro n hn
  change Nat.maxPrimeFac n ≤ Nat.maxPrimeFac m
  by_cases hn0 : n = 0
  · subst n
    simp at hn
  · have hmul := Nat.maxPrimeFac_mul hm.ne' hn0
    by_contra hle
    have hge : Nat.maxPrimeFac m ≤ Nat.maxPrimeFac n := by omega
    exact hn (hmul.trans (max_eq_right hge))

end Erdos371Exploration
