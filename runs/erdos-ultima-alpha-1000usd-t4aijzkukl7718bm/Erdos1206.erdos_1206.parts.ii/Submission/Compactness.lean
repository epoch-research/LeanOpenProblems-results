import FormalConjecturesUtil

/-! Verified auxiliary results. These do not settle `erdos_1206.parts.ii`. -/

open Filter
open scoped Topology

namespace Erdos1206

lemma compactness_finite_cube_sidon (δ C : ℝ)
    (h : ∀ N : ℕ, ∃ S : Finset ℕ,
      IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) ∧
      ∀ n ≤ N, δ * n ≤ ((S.filter (fun a => a < n)).card : ℝ) + C) :
    ∃ A : Set ℕ, IsSidon ((fun a : ℕ => a ^ 3) '' A) ∧
      ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C := by
  classical
  choose S hS hd using h
  let x : ℕ → ℕ → Bool := fun i n => decide (n ∈ S i)
  obtain ⟨f, φ, hφ, hf⟩ := SeqCompactSpace.tendsto_subseq x
  let A : Set ℕ := {n | f n = true}
  have hev (n : ℕ) : ∀ᶠ i in atTop, (n ∈ S (φ i) ↔ n ∈ A) := by
    have hn : Tendsto (fun i => x (φ i) n) atTop (𝓝 (f n)) :=
      (tendsto_pi_nhds.mp hf) n
    have heq : ∀ᶠ i in atTop, x (φ i) n = f n :=
      hn.eventually (isOpen_discrete {f n} |>.mem_nhds (by simp))
    filter_upwards [heq] with i hi
    change decide (n ∈ S (φ i)) = f n at hi
    change (n ∈ S (φ i)) ↔ f n = true
    rw [← hi]
    simp
  have hpre (N : ℕ) : ∃ i : ℕ, N ≤ φ i ∧ ∀ n < N, (n ∈ S (φ i) ↔ n ∈ A) := by
    have hh : ∀ᶠ i in atTop, ∀ n ∈ Finset.range N, (n ∈ S (φ i) ↔ n ∈ A) :=
      (Finset.eventually_all (Finset.range N)).mpr (fun n _ => hev n)
    have hbig : ∀ᶠ i : ℕ in atTop, N ≤ φ i := hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
    obtain ⟨i, hi, hni⟩ := (hbig.and hh).exists
    exact ⟨i, hi, fun n hn => hni n (Finset.mem_range.mpr hn)⟩
  refine ⟨A, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hdA, rfl⟩ heq
    obtain ⟨i, _, hi⟩ := hpre (a + b + c + d + 1)
    exact hS (φ i) _ ⟨a, (hi a (by omega)).mpr ha, rfl⟩
      _ ⟨b, (hi b (by omega)).mpr hb, rfl⟩
      _ ⟨c, (hi c (by omega)).mpr hc, rfl⟩
      _ ⟨d, (hi d (by omega)).mpr hdA, rfl⟩ heq
  · intro n
    obtain ⟨i, hni, hi⟩ := hpre n
    have heq : A ∩ Set.Iio n = (S (φ i)).filter (fun a => a < n) := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.mem_coe, Finset.mem_filter]
      exact ⟨fun h => ⟨(hi a h.2).mpr h.1, h.2⟩, fun h => ⟨(hi a h.2).mp h.1, h.2⟩⟩
    rw [heq, Set.ncard_coe_finset]
    exact hd (φ i) n hni

lemma positive_lowerDensity_of_prefix_bound {A : Set ℕ} {δ C : ℝ}
    (hδ : 0 < δ)
    (h : ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C) :
    0 < A.lowerDensity := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * C / δ)
  have hev : ∀ᶠ n : ℕ in atTop, δ / 2 ≤ A.partialDensity Set.univ n := by
    apply eventually_atTop.mpr
    refine ⟨M + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hMn : (M : ℝ) < n := by exact_mod_cast (show M < n by omega)
    have hC : 2 * C < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp (hM.trans hMn)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn0)).mpr
    nlinarith [h n]
  have hlim : δ / 2 ≤ A.lowerDensity :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => Set.partialDensity_le_one A Set.univ n)) hev
  exact (half_pos hδ).trans_le hlim

lemma existence_of_finite_prefix_construction {δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ S : Finset ℕ,
      IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) ∧
      ∀ n ≤ N, δ * n ≤ ((S.filter (fun a => a < n)).card : ℝ) + C) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨A, hS, hd⟩ := compactness_finite_cube_sidon δ C h
  have hpos := positive_lowerDensity_of_prefix_bound hδ hd
  refine ⟨A, ?_, hpos, hS⟩
  by_contra hfin
  have hzero : A.lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  simp [hzero] at hpos

lemma prefix_bound_of_positive_lowerDensity {A : Set ℕ} (hA : 0 < A.lowerDensity) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C := by
  let δ := A.lowerDensity / 2
  have hδ : 0 < δ := half_pos hA
  have hδA : δ < A.lowerDensity := half_lt_self hA
  have hev : ∀ᶠ n : ℕ in atTop, δ < A.partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf hδA (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨δ, hδ, δ * M, fun n => ?_⟩
  by_cases hn : n < M
  · have hle : (n : ℝ) ≤ M := by exact_mod_cast hn.le
    have hmul := mul_le_mul_of_nonneg_left hle hδ.le
    have hcard : (0 : ℝ) ≤ ((A ∩ Set.Iio n).ncard : ℝ) := by positivity
    linarith
  · by_cases hn0 : n = 0
    · subst n
      simpa using mul_nonneg hδ.le (Nat.cast_nonneg M)
    have hnp : 0 < n := Nat.pos_of_ne_zero hn0
    have hp := hM n (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hp
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnp)).mp hp
    have hC : (0 : ℝ) ≤ δ * M := by positivity
    linarith

lemma conjecture_iff_finite_prefix_construction :
    (∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A)) ↔
    (∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, ∃ S : Finset ℕ,
      IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) ∧
      ∀ n ≤ N, δ * n ≤ ((S.filter (fun a => a < n)).card : ℝ) + C) := by
  classical
  constructor
  · rintro ⟨A, _, hA, hs⟩
    obtain ⟨δ, hδ, C, hd⟩ := prefix_bound_of_positive_lowerDensity hA
    refine ⟨δ, hδ, C, fun N => ?_⟩
    let S := (Finset.range N).filter (fun a => a ∈ A)
    refine ⟨S, ?_, ?_⟩
    · apply Set.IsSidon.subset hs
      rintro _ ⟨a, ha, rfl⟩
      have ha' : a ∈ (Finset.range N).filter (fun a => a ∈ A) := ha
      exact ⟨a, (Finset.mem_filter.mp ha').2, rfl⟩
    · intro n hn
      have heq : A ∩ Set.Iio n = (S.filter (fun a => a < n) : Set ℕ) := by
        ext a
        simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.mem_coe, Finset.mem_filter,
          S, Finset.mem_range]
        constructor
        · rintro ⟨ha, han⟩
          exact ⟨⟨lt_of_lt_of_le han hn, ha⟩, han⟩
        · rintro ⟨⟨_, ha⟩, han⟩
          exact ⟨ha, han⟩
      have hp := hd n
      rw [heq, Set.ncard_coe_finset] at hp
      exact hp
  · rintro ⟨δ, hδ, C, h⟩
    exact existence_of_finite_prefix_construction hδ h

end Erdos1206
