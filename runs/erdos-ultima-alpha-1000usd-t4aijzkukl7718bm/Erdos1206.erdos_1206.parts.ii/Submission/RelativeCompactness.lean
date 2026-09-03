import Submission.Compactness

/-! Source-preserving compactness for finite cube-Sidon witnesses.
This is a relative reduction, not a construction of such witnesses. -/

open Filter
open scoped Topology

namespace Erdos1206

lemma compactness_finite_cube_sidon_in (T : Set ℕ) (δ C : ℝ)
    (h : ∀ N : ℕ, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ T ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) ∧
      ∀ n ≤ N, δ * n ≤ ((S.filter (fun a => a < n)).card : ℝ) + C) :
    ∃ A : Set ℕ, A ⊆ T ∧ IsSidon ((fun a : ℕ => a ^ 3) '' A) ∧
      ∀ n : ℕ, δ * n ≤ ((A ∩ Set.Iio n).ncard : ℝ) + C := by
  classical
  choose S hST hS hd using h
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
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ := (hev n).exists
    exact hST (φ i) (hi.mpr hn)
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


lemma existence_of_finite_prefix_construction_in {T : Set ℕ} {δ C : ℝ}
    (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ T ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) ∧
      ∀ n ≤ N, δ * n ≤ ((S.filter (fun a => a < n)).card : ℝ) + C) :
    ∃ A : Set ℕ, A ⊆ T ∧ A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  obtain ⟨A, hAT, hS, hd⟩ := compactness_finite_cube_sidon_in T δ C h
  have hpos := positive_lowerDensity_of_prefix_bound hδ hd
  refine ⟨A, hAT, ?_, hpos, hS⟩
  by_contra hfin
  have hzero : A.lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  simp [hzero] at hpos

#print axioms compactness_finite_cube_sidon_in
#print axioms existence_of_finite_prefix_construction_in
end Erdos1206
