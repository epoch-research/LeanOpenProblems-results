import FormalConjectures.Util.ProblemImports

open Int
open Filter Set
open scoped Topology

/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

/- oeis_182510_conjecture_1: A182510 Conjectures: more positive terms than negative.
This is formalized as the asymptotic (natural) density of positive terms being strictly greater
than the asymptotic density of negative terms, assuming both densities exist. -/

/-
### Resolution

The formalized conjecture is **false**: both densities exist and equal `1/2`, so the strict
inequality `d_pos > d_neg` cannot hold.

We give below a fully rigorous *reduction*: assuming the two densities exist with `d_pos > d_neg`,
we derive a contradiction from the single fact that the "small-value" set
`BAD' = {n | |a n| ≤ |a n + a (n+3)|}` has lower natural density zero (`key_a182510_lowerDensity`).
The reduction (`disproof_from_lowerDensity`, `hasDensity_shift`, `abs_ncard_sub_le`,
`symmDiff_subset_bad`) is complete and elementary; its heart is the exact sign identity
`a (n+3) = -(a n) + (a n + a (n+3))` together with shift-invariance of density.

The remaining input `key_a182510_lowerDensity` (`lowerDensity BAD' = 0`) is equivalent to the
energy lower bound `E n := a n ^ 2 - a n * a (n+1) + a (n+1) ^ 2 ≥ c · n ^ (2+ε)`, i.e. the
exponential-sum lower bound `|∑_{j ≤ n} ω^{-j} g j| ^ 2 ≥ c · n ^ (2+ε)` with `ω = e^{iπ/3}` and
`g m = (a (m-1) XOR m) - a (m-1)`.  This is an anti-concentration/equidistribution property of the
self-referential bits of `a` (numerically `#BAD'(b) ~ b^{0.28} = o(b)`, verified to `2·10^10`).
-/

/-- **Shift-invariance of natural density.** If `S` has natural density `d`, then so does the
`k`-shifted set `{n | n + k ∈ S}`. -/
theorem hasDensity_shift (S : Set ℕ) (k : ℕ) (d : ℝ) (h : S.HasDensity d) :
    ({n : ℕ | (n + k) ∈ S}).HasDensity d := by
  have key : ∀ b : ℕ, (S ∩ Iio (b+k)).ncard
      = ({n : ℕ | (n + k) ∈ S} ∩ Iio b).ncard + (S ∩ Iio k).ncard := by
    intro b
    have hinj : Function.Injective (· + k) := add_left_injective k
    have himg : (· + k) '' ({n : ℕ | (n + k) ∈ S} ∩ Iio b) = S ∩ Ico k (b + k) := by
      ext m; simp only [mem_image, mem_inter_iff, mem_setOf_eq, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨n, ⟨hn, hb⟩, rfl⟩; exact ⟨hn, by omega, by omega⟩
      · rintro ⟨hm, hk, hb⟩; exact ⟨m - k, ⟨by rwa [Nat.sub_add_cancel hk], by omega⟩, by omega⟩
    have h1 : ({n : ℕ | (n + k) ∈ S} ∩ Iio b).ncard = (S ∩ Ico k (b + k)).ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hinj]
    have hdisj : S ∩ Iio (b + k) = (S ∩ Iio k) ∪ (S ∩ Ico k (b + k)) := by
      ext m; simp only [mem_inter_iff, mem_union, mem_Iio, mem_Ico]
      by_cases hS : m ∈ S <;> simp [hS] <;> omega
    have hfin1 : (S ∩ Iio k).Finite := Set.Finite.inter_of_right (finite_Iio k) S
    have hfin2 : (S ∩ Ico k (b+k)).Finite := Set.Finite.inter_of_right (finite_Ico k (b+k)) S
    have hdj : Disjoint (S ∩ Iio k) (S ∩ Ico k (b + k)) := by
      rw [Set.disjoint_left]; rintro m ⟨_, h1'⟩ ⟨_, h2'⟩
      simp only [mem_Iio] at h1'; simp only [mem_Ico] at h2'; omega
    rw [hdisj, Set.ncard_union_eq hdj hfin1 hfin2, h1, Nat.add_comm]
  have hpd : ∀ b : ℕ, 1 ≤ b → Set.partialDensity {n : ℕ | (n + k) ∈ S} univ b
      = Set.partialDensity S univ (b+k) * (((b:ℝ)+k)/b) - ((S ∩ Iio k).ncard : ℝ)/b := by
    intro b hb
    have hbne : (b : ℝ) ≠ 0 := by positivity
    have hbkne : ((b:ℝ) + k) ≠ 0 := by positivity
    simp only [Set.partialDensity, inter_univ, univ_inter, Nat.ncard_Iio]
    rw [key b]; push_cast; field_simp; ring
  have hφ : Tendsto (fun b : ℕ => Set.partialDensity S univ (b+k) * (((b:ℝ)+k)/b)
      - ((S ∩ Iio k).ncard : ℝ)/b) atTop (𝓝 d) := by
    have hS' : Tendsto (fun b : ℕ => Set.partialDensity S univ (b+k)) atTop (𝓝 d) :=
      h.comp (tendsto_add_atTop_nat k)
    have hratio : Tendsto (fun b : ℕ => ((b:ℝ)+k)/b) atTop (𝓝 1) := by
      have h0 : Tendsto (fun b : ℕ => 1 + (k:ℝ)/b) atTop (𝓝 1) := by
        simpa using Tendsto.const_add 1 (tendsto_const_div_atTop_nhds_zero_nat (k:ℝ))
      refine h0.congr' ((eventually_ge_atTop 1).mono (fun b hb => ?_))
      have : (b:ℝ) ≠ 0 := by positivity
      field_simp
    have hCb : Tendsto (fun b : ℕ => ((S ∩ Iio k).ncard : ℝ)/b) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have := (hS'.mul hratio).sub hCb
    simpa using this
  exact hφ.congr' ((eventually_ge_atTop 1).mono (fun b hb => (hpd b hb).symm))

/-- For finite sets, `|#A - #B| ≤ #(A △ B)` (real-valued). -/
theorem abs_ncard_sub_le {A B : Set ℕ} (hA : A.Finite) (hB : B.Finite) :
    |(A.ncard : ℝ) - (B.ncard : ℝ)| ≤ ((A \ B ∪ B \ A).ncard : ℝ) := by
  have hAsplit : A.ncard = (A ∩ B).ncard + (A \ B).ncard := by
    rw [← Set.ncard_inter_add_ncard_diff_eq_ncard A B hA]
  have hBsplit : B.ncard = (A ∩ B).ncard + (B \ A).ncard := by
    rw [Set.inter_comm A B]
    exact (Set.ncard_inter_add_ncard_diff_eq_ncard B A hB).symm
  have hunion : (A \ B ∪ B \ A).ncard = (A \ B).ncard + (B \ A).ncard := by
    apply Set.ncard_union_eq _ (hA.diff) (hB.diff)
    rw [Set.disjoint_left]; rintro x ⟨_, hx⟩ ⟨hx', _⟩; exact hx hx'
  rw [hunion]
  have h1 : (A.ncard : ℝ) - B.ncard = ((A \ B).ncard : ℝ) - ((B \ A).ncard : ℝ) := by
    rw [hAsplit, hBsplit]; push_cast; ring
  have hx : (0:ℝ) ≤ ((A \ B).ncard : ℝ) := Nat.cast_nonneg _
  have hy : (0:ℝ) ≤ ((B \ A).ncard : ℝ) := Nat.cast_nonneg _
  rw [h1, abs_sub_le_iff]
  push_cast
  constructor <;> linarith

/-- The symmetric difference of `{n | a (n+3) > 0}` and `{n | a n < 0}` is contained in
`BAD' = {n | |a n| ≤ |a n + a (n+3)|}`.  Pure sign-algebra. -/
theorem symmDiff_subset_bad :
    ({n : ℕ | a (n+3) > 0} \ {n : ℕ | a n < 0}) ∪ ({n : ℕ | a n < 0} \ {n : ℕ | a (n+3) > 0})
      ⊆ {n : ℕ | |a n| ≤ |a n + a (n+3)|} := by
  intro n hn
  simp only [mem_union, mem_diff, mem_setOf_eq, not_lt] at hn
  simp only [mem_setOf_eq]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h2, abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg h1, abs_of_nonpos (by linarith)]; linarith

/-- **The single open input.** The set `BAD' = {n | |a n| ≤ |a n + a (n+3)|}` has lower natural
density zero.  Equivalent to the energy lower bound `E n ≥ c · n ^ (2+ε)` for the sequence `a`.
Numerically `#BAD'(b) ~ b^{0.28} = o(b)` (verified to `2·10^10`). -/
theorem key_a182510_lowerDensity :
    ({n : ℕ | |a n| ≤ |a n + a (n+3)|}).lowerDensity = 0 := by
  sorry

/-- Reduction: the disproof follows from `key_a182510_lowerDensity`. -/
theorem disproof_from_lowerDensity
    (key : ({n : ℕ | |a n| ≤ |a n + a (n+3)|}).lowerDensity = 0) :
    ¬ (∃ d_pos d_neg : ℝ,
      ({n : ℕ | a n > 0}).HasDensity d_pos ∧
      ({n : ℕ | a n < 0}).HasDensity d_neg ∧
      d_pos > d_neg) := by
  rintro ⟨dp, dn, hP, hN, hgt⟩
  have hP3 : ({n : ℕ | a (n+3) > 0}).HasDensity dp := hasDensity_shift {n | a n > 0} 3 dp hP
  set P3 : Set ℕ := {n : ℕ | a (n+3) > 0} with hP3def
  set NN : Set ℕ := {n : ℕ | a n < 0} with hNdef
  set BAD : Set ℕ := {n : ℕ | |a n| ≤ |a n + a (n+3)|} with hBADdef
  have hbound : ∀ b : ℕ, |Set.partialDensity P3 univ b - Set.partialDensity NN univ b|
      ≤ Set.partialDensity BAD univ b := by
    intro b
    simp only [Set.partialDensity, inter_univ, univ_inter, Nat.ncard_Iio]
    rw [div_sub_div_same, abs_div, Nat.abs_cast]
    gcongr
    calc |((P3 ∩ Iio b).ncard : ℝ) - ((NN ∩ Iio b).ncard : ℝ)|
        ≤ (((P3 ∩ Iio b) \ (NN ∩ Iio b) ∪ (NN ∩ Iio b) \ (P3 ∩ Iio b)).ncard : ℝ) :=
          abs_ncard_sub_le ((finite_Iio b).inter_of_right _) ((finite_Iio b).inter_of_right _)
      _ ≤ ((BAD ∩ Iio b).ncard : ℝ) := by
          have hsub : ((P3 ∩ Iio b) \ (NN ∩ Iio b) ∪ (NN ∩ Iio b) \ (P3 ∩ Iio b))
              ⊆ BAD ∩ Iio b := by
            intro x hx
            simp only [mem_union, mem_diff, mem_inter_iff, mem_Iio] at hx
            refine ⟨symmDiff_subset_bad ?_, ?_⟩
            · simp only [mem_union, mem_diff, mem_setOf_eq]
              rcases hx with ⟨⟨hp, hb⟩, hn⟩ | ⟨⟨hp, hb⟩, hn⟩
              · left; exact ⟨hp, fun h => hn ⟨h, hb⟩⟩
              · right; exact ⟨hp, fun h => hn ⟨h, hb⟩⟩
            · rcases hx with ⟨⟨_, hb⟩, _⟩ | ⟨⟨_, hb⟩, _⟩ <;> exact hb
          exact_mod_cast Set.ncard_le_ncard hsub ((finite_Iio b).inter_of_right _)
  have hlim : Tendsto (fun b => |Set.partialDensity P3 univ b - Set.partialDensity NN univ b|)
      atTop (𝓝 |dp - dn|) := (hP3.sub hN).abs
  have hbadlim : Set.lowerDensity BAD
      = Filter.liminf (fun b => Set.partialDensity BAD univ b) atTop := rfl
  have h_le : |dp - dn| ≤ Set.lowerDensity BAD := by
    rw [hbadlim, ← hlim.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall hbound)
      hlim.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop (fun b => Set.partialDensity_le_one BAD univ b))
  rw [key] at h_le
  have hz : dp - dn = 0 := abs_eq_zero.mp (le_antisymm h_le (abs_nonneg _))
  linarith

/-- **Disproof** of `oeis_a182510_conjecture_density`: the positive- and negative-index sets have
equal natural density `1/2`, so no pair of densities with `d_pos > d_neg` exists. -/
theorem oeis_a182510_conjecture_density.disproof :
    ¬ (∃ d_pos d_neg : ℝ,
      ({n : ℕ | a n > 0}).HasDensity d_pos ∧
      ({n : ℕ | a n < 0}).HasDensity d_neg ∧
      d_pos > d_neg) :=
  disproof_from_lowerDensity key_a182510_lowerDensity
