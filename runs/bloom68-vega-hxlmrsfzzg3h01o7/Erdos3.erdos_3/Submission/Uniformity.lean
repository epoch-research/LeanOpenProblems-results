import Submission.WeightedReduction
import Submission.APReduction

/-!
# Uniformization of finite reciprocal-weight bounds

For each length at least three, summability for every set avoiding that length
implies a uniform bound on the reciprocal weights of finite sets avoiding it.
This is a reduction, not an unconditional proof of the uniform bound.

The gluing used here puts a positive lower block in `[1, M]` and an upper block
among the positive multiples of `2 * M`. Unlike translation into a bounded
interval, dilation allows the upper source block to have arbitrarily large
weight. Iterating such extensions produces an AP-free set with unbounded
finite reciprocal sums whenever the uniform bound fails.
-/

namespace Erdos3Weighted

/-- Removing zero does not change reciprocal weight. -/
@[simp] lemma weight_erase_zero (F : Finset ℕ) : weight (F.erase 0) = weight F := by
  exact Finset.sum_erase F (by simp)

/-- Dilation by a positive integer divides reciprocal weight by that integer. -/
lemma weight_dilate {c : ℕ} (hc : 0 < c) (E : Finset ℕ) :
    weight (E.image (fun n ↦ c * n)) = weight E / (c : ℝ) := by
  classical
  unfold weight
  rw [Finset.sum_image (fun _ _ _ _ h ↦ Nat.mul_left_cancel hc h), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  simp [Nat.cast_mul, div_eq_mul_inv, mul_comm]

/-- Positive integer dilation preserves exclusion of any length at least two. -/
lemma avoids_dilate {k c : ℕ} (hk : 2 ≤ k) (hc : 0 < c)
    {E : Set ℕ} (hE : Avoids k E) :
    Avoids k ((fun n : ℕ ↦ c * n) '' E) := by
  intro S hS hAP
  obtain ⟨a, d, hAP⟩ := hAP
  have hd : d ≠ 0 := Erdos3Reduction.isAPOfLengthWith_step_ne_zero hAP
    (by exact_mod_cast (show 1 < k by omega))
  have hterm : ∀ n : ℕ, n < k → a + n * d ∈ (fun n : ℕ ↦ c * n) '' E := by
    intro n hn
    apply hS
    rw [hAP.eq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  obtain ⟨b, hb, hab⟩ : a ∈ (fun n : ℕ ↦ c * n) '' E := by
    simpa only [zero_mul, add_zero] using hterm 0 (by omega)
  have hca : c ∣ a := ⟨b, hab.symm⟩
  have hcad : c ∣ a + d := by
    obtain ⟨u, _, hu⟩ := hterm 1 (by omega)
    exact ⟨u, by simpa only [one_mul] using hu.symm⟩
  obtain ⟨e, he⟩ := (Nat.dvd_add_iff_right hca).mpr hcad
  have he0 : e ≠ 0 := by
    intro he0
    apply hd
    simp [he, he0]
  refine hE _ ?_ ⟨b, e, Erdos3Reduction.isAPOfLengthWith_prefix he0 k⟩
  rintro x ⟨n, hn, rfl⟩
  obtain ⟨u, hu, hu'⟩ := hterm n (by exact_mod_cast hn)
  have hue : u = b + n • e := by
    apply Nat.mul_left_cancel hc
    calc
      c * u = a + n * d := hu'
      _ = c * (b + n • e) := by
        rw [← hab, he]
        simp only [nsmul_eq_mul, Nat.cast_id]
        ring
  simpa only [hue] using hu

/-- An AP of length at least three cannot cross from `[1, M]` to positive
multiples of `2 * M`. There is no upper bound on the upper block. -/
lemma isAPOfLength_subset_or_subset_of_multiples
    {M k : ℕ} {X Y S : Set ℕ} (hM : 1 ≤ M) (hk : 3 ≤ k)
    (hX : X ⊆ Set.Icc 1 M)
    (hY : ∀ y ∈ Y, 2 * M ≤ y ∧ 2 * M ∣ y)
    (hAP : S.IsAPOfLength (k : ℕ∞)) (hsub : S ⊆ X ∪ Y) :
    S ⊆ X ∨ S ⊆ Y := by
  obtain ⟨a, d, hAP⟩ := hAP
  have hterm : ∀ n : ℕ, n < k → a + n * d ∈ X ∪ Y := by
    intro n hn
    apply hsub
    rw [hAP.eq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have ha := hterm 0 (by omega)
  simp only [zero_mul, add_zero] at ha
  rcases ha with ha | ha
  · obtain ⟨ha1, haM⟩ := hX ha
    have hfirst := hterm 1 (by omega)
    simp only [one_mul] at hfirst
    have hd : d < M := by
      rcases hfirst with hx | hy
      · have := (hX hx).2
        omega
      · obtain ⟨hfirst_ge, hfirst_dvd⟩ := hY _ hy
        have hthird : a + 2 * d ∈ Y := by
          rcases hterm 2 (by omega) with hx | hy
          · have := (hX hx).2
            omega
          · exact hy
        have hthird_dvd := (hY _ hthird).2
        have hdvd : 2 * M ∣ d := (Nat.dvd_add_iff_right hfirst_dvd).mpr (by
          convert hthird_dvd using 1
          omega)
        have hadvd : 2 * M ∣ a := (Nat.dvd_add_iff_left hdvd).mpr hfirst_dvd
        have := Nat.le_of_dvd (by omega : 0 < a) hadvd
        omega
    have hall : ∀ n : ℕ, n < k → a + n * d ∈ X := by
      intro n
      induction n with
      | zero =>
          intro _
          simpa only [zero_mul, add_zero] using ha
      | succ n ih =>
          intro hn
          have hprev : a + n * d ≤ M := (hX (ih (by omega))).2
          rcases hterm (n + 1) hn with hx | hy
          · exact hx
          · have hnext := (hY _ hy).1
            simp only [Nat.add_mul, one_mul] at hnext
            omega
    left
    rw [hAP.eq]
    rintro x ⟨n, hn, rfl⟩
    simpa only [nsmul_eq_mul] using hall n (by exact_mod_cast hn)
  · right
    rw [hAP.eq]
    rintro x ⟨n, hn, rfl⟩
    rcases hterm n (by exact_mod_cast hn) with hx | hy
    · have hstart := (hY _ ha).1
      have hbound := (hX hx).2
      omega
    · simpa only [nsmul_eq_mul] using hy

/-- Safe gluing when the upper block consists of positive multiples of `2 * M`. -/
lemma avoids_union_of_multiples {M k : ℕ} {X Y : Set ℕ}
    (hM : 1 ≤ M) (hk : 3 ≤ k) (hX : X ⊆ Set.Icc 1 M)
    (hY : ∀ y ∈ Y, 2 * M ≤ y ∧ 2 * M ∣ y)
    (hXfree : Avoids k X) (hYfree : Avoids k Y) : Avoids k (X ∪ Y) := by
  intro S hsub hAP
  rcases isAPOfLength_subset_or_subset_of_multiples hM hk hX hY hAP hsub with h | h
  · exact hXfree S h hAP
  · exact hYfree S h hAP

/-- Failure of uniform boundedness supplies arbitrarily heavy positive finite blocks. -/
lemma exists_positive_finite_weight_gt {k : ℕ} (h : ¬ UniformBound k) (C : ℝ) :
    ∃ E : Finset ℕ, (∀ n ∈ E, 1 ≤ n) ∧ Avoids k (E : Set ℕ) ∧ C < weight E := by
  classical
  have hex : ∃ E : Finset ℕ, Avoids k (E : Set ℕ) ∧ C < weight E := by
    by_contra hnone
    apply h
    refine ⟨C, ?_⟩
    intro F hF
    by_contra hlt
    exact hnone ⟨F, hF, lt_of_not_ge hlt⟩
  obtain ⟨E, hE, hCE⟩ := hex
  refine ⟨E.erase 0, ?_, avoids_subset hE ?_, ?_⟩
  · intro n hn
    have := (Finset.mem_erase.mp hn).1
    omega
  · intro n hn
    exact Finset.mem_of_mem_erase hn
  · simpa only [weight_erase_zero] using hCE

/-- Under failure of the uniform bound, every positive finite AP-free block has
an AP-free positive extension gaining at least one unit of reciprocal weight. -/
lemma exists_finite_extension {k : ℕ} (hk : 3 ≤ k) (hunb : ¬ UniformBound k)
    (F : Finset ℕ) (hF : Avoids k (F : Set ℕ)) (hFpos : ∀ n ∈ F, 1 ≤ n) :
    ∃ G : Finset ℕ, F ⊆ G ∧ Avoids k (G : Set ℕ) ∧
      (∀ n ∈ G, 1 ≤ n) ∧ weight F + 1 ≤ weight G := by
  classical
  let M : ℕ := max (F.sup id) 1
  have hM : 1 ≤ M := le_max_right _ _
  have hFM : (F : Set ℕ) ⊆ Set.Icc 1 M := by
    intro n hn
    exact ⟨hFpos n hn, (Finset.le_sup (f := id) hn).trans (le_max_left _ _)⟩
  obtain ⟨E, hEpos, hE, hWE⟩ := exists_positive_finite_weight_gt hunb (2 * M : ℕ)
  let D : Finset ℕ := E.image (fun n ↦ 2 * M * n)
  have hc : 0 < 2 * M := by omega
  have hD : Avoids k (D : Set ℕ) := by
    simpa only [D, Finset.coe_image] using avoids_dilate (by omega : 2 ≤ k) hc hE
  have hDmul : ∀ y ∈ (D : Set ℕ), 2 * M ≤ y ∧ 2 * M ∣ y := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨by simpa only [mul_one] using Nat.mul_le_mul_left (2 * M) (hEpos e he),
      ⟨e, rfl⟩⟩
  have hdis : Disjoint F D := by
    apply Finset.disjoint_left.mpr
    intro n hn hnD
    have := (hFM hn).2
    have := (hDmul n hnD).1
    omega
  have hfree : Avoids k ((F ∪ D : Finset ℕ) : Set ℕ) := by
    simpa only [Finset.coe_union] using avoids_union_of_multiples hM hk hFM hDmul hF hD
  have hDw : 1 ≤ weight D := by
    rw [show D = E.image (fun n ↦ 2 * M * n) from rfl, weight_dilate hc]
    apply (le_div_iff₀ (show (0 : ℝ) < (2 * M : ℕ) by exact_mod_cast hc)).mpr
    simpa only [one_mul] using le_of_lt hWE
  refine ⟨F ∪ D, Finset.subset_union_left, hfree, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hFpos n hn
    · have := (hDmul n hn).1
      omega
  · have hw : weight (F ∪ D) = weight F + weight D := Finset.sum_union hdis
    rw [hw]
    exact add_le_add le_rfl hDw

/-- Iterating positive finite extensions gives nested AP-free stages whose
weights dominate the stage index. -/
lemma exists_increasing_finite_stages {k : ℕ} (hk : 3 ≤ k) (hunb : ¬ UniformBound k) :
    ∃ F : ℕ → Finset ℕ, Monotone F ∧ (∀ n, Avoids k (F n : Set ℕ)) ∧
      (∀ n x, x ∈ F n → 1 ≤ x) ∧ ∀ n : ℕ, (n : ℝ) ≤ weight (F n) := by
  classical
  let Good := {F : Finset ℕ // Avoids k (F : Set ℕ) ∧ ∀ n ∈ F, 1 ≤ n}
  have hstep : ∀ F : Good, ∃ G : Good,
      F.val ⊆ G.val ∧ weight F.val + 1 ≤ weight G.val := by
    intro F
    obtain ⟨G, hFG, hG, hGpos, hw⟩ :=
      exists_finite_extension hk hunb F.val F.property.1 F.property.2
    exact ⟨⟨G, hG, hGpos⟩, hFG, hw⟩
  choose next hnext using hstep
  have hempty : Avoids k (∅ : Set ℕ) := by
    intro S hS hAP
    have hS0 : S = ∅ := Set.subset_empty_iff.mp hS
    have hk0 : k = 0 := by simpa [hS0] using hAP.card.symm
    omega
  let initial : Good := ⟨∅, by simpa only [Finset.coe_empty] using hempty, by simp⟩
  let seq : ℕ → Good := Nat.rec initial (fun _ F ↦ next F)
  let F : ℕ → Finset ℕ := fun n ↦ (seq n).val
  have hstep' : ∀ n, F n ⊆ F (n + 1) ∧ weight (F n) + 1 ≤ weight (F (n + 1)) :=
    fun n ↦ hnext (seq n)
  refine ⟨F, monotone_nat_of_le_succ (fun n ↦ (hstep' n).1), ?_, ?_, ?_⟩
  · exact fun n ↦ (seq n).property.1
  · exact fun n ↦ (seq n).property.2
  · intro n
    induction n with
    | zero => simp [F, seq, initial, weight]
    | succ n ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans (hstep' n).2

/-- A nested union preserves exclusion of a fixed finite AP length: every
finite progression in the union is contained in one stage. -/
lemma avoids_iUnion_of_monotone {k : ℕ} {F : ℕ → Finset ℕ}
    (hmono : Monotone F) (hfree : ∀ n, Avoids k (F n : Set ℕ)) :
    Avoids k (⋃ n, (F n : Set ℕ)) := by
  intro S hS hAP
  have hfinite : S.Finite := Set.finite_of_encard_eq_coe hAP.card
  have hdir : Directed (· ⊆ ·) (fun n ↦ (F n : Set ℕ)) := by
    intro i j
    exact ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  obtain ⟨n, hn⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion
    (s := hfinite.toFinset) (by simpa only [hfinite.coe_toFinset] using hS)
  exact hfree n S (by simpa only [hfinite.coe_toFinset] using hn) hAP

/-- Contrapositive uniformization: failure of the finite uniform estimate
produces an AP-free set with nonsummable reciprocal family. -/
theorem exists_avoids_not_summable_of_not_uniformBound {k : ℕ} (hk : 3 ≤ k)
    (hunb : ¬ UniformBound k) :
    ∃ A : Set ℕ, Avoids k A ∧ ¬ Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  obtain ⟨F, hmono, hfree, _, hweight⟩ := exists_increasing_finite_stages hk hunb
  let A : Set ℕ := ⋃ n, (F n : Set ℕ)
  refine ⟨A, avoids_iUnion_of_monotone hmono hfree, ?_⟩
  intro hs
  obtain ⟨C, hC⟩ := (summable_iff_bounded_finite_weight A).mp hs
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hCn : weight (F n) ≤ C := hC _ (Set.subset_iUnion (fun n ↦ (F n : Set ℕ)) n)
  exact (not_le_of_gt hn) ((hweight n).trans hCn)

/-- Summability for every set avoiding a fixed length at least three implies
a uniform bound on all finite reciprocal weights at that length. -/
theorem uniformBound_of_all_summable {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ A : Set ℕ, Avoids k A → Summable (fun a : A ↦ 1 / (a : ℝ))) :
    UniformBound k := by
  by_contra hunb
  obtain ⟨A, hA, hnot⟩ := exists_avoids_not_summable_of_not_uniformBound hk hunb
  exact hnot (h A hA)

/-- For lengths at least three, the uniform finite weighted estimate and
summability for every AP-free set are equivalent. Both remain hypotheses,
not unconditional conclusions about AP-free sets. -/
theorem uniformBound_iff_all_summable {k : ℕ} (hk : 3 ≤ k) :
    UniformBound k ↔ ∀ A : Set ℕ, Avoids k A → Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  constructor
  · intro h A hA
    exact summable_of_uniformBound h hA
  · exact uniformBound_of_all_summable hk

end Erdos3Weighted

#print axioms Erdos3Weighted.weight_erase_zero
#print axioms Erdos3Weighted.weight_dilate
#print axioms Erdos3Weighted.avoids_dilate
#print axioms Erdos3Weighted.isAPOfLength_subset_or_subset_of_multiples
#print axioms Erdos3Weighted.avoids_union_of_multiples
#print axioms Erdos3Weighted.exists_positive_finite_weight_gt
#print axioms Erdos3Weighted.exists_finite_extension
#print axioms Erdos3Weighted.exists_increasing_finite_stages
#print axioms Erdos3Weighted.avoids_iUnion_of_monotone
#print axioms Erdos3Weighted.exists_avoids_not_summable_of_not_uniformBound
#print axioms Erdos3Weighted.uniformBound_of_all_summable
#print axioms Erdos3Weighted.uniformBound_iff_all_summable
