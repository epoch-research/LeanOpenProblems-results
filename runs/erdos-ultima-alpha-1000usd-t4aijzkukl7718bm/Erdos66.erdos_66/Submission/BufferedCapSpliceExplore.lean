import Submission.PointwiseCapBlockingExplore

/-! Finite-prefix splicing under unbounded additive headroom.
This does not supply asymptotic lower representation bounds. -/
namespace Erdos66BufferedCapSplice
open Filter AdditiveCombinatorics Erdos66Explore Erdos66Compactness
  Erdos66NaturalRepairBridge Erdos66PointwiseCapBlocking
open scoped Classical Topology

noncomputable def splice (A : Set ℕ) (F : Finset ℕ) (L : ℕ) : Set ℕ :=
  (A ∩ Set.Ici L) ∪ (F : Set ℕ)

lemma splice_below (A : Set ℕ) (F : Finset ℕ) (L a : ℕ) (ha : a < L) :
    a ∈ splice A F L ↔ a ∈ F := by
  simp [splice, show ¬L ≤ a by omega]

lemma splice_above (A : Set ℕ) (F : Finset ℕ) (L a : ℕ)
    (hF : ∀ x ∈ F, x < L) (ha : L ≤ a) :
    a ∈ splice A F L ↔ a ∈ A := by
  have hn : a ∉ F := by intro h; have := hF a h; omega
  simp [splice, ha, hn]

lemma splice_rep_below (A : Set ℕ) (F : Finset ℕ) (L n : ℕ) (hn : n < L) :
    sumRep (splice A F L) n = sumRep (F : Set ℕ) n := by
  apply sumRep_congr_below
  intro a ha
  exact splice_below A F L a (by omega)

lemma splice_rep_le (A : Set ℕ) (F : Finset ℕ) (L n : ℕ) :
    sumRep (splice A F L) n ≤ sumRep A n + 2 * F.card := by
  apply (sumRep_mono (B := A ∪ (F : Set ℕ)) ?_ n).trans
    (sumRep_union_finset_le A F n)
  rintro a (ha | ha)
  · exact Or.inl ha.1
  · exact Or.inr ha

/-- Every finite capped pattern can be spliced onto a sufficiently remote
    tail with unbounded additive cap headroom. -/
theorem exists_capped_splice (q : ℕ → ℕ) (A : Set ℕ)
    (hhead : ∀ m : ℕ, ∀ᶠ n in atTop, sumRep A n + m ≤ q n)
    (F : Finset ℕ) (hF : Capped q (F : Set ℕ)) (L₀ : ℕ) :
    ∃ L ≥ L₀, (∀ x ∈ F, x < L) ∧ Capped q (splice A F L) ∧
      (∀ a < L, a ∈ splice A F L ↔ a ∈ F) ∧
      (∀ a, L ≤ a → (a ∈ splice A F L ↔ a ∈ A)) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hhead (2*F.card))
  let L := max L₀ (max T (F.sup id + 1))
  have hLT : T ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLF : ∀ x ∈ F, x < L := by
    intro x hx
    have hx' : x ≤ F.sup id := Finset.le_sup (f := id) hx
    have : F.sup id + 1 ≤ L := (le_max_right _ _).trans (le_max_right _ _)
    omega
  refine ⟨L, le_max_left _ _, hLF, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n < L
    · rw [splice_rep_below A F L n hn]
      exact hF n
    · exact (splice_rep_le A F L n).trans (hT n (by omega))
  · exact fun a ha ↦ splice_below A F L a ha
  · exact fun a ha ↦ splice_above A F L a hLF ha

lemma sumRep_le_of_agree_above (A B : Set ℕ) (L n : ℕ)
    (h : ∀ a, L ≤ a → (a ∈ A ↔ a ∈ B)) :
    sumRep A n ≤ sumRep B n + 2*L := by
  have hsub : A ⊆ B ∪ (Finset.range L : Set ℕ) := by
    intro a ha
    by_cases hb : L ≤ a
    · exact Or.inl ((h a hb).mp ha)
    · exact Or.inr (Finset.mem_range.mpr (by omega))
  simpa using (sumRep_mono hsub n).trans (sumRep_union_finset_le B (Finset.range L) n)

lemma sumRep_abs_sub_le_of_agree_above (A B : Set ℕ) (L n : ℕ)
    (h : ∀ a, L ≤ a → (a ∈ A ↔ a ∈ B)) :
    |(sumRep A n : ℝ) - sumRep B n| ≤ 2*(L:ℝ) := by
  have h₁ := sumRep_le_of_agree_above A B L n h
  have h₂ := sumRep_le_of_agree_above B A L n (fun a ha ↦ (h a ha).symm)
  have h₁' : (sumRep A n : ℝ) ≤ sumRep B n + 2*(L:ℝ) := by exact_mod_cast h₁
  have h₂' : (sumRep B n : ℝ) ≤ sumRep A n + 2*(L:ℝ) := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma normalized_limit_of_agree_above (A B : Set ℕ) (L : ℕ) (c : ℝ)
    (h : ∀ a, L ≤ a → (a ∈ A ↔ a ∈ B))
    (hA : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  have hz : Tendsto (fun n : ℕ ↦ (2*(L:ℝ))/Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl := hA.sub hz
  have hu := hA.add hz
  simp only [sub_zero, add_zero] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 2] with n hn
    rw [←sub_div]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    have hh := (abs_le.mp (sumRep_abs_sub_le_of_agree_above A B L n h)).2
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    have hh := (abs_le.mp (sumRep_abs_sub_le_of_agree_above A B L n h)).1
    linarith

end Erdos66BufferedCapSplice
