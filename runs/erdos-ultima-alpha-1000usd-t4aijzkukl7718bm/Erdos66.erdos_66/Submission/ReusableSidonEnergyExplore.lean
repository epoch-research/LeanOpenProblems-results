import Submission.ReusableSidonTemplateExplore

/-! A second-moment budget for the designated profile of a reusable Sidon
template. This quantifies point reuse without assuming such templates exist
for arbitrary exceptional sets. -/
namespace Erdos66ReusableSidonEnergy
open Erdos66OriginRepair Erdos66SymmetricSidon Erdos66ReusableSidonTemplate
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def partners (U V : Finset ℤ) (z : ℤ) : Finset ℤ :=
  U.filter (fun u ↦ z-u ∈ V)

lemma partners_card (U V : Finset ℤ) (z : ℤ) :
    (partners U V z).card = pairCount U V z := rfl

/-- If V is Sidon, two distinct U-vertices can both participate at at most
one common target. -/
lemma two_vertices_target_unique (U V : Finset ℤ) (hV : IsSidon V)
    {u v z w : ℤ} (huv : u ≠ v)
    (huz : u ∈ partners U V z) (hvz : v ∈ partners U V z)
    (huw : u ∈ partners U V w) (hvw : v ∈ partners U V w) : z = w := by
  have h1 : z-u ∈ V := (Finset.mem_filter.mp huz).2
  have h2 : z-v ∈ V := (Finset.mem_filter.mp hvz).2
  have h3 : w-u ∈ V := (Finset.mem_filter.mp huw).2
  have h4 : w-v ∈ V := (Finset.mem_filter.mp hvw).2
  have hh := hV (z-u) h1 (w-v) h4 (z-v) h2 (w-u) h3 (by omega)
  rcases hh with ⟨he,_⟩ | ⟨he,_⟩ <;> omega

lemma partner_offDiag_disjoint (U V : Finset ℤ) (hV : IsSidon V) (T : Finset ℤ) :
    (T : Set ℤ).PairwiseDisjoint (fun z ↦ (partners U V z).offDiag) := by
  intro z hz w hw hzw
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hp1,hp2,hne⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hq1,hq2,_⟩ := Finset.mem_offDiag.mp hq
  exact hzw (two_vertices_target_unique U V hV hne hp1 hp2 hq1 hq2)

lemma mixed_second_factorial_bound (U V T : Finset ℤ) (hV : IsSidon V) :
    (∑ z ∈ T, pairCount U V z*(pairCount U V z-1)) ≤ U.card*(U.card-1) := by
  have hdis := partner_offDiag_disjoint U V hV T
  have hsub : T.biUnion (fun z ↦ (partners U V z).offDiag) ⊆ U.offDiag := by
    intro p hp
    obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.offDiag_mono (Finset.filter_subset _ _) hp
  have hh := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis, Finset.offDiag_card] at hh
  simp_rw [Finset.offDiag_card, partners_card] at hh
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using hh

lemma high_target_budget (U V T : Finset ℤ) (hU : IsSidon U) (hV : IsSidon V)
    (k : ℕ) (hk : ∀ z ∈ T, k ≤ pairCount U V z) :
    T.card*k*(k-1) ≤ min (U.card*(U.card-1)) (V.card*(V.card-1)) := by
  have hcost : T.card*k*(k-1) ≤ ∑ z ∈ T, pairCount U V z*(pairCount U V z-1) := by
    have hh := Finset.sum_le_sum (fun z hz ↦
      Nat.mul_le_mul (hk z hz) (Nat.sub_le_sub_right (hk z hz) 1))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hh
  apply le_min
  · exact hcost.trans (mixed_second_factorial_bound U V T hV)
  · have hh := mixed_second_factorial_bound V U T hU
    simp_rw [pairCount_comm V U] at hh
    exact hcost.trans hh

/-- A k-fold profile on T requires both Sidon halves to have at least
sqrt(|T| k(k-1)) points, even though a vertex may serve many targets. -/
lemma reusable_card_lower (U V T : Finset ℤ) (hU : IsSidon U) (hV : IsSidon V)
    (k : ℕ) (hk : ∀ z ∈ T, k ≤ pairCount U V z)
    (t : ℤ) (hdis : Disjoint (shift t U) (shift (-t) V)) :
    2*Real.sqrt ((T.card : ℝ)*k*(k-1 : ℕ)) ≤ (reusable U V t).card := by
  have hb := high_target_budget U V T hU hV k hk
  have h1 := hb.trans (min_le_left _ _)
  have h2 := hb.trans (min_le_right _ _)
  have h1' : (T.card : ℝ)*k*(k-1 : ℕ) ≤ (U.card : ℝ)^2 := by
    have hh : T.card*k*(k-1) ≤ U.card^2 :=
      h1.trans (by nlinarith [Nat.sub_le U.card 1])
    exact_mod_cast hh
  have h2' : (T.card : ℝ)*k*(k-1 : ℕ) ≤ (V.card : ℝ)^2 := by
    have hh : T.card*k*(k-1) ≤ V.card^2 :=
      h2.trans (by nlinarith [Nat.sub_le V.card 1])
    exact_mod_cast hh
  have hs1 := Real.sqrt_le_sqrt h1'
  have hs2 := Real.sqrt_le_sqrt h2'
  rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hs1 hs2
  rw [reusable_card U V t hdis, Nat.cast_add]
  linarith

end Erdos66ReusableSidonEnergy
