import Submission.SumsetIncidence

/-! Finite sumset bounds, with either Sidonness or a translate-intersection bound. -/
namespace Erdos773.SidonInSumset
open Finset SumsetIncidence
open scoped Pointwise
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] Classical.propDecidable

lemma card_le_incidences (S X Y : Finset ℕ) (hcover : S ⊆ X+Y) :
    S.card ≤ incidenceCount X Y (fun x y => x+y ∈ S) := by
  have hsub : S ⊆ X.biUnion (fun x => (Y.filter (fun y => x+y ∈ S)).image (x+·)) := by
    intro s hs
    obtain ⟨x,hx,y,hy,he⟩ := mem_add.mp (hcover hs)
    apply mem_biUnion.mpr
    exact ⟨x,hx,mem_image.mpr ⟨y,mem_filter.mpr ⟨hy,by simpa [he] using hs⟩,he⟩⟩
  calc
    S.card ≤ (X.biUnion (fun x => (Y.filter (fun y => x+y ∈ S)).image (x+·))).card :=
      card_le_card hsub
    _ ≤ ∑ x ∈ X, ((Y.filter (fun y => x+y ∈ S)).image (x+·)).card := card_biUnion_le
    _ ≤ incidenceCount X Y (fun x y => x+y ∈ S) := by
      exact sum_le_sum (fun x hx => card_image_le)

lemma sidon_common_neighbors (S X : Finset ℕ) (hS : IsSidon (S : Set ℕ))
    (y z : ℕ) (hyz : y ≠ z) :
    (X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx w hw
  obtain ⟨_,hxy,hxz⟩ := mem_filter.mp hx
  obtain ⟨_,hwy,hwz⟩ := mem_filter.mp hw
  rcases hS (x+y) hxy (x+z) hxz (w+z) hwz (w+y) hwy (by omega) with h | h <;> omega

/-- A Sidon set inside X+Y has at most |Y| sqrt(|X|)+|X| elements. -/
theorem card_le (S X Y : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (hcover : S ⊆ X+Y) :
    (S.card : ℝ) ≤ Y.card*Real.sqrt X.card + X.card := by
  have hcommon : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      ((X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card : ℝ) ≤ 1 := by
    intro y hy z hz hyz
    exact_mod_cast sidon_common_neighbors S X hS y z hyz
  have hc : (S.card : ℝ) ≤ incidenceCount X Y (fun x y => x+y ∈ S) := by
    exact_mod_cast card_le_incidences S X Y hcover
  exact hc.trans (by simpa using incidence_le X Y (fun x y => x+y ∈ S) 1 (by norm_num) hcommon)

/-- A bound for the actual maximal Sidon cardinality, not just for a chosen subset. -/
theorem max_card_le (A X Y : Finset ℕ) (hcover : A ⊆ X+Y) :
    (maxSidonSubsetCard A : ℝ) ≤ Y.card*Real.sqrt X.card + X.card := by
  have hmax : ∃ S : Finset ℕ, S ⊆ A ∧ IsSidon (S : Set ℕ) ∧ S.card=maxSidonSubsetCard A := by
    have hn : (A.powerset.filter (fun S : Finset ℕ => IsSidon (S : Set ℕ))).Nonempty := by
      refine ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩⟩
      simp [IsSidon]
    obtain ⟨S,hS,hcard⟩ := exists_mem_eq_sup _ hn card
    obtain ⟨hSA,hSidon⟩ := mem_filter.mp hS
    exact ⟨S,mem_powerset.mp hSA,hSidon,hcard.symm⟩
  obtain ⟨S,hSA,hS,he⟩ := hmax
  rw [← he]
  exact card_le S X Y hS (hSA.trans hcover)

/-- Translate-intersection bounds give bounded common neighborhoods. -/
lemma common_neighbors_le (S X : Finset ℕ) (K : ℝ)
    (htranslate : ∀ D : ℕ, 0 < D → ((S.filter (fun a => a+D ∈ S)).card : ℝ) ≤ K)
    (y z : ℕ) (hyz : y ≠ z) :
    ((X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card : ℝ) ≤ K := by
  have hordered (y z : ℕ) (hyz : y < z) :
      ((X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card : ℝ) ≤ K := by
    have hcard : (X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card ≤
        (S.filter (fun a => a+(z-y) ∈ S)).card := by
      apply card_le_card_of_injOn (fun x => x+y)
      · intro x hx
        obtain ⟨_,hxy,hxz⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨hxy,by simpa [show x+y+(z-y)=x+z by omega] using hxz⟩
      · intro x hx w hw he
        change x+y=w+y at he
        omega
    exact (show ((X.filter (fun x => x+y ∈ S ∧ x+z ∈ S)).card : ℝ) ≤
      (S.filter (fun a => a+(z-y) ∈ S)).card by exact_mod_cast hcard).trans
        (htranslate (z-y) (by omega))
  rcases lt_or_gt_of_ne hyz with h | h
  · exact hordered y z h
  · simpa only [and_comm] using hordered z y h

/-- Sumset-cover cardinality bound for a set with bounded nonzero translates. -/
theorem card_le_of_translate_bound (S X Y : Finset ℕ) (hcover : S ⊆ X+Y)
    (K : ℝ) (hK : 0 ≤ K)
    (htranslate : ∀ D : ℕ, 0 < D → ((S.filter (fun a => a+D ∈ S)).card : ℝ) ≤ K) :
    (S.card : ℝ) ≤ Y.card*Real.sqrt (X.card*K) + X.card := by
  have hc : (S.card : ℝ) ≤ incidenceCount X Y (fun x y => x+y ∈ S) := by
    exact_mod_cast card_le_incidences S X Y hcover
  exact hc.trans (incidence_le X Y (fun x y => x+y ∈ S) K hK
    (fun y hy z hz hyz => common_neighbors_le S X K htranslate y z hyz))

#print axioms card_le
#print axioms max_card_le
#print axioms card_le_of_translate_bound
end
end Erdos773.SidonInSumset
