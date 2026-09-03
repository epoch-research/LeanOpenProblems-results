import Submission.DilutingDenseExtensionExplore

/-! Finite nested palettes, their cardinality bound, and multiplicative density
coverage. These lemmas prepare a finite saturation argument. -/
namespace Erdos66FinitePaletteGeometry
open Erdos66GroupRepBernoulli Erdos66DenseGroupExtension
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 1500000

def Flat (η : ℝ) (C D : Finset G) : Prop :=
  ∀ z, |(count C D z : ℝ)-actualMean C D| ≤ η*actualMean C D

def Nested (P : Finset (Finset G)) : Prop :=
  ∀ C∈P, ∀ D∈P, C ⊆ D ∨ D ⊆ C

def FlatPalette (η : ℝ) (P : Finset (Finset G)) : Prop :=
  ∀ C∈P, ∀ D∈P, Flat η C D

/-- Every density above the starting cardinality, if reached at all by the
palette, is reached without a multiplicative overshoot greater than R. -/
def Covers (C₀ : Finset G) (R : ℝ) (P : Finset (Finset G)) : Prop :=
  ∀ x : ℝ, (C₀.card : ℝ) ≤ x → (∃ C∈P, x ≤ (C.card : ℝ)) →
    ∃ D∈P, x ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ R*x

lemma count_comm (C D : Finset G) (z : G) : count C D z=count D C z := by
  have he : (count C D z : ℝ)=(count D C z : ℝ) := by
    rw [count_indicator,count_indicator,←Equiv.sum_comp (Equiv.subLeft z)]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Equiv.subLeft_apply,sub_sub_cancel,mul_comm]
  exact_mod_cast he

lemma mean_comm (C D : Finset G) : actualMean C D=actualMean D C := by
  unfold actualMean
  ring

lemma flat_symm {η : ℝ} {C D : Finset G} (h : Flat η C D) : Flat η D C := by
  intro z
  simpa only [count_comm D C,mean_comm D C] using h z

lemma flat_full (η : ℝ) (hη : 0 ≤ η) (C : Finset G) : Flat η C Finset.univ := by
  have hn := (card_group_pos (G := G)).ne'
  intro z
  simp only [count,Finset.mem_univ,Finset.filter_true,actualMean,Finset.card_univ]
  rw [mul_div_cancel_right₀ _ hn,sub_self,abs_zero]
  positivity

lemma nested_card_le {P : Finset (Finset G)} (hP : Nested P) :
    P.card ≤ Fintype.card G+1 := by
  calc
    _ ≤ (Finset.range (Fintype.card G+1)).card := by
      apply Finset.card_le_card_of_injOn Finset.card
      · intro C hC
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ C))
      · intro C hC D hD he
        rcases hP C hC D hD with h | h
        · exact Finset.eq_of_subset_of_card_le h he.ge
        · exact (Finset.eq_of_subset_of_card_le h he.le).symm
    _ = _ := Finset.card_range _

lemma nested_max {P : Finset (Finset G)} (hP : Nested P) (hne : P.Nonempty) :
    ∃ C∈P, ∀ D∈P, D ⊆ C := by
  obtain ⟨C,hC,hmax⟩ := P.exists_max_image Finset.card hne
  refine ⟨C,hC,fun D hD ↦ ?_⟩
  rcases hP D hD C hC with h | h
  · exact h
  · have he : C=D := Finset.eq_of_subset_of_card_le h (hmax D hD)
    simpa only [he] using (Finset.Subset.refl D)

lemma nested_insert {P : Finset (Finset G)} {B : Finset G}
    (hP : Nested P) (hB : ∀ C∈P, C ⊆ B) : Nested (insert B P) := by
  intro C hC D hD
  rcases Finset.mem_insert.mp hC with he | hC
  · subst C
    rcases Finset.mem_insert.mp hD with he | hD
    · subst D; exact Or.inl (Finset.Subset.refl B)
    · exact Or.inr (hB D hD)
  · rcases Finset.mem_insert.mp hD with he | hD
    · subst D; exact Or.inl (hB C hC)
    · exact hP C hC D hD

lemma flatPalette_insert {η : ℝ} {P : Finset (Finset G)} {B : Finset G}
    (hP : FlatPalette η P) (hBB : Flat η B B) (hB : ∀ C∈P, Flat η C B) :
    FlatPalette η (insert B P) := by
  intro C hC D hD
  rcases Finset.mem_insert.mp hC with he | hC
  · subst C
    rcases Finset.mem_insert.mp hD with he | hD
    · subst D; exact hBB
    · exact flat_symm (hB D hD)
  · rcases Finset.mem_insert.mp hD with he | hD
    · subst D; exact hB C hC
    · exact hP C hC D hD

lemma covers_initial {C₀ : Finset G} {R : ℝ} {P : Finset (Finset G)}
    (hR : 1 ≤ R) (hC₀ : C₀∈P) (hmax : ∀ C∈P, C ⊆ C₀) : Covers C₀ R P := by
  intro x hx ⟨C,hC,hxC⟩
  have hc : (C.card : ℝ) ≤ C₀.card := by exact_mod_cast Finset.card_le_card (hmax C hC)
  have he : x=(C₀.card : ℝ) := by linarith
  refine ⟨C₀,hC₀,by linarith,?_⟩
  rw [he]
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hR

lemma covers_insert {C₀ C B : Finset G} {R : ℝ} {P : Finset (Finset G)}
    (hR : 0 ≤ R) (hP : Covers C₀ R P) (hC : C∈P)
    (hB : (B.card : ℝ) ≤ R*C.card) : Covers C₀ R (insert B P) := by
  intro x hx ⟨D,hD,hxD⟩
  rcases Finset.mem_insert.mp hD with he | hD
  · subst D
    by_cases hxC : x ≤ (C.card : ℝ)
    · obtain ⟨E,hE,hxE,hEup⟩ := hP x hx ⟨C,hC,hxC⟩
      exact ⟨E,Finset.mem_insert_of_mem hE,hxE,hEup⟩
    · exact ⟨B,Finset.mem_insert_self _ _,hxD,
        hB.trans (mul_le_mul_of_nonneg_left (le_of_not_ge hxC) hR)⟩
  · obtain ⟨E,hE,hxE,hEup⟩ := hP x hx ⟨D,hD,hxD⟩
    exact ⟨E,Finset.mem_insert_of_mem hE,hxE,hEup⟩

end Erdos66FinitePaletteGeometry
