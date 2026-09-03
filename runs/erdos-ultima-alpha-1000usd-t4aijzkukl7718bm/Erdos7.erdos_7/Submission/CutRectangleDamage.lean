import Submission.RectangleFamilies

/-! A location-sensitive weighted union bound. Unlike an area-only estimate,
this controls every cut rectangle. Labels remain independent throughout. -/
namespace Erdos7CutRectangleDamage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

noncomputable def mass (ρ : A → ℝ) (P : A → Prop) : ℝ :=
  ∑ x, if P x then ρ x else 0

lemma mass_nonneg (ρ : A → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (P : A → Prop) :
    0 ≤ mass ρ P := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> [exact hρ x; exact le_rfl]

lemma mass_mono (ρ : A → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (P Q : A → Prop)
    (hPQ : ∀ x, P x → Q x) : mass ρ P ≤ mass ρ Q := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp only [if_pos hp, if_pos (hPQ x hp)]
    exact le_rfl
  · simp only [if_neg hp]
    split_ifs <;> [exact hρ x; exact le_rfl]

lemma intersection_bound (ρ : A → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (P X : A → Prop) (r : ℝ) (hX : mass ρ X ≤ r) :
    mass ρ (fun x => P x ∧ X x) ≤ min (mass ρ P) r := by
  exact le_min (mass_mono ρ hρ _ _ (fun _ h => h.1))
    ((mass_mono ρ hρ _ _ (fun _ h => h.2)).trans hX)

lemma rectangle_mass (ρ : A → ℝ) (σ : B → ℝ)
    (P : A → Prop) (Q : B → Prop) :
    mass (fun z : A × B => ρ z.1 * σ z.2) (fun z => P z.1 ∧ Q z.2) =
      mass ρ P * mass σ Q := by
  unfold mass
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp : P x <;> by_cases hq : Q y <;> simp [hp,hq]

/-- For each cut P×Q, retain the separate row and column size of every
covering rectangle. The weight w(i) may depend on old coordinates, but no
identification of different labels is made. -/
theorem cut_damage_bound (ρ : A → ℝ) (σ : B → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ y, 0 ≤ σ y)
    (w r c : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : I → A → Prop) (Y : I → B → Prop) (D : A → B → Prop)
    (hD : ∀ x y, D x y → ∃ i, w i = 1 ∧ X i x ∧ Y i y)
    (hX : ∀ i, mass ρ (X i) ≤ r i) (hY : ∀ i, mass σ (Y i) ≤ c i)
    (P : A → Prop) (Q : B → Prop) :
    mass (fun z : A × B => ρ z.1 * σ z.2)
      (fun z => P z.1 ∧ Q z.2 ∧ D z.1 z.2) ≤
      ∑ i, w i * min (mass ρ P) (r i) * min (mass σ Q) (c i) := by
  have hh := Erdos7CompleteFamilyModel.weighted_event_union_bound
    (fun z : A × B => ρ z.1*σ z.2)
    (fun z : A × B => mul_nonneg (hρ z.1) (hσ z.2)) w
    (fun i => min (mass ρ P) (r i) * min (mass σ Q) (c i)) hw
    (fun (i : I) (z : A × B) => (P z.1 ∧ X i z.1) ∧ (Q z.2 ∧ Y i z.2))
    (fun z : A × B => P z.1 ∧ Q z.2 ∧ D z.1 z.2) ?_ ?_
  · simpa only [mass,mul_assoc] using hh
  · rintro ⟨x,y⟩ ⟨hp,hq,hd⟩
    obtain ⟨i,hi,hix,hiy⟩ := hD x y hd
    exact ⟨i,hi,⟨hp,hix⟩,⟨hq,hiy⟩⟩
  · intro i
    have hb := mul_le_mul (intersection_bound ρ hρ P (X i) (r i) (hX i))
      (intersection_bound σ hσ Q (Y i) (c i) (hY i))
      (mass_nonneg σ hσ _) (le_min (mass_nonneg ρ hρ P)
        ((mass_nonneg ρ hρ (X i)).trans (hX i)))
    rw [← rectangle_mass] at hb
    simpa only [mass] using hb


#print axioms cut_damage_bound
end Erdos7CutRectangleDamage
