import FormalConjecturesUtil

/-!
Harmonic-quadruple-free subsets of finite fields of odd characteristic have
vanishing density. This is an obstruction to a possible row-selection rule,
not a proof or disproof of the extremal graph conjecture in Spec.lean.
-/
noncomputable section
open Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714Harmonic
variable {F : Type*} [Field F]

/-- The denominator-free cross-ratio-minus-one equation. -/
def Harmonic (a b c d : F) : Prop :=
  (a-b)*(c-d)+(a-d)*(c-b)=0

/-- Repeated points are explicitly excluded from forbidden quadruples. -/
def HarmonicFree (S : Set F) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ∀ ⦃c⦄, c ∈ S → ∀ ⦃d⦄, d ∈ S →
    Harmonic a b c d → a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d

lemma inversion_injective (a : F) : Function.Injective (fun x : F => (x-a)⁻¹) := by
  intro x y h
  have hh := inv_injective h
  linear_combination hh

lemma harmonic_of_inverted_progression {a b c d : F}
    (hb : b≠a) (hc : c≠a) (hd : d≠a)
    (h : (b-a)⁻¹+(d-a)⁻¹=(c-a)⁻¹+(c-a)⁻¹) : Harmonic a b c d := by
  have hb0 := sub_ne_zero.mpr hb
  have hc0 := sub_ne_zero.mpr hc
  have hd0 := sub_ne_zero.mpr hd
  field_simp at h
  dsimp [Harmonic]
  linear_combination -h

/-- Inversion about any selected point turns the remaining set into a 3AP-free set. -/
theorem inverted_threeAPFree (h2 : (2:F)≠0) {S : Finset F}
    (hS : HarmonicFree (S : Set F)) {a : F} (ha : a∈S) :
    ThreeAPFree (((S.erase a).image (fun x => (x-a)⁻¹)) : Set F) := by
  intro u hu v hv w hw he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hu
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hv
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hw
  obtain ⟨hba,hb⟩ := mem_erase.mp hb
  obtain ⟨hca,hc⟩ := mem_erase.mp hc
  obtain ⟨hda,hd⟩ := mem_erase.mp hd
  have hh := harmonic_of_inverted_progression hba hca hda he
  rcases hS ha hb hc hd hh with h | h | h | h | h | h
  · exact False.elim (hba h.symm)
  · exact False.elim (hca h.symm)
  · exact False.elim (hda h.symm)
  · exact congrArg (fun x => (x-a)⁻¹) h
  · subst d
    have hh : (2:F)*((b-a)⁻¹-(c-a)⁻¹)=0 := by linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left h2)
  · subst d
    exact add_right_cancel he

/-- A finite, quantitative version: all but one selected point obey Roth's bound. -/
theorem card_sub_one_lt [Fintype F] (h2 : (2:F)≠0)
    (ε : ℝ) (hε : 0<ε) (hF : cornersTheoremBound ε ≤ Fintype.card F)
    {S : Finset F} (hS : HarmonicFree (S : Set F)) :
    (S.card : ℝ)-1 < ε*Fintype.card F := by
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have hfree := inverted_threeAPFree h2 hS ha
    have hc : ((S.erase a).image (fun x => (x-a)⁻¹)).card = S.card-1 := by
      rw [card_image_of_injective _ (inversion_injective a), card_erase_of_mem ha]
    have hn : 1≤S.card := card_pos.mpr ⟨a,ha⟩
    by_contra h
    have hbound : ε*Fintype.card F ≤
        (((S.erase a).image (fun x => (x-a)⁻¹)).card : ℝ) := by
      rw [hc,Nat.cast_sub hn,Nat.cast_one]
      exact le_of_not_gt h
    exact roth_3ap_theorem ε hε hF _ hbound hfree
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
    subst S
    simp only [card_empty,Nat.cast_zero,zero_sub]
    have hpos : (0:ℝ)<ε*Fintype.card F := mul_pos hε (by exact_mod_cast Fintype.card_pos)
    linarith

/-- A threshold uniform over all finite fields with injective doubling. -/
theorem density_bound (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (F : Type) [Field F] [Fintype F], (2:F)≠0 →
      N≤Fintype.card F → ∀ S : Finset F, HarmonicFree (S : Set F) →
        (S.card : ℝ)<ε*Fintype.card F := by
  obtain ⟨M,hM⟩ := exists_nat_ge (2/ε)
  refine ⟨max (cornersTheoremBound (ε/2)) M, ?_⟩
  intro F _ _ h2 hN S hS
  have hF : cornersTheoremBound (ε/2)≤Fintype.card F := (le_max_left _ _).trans hN
  have hM' : (2:ℝ)/ε≤Fintype.card F :=
    hM.trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have h1 : (1:ℝ)≤(ε/2)*Fintype.card F := by
    have hh := (div_le_iff₀ hε).mp hM'
    nlinarith
  have hh := card_sub_one_lt h2 (ε/2) (by positivity) hF hS
  linarith

#print axioms harmonic_of_inverted_progression
#print axioms inverted_threeAPFree
#print axioms card_sub_one_lt
#print axioms density_bound
end Erdos714Harmonic
