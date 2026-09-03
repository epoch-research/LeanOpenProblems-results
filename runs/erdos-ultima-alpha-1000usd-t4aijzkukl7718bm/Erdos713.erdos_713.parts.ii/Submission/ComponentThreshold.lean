import FormalConjecturesUtil
import Submission.CompactCycleAssemblyAudit

/-! Attained superlinear thresholds, unlike exact leading constants, pass to
at least one connected component. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713Rate

lemma HasRate.unique {W : Type*} {G : SimpleGraph W} {r s : ℝ}
    (hr : HasRate G r) (hs : HasRate G s) : r = s :=
  le_antisymm (hr.lower s hs.one_le hs.upper) (hs.lower r hr.one_le hr.upper)

lemma rate_of_asymptotic {W : Type*} {G : SimpleGraph W} {a c : ℝ}
    (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^a)) : HasRate G a := by
  refine ⟨ha,(isBigO_const_mul_right_iff hc).mp h.isBigO,?_⟩
  intro r hr hu
  exact Erdos713Forest.exponent_le_of_isBigO
    (((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans hu)

lemma sum_upper {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) {r : ℝ} (hr : 1 ≤ r)
    (h₁ : (fun n : ℕ => (extremalNumber n H₁ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r))
    (h₂ : (fun n : ℕ => (extremalNumber n H₂ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r) := by
  have hB := shifted_upper (by linarith : 0 ≤ r) (Fintype.card A) h₂
  have hC := cast_linear_bigO hr (Fintype.card A)
  apply IsBigO.trans _ ((h₁.add hB).add hC)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (by positivity),one_mul]
  exact_mod_cast Erdos713Union.extremal_sum_bound H₁ H₂ n
end Erdos713Rate

namespace Erdos713ComponentRates
open Erdos713Rate
universe u v

/-- Finitely many subcritical fibre bounds combine to one subcritical bound.
The set of labels may be infinite: only finitely many fibres are inhabited. -/
lemma subcritical_upper_of_fibres {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I) {r : ℝ} (hr : 1 < r)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v)
    (hR : ∀ i, ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (fun n : ℕ => (extremalNumber n (G.induce {w | χ w = i}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^a)) :
    ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^a) := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (χ : W → I),
      (∀ u v, G.Adj u v → χ u = χ v) →
      (∀ i, ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n (G.induce {w | χ w = i}) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) →
        ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
          (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^a) from
    hP _ W rfl G χ hχ hR
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G χ hχ hR
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      exact ⟨1,le_rfl,hr,(forest_rate G (by intro v; exact isEmptyElim v)).upper⟩
    let w : W := hne.some
    let i : I := χ w
    let S : Set W := {v | χ v = i}
    have hsmall : Fintype.card ↥(Sᶜ) < k :=
      (Fintype.card_subtype_lt (x := w) (by simp [S,i])).trans_eq hW
    have hχ' : ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Adj u v → χ u.val = χ v.val := by
      intro u v huv
      exact hχ _ _ huv
    have hR' : ∀ j, ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n
          ((G.induce Sᶜ).induce {v : ↥(Sᶜ) | χ v.val = j}) : ℝ)) =O[atTop]
            (fun n : ℕ => (n : ℝ)^a) := by
      intro j
      by_cases hj : j = i
      · subst j
        letI : IsEmpty {v : ↥(Sᶜ) // χ v.val = i} := ⟨fun v => v.val.prop v.prop⟩
        exact ⟨1,le_rfl,hr,(forest_rate _ (by intro v; exact (v.val.prop v.prop).elim)).upper⟩
      · obtain ⟨a,ha,har,hu⟩ := hR j
        exact ⟨a,ha,har,(extremal_mono_bigO ⟨(fibreComplementIso G χ hj).toCopy⟩).trans hu⟩
    obtain ⟨a₂,ha₂,ha₂r,hSc⟩ := ih _ hsmall _ rfl (G.induce Sᶜ) (fun v => χ v.val) hχ' hR'
    obtain ⟨a₁,ha₁,ha₁r,hS⟩ := hR i
    have he : G.induce S ⊕g G.induce Sᶜ ≃g G := splitIso G S (by
      intro u v huv
      change χ u = i ↔ χ v = i
      rw [hχ u v huv])
    refine ⟨max a₁ a₂,ha₁.trans (le_max_left _ _),max_lt ha₁r ha₂r,?_⟩
    exact (extremal_mono_bigO ⟨he.symm.toCopy⟩).trans
      (sum_upper _ _ (ha₁.trans (le_max_left _ _))
        (hS.trans (rpow_mono_bigO (le_max_left _ _)))
        (hSc.trans (rpow_mono_bigO (le_max_right _ _))))

/-- At least one component attains the same superlinear growth threshold.
No pure-power asymptotic, nor its constant, is claimed for that component. -/
lemma exists_component_rate {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (hR : HasRate G r) :
    ∃ C : G.ConnectedComponent, HasRate C.toSimpleGraph r := by
  classical
  by_contra hn
  push_neg at hn
  have hsub : ∀ C : G.ConnectedComponent, ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^a) := by
    intro C
    have hu := (extremal_mono_bigO
      (show C.toSimpleGraph ⊑ G from ⟨⟨C.toSimpleGraph_hom,Subtype.val_injective⟩⟩)).trans hR.upper
    have hl : ¬ ∀ a : ℝ, 1 ≤ a →
        ((fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) → r ≤ a := fun hl => hn C ⟨hr.le,hu,hl⟩
    push_neg at hl
    obtain ⟨a,ha,hu,hlt⟩ := hl
    exact ⟨a,ha,hlt,hu⟩
  obtain ⟨a,ha,har,hu⟩ := subcritical_upper_of_fibres G G.connectedComponentMk hr
    (fun _ _ huv => ConnectedComponent.connectedComponentMk_eq_of_adj huv) hsub
  exact (not_lt_of_ge (hR.lower a ha hu)) har

#print axioms Erdos713Rate.HasRate.unique
#print axioms Erdos713Rate.rate_of_asymptotic
#print axioms subcritical_upper_of_fibres
#print axioms exists_component_rate
end Erdos713ComponentRates
