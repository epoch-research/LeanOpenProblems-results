import Submission.APBounds

/-!
Three-root progression supports for the square-Sidon problem. Each support
is counted once. Avoiding these supports gives progression-free square values,
not Sidon square values.
-/
noncomputable section
namespace Erdos773.SquareProgressionSupports
open Finset
set_option maxHeartbeats 1000000

/-- Three distinct roots whose squares form a three-term progression. -/
def progressions (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact A.powerset.filter (fun e => e.card=3 ∧ ∃ a b c : ℕ,
    e={a,b,c} ∧ a^2+c^2=2*b^2)

lemma mem_progressions {A e : Finset ℕ} :
    e ∈ progressions A ↔ e ⊆ A ∧ e.card=3 ∧ ∃ a b c : ℕ,
      e={a,b,c} ∧ a^2+c^2=2*b^2 := by
  classical
  simp only [progressions,mem_filter,mem_powerset]

lemma distinct_of_card_three {a b c : ℕ} (h : ({a,b,c}:Finset ℕ).card=3) :
    a≠b ∧ a≠c ∧ b≠c := by
  simp only [card_insert_eq_ite,card_singleton,mem_insert,mem_singleton] at h
  split_ifs at h <;> simp_all

lemma progressions_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    progressions A ⊆ progressions B := by
  intro e he
  obtain ⟨heA,hcard,hs⟩ := mem_progressions.mp he
  exact mem_progressions.mpr ⟨heA.trans hAB,hcard,hs⟩

lemma progressions_restrict {A B : Finset ℕ} (hBA : B ⊆ A) :
    progressions B = (progressions A).filter (fun e => e ⊆ B) := by
  classical
  ext e
  simp only [mem_progressions,mem_filter]
  constructor
  · rintro ⟨heB,hcard,hs⟩
    exact ⟨⟨heB.trans hBA,hcard,hs⟩,heB⟩
  · rintro ⟨⟨heA,hcard,hs⟩,heB⟩
    exact ⟨heB,hcard,hs⟩

/-- The existing ordered progression count bounds these supports. -/
lemma progression_card_bound (N : ℕ) :
    (progressions (Icc 1 N)).card ≤ (squareAPs N).card := by
  classical
  let f : (ℕ × ℕ) × ℕ → Finset ℕ := fun t => {t.1.1,t.1.2,t.2}
  have hsub : progressions (Icc 1 N) ⊆ (squareAPs N).image f := by
    intro e he
    obtain ⟨heA,hcard,a,b,c,rfl,hs⟩ := mem_progressions.mp he
    obtain ⟨hab,hac,hbc⟩ := distinct_of_card_three hcard
    have ha := heA (by simp : a ∈ ({a,b,c}:Finset ℕ))
    have hb := heA (by simp : b ∈ ({a,b,c}:Finset ℕ))
    have hc := heA (by simp : c ∈ ({a,b,c}:Finset ℕ))
    rcases lt_or_gt_of_ne hac with hh | hh
    · have hab' : a<b := by nlinarith
      have hbc' : b<c := by nlinarith
      refine mem_image.mpr ⟨((a,b),c),?_,rfl⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hc⟩,hab',hbc',hs⟩
    · have hcb' : c<b := by nlinarith
      have hba' : b<a := by nlinarith
      refine mem_image.mpr ⟨((c,b),a),?_,?_⟩
      · exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hc,hb⟩,ha⟩,
          hcb',hba',by nlinarith only [hs]⟩
      · ext n
        simp only [f,mem_insert,mem_singleton]
        tauto
  exact (card_le_card hsub).trans card_image_le

lemma ap_free_of_avoids {A B : Finset ℕ} (hBA : B ⊆ A)
    (havoid : ∀ e ∈ progressions A, ¬e ⊆ B) :
    ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) := by
  intro x hx y hy z hz he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
  by_contra hne
  have hab : a≠b := fun h => hne (congrArg (fun n : ℕ => n^2) h)
  have hac : a≠c := by intro h; subst c; apply hne; nlinarith only [he]
  have hbc : b≠c := by intro h; subst c; apply hne; nlinarith only [he]
  have heB : ({a,b,c}:Finset ℕ) ⊆ B := by
    intro n hn
    simp only [mem_insert,mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> assumption
  apply havoid {a,b,c} _ heB
  exact mem_progressions.mpr ⟨heB.trans hBA,by simp [hab,hac,hbc],a,b,c,rfl,by omega⟩

#print axioms progressions_restrict
#print axioms progression_card_bound
#print axioms ap_free_of_avoids
end Erdos773.SquareProgressionSupports
