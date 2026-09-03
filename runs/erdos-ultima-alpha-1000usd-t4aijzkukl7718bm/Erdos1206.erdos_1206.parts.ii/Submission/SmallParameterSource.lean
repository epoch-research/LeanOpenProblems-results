import Submission.SmallDefectSummability
import Submission.SmallGapSummability

/-! One positive-density source simultaneously excludes the two proved
small-parameter regimes, including all common dilations. -/
namespace Erdos1206.SmallParameterSource
open DefectCollisionCounting
open scoped Classical

def forbidden : Set ℕ := SmallDefectSummability.maxima ∪ SmallGapSummability.maxima

lemma forbidden_reciprocals_summable :
    Summable (fun n : ℕ => if n∈forbidden then (1:ℝ)/n else 0) := by
  have hs := SmallDefectSummability.maxima_reciprocals_summable.add
    SmallGapSummability.maxima_reciprocals_summable
  apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
  intro n
  by_cases hd : n∈SmallDefectSummability.maxima <;>
    by_cases hg : n∈SmallGapSummability.maxima <;>
    simp [forbidden,hd,hg]

lemma one_not_forbidden : 1∉forbidden := by
  intro hh
  rcases hh with ⟨e,he⟩ | ⟨e,he⟩ <;>
    change e.val.d=1 at he <;>
    have := e.val.hab <;> have := e.val.hbc <;> have := e.val.hcd <;> omega

/-- Both exclusions hold on the same source, not merely on two unrelated
positive-density sets whose intersection might have density zero. -/
theorem positive_density_avoids_both :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      ∀e : Collision, (e.defect^32≤e.d ∨ e.smallGap^48≤e.d) →
        ∀t : ℕ, t*e.d∉A := by
  let A := divisorAvoider forbidden
  have hd : 0<A.lowerDensity :=
    divisorAvoider_positive_density_of_summable one_not_forbidden forbidden_reciprocals_summable
  refine ⟨A,?_,hd,?_⟩
  · by_contra hf
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hf)).liminf_eq
    linarith
  · intro e he t ht
    have hed : e.d∈forbidden := by
      rcases he with he | he
      · exact Or.inl ⟨⟨e,he⟩,rfl⟩
      · exact Or.inr ⟨⟨e,he⟩,rfl⟩
    exact ht.2 e.d hed (dvd_mul_left e.d t)

/-- All surviving collisions have both normalized parameters larger than
fixed positive powers of their primitive maximum root. -/
theorem positive_density_normalized_parameters_lower_bound :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      ∀e : Collision, e.d∈A →
        let g := ConicHeightProduct.rootGcd e.a e.b e.c e.d
        e.d/g<(e.defect/g)^32 ∧ e.d/g<(e.smallGap/g)^48 := by
  obtain ⟨A,hAi,hAd,hA⟩ := positive_density_avoids_both
  refine ⟨A,hAi,hAd,?_⟩
  intro e hed
  let g := ConicHeightProduct.rootGcd e.a e.b e.c e.d
  have hd : 0<e.d := by have := e.hcd; omega
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right e.c hd)
  have hga : g∣e.a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left e.a e.b)
  have hgb : g∣e.b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right e.a e.b)
  have hgc : g∣e.c := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left e.c e.d)
  have hgd : g∣e.d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right e.c e.d)
  change e.d/g<(e.defect/g)^32 ∧ e.d/g<(e.smallGap/g)^48
  constructor
  · obtain ⟨f,hfd,hfk,hs⟩ := SmallDefectSummability.normalize_collision e hg hga hgb hgc hgd
    by_contra hn
    have hsmall : f.defect^32≤f.d := by rw [hfk,hfd]; omega
    exact hA f (Or.inl hsmall) g (by rwa [←hs])
  · obtain ⟨f,hfd,hfk,hs⟩ := SmallGapSummability.normalize_collision e hg hga hgb hgc hgd
    by_contra hn
    have hsmall : f.smallGap^48≤f.d := by rw [hfk,hfd]; omega
    exact hA f (Or.inr hsmall) g (by rwa [←hs])

#print axioms forbidden_reciprocals_summable
#print axioms positive_density_avoids_both
#print axioms positive_density_normalized_parameters_lower_bound
end Erdos1206.SmallParameterSource
