import Submission.GreedyHypergraphState
import Submission.PenalizedAlteration

/-!
A finite extension certificate that retains every active residual constraint.
It is not an asymptotic improvement for Erdős 773. The final scalar lemma
bounds a one-shot certificate, not the actual independence number.
-/
namespace Erdos773.GreedyRestartAlteration
open Finset GreedyHypergraphState
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Equal residual supports may be identified for independence. Their original
edge multiplicities are retained in the upper bound on the deletion cost. -/
def residual (H : Finset (Finset α)) (I : Finset α) : Finset (Finset α) :=
  (H.filter (fun e => e \ I ⊆ available H I)).image (fun e => e \ I)

lemma residual_subset {H : Finset (Finset α)} {I f : Finset α}
    (hf : f ∈ residual H I) : f ⊆ available H I := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact (mem_filter.mp he).2

lemma residual_nonempty {H : Finset (Finset α)} {I f : Finset α}
    (hI : Independent H I) (hf : f ∈ residual H I) : f.Nonempty := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact sdiff_nonempty.mpr (hI e (mem_filter.mp he).1)

/-- This equivalence includes all shortened edges, not just original edges
contained in the remaining vertex carrier. -/
theorem extension_iff {H : Finset (Finset α)} {I J : Finset α}
    (hJ : J ⊆ available H I) :
    Independent H (I ∪ J) ↔ Independent (residual H I) J := by
  constructor
  · intro h f hf hfJ
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    apply h e (mem_filter.mp he).1
    intro a ha
    by_cases hai : a ∈ I
    · exact mem_union_left J hai
    · exact mem_union_right I (hfJ (mem_sdiff.mpr ⟨ha,hai⟩))
  · intro h e he heIJ
    have hres : e \ I ⊆ J := by
      intro a ha
      exact (mem_union.mp (heIJ (mem_sdiff.mp ha).1)).resolve_left (mem_sdiff.mp ha).2
    exact h (e \ I) (mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hres.trans hJ⟩,rfl⟩) hres

lemma residual_size {H : Finset (Finset α)} {I f : Finset α}
    (hI : Independent H I) (hfour : ∀ e ∈ H, e.card=4)
    (hf : f ∈ residual H I) : 2 ≤ f.card ∧ f.card ≤ 4 := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact active_size_bounds hI hfour (mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2,rfl⟩)

lemma indexed_cost {H : Finset (Finset α)} {I : Finset α}
    (hI : Independent H I) (hfour : ∀ e ∈ H, e.card=4) (p : ℝ) :
    (∑ e ∈ H.filter (fun e => e \ I ⊆ available H I), p^(e \ I).card) =
      p^2*(active H I 2).card+p^3*(active H I 3).card+p^4*(active H I 4).card := by
  classical
  let F := H.filter (fun e => e \ I ⊆ available H I)
  have hF (j : ℕ) : F.filter (fun e => (e \ I).card=j)=active H I j := by
    ext e
    simp [F,active,and_assoc]
  have he (e : Finset α) (he : e ∈ F) :
      p^(e \ I).card = (if (e \ I).card=2 then p^2 else 0)+
        (if (e \ I).card=3 then p^3 else 0)+(if (e \ I).card=4 then p^4 else 0) := by
    have hb := active_size_bounds hI hfour
      (mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2,rfl⟩)
    have hh : (e \ I).card=2 ∨ (e \ I).card=3 ∨ (e \ I).card=4 := by omega
    rcases hh with hh | hh | hh <;> simp [hh]
  change (∑ e ∈ F, p^(e \ I).card) = _
  rw [sum_congr rfl he,sum_add_distrib,sum_add_distrib]
  simp only [← sum_filter,hF,sum_const,nsmul_eq_mul]
  ring

/-- Multiplicity can only increase the indexed deletion budget. -/
lemma residual_cost_le {H : Finset (Finset α)} {I : Finset α}
    (hI : Independent H I) (hfour : ∀ e ∈ H, e.card=4) {p : ℝ} (hp : 0 ≤ p) :
    (∑ f ∈ residual H I, p^f.card) ≤
      p^2*(active H I 2).card+p^3*(active H I 3).card+p^4*(active H I 4).card := by
  rw [← indexed_cost hI hfour p]
  unfold residual
  exact sum_image_le_of_nonneg (fun f _ => pow_nonneg hp f.card)

/-- A genuine extension of the prescribed independent set. In particular,
none of the old selected vertices is silently discarded. -/
theorem extend {H : Finset (Finset α)} {I : Finset α}
    (hI : Independent H I) (hfour : ∀ e ∈ H, e.card=4)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ J ⊆ available H I, Independent H (I ∪ J) ∧
      (I.card:ℝ)+p*(available H I).card-
        (p^2*(active H I 2).card+p^3*(active H I 3).card+p^4*(active H I 4).card)
        ≤ (I ∪ J).card := by
  classical
  obtain ⟨J,hJ,hind,hcard⟩ := PenalizedAlteration.ambient (available H I) (residual H I) ∅
    (fun _ hf => residual_subset hf) (by simp) (fun _ hf => residual_nonempty hI hf)
    p 0 hp hp1 (by norm_num)
  simp only [sum_empty,mul_zero,zero_mul,sub_zero] at hcard
  have hcost := residual_cost_le hI hfour hp
  have hdis : Disjoint I J := ((available_disjoint H I).mono_left hJ).symm
  have hc : ((I ∪ J).card:ℝ) = (I.card:ℝ)+(J.card:ℝ) := by
    rw [card_union_of_disjoint hdis,Nat.cast_add]
  refine ⟨J,hJ,(extension_iff hJ).mpr hind,?_⟩
  rw [hc]
  linarith only [hcard,hcost]

/-- Dimensionless one-shot alteration reward at the ideal mixed-degree
trajectory. This is only a numerical certificate, not an actual trajectory. -/
def modelReward (t z : ℝ) : ℝ := t+z-(3/2)*t^2*z^2-t*z^3-z^4/4

/-- Even in the ideal model, the one-shot alteration certificate adds at
most 1/(6t^2). This is NOT an upper bound on what other extensions can attain. -/
lemma model_reward_upper {t z : ℝ} (ht : 0<t) (hz : 0 ≤ z) :
    modelReward t z ≤ t+1/(6*t^2) := by
  have ht2 : 0 < 6*t^2 := by positivity
  have hquad : z-(3/2)*t^2*z^2 ≤ 1/(6*t^2) := by
    apply (le_div_iff₀ ht2).mpr
    nlinarith only [sq_nonneg (3*t^2*z-1)]
  have h3 : 0 ≤ t*z^3 := by positivity
  have h4 : 0 ≤ z^4/4 := by positivity
  unfold modelReward
  linarith only [hquad,h3,h4]

#print axioms extension_iff
#print axioms residual_size
#print axioms indexed_cost
#print axioms residual_cost_le
#print axioms extend
#print axioms model_reward_upper
end
end Erdos773.GreedyRestartAlteration
