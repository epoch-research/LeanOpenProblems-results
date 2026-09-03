import FormalConjecturesUtil
import Submission.DegreePenaltySupports

/-! Quantitative edge-deletion resistance of clones of a penalized maximizer.
These inequalities do not assert a rate transfer to an identification quotient. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713CloneResistance
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713Cloning
variable {V W : Type*}
set_option maxHeartbeats 1000000

lemma energy_mono [Fintype V] {J G : SimpleGraph V} (h : J ≤ G) :
    energy J ≤ energy G := by
  unfold energy
  exact sum_le_sum (fun v _ => pow_le_pow_left₀ (degreeR_nonneg _ _)
    (degreeR_mono h v) 2)

lemma score_drop_le_edges [Fintype V] {J G : SimpleGraph V} (h : J ≤ G)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    score lam G - score lam J ≤ edgesR G - edgesR J := by
  have hh := mul_le_mul_of_nonneg_left (energy_mono h) hlam
  unfold score
  linarith

/-- A free spanning subgraph of a clone pays at least the positive net
clone gain in deleted edges. Edges may be deleted anywhere in the clone. -/
lemma free_subclone_cost [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    (v : V) (J : SimpleGraph (Option V)) (hJ : J ≤ clone G v) (hf : H.Free J) :
    score lam (clone G v) - score lam G - mu*(2*Fintype.card V+1) ≤
      edgesR (clone G v) - edgesR J := by
  have hh := hg.compare_graph J hf
  unfold potential at hh
  simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hh
  have hs := score_drop_le_edges hJ hlam
  nlinarith only [hh, hs]

/-- The summed positive-source budget; this expression can be negative on
an arbitrary globally optimal host, but is positive on the selected hosts. -/
noncomputable def netBudget [Fintype V] (G : SimpleGraph V) (lam mu : ℝ) : ℝ :=
  2*edgesR G-lam*(3*energy G+2*edgesR G)-
    (Fintype.card V : ℝ)*(mu*(2*Fintype.card V+1))

lemma sum_net_gain [Fintype V] (G : SimpleGraph V) (lam mu : ℝ) :
    (∑ v, (score lam (clone G v)-score lam G-mu*(2*Fintype.card V+1))) =
      netBudget G lam mu := by
  rw [sum_sub_distrib, sum_clone_score, sum_const, card_univ, nsmul_eq_mul]
  rfl

/-- Simultaneous lower bound valid for every choice of an H-free spanning
subgraph in each clone, including maximum-edge choices. -/
theorem total_free_subclone_cost [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    (J : V → SimpleGraph (Option V)) (hJ : ∀ v, J v ≤ clone G v)
    (hf : ∀ v, H.Free (J v)) :
    netBudget G lam mu ≤ ∑ v, (edgesR (clone G v)-edgesR (J v)) := by
  rw [← sum_net_gain]
  exact sum_le_sum (fun v _ => free_subclone_cost hg hlam v (J v) (hJ v) (hf v))

lemma budget_le_fold_mass [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    netBudget G lam mu ≤ ∑ v, if SingleFold H G v then degreeR G v else 0 :=
  hg.fold_mass hlam hmu

#print axioms free_subclone_cost
#print axioms total_free_subclone_cost
end Erdos713CloneResistance
