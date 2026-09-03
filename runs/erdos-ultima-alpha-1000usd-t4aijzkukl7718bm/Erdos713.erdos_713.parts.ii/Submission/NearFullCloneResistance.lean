import FormalConjecturesUtil
import Submission.NearFullPenaltyWitnesses

/-! Near-full-density hosts with quantitative cloning resistance on the
same host. This does not imply rationality of the extremal exponent. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713NearFullCloneResistance
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713Cloning
open Erdos713CloneResistance Erdos713NearFullPenaltyWitnesses
variable {W : Type*}

/-- The coefficients a and κ are uniform in the density accuracy. On each
selected host, the resistance estimate holds for every family of H-free
spanning subgraphs of its clones, not just a chosen family. -/
theorem near_full_resistant [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        (∀ J : Fin n → SimpleGraph (Option (Fin n)),
          (∀ v, J v ≤ clone G v) → (∀ v, H.Free (J v)) →
          κ*(n : ℝ)^α ≤ ∑ v, (edgesR (clone G v)-edgesR (J v))) ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu := by
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_joint_budget H hH hEdge ha ha2 hc h
  refine ⟨a,κ,ha',hκ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hD'⟩ := hs ε hε
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,_,lam,mu,hlam,hmu,hG,hBudget⟩ := hD' L
  refine ⟨n,G,hn,hFree,hDense,hDeg,?_,lam,mu,hlam,hmu,hG⟩
  intro J hJ hf
  exact hBudget.trans (total_free_subclone_cost hG hlam.le J hJ hf)

#print axioms near_full_resistant
end Erdos713NearFullCloneResistance
