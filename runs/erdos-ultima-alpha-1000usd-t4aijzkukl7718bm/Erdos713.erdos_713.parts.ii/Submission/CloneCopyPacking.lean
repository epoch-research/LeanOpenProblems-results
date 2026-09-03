import FormalConjecturesUtil
import Submission.NearFullCloneResistance
import Submission.FiniteCopyEdgePacking

/-! Edge-disjoint copy packings in clones of the same near-optimal host.
The packings are edge-disjoint within a clone, not across different clones,
and no disjointness of their vertex sets is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713CloneCopyPacking
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713Cloning
open Erdos713CloneResistance Erdos713NearFullPenaltyWitnesses
open Erdos713FiniteCopyEdgePacking
variable {V W : Type*}
set_option maxHeartbeats 1000000

/-- A positive net budget forces a large total number of packed copies. -/
theorem exists_clone_packings [Fintype W] [Fintype V] (H : SimpleGraph W)
    (hEdge : 0 < H.edgeFinset.card) {G : SimpleGraph V} {lam mu : ℝ}
    (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) :
    ∃ F : V → Finset (Finset (Sym2 (Option V))),
      (∀ v, Packing H (clone G v) (F v)) ∧
      netBudget G lam mu ≤ (H.edgeFinset.card : ℝ)*∑ v, ((F v).card : ℝ) := by
  choose F hF hFree hCost using fun v : V => exists_packing H hEdge (clone G v)
  let J : V → SimpleGraph (Option V) := fun v =>
    (clone G v).deleteEdges (used (F v) : Set (Sym2 (Option V)))
  have hsum := total_free_subclone_cost hg hlam J (fun _ => deleteEdges_le _) hFree
  refine ⟨F,hF,hsum.trans ?_⟩
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  have hc : edgesR (clone G v) ≤ edgesR (J v)+(H.edgeFinset.card : ℝ)*(F v).card := by
    have hh := hCost v
    unfold edgesR
    exact_mod_cast (by simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh)
  linarith

/-- Fixed positive packing mass, near-full edge count, and both degree
bounds hold simultaneously on arbitrarily large H-free hosts. -/
theorem near_full_packings [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        ∃ F : Fin n → Finset (Finset (Sym2 (Option (Fin n)))),
          (∀ v, Packing H (clone G v) (F v)) ∧
          κ*(n : ℝ)^α ≤ ∑ v, ((F v).card : ℝ) := by
  have hEdge' : 0 < H.edgeFinset.card := card_pos.mpr (by
    obtain ⟨v,w,hvw⟩ := hEdge
    exact ⟨s(v,w),by simpa using hvw⟩)
  have hEdgeR : (0 : ℝ) < H.edgeFinset.card := by exact_mod_cast hEdge'
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_joint_budget H hH hEdge ha ha2 hc h
  refine ⟨a,κ/H.edgeFinset.card,ha',div_pos hκ hEdgeR,?_⟩
  intro ε hε
  obtain ⟨D,hD,hD'⟩ := hs ε hε
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,_,lam,mu,hlam,_,hG,hBudget⟩ := hD' L
  obtain ⟨F,hF,hPack⟩ := exists_clone_packings H hEdge' hG hlam.le
  refine ⟨n,G,hn,hFree,hDense,hDeg,F,hF,?_⟩
  have hh := hBudget.trans hPack
  rw [div_mul_eq_mul_div,div_le_iff₀ hEdgeR]
  nlinarith only [hh]

#print axioms exists_clone_packings
#print axioms near_full_packings
end Erdos713CloneCopyPacking
