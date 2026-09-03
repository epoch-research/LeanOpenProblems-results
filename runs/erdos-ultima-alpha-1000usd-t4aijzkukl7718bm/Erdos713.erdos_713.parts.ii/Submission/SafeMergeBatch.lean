import FormalConjecturesUtil
import Submission.GreedySafeMergeStep
import Submission.MergeCostPropagation

/-! A finite greedy batch of C8-safe identifications with explicit candidate
loss, degree control, and accumulated penalized-score cost. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713SafeMergeBatch
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713MergeDegreePenalty
open Erdos713VertexMerging Erdos713C8TwoMergers Erdos713CommonBlockerPairCount
open Erdos713MergeCostPropagation
universe u
set_option maxHeartbeats 2000000

def lossBound (N D : ℕ) : ℕ := 6*N*(2*D)^4+4*N+1

lemma interaction_bound {V : Type u} [Fintype V] (G : SimpleGraph V) (N D : ℕ)
    (hN : Fintype.card V ≤ N) (hD : ∀ v, G.degree v ≤ 2*D) :
    (genuineRoots G).card ≤ (6*N*(2*D)^4)^2 := by
  calc
    _ ≤ 18*(Fintype.card V)^2*(2*D)^8 := card_genuineRoots_le G (2*D) hD
    _ ≤ 18*N^2*(2*D)^8 := by gcongr
    _ ≤ 36*N^2*(2*D)^8 := by
      exact Nat.mul_le_mul_right ((2*D)^8) (Nat.mul_le_mul_right (N^2) (by decide : 18 ≤ 36))
    _ = _ := by ring

/-- The candidate pairs are disjoint from every previously merged root.
The whole graph has degree at most 2D, while candidate endpoints still have
degree at most D. The accumulated score loss is k*s+k*(k-1)/2. -/
theorem exists_batch (k N D : ℕ) {lam s : ℝ} (hlam : 0 ≤ lam)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hFree : (cycleGraph 8).Free G)
    (hN : Fintype.card V ≤ N) (hCap : ∀ v, G.degree v ≤ 2*D)
    (S : Finset (V × V))
    (hSafe : ∀ p ∈ S, SafePair (cycleGraph 8) G p.1 p.2)
    (hDeg : ∀ p ∈ S, G.degree p.1 ≤ D ∧ G.degree p.2 ≤ D)
    (hCost : ∀ p ∈ S, pairCost G lam p ≤ s)
    (hSize : k*lossBound N D < S.card) :
    ∃ (U : Type u) (_ : Fintype U) (J : SimpleGraph U),
      (cycleGraph 8).Free J ∧ Fintype.card U+k=Fintype.card V ∧
      score lam G-((k : ℝ)*s+(k : ℝ)*(k-1)/2) ≤ score lam J := by
  induction k generalizing V s with
  | zero => exact ⟨V,inferInstance,G,hFree,by simp,by simp⟩
  | succ k ih =>
    let B := 6*N*(2*D)^4
    have hB : B < S.card := by
      have h₁ : lossBound N D ≤ (k+1)*lossBound N D := by
        simpa only [one_mul] using Nat.mul_le_mul_right (lossBound N D) (show 1 ≤ k+1 by omega)
      have h₂ : B ≤ lossBound N D := by dsimp [B,lossBound]; omega
      exact h₂.trans_lt (h₁.trans_lt hSize)
    obtain ⟨a,b,hab,hn,habS,hFreeM,T,hTcard,hTS,hSafeT⟩ :=
      Erdos713GreedySafeMergeStep.step G hFree S hSafe B hB (interaction_bound G N D hN hCap)
    let M := merge G a b hn
    have hCard : Fintype.card {x : V // x ≠ b}+1=Fintype.card V := by
      have hn0 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨b⟩
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_unique]
      omega
    have hNM : Fintype.card {x : V // x ≠ b} ≤ N := by omega
    have hCapM : ∀ v, M.degree v ≤ 2*D :=
      degree_cap_preserved G hab hn D hCap (hDeg (a,b) habS).1 (hDeg (a,b) habS).2
    have hDegT : ∀ p ∈ T, M.degree p.1 ≤ D ∧ M.degree p.2 ≤ D := by
      intro p hp
      obtain ⟨hpS,hpa,hpb⟩ := hTS p hp
      exact ⟨(degree_merge_other_nat G hn p.1 hpa).trans (hDeg _ hpS).1,
        (degree_merge_other_nat G hn p.2 hpb).trans (hDeg _ hpS).2⟩
    have hCostT : ∀ p ∈ T, pairCost M lam p ≤ s+1 := by
      intro p hp
      obtain ⟨hpS,hpa,hpb⟩ := hTS p hp
      have h₁ := pairCost_merge G hn p hpa hpb hlam
      have h₂ := hCost _ hpS
      linarith
    have hSizeT : k*lossBound N D < T.card := by
      have hle : 4*Fintype.card V ≤ 4*N := Nat.mul_le_mul_left 4 hN
      have he : (k+1)*lossBound N D=k*lossBound N D+lossBound N D := by ring
      rw [he] at hSize
      dsimp only [B] at hTcard
      dsimp only [lossBound] at hSize ⊢
      omega
    obtain ⟨U,instU,J,hJ,hCJ,hScoreJ⟩ := ih M hFreeM hNM hCapM T hSafeT hDegT hCostT hSizeT
    have hScoreM := merge_score_loss G hab hn hlam (hCost (a,b) habS)
    refine ⟨U,instU,J,hJ,by omega,?_⟩
    simp only [Nat.cast_add,Nat.cast_one] at *
    change score lam G-((k+1)*s+(k+1)*((k+1)-1)/2) ≤ score lam J
    change score lam G-s ≤ score lam M at hScoreM
    nlinarith only [hScoreM,hScoreJ]

/-- The loss budget is paid once for a whole safe batch. This bounds the
number of low-cost safe pairs after ANY common spanning edge loss. -/
theorem pair_count {V : Type u} [Fintype V] {G F : SimpleGraph V}
    {lam mu t s : ℝ} (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t) (k N D : ℕ)
    (hN : Fintype.card V ≤ N) (hCap : ∀ v, F.degree v ≤ 2*D)
    (S : Finset (V × V))
    (hSafe : ∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2)
    (hDeg : ∀ p ∈ S, F.degree p.1 ≤ D ∧ F.degree p.2 ≤ D)
    (hCost : ∀ p ∈ S, pairCost F lam p ≤ s)
    (hcost : t+(k : ℝ)*s+(k : ℝ)*(k-1)/2 < mu*(2*Fintype.card V*k-(k : ℝ)^2)) :
    S.card ≤ k*lossBound N D := by
  by_contra hbad
  obtain ⟨U,instU,J,hJ,hCard,hScore⟩ := exists_batch k N D hlam F
    (fun h => hg.free (h.trans ⟨Copy.ofLE _ _ hle⟩)) hN hCap S hSafe hDeg hCost
    (Nat.lt_of_not_ge hbad)
  have hComp := hg.compare_graph J hJ
  have hDrop := Erdos713CloneResistance.score_drop_le_edges hle hlam
  have hC : (Fintype.card U : ℝ)+(k : ℝ)=(Fintype.card V : ℝ) := by exact_mod_cast hCard
  have hC' : (Fintype.card U : ℝ)=(Fintype.card V : ℝ)-k := by linarith
  unfold potential at hComp
  rw [hC'] at hComp
  nlinarith only [hScore,hComp,hDrop,hloss,hcost]

#print axioms exists_batch
#print axioms pair_count
end Erdos713SafeMergeBatch
