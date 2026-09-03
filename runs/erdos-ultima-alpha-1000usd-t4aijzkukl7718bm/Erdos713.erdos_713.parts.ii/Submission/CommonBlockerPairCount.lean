import FormalConjecturesUtil
import Submission.PenalizedDoubleMerge
import Submission.PairCollisionCounting

/-! A common low-cost loss cannot make many bounded-cost C8 mergers safe
on the same penalized host. No cheap blocker is constructed. -/
open SimpleGraph Finset Filter
open scoped Classical Topology
namespace Erdos713CommonBlockerPairCount
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713MergeDegreePenalty
open Erdos713PenalizedDoubleMerge Erdos713TwoPathRootCounting
variable {V : Type*}
set_option maxHeartbeats 2000000

/-- The pair cost is measured in the original host, before the common loss. -/
noncomputable def pairCost [Fintype V] (G : SimpleGraph V) (lam : ℝ) (p : V × V) : ℝ :=
  (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)+2*lam*degreeR G p.1*degreeR G p.2

/-- S may be any collection of ordered safe pairs in the retained graph.
The common loss t is charged just once in the double-merger comparison. -/
theorem square_bound [Fintype V] {G F : SimpleGraph V} {lam mu t s : ℝ}
    (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t)
    (S : Finset (V × V))
    (hSafe : ∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2)
    (hPair : ∀ p ∈ S, pairCost G lam p ≤ s)
    (hcost : t+2*s+1 < mu*(4*Fintype.card V-4)) :
    S.card^2 ≤ 4*Fintype.card V*S.card+(totalLengthRoots F 8).card := by
  apply Erdos713PairCollisionCounting.square_le
  intro p hp q hq hca hcb hda hdb
  obtain ⟨hab,hn,hfirst⟩ := hSafe p hp
  obtain ⟨hcd,hncd,hsecond⟩ := hSafe q hq
  apply common_blocker_mem_total hg hlam hle hloss p.1 p.2 q.1 q.2
    hab hca hcb hda hdb hcd hn hncd hfirst hsecond
  have h₁ := hPair p hp
  have h₂ := hPair q hq
  dsimp only [pairCost] at h₁ h₂
  nlinarith only [h₁,h₂,hcost]

/-- Explicit finite form, using a degree cap on the retained graph only. -/
theorem degree_bound [Fintype V] {G F : SimpleGraph V} {lam mu t s : ℝ}
    (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t)
    (S : Finset (V × V))
    (hSafe : ∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2)
    (hPair : ∀ p ∈ S, pairCost G lam p ≤ s)
    (hcost : t+2*s+1 < mu*(4*Fintype.card V-4))
    (D : ℕ) (hD : ∀ v, F.degree v ≤ D) :
    S.card^2 ≤ 4*Fintype.card V*S.card+18*(Fintype.card V)^2*D^8 := by
  apply (square_bound hg hlam hle hloss S hSafe hPair hcost).trans
  apply Nat.add_le_add_left
  simpa using card_totalLengthRoots_le F D hD 8

/-- Uniform sparsity over all common losses and pair sets satisfying the
finite cost condition. No asymptotic for ex(n,C8) is used in this implication. -/
theorem eventually_sparse {β C ε : ℝ} (hβ : β < 1/4) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G F : SimpleGraph (Fin n)) (lam mu t s : ℝ),
      GlobalOptimal (cycleGraph 8) G lam mu → 0 ≤ lam → F ≤ G →
      edgesR G ≤ edgesR F+t → ∀ (S : Finset (Fin n × Fin n)),
      (∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2) →
      (∀ p ∈ S, pairCost G lam p ≤ s) →
      t+2*s+1 < mu*(4*n-4) → ∀ (D : ℕ),
      (∀ v, F.degree v ≤ D) → (D : ℝ) ≤ C*(n : ℝ)^β →
      (S.card : ℝ) ≤ ε*(n : ℝ)^2 := by
  have hε₂ : 0 < ε^2/2 := by positivity
  have hlim : Tendsto (fun n : ℕ => 4/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (4 : ℝ)
  filter_upwards [Erdos713TwoPathSparseRoots.eventually_eight_roots_sparse (C := C) hβ hε₂,
    hlim.eventually_lt_const hε₂,eventually_gt_atTop (0 : ℕ)] with n hn hlarge hn0
  intro G F lam mu t s hg hlam hle hloss S hSafe hPair hcost D hD hDC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hSq : (S.card : ℝ)^2 ≤ 4*n*S.card+(totalLengthRoots F 8).card := by
    have hh := square_bound hg hlam hle hloss S hSafe hPair
      (by simpa only [Fintype.card_fin] using hcost)
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hCard : (S.card : ℝ) ≤ (n : ℝ)^2 := by
    exact_mod_cast (show S.card ≤ n^2 by simpa [pow_two] using card_le_univ S)
  have hRoots := hn F D hD hDC
  have hcoef : 4 < (ε^2/2)*(n : ℝ) := (div_lt_iff₀ hnR).mp hlarge
  have hmul := mul_le_mul_of_nonneg_right hcoef.le (show 0 ≤ (n : ℝ)^3 by positivity)
  have hM := mul_le_mul_of_nonneg_left hCard (show 0 ≤ 4*(n : ℝ) by positivity)
  have hSq' : (S.card : ℝ)^2 ≤ (ε*(n : ℝ)^2)^2 := by
    nlinarith only [hSq,hRoots,hmul,hM]
  exact (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp hSq'

#print axioms square_bound
#print axioms degree_bound
#print axioms eventually_sparse
end Erdos713CommonBlockerPairCount
