import Submission.PackingEdgeDeletionPaths

/-! An explicit O((t+1) log²(t+1)) threshold for the deletion cost t. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficit
set_option maxHeartbeats 1000000

def cutoffIndex (t : ℕ) : ℕ :=
  Nat.log 2 (t+1) + 2*Nat.log 2 (Nat.log 2 (t+1)+1) + 13

def cutoff (t : ℕ) : ℕ := 2^(cutoffIndex t)

lemma cutoffIndex_pos (t : ℕ) : 1 ≤ cutoffIndex t := by unfold cutoffIndex; omega

lemma cutoff_pays (t : ℕ) :
    4*(cutoffIndex t+1)*(cutoffIndex t+2)*t ≤ cutoff t := by
  let k := Nat.log 2 (t+1)
  let r := Nat.log 2 (k+1)
  have hr : r ≤ k := by
    have h := Nat.log_lt_self 2 (Nat.succ_ne_zero k)
    change Nat.log 2 (k+1) < k+1 at h
    omega
  have ht : t ≤ 2*2^k := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (t+1)
    change t+1 < 2^(k+1) at h
    rw [pow_succ] at h
    omega
  have hkr : k+1 ≤ 2*2^r := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (k+1)
    change k+1 < 2^(r+1) at h
    rw [pow_succ] at h
    omega
  have hsq : (k+1)^2 ≤ 4*(2^r)^2 := by nlinarith
  have hquad : (k+2*r+14)*(k+2*r+15) ≤ 210*(k+1)^2 := by
    have h := Nat.mul_le_mul
      (show k+2*r+14 ≤ 14*(k+1) by omega)
      (show k+2*r+15 ≤ 15*(k+1) by omega)
    nlinarith
  change 4*(k+2*r+13+1)*(k+2*r+13+2)*t ≤ 2^(k+2*r+13)
  calc
    _ = 4*((k+2*r+14)*(k+2*r+15))*t := by ring
    _ ≤ 4*(210*(k+1)^2)*(2*2^k) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 hquad) ht
    _ ≤ 4*(210*(4*(2^r)^2))*(2*2^k) := by gcongr
    _ ≤ 8192*2^k*(2^r)^2 := by nlinarith [Nat.zero_le (2^k*(2^r)^2)]
    _ = 2^(k+2*r+13) := by
      simp only [pow_add,pow_mul']
      norm_num
      ring

lemma cutoff_le (t : ℕ) :
    cutoff t ≤ 8192*(t+1)*(Nat.log 2 (t+1)+1)^2 := by
  have hk := Nat.pow_log_le_self 2 (Nat.succ_ne_zero t)
  have hr := Nat.pow_log_le_self 2 (Nat.succ_ne_zero (Nat.log 2 (t+1)))
  have he : cutoff t =
      8192*2^(Nat.log 2 (t+1))*(2^(Nat.log 2 (Nat.log 2 (t+1)+1)))^2 := by
    unfold cutoff cutoffIndex
    simp only [pow_add,pow_mul']
    norm_num
    ring
  rw [he]
  gcongr

lemma threshold_above_cutoff (t : ℕ) {x : ℕ} (hx : cutoff t ≤ x) :
    4*scale x*t ≤ x :=
  threshold_persists (cutoffIndex_pos t) (cutoff_pays t) hx

end Erdos184.LogDeficit

namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionPaths
universe u
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

/-- Simultaneous edge and cycle deletions only require endpoint sets of
size O((t+1) log²(t+1)), independent of the ambient order. -/
lemma IsVertexMinimal.short_path_after_packing_edges_cutoff (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Set (Sym2 V)) (t : ℕ) (hcost : P.card+F.ncard ≤ C*t)
    (A B : Set V) (haA : cutoff t ≤ A.ncard) (haB : cutoff t ≤ B.ncard) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : ((G \ unionPieces G P).deleteEdges F).Walk u v,
      p.IsPath ∧ p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1) := by
  have hp : 0 < cutoff t := Nat.two_pow_pos _
  obtain ⟨u,hu,v,hv,p,hp,hlen⟩ := short_path_between_sets _
    (show 0 < 12*scale (Fintype.card V) from Nat.mul_pos (by decide) (scale_pos _))
    (hG.expands_after_packing_edges_at_scale hC P hc hd F t (cutoffIndex t)
      hcost (cutoffIndex_pos t) (cutoff_pays t)) A B
    (hp.trans_le haA) haA (hp.trans_le haB) haB
  exact ⟨u,hu,v,hv,p,hp,by nlinarith⟩

end Erdos184.LogDeficitSeparator
