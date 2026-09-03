import Submission.ExpansionLongCycles
import Submission.LongCyclePacking

/-! Long cycles resilient under the logarithmic-budget deletion allowance,
and a resulting lower bound on the density of a vertex-minimal counterexample.
Neither assertion supplies a uniform linear cycle decomposition. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionLongCycles
open SqrtDeficitSeparator (externalBoundary)
universe u
set_option maxHeartbeats 1000000
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

/-- Convert the precise cost-dependent boundary inequality into a long cycle. -/
lemma long_cycle_of_log_boundary (H : SimpleGraph V) (t : ℕ) (ht : 0 < t)
    (hn : 32 * scale (Fintype.card V) * t ≤ Fintype.card V)
    (hb : ∀ X : Set V, 0 < X.ncard → 2*X.ncard ≤ Fintype.card V →
      X.ncard < 2 * scale X.ncard * (3*(externalBoundary H X).ncard+t)) :
    ∃ (a : V) (p : H.Walk a a), p.IsCycle ∧ t+2 ≤ p.length := by
  let k := 8 * scale (Fintype.card V) * t
  have hkpos : 0 < k := by dsimp [k]; exact Nat.mul_pos (Nat.mul_pos (by decide) (scale_pos _)) ht
  have hkn : 4*k ≤ Fintype.card V := by dsimp [k]; nlinarith
  apply long_cycle_of_band_expansion (k := k) (t := t+1) (by omega) (by omega)
  intro X hlo hhi
  have hxpos : 0 < X.ncard := by omega
  have hxhalf : 2*X.ncard ≤ Fintype.card V := by omega
  have hbound := hb X hxpos hxhalf
  have hscale := scale_mono (show X.ncard ≤ Fintype.card V by omega)
  by_contra! hbad
  have hBt : (externalBoundary H X).ncard ≤ t := by omega
  have hmul := Nat.mul_le_mul_right (3*(externalBoundary H X).ncard+t)
    (Nat.mul_le_mul_left 2 hscale)
  have hmul' := Nat.mul_le_mul_left (2*scale (Fintype.card V))
    (show 3*(externalBoundary H X).ncard+t ≤ 4*t by omega)
  dsimp [k] at hlo
  nlinarith

/-- Whole-cycle deletion costs one per piece, independently of its length. -/
lemma IsVertexMinimal.long_cycle_after_packing (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (ht : 0 < t) (hP : P.card ≤ C*t)
    (hn : 32 * scale (Fintype.card V) * t ≤ Fintype.card V) :
    ∃ (a : V) (p : (G \ unionPieces G P).Walk a a), p.IsCycle ∧ t+2 ≤ p.length :=
  long_cycle_of_log_boundary _ t ht hn (hG.packing_boundary_bound hC P hc hd t hP)

/-- Arbitrary edge deletion has the same numerical budget. The residual need
not be even or a minimal counterexample. -/
lemma IsVertexMinimal.long_cycle_after_edge_deletion (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (ht : 0 < t) (hF : F.ncard ≤ C*t)
    (hn : 32 * scale (Fintype.card V) * t ≤ Fintype.card V) :
    ∃ (a : V) (p : (G.deleteEdges F).Walk a a), p.IsCycle ∧ t+2 ≤ p.length :=
  long_cycle_of_log_boundary _ t ht hn (hG.edge_deletion_boundary_bound hC F t hF)

/-- A necessary density bound, at every admissible integer scale t. -/
theorem IsVertexMinimal.long_cycle_density_lower (hG : IsVertexMinimal C G)
    (hC : 0 < C) (t : ℕ) (ht : 0 < t)
    (hn : 32 * scale (Fintype.card V) * t ≤ Fintype.card V) :
    (C*t+1)*(t+2) ≤ G.edgeSet.ncard := by
  obtain ⟨P,hcP,hdP,hmax⟩ := exists_maximal_long_cycle_packing G (t+1)
  have hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => ⟨(hcP H hH).1,(hcP H hH).2.1⟩
  have hP : C*t < P.card := by
    by_contra! hsmall
    obtain ⟨a,p,hp,hlen⟩ := hG.long_cycle_after_packing hC P hc hdP t ht hsmall hn
    have hh := hmax a p hp
    omega
  have hsum : P.card*(t+2) ≤ ∑ H ∈ P, H.edgeSet.ncard := by
    calc
      P.card*(t+2) = ∑ _H ∈ P, (t+2) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun H hH => (hcP H hH).2.2)
  have hpart := cycle_packing_edge_card_partition G P hdP
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hpart
  have hmul := Nat.mul_le_mul_right (t+2) (show C*t+1 ≤ P.card by omega)
  omega

/-- In the large-order range the necessary density is near quadratic, with
an explicit log-fourth-power denominator. This is still only a lower bound. -/
theorem IsVertexMinimal.near_quadratic_density (hG : IsVertexMinimal C G)
    (hC : 0 < C) (hn : 64 * scale (Fintype.card V) ≤ Fintype.card V) :
    C * (Fintype.card V)^2 ≤
      (64 * scale (Fintype.card V))^2 * G.edgeSet.ncard := by
  let n := Fintype.card V
  let d := 32 * scale n
  let t := n / d
  have hd : 0 < d := Nat.mul_pos (by decide) (scale_pos n)
  have hdn : 2*d ≤ n := by dsimp [d,n]; nlinarith
  have ht : 0 < t := Nat.div_pos (by omega) hd
  have hdt : d*t ≤ n := Nat.mul_div_le n d
  have hnlt : n < d*(t+1) := by
    have hh := Nat.mod_lt n hd
    have heq := Nat.mod_add_div n d
    dsimp [t]
    nlinarith
  have hn2 : n ≤ 2*d*t := by nlinarith
  have hm := hG.long_cycle_density_lower hC t ht hdt
  have hmt : C*t^2 ≤ G.edgeSet.ncard := by nlinarith
  have hsq := Nat.mul_self_le_mul_self hn2
  have hCsq := Nat.mul_le_mul_left C hsq
  have hprod := Nat.mul_le_mul_left ((2*d)^2) hmt
  change C*n^2 ≤ (64*scale n)^2 * G.edgeSet.ncard
  have heq : 64*scale n = 2*d := by dsimp [d]; ring
  rw [heq]
  nlinarith

end Erdos184.LogDeficitSeparator
