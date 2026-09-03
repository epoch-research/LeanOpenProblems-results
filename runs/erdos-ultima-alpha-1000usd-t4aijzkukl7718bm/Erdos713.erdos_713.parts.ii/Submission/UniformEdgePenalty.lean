import FormalConjecturesUtil
import Submission.MergeDegreePenalty

/-! Uniform control of the contraction penalty on actual host edges.
The degree cutoff is chosen before the energy accuracy; no bound whose
constant depends on that accuracy is used. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713UniformEdgePenalty
open Erdos713DegreePenalty Erdos713UniformIncidence
variable {V W : Type*}
set_option maxHeartbeats 2000000

noncomputable def badPenaltyEdges [Fintype V] (G : SimpleGraph V) (lam t : ℝ) : Finset (V × V) :=
  univ.filter (fun p => G.Adj p.1 p.2 ∧ t < 2*lam*degreeR G p.1*degreeR G p.2)

lemma sum_left_incidence [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (∑ p : V × V, if G.Adj p.1 p.2 then (if p.1 ∈ S then (1 : ℝ) else 0) else 0) =
      ∑ v ∈ S, degreeR G v := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v : V, if v ∈ S then degreeR G v else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases hv : v ∈ S
      · simp only [hv,ite_true]
        exact (degreeR_as_sum G v).symm
      · simp [hv]
    _ = _ := by rw [← sum_filter]; simp

lemma sum_right_incidence [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (∑ p : V × V, if G.Adj p.1 p.2 then (if p.2 ∈ S then (1 : ℝ) else 0) else 0) =
      ∑ v ∈ S, degreeR G v := by
  rw [Fintype.sum_prod_type,sum_comm]
  have he (v w : V) : G.Adj w v = G.Adj v w := propext (G.adj_comm w v)
  simp_rw [he]
  simpa only [Fintype.sum_prod_type] using sum_left_incidence G S

lemma sum_edge_degree [Fintype V] (G : SimpleGraph V) :
    (∑ p : V × V, if G.Adj p.1 p.2 then degreeR G p.1+degreeR G p.2 else 0) = 2*energy G := by
  have ht (p : V × V) :
      (if G.Adj p.1 p.2 then degreeR G p.1+degreeR G p.2 else 0) =
      (if G.Adj p.1 p.2 then degreeR G p.1 else 0)+
      (if G.Adj p.1 p.2 then degreeR G p.2 else 0) := by split_ifs <;> ring
  simp_rw [ht, Fintype.sum_prod_type,sum_add_distrib]
  have hright := neighbor_degree_sum G
  have hleft : (∑ v : V, ∑ w : V, if G.Adj v w then degreeR G v else 0)=energy G := by
    rw [sum_comm]
    have he (v w : V) : G.Adj w v = G.Adj v w := propext (G.adj_comm w v)
    simp_rw [he]
    exact neighbor_degree_sum G
  rw [hleft,hright]
  ring

/-- A finite tail bound. The sum over S controls edges touching the high-degree
vertices; the remaining weighted edge sum is bounded by degree energy. -/
lemma badPenaltyEdges_bound [Fintype V] (G : SimpleGraph V) {lam t D : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) (hD : 0 ≤ D) (S : Finset V)
    (hLow : ∀ v, v ∉ S → degreeR G v ≤ D) :
    t*(badPenaltyEdges G lam t).card ≤
      2*t*(∑ v ∈ S, degreeR G v)+2*lam*D*energy G := by
  let w : V × V → ℝ := fun p => if G.Adj p.1 p.2 then
    t*(if p.1 ∈ S then 1 else 0)+t*(if p.2 ∈ S then 1 else 0)+
      lam*D*(degreeR G p.1+degreeR G p.2) else 0
  have hw (p : V × V) : 0 ≤ w p := by
    have hu := degreeR_nonneg G p.1
    have hv := degreeR_nonneg G p.2
    dsimp only [w]
    split_ifs <;> positivity
  have hp (p : V × V) (hp : p ∈ badPenaltyEdges G lam t) : t ≤ w p := by
    obtain ⟨hadj,hbad⟩ := (mem_filter.mp hp).2
    dsimp only [w]
    rw [if_pos hadj]
    have hu := degreeR_nonneg G p.1
    have hv := degreeR_nonneg G p.2
    have hnon := mul_nonneg (mul_nonneg hlam hD) (add_nonneg hu hv)
    by_cases hUS : p.1 ∈ S
    · rw [if_pos hUS]
      split_ifs <;> linarith
    by_cases hVS : p.2 ∈ S
    · rw [if_pos hVS,if_neg hUS]
      linarith
    rw [if_neg hUS,if_neg hVS]
    have h1 := mul_le_mul_of_nonneg_left (hLow p.1 hUS) hv
    have h2 := mul_le_mul_of_nonneg_left (hLow p.2 hVS) hu
    have hprod : 2*degreeR G p.1*degreeR G p.2 ≤ D*(degreeR G p.1+degreeR G p.2) := by
      nlinarith only [h1,h2]
    have hh := mul_le_mul_of_nonneg_left hprod hlam
    nlinarith only [hbad,hh]
  have hsum := sum_le_sum hp
  have hsub := sum_le_univ_sum_of_nonneg (s := badPenaltyEdges G lam t) (f := w) hw
  simp only [sum_const,nsmul_eq_mul] at hsum
  have htotal : (∑ p : V × V, w p)=2*t*(∑ v ∈ S, degreeR G v)+2*lam*D*energy G := by
    have hterm (p : V × V) : w p =
        t*(if G.Adj p.1 p.2 then (if p.1 ∈ S then 1 else 0) else 0)+
        t*(if G.Adj p.1 p.2 then (if p.2 ∈ S then 1 else 0) else 0)+
        lam*D*(if G.Adj p.1 p.2 then degreeR G p.1+degreeR G p.2 else 0) := by
      dsimp only [w]
      split_ifs <;> ring
    simp_rw [hterm,sum_add_distrib,← mul_sum]
    rw [sum_left_incidence,sum_right_incidence,sum_edge_degree]
    ring
  rw [htotal] at hsub
  nlinarith only [hsum,hsub]

/-- An arbitrarily small normalized energy penalty forces an arbitrarily
small exceptional set of ordered EDGES. The implication is uniform in
both the graph and its nonnegative penalty parameter. -/
theorem eventually_few_penalty_edges (H : SimpleGraph W) {α c t ε : ℝ}
    (ha : 1 < α) (hc : 0 < c) (ht : 0 < t) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V=n → H.Free G →
        ∀ lam : ℝ, 0 ≤ lam → lam*energy G ≤ η*(n : ℝ)^α →
          ((badPenaltyEdges G lam (t*(n : ℝ)^(α-1))).card : ℝ) ≤ ε*(n : ℝ)^α := by
  obtain ⟨K,hK,hMass⟩ := high_degree_mass H ha hc h (show 0 < ε/4 by positivity)
  let η := ε*t/(4*K)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η,hη,?_⟩
  filter_upwards [hMass,eventually_gt_atTop (0 : ℕ)] with n hmass hn
  intro V instV G hcard hf lam hlam hPenalty
  let P : ℝ := (n : ℝ)^(α-1)
  have hP : 0 < P := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  let S := univ.filter (fun v => K*P < degreeR G v)
  have hm : (∑ v ∈ S, degreeR G v) ≤ ε/4*(n : ℝ)^α :=
    hmass V G hcard hf S (fun v hv => (mem_filter.mp hv).2.le)
  have hLow (v : V) (hv : v ∉ S) : degreeR G v ≤ K*P := by
    simpa only [S,mem_filter,mem_univ,true_and,not_lt] using hv
  have hb := badPenaltyEdges_bound G hlam (mul_pos ht hP).le (mul_pos hK hP).le S hLow
  have hmass' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*(t*P) by positivity)
  have hpen' := mul_le_mul_of_nonneg_left hPenalty (show 0 ≤ 2*K*P by positivity)
  have hηeq : 4*K*η=ε*t := by dsimp [η]; field_simp
  apply (mul_le_mul_iff_right₀ (mul_pos ht hP)).mp
  have heq : (2*K*P)*(η*(n : ℝ)^α)=ε*t*P*(n : ℝ)^α/2 := by
    nlinarith only [congrArg (fun z : ℝ => z*P*(n : ℝ)^α) hηeq]
  nlinarith only [hb,hmass',hpen',heq]

#print axioms badPenaltyEdges_bound
#print axioms eventually_few_penalty_edges
end Erdos713UniformEdgePenalty
