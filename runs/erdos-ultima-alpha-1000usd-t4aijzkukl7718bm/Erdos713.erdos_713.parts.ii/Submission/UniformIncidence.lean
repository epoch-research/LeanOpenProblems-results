import FormalConjecturesUtil
import Submission.SmallSetIncidence

/-! Uniform small-set and high-degree incidence control in H-free hosts.
These conclusions do not preserve full clone saturation under deletion. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713UniformIncidence
open Erdos713SmallSetIncidence Erdos713Cloning
set_option maxHeartbeats 2000000
variable {V W : Type*}

lemma small_fraction_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (hFree : H.Free G)
    {α C B δ : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ δ)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (S : Finset V) (hS : (S.card : ℝ) ≤ δ*Fintype.card V) :
    (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤
      (4*C*(2 : ℝ)^α*δ^(α-1))*(Fintype.card V : ℝ)^α+8*B*Fintype.card V := by
  have he := degree_mass_power_bound H G hFree ha hC hB hU S
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg S.card) hS (show 0 ≤ α-1 by linarith)
  rw [Real.mul_rpow hd (Nat.cast_nonneg (Fintype.card V))] at hp
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 4*C*(2 : ℝ)^α*Fintype.card V by positivity)
  rw [rpow_factor (Nat.cast_nonneg (Fintype.card V)) ha]
  nlinarith only [he,hm]

/-- Uniform absolute continuity of degree mass with respect to vertex mass
at the n^alpha scale. The host need only be H-free, not extremal. -/
theorem small_set_mass {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n → H.Free G →
        ∀ S : Finset V, (S.card : ℝ) ≤ δ*n →
          (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤ ε*(n : ℝ)^α := by
  let C := 2*c
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨B,hB,hU⟩ := Erdos713RelativeExpansion.linear_error_upper
    (fun n => extremalNumber n H) (extremal_zero H) hC (by dsimp [C]; linarith) h
  let A := 4*C*(2 : ℝ)^α
  have hA : 0 < A := by dsimp [A]; positivity
  let δ := (ε/(2*A))^((α-1)⁻¹)
  have hd : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hdpow : δ^(α-1) = ε/(2*A) := Real.rpow_inv_rpow (by positivity) (by linarith)
  have hcoef : A*δ^(α-1) = ε/2 := by rw [hdpow]; field_simp
  have ht : Tendsto (fun n : ℕ => (ε/16)*(n : ℝ)^(α-1)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop (by linarith : 0 < α-1)).comp tendsto_natCast_atTop_atTop)
  refine ⟨δ,hd,?_⟩
  filter_upwards [ht.eventually_ge_atTop B] with n hn
  intro V instV G hcard hf S hS
  have hm := small_fraction_bound H G hf ha hC.le hB hd.le hU S (by simpa [hcard] using hS)
  change (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤
    (A*δ^(α-1))*(Fintype.card V : ℝ)^α+8*B*Fintype.card V at hm
  rw [hcoef,hcard] at hm
  have hb := mul_le_mul_of_nonneg_right hn (show (0 : ℝ) ≤ 8*n by positivity)
  have hfac := rpow_factor (Nat.cast_nonneg n) ha
  rw [hfac] at hm ⊢
  nlinarith only [hm,hb]

/-- High-degree vertices carry arbitrarily little total degree mass when
the threshold constant is chosen sufficiently large. -/
theorem high_degree_mass {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n → H.Free G →
        ∀ S : Finset V, (∀ v ∈ S, K*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) →
          (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤ ε*(n : ℝ)^α := by
  classical
  obtain ⟨δ,hd,hSmall⟩ := small_set_mass H ha hc h hε
  let K := 4*c/δ
  have hK : 0 < K := by dsimp [K]; positivity
  have hkδ : K*δ = 4*c := by dsimp [K]; field_simp
  have hu : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ 2*c*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const (show c < 2*c by linarith),
      eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp : (0 : ℝ) < n) α)).mp hn).le
  refine ⟨K,hK,?_⟩
  filter_upwards [hSmall,hu,eventually_gt_atTop (0 : ℕ)] with n hS hU hn
  intro V instV G hcard hf S hHigh
  apply hS V G hcard hf S
  have he : (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber n H : ℝ) := by
    have hh := card_edgeFinset_le_extremalNumber hf
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card,← hcard] using
      (show (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber (Fintype.card V) H : ℝ) by
        exact_mod_cast (by simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh))
  have hsum : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    exact_mod_cast (by
      simpa only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] using
        G.sum_degrees_eq_twice_card_edges)
  have hSub : (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤
      ∑ v : V, (Nat.card (G.neighborSet v) : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.cast_nonneg _)
  have hLow := sum_le_sum (s := S) hHigh
  simp only [sum_const,nsmul_eq_mul] at hLow
  rw [hsum] at hSub
  have hp : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hfac := rpow_factor (Nat.cast_nonneg n) ha
  rw [hfac] at hU
  have hh : (K*(S.card : ℝ))*(n : ℝ)^(α-1) ≤ (4*c*n)*(n : ℝ)^(α-1) := by
    nlinarith only [he,hU,hSub,hLow]
  have hKs : K*(S.card : ℝ) ≤ 4*c*n := (mul_le_mul_iff_left₀ hp).mp hh
  have heq : 4*c*(n : ℝ) = K*(δ*n) := by rw [← hkδ]; ring
  rw [heq] at hKs
  exact (mul_le_mul_iff_right₀ hK).mp hKs

/-- Vertex deletion loses at most the original degree sum of the deleted
set; no maximum-degree bound is assumed. -/
lemma edges_le_induce_compl_add_degree [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    Nat.card G.edgeSet ≤ Nat.card (G.induce (S : Set V)ᶜ).edgeSet +
      ∑ v ∈ S, Nat.card (G.neighborSet v) := by
  classical
  let B := S.biUnion (fun v => G.incidenceFinset v)
  have hcov : G.edgeFinset ⊆ (G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2) ∪ B := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      by_cases hu : u ∈ S
      · apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨u,hu,?_⟩
        simp [incidenceFinset_eq_filter,huv]
      by_cases hv : v ∈ S
      · apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨v,hv,?_⟩
        simp [incidenceFinset_eq_filter,huv]
      · exact mem_union_left _ (mem_inter.mpr ⟨he,by simp [hu,hv]⟩)
  have hB : B.card ≤ ∑ v ∈ S, Nat.card (G.neighborSet v) := by
    simpa only [card_incidenceFinset_eq_degree,Nat.card_eq_fintype_card,
      card_neighborSet_eq_degree] using (card_biUnion_le (s := S) (t := fun v => G.incidenceFinset v))
  have hinner : (G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2).card =
      Nat.card (G.induce (S : Set V)ᶜ).edgeSet := by
    rw [← map_edgeFinset_induce,card_map,edgeFinset_card,Fintype.card_eq_nat_card]
  have hh := ((card_le_card hcov).trans (card_union_le _ _)).trans (Nat.add_le_add_left hB _)
  simpa only [hinner,edgeFinset_card,Fintype.card_eq_nat_card] using hh

#print axioms small_fraction_bound
#print axioms small_set_mass
#print axioms high_degree_mass
#print axioms edges_le_induce_compl_add_degree
end Erdos713UniformIncidence
