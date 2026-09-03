import FormalConjecturesUtil
import Submission.NearOptimalExpanders

/-! Finite comparisons for a degree-square-penalized edge objective.
These are witness lemmas, not a rationality theorem. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713DegreePenalty
open Erdos713Cloning
variable {V W : Type*}
set_option maxHeartbeats 1000000

noncomputable def degreeR [Fintype V] (G : SimpleGraph V) (v : V) : ℝ :=
  Nat.card (G.neighborSet v)

noncomputable def edgesR [Fintype V] (G : SimpleGraph V) : ℝ :=
  Nat.card G.edgeSet

open scoped Classical in
noncomputable def energy [Fintype V] (G : SimpleGraph V) : ℝ :=
  ∑ v, degreeR G v ^ 2

noncomputable def score [Fintype V] (lam : ℝ) (G : SimpleGraph V) : ℝ :=
  edgesR G - lam * energy G

lemma degreeR_nonneg [Fintype V] (G : SimpleGraph V) (v : V) : 0 ≤ degreeR G v :=
  Nat.cast_nonneg _

lemma energy_nonneg [Fintype V] (G : SimpleGraph V) : 0 ≤ energy G := by
  classical
  exact sum_nonneg (fun _ _ => sq_nonneg _)

lemma degreeR_sum [Fintype V] (G : SimpleGraph V) :
    ∑ v, degreeR G v = 2 * edgesR G := by
  classical
  have h := G.sum_degrees_eq_twice_card_edges
  simpa only [degreeR, edgesR, Nat.card_eq_fintype_card,
    card_neighborSet_eq_degree, ← edgeFinset_card, Nat.cast_sum, Nat.cast_mul,
    Nat.cast_ofNat] using congrArg (fun n : ℕ => (n : ℝ)) h

lemma degreeR_as_sum [Fintype V] (G : SimpleGraph V) (x : V) :
    degreeR G x = ∑ y, if G.Adj x y then (1 : ℝ) else 0 := by
  classical
  rw [degreeR, Nat.card_eq_fintype_card, card_neighborSet_eq_degree,
    ← card_neighborFinset_eq_degree, Finset.card_eq_sum_ones]
  push_cast
  simpa only [neighborFinset_eq_filter] using
    (sum_filter (s := univ) (p := G.Adj x) (f := fun _ => (1 : ℝ)))

lemma clone_degree_none [Fintype V] (G : SimpleGraph V) (v : V) :
    degreeR (clone G v) none = degreeR G v := by
  unfold degreeR
  rw [Nat.card_congr (neighborEquiv G v)]

lemma clone_degree_some [Fintype V] (G : SimpleGraph V) (v w : V) :
    degreeR (clone G v) (some w) = degreeR G w + if G.Adj w v then 1 else 0 := by
  classical
  rw [degreeR_as_sum, Fintype.sum_option, degreeR_as_sum]
  simp only [clone_adj, project_some, project_none]
  ring

lemma clone_energy [Fintype V] (G : SimpleGraph V) (v : V) :
    energy (clone G v) - energy G = degreeR G v ^ 2 + degreeR G v +
      2 * ∑ w, if G.Adj v w then degreeR G w else 0 := by
  classical
  unfold energy
  rw [Fintype.sum_option, clone_degree_none]
  simp_rw [clone_degree_some]
  have hterm (w : V) : (degreeR G w + if G.Adj w v then 1 else 0)^2 =
      degreeR G w ^ 2 + (if G.Adj v w then (1 : ℝ) else 0) +
        2 * (if G.Adj v w then degreeR G w else 0) := by
    by_cases hw : G.Adj v w
    · simp [hw, hw.symm]; ring
    · have hw' : ¬ G.Adj w v := fun h => hw h.symm
      simp [hw, hw']
  simp_rw [hterm]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← degreeR_as_sum]
  ring

lemma clone_energy_nonneg [Fintype V] (G : SimpleGraph V) (v : V) :
    0 ≤ energy (clone G v) - energy G := by
  classical
  rw [clone_energy]
  exact add_nonneg (add_nonneg (sq_nonneg _) (degreeR_nonneg _ _))
    (mul_nonneg (by norm_num) (sum_nonneg (fun w _ => by
      split_ifs
      · exact degreeR_nonneg G w
      · exact le_refl 0)))

lemma neighbor_degree_sum [Fintype V] (G : SimpleGraph V) :
    (∑ v, ∑ w, if G.Adj v w then degreeR G w else 0) = energy G := by
  classical
  rw [sum_comm]
  unfold energy
  apply sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then degreeR G w else 0) =
        (∑ v, if G.Adj w v then (1 : ℝ) else 0) * degreeR G w := by
      rw [sum_mul]
      apply sum_congr rfl
      intro v _
      by_cases h : G.Adj w v
      · simp [h, h.symm]
      · have h' : ¬ G.Adj v w := fun h' => h h'.symm
        simp [h, h']
    _ = degreeR G w ^ 2 := by rw [← degreeR_as_sum]; ring

lemma sum_clone_energy [Fintype V] (G : SimpleGraph V) :
    (∑ v, (energy (clone G v) - energy G)) = 3 * energy G + 2 * edgesR G := by
  classical
  simp_rw [clone_energy]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, neighbor_degree_sum, degreeR_sum]
  change energy G + 2 * edgesR G + 2 * energy G = _
  ring

lemma clone_score [Fintype V] (G : SimpleGraph V) (lam : ℝ) (v : V) :
    score lam (clone G v) - score lam G =
      degreeR G v - lam * (energy (clone G v) - energy G) := by
  have he : edgesR (clone G v) = edgesR G + degreeR G v := by
    unfold edgesR degreeR
    rw [card_edges_clone, Nat.cast_add]
  unfold score
  rw [he]
  ring

lemma sum_clone_score [Fintype V] (G : SimpleGraph V) (lam : ℝ) :
    (∑ v, (score lam (clone G v) - score lam G)) =
      2 * edgesR G - lam * (3 * energy G + 2 * edgesR G) := by
  classical
  simp_rw [clone_score]
  rw [sum_sub_distrib, ← mul_sum, sum_clone_energy, degreeR_sum]

/-- Safe-clone comparisons imply a lower bound on the degree mass of the
obstructed roots of the same host. -/
lemma obstructed_degree_mass [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {lam Δ : ℝ} (hlam : 0 ≤ lam) (hΔ : 0 ≤ Δ)
    (hsafe : ∀ v, H.Free (clone G v) → score lam (clone G v) ≤ score lam G + Δ) :
    2 * edgesR G - lam * (3 * energy G + 2 * edgesR G) - Fintype.card V * Δ ≤
      ∑ v, if H ⊑ clone G v then degreeR G v else 0 := by
  classical
  have hpoint (v : V) : score lam (clone G v) - score lam G ≤
      Δ + if H ⊑ clone G v then degreeR G v else 0 := by
    by_cases h : H ⊑ clone G v
    · rw [if_pos h, clone_score]
      have hp := mul_nonneg hlam (clone_energy_nonneg G v)
      linarith
    · rw [if_neg h]
      have hh := hsafe v h
      linarith
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  rw [sum_clone_score, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hh
  linarith

lemma fold_degree_mass [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hfree : H.Free G) {lam Δ : ℝ} (hlam : 0 ≤ lam) (hΔ : 0 ≤ Δ)
    (hsafe : ∀ v, H.Free (clone G v) → score lam (clone G v) ≤ score lam G + Δ) :
    2 * edgesR G - lam * (3 * energy G + 2 * edgesR G) - Fintype.card V * Δ ≤
      ∑ v, if SingleFold H G v then degreeR G v else 0 := by
  classical
  simpa only [fold_iff_obstructed H G _ hfree] using
    obstructed_degree_mass H G hlam hΔ hsafe


lemma degreeR_mono [Fintype V] {J G : SimpleGraph V} (h : J ≤ G) (v : V) :
    degreeR J v ≤ degreeR G v := by
  classical
  rw [degreeR_as_sum, degreeR_as_sum]
  apply sum_le_sum
  intro w _
  by_cases hj : J.Adj v w
  · simp [hj, h hj]
  · simp only [if_neg hj]
    split_ifs <;> norm_num

lemma deletion_energy [Fintype V] (G : SimpleGraph V) (v : V) :
    energy (G.deleteIncidenceSet v) + degreeR G v ^ 2 ≤ energy G := by
  classical
  have hzero : degreeR (G.deleteIncidenceSet v) v = 0 := by
    rw [degreeR_as_sum]
    simp only [deleteIncidenceSet_adj, ne_eq, not_true_eq_false, and_false,
      false_and, ite_false, sum_const_zero]
  have hle : (∑ w ∈ univ.erase v, degreeR (G.deleteIncidenceSet v) w ^ 2) ≤
      ∑ w ∈ univ.erase v, degreeR G w ^ 2 := by
    apply sum_le_sum
    intro w _
    exact pow_le_pow_left₀ (degreeR_nonneg _ _)
      (degreeR_mono (G.deleteIncidenceSet_le v) w) 2
  have hJ := sum_erase_add (s := (univ : Finset V))
    (f := fun w => degreeR (G.deleteIncidenceSet v) w ^ 2) (mem_univ v)
  have hG := sum_erase_add (s := (univ : Finset V))
    (f := fun w => degreeR G w ^ 2) (mem_univ v)
  dsimp only at hJ hG
  rw [hzero, zero_pow (by decide : 2 ≠ 0), add_zero] at hJ
  unfold energy
  linarith

lemma deletion_edges [Fintype V] (G : SimpleGraph V) (v : V) :
    edgesR (G.deleteIncidenceSet v) = edgesR G - degreeR G v := by
  classical
  have hh := G.card_edgeFinset_deleteIncidenceSet v
  have hd := G.degree_le_card_edgeFinset v
  unfold edgesR degreeR
  simp only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, ← edgeFinset_card]
  rw [hh, Nat.cast_sub hd]

/-- Same-order optimality for the penalized objective. -/
structure Optimal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (lam : ℝ) : Prop where
  free : H.Free G
  compare : ∀ J : SimpleGraph V, H.Free J → score lam J ≤ score lam G

lemma Optimal.degree_bound [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam : ℝ} (hopt : Optimal H G lam) (hlam : 0 < lam) (v : V) :
    degreeR G v ≤ 1 / lam := by
  have hJ : H.Free (G.deleteIncidenceSet v) :=
    fun h => hopt.free (h.trans (IsContained.of_le (G.deleteIncidenceSet_le v)))
  have hcomp := hopt.compare _ hJ
  have henergy := mul_le_mul_of_nonneg_left (deletion_energy G v) hlam.le
  unfold score at hcomp
  rw [deletion_edges] at hcomp
  have hquad : lam * degreeR G v ^ 2 ≤ degreeR G v := by nlinarith only [hcomp, henergy]
  by_cases hz : degreeR G v = 0
  · rw [hz]
    positivity
  · have hd : 0 < degreeR G v := lt_of_le_of_ne (degreeR_nonneg _ _) (Ne.symm hz)
    apply (le_div_iff₀ hlam).mpr
    nlinarith only [hquad, hd]

lemma exists_optimal [Fintype V] (H : SimpleGraph W) (lam : ℝ)
    (hex : ∃ J : SimpleGraph V, H.Free J) :
    ∃ G : SimpleGraph V, Optimal H G lam := by
  classical
  let S : Finset (SimpleGraph V) := univ.filter (H.Free ·)
  have hS : S.Nonempty := by
    obtain ⟨J, hJ⟩ := hex
    exact ⟨J, by simpa [S] using hJ⟩
  obtain ⟨G, hG, hmax⟩ := S.exists_max_image (score lam) hS
  refine ⟨G, ⟨?_, ?_⟩⟩
  · simpa [S] using hG
  · intro J hJ
    exact hmax J (by simpa [S] using hJ)

#print axioms clone_energy
#print axioms sum_clone_energy
#print axioms sum_clone_score
#print axioms fold_degree_mass
#print axioms deletion_energy
#print axioms Optimal.degree_bound
#print axioms exists_optimal


end Erdos713DegreePenalty
