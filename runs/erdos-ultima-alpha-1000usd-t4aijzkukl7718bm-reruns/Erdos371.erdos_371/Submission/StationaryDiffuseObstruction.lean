import FormalConjecturesUtil
import Submission.StationaryMomentObstruction
import Submission.DiffuseMomentObstruction

/-! Combining the stationary finite-state moment model with independent scale
labels. This is an abstract obstruction, not a statement about largest prime
factors of integers and not a disproof of Erdős 371. -/

namespace Erdos371StationaryDiffuseObstruction

open Finset

abbrev State (L : ℕ) := Erdos371DiffuseMomentObstruction.State L
abbrev Observation (L : ℕ) := Fin L × List ℕ

def pi {L : ℕ} (i : State L) : ℚ := Erdos371StationaryMomentObstruction.π i.1 / L
def transition {L : ℕ} (i j : State L) : ℚ := Erdos371StationaryMomentObstruction.transition i.1 j.1 / L
def observable {L : ℕ} (u : Observation L) (i : State L) : ℚ :=
  if u.1 = i.2 then Erdos371StationaryMomentObstruction.observable u.2 i.1 else 0

def expectation {L : ℕ} (f : State L → ℚ) : ℚ := ∑ i, pi i * f i

def eval {L : ℕ} : List (Observation L) → State L → ℚ
  | [], _ => 1
  | u :: us, i => observable u i * ∑ j : State L, transition i j * eval us j

def moment {L : ℕ} (us : List (Observation L)) : ℚ := expectation (eval us)
def independentMoment {L : ℕ} (us : List (Observation L)) : ℚ :=
  (us.map (fun u => expectation (observable u))).prod

def edgeExpectation {L : ℕ} (f : State L → State L → ℚ) : ℚ :=
  ∑ i, ∑ j, pi i * transition i j * f i j

lemma uniform_sum {L : ℕ} (hL : 0 < L) (a : ℚ) : (∑ _t : Fin L, a / L) = a := by
  have hl : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma pi_sum {L : ℕ} (hL : 0 < L) : (∑ i : State L, pi i) = 1 := by
  simp only [Fintype.sum_prod_type, pi]
  simp_rw [uniform_sum hL]
  exact Erdos371StationaryMomentObstruction.pi_sum

lemma row_sum {L : ℕ} (hL : 0 < L) (i : State L) :
    (∑ j : State L, transition i j) = 1 := by
  simp only [Fintype.sum_prod_type, transition]
  simp_rw [uniform_sum hL]
  exact Erdos371StationaryMomentObstruction.row_sum i.1

lemma pi_pos {L : ℕ} (hL : 0 < L) (i : State L) : 0 < pi i :=
  div_pos (Erdos371StationaryMomentObstruction.pi_pos i.1) (Nat.cast_pos.mpr hL)

lemma transition_pos {L : ℕ} (hL : 0 < L) (i j : State L) : 0 < transition i j :=
  div_pos (Erdos371StationaryMomentObstruction.transition_pos i.1 j.1) (Nat.cast_pos.mpr hL)

lemma stationary {L : ℕ} (hL : 0 < L) (j : State L) :
    (∑ i : State L, pi i * transition i j) = pi j := by
  simp only [Fintype.sum_prod_type, pi, transition]
  have he (i : Erdos371RestrictedMoments.State) : (Erdos371StationaryMomentObstruction.π i / (L:ℚ)) * (Erdos371StationaryMomentObstruction.transition i j.1 / L) =
      ((Erdos371StationaryMomentObstruction.π i * Erdos371StationaryMomentObstruction.transition i j.1) / L) / L := by ring
  simp_rw [he, uniform_sum hL]
  rw [← Finset.sum_div, Erdos371StationaryMomentObstruction.stationary]

lemma scale_average_eval {L : ℕ} (hL : 0 < L) (us : List (Observation L)) (i : Erdos371RestrictedMoments.State) :
    (∑ t : Fin L, eval us (i,t) / L) =
      (1 / (L:ℚ)) ^ us.length * Erdos371StationaryMomentObstruction.eval (us.map Prod.snd) i := by
  induction us generalizing i with
  | nil => simpa [eval, Erdos371StationaryMomentObstruction.eval] using uniform_sum hL 1
  | cons u us ih =>
      simp only [eval, observable, transition, Fintype.sum_prod_type]
      have he (i : Erdos371RestrictedMoments.State) :
          (∑ j : Erdos371RestrictedMoments.State, ∑ s : Fin L, Erdos371StationaryMomentObstruction.transition i j / (L:ℚ) * eval us (j,s)) =
          (1 / (L:ℚ)) ^ us.length * ∑ j : Erdos371RestrictedMoments.State, Erdos371StationaryMomentObstruction.transition i j * Erdos371StationaryMomentObstruction.eval (us.map Prod.snd) j := by
        calc
          _ = ∑ j : Erdos371RestrictedMoments.State, Erdos371StationaryMomentObstruction.transition i j * ∑ s : Fin L, eval us (j,s) / L := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = _ := by
            simp_rw [ih]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      rw [he]
      simp only [ite_mul, zero_mul, ite_div, zero_div, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, List.length_cons, List.map_cons, Erdos371StationaryMomentObstruction.eval, pow_succ]
      ring

lemma moment_lift {L : ℕ} (hL : 0 < L) (us : List (Observation L)) :
    moment us = (1 / (L:ℚ)) ^ us.length * Erdos371StationaryMomentObstruction.moment (us.map Prod.snd) := by
  unfold moment expectation
  simp only [Fintype.sum_prod_type, pi]
  calc
    _ = ∑ i : Erdos371RestrictedMoments.State, Erdos371StationaryMomentObstruction.π i * ∑ t : Fin L, eval us (i,t) / L := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by
      simp_rw [scale_average_eval hL]
      unfold Erdos371StationaryMomentObstruction.moment Erdos371StationaryMomentObstruction.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma expectation_observable {L : ℕ} (u : Observation L) :
    expectation (observable u) = (1 / (L:ℚ)) * Erdos371StationaryMomentObstruction.expectation (Erdos371StationaryMomentObstruction.observable u.2) := by
  simp only [expectation, observable, pi, Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold Erdos371StationaryMomentObstruction.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma independentMoment_lift {L : ℕ} (us : List (Observation L)) :
    independentMoment us = (1 / (L:ℚ)) ^ us.length * Erdos371StationaryMomentObstruction.independentMoment (us.map Prod.snd) := by
  induction us with
  | nil => simp [independentMoment, Erdos371StationaryMomentObstruction.independentMoment]
  | cons u us ih =>
      change expectation (observable u) * independentMoment us = _
      rw [expectation_observable, ih]
      simp only [List.length_cons, List.map_cons, Erdos371StationaryMomentObstruction.independentMoment_cons, pow_succ]
      ring

lemma selection_budget {L : ℕ} (hL : 0 < L) (us : List (Observation L))
    (hbudget : (us.map (fun u => Erdos371DiffuseMomentObstruction.atom L u.1 * u.2.sum)).sum ≤ 55*L) :
    ((us.map Prod.snd).map List.sum).sum ≤ 5 := by
  have hh : 10*L * ((us.map Prod.snd).map List.sum).sum ≤
      (us.map (fun u => Erdos371DiffuseMomentObstruction.atom L u.1 * u.2.sum)).sum := by
    clear hbudget
    induction us with
    | nil => simp
    | cons u us ih =>
        have hatom : 10*L ≤ Erdos371DiffuseMomentObstruction.atom L u.1 := by simp [Erdos371DiffuseMomentObstruction.atom]
        have hu := Nat.mul_le_mul_right u.2.sum hatom
        simp only [List.map_cons, List.sum_cons]
        nlinarith
  by_contra h
  have hs : 6 ≤ ((us.map Prod.snd).map List.sum).sum := by omega
  nlinarith

/-- Arbitrarily long stationary paths retain all the specified typed
subcritical selection moments, including independent scale labels. -/
theorem subcritical_path_moments {L : ℕ} (hL : 0 < L) (us : List (Observation L))
    (hmem : ∀ u ∈ us, u.2 ∈ Erdos371RestrictedMoments.selections)
    (hbudget : (us.map (fun u => Erdos371DiffuseMomentObstruction.atom L u.1 * u.2.sum)).sum ≤ 55*L) :
    moment us = independentMoment us := by
  rw [moment_lift hL, independentMoment_lift]
  congr 1
  apply Erdos371StationaryMomentObstruction.subcritical_path_moments
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    exact hmem v hv
  · exact selection_budget hL us hbudget

lemma edge_mass {L : ℕ} (i j : State L) :
    pi i * transition i j = (Erdos371DiffuseMomentObstruction.weight i j : ℚ) / (14400*(L:ℚ)^2) := by
  have hb := Erdos371StationaryMomentObstruction.pi_pos i.1
  have hbne : (Erdos371RestrictedMoments.base i.1 : ℚ) ≠ 0 := by
    intro h
    change 0 < (Erdos371RestrictedMoments.base i.1 : ℚ) / 120 at hb
    rw [h] at hb
    norm_num at hb
  unfold pi transition Erdos371DiffuseMomentObstruction.weight
  dsimp only [Erdos371StationaryMomentObstruction.π, Erdos371StationaryMomentObstruction.transition]
  field_simp
  ring

lemma edgeExpectation_eq {L : ℕ} (f : State L → State L → ℚ) :
    edgeExpectation f =
      (∑ i : State L, ∑ j : State L, (Erdos371DiffuseMomentObstruction.weight i j : ℚ) * f i j) / (14400*(L:ℚ)^2) := by
  simp only [edgeExpectation, edge_mass, Finset.sum_div, div_mul_eq_mul_div]

/-- Bias survives the stationary diffuse extension. -/
theorem signed_adjacent_mean {L : ℕ} (hL : 0 < L) :
    edgeExpectation (fun i j : State L => (Erdos371DiffuseMomentObstruction.cmp (Erdos371DiffuseMomentObstruction.value i) (Erdos371DiffuseMomentObstruction.value j) : ℚ)) = 1/7200 := by
  rw [edgeExpectation_eq]
  have hs : (∑ i : State L, ∑ j : State L,
      (Erdos371DiffuseMomentObstruction.weight i j : ℚ) * (Erdos371DiffuseMomentObstruction.cmp (Erdos371DiffuseMomentObstruction.value i) (Erdos371DiffuseMomentObstruction.value j) : ℚ)) = 2*(L:ℚ)^2 := by
    exact_mod_cast Erdos371DiffuseMomentObstruction.signed_comparison L
  rw [hs]
  have hl : (L:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp
  ring

lemma tie_probability_eq (L : ℕ) :
    (edgeExpectation (fun i j : State L => if Erdos371DiffuseMomentObstruction.value i = Erdos371DiffuseMomentObstruction.value j then 1 else 0) : ℝ) =
      (Erdos371DiffuseMomentObstruction.tieWeight L : ℝ) / (14400*(L:ℝ)^2) := by
  have he : edgeExpectation (fun i j : State L =>
      if Erdos371DiffuseMomentObstruction.value i = Erdos371DiffuseMomentObstruction.value j then 1 else 0) =
      (Erdos371DiffuseMomentObstruction.tieWeight L : ℚ) / (14400*(L:ℚ)^2) := by
    rw [edgeExpectation_eq]
    simp [Erdos371DiffuseMomentObstruction.tieWeight, mul_ite]
  rw [he]
  push_cast
  rfl

open Filter
open scoped Topology

/-- The stationary kernels have vanishing tie probability, but their signed
adjacent comparison remains the nonzero constant above. -/
theorem tie_probability_tendsto_zero :
    Tendsto (fun L : ℕ =>
      (edgeExpectation (fun i j : State L => if Erdos371DiffuseMomentObstruction.value i = Erdos371DiffuseMomentObstruction.value j then 1 else 0) : ℝ))
      atTop (𝓝 0) := by
  simpa only [tie_probability_eq] using Erdos371DiffuseMomentObstruction.tie_probability_tendsto_zero

end Erdos371StationaryDiffuseObstruction

#print axioms Erdos371StationaryDiffuseObstruction.subcritical_path_moments
#print axioms Erdos371StationaryDiffuseObstruction.signed_adjacent_mean
#print axioms Erdos371StationaryDiffuseObstruction.tie_probability_tendsto_zero
