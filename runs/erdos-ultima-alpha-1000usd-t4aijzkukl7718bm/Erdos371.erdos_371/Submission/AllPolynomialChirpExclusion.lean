import Submission.HigherChirpScale

/-! The archimedean chirp obstruction fails uniform multiplier stability on
EVERY fixed positive-power range. This rules out this specific countermodel,
not all possible obstructions to natural prime-factor comparison symmetry. -/
namespace Erdos371.HigherChirp
open Finset Filter MultiplicativeChirpObstruction
open scoped Topology
set_option autoImplicit false

/-- For every delta>0, a chirp at parameter N has a multiplier at most N^delta
whose value stays a definite distance from one, for every sufficiently large N. -/
theorem chirp_polynomial_multiplier_separation (δ : ℝ) (hδ : 0<δ) :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ N : ℕ in atTop,
      ∃ k : ℕ, 0<k ∧ (k : ℝ)≤(N : ℝ)^δ ∧ η≤‖chirp N k-1‖ := by
  obtain ⟨r,hr⟩ := exists_nat_one_div_lt hδ
  let z := ‖unitPhase 1-1‖
  have hz : 0<z := norm_pos_iff.mpr (sub_ne_zero.mpr unitPhase_one_ne_one)
  let η := z/(2 : ℝ)^(r+2)
  have hη : 0<η := by dsimp [η]; positivity
  have ht := ((unitPhase_continuous.tendsto 1).comp (higher_chirp_phase_tendsto_one r)).sub_const (1 : ℂ)
  have hnorm := ht.norm
  have hsmall := hnorm.eventually_const_lt (show z/2<z by linarith)
  refine ⟨η,hη,?_⟩
  filter_upwards [hsmall,(chirpDifferenceBase_tendsto r).eventually_gt_atTop 0,
    chirpDifferenceBase_polynomial_range r δ hr] with N hphase hbase hrange
  by_contra h
  push_neg at h
  have hvalues (j : ℕ) (hj : j≤r+1) :
      ‖chirp N (chirpDifferenceBase r N+j)-1‖≤η := by
    apply (h _ (by omega) _).le
    have he : (chirpDifferenceBase r N+j : ℕ)≤chirpDifferenceBase r N+r+1 := by omega
    exact (show ((chirpDifferenceBase r N+j : ℕ) : ℝ)≤(chirpDifferenceBase r N+r+1 : ℕ) by exact_mod_cast he).trans hrange
  have hb := unitPhase_higher_difference_bound r N (chirpDifferenceBase r N) hbase η hvalues
  have he : (2 : ℝ)^(r+1)*η=z/2 := by
    dsimp [η]
    rw [show r+2=(r+1)+1 by omega,pow_succ]
    field_simp
    ring
  rw [he] at hb
  exact (not_lt_of_ge hb) hphase

/-- In particular, taking a subsequence of parameters cannot repair the
failure of uniform stability on a prescribed positive-power multiplier range. -/
theorem no_uniform_polynomial_multiplier_invariance (δ : ℝ) (hδ : 0<δ)
    (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ¬(∀ ε : ℝ, 0<ε → ∀ᶠ j : ℕ in atTop,
      ∀ k : ℕ, 0<k → (k : ℝ)≤(A j : ℝ)^δ → ‖chirp (A j) k-1‖<ε) := by
  intro h
  obtain ⟨η,hη,hsep⟩ := chirp_polynomial_multiplier_separation δ hδ
  obtain ⟨j,hj,hclose⟩ := ((hA.eventually hsep).and (h η hη)).exists
  obtain ⟨k,hk,hkbound,hfar⟩ := hj
  exact hfar.not_gt (hclose k hk hkbound)

#print axioms chirp_polynomial_multiplier_separation
#print axioms no_uniform_polynomial_multiplier_invariance
end Erdos371.HigherChirp
