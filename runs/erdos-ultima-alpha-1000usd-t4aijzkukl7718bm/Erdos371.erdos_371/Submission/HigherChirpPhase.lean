import Submission.HigherLogDifference

/-! Higher multiplicative differences of the archimedean chirp. Uniform
smallness at r+2 consecutive integer multipliers forces smallness of the
r+1-st logarithmic difference phase. -/
namespace Erdos371.HigherChirp
open Finset Filter MultiplicativeChirpObstruction
open scoped Topology
set_option autoImplicit false

noncomputable def unitPhase (x : ℝ) : ℂ := Complex.exp ((x : ℂ)*Complex.I)

lemma unitPhase_norm (x : ℝ) : ‖unitPhase x‖=1 := Complex.norm_exp_ofReal_mul_I x

lemma unitPhase_im (x : ℝ) : (unitPhase x).im=Real.sin x := by
  simp [unitPhase,Complex.exp_im]

lemma unitPhase_sub (x y : ℝ) :
    unitPhase (x-y)=unitPhase x*(starRingEnd ℂ) (unitPhase y) := by
  unfold unitPhase
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub]
  ring

lemma unitPhase_sub_distance (x y : ℝ) :
    ‖unitPhase (x-y)-1‖ ≤ ‖unitPhase x-1‖+‖unitPhase y-1‖ := by
  rw [unitPhase_sub]
  have he : unitPhase x*(starRingEnd ℂ) (unitPhase y)-1 =
      (unitPhase x-1)+unitPhase x*((starRingEnd ℂ) (unitPhase y)-1) := by ring
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_mul,unitPhase_norm,one_mul,← map_one (starRingEnd ℂ),← map_sub,Complex.norm_conj]
  simp only [map_one]

lemma unitPhase_chirp (t : ℝ) (n : ℕ) (hn : n≠0) :
    unitPhase (t*Real.log n)=chirp t n := (chirp_apply t n hn).symm

lemma unitPhase_higher_difference_bound (r : ℕ) (t : ℝ) (n : ℕ) (hn : 0<n)
    (η : ℝ) (hη : ∀ j : ℕ, j≤r+1 → ‖chirp t (n+j)-1‖≤η) :
    ‖unitPhase (t*positiveLogDifference r n)-1‖ ≤ (2 : ℝ)^(r+1)*η := by
  induction r generalizing n with
  | zero =>
    rw [positiveLogDifference,mul_sub]
    have h := unitPhase_sub_distance (t*Real.log (n+1 : ℝ)) (t*Real.log n)
    have he : (n+1 : ℝ)=((n+1 : ℕ) : ℝ) := by push_cast; rfl
    rw [he,unitPhase_chirp t (n+1) (by omega),unitPhase_chirp t n hn.ne'] at h
    have h0 := hη 0 (by omega)
    have h1 := hη 1 (by omega)
    simp only [Nat.add_zero] at h0
    push_cast at h
    norm_num only [pow_one]
    linarith
  | succ r ih =>
    rw [positiveLogDifference,mul_sub]
    have h := unitPhase_sub_distance (t*positiveLogDifference r n)
      (t*positiveLogDifference r (n+1 : ℝ))
    have h0 := ih n hn (fun j hj => hη j (by omega))
    have h1 := ih (n+1) (by omega) (fun j hj => by
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hη (j+1) (by omega))
    push_cast at h1
    rw [pow_succ]
    linarith

lemma unitPhase_one_ne_one : unitPhase 1≠1 := by
  intro h
  have hs : 0<Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hi := congrArg Complex.im h
  rw [unitPhase_im] at hi
  norm_num at hi
  linarith

lemma unitPhase_continuous : Continuous unitPhase := by unfold unitPhase; fun_prop

#print axioms unitPhase_higher_difference_bound
end Erdos371.HigherChirp
