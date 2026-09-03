import Submission.TripleIntersectionPotentialExplore

/-! The triple-mean estimate for every fixed comparability factor, not only
for n <= 4N. Constants may depend on the fixed factor. -/
namespace Erdos66GeneralCentralTripleMean
open Filter Erdos66TripleIntersectionMean Erdos66TripleIntersectionPotential
  Erdos66TripleIntersectionGeometry Erdos66BernoulliMatchingPolynomial
  Erdos66Fractional Erdos66FractionalFourthPower Erdos66Generating
  Erdos66CumulativeRoundingError Erdos66QuadraticWindowRounding
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma prefixMajorant_comparable (C N n : ℕ) (hn : n ≤ C*N) :
    Real.sqrt (prefixMajorant n) ≤ (2*(C:ℝ)+2)*Real.sqrt ((N:ℝ)+1)*ell N := by
  have hx : 0 < (N:ℝ)+1 := by positivity
  have hnr : (n:ℝ) ≤ (C:ℝ)*N := by exact_mod_cast hn
  have harg : ((2*n+1:ℕ):ℝ) ≤ (2*(C:ℝ)+1)*((N:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) C]
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < ((2*n+1:ℕ):ℝ)) harg
  rw [Real.log_mul (by positivity) hx.ne'] at hlog
  have hlogC : Real.log (2*(C:ℝ)+1) ≤ 2*(C:ℝ)+1 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hharm := harmonic_le_one_add_log (2*n+1)
  have he := ell_one_le N
  have he0 : 0 ≤ ell N := by linarith
  have hH : (harmonic (2*n+1):ℝ) ≤ (2*(C:ℝ)+2)*ell N := by
    dsimp only [ell] at he ⊢
    have hC := Nat.cast_nonneg (α := ℝ) C
    nlinarith
  have harg' : ((2*n+1:ℕ):ℝ) ≤ (2*(C:ℝ)+2)*((N:ℝ)+1) := by nlinarith only [harg,hx]
  have hmul := mul_le_mul harg' hH (harmonic_nonneg _) (by positivity : (0:ℝ) ≤ (2*(C:ℝ)+2)*((N:ℝ)+1))
  have hpref : prefixMajorant n ≤ (2*(C:ℝ)+2)^2*((N:ℝ)+1)*ell N := by
    dsimp only [prefixMajorant]
    convert hmul using 1 <;> ring
  have hs := Real.sq_sqrt hx.le
  have he2 : ell N ≤ (ell N)^2 := by nlinarith
  have hmul2 := mul_le_mul_of_nonneg_left he2
    (show 0 ≤ (2*(C:ℝ)+2)^2*((N:ℝ)+1) by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (2*(C:ℝ)+2)^2*((N:ℝ)+1)*(ell N)^2 := hpref.trans hmul2
    _ = _ := by nlinarith only [hs]

noncomputable def comparableMeanBound (C N : ℕ) : ℝ :=
  (2*(C:ℝ)+2)*(ell N)^2/Real.sqrt ((N:ℝ)+1)

lemma tripleMean_comparable (L C N n z : ℕ) (hn : n ≤ C*N) :
    tripleMean L N n z ≤ comparableMeanBound C N := by
  have hx : 0 < (N:ℝ)+1 := by positivity
  have hspos := Real.sqrt_pos.mpr hx
  have hs := Real.sq_sqrt hx.le
  have hsq := profile_square_bound N
  have hH := harmonic_le_one_add_log (N+1)
  simp only [Nat.cast_add,Nat.cast_one] at hH
  have hp : (profile N)^2*((N:ℝ)+1) ≤ ell N := by dsimp only [ell]; nlinarith only [hsq,hH]
  have he := ell_one_le N
  have hps : (profile N)^2*Real.sqrt ((N:ℝ)+1) ≤ ell N/Real.sqrt ((N:ℝ)+1) := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith only [hp,hs]
  calc
    _ ≤ (profile N)^2*Real.sqrt (prefixMajorant n) := tripleMean_bound L N n z
    _ ≤ (profile N)^2*((2*(C:ℝ)+2)*Real.sqrt ((N:ℝ)+1)*ell N) :=
      mul_le_mul_of_nonneg_left (prefixMajorant_comparable C N n hn) (sq_nonneg _)
    _ ≤ comparableMeanBound C N := by
      have hh := mul_le_mul_of_nonneg_right hps (show 0 ≤ (2*(C:ℝ)+2)*ell N by positivity)
      dsimp only [comparableMeanBound]
      convert hh using 1 <;> ring

lemma comparable_tilted_mean_limit (C : ℕ) :
    Tendsto (fun N ↦ Real.exp (tilt N)*comparableMeanBound C N) atTop (𝓝 0) := by
  have hh := tilted_mean_limit.const_mul ((2*(C:ℝ)+2)/10)
  simp only [mul_zero] at hh
  convert hh using 1
  funext N
  dsimp only [comparableMeanBound,meanBound]
  ring

lemma eventually_comparable_poly_mean (C : ℕ) : ∀ᶠ N : ℕ in atTop,
    ∀ L n z, n ≤ C*N → matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ profile i.val) ≤ Real.exp 1 := by
  filter_upwards [(comparable_tilted_mean_limit C).eventually_le_const (show (0:ℝ)<1 by norm_num)] with N hN
  intro L n z hn
  have hm := tripleMean_comparable L C N n z hn
  have h1 := mul_le_mul_of_nonneg_right
    (show Real.exp (tilt N)-1 ≤ Real.exp (tilt N) by linarith) (tripleMean_nonneg L N n z)
  have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos (tilt N)).le
  have he : (Real.exp (tilt N)-1)*tripleMean L N n z ≤ 1 := by linarith only [hN,h1,h2]
  exact (matchingPoly_upper (triples L N n z) coords (tilt N) (tilt_nonneg N) (fun i ↦ profile i.val)
    (fun i ↦ profile_nonneg i.val)).trans (Real.exp_le_exp.mpr he)

end Erdos66GeneralCentralTripleMean
