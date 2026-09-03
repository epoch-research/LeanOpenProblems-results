import Submission.BernoulliMatchingPolynomialExplore
import Submission.TripleIntersectionMeanExplore

/-! Summable matching-polynomial penalties for uniformly bounded central
triple intersections on any fixed polynomial target horizon. -/
namespace Erdos66TripleIntersectionPotential
open Filter Erdos66FiniteBernoulli Erdos66Fractional Erdos66TripleIntersectionGeometry
  Erdos66TripleIntersectionMean Erdos66BernoulliMatchingPolynomial
open scoped Classical Topology
set_option maxHeartbeats 2200000

noncomputable def tripleWeight (h N : ℕ) : ℝ :=
  Real.exp (-((h : ℝ)+4)*Real.log ((N : ℝ)+1))

lemma tripleWeight_pos (h N : ℕ) : 0 < tripleWeight h N := Real.exp_pos _

lemma tripleWeight_formula (h N : ℕ) : tripleWeight h N = 1/((N : ℝ)+1)^(h+4) := by
  rw [tripleWeight, neg_mul, Real.exp_neg]
  have he : Real.exp (((h : ℝ)+4)*Real.log ((N : ℝ)+1)) = ((N : ℝ)+1)^(h+4) := by
    have hh := Real.exp_nat_mul (Real.log ((N : ℝ)+1)) (h+4)
    rw [Real.exp_log (by positivity)] at hh
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh
  rw [he,one_div]

lemma tripleMean_nonneg (L N n z : ℕ) : 0 ≤ tripleMean L N n z :=
  Finset.sum_nonneg (fun e he ↦ Finset.prod_nonneg (fun i hi ↦ profile_nonneg i.val))

lemma eventually_weighted_triple_mean : ∀ᶠ N : ℕ in atTop, ∀ L h n z : ℕ, n ≤ 4*N →
    tripleWeight h N*matchingPoly (triples L N n z) coords (tilt N)
      (fun i ↦ profile i.val) ≤ Real.exp 1/((N : ℝ)+1)^(h+4) := by
  filter_upwards [tilted_mean_limit.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with N hN
  intro L h n z hn
  have hb := matchingPoly_upper (triples L N n z) coords (tilt N) (tilt_nonneg N)
    (fun i ↦ profile i.val) (fun i ↦ profile_nonneg i.val)
  have hm := tripleMean_central_bound L N n z hn
  have he : (Real.exp (tilt N)-1)*tripleMean L N n z ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right
      (show Real.exp (tilt N)-1 ≤ Real.exp (tilt N) by linarith) (tripleMean_nonneg L N n z)
    have h2 := mul_le_mul_of_nonneg_left hm (Real.exp_pos (tilt N)).le
    linarith
  have hh := hb.trans (Real.exp_le_exp.mpr he)
  have ht := mul_le_mul_of_nonneg_left hh (tripleWeight_pos h N).le
  rw [tripleWeight_formula] at ht ⊢
  convert ht using 1 <;> ring

noncomputable def rowTail (N : ℕ) : ℝ := 10*Real.exp 1/((N : ℝ)+1)^3

lemma rowTail_summable : Summable rowTail := by
  have hh := (Real.summable_one_div_nat_add_rpow 1 (3 : ℕ)).mpr (by norm_num)
  have hh' := hh.mul_left (10*Real.exp 1)
  simpa only [rowTail,Real.rpow_natCast,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑(_:ℕ):ℝ)+1),
    mul_one_div] using hh'

lemma target_count_weight (h N : ℕ) :
    ((4*N+1 : ℕ) : ℝ)*(N^h+1 : ℕ)*(Real.exp 1/((N : ℝ)+1)^(h+4)) ≤ rowTail N := by
  have hx : 0 < (N : ℝ)+1 := by positivity
  have hx1 : (1 : ℝ) ≤ (N : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hpow : (N : ℝ)^h ≤ ((N : ℝ)+1)^h := pow_le_pow_left₀ (by positivity) (by linarith) h
  have hp1 : (1 : ℝ) ≤ ((N : ℝ)+1)^h := one_le_pow₀ hx1
  have hc1 : ((4*N+1 : ℕ) : ℝ) ≤ 5*((N : ℝ)+1) := by push_cast; linarith
  have hc2 : ((N^h+1 : ℕ) : ℝ) ≤ 2*((N : ℝ)+1)^h := by push_cast; linarith
  have hmul := mul_le_mul hc1 hc2 (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 5*((N : ℝ)+1))
  have hh := mul_le_mul_of_nonneg_right hmul
    (show (0 : ℝ) ≤ Real.exp 1/((N : ℝ)+1)^(h+4) by positivity)
  apply hh.trans_eq
  dsimp only [rowTail]
  rw [show h+4=h+1+3 by omega,pow_add,pow_succ]
  field_simp
  ring

lemma weighted_cost_bounds_count (L h N n z : ℕ) (hN : 0 < N) (ω : Fin (L+1) → Bool)
    (hcost : tripleWeight h N*matchingPoly (triples L N n z) coords (tilt N)
      (fun i ↦ bit (ω i)) < 1) :
    (realized (triples L N n z) coords ω).card ≤ 36*(h+4) := by
  let k := 4*(h+4)
  have ht := tilt_pos hN
  have he : tripleWeight h N*Real.exp (tilt N*(k : ℝ)) = 1 := by
    rw [tripleWeight,← Real.exp_add]
    dsimp only [tilt,k]
    push_cast
    rw [show -((h : ℝ)+4)*Real.log ((N : ℝ)+1)+
        Real.log ((N : ℝ)+1)/4*(4*(h+4)) = 0 by ring,Real.exp_zero]
  have hp : matchingPoly (triples L N n z) coords (tilt N) (fun i ↦ bit (ω i)) <
      Real.exp (tilt N*(k : ℝ)) := by
    exact lt_of_mul_lt_mul_left (by rwa [he]) (tripleWeight_pos h N).le
  have hp' := hp.trans_le (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ (k : ℝ)+1 by linarith) ht.le))
  have hdeg : ∀ e ∈ triples L N n z,
      ((triples L N n z).filter (fun f ↦ ¬ Disjoint (coords e) (coords f))).card ≤ 9 := by
    intro e he
    exact conflict_card L N n z e
  have hh := matchingPoly_bounds_realized (triples L N n z) coords 9 k
    (fun e he ↦ coords_nonempty e) (by
      intro e he
      convert hdeg e he using 1
      congr 1
      ext f
      simp only [Finset.mem_filter]) (tilt N) ht ω hp'
  trace_state
  dsimp only [k] at hh
  omega

end Erdos66TripleIntersectionPotential
