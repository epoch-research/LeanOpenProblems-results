import Submission.ContinuousIntervalSectorCosts

/-! A superlinear zero barrier for the ordinary reference envelope. The
statement concerns a lower-bound algorithm, not the actual Jacobsthal
function, and neither proves nor disproves its quadratic conjecture. -/
namespace Erdos970.ContinuousInterval
open Finset Real Filter FiniteSelberg
open scoped Topology
set_option maxHeartbeats 1800000

lemma eventually_initial_half_density : ∃ A > (0 : ℝ),
    ∀ᶠ L : ℝ in atTop, 1/initialEulerMass (expFloor (1/2) L) ≤ A/L := by
  obtain ⟨C,hC,hlim⟩ := exists_scaledEulerMass_limit
  refine ⟨4/C,by positivity,?_⟩
  have hh := (hlim (1/2) (by norm_num)).eventually
    (eventually_gt_nhds (show C/4 < C*(1/2) by linarith))
  filter_upwards [hh,eventually_gt_atTop (0 : ℝ)] with L hmass hL
  have hm := initialEulerMass_pos (expFloor (1/2) L)
  have hm' := (lt_div_iff₀ hL).mp hmass
  apply (div_le_div_iff₀ hm hL).mpr
  have he : (4/C)*(C/4*L)=L := by field_simp
  have hh := mul_le_mul_of_nonneg_left hm'.le (show 0 ≤ 4/C by positivity)
  simpa only [he,one_mul] using hh

lemma prime_annuli_telescope (a : ℕ → ℕ) (ha : Monotone a) (N : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range N, ∑ p ∈ Ioc (a j) (a (j+1)) with p.Prime, f p) =
      ∑ p ∈ Ioc (a 0) (a N) with p.Prime, f p := by
  have hh (j : ℕ) := initial_prime_sum_difference f (a j) (a (j+1)) (ha (by omega))
  simp_rw [← hh]
  rw [← initial_prime_sum_difference f (a 0) (a N) (ha (by omega))]
  simpa only [Nat.Ico_zero_eq_range] using
    sum_Ico_sub (fun j => ∑ p ∈ (a j+1).primesBelow, f p) (Nat.zero_le N)

noncomputable def barrierScale (j : ℕ) : ℝ := 1-(1/2 : ℝ)^(j+1)

lemma barrierScale_zero : barrierScale 0 = 1/2 := by norm_num [barrierScale]

lemma barrierScale_step (j : ℕ) :
    barrierScale (j+1)-barrierScale j=(1/2 : ℝ)^(j+2) := by
  simp only [barrierScale,pow_succ]
  ring

lemma barrierScale_strictMono : StrictMono barrierScale := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hh := barrierScale_step j
  have hp : 0 < (1/2 : ℝ)^(j+2) := by positivity
  linarith

lemma barrierScale_pos (j : ℕ) : 0 < barrierScale j := by
  have hh := barrierScale_strictMono.monotone (Nat.zero_le j)
  rw [barrierScale_zero] at hh
  linarith

lemma barrierScale_lt_one (j : ℕ) : barrierScale j < 1 := by
  have hp : 0 < (1/2 : ℝ)^(j+1) := by positivity
  dsimp only [barrierScale]
  linarith

lemma barrierScale_sector_ratio (N j : ℕ) (hj : j < N) :
    1+(1/2 : ℝ)^(N+1)-barrierScale j ≤
      3*(barrierScale (j+1)-barrierScale j) := by
  have hh : (1/2 : ℝ)^(N+1) ≤ (1/2 : ℝ)^(j+2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [barrierScale_step]
  dsimp only [barrierScale]
  rw [show j+2=(j+1)+1 by omega,pow_succ (1/2 : ℝ) (j+1)] at hh ⊢
  linarith

lemma eventually_reference_sector_cost_sum (a b s : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (has : a < s) :
    ∀ᶠ L : ℝ in atTop,
      exp (-WeightedMertens.reciprocalConstant-1)*exp (s*L)/(2*(s-a)*L)*((b-a)/2) ≤
        ∑ p ∈ Ioc (expFloor a L) (expFloor b L) with p.Prime,
          referenceUpperCost (exp (s*L)) p := by
  filter_upwards [eventually_reciprocal_sector_lower a b ha hab hb,
    eventually_referenceUpperCost_sector a s ha has,
    eventually_gt_atTop (0 : ℝ)] with L hmass hcost hL
  let F := exp (-WeightedMertens.reciprocalConstant-1)*exp (s*L)/(2*(s-a)*L)
  have hgap : 0 < s-a := sub_pos.mpr has
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hh := mul_le_mul_of_nonneg_left hmass hF
  change F*((b-a)/2) ≤ _
  apply hh.trans
  unfold WeightedMertens.reciprocalInterval
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
  exact hcost p hpp ((Nat.floor_lt (exp_pos _).le).mp (mem_Ioc.mp hpI).1)

lemma primeCounting_le_input (n : ℕ) : n.primeCounting ≤ n := by
  by_contra hh
  have hlt : n < Nat.count Nat.Prime (n+1) := by
    change n < n.primeCounting
    omega
  have hp := Nat.nth_lt_of_lt_count hlt
  have hb := Nat.add_two_le_nth_prime n
  omega

/-- Exponential-coordinate version of the barrier. Its exponent gap may be
very small, but is a single positive constant independent of the stage. -/
theorem exists_exponential_ordinary_zero_barrier : ∃ δ > (0 : ℝ),
    ∀ᶠ L : ℝ in atTop,
      (envelope (fun i => (referenceMarginal i : ℝ)) (expFloor 1 L)
        (exp ((1+δ)*L))).1 = 0 := by
  obtain ⟨A,hA,hprefix⟩ := eventually_initial_half_density
  let c := exp (-WeightedMertens.reciprocalConstant-1)
  have hc : 0 < c := exp_pos _
  obtain ⟨N,hN⟩ := exists_nat_gt (12*A/c)
  have hNc : 12*A < (N : ℝ)*c := (div_lt_iff₀ hc).mp hN
  let δ := (1/2 : ℝ)^(N+1)
  let s := 1+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hs (j : ℕ) : barrierScale j < s := by
    have hh := barrierScale_lt_one j
    dsimp only [s]
    linarith
  have hsectors : ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N,
      c*exp (s*L)/(2*(s-barrierScale j)*L)*
        ((barrierScale (j+1)-barrierScale j)/2) ≤
      ∑ p ∈ Ioc (expFloor (barrierScale j) L) (expFloor (barrierScale (j+1)) L)
        with p.Prime, referenceUpperCost (exp (s*L)) p := by
    apply (eventually_all_finset (range N)).mpr
    intro j hj
    exact eventually_reference_sector_cost_sum (barrierScale j) (barrierScale (j+1)) s
      (barrierScale_pos j) (barrierScale_strictMono (by omega))
      (barrierScale_lt_one (j+1)).le (hs j)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hsectors,hprefix,eventually_gt_atTop (0 : ℝ)] with L hsect hpref hL
  let x := exp (s*L)
  let a := fun j => expFloor (barrierScale j) L
  have hx : 0 < x := exp_pos _
  have ha : Monotone a := by
    intro i j hij
    exact Nat.floor_le_floor (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (barrierScale_strictMono.monotone hij) hL.le))
  have hbound : a N ≤ expFloor 1 L := Nat.floor_le_floor (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (barrierScale_lt_one N).le hL.le))
  have hindex := (primeCounting_le_input (a N)).trans hbound
  have hr := envelope_regular (fun i => (referenceMarginal i : ℝ)) (expFloor 1 L)
    (fun i _ => referenceMarginal_real_bounds i)
  apply le_antisymm _ (hr.lower_nonneg _)
  by_contra hh
  have hpos : 0 < (envelope (fun i => (referenceMarginal i : ℝ))
      (a N).primeCounting x).1 := by
    have hh' : 0 < (envelope (fun i => (referenceMarginal i : ℝ))
      (expFloor 1 L) x).1 := lt_of_not_ge hh
    exact hh'.trans_le (envelope_lower_antitone _ referenceMarginal_real_bounds x hx.le hindex)
  have htail := reference_positive_prime_tail_cost (a 0) (a N) (ha (by omega)) x hx.le hpos
  have hpf : x/initialEulerMass (a 0) ≤ A*x/L := by
    have hh := mul_le_mul_of_nonneg_right hpref hx.le
    dsimp only [a] at *
    rw [barrierScale_zero]
    convert hh using 1 <;> ring
  have hlow : (N : ℝ)*(c*x/(12*L)) ≤
      ∑ p ∈ Ioc (a 0) (a N) with p.Prime, referenceUpperCost x p := by
    rw [← prime_annuli_telescope a ha N]
    have hsumm : (∑ j ∈ range N, c*x/(12*L)) ≤
        ∑ j ∈ range N, ∑ p ∈ Ioc (a j) (a (j+1)) with p.Prime,
          referenceUpperCost x p := by
      apply sum_le_sum
      intro j hj
      apply le_trans _ (hsect j hj)
      have hratio := barrierScale_sector_ratio N j (mem_range.mp hj)
      have hg : 0 < s-barrierScale j := sub_pos.mpr (hs j)
      have hcx : 0 < c*x := mul_pos hc hx
      have he : c*x/(2*(s-barrierScale j)*L)*
          ((barrierScale (j+1)-barrierScale j)/2) =
          c*x*(barrierScale (j+1)-barrierScale j)/(4*(s-barrierScale j)*L) := by field_simp; ring
      change c*x/(12*L) ≤ c*x/(2*(s-barrierScale j)*L)*
        ((barrierScale (j+1)-barrierScale j)/2)
      rw [he]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      change s-barrierScale j ≤ 3*(barrierScale (j+1)-barrierScale j) at hratio
      have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4*(c*x)*L by positivity)
      nlinarith only [hm]
    simpa only [sum_const,card_range,nsmul_eq_mul] using hsumm
  have hlt : A*x/L < (N : ℝ)*(c*x/(12*L)) := by
    have hm := mul_lt_mul_of_pos_right hNc (div_pos hx (show 0 < 12*L by positivity))
    convert hm using 1 <;> field_simp
  exact (hlow.trans_lt (htail.trans_le hpf)).not_ge hlt.le

/-- A fixed superlinear power is still a zero region for the ordinary
reference lower envelope at all sufficiently large stages. This is NOT a
lower bound on the actual Jacobsthal function. -/
theorem exists_polynomial_ordinary_zero_barrier : ∃ δ > (0 : ℝ),
    ∀ᶠ k : ℕ in atTop,
      (envelope (fun i => (referenceMarginal i : ℝ)) k ((k : ℝ)^(1+δ))).1 = 0 := by
  obtain ⟨δ,hδ,hh⟩ := exists_exponential_ordinary_zero_barrier
  refine ⟨δ,hδ,?_⟩
  have ht := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hh,eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  simpa only [Function.comp_def,expFloor,one_mul,exp_log hk0,Nat.floor_natCast,
    rpow_def_of_pos hk0,mul_comm (log (k : ℝ)) (1+δ)] using hk

#print axioms exists_exponential_ordinary_zero_barrier
#print axioms exists_polynomial_ordinary_zero_barrier
end Erdos970.ContinuousInterval
