import Submission.ContinuousIntervalUpperFreezing
import Submission.EulerMassScaling

/-! Exact prefix accounting and logarithmic-sector lower costs for the
ordinary interval envelope. These do not assert a Jacobsthal lower bound. -/
namespace Erdos970.ContinuousInterval
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1500000

lemma envelope_positive_tail_cost (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (m n : ℕ) (hmn : m ≤ n)
    (x : ℝ) (hx : 0 ≤ x) (hp : 0 < (envelope q n x).1) :
    (∑ i ∈ Ico m n, (envelope q i (1+(x-1)*q i)).2) < density q m*x := by
  have he (i : ℕ) (hi : i ∈ Ico m n) :
      (envelope q i (1+(x-1)*q i)).2 =
        (envelope q i x).1-(envelope q (i+1) x).1 := by
    have hh := hp.trans_le (envelope_lower_antitone q hq x hx
      (show i+1 ≤ n by have := (mem_Ico.mp hi).2; omega))
    change 0 < max 0 ((envelope q i (max 0 x)).1-
      (envelope q i (1+(max 0 x-1)*q i)).2) at hh
    rw [max_eq_right hx] at hh
    have hpos := (lt_max_iff.mp hh).resolve_left (lt_irrefl 0)
    change _ = (envelope q i x).1-max 0 ((envelope q i (max 0 x)).1-
      (envelope q i (1+(max 0 x-1)*q i)).2)
    rw [max_eq_right hx,max_eq_right hpos.le]
    ring
  have hs : (∑ i ∈ Ico m n, (envelope q i (1+(x-1)*q i)).2) =
      (envelope q m x).1-(envelope q n x).1 := by
    simp_rw [sum_congr rfl he]
    have ht := sum_Ico_sub (fun i => (envelope q i x).1) hmn
    have hh : (∑ i ∈ Ico m n, ((envelope q i x).1-(envelope q (i+1) x).1)) =
        -(∑ i ∈ Ico m n, ((envelope q (i+1) x).1-(envelope q i x).1)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hh,ht]
    ring
  have hr := envelope_regular q m (fun i _ => hq i)
  have hb := hr.lower_lip 0 x hx
  rw [hr.lower_zero 0 le_rfl,sub_zero,sub_zero] at hb
  rw [hs]
  linarith

lemma primeCounting_prefix_image (n : ℕ) :
    (range n.primeCounting).image (Nat.nth Nat.Prime) = (n+1).primesBelow := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    refine Nat.mem_primesBelow.mpr ⟨?_,Nat.prime_nth_prime i⟩
    exact Nat.nth_lt_of_lt_count (mem_range.mp hi)
  · intro hp
    obtain ⟨hpn,hpp⟩ := Nat.mem_primesBelow.mp hp
    refine mem_image.mpr ⟨Nat.count Nat.Prime p,mem_range.mpr ?_,Nat.nth_count hpp⟩
    apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mpr
    simpa only [Nat.nth_count hpp] using hpn

lemma reference_density_primeCounting (n : ℕ) :
    density (fun i => (referenceMarginal i : ℝ)) n.primeCounting =
      1/initialEulerMass n := by
  rw [initialEulerMass,inverse_eulerMass,← primeCounting_prefix_image]
  rw [prod_image (Nat.nth_strictMono Nat.infinite_setOf_prime).injective.injOn]
  simp [density,referenceMarginal]

lemma primeCounting_prefix_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n.primeCounting, f (Nat.nth Nat.Prime i)) =
      ∑ p ∈ (n+1).primesBelow, f p := by
  rw [← primeCounting_prefix_image,
    sum_image (Nat.nth_strictMono Nat.infinite_setOf_prime).injective.injOn]

lemma primeCounting_interval_sum (f : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ i ∈ Ico m.primeCounting n.primeCounting, f (Nat.nth Nat.Prime i)) =
      ∑ p ∈ Ioc m n with p.Prime, f p := by
  rw [sum_Ico_eq_sub _ (Nat.monotone_primeCounting hmn),
    primeCounting_prefix_sum,primeCounting_prefix_sum,initial_prime_sum_difference f m n hmn]

noncomputable def referenceUpperCost (x : ℝ) (p : ℕ) : ℝ :=
  (envelope (fun i => (referenceMarginal i : ℝ)) p.primeCounting'
    (1+(x-1)/(p : ℝ))).2

lemma referenceUpperCost_nth (x : ℝ) (i : ℕ) :
    referenceUpperCost x (Nat.nth Nat.Prime i) =
      (envelope (fun i => (referenceMarginal i : ℝ)) i
        (1+(x-1)*(referenceMarginal i : ℝ))).2 := by
  simp [referenceUpperCost,Nat.primeCounting'_nth_eq,referenceMarginal,div_eq_mul_inv]

lemma reference_positive_prime_tail_cost (m n : ℕ) (hmn : m ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hp : 0 < (envelope (fun i => (referenceMarginal i : ℝ)) n.primeCounting x).1) :
    (∑ p ∈ Ioc m n with p.Prime, referenceUpperCost x p) < x/initialEulerMass m := by
  rw [← primeCounting_interval_sum _ m n hmn]
  simp_rw [referenceUpperCost_nth]
  have hh := envelope_positive_tail_cost _ referenceMarginal_real_bounds
    m.primeCounting n.primeCounting (Nat.monotone_primeCounting hmn) x hx hp
  rw [reference_density_primeCounting] at hh
  convert hh using 1 <;> ring

lemma eventually_reciprocal_sector_lower (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b ≤ 1) :
    ∀ᶠ L : ℝ in atTop, (b-a)/2 ≤
      WeightedMertens.reciprocalInterval (exp (a*L)) (exp (b*L)) := by
  let E := 2*(WeightedMertens.boundConstant+1)
  have hab0 : 0 < b-a := sub_pos.mpr hab
  have hb0 : 0 < b := ha.trans hab
  have hmain : b-a ≤ log b-log a := by
    have hh := one_sub_inv_le_log_of_pos (div_pos hb0 ha)
    rw [log_div hb0.ne' ha.ne'] at hh
    have he : (b/a)⁻¹=a/b := by field_simp
    rw [he] at hh
    have hrat : b-a ≤ 1-a/b := by
      have haux : (b-a)*b ≤ b-a := mul_le_of_le_one_right hab0.le hb
      have heq : (1-a/b)*b=b-a := by field_simp
      nlinarith only [haux,heq,hb0]
    exact hrat.trans hh
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (log 2/a),eventually_ge_atTop (2*E/(a*(b-a)))] with L hL htwo herr
  have haL : 0 < a*L := mul_pos ha hL
  have hexp : 2 ≤ exp (a*L) := by
    rw [← exp_log (by norm_num : (0 : ℝ) < 2)]
    exact exp_le_exp.mpr ((div_le_iff₀ ha).mp htwo |>.trans_eq (mul_comm L a))
  have herror : E/(a*L) ≤ (b-a)/2 := by
    have hh := (div_le_iff₀ (mul_pos ha hab0)).mp herr
    apply (div_le_iff₀ haL).mpr
    nlinarith only [hh]
  have hh := (abs_le.mp (WeightedMertens.abs_reciprocalInterval_sub_loglog hexp
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab.le hL.le)))).1
  rw [log_exp,log_exp,log_mul hb0.ne' hL.ne',log_mul ha.ne' hL.ne'] at hh
  dsimp only [E] at herror
  linarith

/-- A single prime sector has a uniformly positive cost at exponential length.
The eventual threshold depends on the two fixed exponent parameters. -/
lemma eventually_referenceUpperCost_sector (a s : ℝ) (ha : 0 < a) (has : a < s) :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℕ, p.Prime → exp (a*L) < (p : ℝ) →
      exp (-WeightedMertens.reciprocalConstant-1)*exp (s*L)/(2*(s-a)*L)*(p : ℝ)⁻¹ ≤
        referenceUpperCost (exp (s*L)) p := by
  have hgap : 0 < s-a := sub_pos.mpr has
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (log 6/(s-a))] with L hL hlog
  intro p hp hpa
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let x := exp (s*L)
  let y := 1+(x-1)/(p : ℝ)
  let c := exp (-WeightedMertens.reciprocalConstant-1)
  have hc : 0 < c := exp_pos _
  have hx : 1 ≤ x := one_le_exp (mul_nonneg (ha.trans has).le hL.le)
  have hy : 0 ≤ y := by
    have hxm : 0 ≤ x-1 := sub_nonneg.mpr hx
    exact add_nonneg (by norm_num) (div_nonneg hxm hp0.le)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hylo : x/(p : ℝ) ≤ y := by
    dsimp only [y]
    apply (div_le_iff₀ hp0).mpr
    have he : (1+(x-1)/(p : ℝ))*(p : ℝ)=(p : ℝ)+x-1 := by field_simp; ring
    rw [he]
    linarith
  have hxy : x/(p : ℝ) ≤ exp ((s-a)*L) := by
    calc
      _ ≤ x/exp (a*L) := div_le_div_of_nonneg_left (by dsimp [x]; positivity)
        (exp_pos _) hpa.le
      _ = _ := by dsimp [x]; rw [← exp_sub]; congr 1; ring
  have hyhi : y ≤ 1+exp ((s-a)*L) := by
    dsimp only [y]
    have hh : (x-1)/(p : ℝ) ≤ x/(p : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hp0.le
    linarith
  have he1 : 1 ≤ exp ((s-a)*L) := one_le_exp (mul_nonneg hgap.le hL.le)
  have hroot : sqrt y ≤ y+1 := by
    have hh := sq_sqrt hy
    have hn := sqrt_nonneg y
    nlinarith [sq_nonneg (sqrt y-1)]
  have hsource := reference_upper_log_source p.primeCounting' y hy
  have hden0 : 0 < log (sqrt y+3) := log_pos (by have := sqrt_nonneg y; linarith)
  have hden : log (sqrt y+3) ≤ 2*(s-a)*L := by
    have hh : sqrt y+3 ≤ 6*exp ((s-a)*L) := by linarith
    have hl := log_le_log (by have := sqrt_nonneg y; positivity : 0 < sqrt y+3) hh
    rw [log_mul (by norm_num : (6 : ℝ) ≠ 0) (exp_ne_zero _),log_exp] at hl
    have hlog' := (div_le_iff₀ hgap).mp hlog
    nlinarith only [hl,hlog']
  have hden' : 0 < 2*(s-a)*L := by positivity
  have hh := div_le_div₀ (mul_nonneg hc.le hy)
    (mul_le_mul_of_nonneg_left hylo hc.le) hden0 hden
  change c*x/(2*(s-a)*L)*(p : ℝ)⁻¹ ≤ _
  apply le_trans _ hsource
  convert hh using 1 <;> dsimp only [c,x] <;> ring

#print axioms reference_positive_prime_tail_cost
#print axioms eventually_reciprocal_sector_lower
#print axioms eventually_referenceUpperCost_sector
end Erdos970.ContinuousInterval
