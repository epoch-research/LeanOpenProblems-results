import Submission.QuantitativeSmoothReciprocal

/-! Uniform upper bounds for the reciprocal mass of smooth integers beyond
an endpoint, and for the corresponding harmonic multiplier-defect tails.
No ordinary-density cancellation is asserted. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x-1 ≤ x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x) (Real.exp_nonneg x)
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at h
  nlinarith

lemma primeEulerFactor_below_one_comparison (p : ℕ) (hp : p.Prime)
    (d : ℝ) (hd : 0<d) (hd' : d≤1/2) :
    (1-(p : ℝ)^(-(1-d)))⁻¹ ≤
      (1-(p : ℝ)⁻¹)⁻¹ * Real.exp (4*d*Real.log p*(p : ℝ)^d/p) := by
  have hp1 : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ)<p := by linarith
  let x : ℝ := (p : ℝ)⁻¹
  let y : ℝ := (p : ℝ)^(-(1-d))
  have hx : 0≤x := by dsimp [x]; positivity
  have hx1 : x<1 := inv_lt_one_of_one_lt₀ hp1
  have hy : y≤3/4 := prime_neg_rpow_le_three_quarters p hp (1-d) (by linarith)
  have hxy : x≤y := by
    dsimp [x,y]
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hA : 0<1-x := by linarith
  have hB : 0<1-y := by linarith
  have hexact : (1-x)/(1-y) = 1+(y-x)/(1-y) := by field_simp; ring
  have hratio : (1-x)/(1-y) ≤ 1+4*(y-x) := by
    rw [hexact]
    apply add_le_add_right
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hrat : (1-x)/(1-y) ≤ Real.exp (4*(y-x)) := hratio.trans (by
    simpa only [add_comm] using Real.add_one_le_exp (4*(y-x)))
  have hdiff : y-x ≤ d*Real.log p*(p : ℝ)^d/p := by
    have hyid : y-x = ((p : ℝ)^d-1)/p := by
      dsimp [x,y]
      rw [show -(1-d)=d-1 by ring,Real.rpow_sub hp0,Real.rpow_one]
      ring
    rw [hyid]
    apply div_le_div_of_nonneg_right _ hp0.le
    rw [Real.rpow_def_of_pos hp0]
    have h := exp_sub_one_le_mul_exp (Real.log p*d)
    nlinarith
  have h := hrat.trans (Real.exp_le_exp.mpr (show 4*(y-x)≤4*d*Real.log p*(p : ℝ)^d/p by
    convert mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ)≤4) using 1; ring))
  change (1-y)⁻¹ ≤ (1-x)⁻¹ * _
  apply (le_inv_mul_iff₀ hA).mpr
  simpa only [div_eq_mul_inv] using h

lemma primeEulerProduct_below_one_comparison (B : ℕ) (hB : 1<B)
    (d : ℝ) (hd : 0<d) (hd' : d≤1/2) :
    (∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-(1-d)))⁻¹) ≤
      (∏ p ∈ B.primesBelow, (1-(p : ℝ)⁻¹)⁻¹) *
        Real.exp (16*d*(B : ℝ)^d*Real.log B) := by
  have hsum : (∑ p ∈ B.primesBelow, 4*d*Real.log p*(p : ℝ)^d/p) ≤
      16*d*(B : ℝ)^d*Real.log B := by
    calc
      _ ≤ ∑ p ∈ B.primesBelow, (4*d*(B : ℝ)^d)*(Real.log p/((p : ℝ)-1)) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpB,hp⟩ := Nat.mem_primesBelow.mp hp
        have hp1 : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
        have hp0 : (0 : ℝ)<p := by linarith
        have hlog : 0≤Real.log p := Real.log_nonneg hp1.le
        have hpow : (p : ℝ)^d≤(B : ℝ)^d :=
          Real.rpow_le_rpow hp0.le (by exact_mod_cast hpB.le) hd.le
        calc
          _ = (4*d*(p : ℝ)^d)*(Real.log p/p) := by ring
          _ ≤ (4*d*(B : ℝ)^d)*(Real.log p/((p : ℝ)-1)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hpow (by positivity)
            · exact div_le_div_of_nonneg_left hlog (by linarith) (by linarith)
            · positivity
            · positivity
      _ = (4*d*(B : ℝ)^d)*(∑ p ∈ B.primesBelow, Real.log p/((p : ℝ)-1)) := by
        rw [mul_sum]
      _ ≤ (4*d*(B : ℝ)^d)*(4*Real.log B) :=
        mul_le_mul_of_nonneg_left (prime_log_div_pred_sum_le B) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∏ p ∈ B.primesBelow,
        (1-(p : ℝ)⁻¹)⁻¹ * Real.exp (4*d*Real.log p*(p : ℝ)^d/p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h := prime_neg_rpow_le_three_quarters p (Nat.mem_primesBelow.mp hp).2 (1-d) (by linarith)
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact primeEulerFactor_below_one_comparison p (Nat.mem_primesBelow.mp hp).2 d hd hd'
    _ = (∏ p ∈ B.primesBelow, (1-(p : ℝ)⁻¹)⁻¹) *
        Real.exp (∑ p ∈ B.primesBelow, 4*d*Real.log p*(p : ℝ)^d/p) := by
      rw [prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum)
      apply prod_nonneg
      intro p hp
      have h : (p : ℝ)⁻¹<1 := inv_lt_one_of_one_lt₀
        (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt)
      exact inv_nonneg.mpr (by linarith)

noncomputable def smoothRpow (B : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ∈ (B+1).smoothNumbers then (n : ℝ)^(-s) else 0

lemma smoothRpow_nonneg (B : ℕ) (s : ℝ) (n : ℕ) : 0≤smoothRpow B s n := by
  unfold smoothRpow
  split_ifs <;> positivity

lemma smoothRpow_hasSum (B : ℕ) (s : ℝ) (hs : 0<s) :
    HasSum (smoothRpow B s)
      (∏ p ∈ (B+1).primesBelow, (1-(p : ℝ)^(-s))⁻¹) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖natNegRpowHom s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have he := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (B+1)).2
  change HasSum (fun n : (B+1).smoothNumbers => (n.val : ℝ)^(-s))
    (∏ p ∈ (B+1).primesBelow, (1-(p : ℝ)^(-s))⁻¹) at he
  have hi := (hasSum_subtype_iff_indicator (f := fun n : ℕ => (n : ℝ)^(-s))).mp he
  convert hi using 1
  funext n
  simp only [smoothRpow,Set.indicator]

noncomputable def smoothReciprocalTail (B N : ℕ) : ℝ :=
  ∑' n, if N≤n then smoothReciprocal B n else 0

lemma smoothReciprocalTail_summable (B N : ℕ) :
    Summable (fun n => if N≤n then smoothReciprocal B n else 0) := by
  convert (summable_smoothReciprocal B).indicator {n | N≤n} using 1
  funext n
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

lemma smoothReciprocalTail_rankin_bound (B N : ℕ) (hN : 0<N)
    (d : ℝ) (hd : 0<d) (hd' : d<1) :
    smoothReciprocalTail B N ≤ (N : ℝ)^(-d) *
      (∏ p ∈ (B+1).primesBelow, (1-(p : ℝ)^(-(1-d)))⁻¹) := by
  have he := smoothRpow_hasSum B (1-d) (by linarith)
  have hmajor (n : ℕ) : (if N≤n then smoothReciprocal B n else 0) ≤
      (N : ℝ)^(-d)*smoothRpow B (1-d) n := by
    by_cases hNn : N≤n
    · rw [if_pos hNn,smoothReciprocal,smoothRpow]
      split_ifs with hn
      · have hn0 : (0 : ℝ)<n := by exact_mod_cast hN.trans_le hNn
        have heq : (1 : ℝ)/n = (n : ℝ)^(-d)*(n : ℝ)^(-(1-d)) := by
          rw [← Real.rpow_add hn0,show -d + -(1-d) = (-1 : ℝ) by ring,Real.rpow_neg_one,one_div]
        rw [heq]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN)
          (by exact_mod_cast hNn) (by linarith)
      · simp
    · rw [if_neg hNn]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (smoothRpow_nonneg B (1-d) n)
  have h := Summable.tsum_le_tsum hmajor (smoothReciprocalTail_summable B N)
    (he.summable.mul_left ((N : ℝ)^(-d)))
  rw [he.summable.tsum_mul_left,he.tsum_eq] at h
  exact h

/-- The free-parameter reciprocal-tail estimate retains the Euler-product
mass at exponent one rather than replacing it by a much larger loss. -/
theorem smoothReciprocalTail_parameter_bound (B N : ℕ) (hB : 0<B) (hN : 0<N)
    (d : ℝ) (hd : 0<d) (hd' : d≤1/2) :
    smoothReciprocalTail B N ≤ (N : ℝ)^(-d) *
      (Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)) *
        Real.exp (16*d*(B+1 : ℝ)^d*Real.log (B+1 : ℝ)) := by
  have hc := primeEulerProduct_below_one_comparison (B+1) (by omega) d hd hd'
  have he := primeEulerProduct_le_log (B+1) (by omega)
  push_cast at hc he
  have hprod := hc.trans (mul_le_mul_of_nonneg_right he (Real.exp_nonneg _))
  exact (smoothReciprocalTail_rankin_bound B N hN d hd (by linarith)).trans
    ((mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq (by ring))

noncomputable def smoothTailExponent (B : ℕ) : ℝ :=
  Real.log 2/(32*Real.log (B+1 : ℝ))

lemma smoothTailExponent_bounds (B : ℕ) (hB : 0<B) :
    0<smoothTailExponent B ∧ smoothTailExponent B≤1/32 := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlB : Real.log 2≤Real.log (B+1 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤B+1 by omega))
  have hlB0 : 0<Real.log (B+1 : ℝ) := hl2.trans_le hlB
  constructor
  · unfold smoothTailExponent; positivity
  · unfold smoothTailExponent
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<32*Real.log (B+1 : ℝ))).mpr
    linarith

lemma smoothTailExponent_log (B : ℕ) (hB : 0<B) :
    smoothTailExponent B*Real.log (B+1 : ℝ) = Real.log 2/32 := by
  have hlB : 0<Real.log (B+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<B+1 by omega))
  unfold smoothTailExponent
  field_simp

lemma smoothTailExponent_euler_loss_le_two (B : ℕ) (hB : 0<B) :
    Real.exp (16*smoothTailExponent B*(B+1 : ℝ)^(smoothTailExponent B)*
      Real.log (B+1 : ℝ)) ≤ 2 := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (B+1 : ℝ)^(smoothTailExponent B) ≤ 2 := by
    rw [Real.rpow_def_of_pos (by positivity),mul_comm, smoothTailExponent_log B hB]
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have he : 16*smoothTailExponent B*(B+1 : ℝ)^(smoothTailExponent B)*
      Real.log (B+1 : ℝ) =
        (Real.log 2/2)*(B+1 : ℝ)^(smoothTailExponent B) := by
    calc
      _ = 16*(smoothTailExponent B*Real.log (B+1 : ℝ))*
          (B+1 : ℝ)^(smoothTailExponent B) := by ring
      _ = _ := by rw [smoothTailExponent_log B hB]; ring
  rw [he]
  calc
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- An explicit exponential decay in log N / log(B+1), with only a
logarithmic prefactor in B. Uniform in BOTH B and N. -/
theorem smoothReciprocalTail_uniform_bound (B N : ℕ) (hB : 0<B) (hN : 0<N) :
    smoothReciprocalTail B N ≤
      2*Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2) *
        Real.exp (-Real.log 2*Real.log N/(32*Real.log (B+1 : ℝ))) := by
  have hd := smoothTailExponent_bounds B hB
  have hlB : 0≤Real.log (B+1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) B; linarith)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hr := smoothReciprocalTail_parameter_bound B N hB hN (smoothTailExponent B)
    hd.1 (by linarith)
  have hu := hr.trans (mul_le_mul_of_nonneg_left (smoothTailExponent_euler_loss_le_two B hB)
    (by positivity))
  apply hu.trans_eq
  rw [Real.rpow_def_of_pos (by exact_mod_cast hN)]
  have he : Real.log N * (-smoothTailExponent B) =
      -Real.log 2*Real.log N/(32*Real.log (B+1 : ℝ)) := by
    unfold smoothTailExponent
    ring
  rw [he]
  ring

noncomputable def harmonicLabelDefectTail {A : Type*} (k N : ℕ) (L : ℕ → A) : ℝ :=
  ∑' n, if N≤n then ‖labelDilationDefect k L n/(n : ℝ)‖ else 0

lemma maxPrimeFac_harmonicLabelDefectTail_le {A : Type*} (g : ℕ → A)
    (k N : ℕ) (hk : 0<k) :
    harmonicLabelDefectTail k N (g ∘ Nat.maxPrimeFac) ≤ smoothReciprocalTail k N := by
  have hpoint (n : ℕ) : (if N≤n then
      ‖labelDilationDefect k (g ∘ Nat.maxPrimeFac) n/(n : ℝ)‖ else 0) ≤
        (if N≤n then smoothReciprocal k n else 0) := by
    split_ifs
    · exact maxPrimeFac_label_harmonic_defect_le g k n hk
    · rfl
  have hs := smoothReciprocalTail_summable k N
  exact Summable.tsum_le_tsum hpoint
    (Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpoint hs) hs

/-- Every relabelling of the actual largest-prime factor enjoys the same
uniform tail bound. This is a quantitative stability result, not adjacent
order-skew cancellation. -/
theorem maxPrimeFac_harmonicLabelDefectTail_uniform_bound {A : Type*} (g : ℕ → A)
    (k N : ℕ) (hk : 0<k) (hN : 0<N) :
    harmonicLabelDefectTail k N (g ∘ Nat.maxPrimeFac) ≤
      2*Real.exp 4*(1+Real.log (k+1 : ℝ)/Real.log 2) *
        Real.exp (-Real.log 2*Real.log N/(32*Real.log (k+1 : ℝ))) :=
  (maxPrimeFac_harmonicLabelDefectTail_le g k N hk).trans
    (smoothReciprocalTail_uniform_bound k N hk hN)

/-- A stronger, free-scale tail estimate in the range where the optimizing
Rankin exponent remains at most 1/2. The constants are intentionally coarse.
Here u = log N / log(B+1). This is a smooth-number estimate only. -/
theorem smoothReciprocalTail_large_u_bound (B N : ℕ) (hB : 0<B) (hN : 0<N)
    (u : ℝ) (hu : 1024≤u)
    (hscale : u*Real.log (B+1 : ℝ)=Real.log N)
    (hrange : Real.log u≤4*Real.log (B+1 : ℝ)) :
    smoothReciprocalTail B N ≤
      Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)*Real.exp (-u*Real.log u/16) := by
  have hu0 : 0<u := by linarith
  have hu1 : 1≤u := by linarith
  have hlu : 0<Real.log u := Real.log_pos (by linarith)
  have hlB : 0<Real.log (B+1 : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1<B+1 by omega))
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let d : ℝ := Real.log u/(8*Real.log (B+1 : ℝ))
  have hd : 0<d := by dsimp [d]; positivity
  have hd' : d≤1/2 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<8*Real.log (B+1 : ℝ))).mpr
    linarith
  have hdlog : d*Real.log (B+1 : ℝ)=Real.log u/8 := by
    dsimp [d]
    field_simp
  have hpow : (B+1 : ℝ)^d ≤ u/32 := by
    calc
      _ = u^(1/8 : ℝ) := by
        rw [Real.rpow_def_of_pos (by positivity),Real.rpow_def_of_pos hu0]
        congr 1
        have h := hdlog
        linarith
      _ ≤ u^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = Real.sqrt u := (Real.sqrt_eq_rpow u).symm
      _ ≤ u/32 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith
  have hgain : 16*d*(B+1 : ℝ)^d*Real.log (B+1 : ℝ) ≤ u*Real.log u/16 := by
    calc
      _ = 2*Real.log u*(B+1 : ℝ)^d := by
        calc
          _ = 16*(d*Real.log (B+1 : ℝ))*(B+1 : ℝ)^d := by ring
          _ = _ := by rw [hdlog]; ring
      _ ≤ 2*Real.log u*(u/32) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hNlog : d*Real.log N=u*Real.log u/8 := by
    rw [← hscale]
    calc
      _ = u*(d*Real.log (B+1 : ℝ)) := by ring
      _ = _ := by rw [hdlog]; ring
  have hr := smoothReciprocalTail_parameter_bound B N hB hN d hd hd'
  have he : (N : ℝ)^(-d) *
      (Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)) *
        Real.exp (16*d*(B+1 : ℝ)^d*Real.log (B+1 : ℝ)) =
      (Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)) *
        Real.exp (-d*Real.log N+16*d*(B+1 : ℝ)^d*Real.log (B+1 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hN),Real.exp_add]
    have hx : Real.log N*(-d)= -d*Real.log N := by ring
    rw [hx]
    ring
  rw [he] at hr
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_mul,hNlog]
  linarith

#print axioms smoothReciprocalTail_large_u_bound
#print axioms smoothReciprocalTail_parameter_bound
#print axioms smoothReciprocalTail_uniform_bound
#print axioms maxPrimeFac_harmonicLabelDefectTail_uniform_bound
end Erdos371
