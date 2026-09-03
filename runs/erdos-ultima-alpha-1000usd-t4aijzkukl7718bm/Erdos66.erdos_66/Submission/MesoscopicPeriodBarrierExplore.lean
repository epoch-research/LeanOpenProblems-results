import Submission.RepeatedPeriodBarrierExplore

/-! Clipped periodic pieces in shrinking windows still impose a product-period
resolution cost. This restricts complete-product-period averaging, not
incomplete-period cancellation or arbitrary constructions. -/
namespace Erdos66MesoscopicPeriodBarrier
open Filter AdditiveCombinatorics Erdos66Explore Erdos66RepeatedPeriodBarrier
open scoped Topology Classical
set_option maxHeartbeats 1600000

/-- A single completely retained residue class in a clipped window suffices.
The window may be much shorter than its location. -/
theorem clipped_period_bound {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ N₀ : ℕ, ∀ N≥N₀, ∀ W d r : ℕ,
      W≤N → 0<d → r<d →
      (∀ n, N≤n → n<N+W → n%d=r → n∈A) →
      (W:ℝ)≤((c+1)*Real.log (6*(N:ℝ))+2)*d := by
  obtain ⟨N₀,hbound⟩ := progression_length_bound h
  refine ⟨max N₀ 1,fun N hN W d r hWN hd hr hA ↦ ?_⟩
  have hN1 : 1≤N := by omega
  have hX : 0≤(c+1)*Real.log (6*(N:ℝ)) := by
    apply mul_nonneg (by linarith [limit_nonneg h])
    apply Real.log_nonneg
    have hNr : (1:ℝ)≤N := by exact_mod_cast hN1
    linarith
  by_cases hsmall : W<2*d
  · have hs : (W:ℝ)≤2*(d:ℝ) := by exact_mod_cast hsmall.le
    have hm := mul_nonneg hX (Nat.cast_nonneg (α:=ℝ) d)
    nlinarith
  have hWd : 2*d≤W := by omega
  let a := (N/d+1)*d+r
  have hrem : d*(N/d)+N%d=N := Nat.div_add_mod N d
  have hrem_lt := Nat.mod_lt N hd
  have hrem0 := Nat.zero_le (N%d)
  have ha : N≤a := by dsimp [a]; nlinarith
  have ha2 : a<N+2*d := by dsimp [a]; nlinarith
  have haW : a<N+W := by omega
  have hamod : a%d=r := by simp [a,Nat.add_mod, Nat.mod_eq_of_lt hr]
  let T := N+W-1-a
  let K := T/d
  have hT : T+a+1=N+W := by dsimp [T]; omega
  have hdecomp : d*K+T%d=T := Nat.div_add_mod T d
  have hmod := Nat.mod_lt T hd
  have hmod0 := Nat.zero_le (T%d)
  have hspan : d*(K+1)≤2*N := by nlinarith
  have hwidth : W≤d*(K+3) := by nlinarith
  have hp : ∀ j≤K, a+d*j∈A := by
    intro j hj
    have hmul := Nat.mul_le_mul_left d hj
    apply hA (a+d*j) (by omega) (by nlinarith)
    simpa [Nat.add_mod] using hamod
  have hlen := hbound N (by omega) a d K hd ha (by omega) hspan hp
  have hw : (W:ℝ)≤(d:ℝ)*((K:ℝ)+3) := by exact_mod_cast hwidth
  have hm := mul_le_mul_of_nonneg_right hlen (Nat.cast_nonneg (α:=ℝ) d)
  nlinarith

lemma product_resolution_bound (w d e X : ℝ) (hw : 0<w) (hd : 0<d) (he : 0<e)
    (hX : 0≤X) (hwd : w≤X*d) (hwe : w≤X*e) :
    w/(d*e)≤X^2/w := by
  have hp := mul_le_mul hwd hwe hw.le (mul_nonneg hX hd.le)
  apply (div_le_div_iff₀ (mul_pos hd he) hw).mpr
  nlinarith

/-- In windows W much longer than log(N)^2, the window/product-period ratio
vanishes. Both patterns are merely clipped, not retained outside the window.
Coprimality is unnecessary for the product bound; it is needed to identify
that product with the CRT period. -/
theorem clipped_window_div_product_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (N W d e r s : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hwindow : Tendsto (fun j ↦ (Real.log (6*(N j:ℝ)))^2/(W j:ℝ)) atTop (𝓝 0))
    (hdata : ∀ᶠ j in atTop, W j≤N j ∧ 0<d j ∧ r j<d j ∧ 0<e j ∧ s j<e j ∧
      (∀ n, N j≤n → n<N j+W j → n%d j=r j → n∈A) ∧
      (∀ n, N j≤n → n<N j+W j → n%e j=s j → n∈A)) :
    Tendsto (fun j ↦ (W j:ℝ)/((d j:ℝ)*(e j:ℝ))) atTop (𝓝 0) := by
  obtain ⟨N₀,hbound⟩ := clipped_period_bound h
  have hc : 0≤c := limit_nonneg h
  have hlog := Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop (by norm_num : (0:ℝ)<6))
  have hupper : Tendsto (fun j ↦ (c+3)^2*((Real.log (6*(N j:ℝ)))^2/(W j:ℝ)))
      atTop (𝓝 0) := by simpa using hwindow.const_mul ((c+3)^2)
  refine squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) ?_ hupper
  filter_upwards [hdata,hN.eventually_ge_atTop N₀,hlog.eventually_ge_atTop 1]
    with j hj hNj hlogj
  obtain ⟨hWN,hd,hr,he,hs,hA,hB⟩ := hj
  by_cases hW : W j=0
  · simp [hW]
  have hwp : (0:ℝ)<W j := by exact_mod_cast (show 0<W j by omega)
  have hdp : (0:ℝ)<d j := by exact_mod_cast hd
  have hep : (0:ℝ)<e j := by exact_mod_cast he
  have h₁ := hbound (N j) hNj (W j) (d j) (r j) hWN hd hr hA
  have h₂ := hbound (N j) hNj (W j) (e j) (s j) hWN he hs hB
  change 1≤Real.log (6*(N j:ℝ)) at hlogj
  let X := (c+1)*Real.log (6*(N j:ℝ))+2
  have hX : 0≤X := by dsimp [X]; positivity
  have hXupper : X≤(c+3)*Real.log (6*(N j:ℝ)) := by dsimp [X]; nlinarith
  have hsquare : X^2≤(c+3)^2*(Real.log (6*(N j:ℝ)))^2 := by
    have hh := pow_le_pow_left₀ hX hXupper 2
    simpa only [mul_pow] using hh
  have hh := product_resolution_bound (W j) (d j) (e j) X hwp hdp hep hX h₁ h₂
  have hdiv := div_le_div_of_nonneg_right hsquare hwp.le
  exact hh.trans (by simpa only [mul_div_assoc] using hdiv)

/-- An explicit shrinking window: position N=j^2 and width W=j. -/
lemma square_scale_log_window_zero :
    Tendsto (fun j : ℕ ↦ (Real.log (6*((j^2:ℕ):ℝ)))^2/(j:ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun j : ℕ ↦ 4*((Real.log (6*(j:ℝ)))^2/(j:ℝ))) atTop (𝓝 0) := by
    simpa using log_six_square_div_limit.const_mul 4
  refine squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) ?_ hu
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hjr : (1:ℝ)≤j := by exact_mod_cast hj
  have hl0 : 0≤Real.log (6*(j:ℝ)^2) := Real.log_nonneg (by nlinarith)
  have hl : Real.log (6*(j:ℝ)^2)≤2*Real.log (6*(j:ℝ)) := by
    have hh := Real.log_le_log (by nlinarith : (0:ℝ)<6*(j:ℝ)^2)
      (show 6*(j:ℝ)^2≤(6*(j:ℝ))^2 by nlinarith [sq_nonneg (j:ℝ)])
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hs := pow_le_pow_left₀ hl0 hl 2
  push_cast
  have hd := div_le_div_of_nonneg_right hs (by positivity : (0:ℝ)≤j)
  convert hd using 1 <;> ring


/-- The product eventually exceeds every fixed multiple of the window.
For coprime periods this is the same assertion for their common CRT period. -/
theorem clipped_no_complete_product_average {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (N W d e r s : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hwindow : Tendsto (fun j ↦ (Real.log (6*(N j:ℝ)))^2/(W j:ℝ)) atTop (𝓝 0))
    (hdata : ∀ᶠ j in atTop, W j≤N j ∧ 0<d j ∧ r j<d j ∧ 0<e j ∧ s j<e j ∧
      (∀ n, N j≤n → n<N j+W j → n%d j=r j → n∈A) ∧
      (∀ n, N j≤n → n<N j+W j → n%e j=s j → n∈A)) (R : ℕ) :
    ∀ᶠ j in atTop, R*W j<d j*e j := by
  have hl := clipped_window_div_product_zero h N W d e r s hN hwindow hdata
  have hRp : (0:ℝ)<(R:ℝ)+1 := by positivity
  filter_upwards [hdata,hl.eventually_lt_const (by positivity : (0:ℝ)<1/((R:ℝ)+1))]
    with j hj hratio
  have hdp : (0:ℝ)<d j := by exact_mod_cast hj.2.1
  have hep : (0:ℝ)<e j := by exact_mod_cast hj.2.2.2.1
  have hh := (div_lt_div_iff₀ (mul_pos hdp hep) hRp).mp hratio
  have hineq : (R:ℝ)*(W j:ℝ)<(d j:ℝ)*(e j:ℝ) := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) (W j)]
  exact_mod_cast hineq

/-- Full repetitions clipped to [j^2,j^2+j) still cannot be mixed by
averaging a complete product period, although the relative window width
j/j^2 tends to zero. -/
theorem square_scale_clipped_product_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (d e r s : ℕ → ℕ)
    (hdata : ∀ᶠ j in atTop, 0<d j ∧ r j<d j ∧ 0<e j ∧ s j<e j ∧
      (∀ n, j^2≤n → n<j^2+j → n%d j=r j → n∈A) ∧
      (∀ n, j^2≤n → n<j^2+j → n%e j=s j → n∈A)) :
    Tendsto (fun j : ℕ ↦ (j:ℝ)/((d j:ℝ)*(e j:ℝ))) atTop (𝓝 0) := by
  have hN : Tendsto (fun j : ℕ ↦ j^2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with j hj
    have hj1 : 1≤j := by omega
    have hjb : b≤j := by omega
    nlinarith
  apply clipped_window_div_product_zero h (fun j ↦ j^2) id d e r s hN
    square_scale_log_window_zero
  filter_upwards [hdata,eventually_ge_atTop 1] with j hj hj1
  exact ⟨by dsimp; nlinarith,hj⟩

end Erdos66MesoscopicPeriodBarrier
