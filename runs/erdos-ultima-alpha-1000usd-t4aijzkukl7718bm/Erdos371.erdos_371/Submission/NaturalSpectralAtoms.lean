import Submission.StableLocalCovarianceFourier

/-! Irrational atoms are excluded from any natural covariance spectral limit
of a bounded fixed-prime-stable family. This is one-coordinate spectral
information, not natural adjacent order cancellation. -/
namespace Erdos371
open Finset Filter Complex MeasureTheory DilationSpectrum
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma strictMono_growing_extension (D H : ℕ → ℕ) (hD : StrictMono D)
    (hH : Tendsto H atTop atTop) :
    ∃ G : ℕ → ℕ, Tendsto G atTop atTop ∧ ∀ j, G (D j)=H j := by
  let J (N : ℕ) := Nat.findGreatest (fun j => D j≤N) N
  have hJ : Tendsto J atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (D j)] with N hN
    exact Nat.le_findGreatest ((hD.id_le j).trans hN) hN
  have hJD (j : ℕ) : J (D j)=j := by
    apply le_antisymm
    · apply hD.le_iff_le.mp
      exact Nat.findGreatest_spec (P := fun k => D k≤D j) (m := j) (hD.id_le j) (le_refl (D j))
    · exact Nat.le_findGreatest (hD.id_le j) (le_refl (D j))
  exact ⟨H ∘ J,hH.comp hJ,fun j => by simp only [Function.comp_apply,hJD]⟩

lemma joint_limit_of_growing_graphs {X : Type*} [PseudoMetricSpace X]
    (F : ℕ → ℕ → X) (z : X)
    (h : ∀ H : ℕ → ℕ, Tendsto H atTop atTop → Tendsto (fun N => F N (H N)) atTop (𝓝 z)) :
    Tendsto (fun NH : ℕ×ℕ => F NH.1 NH.2) atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hh
  push_neg at hh
  have hb (j : ℕ) : ∃ N H : ℕ, j≤N ∧ j≤H ∧ ε≤dist (F N H) z := by
    obtain ⟨⟨N,H⟩,hNH,hbad⟩ := hh (j,j)
    exact ⟨N,H,hNH.1,hNH.2,hbad⟩
  choose N H hN hH hbad using hb
  have htN : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  have htH : Tendsto H atTop atTop := tendsto_atTop_mono hH tendsto_id
  obtain ⟨φ,hφ,hNφ⟩ := strictMono_subseq_of_tendsto_atTop htN
  obtain ⟨G,hG,he⟩ := strictMono_growing_extension (N ∘ φ) (H ∘ φ) hNφ (htH.comp hφ.tendsto_atTop)
  have hg := (h G hG).comp (htN.comp hφ.tendsto_atTop)
  have he' (j : ℕ) : G (N (φ j))=H (φ j) := he j
  have hl : Tendsto (fun j => F (N (φ j)) (H (φ j))) atTop (𝓝 z) := by
    simpa only [Function.comp_def,he'] using hg
  obtain ⟨j,hj⟩ := ((Metric.tendsto_nhds.mp hl) ε hε).exists
  exact (hbad (φ j)).not_gt hj

lemma row_limit_of_joint_limit {X : Type*} [PseudoMetricSpace X]
    (F : ℕ → ℕ → X) (z : X)
    (hF : Tendsto (fun NH : ℕ×ℕ => F NH.1 NH.2) atTop (𝓝 z))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (c : ℕ → X)
    (hc : ∀ H, Tendsto (fun j => F (D j) H) atTop (𝓝 (c H))) :
    Tendsto c atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨⟨N₀,H₀⟩,hh⟩ := (Metric.tendsto_atTop.mp hF) (ε/2) (by positivity)
  refine ⟨H₀,fun H hH => ?_⟩
  have hb : dist (c H) z≤ε/2 := by
    apply le_of_tendsto ((hc H).dist (tendsto_const_nhds (x := z)))
    filter_upwards [hD.eventually_ge_atTop N₀] with j hj
    exact (hh (D j,H) ⟨hj,hH⟩).le
  linarith

lemma stable_localCovarianceFourierMean_joint_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N n, |f N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun NH : ℕ×ℕ => localCovarianceFourierMean NH.1 NH.2 (f NH.1) x) atTop (𝓝 0) :=
  joint_limit_of_growing_graphs (fun N H => localCovarianceFourierMean N H (f N) x) 0 (fun H hH => stable_localCovarianceFourierMean_zero f hf hd H hH x hx)

lemma fourierAverage_integral_linear_atom (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (x : UnitAddCircle) :
    Tendsto (fun H => ∫ y, fourierAverage H (y-x) ∂σ) atTop (𝓝 ((σ.real {x} : ℝ) : ℂ)) := by
  have hm (H : ℕ) : AEStronglyMeasurable (fun y => fourierAverage H (y-x)) σ :=
    ((continuous_fourierAverage H).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hb (H : ℕ) : ∀ᵐ y ∂σ, ‖fourierAverage H (y-x)‖≤(1 : ℝ) :=
    Eventually.of_forall (fun y => fourierAverage_norm_le H (y-x))
  have ht : ∀ᵐ y ∂σ, Tendsto (fun H => fourierAverage H (y-x)) atTop
      (𝓝 (({x} : Set UnitAddCircle).indicator (fun _ => (1 : ℂ)) y)) := by
    filter_upwards [] with y
    by_cases he : y=x
    · subst y
      simpa only [sub_self,fourierAverage_zero,Set.indicator_of_mem (Set.mem_singleton x)] using
        (tendsto_const_nhds (x := (1 : ℂ)))
    · simpa only [Set.indicator_of_notMem (show y∉({x} : Set UnitAddCircle) from he)] using
        fourierAverage_tendsto_zero (sub_ne_zero.mpr he)
  have hz := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1) hb ht
  simpa only [integral_indicator_const (1 : ℂ) (measurableSet_singleton x),Complex.real_smul,mul_one] using hz

lemma integral_fourierAverage_shift (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (x : UnitAddCircle) (H : ℕ) :
    (∫ y, fourierAverage H (y-x) ∂σ) =
      (∑ h ∈ range (H+1), (∫ y, fourier (h : ℤ) y ∂σ)*fourier (-(h : ℤ)) x)/(H+1 : ℂ) := by
  have he (y : UnitAddCircle) : fourierAverage H (y-x) =
      (∑ h ∈ range (H+1), fourier (h : ℤ) (y-x))/(H+1 : ℂ) := by
    unfold fourierAverage
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun h : ℕ => fourier (h : ℤ) (y-x)) (H+1)
  simp_rw [he]
  have hi (h : ℕ) : Integrable (fun y : UnitAddCircle => fourier (h : ℤ) (y-x)) σ :=
    (((fourier (h : ℤ)).continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  rw [integral_div,integral_finset_sum _ (fun h _ => hi h)]
  congr 1
  apply sum_congr rfl
  intro h _
  simp_rw [fourier_sub_argument,← fourier_neg]
  rw [integral_mul_const]

/-- Any natural covariance spectral limit of a stable family has no
irrational atom. The covariance limits may be taken along ANY subsequence
whose endpoints tend to infinity. No natural density is assumed to exist. -/
theorem natural_covariance_spectral_no_infinite_order_atoms
    (f : ℕ → ℕ → ℝ) (hf : ∀ N n, |f N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hc : ∀ h : ℕ, Tendsto (fun j =>
      (((∑ n ∈ range (D j), f (D j) (n+1)*f (D j) (n+1+h))/(D j : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (∫ y, fourier (h : ℤ) y ∂σ))) :
    ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → σ {x}=0 := by
  intro x hx
  let c (H : ℕ) :=
    (∑ h ∈ range H, (∫ y, fourier (h : ℤ) y ∂σ)*fourier (-(h : ℤ)) x)/(H : ℂ)
  have hrows (H : ℕ) : Tendsto (fun j => localCovarianceFourierMean (D j) H (f (D j)) x)
      atTop (𝓝 (c H)) := by
    have h := (tendsto_finset_sum (range H) (fun h _ => (hc h).mul_const (fourier (-(h : ℤ)) x))).div_const (H : ℂ)
    simpa only [localCovarianceFourierMean_expansion,c] using h
  have ht := row_limit_of_joint_limit (fun N H => localCovarianceFourierMean N H (f N) x) 0
    (stable_localCovarianceFourierMean_joint_zero f hf hd x hx) D hD c hrows
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  have he (H : ℕ) : c (H+1) = ∫ y, fourierAverage H (y-x) ∂σ := by
    rw [integral_fourierAverage_shift]
    simp only [c,Nat.cast_add,Nat.cast_one]
  simp only [Function.comp_def,he] at ht'
  have hz := tendsto_nhds_unique ht' (fourierAverage_integral_linear_atom σ x)
  have hreal : σ.real {x}=0 := by exact_mod_cast hz.symm
  exact ((ENNReal.toReal_eq_zero_iff (σ {x})).mp hreal).resolve_right (measure_ne_top σ {x})

/-- Application to actual largest prime factors, uniformly in bounded
endpoint-dependent real prime weights. This does not assert two-coordinate
order symmetry or existence of all natural covariance limits. -/
theorem maxPrimeFac_natural_spectral_no_infinite_order_atoms
    (g : ℕ → ℕ → ℝ) (hg : ∀ N p, |g N p|≤1)
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hc : ∀ h : ℕ, Tendsto (fun j =>
      (((∑ n ∈ range (D j), g (D j) (Nat.maxPrimeFac (n+1))*
        g (D j) (Nat.maxPrimeFac (n+1+h)))/(D j : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (∫ y, fourier (h : ℤ) y ∂σ))) :
    ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → σ {x}=0 :=
  natural_covariance_spectral_no_infinite_order_atoms
    (fun N n => g N (Nat.maxPrimeFac n)) (fun N _ => hg N _)
    (fun p hp => maxPrimeFac_moving_weight_dilation_zero g hg p hp.pos) D hD σ hc


#print axioms joint_limit_of_growing_graphs
#print axioms natural_covariance_spectral_no_infinite_order_atoms
#print axioms maxPrimeFac_natural_spectral_no_infinite_order_atoms
end Erdos371
