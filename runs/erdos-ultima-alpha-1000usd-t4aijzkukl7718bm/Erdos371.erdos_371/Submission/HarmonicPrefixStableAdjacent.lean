import Submission.HarmonicPrefixFloorReindex
import Submission.PrefixEnergyIdentity

/-! Mean-stable labels transfer to their actual shorter adjacent endpoints
inside the harmonic-prefix mixture. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

lemma harmonicPrefixLaw_mean_abs_zero (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ n, |G n| ≤ B) (h : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun N => mean (harmonicPrefixLaw N) (fun i => |G (harmonicPrefixLength N i)|))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (h.abs.eventually_lt_const (show |(0 : ℝ)| < ε/2 by simpa using half_pos hε))
  have ht : Tendsto (fun N => B*(harmonic T : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  filter_upwards [eventually_ge_atTop T,ht.eventually_lt_const (half_pos hε)] with N hNT ht
  have hpoint (i : Fin (N+1)) : |G (harmonicPrefixLength N i)| ≤
      ε/2+B*(if harmonicPrefixLength N i < T then (1 : ℝ) else 0) := by
    split_ifs with hi
    · simpa only [mul_one] using (hG _).trans (by linarith : B ≤ ε/2+B)
    · simpa only [mul_zero,add_zero] using (hT _ (not_lt.mp hi)).le
  have hm := mean_mono (harmonicPrefixLaw N) _ _ hpoint
  rw [mean_add,mean_const,mean_const_mul] at hm
  have hmass := mul_le_mul_of_nonneg_left (harmonicPrefixLaw_short_length_mass N T (by omega)) hB
  have hnon := mean_nonneg_of_nonneg (harmonicPrefixLaw N) _ (fun i => abs_nonneg (G (harmonicPrefixLength N i)))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  calc
    _ ≤ ε/2+B*((harmonic T : ℝ)/(harmonic (N+1) : ℝ)) := hm.trans (add_le_add le_rfl hmass)
    _ < ε := by rw [← mul_div_assoc]; linarith

lemma conditioned_prefix_general_dilation_error {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (p N : ℕ) (hp : 0 < p) (hpN : p ≤ N) (hC : ∀ a b, |C a b| ≤ 1) :
    |p*prefixMean N (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)-
      prefixMean (N/p) (fun m => C (L (p*m)) (L (p*(m+1))))| ≤ 2*(p : ℝ)^2/N := by
  classical
  let T := N/p
  let M := p*T
  have hT : 0 < T := Nat.div_pos hpN hp
  have hM : 0 < M := Nat.mul_pos hp hT
  have hMN : M ≤ N := Nat.mul_div_le N p
  have htail : N-M ≤ p := by
    have he := Nat.div_add_mod N p
    have hr := Nat.mod_lt N hp
    dsimp [M,T]
    omega
  have he : p*prefixMean M (fun n => if p ∣ n then C (L n) (L (n+p)) else 0) =
      prefixMean T (fun m => C (L (p*m)) (L (p*(m+1)))) := by
    unfold prefixMean
    rw [show M=p*T from rfl,sum_divisible_range p T hp]
    have hpoint (m : ℕ) : C (L (p*m)) (L (p*m+p))=C (L (p*m)) (L (p*(m+1))) := by ring_nf
    simp_rw [hpoint]
    push_cast
    have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
  rw [← he,← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hb := prefixMean_endpoint_bound M N hM hMN
    (fun n => if p ∣ n then C (L n) (L (n+p)) else 0) 1
    (fun n _ => by dsimp only; split_ifs <;> simp_all)
  simp only [mul_one] at hb
  calc
    _ ≤ (p : ℝ)*(2*(N-M : ℕ)/N) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg p)
    _ ≤ (p : ℝ)*(2*p/N) := by gcongr
    _ = _ := by ring

noncomputable def naturalAdjacentTransferError {A : Type*}
    (p N : ℕ) (L : ℕ → A) (C : A → A → ℝ) : ℝ :=
  naturalGapDiscrepancy N p L C-
    (prefixMean (N/p) (fun n => C (L n) (L (n+1)))-
      prefixMean N (fun n => C (L n) (L (n+p))))

lemma naturalAdjacentTransferError_bound {A : Type*} (p N : ℕ) (L : ℕ → A)
    (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |naturalAdjacentTransferError p N L C| ≤ (p : ℝ)+1 := by
  unfold naturalAdjacentTransferError naturalGapDiscrepancy
  rw [sub_sub_sub_cancel_right]
  have h₁ := prefixMean_unit_bound (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)
    (fun n => by dsimp only; split_ifs <;> simp_all) N
  have h₂ := prefixMean_unit_bound (fun n => C (L n) (L (n+1))) (fun n => hC _ _) (N/p)
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  nlinarith [mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α := ℝ) p)]

lemma naturalAdjacentTransferError_zero {A : Type*} (p : ℕ) (hp : 0 < p) (L : ℕ → A)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    Tendsto (fun N => naturalAdjacentTransferError p N L C) atTop (𝓝 0) := by
  classical
  let V (m : ℕ) := C (L (p*m)) (L (p*(m+1)))
  let W (m : ℕ) := C (L m) (L (m+1))
  have hshift := prefixMean_shift_zero _ (labelDilationDefect_abs_le p L) hL 1
  have hdiff : Tendsto (fun T => prefixMean T V-prefixMean T W) atTop (𝓝 0) := by
    have ht := (hL.const_mul 2).add (hshift.const_mul 2)
    simp only [mul_zero,add_zero] at ht
    apply squeeze_zero_norm _ ht
    intro T
    rw [Real.norm_eq_abs]
    have hb (m : ℕ) : |V m-W m| ≤ 2*labelDilationDefect p L m+2*labelDilationDefect p L (m+1) :=
      bounded_pair_observable_change C hC _ _ _ _
    unfold prefixMean
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
    have hh := (abs_sum_le_sum_abs (fun m => V m-W m) (range T)).trans (sum_le_sum (fun m _ => hb m))
    have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) T)
    simpa only [sum_add_distrib,← mul_sum,add_div,mul_div_assoc] using hh'
  have hr : Tendsto (fun N => p*prefixMean N (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)-
      prefixMean (N/p) V) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (2*(p : ℝ)^2))
    filter_upwards [eventually_ge_atTop p] with N hN
    simpa only [Real.norm_eq_abs] using conditioned_prefix_general_dilation_error L C p N hp hN hC
  have ht := hr.add (hdiff.comp (Nat.tendsto_div_const_atTop hp.ne'))
  simp only [add_zero] at ht
  convert ht using 1
  funext N
  unfold naturalAdjacentTransferError naturalGapDiscrepancy
  dsimp only [Function.comp_def,W,V]
  ring

lemma harmonicPrefixAdjacentTransferError_zero {A : Type*} (p : ℕ) (hp : 0 < p) (L : ℕ → A)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    Tendsto (fun N => mean (harmonicPrefixLaw N) (fun i =>
      |naturalAdjacentTransferError p (harmonicPrefixLength N i) L C|)) atTop (𝓝 0) :=
  harmonicPrefixLaw_mean_abs_zero (fun N => naturalAdjacentTransferError p N L C)
    ((p : ℝ)+1) (by positivity)
    (fun N => naturalAdjacentTransferError_bound p N L C hC)
    (naturalAdjacentTransferError_zero p hp L hL C hC)

lemma mean_abs_finset_average_le {ι κ : Type*} [Fintype ι]
    (ρ : Law ι) (P : Finset κ) (F : κ → ι → ℝ) :
    mean ρ (fun i => |(∑ p ∈ P, F p i)/(P.card : ℝ)|) ≤
      (∑ p ∈ P, mean ρ (fun i => |F p i|))/(P.card : ℝ) := by
  have hh (i : ι) : |(∑ p ∈ P, F p i)/(P.card : ℝ)| ≤
      (∑ p ∈ P, |F p i|)/(P.card : ℝ) := by
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg P.card)
  have hm := mean_mono ρ _ _ hh
  simpa only [mean_div,mean_finset_sum] using hm

lemma harmonicPrefixAdjacentTransferError_average_zero {A : Type*} (L : ℕ → A)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    Tendsto (fun N => mean (harmonicPrefixLaw N) (fun i =>
      |(∑ p ∈ P, naturalAdjacentTransferError p (harmonicPrefixLength N i) L C)/(P.card : ℝ)|))
      atTop (𝓝 0) := by
  have ht := (tendsto_finset_sum P (fun p hp =>
    harmonicPrefixAdjacentTransferError_zero p (hP p hp) L (hL p (hP p hp)) C hC)).div_const (P.card : ℝ)
  simp only [sum_const_zero,zero_div] at ht
  apply squeeze_zero (fun N => mean_nonneg_of_nonneg _ _ (fun i => abs_nonneg _)) _ ht
  intro N
  exact mean_abs_finset_average_le (harmonicPrefixLaw N) P _

#print axioms harmonicPrefixLaw_mean_abs_zero
#print axioms naturalAdjacentTransferError_zero
#print axioms harmonicPrefixAdjacentTransferError_average_zero
end Erdos371.FiniteInformation
