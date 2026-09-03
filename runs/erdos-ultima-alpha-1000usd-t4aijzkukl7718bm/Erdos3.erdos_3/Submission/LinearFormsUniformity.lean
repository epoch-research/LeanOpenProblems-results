import Submission.FiniteUniformity
import Submission.FiniteSamplingMoments

/-! Generalized von Neumann bounds for distinct one-variable slopes over finite fields.
These counting inequalities do not supply a higher-order inverse or density increment theorem. -/
namespace Erdos3LinearFormsUniformity
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3QuadraticFourAPBarrier
  Erdos3FiniteSamplingMoments
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma expect_re {I : Type*} [Fintype I] (f : I → ℂ) :
    (𝔼 x : I, f x).re = 𝔼 x : I, (f x).re :=
  map_expect (Complex.reCLM.toLinearMap.restrictScalars ℚ≥0) f univ

lemma mean_complexCorr_re (f : G → ℂ) :
    ‖𝔼 x : G, f x‖^2 = 𝔼 h : G, (complexCorr f h).re := by
  have hh : (𝔼 h : G, complexCorr f h) = ((‖𝔼 x : G, f x‖^2 : ℝ) : ℂ) := by
    simpa only [hat,AddChar.one_apply,map_one,mul_one] using hat_complexCorr f 1
  have hh' := congrArg Complex.re hh
  simpa only [expect_re,Complex.ofReal_re] using hh'.symm

lemma mean_product_sq_le (f g : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 x : G, f x*g x‖^2 ≤ 𝔼 x : G, ‖g x‖^2 := by
  have hn : ‖𝔼 x : G, f x*g x‖ ≤ 𝔼 x : G, ‖g x‖ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le_expect
    intro x _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)).trans_eq (one_mul _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (expect_even_pow_le (by decide : Even 2) _)

variable {F : Type*} [Field F] [Fintype F]

noncomputable def linearAverage {k : ℕ} (v : Fin k → F) (f : Fin k → F → ℂ) : ℂ :=
  𝔼 x : F, 𝔼 d : F, ∏ i : Fin k, f i (x+v i*d)

lemma linearAverage_sub_slopes {k : ℕ} (v : Fin k → F) (f : Fin k → F → ℂ) (c : F) :
    linearAverage (fun i ↦ v i-c) f = linearAverage v f := by
  unfold linearAverage
  calc
    _ = 𝔼 d : F, 𝔼 x : F, ∏ i : Fin k, f i (x+(v i-c)*d) := expect_comm _ _ _
    _ = 𝔼 d : F, 𝔼 x : F, ∏ i : Fin k, f i (x+v i*d) := by
      apply expect_congr rfl
      intro d _
      exact Fintype.expect_equiv (Equiv.addRight (-c*d)) _ _ (fun x ↦ by
        apply prod_congr rfl
        intro i _
        congr 1
        change x+(v i-c)*d = (x+ -c*d)+v i*d
        ring)
    _ = _ := expect_comm _ _ _

lemma linearAverage_reindex {k : ℕ} (v : Fin k → F) (f : Fin k → F → ℂ) (e : Equiv.Perm (Fin k)) :
    linearAverage (fun i ↦ v (e i)) (fun i ↦ f (e i)) = linearAverage v f := by
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro d _
  exact Fintype.prod_equiv e _ _ (fun i ↦ rfl)

lemma two_forms_factor (v : Fin 2 → F) (f : Fin 2 → F → ℂ)
    (hv0 : v 0 = 0) (hv1 : v 1 ≠ 0) :
    linearAverage v f = (𝔼 x : F, f 0 x)*(𝔼 x : F, f 1 x) := by
  unfold linearAverage
  simp only [Fin.prod_univ_two,hv0,zero_mul,add_zero]
  simp_rw [← mul_expect]
  have he (x : F) : (𝔼 d : F, f 1 (x+v 1*d)) = 𝔼 y : F, f 1 y :=
    Fintype.expect_equiv ((Equiv.mulLeft₀ (v 1) hv1).trans (Equiv.addLeft x)) _ _ (fun d ↦ rfl)
  simp_rw [he]
  exact (expect_mul ..).symm

lemma derivative_average_identity {k : ℕ} (v : Fin (k+1) → F)
    (f : Fin (k+1) → F → ℂ) (h : F) :
    (𝔼 x : F, complexCorr (fun d : F ↦ ∏ i : Fin k, f i.succ (x+v i.succ*d)) h) =
      linearAverage (fun i : Fin k ↦ v i.succ)
        (fun i : Fin k ↦ derivative (f i.succ) (v i.succ*h)) := by
  unfold complexCorr linearAverage
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro d _
  rw [map_prod,← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  unfold derivative
  congr 2
  ring

/-- One Cauchy--Schwarz step removes the zero-slope function. -/
lemma eliminate_zero_slope {k : ℕ} (v : Fin (k+1) → F) (f : Fin (k+1) → F → ℂ)
    (hv : v 0 = 0) (hf : ∀ x, ‖f 0 x‖ ≤ 1) :
    ‖linearAverage v f‖^2 ≤
      𝔼 h : F, ‖linearAverage (fun i : Fin k ↦ v i.succ)
        (fun i : Fin k ↦ derivative (f i.succ) (v i.succ*h))‖ := by
  let g : F → F → ℂ := fun x d ↦ ∏ i : Fin k, f i.succ (x+v i.succ*d)
  have he : linearAverage v f = 𝔼 x : F, f 0 x*(𝔼 d : F, g x d) := by
    unfold linearAverage
    simp only [Fin.prod_univ_succ,hv,zero_mul,add_zero,← mul_expect]
    rfl
  rw [he]
  calc
    _ ≤ 𝔼 x : F, ‖𝔼 d : F, g x d‖^2 := mean_product_sq_le (f 0) _ hf
    _ = 𝔼 x : F, 𝔼 h : F, (complexCorr (g x) h).re := by
      apply expect_congr rfl
      intro x _
      exact mean_complexCorr_re (g x)
    _ = 𝔼 h : F, (𝔼 x : F, complexCorr (g x) h).re := by
      rw [expect_comm]
      simp only [expect_re]
    _ = 𝔼 h : F, (linearAverage (fun i : Fin k ↦ v i.succ)
        (fun i : Fin k ↦ derivative (f i.succ) (v i.succ*h))).re := by
      simp only [g,derivative_average_identity]
    _ ≤ _ := expect_le_expect (fun _ _ ↦ Complex.re_le_norm _)

/-- A distinct-slope system with n+2 forms is controlled by U^(n+1) of its last function. -/
theorem distinct_slopes_last_bound (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (f : Fin (n+2) → F → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖linearAverage v f‖^(2^(n+1)) ≤ uniformityPower n (f (Fin.last (n+1))) := by
  induction n with
  | zero =>
    let w : Fin 2 → F := fun i ↦ v i-v 0
    have hw0 : w 0 = 0 := sub_self _
    have hw1 : w 1 ≠ 0 := by
      intro hh
      have he := hv (sub_eq_zero.mp hh)
      exact (by decide : (1 : Fin 2) ≠ 0) he
    rw [← linearAverage_sub_slopes v f (v 0)]
    change ‖linearAverage w f‖^2 ≤ ‖𝔼 x : F, f 1 x‖^2
    rw [two_forms_factor w f hw0 hw1,norm_mul]
    have hm : ‖𝔼 x : F, f 0 x‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun x _ ↦ hf 0 x))
    exact pow_le_pow_left₀ (by positivity)
      ((mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans_eq (one_mul _)) 2
  | succ n ih =>
    let w : Fin (n+3) → F := fun i ↦ v i-v 0
    have hw : Function.Injective w := fun i j hij ↦ hv (sub_left_injective hij)
    have hw0 : w 0 = 0 := sub_self _
    let v' : Fin (n+2) → F := fun i ↦ w i.succ
    have hv' : Function.Injective v' := fun i j hij ↦ Fin.succ_injective _ (hw hij)
    let f' : F → Fin (n+2) → F → ℂ := fun h i ↦ derivative (f i.succ) (w i.succ*h)
    have hfn (h : F) (i : Fin (n+2)) (x : F) : ‖f' h i x‖ ≤ 1 := derivative_norm_le_one _ (hf i.succ) _ _
    have hcs : ‖linearAverage v f‖^2 ≤ 𝔼 h : F, ‖linearAverage v' (f' h)‖ := by
      rw [← linearAverage_sub_slopes v f (v 0)]
      exact eliminate_zero_slope w f hw0 (hf 0)
    have heven : Even (2^(n+1)) := ⟨2^n, by rw [pow_succ]; omega⟩
    have hlast : w (Fin.last (n+2)) ≠ 0 := by
      intro he
      have hi := hw (he.trans hw0.symm)
      have hh := congrArg Fin.val hi
      simp only [Fin.val_last,Fin.val_zero] at hh
      omega
    calc
      _ = (‖linearAverage v f‖^2)^(2^(n+1)) := by
        rw [← pow_mul]
        congr 1
        rw [pow_succ]
        ring
      _ ≤ (𝔼 h : F, ‖linearAverage v' (f' h)‖)^(2^(n+1)) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 h : F, ‖linearAverage v' (f' h)‖^(2^(n+1)) := expect_even_pow_le heven _
      _ ≤ 𝔼 h : F, uniformityPower n (f' h (Fin.last (n+1))) :=
        expect_le_expect (fun h _ ↦ ih v' hv' (f' h) (hfn h))
      _ = 𝔼 h : F, uniformityPower n (derivative (f (Fin.last (n+2))) h) := by
        simp only [f',Fin.succ_last]
        exact Fintype.expect_equiv (Equiv.mulLeft₀ (w (Fin.last (n+2))) hlast) _ _ (fun h ↦ rfl)
      _ = _ := rfl

/-- Generalized von Neumann inequality, with any selected function on the right. -/
theorem distinct_slopes_bound (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (f : Fin (n+2) → F → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (i : Fin (n+2)) :
    ‖linearAverage v f‖^(2^(n+1)) ≤ uniformityPower n (f i) := by
  let e := Equiv.swap i (Fin.last (n+1))
  have hh := distinct_slopes_last_bound n (fun j ↦ v (e j)) (hv.comp e.injective)
    (fun j ↦ f (e j)) (fun j x ↦ hf (e j) x)
  simpa only [linearAverage_reindex,e,Equiv.swap_apply_right] using hh

#print axioms eliminate_zero_slope
#print axioms distinct_slopes_bound
end Erdos3LinearFormsUniformity
