import Submission.PolynomialSquareRecurrence
import Submission.MaskedPhaseIncrement

/-! Simultaneous linear and square recurrence with a bound polynomial in
inverse accuracy for each fixed number of phases. -/
namespace Erdos3PolynomialMixedRecurrence
open Finset Erdos3PolynomialSquareRecurrence Erdos3MaskedPhaseIncrement
  Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma same_grid_close {V : Type*} (n : ℕ) (hn : 0 < n) (q : V → ℂ)
    (hq : ∀ x, ‖q x‖ ≤ 1) {x y : V} (he : phaseLabel n q hq x = phaseLabel n q hq y) :
    ‖q x-q y‖ ≤ 2/(n : ℝ) := by
  have hre := gridCoord_close hn ((Complex.abs_re_le_norm _).trans (hq x))
    ((Complex.abs_re_le_norm _).trans (hq y)) (congrArg Prod.fst he)
  have him := gridCoord_close hn ((Complex.abs_im_le_norm _).trans (hq x))
    ((Complex.abs_im_le_norm _).trans (hq y)) (congrArg Prod.snd he)
  calc
    _ ≤ |(q x-q y).re|+|(q x-q y).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(n : ℝ)+1/(n : ℝ) := by simpa only [Complex.sub_re,Complex.sub_im] using add_le_add hre him
    _ = _ := by ring

lemma single_linear_recurrence (v : ℂ) (hv : ‖v‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(11*t+39) ∧ ‖v^d-1‖ ≤ (1/2 : ℝ)^t := by
  let n := 2^(t+1)
  have hn : 0 < n := by dsimp [n]; positivity
  let M := (2*n+1)^2
  let c : Fin (M+1) → PhaseGrid n := fun k ↦
    phaseLabel n (fun k : ℕ ↦ v^k) (fun k ↦ by rw [norm_pow,hv,one_pow]) k.val
  have hcard : Fintype.card (PhaseGrid n) = M := by
    simp only [PhaseGrid,Fintype.card_prod,Fintype.card_fin,M,pow_two]
  obtain ⟨x,y,hxy,he⟩ := Fintype.exists_ne_map_eq_of_card_lt c
    (by rw [hcard,Fintype.card_fin]; omega)
  have hordered : ∃ x y : Fin (M+1), x.val < y.val ∧ c x = c y := by
    rcases lt_trichotomy x.val y.val with h|h|h
    · exact ⟨x,y,h,he⟩
    · exact (hxy (Fin.ext h)).elim
    · exact ⟨y,x,h,he.symm⟩
  obtain ⟨x,y,hxy,he⟩ := hordered
  let d := y.val-x.val
  have hd : 0 < d := by dsimp [d]; omega
  have hdM : d ≤ M := by dsimp [d]; omega
  have hn1 : 1 ≤ n := hn
  have hM : M ≤ 2^(11*t+39) := by
    calc
      _ ≤ (4*n)^2 := Nat.pow_le_pow_left (by omega : 2*n+1 ≤ 4*n) 2
      _ = 2^(2*t+6) := by
        dsimp [n]
        rw [show 4 = 2^2 by norm_num, ← pow_add, ← pow_mul]
        congr 1
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨d,hd,hdM.trans hM,?_⟩
  have hh := same_grid_close n hn (fun k : ℕ ↦ v^k)
    (fun k ↦ by rw [norm_pow,hv,one_pow]) he
  calc
    _ = ‖v^x.val*(v^d-1)‖ := by rw [norm_mul,norm_pow,hv,one_pow,one_mul]
    _ = ‖v^y.val-v^x.val‖ := by rw [mul_sub,mul_one,← pow_add,show x.val+d = y.val by dsimp [d]; omega]
    _ ≤ 2/(n : ℝ) := by simpa only [norm_sub_rev] using hh
    _ = _ := by
      dsimp [n]
      rw [Nat.cast_pow,Nat.cast_ofNat,pow_succ,div_pow,one_pow]
      field_simp

lemma single_power_recurrence (e : ℕ) (he : e = 1 ∨ e = 2)
    (v : ℂ) (hv : ‖v‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(11*t+39) ∧ ‖v^(d^e)-1‖ ≤ (1/2 : ℝ)^t := by
  rcases he with rfl|rfl
  · simpa only [pow_one] using single_linear_recurrence v hv t
  · obtain ⟨d,hd,hbound,hrec⟩ := single_square_recurrence v hv t
    rw [singleRecurrenceBound_eq] at hbound
    refine ⟨d,hd,?_,hrec⟩
    exact (Nat.lt_succ_iff.mp hbound).trans (Nat.pow_le_pow_right (by decide) (by omega))

lemma dyadic_dilate_bound (v : ℂ) (hv : ‖v‖ = 1) (a b e t B : ℕ)
    (he : e = 1 ∨ e = 2) (hb : b ≤ 2^B)
    (hclose : ‖v^(a^e)-1‖ ≤ (1/2 : ℝ)^(t+2*B)) :
    ‖v^((a*b)^e)-1‖ ≤ (1/2 : ℝ)^t := by
  have hpow : b^e ≤ (2^B)^2 := by
    rcases he with rfl|rfl
    · rw [pow_one]
      exact hb.trans (Nat.le_self_pow (by decide) (2^B))
    · exact Nat.pow_le_pow_left hb 2
  have hunit : ‖v^(a^e)‖ = 1 := by rw [norm_pow,hv,one_pow]
  calc
    _ = ‖(v^(a^e))^(b^e)-1‖ := by rw [← pow_mul, mul_pow]
    _ ≤ (b^e : ℕ)*‖v^(a^e)-1‖ := unit_power_oscillation _ hunit _
    _ ≤ ((2^B : ℕ) : ℝ)^2*(1/2 : ℝ)^(t+2*B) := by
      apply mul_le_mul
      · exact_mod_cast hpow
      · exact hclose
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      rw [Nat.cast_pow,Nat.cast_ofNat,pow_add,show 2*B = B*2 by omega,pow_mul,
        div_pow,one_pow]
      simp only [div_pow,one_pow]
      have hp : (2 : ℝ)^B ≠ 0 := by positivity
      field_simp

def mixedExponent : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m+1, t => mixedExponent m (23*t+78)+11*t+39

lemma mixedExponent_upper (m t : ℕ) :
    2*mixedExponent m t+t+4 ≤ 23^m*(t+4) := by
  induction m generalizing t with
  | zero => simp [mixedExponent]
  | succ m ih =>
    have hh := ih (23*t+78)
    rw [mixedExponent,pow_succ]
    nlinarith only [hh,show (0 : ℕ) ≤ 23^m from Nat.zero_le _]

/-- Recursive simultaneous recurrence for phases with exponent one or two. -/
theorem mixed_recurrence_fin (m : ℕ) (e : Fin m → ℕ) (he : ∀ i, e i = 1 ∨ e i = 2)
    (v : Fin m → ℂ) (hv : ∀ i, ‖v i‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(mixedExponent m t) ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2 : ℝ)^t := by
  induction m generalizing t with
  | zero =>
    refine ⟨1,by decide,by simp [mixedExponent],?_⟩
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    obtain ⟨a,ha,hab,hrec⟩ := ih (fun i ↦ e i.succ) (fun i ↦ he i.succ)
      (fun i ↦ v i.succ) (fun i ↦ hv i.succ) (23*t+78)
    obtain ⟨b,hb,hbb,hfirst⟩ := single_power_recurrence (e 0) (he 0)
      ((v 0)^(a^(e 0))) (by rw [norm_pow,hv,one_pow]) t
    refine ⟨a*b,Nat.mul_pos ha hb,?_,?_⟩
    · calc
        _ ≤ 2^(mixedExponent m (23*t+78))*2^(11*t+39) := Nat.mul_le_mul hab hbb
        _ = _ := by rw [← pow_add]; congr 1
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [← pow_mul,← mul_pow] using hfirst
      · apply dyadic_dilate_bound (v j.succ) (hv j.succ) a b (e j.succ) t (11*t+39)
          (he j.succ) hbb
        simpa only [show t+2*(11*t+39) = 23*t+78 by omega] using hrec j

def polynomialRecurrenceBound (m t : ℕ) : ℕ := 2^(mixedExponent m t)+1

/-- Arbitrary finite index sets, retaining the polynomial accuracy dependence. -/
theorem polynomial_power_recurrence {I : Type*} [Fintype I]
    (e : I → ℕ) (he : ∀ i, e i = 1 ∨ e i = 2)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d < polynomialRecurrenceBound (Fintype.card I) t ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2 : ℝ)^t := by
  let E := (Fintype.equivFin I).symm
  obtain ⟨d,hd,hdb,hrec⟩ := mixed_recurrence_fin (Fintype.card I)
    (e ∘ E) (fun i ↦ he (E i)) (v ∘ E) (fun i ↦ hv (E i)) t
  refine ⟨d,hd,by unfold polynomialRecurrenceBound; omega,?_⟩
  intro i
  simpa only [Function.comp_apply,E,Equiv.symm_apply_apply] using hrec ((Fintype.equivFin I) i)

theorem polynomial_mixed_recurrence {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℂ) (v : J → ℂ) (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d < polynomialRecurrenceBound (Fintype.card I+Fintype.card J) t ∧
      (∀ i, ‖(w i)^d-1‖ ≤ (1/2 : ℝ)^t) ∧
      ∀ j, ‖(v j)^(d^2)-1‖ ≤ (1/2 : ℝ)^t := by
  let e : I ⊕ J → ℕ := Sum.elim (fun _ ↦ 1) (fun _ ↦ 2)
  let u : I ⊕ J → ℂ := Sum.elim w v
  have he (i : I ⊕ J) : e i = 1 ∨ e i = 2 := by
    cases i with
    | inl i => exact Or.inl rfl
    | inr j => exact Or.inr rfl
  have hu (i : I ⊕ J) : ‖u i‖ = 1 := by cases i <;> simp only [u,Sum.elim_inl,Sum.elim_inr,hw,hv]
  obtain ⟨d,hd,hbound,hrec⟩ := polynomial_power_recurrence e he u hu t
  refine ⟨d,hd,by simpa only [Fintype.card_sum] using hbound,?_,?_⟩
  · intro i
    simpa only [e,u,Sum.elim_inl,pow_one] using hrec (Sum.inl i)
  · intro j
    simpa only [e,u,Sum.elim_inr] using hrec (Sum.inr j)

#print axioms mixed_recurrence_fin
#print axioms polynomial_mixed_recurrence
end Erdos3PolynomialMixedRecurrence
