import Submission.PolynomialMonomialRecurrence

/-! Simultaneous recurrence for arbitrary finite collections of positive
monomial degrees, polynomial in inverse accuracy for each fixed complexity. -/
namespace Erdos3SimultaneousPolynomialRecurrence
open Finset Erdos3PolynomialMonomialRecurrence Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

def degreeRecurrenceConstant (K : ℕ) : ℕ := 1+∑ k ∈ range K, powerRecurrenceConstant k

lemma degreeRecurrenceConstant_pos (K : ℕ) : 0 < degreeRecurrenceConstant K := by
  unfold degreeRecurrenceConstant
  omega

lemma powerRecurrenceConstant_le {K k : ℕ} (hk : k < K) :
    powerRecurrenceConstant k ≤ degreeRecurrenceConstant K := by
  have hh := single_le_sum (fun j (_ : j ∈ range K) ↦ Nat.zero_le (powerRecurrenceConstant j))
    (mem_range.mpr hk)
  exact hh.trans (by unfold degreeRecurrenceConstant; omega)

lemma bounded_degree_recurrence (K e : ℕ) (he : 0 < e) (heK : e ≤ K)
    (v : ℂ) (hv : ‖v‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(degreeRecurrenceConstant K*(t+1)) ∧
      ‖v^(d^e)-1‖ ≤ (1/2 : ℝ)^t := by
  cases e with
  | zero => omega
  | succ k =>
    obtain ⟨d,hd,hbound,hrec⟩ := monomial_recurrence k v hv t
    exact ⟨d,hd,hbound.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (powerRecurrenceConstant_le (by omega)))),hrec⟩

lemma polynomial_dilate_bound (v : ℂ) (hv : ‖v‖ = 1) (a b e K t B : ℕ)
    (he : e ≤ K) (hb : b ≤ 2^B)
    (hclose : ‖v^(a^e)-1‖ ≤ (1/2 : ℝ)^(t+K*B)) :
    ‖v^((a*b)^e)-1‖ ≤ (1/2 : ℝ)^t := by
  have hpow : b^e ≤ (2^B)^K := (Nat.pow_le_pow_left hb e).trans
    (Nat.pow_le_pow_right (Nat.two_pow_pos _) he)
  have hunit : ‖v^(a^e)‖ = 1 := by rw [norm_pow,hv,one_pow]
  calc
    _ = ‖(v^(a^e))^(b^e)-1‖ := by rw [← pow_mul,mul_pow]
    _ ≤ (b^e : ℕ)*‖v^(a^e)-1‖ := unit_power_oscillation _ hunit _
    _ ≤ ((2^B : ℕ) : ℝ)^K*(1/2 : ℝ)^(t+K*B) := by
      apply mul_le_mul
      · exact_mod_cast hpow
      · exact hclose
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      rw [Nat.cast_pow,Nat.cast_ofNat,pow_add,Nat.mul_comm K B,pow_mul]
      simp only [div_pow,one_pow]
      field_simp

def simultaneousPowerConstant (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => simultaneousPowerConstant K m*(K*degreeRecurrenceConstant K+1)+degreeRecurrenceConstant K

/-- Simultaneous recurrence on a finite tuple. No linear or quadratic degree
restriction remains; the cost constant depends on the maximal degree and tuple length. -/
theorem simultaneous_recurrence_fin (K m : ℕ) (e : Fin m → ℕ)
    (he : ∀ i, 0 < e i ∧ e i ≤ K) (v : Fin m → ℂ) (hv : ∀ i, ‖v i‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(simultaneousPowerConstant K m*(t+1)) ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2 : ℝ)^t := by
  induction m generalizing t with
  | zero =>
    refine ⟨1,by decide,by simp [simultaneousPowerConstant],?_⟩
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    obtain ⟨a,ha,hab,hrec⟩ := ih (fun i ↦ e i.succ) (fun i ↦ he i.succ)
      (fun i ↦ v i.succ) (fun i ↦ hv i.succ)
      (t+K*(degreeRecurrenceConstant K*(t+1)))
    obtain ⟨b,hb,hbb,hfirst⟩ := bounded_degree_recurrence K (e 0) (he 0).1 (he 0).2
      ((v 0)^(a^(e 0))) (by rw [norm_pow,hv,one_pow]) t
    refine ⟨a*b,Nat.mul_pos ha hb,?_,?_⟩
    · calc
        _ ≤ 2^(simultaneousPowerConstant K m*(t+K*(degreeRecurrenceConstant K*(t+1))+1))*
            2^(degreeRecurrenceConstant K*(t+1)) := Nat.mul_le_mul hab hbb
        _ = _ := by
          rw [← pow_add]
          congr 1
          rw [simultaneousPowerConstant]
          ring
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [← pow_mul,← mul_pow] using hfirst
      · exact polynomial_dilate_bound (v j.succ) (hv j.succ) a b (e j.succ) K t
          (degreeRecurrenceConstant K*(t+1)) (he j.succ).2 hbb (hrec j)

/-- Arbitrary finite collections of unit phases and positive monomial degrees. -/
theorem simultaneous_polynomial_recurrence {I : Type*} [Fintype I]
    (K : ℕ) (e : I → ℕ) (he : ∀ i, 0 < e i ∧ e i ≤ K)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(simultaneousPowerConstant K (Fintype.card I)*(t+1)) ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2 : ℝ)^t := by
  let E := (Fintype.equivFin I).symm
  obtain ⟨d,hd,hdb,hrec⟩ := simultaneous_recurrence_fin K (Fintype.card I)
    (e ∘ E) (fun i ↦ he (E i)) (v ∘ E) (fun i ↦ hv (E i)) t
  refine ⟨d,hd,hdb,?_⟩
  intro i
  simpa only [Function.comp_apply,E,Equiv.symm_apply_apply] using hrec ((Fintype.equivFin I) i)

lemma simultaneousPowerConstant_upper (K m : ℕ) :
    simultaneousPowerConstant K m ≤ (K*degreeRecurrenceConstant K+degreeRecurrenceConstant K+1)^m := by
  induction m with
  | zero => simp [simultaneousPowerConstant]
  | succ m ih =>
    have hp : 1 ≤ (K*degreeRecurrenceConstant K+degreeRecurrenceConstant K+1)^m :=
      Nat.one_le_pow _ _ (by omega)
    rw [simultaneousPowerConstant,pow_succ]
    nlinarith only [ih,hp,Nat.zero_le (degreeRecurrenceConstant K),
      Nat.mul_le_mul_right (K*degreeRecurrenceConstant K+1) ih,
      Nat.mul_le_mul_left (degreeRecurrenceConstant K) hp]

#print axioms simultaneous_polynomial_recurrence
#print axioms simultaneousPowerConstant_upper
end Erdos3SimultaneousPolynomialRecurrence
