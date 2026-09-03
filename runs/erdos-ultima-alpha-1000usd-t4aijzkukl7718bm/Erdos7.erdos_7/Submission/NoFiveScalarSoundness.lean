import Submission.NoFiveScalarData

/-! Soundness of the mixed-cap finite supersolution, at arbitrary exponent caps. -/
namespace Erdos7NoFiveScalar
open scoped BigOperators
open Erdos7RationalGeometricBudget
open Erdos7CompressionSieve Erdos7Distortion
open Erdos7BinarySieve (expect expect_add expect_le)
open Erdos7ExponentLaw
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

variable (hcert :
    (∀ i : Fin 366, 3 ≤ primes i ∧ primes i ≤ 2503 ∧
      Row (primes i) (states i.castSucc) (states i.succ)) ∧
    (∀ x : Fin 501, (states 366).values x=0) ∧
    (states 366).slope=0 ∧ (states 366).intercept=0)

lemma loss_affine (p x : ℕ) (hp : 3 ≤ p) (hp53 : p ≤ 2503) (hx : 501 ≤ x) :
    loss p x=cap p/(p-1)*x-(cap p-1) := by
  have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hpQ53 : (p : ℚ) ≤ 2503 := by exact_mod_cast hp53
  have hxQ : (501 : ℚ) ≤ x := by exact_mod_cast hx
  have hp1 : (0 : ℚ)<p-1 := by linarith
  by_cases h3 : p=3
  · subst p
    norm_num [loss,cap]
    omega
  · have hc : cap p=(5/4 : ℚ) := by simp [cap,h3]
    unfold loss
    rw [hc,max_eq_right]
    · ring
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ hp1).mpr
      nlinarith

lemma row_budget (p : ℕ) (hp : 3 ≤ p) (hp53 : p ≤ 2503)
    (s t : State) (hr : Row p s t) (x : ℕ) :
    loss p x+budget p (cap p) t.eval t.slope (501/x) x ≤ s.eval x := by
  by_cases hx : x<502
  · exact hr.2.2.1 ⟨x,hx⟩
  · have h11 : 501 ≤ x := by omega
    have hpQ : (1 : ℚ)<p := by exact_mod_cast (show 1<p by omega)
    have hrow := hr.2.2.1 (501 : Fin 502)
    change loss p 501+budget p (cap p) t.eval t.slope (501/501) 501 ≤ s.eval 501 at hrow
    rw [loss_affine p 501 hp hp53 (by omega),
      budget_affine p (cap p) hpQ t.eval 501 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) (501/501) 501 (by omega),
      s.eval_affine 501 (by omega)] at hrow
    rw [loss_affine p x hp hp53 h11,
      budget_affine p (cap p) hpQ t.eval 501 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) (501/x) x h11,
      s.eval_affine x h11]
    have hxQ : (501 : ℚ) ≤ x := by exact_mod_cast h11
    nlinarith [hr.2.2.2]

/- A certified row bounds every finite exponent cap, not just the state-dependent
geometric terms used in checking it. -/
include hcert in
theorem row_op_of_certificate (i : Fin 366) (E x : ℕ) :
    loss (primes i) x + op (primes i) (cap (primes i)) (states i.succ).eval E x ≤
      (states i.castSucc).eval x := by
  obtain ⟨hp,hp53,hr⟩ := hcert.1 i
  have hh := row_budget (primes i) hp hp53 _ _ hr x
  apply (add_le_add (le_refl (loss (primes i) x)) ?_).trans hh
  by_cases hx : x=0
  · subst x
    rw [op_zero,budget_zero]
  · apply op_le_budget (primes i) (cap (primes i)) (by exact_mod_cast (show 1<primes i by omega))
      (by have := (cap_bounds (primes i)).1; linarith) _ (State.monotone _ hr.2.1) 501 _ _ hr.2.1.1
      (fun x hx => State.eval_affine _ x hx) (501/x) E x
    have ht := Nat.lt_mul_div_succ 501 (show 0<x by omega)
    simpa only [Nat.mul_comm] using ht.le

include hcert in
lemma terminal_eval_of_certificate (x : ℕ) : (states 366).eval x=0 := by
  unfold State.eval
  split
  · exact hcert.2.1 _
  · rw [hcert.2.2.1,hcert.2.2.2]
    ring

def tails (E : Fin 366 → ℕ) (i : Fin 366) := powerTail (primes i) (cap (primes i)) (E i)

noncomputable def lossAt (E : Fin 366 → ℕ) (t : ℕ) : ℚ :=
  if h : t<366 then expect (prefixLaw E (tails E) t) (loss (primes ⟨t,h⟩)) else 0

include hcert in
lemma law_nonneg_of_certificate (E : Fin 366 → ℕ) (t x : ℕ) : 0 ≤ prefixLaw E (tails E) t x := by
  apply prefix_nonneg E (tails E)
  · intro i
    have hp := (hcert.1 i).1
    exact powerTail_zero_le_one (primes i) (by omega) (cap (primes i))
      (cap_le_prime (primes i) hp) (E i)
  · intro i g hg
    exact powerTail_decreasing (primes i) (by have := (hcert.1 i).1; omega)
      (cap (primes i)) (by have := (cap_bounds (primes i)).1; linarith) (E i) g

include hcert in
lemma prefix_potential_of_certificate (E : Fin 366 → ℕ) (t : ℕ) (ht : t ≤ 366) :
    (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (states ⟨t,by omega⟩).eval ≤ (states 0).eval 1 := by
  induction t with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,prefixLaw,expect_initial]; exact le_rfl
  | succ t ih =>
    have ht14 : t<366 := by omega
    let i : Fin 366 := ⟨t,ht14⟩
    have hstep := expect_le (prefixLaw E (tails E) t) (law_nonneg_of_certificate hcert E t)
      (fun x => loss (primes i) x + op (primes i) (cap (primes i)) (states i.succ).eval (E i) x)
      (states i.castSucc).eval (row_op_of_certificate hcert i (E i))
    rw [expect_add,expect_op] at hstep
    have hrec : prefixLaw E (tails E) (t+1) =
        step (E i) (tails E i) (prefixLaw E (tails E) t) := by
      simp only [prefixLaw,ht14,dif_pos,i]
    rw [Finset.sum_range_succ,hrec]
    have hi := ih (by omega)
    have he : lossAt E t=expect (prefixLaw E (tails E) t) (loss (primes i)) := by
      simp only [lossAt,ht14,dif_pos,i]
    rw [he]
    change (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (loss (primes i)) +
      expect (step (E i) (tails E i) (prefixLaw E (tails E) t)) (states i.succ).eval ≤ _
    change (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (states i.castSucc).eval ≤ _ at hi
    change expect (prefixLaw E (tails E) t) (loss (primes i)) +
      expect (step (E i) (tails E i) (prefixLaw E (tails E) t)) (states i.succ).eval ≤ _ at hstep
    linarith

/- The complete ninety-four-prime finite-exponent hinge budget is below the
certified initial value, independently of all ninety-four exponent bounds. -/
include hcert in
theorem prefix_cost_bound_of_certificate (E : Fin 366 → ℕ) :
    exponentCost E (tails E) (fun i => cap (primes i)) (fun i => 1/(primes i-1 : ℚ)) ≤
      (states 0).eval 1 := by
  have hh := prefix_potential_of_certificate hcert E 366 le_rfl
  have hz : expect (prefixLaw E (tails E) 366) (states 366).eval=0 := by
    simp only [expect,Finsupp.sum,terminal_eval_of_certificate hcert,mul_zero,Finset.sum_const_zero]
  change (∑ j ∈ Finset.range 366, lossAt E j) +
    expect (prefixLaw E (tails E) 366) (states 366).eval ≤ _ at hh
  rw [hz,add_zero] at hh
  apply le_trans (le_of_eq ?_) hh
  unfold exponentCost
  rw [← Fin.sum_univ_eq_sum_range (lossAt E) 366]
  apply Finset.sum_congr rfl
  intro i hi
  rw [exponentEnvelope_eq_expect]
  simp only [lossAt,i.isLt,dif_pos,Nat.cast_one,one_mul]
  apply Erdos7BinarySieve.expect_congr
  intro k
  unfold loss Erdos7Distortion.residual
  congr 1
  ring

#print axioms prefix_cost_bound_of_certificate
#print axioms row_op_of_certificate
end Erdos7NoFiveScalar
