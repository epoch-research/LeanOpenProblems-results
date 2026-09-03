import Submission.DirectFiveScalarCheck

/-! Uniform finite-exponent soundness of the 366-prime prefix with a modified root. -/
namespace Erdos7DirectFiveScalar
open scoped BigOperators
open Erdos7NoFiveScalar (State)
open Erdos7RationalGeometricBudget Erdos7CompressionSieve Erdos7Distortion
open Erdos7BinarySieve (expect expect_add expect_le)
open Erdos7ExponentLaw
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma row_certificate (i : Fin 366) : Row (primes i) (states i.castSucc) (states i.succ) := by
  by_cases h0 : i=0
  · subst i; exact row_certificate_0
  apply row_suffix i
  have h0' : i.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
  omega

lemma terminal_eval (x : ℕ) : (states 366).eval x=0 := by
  change (Erdos7NoFiveScalar.states 366).eval x=0
  exact Erdos7NoFiveScalar.terminal_eval_of_certificate Erdos7NoFiveScalar.certificate x

lemma initial_bound : (states 0).eval 1 ≤ (87/200 : ℚ) := by decide +kernel

def tails (E : Fin 366 → ℕ) (i : Fin 366) := powerTail (primes i) (cap (primes i)) (E i)

noncomputable def lossAt (E : Fin 366 → ℕ) (t : ℕ) : ℚ :=
  if h : t<366 then expect (prefixLaw E (tails E) t) (loss (primes ⟨t,h⟩)) else 0

lemma law_nonneg (E : Fin 366 → ℕ) (t x : ℕ) : 0 ≤ prefixLaw E (tails E) t x := by
  apply prefix_nonneg E (tails E)
  · intro i
    have hp := (prime_metadata.1 i).2.1
    exact powerTail_zero_le_one (primes i) (by omega) (cap (primes i))
      (cap_le_prime (primes i) hp) (E i)
  · intro i g hg
    exact powerTail_decreasing (primes i) (by have := (prime_metadata.1 i).2.1; omega)
      (cap (primes i)) (by have := (cap_bounds (primes i)).1; linarith) (E i) g

lemma prefix_potential (E : Fin 366 → ℕ) (t : ℕ) (ht : t ≤ 366) :
    (∑ j ∈ Finset.range t, lossAt E j) +
      expect (prefixLaw E (tails E) t) (states ⟨t,by omega⟩).eval ≤ (states 0).eval 1 := by
  induction t with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,prefixLaw,expect_initial]; exact le_rfl
  | succ t ih =>
    have ht14 : t<366 := by omega
    let i : Fin 366 := ⟨t,ht14⟩
    have hstep := expect_le (prefixLaw E (tails E) t) (law_nonneg E t)
      (fun x => loss (primes i) x + op (primes i) (cap (primes i)) (states i.succ).eval (E i) x)
      (states i.castSucc).eval (row_op i (row_certificate i) (E i))
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

/- The complete 366-prime finite-exponent hinge budget is below the
certified initial value, independently of all 366 exponent bounds. -/
theorem prefix_cost_bound (E : Fin 366 → ℕ) :
    (∑ i, exponentEnvelope E (tails E)
      (fun x => residual (cap (primes i)) (1/(primes i-1 : ℚ)*x+offset (primes i))) i.val 1) ≤
      (states 0).eval 1 := by
  have hh := prefix_potential E 366 le_rfl
  have hz : expect (prefixLaw E (tails E) 366) (states 366).eval=0 := by
    simp only [expect,Finsupp.sum,terminal_eval,mul_zero,Finset.sum_const_zero]
  change (∑ j ∈ Finset.range 366, lossAt E j) +
    expect (prefixLaw E (tails E) 366) (states 366).eval ≤ _ at hh
  rw [hz,add_zero] at hh
  apply le_trans (le_of_eq ?_) hh
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

#print axioms prefix_cost_bound
end Erdos7DirectFiveScalar
