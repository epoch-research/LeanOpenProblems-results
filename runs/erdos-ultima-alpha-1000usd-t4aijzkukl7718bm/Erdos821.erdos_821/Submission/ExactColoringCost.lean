import Submission.SquarefreeColoring

/-!
# Exact divisor-tuple cost for squarefree coloring

The number of possible ordered output tuples is the higher divisor function,
not a power of the ordinary divisor count. All extraction hypotheses below
remain explicit; this module does not assert a new multiplicity exponent.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta
namespace Erdos821
open HigherDivisors
set_option maxHeartbeats 3000000

lemma coloredFiber_add_le (r s n : ℕ) (hn : 0 < n) :
    coloredFiber (r+s) n ≤
      ∑ d ∈ n.divisors, coloredFiber r d * coloredFiber s (n/d) := by
  have H := squarefree_convolution_push_le ((ζ : ArithmeticFunction ℕ)^r)
    ((ζ : ArithmeticFunction ℕ)^s) n hn
  simpa only [← pow_add,coloredFiber,tau] using H

/-- Uniform in every positive integer number of colors. -/
theorem coloredFiber_le_tau_of_divisor_bound (C s : ℝ) (hC : 0 ≤ C)
    (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n)
    (H : ∀ d ∈ n.divisors, (g d : ℝ) ≤ C*(d : ℝ)^s) :
    (coloredFiber r n : ℝ) ≤ C^r*(n : ℝ)^s*(tau r n : ℝ) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  induction r generalizing n with
  | zero =>
    have ht : tau 1 n = 1 := by simp [tau,hn.ne']
    rw [ht,Nat.cast_one,mul_one,pow_one,coloredFiber_one]
    exact (show (gSquarefree n : ℝ) ≤ (g n : ℝ) by exact_mod_cast gSquarefree_le_g n).trans
      (H n (Nat.mem_divisors.mpr ⟨dvd_refl n,hn.ne'⟩))
  | succ r ih =>
    have hbound (d : ℕ) (hd : d ∈ n.divisors) :
        (coloredFiber (r+1) d : ℝ) ≤ C^(r+1)*(d : ℝ)^s*(tau (r+1) d : ℝ) :=
      ih d (Nat.pos_of_mem_divisors hd) (fun a ha =>
        H a (Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors ha).trans (Nat.dvd_of_mem_divisors hd),hn.ne'⟩)) (by omega)
    have hterm (d : ℕ) (hd : d ∈ n.divisors) :
        (coloredFiber (r+1) d : ℝ)*(coloredFiber 1 (n/d) : ℝ) ≤
          C^(r+1+1)*(n : ℝ)^s*(tau (r+1) d : ℝ) := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hnd : n/d ∈ n.divisors := Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd hdvd,hn.ne'⟩
      have hb : (coloredFiber 1 (n/d) : ℝ) ≤ C*((n/d : ℕ) : ℝ)^s := by
        rw [coloredFiber_one]
        exact (show (gSquarefree (n/d) : ℝ) ≤ (g (n/d) : ℝ) by
          exact_mod_cast gSquarefree_le_g (n/d)).trans (H (n/d) hnd)
      have hprod : (d : ℝ)*((n/d : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      calc
        _ ≤ (C^(r+1)*(d : ℝ)^s*(tau (r+1) d : ℝ)) *
            (C*((n/d : ℕ) : ℝ)^s) :=
          mul_le_mul (hbound d hd) hb (Nat.cast_nonneg _) (by positivity)
        _ = C^(r+1+1)*((d : ℝ)^s*((n/d : ℕ) : ℝ)^s)*(tau (r+1) d : ℝ) := by
          rw [_root_.pow_succ]; ring
        _ = _ := by rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),hprod]
    calc
      _ ≤ ∑ d ∈ n.divisors,
          (coloredFiber (r+1) d : ℝ)*(coloredFiber 1 (n/d) : ℝ) := by
        exact_mod_cast coloredFiber_add_le (r+1) 1 n hn
      _ ≤ ∑ d ∈ n.divisors, C^(r+1+1)*(n : ℝ)^s*(tau (r+1) d : ℝ) :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.mul_sum,← Nat.cast_sum,← tau_succ]

theorem coloredFiber_le_tau_of_power_bound (C s : ℝ) (hC : 0 ≤ C)
    (H : ∀ n : ℕ, 0 < n → (g n : ℝ) ≤ C*(n : ℝ)^s)
    (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    (coloredFiber r n : ℝ) ≤ C^r*(n : ℝ)^s*(tau r n : ℝ) :=
  coloredFiber_le_tau_of_divisor_bound C s hC r n hr hn
    (fun d hd => H d (Nat.pos_of_mem_divisors hd))

/-- The exact extraction test, without restricting r to a power of two. -/
theorem exists_divisor_large_g_of_exact_coloring
    (C s : ℝ) (hC : 0 ≤ C) (F : Finset ℕ) (n r k : ℕ)
    (hn : 0 < n) (hr : 1 ≤ r)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card)
    (hcolor : C^r*(n : ℝ)^s*(tau r n : ℝ) < (F.card : ℝ)*(r : ℝ)^k) :
    ∃ d ∈ n.divisors, C*(d : ℝ)^s < (g d : ℝ) := by
  by_contra H
  push_neg at H
  have hb := coloredFiber_le_tau_of_divisor_bound C s hC r n hr hn H
  have hl : (F.card : ℝ)*(r : ℝ)^k ≤ (coloredFiber r n : ℝ) := by
    exact_mod_cast finite_squarefree_fiber_color_lower F n r k hr hF
  exact hcolor.not_ge (hl.trans hb)

/-- A pointwise prime-exponent formula for the exact cost. -/
lemma tau_color_cost_product (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    tau r n = ∏ p ∈ n.primeFactors, (n.factorization p+r-1).choose (r-1) := by
  have heq : r-1+1 = r := Nat.sub_add_cancel hr
  have ht := (tau_multiplicative r).multiplicative_factorization
    ((ζ : ArithmeticFunction ℕ)^r) hn.ne'
  change tau r n = _ at ht
  rw [ht]
  simp only [Finsupp.prod,Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  change tau r (p^(n.factorization p)) = _
  rw [← heq,tau_prime_pow (r-1) (n.factorization p) p (Nat.prime_of_mem_primeFactors hp)]
  congr 1

end Erdos821
