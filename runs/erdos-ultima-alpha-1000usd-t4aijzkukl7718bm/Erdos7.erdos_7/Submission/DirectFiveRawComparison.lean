import Submission.DirectFiveHybrid

/-! Only the modified factor at five needs to enlarge the old raw tail. -/
namespace Erdos7DirectFiveRawComparison
open scoped BigOperators
open Erdos7DirectFiveScalar
open Erdos7DoubleExceptionHybrid (raw)
set_option maxHeartbeats 4000000

def multiplier (p : ℕ) : ℚ := 1+cap p*(3*(p : ℚ)-1)/(p-1)^2

lemma multiplier_nonneg (p : ℕ) (hp : 5 ≤ p) : 0 ≤ multiplier p := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hc := (cap_bounds p).1
  unfold multiplier
  exact add_nonneg (by norm_num) (div_nonneg
    (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _))

lemma multiplier_le (p : ℕ) (hp : 5 ≤ p) (h5 : p≠5) :
    multiplier p ≤ Erdos7No23Sieve.multiplier p := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hc : cap p ≤ (5/4 : ℚ) := by
    unfold cap
    rw [if_neg h5]
  have hm : cap p*(3*(p : ℚ)-1) ≤ (5/4 : ℚ)*(3*(p : ℚ)-1) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  simpa only [multiplier,Erdos7No23Sieve.multiplier,add_comm] using
    add_le_add_left (div_le_div_of_nonneg_right hm (sq_nonneg ((p : ℚ)-1))) 1

lemma multiplier_product_le {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 5 ≤ p i)
    (hpi : Function.Injective p) (j₀ : Fin n) (h5 : p j₀=5)
    (S : Finset (Fin n)) (hS : j₀∈S) :
    (∏ j∈S, multiplier (p j)) ≤ (88/67 : ℚ)*(∏ j∈S, Erdos7No23Sieve.multiplier (p j)) := by
  classical
  have hh : (∏ j∈S, multiplier (p j)) ≤
      ∏ j∈S, (if j=j₀ then (88/67 : ℚ) else 1)*Erdos7No23Sieve.multiplier (p j) := by
    apply Finset.prod_le_prod
    · intro j _; exact multiplier_nonneg (p j) (hp j)
    · intro j _
      by_cases hj : j=j₀
      · subst j
        norm_num [h5,multiplier,cap,Erdos7No23Sieve.multiplier]
      · rw [if_neg hj,one_mul]
        apply multiplier_le (p j) (hp j)
        intro h
        exact hj (hpi (h.trans h5.symm))
  rw [Finset.prod_mul_distrib] at hh
  simpa [hS] using hh

lemma raw_tail_bound {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 5 ≤ p i)
    (hpi : Function.Injective p) (j₀ : Fin n) (h5 : p j₀=5)
    (i : Fin n) (hji : j₀ < i) (hi : 7 < p i) :
    (cap (p i))^2/(4*(cap (p i)-1)) * (1/(p i-1 : ℚ)^2 *
      ∏ j∈Finset.univ.filter (fun j => j < i),
        (1+cap (p j)*(3*(p j : ℚ)-1)/(p j-1)^2)) ≤ (88/67 : ℚ)*raw p i := by
  have hc : cap (p i)=(5/4 : ℚ) := by
    have hne5 : p i≠5 := by omega
    have hne7 : p i≠7 := by omega
    simp [cap,hne5,hne7]
  have hpQ : (5 : ℚ) ≤ p i := by exact_mod_cast hp i
  have hh := multiplier_product_le p hp hpi j₀ h5
    (Finset.univ.filter (fun j => j < i)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji⟩)
  have hz : (0 : ℚ) ≤ (25/16)/(p i-1 : ℚ)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hh hz
  rw [hc]
  unfold raw Erdos7No23Sieve.charge
  dsimp only [multiplier] at hmul
  convert hmul using 1 <;> norm_num <;> ring

#print axioms raw_tail_bound
end Erdos7DirectFiveRawComparison
