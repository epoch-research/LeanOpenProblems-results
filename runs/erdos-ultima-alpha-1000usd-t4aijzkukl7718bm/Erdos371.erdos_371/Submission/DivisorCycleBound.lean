import FormalConjecturesUtil

/-! A finite size obstruction to short directed divisor cycles. This is not
an estimate for the density of largest-prime-factor comparisons. -/

namespace Erdos371
open Finset

/-- Increasing all entries increases the product's increment under translation
by one. This avoids subtracting two unrelated product inequalities. -/
lemma prod_succ_sub_prod_mono {ι : Type*} (s : Finset ι) (f g : ι → ℕ)
    (h : ∀ i ∈ s, f i ≤ g i) :
    (∏ i ∈ s, (f i + 1)) - (∏ i ∈ s, f i) ≤
      (∏ i ∈ s, (g i + 1)) - (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi' := h i (mem_insert_self i s)
    have hs : ∀ j ∈ s, f j ≤ g j := fun j hj => h j (mem_insert_of_mem hj)
    have ih' := ih hs
    have hA : (∏ j ∈ s, f j) ≤ ∏ j ∈ s, (f j+1) :=
      prod_le_prod' (fun j _ => Nat.le_succ _)
    have hB : (∏ j ∈ s, g j) ≤ ∏ j ∈ s, (g j+1) :=
      prod_le_prod' (fun j _ => Nat.le_succ _)
    have hC : (∏ j ∈ s, (f j+1)) ≤ ∏ j ∈ s, (g j+1) :=
      prod_le_prod' (fun j hj => Nat.succ_le_succ (hs j hj))
    have hd (a A B : ℕ) (hAB : B ≤ A) :
        (a+1)*A-a*B = a*(A-B)+A := by
      have hh := Nat.sub_add_cancel hAB
      have hh' : a*B ≤ (a+1)*A := by nlinarith
      have hh'' := Nat.sub_add_cancel hh'
      nlinarith
    simp only [prod_insert hi]
    rw [hd _ _ _ hA, hd _ _ _ hB]
    exact Nat.add_le_add (Nat.mul_le_mul hi' ih') hC

/-- A uniform upper bound on the increment of a product. -/
lemma prod_succ_sub_prod_le_pow_difference {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (N : ℕ) (hn : ∀ i ∈ s, n i ≤ N) :
    (∏ i ∈ s, (n i+1)) - (∏ i ∈ s, n i) ≤ (N+1)^s.card-N^s.card := by
  simpa using prod_succ_sub_prod_mono s n (fun _ => N) hn

lemma nat_succ_pow_sub_pow_le (N k : ℕ) :
    (N+1)^k-N^k ≤ k*(N+1)^(k-1) := by
  have h := abs_pow_sub_pow_le (a := (N+1 : ℤ)) (b := (N : ℤ)) (n := k)
  have hpow : (N : ℤ)^k ≤ (N+1 : ℤ)^k := by gcongr; omega
  rw [abs_of_nonneg (sub_nonneg.mpr hpow)] at h
  simp only [add_sub_cancel_left, abs_one] at h
  rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ N+1),
    abs_of_nonneg (by positivity : (0 : ℤ) ≤ N), max_eq_left (by omega)] at h
  have hpow' : N^k ≤ (N+1)^k := by gcongr; omega
  simp only [one_mul] at h
  exact_mod_cast h

/-- Around a directed divisor cycle, the product of the labels divides the
positive difference between the two products of incident consecutive integers.
No primality assumption is needed. -/
theorem divisor_cycle_product_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (n p : ι → ℕ) (N : ℕ)
    (hn : ∀ i, 0 < n i) (hnN : ∀ i, n i ≤ N)
    (hp : ∀ i, p i ∣ n i) (hnext : ∀ i, p (σ i) ∣ n i+1) :
    (∏ i, p i) ≤ (N+1)^Fintype.card ι-N^Fintype.card ι := by
  have hd₁ : (∏ i, p i) ∣ ∏ i, n i := prod_dvd_prod_of_dvd p n (fun i _ => hp i)
  have hd₂ : (∏ i, p i) ∣ ∏ i, (n i+1) := by
    have hh := prod_dvd_prod_of_dvd (fun i => p (σ i)) (fun i => n i+1)
      (s := univ) (fun i _ => hnext i)
    simpa only [Equiv.prod_comp] using hh
  have hpos : (∏ i, n i) < ∏ i, (n i+1) :=
    prod_lt_prod_of_nonempty (fun i _ => hn i) (fun i _ => Nat.lt_succ_self _)
      univ_nonempty
  exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hpos) (Nat.dvd_sub hd₂ hd₁)).trans
    (prod_succ_sub_prod_le_pow_difference univ n N (fun i _ => hnN i))

/-- In particular, a cycle of length k has product of labels at most
k*(N+1)^(k-1). This only excludes short cycles in a high-label range. -/
theorem divisor_cycle_product_bound' {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι ≃ ι) (n p : ι → ℕ) (N : ℕ)
    (hn : ∀ i, 0 < n i) (hnN : ∀ i, n i ≤ N)
    (hp : ∀ i, p i ∣ n i) (hnext : ∀ i, p (σ i) ∣ n i+1) :
    (∏ i, p i) ≤ Fintype.card ι*(N+1)^(Fintype.card ι-1) :=
  (divisor_cycle_product_bound σ n p N hn hnN hp hnext).trans
    (nat_succ_pow_sub_pow_le N (Fintype.card ι))

#print axioms divisor_cycle_product_bound
#print axioms divisor_cycle_product_bound'
end Erdos371
