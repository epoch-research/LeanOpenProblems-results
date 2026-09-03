import FormalConjecturesUtil

/-! A candidate resource budget for the signature method. This file proves
 only the numerical budget, NOT that minimal-core events can be charged to it.
 That missing charging theorem would be needed to use it on Erdős 7. -/
namespace Erdos7SignatureResourceBudget
open scoped BigOperators
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def weight (p : ℕ) : ℝ := 2 / ((p : ℝ) - 2)^2

def budget (s : Finset ℕ) : ℝ := (∏ p ∈ s, (1 + weight p)) - 1 - ∑ p ∈ s, weight p

def primePrefix : Finset ℕ := {3,5,7,11,13,17,19,23,29,31,37}

lemma weight_nonneg (p : ℕ) : 0 ≤ weight p := div_nonneg (by norm_num) (sq_nonneg _)

lemma budget_insert (s : Finset ℕ) (p : ℕ) (hp : p ∉ s) :
    budget (insert p s) = budget s + weight p * ((∏ q ∈ s, (1 + weight q)) - 1) := by
  simp only [budget, prod_insert hp, sum_insert hp]
  ring

lemma product_one_le (s : Finset ℕ) : 1 ≤ ∏ p ∈ s, (1 + weight p) :=
  one_le_prod s (fun p => by have := weight_nonneg p; linarith)

lemma budget_mono {s t : Finset ℕ} (h : s ⊆ t) : budget s ≤ budget t := by
  classical
  apply (Finset.monotone_iff_forall_le_insert.mpr ?_ : Monotone budget) h
  intro s a ha
  rw [budget_insert s a ha]
  have := mul_nonneg (weight_nonneg a) (sub_nonneg.mpr (product_one_le s))
  linarith

/-- A geometric upper bound on a finite product; no exponential estimate. -/
lemma product_budget {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hS : ∑ i ∈ s, w i < 1) :
    (∏ i ∈ s, (1 + w i)) ≤ 1 / (1 - ∑ i ∈ s, w i) := by
  classical
  have main : (1 - ∑ i ∈ s, w i) * (∏ i ∈ s, (1 + w i)) ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have hwₐ := hw a (mem_insert_self a s)
      have hwₛ : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, w i := sum_nonneg hwₛ
      have hSₛ : ∑ i ∈ s, w i < 1 := by rw [sum_insert ha] at hS; linarith
      have hi := ih hwₛ hSₛ
      have hP : 0 ≤ ∏ i ∈ s, (1 + w i) := prod_nonneg (fun i hi => by have := hwₛ i hi; linarith)
      rw [sum_insert ha, prod_insert ha]
      calc
        (1 - (w a + ∑ i ∈ s, w i)) * ((1 + w a) * ∏ i ∈ s, (1 + w i))
          ≤ (1 - ∑ i ∈ s, w i) * ∏ i ∈ s, (1 + w i) := by
            have hlocal : (1 - (w a + ∑ i ∈ s, w i)) * (1 + w a) ≤
                1 - ∑ i ∈ s, w i := by nlinarith [mul_nonneg hwₐ hsum, sq_nonneg (w a)]
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlocal hP
        _ ≤ 1 := hi
  exact (le_div_iff₀ (by linarith : 0 < 1 - ∑ i ∈ s, w i)).mpr (by nlinarith [main])

/-- Telescoping comparison at all odd integers >=39, not just at primes. -/
lemma odd_weight_bound (k : ℕ) :
    weight (39 + 2*k) ≤ 1 / (36 + 2*(k : ℝ)) - 1 / (38 + 2*(k : ℝ)) := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  dsimp [weight]
  push_cast
  have h36 : 0 < 36 + 2*(k : ℝ) := by positivity
  have h38 : 0 < 38 + 2*(k : ℝ) := by positivity
  have h37 : 0 < 39 + 2*(k : ℝ) - 2 := by linarith
  field_simp
  nlinarith [sq_nonneg (k : ℝ)]

lemma initial_telescope (n : ℕ) :
    ∑ k ∈ range n, (1 / (36 + 2*(k : ℝ)) - 1 / (38 + 2*(k : ℝ))) =
      1/36 - 1/(36+2*(n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    have he : 36 + 2*((n : ℝ)+1) = 38 + 2*(n : ℝ) := by ring
    rw [he]
    ring

lemma tail_sum (s : Finset ℕ) (hs : ∀ p ∈ s, 38 ≤ p ∧ Odd p) :
    ∑ p ∈ s, weight p ≤ 1/36 := by
  classical
  let index (p : ℕ) := (p-39)/2
  have rep (p : ℕ) (hp : p ∈ s) : p = 39 + 2*index p := by
    obtain ⟨hp, k, hk⟩ := hs p hp
    dsimp [index]
    omega
  have hinj : Set.InjOn index s := by
    intro p hp q hq he
    rw [rep p hp, rep q hq, he]
  let t := s.image index
  have hsub : t ⊆ range (t.sup id + 1) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  calc
    (∑ p ∈ s, weight p) = ∑ p ∈ s, weight (39+2*index p) :=
      sum_congr rfl (fun p hp => congrArg weight (rep p hp))
    _ = ∑ k ∈ t, weight (39+2*k) := (sum_image (f := fun k => weight (39+2*k)) hinj).symm
    _ ≤ ∑ k ∈ t, (1/(36+2*(k : ℝ)) - 1/(38+2*(k : ℝ))) :=
      sum_le_sum (fun k _ => odd_weight_bound k)
    _ ≤ ∑ k ∈ range (t.sup id + 1), (1/(36+2*(k : ℝ)) - 1/(38+2*(k : ℝ))) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro k _ _
      have := weight_nonneg (39+2*k)
      linarith [odd_weight_bound k]
    _ ≤ 1/36 := by
      rw [initial_telescope]
      have : 0 ≤ 1/(36+2*((t.sup id + 1 : ℕ) : ℝ)) := by positivity
      linarith

lemma prefix_check :
    ((∏ p ∈ primePrefix, (1 + weight p)) * (36/35) - 1 - ∑ p ∈ primePrefix, weight p) < 1 := by
  norm_num [primePrefix, weight]

lemma small_prime (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hb : p < 38) : p ∈ primePrefix := by
  interval_cases p <;> norm_num [primePrefix] at *

/-- This is ONLY a resource-sum bound. No inequality relating it to the union
of actual minimal-core events is asserted in this file. -/
theorem budget_lt_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) : budget s < 1 := by
  classical
  let t := s \ primePrefix
  have ht : ∀ p ∈ t, 38 ≤ p ∧ Odd p := by
    intro p hp
    obtain ⟨hps, hpref⟩ := mem_sdiff.mp hp
    have hh := hs p hps
    exact ⟨by by_contra! h; exact hpref (small_prime p hh.1 hh.2 h), hh.1.odd_of_ne_two (by omega)⟩
  have hsum := tail_sum t ht
  have hp : ∏ p ∈ t, (1 + weight p) ≤ 36/35 := by
    apply (product_budget t weight (fun p _ => weight_nonneg p) (by linarith)).trans
    have h0 : 0 < 1 - ∑ p ∈ t, weight p := by linarith
    apply (div_le_iff₀ h0).mpr
    linarith
  have hd : Disjoint primePrefix t := by
    apply Finset.disjoint_left.mpr
    intro p hp ht
    exact (mem_sdiff.mp ht).2 hp
  have hsub : s ⊆ primePrefix ∪ t := by intro p hp; by_cases hh : p ∈ primePrefix <;> simp_all [t]
  apply (budget_mono hsub).trans_lt
  calc
    budget (primePrefix ∪ t) =
        (∏ p ∈ primePrefix, (1 + weight p)) * (∏ p ∈ t, (1 + weight p)) - 1 -
          (∑ p ∈ primePrefix, weight p) - ∑ p ∈ t, weight p := by
      rw [budget, prod_union hd, sum_union hd]
      ring
    _ ≤ (∏ p ∈ primePrefix, (1 + weight p)) * (36/35) - 1 - ∑ p ∈ primePrefix, weight p := by
      have hpn : 0 ≤ ∏ p ∈ primePrefix, (1+weight p) := (product_one_le primePrefix).trans' (by norm_num)
      have hm := mul_le_mul_of_nonneg_left hp hpn
      have ht0 := sum_nonneg (fun p (_ : p ∈ t) => weight_nonneg p)
      linarith
    _ < 1 := prefix_check

#print axioms budget_lt_one
end
end Erdos7SignatureResourceBudget
