import FormalConjecturesUtil

/-! A product restriction on closed collections of consecutive comparisons.
This is a finite divisibility estimate, not a signed-cancellation estimate. -/

namespace Erdos371CycleProduct

open Finset

lemma product_increment_bound {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (N : ℕ) (hn : ∀ i ∈ s, n i < N) :
    N * (∏ i ∈ s, (n i + 1)) ≤
      N * (∏ i ∈ s, n i) + s.card * N ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hna : n a < N := hn a (mem_insert_self _ _)
    have hns : ∀ i ∈ s, n i < N := fun i hi => hn i (mem_insert_of_mem hi)
    have hi := ih hns
    have hp : (∏ i ∈ s, (n i + 1)) ≤ N ^ s.card :=
      prod_le_pow_card s (fun i => n i + 1) N (fun i hi => hns i hi)
    have hmul := Nat.mul_le_mul_left (n a) hi
    have hmul' := Nat.mul_le_mul_left N hp
    have hcoeff := Nat.mul_le_mul_right (s.card * N ^ s.card) hna.le
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha, pow_succ]
    nlinarith

/-- If factors of the left endpoints, in some permutation, divide the right
endpoints as well, their whole product divides the positive product gap. -/
lemma permuted_factors_dvd_gap {ι : Type*} [Fintype ι]
    (n p : ι → ℕ) (σ : Equiv.Perm ι)
    (hl : ∀ i, p i ∣ n i) (hr : ∀ i, p (σ i) ∣ n i + 1) :
    (∏ i, p i) ∣ (∏ i, (n i + 1)) - ∏ i, n i := by
  have hleft : (∏ i, p i) ∣ ∏ i, n i :=
    prod_dvd_prod_of_dvd _ _ (fun i _ => hl i)
  have hright : (∏ i, p i) ∣ ∏ i, (n i + 1) := by
    have h := prod_dvd_prod_of_dvd (s := univ) _ _ (fun i _ => hr i)
    rw [Equiv.prod_comp σ p] at h
    exact h
  exact Nat.dvd_sub hright hleft

/-- No asymptotic distribution assumption is used. In particular, this
applies to the prime labels around any directed cycle of comparisons. -/
theorem closed_product_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (n p : ι → ℕ) (σ : Equiv.Perm ι) (N : ℕ)
    (hn : ∀ i, 0 < n i ∧ n i < N)
    (hl : ∀ i, p i ∣ n i) (hr : ∀ i, p (σ i) ∣ n i + 1) :
    (∏ i, p i) ≤ Fintype.card ι * N ^ (Fintype.card ι - 1) := by
  classical
  have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hN : 0 < N := (hn i).1.trans (hn i).2
  have hstrict : (∏ i, n i) < ∏ i, (n i + 1) := by
    apply Finset.prod_lt_prod (fun i _ => (hn i).1)
      (fun i _ => Nat.le_succ (n i))
    exact ⟨i, mem_univ _, Nat.lt_succ_self _⟩
  have hgap : (∏ i, p i) ≤ (∏ i, (n i + 1)) - ∏ i, n i :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hstrict)
      (permuted_factors_dvd_gap n p σ hl hr)
  have hb := product_increment_bound univ n N (fun i _ => (hn i).2)
  simp only [card_univ] at hb
  have hsub := Nat.sub_add_cancel hstrict.le
  have hmul := Nat.mul_le_mul_left N hgap
  have hexp : N ^ Fintype.card ι = N ^ (Fintype.card ι - 1) * N := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hexp] at hb
  apply Nat.le_of_mul_le_mul_left (c := N) _ hN
  nlinarith

/-- The specialisation to actual largest prime factors retains the exact
closed-collection hypothesis; it does not assert that such collections are
balanced by orientation. -/
theorem maxPrimeFac_closed_product_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ι → ℕ) (σ : Equiv.Perm ι) (N : ℕ)
    (hn : ∀ i, 0 < n i ∧ n i < N)
    (hcycle : ∀ i, Nat.maxPrimeFac (n (σ i)) = Nat.maxPrimeFac (n i + 1)) :
    (∏ i, Nat.maxPrimeFac (n i)) ≤
      Fintype.card ι * N ^ (Fintype.card ι - 1) := by
  apply closed_product_bound n (fun i => Nat.maxPrimeFac (n i)) σ N hn
  · exact fun _ => Nat.maxPrimeFac_dvd
  · intro i
    rw [hcycle i]
    exact Nat.maxPrimeFac_dvd


/-- A useful two-edge special case, with the exact product gap rather than
its upper bound by the counting range. -/
lemma reversed_pair_product_dvd {a b p q : ℕ}
    (hpa : p ∣ a) (hqa : q ∣ a + 1)
    (hqb : q ∣ b) (hpb : p ∣ b + 1) :
    p * q ∣ a + b + 1 := by
  have hl := Nat.mul_dvd_mul hpa hqb
  have hr : p * q ∣ (a + 1) * (b + 1) := by
    simpa only [Nat.mul_comm q p] using Nat.mul_dvd_mul hqa hpb
  have h := Nat.dvd_sub hr hl
  have he : (a + 1) * (b + 1) = a * b + (a + b + 1) := by ring
  simpa only [he, Nat.add_sub_cancel_left] using h

lemma reversed_pair_product_le {a b p q : ℕ}
    (hpa : p ∣ a) (hqa : q ∣ a + 1)
    (hqb : q ∣ b) (hpb : p ∣ b + 1) :
    p * q ≤ a + b + 1 :=
  Nat.le_of_dvd (by omega) (reversed_pair_product_dvd hpa hqa hqb hpb)

/-- Closed collections above a fixed threshold obey the resulting
length/product restriction. -/
theorem threshold_cycle_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (n p : ι → ℕ) (σ : Equiv.Perm ι) (N H : ℕ)
    (hn : ∀ i, 0 < n i ∧ n i < N)
    (hl : ∀ i, p i ∣ n i) (hr : ∀ i, p (σ i) ∣ n i + 1)
    (hp : ∀ i, H < p i) :
    (H + 1) ^ Fintype.card ι ≤
      Fintype.card ι * N ^ (Fintype.card ι - 1) := by
  have hprod : (H + 1) ^ Fintype.card ι ≤ ∏ i, p i := by
    calc
      _ = ∏ _i : ι, (H + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hp i)
  exact hprod.trans (closed_product_bound n p σ N hn hl hr)

/-- The product restriction is not itself a balance theorem: the actual
comparisons at inputs 2, 6 and 7 form a cycle with signed sum one. -/
lemma biased_closed_example :
    let n : Fin 3 → ℕ := ![2, 6, 7]
    let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
    (∀ i, Nat.maxPrimeFac (n (σ i)) = Nat.maxPrimeFac (n i + 1)) ∧
      (∑ i, if Nat.maxPrimeFac (n i) < Nat.maxPrimeFac (n i + 1)
        then (1 : ℤ) else -1) = 1 := by
  decide +kernel


end Erdos371CycleProduct

#print axioms Erdos371CycleProduct.closed_product_bound
#print axioms Erdos371CycleProduct.maxPrimeFac_closed_product_bound

#print axioms Erdos371CycleProduct.threshold_cycle_bound
#print axioms Erdos371CycleProduct.biased_closed_example
