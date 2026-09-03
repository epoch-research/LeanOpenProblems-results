import Submission.Valuation

/-!
# A constant bound when four does not divide the output

This restricted-family upper bound does not settle the full conjecture.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma admissibleSupport_erase_two_card_le_one {n : ℕ} (h4 : ¬4 ∣ n)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) : (S.erase 2).card ≤ 1 := by
  classical
  obtain ⟨hSp, hprod, _⟩ := Finset.mem_filter.mp hS
  have hsub := Finset.mem_powerset.mp hSp
  have htwo : 2 ^ (S.erase 2).card ∣ ∏ p ∈ S.erase 2, (p - 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨hp2, hpS⟩ := Finset.mem_erase.mp hp
    exact ((Finset.mem_filter.mp (hsub hpS)).2.1.even_sub_one hp2).two_dvd
  have hdiv : 2 ^ (S.erase 2).card ∣ n := htwo.trans
    ((Finset.prod_dvd_prod_of_subset (S.erase 2) S (fun p => p - 1)
      (Finset.erase_subset 2 S)).trans hprod)
  by_contra h
  apply h4
  have hp : (2 : ℕ) ^ 2 ∣ 2 ^ (S.erase 2).card := pow_dvd_pow 2 (by omega)
  exact hp.trans hdiv

lemma admissibleSupport_odd_unique {n : ℕ} (h4 : ¬4 ∣ n)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) {p q : ℕ}
    (hp : p ∈ S) (hq : q ∈ S) (hp2 : p ≠ 2) (hq2 : q ≠ 2) : p = q := by
  exact Finset.card_le_one_iff.mp (admissibleSupport_erase_two_card_le_one h4 hS)
    (Finset.mem_erase.mpr ⟨hp2, hp⟩) (Finset.mem_erase.mpr ⟨hq2, hq⟩)

/-- The only possible odd support prime is either `n+1` or the largest
prime factor of `n`. -/
lemma odd_support_prime_candidates {n : ℕ} (h4 : ¬4 ∣ n)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) {p : ℕ}
    (hp : p ∈ S) (hp2 : p ≠ 2) : p = n + 1 ∨ p = n.primeFactors.sup id := by
  classical
  have hn0 : n ≠ 0 := by intro h; exact h4 (h ▸ dvd_zero _)
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  obtain ⟨hSp, hAdvd, hqsub⟩ := Finset.mem_filter.mp hS
  have hsub := Finset.mem_powerset.mp hSp
  have hpprime := (Finset.mem_filter.mp (hsub hp)).2.1
  have hpredpos : 0 < p - 1 := Nat.sub_pos_of_lt hpprime.one_lt
  have hchoices : ∀ q ∈ S, q = 2 ∨ q = p := by
    intro q hq
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · exact Or.inr (admissibleSupport_odd_unique h4 hS hq hp hq2 hp2)
  have hprod : (∏ q ∈ S, (q - 1)) = p - 1 := by
    apply Finset.prod_eq_single p
    · intro q hq hqp
      have hq2 := (hchoices q hq).resolve_right hqp
      simp [hq2]
    · intro h
      exact (h hp).elim
  rw [hprod] at hAdvd hqsub
  let Q := n / (p - 1)
  have hQpos : 0 < Q := Nat.div_pos (Nat.le_of_dvd hn hAdvd) hpredpos
  have heq : (p - 1) * Q = n := Nat.mul_div_cancel' hAdvd
  have hQdvd : Q ∣ n := Nat.div_dvd_of_dvd hAdvd
  by_cases hpn : p ∣ n
  · right
    apply le_antisymm
    · exact Finset.le_sup (f := id) (hpprime.mem_primeFactors hpn hn0)
    · apply Finset.sup_le
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqd : q ∣ (p - 1) * Q := heq.symm ▸ Nat.dvd_of_mem_primeFactors hq
      rcases hqp.dvd_mul.mp hqd with hqa | hqb
      · exact (Nat.le_of_dvd hpredpos hqa).trans (Nat.sub_le _ _)
      · have hqS := hqsub (hqp.mem_primeFactors hqb hQpos.ne')
        rcases hchoices q hqS with rfl | rfl
        · exact hpprime.two_le
        · exact le_rfl
  · left
    have hQempty : Q.primeFactors = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      rcases hchoices q (hqsub hq) with rfl | rfl
      · apply h4
        have hd := Nat.mul_dvd_mul (hpprime.even_sub_one hp2).two_dvd
          (Nat.dvd_of_mem_primeFactors hq)
        simpa only [heq] using hd
      · exact hpn ((Nat.dvd_of_mem_primeFactors hq).trans hQdvd)
    have hQone : Q = 1 := (Nat.primeFactors_eq_empty.mp hQempty).resolve_left hQpos.ne'
    rw [hQone, mul_one] at heq
    omega

lemma admissibleSupport_has_odd_prime_of_two_lt {n : ℕ} (hn : 2 < n) (h4 : ¬4 ∣ n)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) : ∃ p ∈ S, p ≠ 2 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨_, _, hqsub⟩ := Finset.mem_filter.mp hS
  have hprod : (∏ p ∈ S, (p - 1)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    simp [h p hp]
  rw [hprod, Nat.div_one] at hqsub
  obtain ⟨q, hqprime, hqdvd, hqodd⟩ :=
    (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn).resolve_left h4
  have hqS := hqsub (hqprime.mem_primeFactors hqdvd (by omega))
  have hq2 := h q hqS
  subst q
  norm_num at hqodd

/-- A uniform constant bound on all outputs not divisible by four. -/
lemma g_le_four_of_not_four_dvd {n : ℕ} (h4 : ¬4 ∣ n) : g n ≤ 4 := by
  classical
  have hn0 : n ≠ 0 := by intro h; exact h4 (h ▸ dvd_zero _)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hn : n ≤ 2
  · have hg := g_le_two_pow_shifted_prime_divisors n
    interval_cases n <;> norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton] at hg <;> omega
  have hn2 : 2 < n := by omega
  let a := n + 1
  let b := n.primeFactors.sup id
  let F : Finset (Finset ℕ) := [{a}, {2, a}, {b}, {2, b}].toFinset
  have hsub : admissibleSupports n ⊆ F := by
    intro S hS
    obtain ⟨p, hp, hp2⟩ := admissibleSupport_has_odd_prime_of_two_lt hn2 h4 hS
    have hcan : p = a ∨ p = b := odd_support_prime_candidates h4 hS hp hp2
    have hshape : S = {p} ∨ S = {2, p} := by
      by_cases htwo : 2 ∈ S
      · right
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hq
          by_cases hq2 : q = 2
          · exact Or.inl hq2
          · exact Or.inr (admissibleSupport_odd_unique h4 hS hq hp hq2 hp2)
        · rintro (rfl | rfl) <;> assumption
      · left
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hp, ?_⟩
        intro q hq
        have hq2 : q ≠ 2 := by intro h; subst q; exact htwo hq
        exact admissibleSupport_odd_unique h4 hS hq hp hq2 hp2
    rcases hcan with hpa | hpb <;> rcases hshape with hS1 | hS2 <;>
      simp_all [F]
  rw [g_eq_card_admissibleSupports (by omega)]
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)

lemma g_le_four_of_squarefree {n : ℕ} (hn : Squarefree n) : g n ≤ 4 := by
  apply g_le_four_of_not_four_dvd
  intro h4
  have hpow : (2 : ℕ) ^ 2 ∣ n := h4
  have hval := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne_zero).mp hpow
  have hval' := hn.natFactorization_le_one 2
  omega

/-- The constant four in the restricted-family bound is attained. -/
lemma g_six_eq_four : g 6 = 4 := by
  have hsub : (↑({7, 9, 14, 18} : Finset ℕ) : Set ℕ) ⊆ {m : ℕ | totient m = 6} := by
    intro m hm
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide
  have hlow := Set.ncard_le_ncard hsub (finite_totient_fiber 6)
  change (↑({7, 9, 14, 18} : Finset ℕ) : Set ℕ).ncard ≤ g 6 at hlow
  rw [Set.ncard_coe_finset] at hlow
  have hcard : ({7, 9, 14, 18} : Finset ℕ).card = 4 := by decide
  rw [hcard] at hlow
  exact le_antisymm (g_le_four_of_not_four_dvd (by decide)) hlow

#print axioms g_le_four_of_not_four_dvd
#print axioms g_le_four_of_squarefree
#print axioms g_six_eq_four

end Erdos821
