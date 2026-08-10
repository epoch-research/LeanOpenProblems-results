import FormalConjectures.Util.ProblemImports

open Nat

def remove_gt_5 (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (· ≤ 5), p ^ (n.factorization p)

theorem remove_gt_5_mul_prime {p n : ℕ} (hp : Nat.Prime p) (hp_gt_5 : p > 5) (hn_pos : n > 0) :
    remove_gt_5 (p * n) = remove_gt_5 n := by
  have hp_ne_zero : p ≠ 0 := hp.ne_zero
  have hn_ne_zero : n ≠ 0 := _root_.ne_of_gt hn_pos
  unfold remove_gt_5
  have h_factors : (p * n).primeFactors = p.primeFactors ∪ n.primeFactors := Nat.primeFactors_mul hp_ne_zero hn_ne_zero
  rw [h_factors]
  have h_filter : (p.primeFactors ∪ n.primeFactors).filter (· ≤ 5) = n.primeFactors.filter (· ≤ 5) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h_or, hq⟩
      constructor
      · cases h_or with
        | inl h_qp =>
          have : q = p := by
            have h_mem : q ∈ p.primeFactors := h_qp
            rw [Nat.mem_primeFactors] at h_mem
            exact (hp.eq_one_or_self_of_dvd q h_mem.2.1).resolve_left (Nat.Prime.ne_one h_mem.1)
          subst this
          omega
        | inr h_qn =>
          exact h_qn
      · exact hq
    · intro ⟨h_qn, hq⟩
      constructor
      · exact Or.inr h_qn
      · exact hq
  rw [h_filter]
  refine Finset.prod_congr rfl (fun q hq ↦ ?_)
  have h_q_mem : q ∈ n.primeFactors.filter (· ≤ 5) := hq
  simp only [Finset.mem_filter] at h_q_mem
  have h_q_in : q ∈ n.primeFactors := h_q_mem.1
  have hq_le_5 : q ≤ 5 := h_q_mem.2
  have h_fac_mul : (p * n).factorization q = p.factorization q + n.factorization q := by
    rw [Nat.factorization_mul hp_ne_zero hn_ne_zero]
    rfl
  rw [h_fac_mul]
  have hp_fac : p.factorization q = 0 := by
    by_cases h_qp : q = p
    · subst h_qp
      omega
    · have h_q_prime : q.Prime := Nat.prime_of_mem_primeFactors h_q_in
      have h_not_dvd : ¬ q ∣ p := by
        intro h_dvd
        have h_eq : p = q := (hp.dvd_iff_eq h_q_prime.ne_one).mp h_dvd
        exact h_qp h_eq.symm
      exact Nat.factorization_eq_zero_of_not_dvd h_not_dvd
  rw [hp_fac, zero_add]



