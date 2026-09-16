import FormalConjectures.Util.ProblemImports

open Nat Finset Set

def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }

theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by
  intro n
  constructor
  · intro h
    by_cases hn : n = 4
    · exact hn
    · -- The case n ≠ 4 implies A078729 n = 0, which means P_n(k) + 1 is composite for all k > 0.
      -- By Schur's theorem, P_n(k) + 1 is irreducible for n ≠ 4.
      -- Furthermore, it has no fixed prime divisor.
      -- Thus, by Bunyakovsky's conjecture / Schinzel's Hypothesis H, it must take infinitely many prime values.
      -- Consequently, A078729 n > 0 for all n ≠ 4.
      -- Since Bunyakovsky's conjecture is an open mathematical problem, a formal proof of this direction
      -- is currently impossible in Lean without resolving the conjecture.
      sorry
  · intro h
    subst h
    have H : { k : ℕ | k > 0 ∧ (A078729_product 4 k + 1).Prime } = ∅ := by
      ext k
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hk
      have h1 : A078729_product 4 k = (k+1)*(k+2)*(k+3)*(k+4) := by
        dsimp [A078729_product]
        repeat rw [prod_range_succ]
        rw [prod_range_zero, one_mul]
        ring
      have h2 : A078729_product 4 k + 1 = (k^2+5*k+5)^2 := by
        rw [h1]
        ring
      rw [h2]
      intro h_prime
      have h3 : k^2+5*k+5 > 1 := by nlinarith
      have h4 := Prime.eq_one_or_self_of_dvd h_prime (k^2+5*k+5) (by
        use k^2+5*k+5
        ring
      )
      cases h4 with
      | inl h5 => linarith
      | inr h6 =>
        have h7 : (k^2+5*k+5)^2 = k^2+5*k+5 := h6.symm
        nlinarith
    rw [A078729, H, Nat.sInf_empty]

theorem oeis_78729_conjecture_0.disproof : ¬ (∀ n : ℕ, A078729 n = 0 ↔ n = 4) := by
  sorry
