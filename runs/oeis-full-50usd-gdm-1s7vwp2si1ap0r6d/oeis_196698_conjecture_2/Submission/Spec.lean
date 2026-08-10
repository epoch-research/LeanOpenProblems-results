import FormalConjectures.Util.ProblemImports


open Nat

/--
A196698: Number of primes of the form $3^n \pm 3^k \pm 1$ with $0 \le k < n$.
-/
def A196698 (n : ℕ) : ℕ :=
  let p3n := 3 ^ n
  (Finset.range n).biUnion (fun k =>
    let p3k := 3 ^ k
    -- The four terms $3^n \pm 3^k \pm 1$:
    { p3n + p3k + 1,
      p3n + p3k - 1,
      p3n - p3k + 1,
      p3n - p3k - 1 }
  )
  |>.filter Nat.Prime
  |>.card

lemma A196698_ne_zero_of_mem (n : ℕ) (k : ℕ) (p : ℕ) (hk : k < n) (hp : p.Prime)
    (h_mem : p ∈ ({ 3^n + 3^k + 1, 3^n + 3^k - 1, 3^n - 3^k + 1, 3^n - 3^k - 1 } : Finset ℕ)) :
    A196698 n ≠ 0 := by
  unfold A196698
  apply Finset.card_ne_zero_of_mem (a := p)
  rw [Finset.mem_filter]
  refine ⟨?_, hp⟩
  rw [Finset.mem_biUnion]
  refine ⟨k, ?_, ?_⟩
  · rwa [Finset.mem_range]
  · exact h_mem

lemma A196698_one_ne_zero : A196698 1 ≠ 0 :=
  A196698_ne_zero_of_mem 1 0 5 (by decide) (by decide) (by decide)

lemma A196698_two_ne_zero : A196698 2 ≠ 0 :=
  A196698_ne_zero_of_mem 2 1 5 (by decide) (by decide) (by decide)
lemma A196698_three_ne_zero : A196698 3 ≠ 0 :=
  A196698_ne_zero_of_mem 3 2 17 (by decide) (by decide) (by decide)
lemma A196698_four_ne_zero : A196698 4 ≠ 0 :=
  A196698_ne_zero_of_mem 4 3 53 (by decide) (by decide) (by decide)
lemma A196698_five_ne_zero : A196698 5 ≠ 0 := by
  have h1 : 4 < 5 := by decide
  have h2 : Nat.Prime 163 := by norm_num
  have h3 : (163 : ℕ) ∈ ({ 3^5 + 3^4 + 1, 3^5 + 3^4 - 1, 3^5 - 3^4 + 1, 3^5 - 3^4 - 1 } : Finset ℕ) := by decide
  exact A196698_ne_zero_of_mem 5 4 163 h1 h2 h3
theorem oeis_196698_conjecture_2.disproof : ¬ (∀ M : ℕ, ∃ n : ℕ, n > M ∧ A196698 n = 0) := answer(sorry)

#print axioms oeis_196698_conjecture_2.disproof