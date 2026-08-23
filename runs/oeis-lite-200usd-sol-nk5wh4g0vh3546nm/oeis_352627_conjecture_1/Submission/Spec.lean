import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card


private def FormRep (n : ℕ) : Prop :=
  ∃ x y c d : ℕ, x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n

private lemma rep_mul_four {n : ℕ} (h : FormRep n) : FormRep (4 * n) := by
  rcases h with ⟨x, y, c, d, h⟩
  refine ⟨2 * x, 2 * y, 2 * d, c, ?_⟩
  rw [← h]
  ring

private lemma rep_of_core
    (hcore : ∀ n : ℕ, ¬ 4 ∣ n → FormRep n) : ∀ n : ℕ, FormRep n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h4 : 4 ∣ n
      · obtain ⟨m, rfl⟩ := h4
        rcases m.eq_zero_or_pos with rfl | hm
        · exact ⟨0, 0, 0, 0, by norm_num⟩
        · exact rep_mul_four (ih m (by omega))
      · exact hcore n h4

private lemma a_pos_of_rep {n x y c d : ℕ}
    (h : x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n) :
    0 < a n := by
  rw [a, Finset.card_pos]
  let p : ℕ × (ℕ × (ℕ × ℕ)) := (x, y, c, d)
  have hx2 : x ^ 2 ≤ n := by rw [← h]; omega
  have hy2 : y ^ 2 ≤ n := by rw [← h]; omega
  have hc2 : c ^ 2 ≤ n := by
    rw [← h]
    have hc : c ^ 2 ≤ c ^ 4 := by
      rw [show c ^ 4 = (c ^ 2) ^ 2 by ring]
      exact Nat.le_pow (by omega)
    omega
  have hd2 : d ^ 2 ≤ n := by
    rw [← h]
    have hd : d ^ 2 ≤ d ^ 4 := by
      rw [show d ^ 4 = (d ^ 2) ^ 2 by ring]
      exact Nat.le_pow (by omega)
    omega
  have hx : x < sqrt n + 1 := by
    rw [Nat.lt_add_one_iff]
    exact (Nat.le_sqrt).2 (by simpa [pow_two] using hx2)
  have hy : y < sqrt n + 1 := by
    rw [Nat.lt_add_one_iff]
    exact (Nat.le_sqrt).2 (by simpa [pow_two] using hy2)
  have hc : c < sqrt n + 1 := by
    rw [Nat.lt_add_one_iff]
    exact (Nat.le_sqrt).2 (by simpa [pow_two] using hc2)
  have hd : d < sqrt n + 1 := by
    rw [Nat.lt_add_one_iff]
    exact (Nat.le_sqrt).2 (by simpa [pow_two] using hd2)
  refine ⟨p, ?_⟩
  simp [p, hx, hy, hc, hd, h]

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  sorry
