import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

lemma a_find_min_m_eq_zero_iff (n : ℕ) (is_evil : ℕ → Bool) :
    ∀ m, 0 < m →
      (a.find_min_m n is_evil m = 0 ↔
        ∀ j, m ≤ j → j ≤ n → is_evil (n.choose j) = false) := by
  intro m hm
  induction m using a.find_min_m.induct n is_evil with
  | case1 x hx =>
      rw [a.find_min_m.eq_1]
      simp [hx]
      intro j hj hjn
      omega
  | case2 x hx he =>
      rw [a.find_min_m.eq_1]
      simp [hx, he]
      constructor
      · intro hx0
        omega
      · intro h
        have := h x (le_refl x) (by omega)
        simp [he] at this
  | case3 x hx he ih =>
      rw [a.find_min_m.eq_1]
      simp [hx, he]
      rw [ih (by omega)]
      constructor
      · intro h j hxj hjn
        by_cases hxx : j = x
        · subst hxx
          exact by simpa using he
        · exact h j (by omega) hjn
      · intro h j hj hjn
        exact h j (by omega) hjn

lemma a_eq_zero_iff_all_odious (n : ℕ) :
    a n = 0 ↔ ∀ j, 1 ≤ j → j ≤ n → (n.choose j).bits.count true % 2 ≠ 0 := by
  rw [a]
  rw [a_find_min_m_eq_zero_iff n (fun k => decide (List.count true k.bits % 2 = 0)) 1 (by omega)]
  simp


/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  sorry
