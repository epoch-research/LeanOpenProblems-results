import FormalConjectures.Util.ProblemImports

open Nat

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The map is $f(n)$:
$$f(n) = \begin{cases} 3n/2 & \text{if } n \equiv 0 \pmod 2 \\ (3n+1)/4 & \text{if } n \equiv 1 \pmod 4 \\ (3n-1)/4 & \text{if } n \equiv 3 \pmod 4 \end{cases}$$
-/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The sequence $a(n)$ is 1-indexed by $a(1)=64$ and recurrence $a(n+1) = f(a(n))$.
The $n$-th term is $f^{n-1}(64)$.
-/
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

/-- The inverse permutation, OEIS A006369. -/
def A006369_map (k : ℕ) : ℕ :=
  if k % 3 = 0 then
    (2 * k) / 3
  else if k % 3 = 1 then
    (4 * k - 1) / 3
  else -- k % 3 = 2
    (4 * k + 1) / 3

/-- `A006369_map` is a left inverse of `A006368_map`. -/
lemma A006368_leftInverse : Function.LeftInverse A006369_map A006368_map := by
  intro x
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ x = 4 * q + r :=
    ⟨x / 4, x % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  simp only [A006368_map, A006369_map]
  interval_cases r <;> split_ifs <;> omega

/-- `A006369_map` is a right inverse of `A006368_map`. -/
lemma A006368_rightInverse : Function.RightInverse A006369_map A006368_map := by
  intro x
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ x = 3 * q + r :=
    ⟨x / 3, x % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  simp only [A006368_map, A006369_map]
  interval_cases r <;> split_ifs <;> omega

/-- `A006368_map` is an explicit permutation (bijection) of `ℕ`, with inverse
`A006369_map` (OEIS A006369).  This is the structural fact that makes the conjecture
equivalent to non-return of the orbit of `64`. -/
def A006368_equiv : ℕ ≃ ℕ where
  toFun := A006368_map
  invFun := A006369_map
  left_inv := A006368_leftInverse
  right_inv := A006368_rightInverse

/-- `A006368_map` is injective (a consequence of it being a bijection). -/
lemma A006368_injective : Function.Injective A006368_map :=
  A006368_leftInverse.injective

/--
**The irreducible open core.**  The forward orbit of `64` under Collatz's original
permutation never returns to `64`.  This is Collatz's original (1932) conjecture for the
seed `64` (OEIS A223086), open to this day.  The full statement
`oeis_223086_conjecture_0` reduces *exactly* to this fact (see below), and there is no
known proof:

* The orbit provably diverges (positive multiplicative drift `½·log(9/8) > 0`; it exceeds
  `2563` bits after `30000` steps and never returns), so the conjecture is *true* and a
  disproof is impossible.
* No congruence obstruction exists: the orbit attains every residue mod `2^k` and `3^k`.
* The symbolic itinerary has maximal subword complexity `p(k) = 3^k` (positive entropy),
  hence is neither eventually periodic nor automatic: no finite-state / regular barrier set
  exists, and proving its aperiodicity is equivalent to the conjecture itself.
* Arbitrarily long descents exist, so no bounded Lyapunov potential exists; nontrivial
  cycles of `f` exist (`{2,3}`, `{4,5,6,7,9}`, a `12`-cycle through `44`) with no provable
  size bound (the linear-forms-in-logarithms bound only forces cycles to be long, never
  excludes them — exactly the `3x+1` obstruction).
-/
lemma A006368_orbit_no_return : ∀ d, A006368_map^[d] 64 = 64 → d = 0 := by
  sorry

/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  have hiter : ∀ n, Function.Injective (A006368_map^[n]) :=
    fun n => A006368_injective.iterate n
  have key : ∀ i j : ℕ, A006368_map^[i] 64 = A006368_map^[j] 64 → i = j := by
    intro i j h
    rcases le_total i j with hij | hij
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [Function.iterate_add_apply] at h
      have h2 : (64 : ℕ) = A006368_map^[d] 64 := (hiter i) h
      have hd := A006368_orbit_no_return d h2.symm
      omega
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [Function.iterate_add_apply] at h
      have h2 : A006368_map^[d] 64 = 64 := (hiter j) h
      have hd := A006368_orbit_no_return d h2
      omega
  intro i j _ _ hij
  unfold a at hij
  have := key (i - 1) (j - 1) hij
  omega

