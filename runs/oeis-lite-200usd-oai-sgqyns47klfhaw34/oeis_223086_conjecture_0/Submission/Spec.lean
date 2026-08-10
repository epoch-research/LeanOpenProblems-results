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


def A006368_inv (k : ℕ) : ℕ :=
  if k % 3 = 0 then
    2 * (k / 3)
  else if k % 3 = 1 then
    4 * (k / 3) + 1
  else
    4 * (k / 3) + 3

lemma A006368_inv_map (n : ℕ) : A006368_inv (A006368_map n) = n := by
  unfold A006368_map A006368_inv
  by_cases h2 : n % 2 = 0
  · rw [if_pos h2]
    have hmod : (3 * n / 2) % 3 = 0 := by
      obtain ⟨m, hm⟩ := (Nat.dvd_iff_mod_eq_zero).mpr h2
      subst n
      omega
    rw [if_pos hmod]
    obtain ⟨m, rfl⟩ := (Nat.dvd_iff_mod_eq_zero).mpr h2
    omega
  · rw [if_neg h2]
    have hnodd : n % 2 = 1 := by omega
    have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h4 with h41 | h43
    · rw [if_pos h41]
      have hmod : ((3 * n + 1) / 4) % 3 = 1 := by
        have hn : ∃ m, n = 4 * m + 1 := by
          refine ⟨n / 4, ?_⟩
          omega
        rcases hn with ⟨m, rfl⟩
        omega
      rw [if_neg (by omega : ((3 * n + 1) / 4) % 3 ≠ 0), if_pos hmod]
      have hn : ∃ m, n = 4 * m + 1 := by
        refine ⟨n / 4, ?_⟩
        omega
      rcases hn with ⟨m, rfl⟩
      omega
    · rw [if_neg (by omega : n % 4 ≠ 1)]
      have hmod0 : ((3 * n - 1) / 4) % 3 ≠ 0 := by
        have hn : ∃ m, n = 4 * m + 3 := by
          refine ⟨n / 4, ?_⟩
          omega
        rcases hn with ⟨m, rfl⟩
        omega
      have hmod1 : ((3 * n - 1) / 4) % 3 ≠ 1 := by
        have hn : ∃ m, n = 4 * m + 3 := by
          refine ⟨n / 4, ?_⟩
          omega
        rcases hn with ⟨m, rfl⟩
        omega
      rw [if_neg hmod0, if_neg hmod1]
      have hn : ∃ m, n = 4 * m + 3 := by
        refine ⟨n / 4, ?_⟩
        omega
      rcases hn with ⟨m, rfl⟩
      omega

lemma A006368_map_injective : Function.Injective A006368_map := by
  intro x y h
  have := congrArg A006368_inv h
  simpa [A006368_inv_map] using this


lemma iterate_injective_A006368_map (n : ℕ) : Function.Injective (A006368_map^[n]) := by
  exact A006368_map_injective.iterate n

lemma oeis_223086_of_no_return
    (hno : ∀ n : ℕ, 0 < n → (A006368_map^[n]) 64 ≠ 64) :
    ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj h
  wlog hij : i ≤ j generalizing i j with H
  · exact (H j i hj hi h.symm (Nat.le_of_not_ge hij)).symm
  have hi1 : i - 1 + (j - i) = j - 1 := by omega
  have hiter : (A006368_map^[i - 1]) 64 = (A006368_map^[j - 1]) 64 := by
    simpa [a] using h
  rw [← hi1, Function.iterate_add_apply] at hiter
  have hinj : Function.Injective (A006368_map^[i - 1]) := iterate_injective_A006368_map (i - 1)
  have hret : (A006368_map^[j - i]) 64 = 64 := hinj hiter.symm
  by_cases heq : j = i
  · omega
  have hpos : 0 < j - i := by omega
  exfalso
  exact (hno (j - i) hpos) hret


/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  sorry
