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

/-- The inverse permutation `A006369`, witnessing injectivity of `A006368_map`. -/
def A006369_map (n : ℕ) : ℕ :=
  if n % 3 = 0 then
    (2 * n) / 3
  else if n % 3 = 1 then
    (4 * n - 1) / 3
  else
    (4 * n + 1) / 3

/-- `A006368_map` is injective: `A006369_map` is an explicit left inverse. -/
theorem map_injective : Function.Injective A006368_map := by
  have leftinv : Function.LeftInverse A006369_map A006368_map := by
    intro k
    unfold A006368_map A006369_map
    split_ifs <;> omega
  exact leftinv.injective

/--
**Open core (Conway–Guy / OEIS A223086).** `64` is not a periodic point of the amusical
permutation: its forward orbit never returns to `64`.
-/
theorem orbit_nonperiodic : ∀ d : ℕ, 0 < d → A006368_map^[d] 64 ≠ 64 := by
  sorry

/-- Injectivity of the trajectory follows from injectivity of the map and non-periodicity of `64`. -/
theorem orbit_injective : Function.Injective (fun n => A006368_map^[n] 64) := by
  intro m n h
  simp only at h
  rcases le_total m n with hmn | hnm
  · obtain ⟨k, rfl⟩ := Nat.le.dest hmn
    rw [Function.iterate_add_apply] at h
    have hcancel := (map_injective.iterate m) h
    by_contra hne
    exact orbit_nonperiodic k (by omega) hcancel.symm
  · obtain ⟨k, rfl⟩ := Nat.le.dest hnm
    rw [Function.iterate_add_apply] at h
    have hcancel := (map_injective.iterate n) h.symm
    by_contra hne
    exact orbit_nonperiodic k (by omega) hcancel.symm

/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj hij
  unfold a at hij
  have hidx : i - 1 = j - 1 := orbit_injective hij
  omega
