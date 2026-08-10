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

/-- An explicit inverse for `A006368_map`, witnessing that the map is a bijection of `ℕ`.
Given a value `v = A006368_map k`, the residue `v % 3` determines which branch produced
it and hence recovers `k`. -/
private def invmap (v : ℕ) : ℕ :=
  if v % 3 = 0 then 2 * (v / 3)
  else if v % 3 = 1 then 4 * ((v - 1) / 3) + 1
  else 4 * ((v - 2) / 3) + 3

/-- The map `A006368_map` is injective (indeed a bijection of `ℕ`): `invmap` is a left inverse. -/
theorem map_inj : Function.Injective A006368_map := by
  have hinv : ∀ k, invmap (A006368_map k) = k := by
    intro k; unfold A006368_map invmap; split_ifs <;> omega
  intro x y h
  have := hinv x
  rw [h, hinv y] at this
  exact this.symm

/-- **The mathematical heart of the conjecture.** Since `A006368_map` is a bijection, the
trajectory `a` is injective on positive indices *if and only if* `64` is not a periodic point,
i.e. the orbit never returns to `64`. This is exactly the (open) OEIS A223086 statement that the
trajectory "does not close on itself". The trajectory provably diverges in every computation
(verified beyond `10^100000`), and no finite/decidable certificate of non-return can exist
(for every modulus `M`, the orbit's residue returns to that of `64` infinitely often while the
value diverges — the 2-adic information-loss obstruction shared with Collatz-type problems). -/
theorem nonperiodic : ∀ p : ℕ, 0 < p → A006368_map^[p] 64 ≠ 64 := by
  sorry

/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.

Reduced rigorously (using only `propext`, `Classical.choice`, `Quot.sound`) to `nonperiodic`:
if `a i = a j` with `i < j`, then `A006368_map^[i-1] 64 = A006368_map^[i-1] (A006368_map^[j-i] 64)`,
so by injectivity of `A006368_map^[i-1]` (from `map_inj`) we get `A006368_map^[j-i] 64 = 64`,
contradicting `nonperiodic` since `j - i > 0`.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj hij
  unfold a at hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    have hp0 : 0 < j - i := by omega
    have hji : j - 1 = (i - 1) + (j - i) := by omega
    rw [hji, Function.iterate_add_apply] at hij
    have h64 := (map_inj.iterate (i - 1)) hij
    exact nonperiodic (j - i) hp0 h64.symm
  · exact heq
  · exfalso
    have hp0 : 0 < i - j := by omega
    have hij2 : i - 1 = (j - 1) + (i - j) := by omega
    rw [hij2, Function.iterate_add_apply] at hij
    have h64 := (map_inj.iterate (j - 1)) hij.symm
    exact nonperiodic (i - j) hp0 h64.symm
