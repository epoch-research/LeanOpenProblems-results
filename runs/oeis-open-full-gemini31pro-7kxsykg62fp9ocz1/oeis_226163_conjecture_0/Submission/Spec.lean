import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  M.det

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  sorry

theorem oeis_226163_conjecture_0.disproof : ¬ (type_of% @oeis_226163_conjecture_0) := sorry
