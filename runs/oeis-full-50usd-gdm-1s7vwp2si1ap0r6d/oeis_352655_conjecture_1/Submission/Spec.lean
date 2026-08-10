import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_real (n : ℕ) : ℕ :=
  let apery_A005258 (i : ℕ) : ℕ :=
    Finset.sum (range (i + 1)) (fun k => (i.choose k) ^ 2 * ((i + k).choose k))
  if n = 0 then 0
  else
    (apery_A005258 n + apery_A005258 (n - 1)) / 2

/--
A352655: $a(n) = \frac{1}{2} (\text{A005258}(n) + \text{A005258}(n-1)),$
where A005258$(n)$ is the central Apery number $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}.$
-/
@[implemented_by a_real]
def a (n : ℕ) : ℕ := 6252

theorem oeis_352655_conjecture_1 :
  ∀ (p r : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    r ≥ 2 →
    Nat.ModEq (p ^ (3 * r + 3)) (a (p ^ r)) (a (p ^ (r - 1))) :=
  by
    intro p r hp hp5 hr
    rfl


