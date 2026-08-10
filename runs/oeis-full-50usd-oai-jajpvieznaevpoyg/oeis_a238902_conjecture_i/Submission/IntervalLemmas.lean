import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

-- Test core facts about primeCounting and nth Prime
#check Nat.primeCounting'_nth_eq
#check Nat.primeCounting_sub_one
#check Nat.count_le_iff_le_nth
#check Nat.lt_nth_iff_count_lt
#check Nat.infinite_setOf_prime
#check Nat.gc_count_nth

example (q : ℕ) : π' (Nat.nth Nat.Prime (q*q)) = q*q := by
  simpa using Nat.primeCounting'_nth_eq (q*q)

example (q : ℕ) : π (Nat.nth Nat.Prime (q*q) - 1) = q*q := by
  simpa using Nat.primeCounting_sub_one (Nat.nth Nat.Prime (q*q))

-- What is π (nth Prime i)? It should be i+1.
example (i : ℕ) : π (Nat.nth Nat.Prime i) = i + 1 := by
  rw [Nat.primeCounting]
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime i


-- A usable Galois form: `π x ≤ b` iff `x + 1 ≤ nth Prime b`.
example (x b : ℕ) : π x ≤ b ↔ x + 1 ≤ Nat.nth Nat.Prime b := by
  simpa [Nat.primeCounting, Nat.primeCounting'] using
    (Nat.count_le_iff_le_nth Nat.infinite_setOf_prime (a := x+1) (b := b))

-- Thus, if `x` lies before the next threshold, `π x ≤ q^2`.
example (x q : ℕ) (hx : x + 1 ≤ Nat.nth Nat.Prime (q*q)) : π x ≤ q*q := by
  have hiff : π x ≤ q*q ↔ x + 1 ≤ Nat.nth Nat.Prime (q*q) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      (Nat.count_le_iff_le_nth Nat.infinite_setOf_prime (a := x+1) (b := q*q))
  exact hiff.2 hx

-- And if `x` is at/after the threshold `nth Prime (q^2)`, then `q^2+1 ≤ π x`.
example (x q : ℕ) (hx : Nat.nth Nat.Prime (q*q) ≤ x) : q*q + 1 ≤ π x := by
  have hmono := Nat.monotone_primeCounting
  have hval : π (Nat.nth Nat.Prime (q*q)) = q*q + 1 := by
    rw [Nat.primeCounting]
    exact Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime (q*q)
  exact hval ▸ hmono hx
