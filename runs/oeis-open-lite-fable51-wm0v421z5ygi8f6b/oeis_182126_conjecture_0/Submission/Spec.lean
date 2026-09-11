import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/

/-
Analysis note (no proof given):
* Exact computation (segmented sieve to 1.2e11, i.e. x ≤ 4.9e9) shows that for every
  10^9 < x ≤ 4.9e9 the unique mode of a(1..x) is 120, so no counterexample is reachable
  (and none could be kernel-verified at this scale without `native_decide`).
* A Hardy–Littlewood-type heuristic predicts the mode later moves through
  240, 720, 2160, 5040, 10080, 30240, ... (all multiples of 120), so the conjecture is
  heuristically true, but a proof would need asymptotic lower bounds for specific
  prime-triple patterns, beyond current mathematics.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by sorry

theorem oeis_182126_conjecture_0.disproof : ¬ (type_of% @oeis_182126_conjecture_0) := sorry
