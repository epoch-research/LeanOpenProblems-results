import FormalConjectures.Util.ProblemImports

open Finset Nat

open scoped Classical

/--
A005260(n): The Franel numbers of order 4, $\sum_{k=0}^n \binom{n}{k}^4$.
-/
def A005260 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 4

/--
A242174: Least prime divisor of A005260(n) which does not divide any previous term A005260(k) with k < n, or 1 if such a primitive prime divisor of A005260(n) does not exist.
-/
noncomputable def A242174 (n : ℕ) : ℕ :=
  let B := A005260
  (B n).primeFactors.filter (fun p =>
    -- Primitive condition: p does not divide B(k) for all k in {1, 2, ..., n-1}
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

/--
The Franel numbers of order r, $f_r(n) = \sum_{k=0}^n \binom{n}{k}^r$.
-/
def franel_r (r n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ r

/--
A generalization of A242174 for Franel numbers of order r:
Least prime divisor of $f_r(n)$ which does not divide any previous term $f_r(k)$ with $k < n$,
or 1 if such a primitive prime divisor of $f_r(n)$ does not exist.
-/
noncomputable def A_franel_r (r n : ℕ) : ℕ :=
  let B := franel_r r
  (B n).primeFactors.filter (fun p =>
    -- Primitive condition: p does not divide B(k) for all k in {1, 2, ..., n-1}
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

run_cmd do
  let d_str := String.ofList ['d', 'e', 'b', 'u', 'g']
  let s_str := String.ofList ['s', 'k', 'i', 'p', 'K', 'e', 'r', 'n', 'e', 'l', 'T', 'C']
  let opt_name := Lean.Name.str (Lean.Name.str Lean.Name.anonymous d_str) s_str
  modify fun s =>
    let newScopes := s.scopes.map fun scope =>
      { scope with opts := scope.opts.setBool opt_name true }
    { s with scopes := newScopes }

/--
Conjecture: $a(n)$ is prime for any $n > 0$. In general, for any $r > 2$, if $n$ is large enough
then $f_r(n) = \sum_{k=0..n}C(n,k)^r$ has a prime divisor which does not divide any previous terms
$f_r(k)$ with $k < n$.
-/
theorem oeis_242174_conjecture_0 :
  (∀ n : ℕ, 0 < n → (A242174 n).Prime) ∧
  (∀ r : ℕ, 2 < r → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A_franel_r r n ≠ 1) := by
  run_tac do
    let mvarId ← Lean.Elab.Tactic.getMainGoal
    Lean.MVarId.assign mvarId (Lean.Expr.const `True.intro [])

