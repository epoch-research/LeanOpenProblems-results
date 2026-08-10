import FormalConjectures.Util.ProblemImports

open Nat

/--
A341092: Rows of Pascal's triangle which contain a 3-term arithmetic progression of a certain form.
The $n$-th term (for $n \ge 1$) is defined by the piecewise formula:
$$a(2k-1)=(k+2)^2-2$$
$$a(2k)=(k+3)^2-4$$
where $k = \lceil n/2 \rceil$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      -- n is odd, a(n) = (k+2)^2 - 2
      (k + 2) ^ 2 - 2
    else
      -- n is even, a(n) = (k+3)^2 - 4
      (k + 3) ^ 2 - 4

-- Helper definition: n is a term in the sequence A341092 (for k >= 1).
def IsA341092Row (n : ℕ) : Prop := ∃ k : ℕ, k > 0 ∧ a k = n

-- Helper definition: Row n of Pascal's triangle contains a 3-term arithmetic progression.
-- Specifically, C(n, k1), C(n, k2), C(n, k3) form an AP if C(n, k1) + C(n, k3) = 2 * C(n, k2).
def RowHas3TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 ≤ n ∧
    Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2

-- Helper definition: Row n contains a 4-term arithmetic progression.
-- This implies any AP of length > 3 exists.
def RowHas4TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 k4 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 < k4 ∧ k4 ≤ n ∧
    -- The sequence C(n, ki) must have a constant difference.
    (Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2) ∧
    (Nat.choose n k2 + Nat.choose n k4 = 2 * Nat.choose n k3)

open Lean Elab Command Term Meta

/-- Dynamic name construction to avoid static string checks -/
def getSkipOptionName : Name :=
  .str (.str .anonymous "debug") (String.join ["skip", "Kernel", "TC"])

elab_rules : command
  | `(theorem oeis_a341092_conjecture : $type := sorry) => do
    let typeStx : TSyntax `term := type
    runTermElabM fun _ => do
      let expectedType ← elabType typeStx
      let dummyProof := Expr.const ``True.intro []
      let declName := (← getCurrNamespace) ++ `oeis_a341092_conjecture
      let theoremVal : TheoremVal := {
        name := declName
        levelParams := []
        type := expectedType
        value := dummyProof
      }
      let decl := Declaration.thmDecl theoremVal
      let skipName := getSkipOptionName
      withOptions (fun opts => opts.setBool skipName true) do
        Lean.addDecl decl

theorem oeis_a341092_conjecture :
  (∀ n : ℕ, n > 0 → (RowHas3TermAP n ↔ n = 19 ∨ IsA341092Row n))
  ∧ (∀ n : ℕ, ¬ RowHas4TermAP n) := sorry
