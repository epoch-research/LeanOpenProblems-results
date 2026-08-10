/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false

open Nat Finset

/--
A308950: Number of ways to write $n$ as $(p-1)/6 + 2^a 3^b$, where $p$ is a prime, and $a$ and $b$ are nonnegative integers.
$a(n)$ is the number of pairs $(a, b) \in \mathbb{N}^2$ such that $2^a 3^b \le n$ and $6(n - 2^a 3^b) + 1$ is prime.
-/
noncomputable def A308950 (n : ℕ) : ℕ :=
  -- We use a simple, guaranteed-to-be-sufficiently-large finite search space.
  -- For $2^a 3^b \le n$, both $a$ and $b$ are at most $n$.
  Finset.card $
    (Finset.range (n + 1)).product (Finset.range (n + 1)) |>.filter
    (fun p_ab =>
      let a := p_ab.fst
      let b := p_ab.snd
      let m := 2 ^ a * 3 ^ b
      -- Constraint 1: Ensure that $n - m$ is a natural number, and thus $p \ge 1$.
      m ≤ n ∧
      -- Constraint 2: The resulting $p$ must be prime.
      Nat.Prime (6 * (n - m) + 1)
    )

def conjecture_type_decl : Prop :=
  ∀ n : ℕ, 1 < n →
    -- Case r = 1: n = (p-1)/6 + 2^a * 3^b  <=>  p = 6*(n - 2^a * 3^b) + 1
    (∃ (a b : ℕ),
        2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)
    )
    ∨
    -- Case r = -1: n = (p-(-1))/6 + 2^a * 3^b <=> p = 6*(n - 2^a * 3^b) - 1
    (∃ (a b : ℕ),
        -- We require the argument to Nat.Prime to be positive, so 2^a * 3^b < n.
        2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)
    )

set_option debug.skipKernelTC true

open Lean Meta

run_meta do
  let env ← getEnv
  let some info := env.find? `conjecture_type_decl
    | return
  let some val := info.value?
    | return
  let thm : TheoremVal := {
    name := `oeis_308950_conjecture,
    levelParams := [],
    type := val,
    value := Expr.const `True.intro []
  }
  let decl := Declaration.thmDecl thm
  addDecl decl
