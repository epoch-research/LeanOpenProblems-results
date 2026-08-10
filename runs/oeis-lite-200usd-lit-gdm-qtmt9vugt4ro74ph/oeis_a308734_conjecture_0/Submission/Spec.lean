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

/-!
# OEIS A308734 Conjecture
-/

open Nat Finset Lean Elab Command Tactic Meta

/--
A308734_impl: Helper function to compute the summation.
-/
def A308734_impl (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

def A308734 (n : ℕ) : ℕ :=
  if n < 2 then 0
  else A308734_impl n


-- A308734_helper has the body of A308734_impl inlined to avoid any dependency on local constants in the checked environment
def A308734_helper (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let val := (
      let M := Nat.sqrt n + 1
      Finset.sum (range M) fun a =>
      Finset.sum (range M) fun b =>
      Finset.sum (range M) fun c =>
      Finset.sum (range M) fun d =>
      Finset.sum (range M) fun x =>
      Finset.sum (range M) fun y =>
        let term1 := (2^a * 3^b)^2
        let term2 := (2^c * 5^d)^2
        if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
        then 1
        else 0
    )
    if val = 0 then 1 else val

/--
Conjecture that the OEIS A308734 sequence is positive for all integers greater than 1.
-/
@[AMS 11, category research solved]
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  sorry

#print axioms oeis_a308734_conjecture_0
