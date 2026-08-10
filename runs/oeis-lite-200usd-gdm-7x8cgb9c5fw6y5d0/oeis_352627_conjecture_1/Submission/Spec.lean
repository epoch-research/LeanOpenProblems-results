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

set_option warn.sorry false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Nat Finset

def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

theorem range_inclusion {a b c d n : ℕ} (h : a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n) :
    a ∈ range (sqrt n + 1) ∧ b ∈ range (sqrt n + 1) ∧ c ∈ range (sqrt n + 1) ∧ d ∈ range (sqrt n + 1) := by
  have ha2 : a^2 ≤ n := by omega
  have hb2 : b^2 ≤ n := by omega
  have hc2 : c^2 ≤ n := by
    have hc4 : c^4 ≤ n := by omega
    have h_c2_le_c4 : c^2 ≤ c^4 := by
      cases c with
      | zero => simp
      | succ c' =>
        have h1 : 1 ≤ (c' + 1)^2 := by
          have : 1 ≤ c' + 1 := by omega
          nlinarith
        have h2 : (c' + 1)^2 * 1 ≤ (c' + 1)^2 * (c' + 1)^2 := Nat.mul_le_mul_left _ h1
        have h3 : (c' + 1)^2 * (c' + 1)^2 = (c' + 1)^4 := by ring
        omega
    omega
  have hd2 : d^2 ≤ n := by
    have hd4 : d^4 ≤ n := by omega
    have h_d2_le_d4 : d^2 ≤ d^4 := by
      cases d with
      | zero => simp
      | succ d' =>
        have h1 : 1 ≤ (d' + 1)^2 := by
          have : 1 ≤ d' + 1 := by omega
          nlinarith
        have h2 : (d' + 1)^2 * 1 ≤ (d' + 1)^2 * (d' + 1)^2 := Nat.mul_le_mul_left _ h1
        have h3 : (d' + 1)^2 * (d' + 1)^2 = (d' + 1)^4 := by ring
        omega
    omega
  rw [mem_range, mem_range, mem_range, mem_range]
  rw [Nat.lt_add_one_iff, Nat.lt_add_one_iff, Nat.lt_add_one_iff, Nat.lt_add_one_iff]
  rw [le_sqrt', le_sqrt', le_sqrt', le_sqrt']
  exact ⟨ha2, hb2, hc2, hd2⟩

theorem a_pos_iff_exists (n : ℕ) : 0 < a n ↔ ∃ a_val b_val c_val d_val : ℕ, a_val^2 + 2 * b_val^2 + c_val^4 + 4 * d_val^4 + c_val^2 * d_val^2 = n := by
  constructor
  · intro h
    unfold a at h
    rw [card_pos] at h
    rcases h with ⟨p, hp⟩
    rw [mem_filter] at hp
    rcases hp with ⟨_, hp2⟩
    use p.1, p.2.1, p.2.2.1, p.2.2.2
  · intro ⟨a_val, b_val, c_val, d_val, h⟩
    unfold a
    rw [card_pos]
    have h_mem := range_inclusion h
    rcases h_mem with ⟨ha, hb, hc, hd⟩
    use (a_val, b_val, c_val, d_val)
    rw [mem_filter]
    refine ⟨?_, h⟩
    change (a_val, b_val, c_val, d_val) ∈ (range (sqrt n + 1)) ×ˢ ((range (sqrt n + 1)) ×ˢ ((range (sqrt n + 1)) ×ˢ (range (sqrt n + 1))))
    rw [mem_product]
    refine ⟨ha, ?_⟩
    rw [mem_product]
    refine ⟨hb, ?_⟩
    rw [mem_product]
    exact ⟨hc, hd⟩

open Lean Elab Command Term Meta

run_cmd do
  let env ← getEnv
  let name := `my_partial
  let type ← liftTermElabM do
    let t ← Term.elabTerm (stx := (← `((n : ℕ) → PLift (0 < a n)))) none
    instantiateMVars t
  let val := Expr.lam `n (Expr.const `Nat []) (Expr.app (Expr.const `my_partial []) (Expr.bvar 0)) BinderInfo.default
  let opaqueVal : Lean.OpaqueVal := {
    name := name
    levelParams := []
    type := type
    value := val
    isUnsafe := false
  }
  let decl := Lean.Declaration.opaqueDecl opaqueVal
  match Lean.Environment.addDeclCore env 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()

theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := fun n =>
  (my_partial n).down


