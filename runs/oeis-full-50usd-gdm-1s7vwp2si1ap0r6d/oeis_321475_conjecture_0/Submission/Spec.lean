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
set_option linter.style.copyright.formalConjectures false

open Nat List

/--
A321475: Zeroless factorials (version 2): $a(0) = 1$, and for any $n > 0$,
$a(n) = \operatorname{noz}(1 \cdot \operatorname{noz}(2 \cdot \ldots \cdot \operatorname{noz}((n-1) \cdot n)))$,
where $\operatorname{noz}(n) = A004719(n)$ omits the zeros from $n$.
-/
def A321475 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    -- Helper function noz(k) to omit zeros from k (A004719)
    let noz (k : ℕ) : ℕ :=
      ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k))

    -- The calculation is a tail-recursive loop modeling the nested operations.
    -- i is the descending multiplier, P is the accumulated product/result.
    let rec loop (i : ℕ) (P : ℕ) : ℕ :=
      if i = 0 then P
      -- Apply the next step: noz(i * P) and continue with the next multiplier i-1.
      else loop (i - 1) (noz (i * P))

    -- Initial call: multiplier starts at n - 1, initial value is n.
    loop (n - 1) n

lemma ofDigits_filter_le (b : ℕ) (hb : 1 ≤ b) (p : ℕ → Bool) (l : List ℕ) :
    ofDigits b (l.filter p) ≤ ofDigits b l := by
  induction l with
  | nil =>
    simp [ofDigits]
  | cons hd tl ih =>
    simp only [filter_cons]
    split_ifs with h
    · simp only [ofDigits_cons]
      have h_mul : b * ofDigits b (filter p tl) ≤ b * ofDigits b tl := Nat.mul_le_mul_left b ih
      omega
    · simp only [ofDigits_cons]
      have h_mul : ofDigits b tl ≤ b * ofDigits b tl := by
        calc ofDigits b tl = 1 * ofDigits b tl := by rw [one_mul]
        _ ≤ b * ofDigits b tl := Nat.mul_le_mul_right (ofDigits b tl) hb
      omega

lemma noz_le (k : ℕ) :
    ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k)) ≤ k := by
  have h1 : ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k)) ≤ ofDigits 10 (digits 10 k) := by
    apply ofDigits_filter_le 10 (by omega)
  have h2 : ofDigits 10 (digits 10 k) = k := ofDigits_digits 10 k
  omega

lemma loop_le_factorial (noz : ℕ → ℕ) (h_noz : ∀ x, noz x ≤ x) (i P : ℕ) :
    A321475.loop noz i P ≤ i.factorial * P := by
  induction i generalizing P with
  | zero =>
    rw [A321475.loop.eq_1]
    simp
  | succ i ih =>
    rw [A321475.loop.eq_1]
    simp
    have ih' := ih (noz ((i + 1) * P))
    have h1 : noz ((i + 1) * P) ≤ (i + 1) * P := h_noz ((i + 1) * P)
    have h4 : i.factorial * noz ((i + 1) * P) ≤ i.factorial * ((i + 1) * P) := Nat.mul_le_mul_left _ h1
    have h5 : i.factorial * ((i + 1) * P) = (i + 1).factorial * P := by
      calc i.factorial * ((i + 1) * P) = (i + 1) * i.factorial * P := by ring
      _ = (i + 1).factorial * P := by rw [Nat.factorial_succ]
    omega

theorem A321475_le_factorial (n : ℕ) : A321475 n ≤ n.factorial := by
  unfold A321475
  split_ifs with h
  · simp [h]
  · dsimp
    have h1 : A321475.loop (fun k => ofDigits 10 (filter (fun d => ¬ d = 0) (digits 10 k))) (n - 1) n ≤ (n - 1).factorial * n := by
      apply loop_le_factorial
      intro x
      have h_noz_le := noz_le x
      simp only [ne_eq] at h_noz_le
      exact h_noz_le
    have h2 : (n - 1).factorial * n = n.factorial := by
      cases n with
      | zero => contradiction
      | succ n =>
        simp only [add_tsub_cancel_right]
        rw [Nat.factorial_succ]
        ring
    omega

/--
%C A321475 Is this sequence bounded?
-/
theorem oeis_321475_conjecture_0 : ∃ M : ℕ, ∀ n : ℕ, A321475 n ≤ M := by
  use 10 ^ 150
  intro n
  by_cases h : n ≤ 70
  · have h1 := A321475_le_factorial n
    have h2 : n ! ≤ 70 ! := Nat.factorial_le h
    have h3 : 70 ! ≤ 10 ^ 150 := by decide
    omega
  · sorry
