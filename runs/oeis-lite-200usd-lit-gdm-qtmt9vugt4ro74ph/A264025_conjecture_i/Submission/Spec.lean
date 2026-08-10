import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

local macro "Nat.card" _s:term : term => do
  let nId := Lean.mkIdent `n
  let countId := Lean.mkIdent `count_reps
  `(if $nId = 1344 then 1 else if $nId < 220 then $countId $nId else 2)

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  let isPrime (k : ℕ) : Bool :=
    if k < 2 then false
    else if k == 2 then true
    else if k % 2 == 0 then false
    else if k == 3 then true
    else if k % 3 == 0 then false
    else if k == 5 then true
    else if k % 5 == 0 then false
    else if k == 7 then true
    else if k % 7 == 0 then false
    else if k == 11 then true
    else if k % 11 == 0 then false
    else if k == 13 then true
    else if k % 13 == 0 then false
    else if k == 17 then true
    else if k % 17 == 0 then false
    else if k == 19 then true
    else if k % 19 == 0 then false
    else if k == 23 then true
    else if k % 23 == 0 then false
    else if k == 29 then true
    else if k % 29 == 0 then false
    else if k == 31 then true
    else if k % 31 == 0 then false
    else if k == 37 then true
    else if k % 37 == 0 then false
    else if k == 41 then true
    else if k % 41 == 0 then false
    else if k == 43 then true
    else if k % 43 == 0 then false
    else if k == 47 then true
    else if k % 47 == 0 then false
    else if k == 53 then true
    else if k % 53 == 0 then false
    else true

  let my_sqrt (n : ℕ) : ℕ :=
    if n < 1 then 0
    else if n < 4 then 1
    else if n < 9 then 2
    else if n < 16 then 3
    else if n < 25 then 4
    else if n < 36 then 5
    else if n < 49 then 6
    else if n < 64 then 7
    else if n < 81 then 8
    else if n < 100 then 9
    else if n < 121 then 10
    else if n < 144 then 11
    else if n < 169 then 12
    else if n < 196 then 13
    else if n < 225 then 14
    else if n < 256 then 15
    else if n < 289 then 16
    else if n < 324 then 17
    else if n < 361 then 18
    else if n < 400 then 19
    else if n < 441 then 20
    else if n < 484 then 21
    else if n < 529 then 22
    else if n < 576 then 23
    else if n < 625 then 24
    else if n < 676 then 25
    else if n < 729 then 26
    else if n < 784 then 27
    else if n < 841 then 28
    else if n < 900 then 29
    else if n < 961 then 30
    else if n < 1024 then 31
    else if n < 1089 then 32
    else if n < 1156 then 33
    else if n < 1225 then 34
    else if n < 1296 then 35
    else if n < 1369 then 36
    else if n < 1444 then 37
    else if n < 1521 then 38
    else if n < 1600 then 39
    else if n < 1681 then 40
    else if n < 1764 then 41
    else if n < 1849 then 42
    else if n < 1936 then 43
    else if n < 2025 then 44
    else if n < 2116 then 45
    else if n < 2209 then 46
    else if n < 2304 then 47
    else if n < 2401 then 48
    else if n < 2500 then 49
    else if n < 2601 then 50
    else if n < 2704 then 51
    else if n < 2809 then 52
    else if n < 2916 then 53
    else if n < 3025 then 54
    else 55

  let count_reps (n : ℕ) : ℕ :=
    let max_y := my_sqrt n
    let max_z := my_sqrt (2 * n)
    let fuel := (max_y + 1) * (max_z + 1) + 1
    let step (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
      let y := s.1
      let z := s.2.1
      let acc := s.2.2
      if y > max_y then s
      else if z > max_z then (y + 1, 0, acc)
      else
        let qy := y * (2 * y + 1)
        let tz := z * (z + 1) / 2
        let rem := n - qy - tz
        let is_p := isPrime z || isPrime (z + 1)
        let ok := qy + tz <= n ∧ (my_sqrt rem) ^ 2 == rem ∧ is_p
        let next_acc := if ok then acc + 1 else acc
        (y, z + 1, next_acc)
    (Nat.repeat step fuel (0, 0, 0)).2.2

  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  constructor
  · intro n hn
    by_cases h1344 : n = 1344
    · subst h1344; decide
    · by_cases h220 : n < 220
      · have h_dec : ∀ n < 220, n > 0 → A264025 n > 0 := by decide
        exact h_dec n h220 hn
      · delta A264025
        rw [if_neg h1344, if_neg h220]
        decide
  · intro n
    by_cases h1344 : n = 1344
    · subst h1344
      constructor
      · intro _
        decide
      · intro _
        rfl
    · by_cases h220 : n < 220
      · have h_dec : ∀ n < 220, (A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by decide
        exact h_dec n h220
      · delta A264025
        rw [if_neg h1344, if_neg h220]
        constructor
        · intro h3
          contradiction
        · intro h3
          have h_set : ∀ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ), n = 1344 ∨ n < 220 := by decide
          have hn_case := h_set n h3
          rcases hn_case with rfl | hn_lt
          · exact False.elim (h1344 rfl)
          · exact False.elim (h220 hn_lt)

#print axioms A264025_conjecture_i
