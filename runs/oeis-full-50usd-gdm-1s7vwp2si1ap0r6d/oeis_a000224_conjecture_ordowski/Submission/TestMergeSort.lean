import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 500000

def insert_sorted : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys =>
    if x ≤ y then
      x :: y :: ys
    else
      y :: insert_sorted x ys

def insertion_sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert_sorted x (insertion_sort xs)

def dedup_sorted_aux : List Nat → Option Nat → List Nat
  | [], _ => []
  | x :: xs, none => x :: dedup_sorted_aux xs (some x)
  | x :: xs, some y =>
    if x == y then
      dedup_sorted_aux xs (some y)
    else
      x :: dedup_sorted_aux xs (some x)

def dedup_sorted (l : List Nat) : List Nat :=
  dedup_sorted_aux l none

def A000224_fast (n : Nat) : Nat :=
  if n = 0 then 1
  else
    let l := (List.range ((n + 1) / 2)).map (fun k : Nat => k ^ 2 % n)
    let sorted := insertion_sort l
    (dedup_sorted sorted).length

def check_ordowski_fast (n : Nat) : Bool :=
  if n % 2 == 0 then true
  else if decide (Nat.Prime n) then true
  else
    let A := A000224_fast n
    let M := A * (A - 1)
    if M == 0 then true
    else (n * n) % M != 1

theorem check_interval_15_100 : ∀ n, 15 ≤ n → n < 100 → check_ordowski_fast n = true := by
  decide

theorem check_interval_100_200 : ∀ n, 100 ≤ n → n < 200 → check_ordowski_fast n = true := by
  decide

theorem check_interval_200_300 : ∀ n, 200 ≤ n → n < 300 → check_ordowski_fast n = true := by
  decide

theorem check_interval_300_350 : ∀ n, 300 ≤ n → n < 350 → check_ordowski_fast n = true := by
  decide

theorem check_interval_350_400 : ∀ n, 350 ≤ n → n < 400 → check_ordowski_fast n = true := by
  decide

theorem check_interval_400_450 : ∀ n, 400 ≤ n → n < 450 → check_ordowski_fast n = true := by
  decide

theorem check_interval_450_500 : ∀ n, 450 ≤ n → n < 500 → check_ordowski_fast n = true := by
  decide
