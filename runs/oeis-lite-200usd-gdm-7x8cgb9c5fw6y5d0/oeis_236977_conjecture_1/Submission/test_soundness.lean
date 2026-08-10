import FormalConjectures.Util.ProblemImports

open Nat Finset

def primes_1414 : List Nat := [2, 3] -- placeholder

def remove_p_fuel (p : Nat) : Nat → Nat → Nat
  | 0, t => t
  | fuel + 1, t =>
    if t % p == 0 then remove_p_fuel p fuel (t / p) else t

def totient_list_loop : List Nat → Nat → Nat → Nat
  | [], temp, acc => if temp > 1 then acc - acc / temp else acc
  | p :: ps, temp, acc =>
    if p * p > temp then
      if temp > 1 then acc - acc / temp else acc
    else if temp % p == 0 then
      let acc' := acc - acc / p
      let temp' := remove_p_fuel p 32 temp
      totient_list_loop ps temp' acc'
    else
      totient_list_loop ps temp acc

def totient_fast (primes : List Nat) (n : Nat) : Nat :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_list_loop primes n n

def sqrt_binary_loop (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, high => high
  | fuel + 1, low, high =>
    if low > high then high
    else
      let mid := (low + high) / 2
      let sq := mid * mid
      if sq == m then mid
      else if sq > m then
        if mid == 0 then low
        else sqrt_binary_loop m fuel low (mid - 1)
      else
        sqrt_binary_loop m fuel (mid + 1) high

def sqrt_fast (m : Nat) : Nat :=
  sqrt_binary_loop m 40 0 m

def is_square_fast (m : Nat) : Bool :=
  let r := sqrt_fast m
  r * r == m

def get_witness_final (n : Nat) : Nat := n / 3 -- placeholder

def check_all_loop (primes : List Nat) : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then
      if L % 6 = 3 ∨ L % 10 = 0 ∨ L % 6 = 0 then true
      else
        let k := get_witness_final L
        if k == 0 then false
        else if k > (L - 1) / 2 then false
        else is_square_fast (totient_fast primes k * totient_fast primes (L - k))
    else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then
      if L % 6 = 3 ∨ L % 10 = 0 ∨ L % 6 = 0 then true
      else
        let k := get_witness_final L
        if k == 0 then false
        else if k > (L - 1) / 2 then false
        else is_square_fast (totient_fast primes k * totient_fast primes (L - k))
    else
      let mid := (L + R) / 2
      check_all_loop primes fuel L mid && check_all_loop primes fuel (mid + 1) R

theorem check_all_sound (primes : List Nat) (fuel : Nat) : ∀ L R, L ≤ n → n ≤ R → R - L < 2 ^ fuel → check_all_loop primes fuel L R = true →
    (if n % 6 = 3 ∨ n % 10 = 0 ∨ n % 6 = 0 then true
     else
       let k := get_witness_final n
       if k == 0 then false
       else if k > (n - 1) / 2 then false
       else is_square_fast (totient_fast primes k * totient_fast primes (n - k))) = true := by
  induction fuel with
  | zero =>
    intro L R hL hnR h_lt h_all
    simp only [pow_zero] at h_lt
    have h_eq : L = R := by omega
    have h_n : n = L := by omega
    subst h_eq h_n
    dsimp [check_all_loop] at h_all
    rw [if_pos rfl] at h_all
    exact h_all
  | succ f ih =>
    intro L R hL hnR h_lt h_all
    dsimp [check_all_loop] at h_all
    by_cases h_gt : L > R
    · omega
    · by_cases h_eq : L = R
      · have h_n : n = L := by omega
        subst h_eq h_n
        rw [if_neg h_gt, if_pos rfl] at h_all
        exact h_all
      · rw [if_neg h_gt, if_neg h_eq] at h_all
        rw [Bool.and_eq_true] at h_all
        rcases h_all with ⟨h_left, h_right⟩
        let mid := (L + R) / 2
        have h_mid : mid = (L + R) / 2 := rfl
        by_cases hn : n ≤ mid
        · apply ih L mid hL hn ?_ h_left
          have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
          omega
        · apply ih (mid + 1) R ?_ hnR ?_ h_right
          · omega
          · have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
            omega
