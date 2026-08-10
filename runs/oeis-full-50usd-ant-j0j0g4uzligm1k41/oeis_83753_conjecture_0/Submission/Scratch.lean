import FormalConjectures.Util.ProblemImports

open Nat

-- Check: is there any x in [2, 60], k in [5,12] with x^k a decimal palindrome?
-- We just compute and see. Print any hits.

def isPal (m : ℕ) : Bool := Nat.digits 10 m == (Nat.digits 10 m).reverse

def hits : List (ℕ × ℕ × ℕ) :=
  (List.range 200).flatMap (fun x =>
    (List.range 8).filterMap (fun j =>
      let k := j + 5
      let m := (x+2) ^ k
      if isPal m then some (x+2, k, m) else none))

#eval hits
#eval Nat.digits 10 14641
#eval isPal 14641   -- 11^4, should be true
#eval isPal 32      -- 2^5, should be false

-- Explore provable sub-lemmas.
-- head digit of digits: Nat.head!_digits : (digits b n).head! = n % b (for b ≠ 1)
-- getLast_digit_ne_zero : (digits b m).getLast _ ≠ 0

-- If a number is divisible by 10, its last decimal digit (head of digits list) is 0.
example (m : ℕ) (hm : m ≠ 0) (h10 : 10 ∣ m) : (Nat.digits 10 m).head! = 0 := by
  rw [Nat.head!_digits (by norm_num)]
  omega

-- The leading digit (getLast) is nonzero.
example (m : ℕ) (hm : m ≠ 0) : (Nat.digits 10 m).getLast (by
    simp [Nat.digits_ne_nil_iff_ne_zero, hm]) ≠ 0 :=
  Nat.getLast_digit_ne_zero 10 hm

-- KEY sub-result: if 10 ∣ m and m ≠ 0 then digits are NOT a palindrome.
-- Because head! = 0 but getLast ≠ 0, and for a palindrome head = getLast.
example (m : ℕ) (hm : m ≠ 0) (h10 : 10 ∣ m) :
    Nat.digits 10 m ≠ (Nat.digits 10 m).reverse := by
  intro hpal
  have hne : Nat.digits 10 m ≠ [] := by simp [Nat.digits_ne_nil_iff_ne_zero, hm]
  have hhead : (Nat.digits 10 m).head! = 0 := by
    rw [Nat.head!_digits (by norm_num)]; omega
  have hlast : (Nat.digits 10 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hm
  -- head! of reverse = getLast! of original
  have hgl : (Nat.digits 10 m).getLast hne = (Nat.digits 10 m).getLast! := by
    rw [List.getLast!_eq_getLast?, List.getLast?_eq_getLast _ hne]; rfl
  have : (Nat.digits 10 m).head! = (Nat.digits 10 m).getLast! := by
    conv_lhs => rw [hpal]
    rw [List.head!_reverse]
  rw [hhead, ← hgl] at this
  exact hlast this.symm


