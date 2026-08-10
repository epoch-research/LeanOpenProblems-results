import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.bit
#check Nat.bit_val
#check Nat.two_mul

private def powMod (a m e : ℕ) : ℕ :=
  Nat.binaryRec (1 % m)
    (fun b n r =>
      let sq := (r * r) % m
      if b then (a * sq) % m else sq)
    e


private lemma powMod_eq (a m e : ℕ) : powMod a m e = a ^ e % m := by
  induction e using Nat.binaryRec with
  | zero => simp [powMod, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [powMod]
      rw [Nat.binaryRec_eq]
      · change (let sq := (powMod a m n * powMod a m n) % m; if b then (a * sq) % m else sq) = a ^ Nat.bit b n % m
        rw [ih]
        rw [Nat.bit_val]
        cases b <;> simp [Bool.toNat, pow_succ, pow_mul, Nat.mul_mod, Nat.mod_mod,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.two_mul]
      · cases b
        · left
          by_cases hm0 : m = 0
          · simp [hm0]
          · by_cases hm1 : m = 1
            · simp [hm1]
            · have hmgt : 1 < m := by omega
              have hmod : 1 % m = 1 := Nat.mod_eq_of_lt hmgt
              simp [hmod]
        · right
          intro _
          rfl


