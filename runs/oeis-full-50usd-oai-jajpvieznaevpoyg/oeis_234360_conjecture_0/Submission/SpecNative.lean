import FormalConjectures.Util.ProblemImports

open Nat Finset

private def powMod (a m e : ℕ) : ℕ :=
  Nat.binaryRec (1 % m)
    (fun b _ r =>
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
        cases b <;> simp [Bool.toNat, pow_succ, pow_mul, Nat.mul_mod,
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

/--
A234360: $a(n) = \left|\left\{0 < k < n: (k+1)^{\phi(n-k)} + k \text{ is prime}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

private theorem no_prime_1408 :
    ¬ ∃ k, 0 < k ∧ k < 1408 ∧
      Nat.Prime ((k + 1) ^ (Nat.totient (1408 - k) / 2) - k) := by
  rintro ⟨k, hk0, hklt, hp⟩
  let N := ((k + 1) ^ (Nat.totient (1408 - k) / 2) - k)
  have hcert : N < 2 ∨ (¬ (N ∣ 2) ∧ powMod 2 N (N - 1) ≠ 1 % N) := by
    subst N
    interval_cases k <;> native_decide
  cases hcert with
  | inl hsmall =>
      have htwo := Nat.Prime.two_le hp
      change Nat.Prime N at hp
      omega
  | inr hwit =>
      rcases hwit with ⟨hndvd, hcalc⟩
      change Nat.Prime N at hp
      have hc : Nat.Coprime 2 N := ((hp.coprime_iff_not_dvd).2 hndvd).symm
      have hfer := Nat.ModEq.pow_card_sub_one_eq_one hp hc
      rw [powMod_eq] at hcalc
      exact hcalc hfer

/-- Conjecture: (i) a(n) > 0 for all n > 1. Also, for any n > 5 there is a positive integer k < n with (k+1)^{phi(n-k)/2} - k prime. -/
theorem oeis_234360_conjecture_0.disproof :
  ¬ ((∀ n, 1 < n → 0 < a n) ∧
  (∀ n, 5 < n → ∃ k, 0 < k ∧ k < n ∧ Nat.Prime ((k + 1) ^ (Nat.totient (n - k) / 2) - k))) := by
  intro h
  exact no_prime_1408 (h.2 1408 (by norm_num))
