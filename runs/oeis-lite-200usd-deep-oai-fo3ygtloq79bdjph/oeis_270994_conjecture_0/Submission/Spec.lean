import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

private lemma pow_modEq_of_mod_eq (b p d r m : ℕ) (hmod : m % d = r)
    (hcycle : b ^ d ≡ 1 [MOD p]) : b ^ m ≡ b ^ r [MOD p] := by
  calc
    b ^ m = b ^ (d * (m / d) + m % d) := by
      exact congrArg (fun x => b ^ x) (Nat.div_add_mod m d).symm
    _ = b ^ (d * (m / d) + r) := by rw [hmod]
    _ = (b ^ d) ^ (m / d) * b ^ r := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (m / d) * b ^ r [MOD p] :=
      (Nat.ModEq.pow (m / d) hcycle).mul (Nat.ModEq.refl (b ^ r))
    _ = b ^ r := by simp

private lemma not_prime_of_dvd_lt (N p : ℕ) (hp1 : p ≠ 1) (hpdvd : p ∣ N)
    (hplt : p < N) : ¬ Nat.Prime N := by
  intro hN
  have h := hN.eq_one_or_self_of_dvd p hpdvd
  rcases h with h | h
  · exact hp1 h
  · omega

private lemma dvd_for_residue (K p d r m : ℕ) (hmod : m % d = r)
    (hcycle : 2 ^ d ≡ 1 [MOD p]) (hconst : K * 2 ^ r + 1 ≡ 0 [MOD p]) :
    p ∣ K * 2 ^ m + 1 := by
  have hpow : 2 ^ m ≡ 2 ^ r [MOD p] := pow_modEq_of_mod_eq 2 p d r m hmod hcycle
  have hmain : K * 2 ^ m + 1 ≡ K * 2 ^ r + 1 [MOD p] := by
    exact ((Nat.ModEq.refl K).mul hpow).add (Nat.ModEq.refl 1)
  exact Nat.modEq_zero_iff_dvd.mp (hmain.trans hconst)

private lemma not_prime_of_cover (K p d r m : ℕ) (hp1 : p ≠ 1) (hpK : p < K)
    (hmod : m % d = r) (hcycle : 2 ^ d ≡ 1 [MOD p])
    (hconst : K * 2 ^ r + 1 ≡ 0 [MOD p]) : ¬ Nat.Prime (K * 2 ^ m + 1) := by
  refine not_prime_of_dvd_lt (K * 2 ^ m + 1) p hp1
    (dvd_for_residue K p d r m hmod hcycle hconst) ?_
  have hle : K ≤ K * 2 ^ m := Nat.le_mul_of_pos_right K (pow_pos (by norm_num : 0 < 2) m)
  omega

private lemma not_prime_middle (m : ℕ) (_hm : m > 0) :
    ¬ Nat.Prime ((a 473165 + 4) * 2 ^ m + 1) := by
  have hlt : m % 48 < 48 := Nat.mod_lt _ (by norm_num)
  interval_cases hrem : m % 48
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 0 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 0 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 7 3 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 1 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 1 [MOD 3] := h48.of_dvd (by norm_num)
      change m % 3 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 2 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 2 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 3 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 3 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 4 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 4 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 257 16 5 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 5 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 5 [MOD 16] := h48.of_dvd (by norm_num)
      change m % 16 = 5 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 6 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 6 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 7 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 7 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 8 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 8 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 17 8 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 9 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 9 [MOD 8] := h48.of_dvd (by norm_num)
      change m % 8 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 10 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 10 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 11 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 11 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 12 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 12 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 7 3 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 13 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 13 [MOD 3] := h48.of_dvd (by norm_num)
      change m % 3 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 14 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 14 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 15 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 15 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 16 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 16 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 17 8 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 17 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 17 [MOD 8] := h48.of_dvd (by norm_num)
      change m % 8 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 18 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 18 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 19 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 19 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 20 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 20 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 257 16 5 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 21 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 21 [MOD 16] := h48.of_dvd (by norm_num)
      change m % 16 = 5 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 22 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 22 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 23 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 23 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 24 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 24 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 7 3 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 25 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 25 [MOD 3] := h48.of_dvd (by norm_num)
      change m % 3 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 26 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 26 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 27 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 27 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 28 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 28 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 97 48 29 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 29 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 29 [MOD 48] := h48.of_dvd (by norm_num)
      change m % 48 = 29 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 30 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 30 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 31 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 31 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 32 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 32 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 17 8 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 33 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 33 [MOD 8] := h48.of_dvd (by norm_num)
      change m % 8 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 34 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 34 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 35 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 35 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 36 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 36 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 7 3 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 37 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 37 [MOD 3] := h48.of_dvd (by norm_num)
      change m % 3 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 38 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 38 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 39 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 39 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 40 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 40 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 17 8 1 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 41 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 41 [MOD 8] := h48.of_dvd (by norm_num)
      change m % 8 = 1 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 42 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 42 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 43 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 43 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 44 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 44 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 673 48 45 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 45 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 45 [MOD 48] := h48.of_dvd (by norm_num)
      change m % 48 = 45 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 3 2 0 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 46 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 46 [MOD 2] := h48.of_dvd (by norm_num)
      change m % 2 = 0 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])
  · exact not_prime_of_cover (a 473165 + 4) 5 4 3 m (by norm_num) (by norm_num [a]) (by
      have h48 : m ≡ 47 [MOD 48] := by simpa [Nat.ModEq] using hrem
      have hd : m ≡ 47 [MOD 4] := h48.of_dvd (by norm_num)
      change m % 4 = 3 at hd
      exact hd) (by norm_num [Nat.ModEq]) (by norm_num [a, Nat.ModEq])

private lemma middle_is_sierpinski : is_sierpinski_number (a 473165 + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [a]
  · norm_num [a]
  · exact not_prime_middle

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ ∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False) := by
  intro h
  exact (h 473165).2.2 (a 473165 + 4) middle_is_sierpinski (by norm_num [a]) (by norm_num [a])
