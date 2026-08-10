import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-- If `p` divides `N` with `1 < p < N`, then `N` is not prime. -/
private lemma comp (N p : ℕ) (h2 : 1 < p) (hd : p ∣ N) (hlt : p < N) : ¬ N.Prime := by
  intro hN
  rcases (Nat.Prime.eq_one_or_self_of_dvd hN p hd) with h | h
  · omega
  · omega

/-- Covering-set step: if `2^48 ≡ 1 [MOD p]` and `Mv * 2^m + 1 ≡ 0 [MOD p]`, then for any
    `j` with `j % 48 = m`, we have `p ∣ Mv * 2^j + 1`. -/
private lemma cover_step (Mv p m j : ℕ) (hp : (2:ℕ)^48 % p = 1 % p)
    (hm0 : (Mv * 2^m + 1) % p = 0) (hj : j % 48 = m) :
    p ∣ (Mv * 2^j + 1) := by
  have hp' : (2:ℕ)^48 ≡ 1 [MOD p] := hp
  have hm0' : (Mv * 2^m + 1) ≡ 0 [MOD p] := by
    show (Mv * 2^m + 1) % p = 0 % p
    rw [Nat.zero_mod]; exact hm0
  have hjj : j = 48 * (j / 48) + m := by omega
  have e1 : (2:ℕ)^j = (2^48)^(j/48) * 2^m := by
    conv_lhs => rw [hjj]
    rw [pow_add, pow_mul]
  have e2 : (2:ℕ)^j ≡ 2^m [MOD p] := by
    rw [e1]
    calc (2^48)^(j/48) * 2^m
        ≡ 1^(j/48) * 2^m [MOD p] := (hp'.pow _).mul_right _
      _ = 2^m := by ring
  have e3 : (Mv * 2^j + 1) ≡ 0 [MOD p] :=
    ((Nat.ModEq.refl Mv).mul e2).add_right 1 |>.trans hm0'
  exact (Nat.modEq_zero_iff_dvd).mp e3

/-- The number `5292270077783 = a(473165) + 4` is a Sierpiński number, via the covering set
    `{3, 5, 7, 17, 97, 257, 673}` with period 48. -/
private lemma sier_M : is_sierpinski_number 5292270077783 := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro j _hj
  have hge : (5292270077783:ℕ) ≤ 5292270077783 * 2^j := by
    have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
    calc (5292270077783:ℕ) = 5292270077783 * 1 := (mul_one _).symm
      _ ≤ 5292270077783 * 2^j := by exact Nat.mul_le_mul_left _ h1
  have hsplit : j % 48 = 0 ∨ j % 48 = 1 ∨ j % 48 = 2 ∨ j % 48 = 3 ∨ j % 48 = 4 ∨ j % 48 = 5 ∨ j % 48 = 6 ∨ j % 48 = 7 ∨ j % 48 = 8 ∨ j % 48 = 9 ∨ j % 48 = 10 ∨ j % 48 = 11 ∨ j % 48 = 12 ∨ j % 48 = 13 ∨ j % 48 = 14 ∨ j % 48 = 15 ∨ j % 48 = 16 ∨ j % 48 = 17 ∨ j % 48 = 18 ∨ j % 48 = 19 ∨ j % 48 = 20 ∨ j % 48 = 21 ∨ j % 48 = 22 ∨ j % 48 = 23 ∨ j % 48 = 24 ∨ j % 48 = 25 ∨ j % 48 = 26 ∨ j % 48 = 27 ∨ j % 48 = 28 ∨ j % 48 = 29 ∨ j % 48 = 30 ∨ j % 48 = 31 ∨ j % 48 = 32 ∨ j % 48 = 33 ∨ j % 48 = 34 ∨ j % 48 = 35 ∨ j % 48 = 36 ∨ j % 48 = 37 ∨ j % 48 = 38 ∨ j % 48 = 39 ∨ j % 48 = 40 ∨ j % 48 = 41 ∨ j % 48 = 42 ∨ j % 48 = 43 ∨ j % 48 = 44 ∨ j % 48 = 45 ∨ j % 48 = 46 ∨ j % 48 = 47 := by omega
  rcases hsplit with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 0 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 7 (by norm_num) (cover_step 5292270077783 7 1 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 2 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 3 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 4 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 257 (by norm_num) (cover_step 5292270077783 257 5 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 6 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 7 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 8 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 17 (by norm_num) (cover_step 5292270077783 17 9 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 10 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 11 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 12 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 7 (by norm_num) (cover_step 5292270077783 7 13 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 14 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 15 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 16 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 17 (by norm_num) (cover_step 5292270077783 17 17 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 18 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 19 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 20 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 257 (by norm_num) (cover_step 5292270077783 257 21 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 22 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 23 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 24 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 7 (by norm_num) (cover_step 5292270077783 7 25 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 26 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 27 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 28 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 97 (by norm_num) (cover_step 5292270077783 97 29 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 30 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 31 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 32 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 17 (by norm_num) (cover_step 5292270077783 17 33 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 34 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 35 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 36 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 7 (by norm_num) (cover_step 5292270077783 7 37 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 38 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 39 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 40 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 17 (by norm_num) (cover_step 5292270077783 17 41 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 42 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 43 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 44 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 673 (by norm_num) (cover_step 5292270077783 673 45 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 3 (by norm_num) (cover_step 5292270077783 3 46 j (by decide) (by decide) h) (by omega)
  · exact comp (5292270077783*2^j+1) 5 (by norm_num) (cover_step 5292270077783 5 47 j (by decide) (by decide) h) (by omega)

/--
oeis_270994_conjecture_0 (disproof): It is **not** true that for all `n`, `a(n)` and `a(n)+28`
are consecutive Sierpiński numbers. The number `5292270077783 = a(473165) + 4` is itself a
Sierpiński number lying strictly between `a(473165)` and `a(473165) + 28`.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  obtain ⟨_, _, hR⟩ := h 473165
  exact hR 5292270077783 sier_M (by norm_num [a]) (by norm_num [a])
