import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A224515: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1, \text{ } a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.
-/
noncomputable def A224515 (n : ℕ) : ℕ :=
  -- The term (2*n + 1)^2 is the target value.
  let target_sq : ℕ := (2 * n + 1) ^ 2
  -- Define the set of candidate k's.
  sInf { k : ℕ | Nat.xor (k ^ 2) ((k + 1) ^ 2) = target_sq }

namespace A224515Aux

/-- The carry identity `a + b = (a ^^^ b) + 2 * (a &&& b)`. -/
theorem add_xor (a b : ℕ) : a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit ba a' iha =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit bb b' _ =>
      have h := iha b'
      rw [Nat.xor_bit, Nat.land_bit]
      cases ba <;> cases bb <;>
        simp only [Nat.bit_false, Nat.bit_true, bne_self_eq_false,
          Bool.false_bne, Bool.bne_false, Bool.and_self,
          Bool.and_false, Bool.false_and] <;> omega

/-- Distributivity of `&&&` over `^^^`. -/
theorem xor_and_distrib (a b c : ℕ) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_xor]
  cases Nat.testBit a i <;> cases Nat.testBit b i <;> cases Nat.testBit c i <;> rfl

/-- `(k + 2^i)^2 ≡ k^2 (mod 2^(i+1))` for `i ≥ 1`. -/
theorem sq_mod (k i : ℕ) (hi : 1 ≤ i) :
    (k + 2 ^ i) ^ 2 % 2 ^ (i + 1) = k ^ 2 % 2 ^ (i + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have key : (k + 2 ^ (j + 1)) ^ 2 = k ^ 2 + 2 ^ (j + 1 + 1) * (k + 2 ^ j) := by ring
  rw [key, Nat.add_mul_mod_self_left]

/-- `&&&` respects congruence mod a power of two. -/
theorem and_modeq (x y M t : ℕ) (h : x % 2 ^ t = y % 2 ^ t) :
    (x &&& M) % 2 ^ t = (y &&& M) % 2 ^ t := by
  rw [Nat.and_mod_two_pow, Nat.and_mod_two_pow, h]

/-- If `a + s = 2^w` then `a^2 ≡ s^2 (mod 2^w)`. -/
theorem sq_compl (a s w : ℕ) (h : a + s = 2 ^ w) :
    a ^ 2 % 2 ^ w = s ^ 2 % 2 ^ w := by
  have e1 : a ^ 2 + a * s = a * 2 ^ w := by rw [← h]; ring
  have e2 : s ^ 2 + a * s = s * 2 ^ w := by rw [← h]; ring
  have m1 : (a ^ 2 + a * s) % 2 ^ w = 0 := by rw [e1]; exact Nat.mul_mod_left a (2 ^ w)
  have m2 : (s ^ 2 + a * s) % 2 ^ w = 0 := by rw [e2]; exact Nat.mul_mod_left s (2 ^ w)
  have : (a ^ 2 + a * s) % 2 ^ w = (s ^ 2 + a * s) % 2 ^ w := by rw [m1, m2]
  exact Nat.ModEq.add_right_cancel' (a * s) this

/-- The key step: incrementing `k` by `2^i` shifts `g` by `2^i` modulo `2^(i+1)`. -/
theorem g_shift (M k i : ℕ) (hi : 1 ≤ i) :
    ((k + 2 ^ i) + ((k + 2 ^ i) ^ 2 &&& M)) % 2 ^ (i + 1)
      = ((k + (k ^ 2 &&& M)) + 2 ^ i) % 2 ^ (i + 1) := by
  have hT : ((k + 2 ^ i) ^ 2 &&& M) % 2 ^ (i + 1) = (k ^ 2 &&& M) % 2 ^ (i + 1) :=
    and_modeq _ _ _ _ (sq_mod k i hi)
  have hmod : ((k + 2 ^ i) ^ 2 &&& M) ≡ (k ^ 2 &&& M) [MOD 2 ^ (i + 1)] := hT
  have := hmod.add_left (k + 2 ^ i)
  unfold Nat.ModEq at this
  rw [this]
  congr 1
  ring

/-- The arithmetic lemma resolving the bit choice in the inductive step. -/
theorem arith (A N P : ℕ) (hP : 1 ≤ P) (h1 : A % P = N % P)
    (h2 : A % (2 * P) ≠ N % (2 * P)) : (A + P) % (2 * P) = N % (2 * P) := by
  have hP2 : 0 < 2 * P := by omega
  set a := A % (2 * P) with ha
  set b := N % (2 * P) with hb
  have halt : a < 2 * P := Nat.mod_lt _ hP2
  have hblt : b < 2 * P := Nat.mod_lt _ hP2
  have hdvd : P ∣ 2 * P := ⟨2, by ring⟩
  have hap : a % P = N % P := by rw [ha, Nat.mod_mod_of_dvd _ hdvd, h1]
  have hbp : b % P = N % P := by rw [hb, Nat.mod_mod_of_dvd _ hdvd]
  have hab : a % P = b % P := by rw [hap, hbp]
  have hne : a ≠ b := by rw [ha, hb]; exact h2
  have hgoal : (A + P) % (2 * P) = (a + P) % (2 * P) := by rw [ha, Nat.mod_add_mod]
  rw [hgoal]
  have da := Nat.div_add_mod a P
  have db := Nat.div_add_mod b P
  have hua : a / P < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hub : b / P < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hdisj : a + P = b ∨ a + P = b + 2 * P := by
    interval_cases (a / P) <;> interval_cases (b / P) <;> omega
  rcases hdisj with h | h
  · rw [h]; exact Nat.mod_eq_of_lt hblt
  · rw [h, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hblt

/-- Solvability of the congruence `k + (k^2 &&& M) ≡ N (mod 2^i)` for all `i`,
when `N` is even. -/
theorem stepA (M N : ℕ) (hN : N % 2 = 0) :
    ∀ i, ∃ k, k < 2 ^ i ∧ (k + (k ^ 2 &&& M)) % 2 ^ i = N % 2 ^ i := by
  intro i
  induction i with
  | zero => exact ⟨0, by simp, by simp [Nat.mod_one]⟩
  | succ i ih =>
    obtain ⟨k, hk, hg⟩ := ih
    by_cases hc : (k + (k ^ 2 &&& M)) % 2 ^ (i + 1) = N % 2 ^ (i + 1)
    · refine ⟨k, ?_, hc⟩
      have : (2 : ℕ) ^ i ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · interval_cases k
          exact absurd (by simp [hN]) hc
        · exact h
      refine ⟨k + 2 ^ i, ?_, ?_⟩
      · have h2P : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
        omega
      · rw [g_shift M k i hi]
        have h2P : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
        rw [h2P] at hc ⊢
        exact arith _ N (2 ^ i) Nat.one_le_two_pow hg hc

/-- The equivalence `k^2 ^^^ (k+1)^2 = M ↔ k + (k^2 &&& M) = N` when `M = 2N+1`. -/
theorem equiv (M N k : ℕ) (hM : M = 2 * N + 1) :
    (k ^ 2 ^^^ (k + 1) ^ 2 = M) ↔ (k + (k ^ 2 &&& M) = N) := by
  have hax := add_xor (k ^ 2) M
  have he : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  constructor
  · intro h
    have hc : k ^ 2 ^^^ M = (k + 1) ^ 2 := by
      rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [hc, he] at hax
    omega
  · intro h
    have key : (k ^ 2 ^^^ M) + 2 * (k ^ 2 &&& M) = (k + 1) ^ 2 + 2 * (k ^ 2 &&& M) := by
      rw [← hax, he]; omega
    have hc : k ^ 2 ^^^ M = (k + 1) ^ 2 := Nat.add_right_cancel key
    rw [← hc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- The main existence statement. -/
theorem main (n : ℕ) :
    ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  set M := (2 * n + 1) ^ 2 with hMdef
  have hM : M = 2 * (2 * n ^ 2 + 2 * n) + 1 := by rw [hMdef]; ring
  set N := 2 * n ^ 2 + 2 * n with hNdef
  have hNeven : N % 2 = 0 := by rw [hNdef]; omega
  have hwM : M < 2 ^ (M + 1) := by
    calc M < 2 ^ M := Nat.lt_two_pow_self
      _ ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNM : N < M := by omega
  have hwN : N < 2 ^ (M + 1) := lt_trans hNM hwM
  obtain ⟨k0, hk0lt, hk0g⟩ := stepA M N hNeven (M + 1)
  have hNmod : N % 2 ^ (M + 1) = N := Nat.mod_eq_of_lt hwN
  rw [hNmod] at hk0g
  set c0 := k0 ^ 2 &&& M with hc0def
  have hc0le : c0 ≤ M := Nat.and_le_right
  set g := k0 + c0 with hgdef
  have hglt : g < 2 * 2 ^ (M + 1) := by rw [hgdef]; omega
  have hgmod : g % 2 ^ (M + 1) = N := hk0g
  have hcases : g = N ∨ g = N + 2 ^ (M + 1) := by
    have hdq := Nat.div_add_mod g (2 ^ (M + 1))
    have hd2 : g / 2 ^ (M + 1) < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    interval_cases (g / 2 ^ (M + 1)) <;> omega
  rcases hcases with hgN | hgN
  · refine ⟨k0, ?_⟩
    show k0 ^ 2 ^^^ (k0 + 1) ^ 2 = M
    exact (equiv M N k0 hM).mpr (by rw [← hc0def, ← hgdef]; exact hgN)
  · set w := M + 1 with hwdef
    have hax := add_xor (k0 ^ 2) M
    have h2w1 : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
    have HE0 : (k0 + 1) ^ 2 + 2 * c0 = (k0 ^ 2 ^^^ M) + 2 ^ (w + 1) + 2 * c0 := by
      rw [hc0def] at *
      rw [show (k0 + 1) ^ 2 = k0 ^ 2 + 2 * k0 + 1 by ring]
      have : g = N + 2 ^ w := hgN
      rw [hgdef] at this
      omega
    have HE : (k0 + 1) ^ 2 = (k0 ^ 2 ^^^ M) + 2 ^ (w + 1) := Nat.add_right_cancel HE0
    have hdmod : ((k0 ^ 2 ^^^ M) + 2 ^ (w + 1)) % 2 ^ w = (k0 ^ 2 ^^^ M) % 2 ^ w := by
      rw [h2w1, Nat.add_mul_mod_self_left]
    have hand1 : ((k0 + 1) ^ 2 &&& M) % 2 ^ w = ((k0 ^ 2 ^^^ M) &&& M) % 2 ^ w := by
      rw [HE]; exact and_modeq _ _ _ _ hdmod
    have hMw : M < 2 ^ w := hwM
    have hd1 : (k0 + 1) ^ 2 &&& M = (k0 ^ 2 ^^^ M) &&& M := by
      have l1 : (k0 + 1) ^ 2 &&& M ≤ M := Nat.and_le_right
      have l2 : (k0 ^ 2 ^^^ M) &&& M ≤ M := Nat.and_le_right
      have e1 : ((k0 + 1) ^ 2 &&& M) % 2 ^ w = (k0 + 1) ^ 2 &&& M := Nat.mod_eq_of_lt (by omega)
      have e2 : ((k0 ^ 2 ^^^ M) &&& M) % 2 ^ w = (k0 ^ 2 ^^^ M) &&& M := Nat.mod_eq_of_lt (by omega)
      rw [← e1, ← e2, hand1]
    have hd2 : (k0 ^ 2 ^^^ M) &&& M = c0 ^^^ M := by
      rw [xor_and_distrib, Nat.and_self, hc0def]
    have hdval : (k0 + 1) ^ 2 &&& M = c0 ^^^ M := by rw [hd1, hd2]
    have hc0M : c0 &&& M = c0 := by rw [hc0def, Nat.and_assoc, Nat.and_self]
    have hsum : c0 + (c0 ^^^ M) = M := by
      have hax2 := add_xor c0 (c0 ^^^ M)
      have hcc : c0 ^^^ (c0 ^^^ M) = M := by
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hand0 : c0 &&& (c0 ^^^ M) = 0 := by
        rw [Nat.and_comm, xor_and_distrib, Nat.and_self, Nat.and_comm M c0, hc0M, Nat.xor_self]
      rw [hcc, hand0] at hax2
      omega
    have hk0le : k0 ≤ 2 ^ w - 1 := by omega
    set k1 := 2 ^ w - 1 - k0 with hk1def
    have hk1k0 : k1 + k0 + 1 = 2 ^ w := by rw [hk1def]; omega
    have hsq : k1 ^ 2 % 2 ^ w = (k0 + 1) ^ 2 % 2 ^ w := by
      apply sq_compl
      rw [hk1def]; omega
    have hk1and : k1 ^ 2 &&& M = (k0 + 1) ^ 2 &&& M := by
      have l1 : k1 ^ 2 &&& M ≤ M := Nat.and_le_right
      have l2 : (k0 + 1) ^ 2 &&& M ≤ M := Nat.and_le_right
      have e1 : (k1 ^ 2 &&& M) % 2 ^ w = k1 ^ 2 &&& M := Nat.mod_eq_of_lt (by omega)
      have e2 : ((k0 + 1) ^ 2 &&& M) % 2 ^ w = (k0 + 1) ^ 2 &&& M := Nat.mod_eq_of_lt (by omega)
      have := and_modeq (k1 ^ 2) ((k0 + 1) ^ 2) M w hsq
      rw [e1, e2] at this
      exact this
    have hgk1 : k1 + (k1 ^ 2 &&& M) = N := by
      rw [hk1and, hdval]
      have hgNw : g = N + 2 ^ w := hgN
      rw [hgdef] at hgNw
      omega
    refine ⟨k1, ?_⟩
    show k1 ^ 2 ^^^ (k1 + 1) ^ 2 = M
    exact (equiv M N k1 hM).mpr hgk1

end A224515Aux

/--
**OEIS A224515 Conjecture 1:** A solution $k$ always exists.
Formalization: For every natural number $n$, there is a $k$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
This ensures that $a(n) \ge 0$ in the context of the OEIS definition, as the set of solutions must be non-empty.
-/
theorem A224515_conjecture_existence (n : ℕ) :
  ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 :=
  A224515Aux.main n
