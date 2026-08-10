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

/--
**OEIS A224515 Conjecture 1:** A solution $k$ always exists.
Formalization: For every natural number $n$, there is a $k$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
This ensures that $a(n) \ge 0$ in the context of the OEIS definition, as the set of solutions must be non-empty.
-/
theorem xor_four_four_add_one (A B : ℕ) :
  Nat.xor (4 * A) (4 * B + 1) = 4 * (Nat.xor A B) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h4 : 4 = 2^2 := by rfl
  have h_4A : 4 * A = 2^2 * A + 0 := by rw [h4, Nat.add_zero]
  have h_4B1 : 4 * B + 1 = 2^2 * B + 1 := by rw [h4]
  have h_4X1 : 4 * (Nat.xor A B) + 1 = 2^2 * (Nat.xor A B) + 1 := by rw [h4]
  rw [h_4A, h_4B1, h_4X1]
  change ((2 ^ 2 * A + 0) ^^^ (2 ^ 2 * B + 1)).testBit j = (2 ^ 2 * Nat.xor A B + 1).testBit j
  rw [Nat.testBit_xor]
  rw [Nat.testBit_two_pow_mul_add A (by decide) j]
  rw [Nat.testBit_two_pow_mul_add B (by decide) j]
  rw [Nat.testBit_two_pow_mul_add (Nat.xor A B) (by decide) j]
  by_cases hj : j < 2
  · simp [hj]
  · simp [hj]
    rw [show (A.xor B).testBit (j - 2) = (A ^^^ B).testBit (j - 2) by rfl, Nat.testBit_xor]

def f (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    let m := k / 2
    Nat.xor (m ^ 2) (m * (m + 1))
  else
    let m := (k + 1) / 2
    Nat.xor (m * (m - 1)) (m ^ 2)

theorem xor_sq_succ_sq (k : ℕ) :
  Nat.xor (k ^ 2) ((k + 1) ^ 2) = 4 * f k + 1 := by
  have h_cases : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
  rcases h_cases with hk | hk
  · have h_even : ∃ m, k = 2 * m := by
      use k / 2
      omega
    rcases h_even with ⟨m, rfl⟩
    have h_f : f (2 * m) = Nat.xor (m ^ 2) (m * (m + 1)) := by
      unfold f
      have h_mod : (2 * m) % 2 = 0 := by omega
      rw [if_pos h_mod]
      have h_div : (2 * m) / 2 = m := by omega
      rw [h_div]
    rw [h_f]
    have h_sq1 : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    have h_sq2 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    rw [h_sq1, h_sq2]
    exact xor_four_four_add_one (m ^ 2) (m * (m + 1))
  · have h_odd : ∃ m, k = 2 * m + 1 := by
      use k / 2
      omega
    rcases h_odd with ⟨m, rfl⟩
    have h_f : f (2 * m + 1) = Nat.xor ((m + 1) * m) ((m + 1) ^ 2) := by
      unfold f
      have h_mod_ne : (2 * m + 1) % 2 ≠ 0 := by omega
      rw [if_neg h_mod_ne]
      dsimp only
      have h_div : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [h_div]
      have h_sub : m + 1 - 1 = m := by omega
      rw [h_sub]
    rw [h_f]
    have h_sq1 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    have h_sq2 : ((2 * m + 1) + 1) ^ 2 = 4 * (m + 1) ^ 2 := by ring
    rw [h_sq1, h_sq2]
    change (4 * (m * (m + 1)) + 1) ^^^ (4 * (m + 1) ^ 2) = 4 * (((m + 1) * m) ^^^ ((m + 1) ^ 2)) + 1
    rw [Nat.xor_comm (4 * (m * (m + 1)) + 1)]
    have h_xor : 4 * (m + 1) ^ 2 ^^^ (4 * (m * (m + 1)) + 1) = Nat.xor (4 * (m + 1) ^ 2) (4 * (m * (m + 1)) + 1) := rfl
    rw [h_xor]
    have h_mul_comm : (m + 1) * m = m * (m + 1) := by ring
    rw [h_mul_comm]
    rw [xor_four_four_add_one ((m + 1) ^ 2) (m * (m + 1))]
    change 4 * Nat.xor ((m + 1) ^ 2) (m * (m + 1)) + 1 = 4 * Nat.xor (m * (m + 1)) ((m + 1) ^ 2) + 1
    have h_comm : Nat.xor ((m + 1) ^ 2) (m * (m + 1)) = Nat.xor (m * (m + 1)) ((m + 1) ^ 2) := Nat.xor_comm _ _
    rw [h_comm]

theorem my_xor_mod_two_pow (A B d : ℕ) : Nat.xor A B % 2^d = Nat.xor (A % 2^d) (B % 2^d) := by
  change (A ^^^ B) % 2^d = (A % 2^d) ^^^ (B % 2^d)
  rw [Nat.xor_mod_two_pow]

theorem my_xor_assoc (A B C : ℕ) : Nat.xor (Nat.xor A B) C = Nat.xor A (Nat.xor B C) := by
  change (A ^^^ B) ^^^ C = A ^^^ (B ^^^ C)
  rw [Nat.xor_assoc]

theorem testBit_mod_two_pow (n i d : ℕ) (h : i < d) :
  (n % 2^d).testBit i = n.testBit i := by
  rw [Nat.testBit_mod_two_pow n d i]
  simp [h]

theorem testBit_add_two_pow_of_lt (B s i : ℕ) (hi : i < s) :
  (B + 2^s).testBit i = B.testBit i := by
  have h_mod : (B + 2^s) % 2^(i + 1) = B % 2^(i + 1) := by
    have h_pow : 2^s = 2^(i+1) * 2^(s - (i+1)) := by
      rw [← Nat.pow_add]
      congr
      omega
    rw [h_pow]
    exact Nat.add_mul_mod_self_left B (2^(i+1)) (2^(s - (i+1)))
  rw [← testBit_mod_two_pow _ _ (i+1) (by omega)]
  rw [h_mod]
  rw [testBit_mod_two_pow _ _ (i+1) (by omega)]

theorem testBit_add_two_pow_self (X s : ℕ) :
  (X + 2^s).testBit s = !X.testBit s := by
  rw [testBit, testBit]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h_pos : 2^s > 0 := by positivity
  have h_div : (X + 2^s) / 2^s = X / 2^s + 1 := by
    have h_eq : X + 2^s = X + 1 * 2^s := by omega
    rw [h_eq]
    rw [Nat.add_mul_div_right X 1 h_pos]
  rw [h_div]
  generalize X / 2^s = Y
  simp
  rcases Nat.mod_two_eq_zero_or_one Y with hY | hY
  · rw [show (Y + 1) % 2 = 1 by omega]
    rw [show Y % 2 = 0 by omega]
    rfl
  · rw [show (Y + 1) % 2 = 0 by omega]
    rw [show Y % 2 = 1 by omega]
    rfl

theorem xor_lt_of_div_eq (A B D : ℕ) (h_div : A / 2^D = B / 2^D) : Nat.xor A B < 2^D := by
  have h_div_xor : (Nat.xor A B) / 2^D = Nat.xor (A / 2^D) (B / 2^D) := Nat.xor_div_two_pow
  rw [h_div] at h_div_xor
  have h_self : Nat.xor (B / 2^D) (B / 2^D) = 0 := Nat.xor_self (B / 2^D)
  rw [h_self] at h_div_xor
  have h_zero : 2^D ≠ 0 := by positivity
  rw [Nat.div_eq_zero_iff] at h_div_xor
  rcases h_div_xor with h_err | h_res
  · exact False.elim (h_zero h_err)
  · exact h_res

theorem xor_lt {A B D : ℕ} (hA : A < 2^D) (hB : B < 2^D) : Nat.xor A B < 2^D := by
  have h_divA : A / 2^D = 0 := Nat.div_eq_of_lt hA
  have h_divB : B / 2^D = 0 := Nat.div_eq_of_lt hB
  exact xor_lt_of_div_eq A B D (by rw [h_divA, h_divB])

theorem add_two_pow_eq_xor (B s : ℕ) (hB : B < 2^s) :
  B + 2^s = B ^^^ 2^s := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < s
  · rw [testBit_add_two_pow_of_lt B s i hi]
    rw [Nat.testBit_xor]
    rw [Nat.testBit_two_pow]
    have h_ne : ¬(s = i) := by omega
    simp [h_ne]
  · by_cases h_eq : i = s
    · rw [h_eq]
      rw [Nat.testBit_xor]
      rw [Nat.testBit_two_pow]
      have hB_s : B.testBit s = false := Nat.testBit_eq_false_of_lt hB
      rw [hB_s]
      have h_div : (B + 2^s) >>> s = 1 := by
        rw [Nat.shiftRight_eq_div_pow]
        have h_pos : 2^s > 0 := by positivity
        have h_eq2 : B + 2^s = B + 1 * 2^s := by omega
        rw [h_eq2]
        rw [Nat.add_mul_div_right B 1 h_pos]
        have : B / 2^s = 0 := Nat.div_eq_of_lt hB
        rw [this, Nat.add_zero]
      rw [testBit]
      rw [h_div]
      simp
    · have hi_gt : s < i := by omega
      have h_lt1 : B + 2^s < 2^i := by
        calc
          B + 2^s < 2^s + 2^s := by omega
          _ = 2^(s + 1) := by ring
          _ ≤ 2^i := Nat.pow_le_pow_right (by decide) hi_gt
      rw [Nat.testBit_eq_false_of_lt h_lt1]
      rw [Nat.testBit_xor]
      rw [Nat.testBit_two_pow]
      have hB_i : B.testBit i = false := Nat.testBit_eq_false_of_lt (lt_trans hB (Nat.pow_lt_pow_right (by decide) hi_gt))
      have h_ne : ¬(s = i) := by omega
      simp [hB_i, h_ne]

theorem mod_two_pow_eq_iff_testBit_eq (A B d : ℕ) :
  A % 2^d = B % 2^d ↔ (∀ i < d, A.testBit i = B.testBit i) := by
  constructor
  · intro h i hi
    rw [← testBit_mod_two_pow _ _ _ hi, h, testBit_mod_two_pow _ _ _ hi]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < d
    · rw [testBit_mod_two_pow _ _ _ hi, testBit_mod_two_pow _ _ _ hi]
      exact h i hi
    · have h_ge : d ≤ i := by omega
      have h_lt1 : A % 2^d < 2^i := by
        calc
          A % 2^d < 2^d := Nat.mod_lt _ (by positivity)
          _ ≤ 2^i := Nat.pow_le_pow_right (by decide) h_ge
      have h_lt2 : B % 2^d < 2^i := by
        calc
          B % 2^d < 2^d := Nat.mod_lt _ (by positivity)
          _ ≤ 2^i := Nat.pow_le_pow_right (by decide) h_ge
      rw [Nat.testBit_eq_false_of_lt h_lt1, Nat.testBit_eq_false_of_lt h_lt2]

def g (m : ℕ) : ℕ := Nat.xor (m^2) (m * (m + 1))

theorem g_mod_two_pow (m d : ℕ) : g m % 2^d = g (m % 2^d) % 2^d := by
  unfold g
  rw [my_xor_mod_two_pow, my_xor_mod_two_pow]
  have h1 : m^2 % 2^d = (m % 2^d)^2 % 2^d := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have h2 : (m * (m + 1)) % 2^d = ((m % 2^d) * (m % 2^d + 1)) % 2^d := by
    have h_add_eq : (m + 1) % 2^d = (m % 2^d + 1) % 2^d := by
      by_cases hd : d = 0
      · subst hd
        simp
      · have hd_ge : d ≥ 1 := Nat.pos_of_ne_zero hd
        have h_pow_le : 2 ≤ 2^d := Nat.pow_le_pow_right (show 2 > 0 by decide) hd_ge
        have h_lt : 1 < 2^d := lt_of_lt_of_le (by decide) h_pow_le
        have : 1 % 2^d = 1 := Nat.mod_eq_of_lt h_lt
        rw [Nat.add_mod m 1, this]
    rw [Nat.mul_mod, h_add_eq]
    have h_rhs : ((m % 2^d) * (m % 2^d + 1)) % 2^d = (m % 2^d * ((m % 2^d + 1) % 2^d)) % 2^d := by
      rw [Nat.mul_mod, Nat.mod_mod]
    rw [h_rhs]
  rw [h1, h2]

theorem test_mod (m s : ℕ) : (m + 2^s) % 2^s = m % 2^s := by
  exact Nat.add_mod_right m (2^s)

theorem sq_mod_even (m K : ℕ) (hK : K % 2 = 0) :
  (m + K)^2 % (2 * K) = m^2 % (2 * K) := by
  by_cases hK0 : K = 0
  · subst hK0; rfl
  · have hK2 : K = 2 * (K / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hK)).symm
    generalize hL : K / 2 = L at hK2 ⊢
    rw [hK2]
    have h_exp : (m + 2 * L)^2 = m^2 + (2 * (2 * L)) * (m + L) := by ring
    rw [h_exp]
    exact Nat.add_mul_mod_self_left _ _ _

theorem mul_mod_even (m K : ℕ) (hK : K % 2 = 0) :
  (m + K) * (m + K + 1) % (2 * K) = (m * (m + 1) + K) % (2 * K) := by
  by_cases hK0 : K = 0
  · subst hK0; rfl
  · have hK2 : K = 2 * (K / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hK)).symm
    generalize hL : K / 2 = L at hK2 ⊢
    rw [hK2]
    have h_exp : (m + 2 * L) * (m + 2 * L + 1) = m * (m + 1) + 2 * L + (2 * (2 * L)) * (m + L) := by ring
    rw [h_exp]
    exact Nat.add_mul_mod_self_left _ _ _

theorem xor_add_two_pow (A B s : ℕ) (hA : A < 2^s) (hB : B < 2^s) :
  Nat.xor A (B + 2^s) = Nat.xor A B + 2^s := by
  rw [add_two_pow_eq_xor B s hB]
  rw [add_two_pow_eq_xor (Nat.xor A B) s (xor_lt hA hB)]
  change A ^^^ (B ^^^ 2^s) = (A ^^^ B) ^^^ 2^s
  rw [Nat.xor_assoc]

theorem xor_add_two_pow_mod (A B s : ℕ) :
  Nat.xor A (B + 2^s) % 2^(s+1) = (Nat.xor A B + 2^s) % 2^(s+1) := by
  rw [mod_two_pow_eq_iff_testBit_eq]
  intro i hi
  change (A ^^^ (B + 2^s)).testBit i = ((A ^^^ B) + 2^s).testBit i
  by_cases h_lt : i < s
  · rw [Nat.testBit_xor]
    rw [testBit_add_two_pow_of_lt B s i h_lt]
    rw [testBit_add_two_pow_of_lt (A ^^^ B) s i h_lt]
    rw [← Nat.testBit_xor]
  · have : i = s := by omega
    subst this
    rw [Nat.testBit_xor]
    rw [testBit_add_two_pow_self]
    rw [testBit_add_two_pow_self]
    rw [Nat.testBit_xor]
    generalize A.testBit i = a
    generalize B.testBit i = b
    rcases a <;> rcases b <;> rfl

theorem g_lift (m s : ℕ) (hs : s ≥ 1) : g (m + 2^s) % 2^(s+1) = (g m + 2^s) % 2^(s+1) := by
  unfold g
  rw [my_xor_mod_two_pow]
  have h_pow : 2^(s+1) = 2 * 2^s := by ring
  rw [h_pow]
  have h_even : 2^s % 2 = 0 := by
    have : 2^s = 2^(s - 1) * 2 := by
      rw [show s = s - 1 + 1 by omega]
      exact Nat.pow_succ 2 (s - 1)
    rw [this]
    omega
  rw [sq_mod_even m (2^s) h_even]
  rw [mul_mod_even m (2^s) h_even]
  rw [← h_pow]
  rw [← my_xor_mod_two_pow]
  rw [xor_add_two_pow_mod]

def solve_m (d : ℕ) (Y : ℕ) : ℕ :=
  match d with
  | 0 => 0
  | 1 => 0
  | d' + 1 =>
    let prev := solve_m d' Y
    if g prev % 2^(d' + 1) = Y % 2^(d' + 1) then
      prev
    else
      prev + 2^d'

theorem solve_m_step (d' : ℕ) (Y : ℕ) (h : d' ≥ 1) :
  solve_m (d' + 1) Y =
    let prev := solve_m d' Y
    if g prev % 2^(d' + 1) = Y % 2^(d' + 1) then prev else prev + 2^d' := by
  obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
  rfl

theorem mod_mul_two_cases (X K : ℕ) :
  X % (K * 2) = X % K ∨ X % (K * 2) = X % K + K := by
  have hK : K = 0 ∨ K > 0 := by omega
  rcases hK with rfl | hK
  · simp
  · rcases Nat.mod_two_eq_zero_or_one (X / K) with hq | hq
    · left
      let q := (X / K) / 2
      have hq_eq : X / K = 2 * q := by omega
      have h_div : X = X % K + (K * 2) * q := by
        have h_eq : X = K * (X / K) + X % K := (Nat.div_add_mod X K).symm
        nth_rw 1 [h_eq]
        rw [hq_eq]
        ring
      nth_rw 1 [h_div]
      rw [Nat.add_mul_mod_self_left (X % K) (K * 2) q]
      have h_lt : X % K < K * 2 := by
        have : X % K < K := Nat.mod_lt X hK
        clear h_div hq_eq hq
        omega
      exact Nat.mod_eq_of_lt h_lt
    · right
      let q := (X / K) / 2
      have hq_eq : X / K = 2 * q + 1 := by omega
      have h_div : X = (X % K + K) + (K * 2) * q := by
        have h_eq : X = K * (X / K) + X % K := (Nat.div_add_mod X K).symm
        nth_rw 1 [h_eq]
        rw [hq_eq]
        ring
      nth_rw 1 [h_div]
      rw [Nat.add_mul_mod_self_left (X % K + K) (K * 2) q]
      have h_lt : X % K + K < K * 2 := by
        have : X % K < K := Nat.mod_lt X hK
        clear h_div hq_eq hq
        omega
      exact Nat.mod_eq_of_lt h_lt

theorem solve_m_correct (d : ℕ) (Y : ℕ) (hd : d ≥ 1) (hY : Y % 2 = 0) :
  g (solve_m d Y) % 2^d = Y % 2^d := by
  induction d, hd using Nat.le_induction with
  | base =>
    have : solve_m 1 Y = 0 := rfl
    rw [this]
    have : g 0 = 0 := rfl
    rw [this]
    omega
  | succ d' hd' ih =>
    rw [solve_m_step d' Y hd']
    dsimp only
    have h_pow_eq : 2^(d' + 1) = 2^d' * 2 := rfl
    rw [h_pow_eq]
    by_cases h_eq : g (solve_m d' Y) % (2^d' * 2) = Y % (2^d' * 2)
    · rw [if_pos h_eq]
      exact h_eq
    · rw [if_neg h_eq]
      rw [← h_pow_eq]
      rw [g_lift _ _ hd']
      rw [h_pow_eq]
      have h_pow : 2^d' > 0 := by positivity
      have h_split : g (solve_m d' Y) % (2^d' * 2) = Y % (2^d' * 2) ∨
                     g (solve_m d' Y) % (2^d' * 2) = (Y + 2^d') % (2^d' * 2) := by
        have hA := mod_mul_two_cases (g (solve_m d' Y)) (2^d')
        have hB := mod_mul_two_cases Y (2^d')
        have hC := mod_mul_two_cases (Y + 2^d') (2^d')
        rw [ih] at hA
        have h_mod_add : (Y + 2^d') % 2^d' = Y % 2^d' := Nat.add_mod_right Y (2^d')
        rw [h_mod_add] at hC
        have h_ne : Y % (2^d' * 2) ≠ (Y + 2^d') % (2^d' * 2) := by
          intro h_eq_mod
          have h_mod : (Y + 2^d') % (2^d' * 2) = (Y % (2^d' * 2) + 2^d') % (2^d' * 2) := by
            have h_lt : 2^d' < 2^d' * 2 := by
              generalize 2^d' = V at h_pow ⊢
              omega
            have : 2^d' % (2^d' * 2) = 2^d' := Nat.mod_eq_of_lt h_lt
            rw [Nat.add_mod, this]
          rw [h_mod] at h_eq_mod
          have h_lt_V : Y % (2^d' * 2) < 2^d' * 2 := Nat.mod_lt Y (by positivity)
          generalize Y % (2^d' * 2) = V at h_eq_mod h_lt_V ⊢
          generalize h_W : 2^d' = W at h_eq_mod h_lt_V ⊢
          rcases Nat.lt_or_ge V W with h_lt | h_ge
          · have : V + W < W * 2 := by omega
            rw [Nat.mod_eq_of_lt this] at h_eq_mod
            omega
          · have : V + W = (V - W) + (W * 2) * 1 := by omega
            rw [this, Nat.add_mul_mod_self_left (V - W) (W * 2) 1] at h_eq_mod
            have : V - W < W * 2 := by omega
            rw [Nat.mod_eq_of_lt this] at h_eq_mod
            omega
        generalize h_W : 2^d' = W at hA hB hC h_ne ⊢
        generalize h_X : g (solve_m d' Y) % (W * 2) = X at hA ⊢
        generalize h_Y_mod : Y % (W * 2) = Y_mod at hB h_ne ⊢
        generalize h_C_mod : (Y + W) % (W * 2) = C_mod at hC h_ne ⊢
        generalize h_B_mod : Y % W = B_mod at hA hB hC
        omega
      rcases h_split with h_left | h_right
      · exact False.elim (h_eq h_left)
      · rw [Nat.add_mod]
        rw [h_right]
        rw [← Nat.add_mod]
        have : (Y + 2^d' + 2^d') % (2^d' * 2) = Y % (2^d' * 2) := by
          generalize h_W : 2^d' = W
          have h_add_W : W * 2 = W + W := by ring
          rw [h_add_W]
          rw [Nat.add_assoc]
          exact Nat.add_mod_right Y (W + W)
        exact this

theorem solve_m_lt (d : ℕ) (Y : ℕ) : solve_m d Y < 2^d := by
  induction d with
  | zero =>
    have : solve_m 0 Y = 0 := rfl
    rw [this]
    decide
  | succ d' ih =>
    by_cases hd' : d' = 0
    · subst hd'
      have : solve_m 1 Y = 0 := rfl
      rw [this]
      decide
    · have hd'_ge : d' ≥ 1 := by omega
      rw [solve_m_step d' Y hd'_ge]
      dsimp only
      by_cases h_eq : g (solve_m d' Y) % 2^(d' + 1) = Y % 2^(d' + 1)
      · rw [if_pos h_eq]
        have : solve_m d' Y < 2^(d' + 1) := by
          have : 2^d' < 2^(d' + 1) := by
            have : 2^(d' + 1) = 2 * 2^d' := by ring
            omega
          omega
        exact this
      · rw [if_neg h_eq]
        have : 2^(d' + 1) = 2 * 2^d' := by ring
        omega

theorem comp_sq_mod (x D : ℕ) (hx : x ≤ 2^D) : (2^D - x)^2 % 2^D = x^2 % 2^D := by
  have h_sub : (((2^D - x) : ℕ) : ℤ) = (2^D : ℤ) - (x : ℤ) := Nat.cast_sub hx
  have h_id : (((2^D - x)^2 : ℕ) : ℤ) + 2 * (x : ℤ) * (2^D : ℤ) = (2^D : ℤ)^2 + (x : ℤ)^2 := by
    push_cast
    rw [h_sub]
    ring
  have h_nat : (2^D - x)^2 + 2 * x * 2^D = (2^D)^2 + x^2 := by
    exact_mod_cast h_id
  rw [show (2^D)^2 = 2^D * 2^D by ring] at h_nat
  have h_mod : ((2^D - x)^2 + 2 * x * 2^D) % 2^D = ((2^D * 2^D) + x^2) % 2^D := by rw [h_nat]
  rw [Nat.add_mul_mod_self_right] at h_mod
  rw [show (2^D * 2^D + x^2) = x^2 + 2^D * 2^D by ring] at h_mod
  rw [Nat.add_mul_mod_self_left] at h_mod
  exact h_mod

theorem comp_mul_mod_correct (x D : ℕ) (hx : x ≤ 2^D) (hx1 : x ≥ 1) :
  (2^D - x) * (2^D - x + 1) % 2^D = x * (x - 1) % 2^D := by
  have h_sub : (((2^D - x) : ℕ) : ℤ) = (2^D : ℤ) - (x : ℤ) := Nat.cast_sub hx
  have h_sub1 : (((x - 1) : ℕ) : ℤ) = (x : ℤ) - 1 := Nat.cast_sub hx1
  have h_id : (((2^D - x) * (2^D - x + 1) : ℕ) : ℤ) + 2 * (x : ℤ) * (2^D : ℤ) = (2^D : ℤ)^2 + (2^D : ℤ) + (((x * (x - 1) : ℕ) : ℤ)) := by
    push_cast
    rw [h_sub, h_sub1]
    ring
  have h_nat : (2^D - x) * (2^D - x + 1) + 2 * x * 2^D = (2^D)^2 + 2^D + x * (x - 1) := by
    exact_mod_cast h_id
  rw [show (2^D)^2 = 2^D * 2^D by ring] at h_nat
  have h_mod : ((2^D - x) * (2^D - x + 1) + 2 * x * 2^D) % 2^D = ((2^D * 2^D) + 2^D + x * (x - 1)) % 2^D := by rw [h_nat]
  rw [Nat.add_mul_mod_self_right] at h_mod
  rw [show 2^D * 2^D + 2^D + x * (x - 1) = x * (x - 1) + (2^D + 1) * 2^D by ring] at h_mod
  rw [Nat.add_mul_mod_self_right] at h_mod
  exact h_mod

theorem pronic_lt_two_pow (n : ℕ) : n * (n + 1) < 2^(n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h_pow : 2^(n + 2) = 2^(n + 1) + 2^(n + 1) := by ring
    rw [h_pow]
    by_cases hn : n < 2
    · interval_cases n <;> decide
    · have hn2 : n ≥ 2 := by omega
      have h_ge : n * (n + 1) < 2^(n + 1) := ih
      nlinarith

theorem f_odd_eq_xor (m : ℕ) (hm : m ≥ 1) :
  f (2 * m - 1) = Nat.xor (m^2) (m * (m - 1)) := by
  have h_odd : (2 * m - 1) % 2 = 1 := by omega
  unfold f
  have h_mod_ne : (2 * m - 1) % 2 ≠ 0 := by omega
  rw [if_neg h_mod_ne]
  dsimp only
  have h_div : (2 * m - 1 + 1) / 2 = m := by omega
  rw [h_div]
  have h_sub : m - 1 = m - 1 := rfl
  rw [h_sub]
  exact Nat.xor_comm _ _

theorem f_odd_mod_comp (m D : ℕ) (hm : m ≥ 1) (hm_le : m ≤ 2^D) :
  f (2 * m - 1) % 2^D = g (2^D - m) % 2^D := by
  rw [f_odd_eq_xor m hm]
  unfold g
  rw [my_xor_mod_two_pow, my_xor_mod_two_pow]
  rw [comp_sq_mod m D hm_le]
  rw [comp_mul_mod_correct m D hm_le hm]

theorem g_lt_of_carry_zero (M D : ℕ) (h_carry : M^2 % 2^D + M < 2^D) : g M < 2^D := by
  unfold g
  have h_mul : M * (M + 1) = M^2 + M := by ring
  rw [h_mul]
  have h_div_eq : (M^2) / 2^D = (M^2 + M) / 2^D := by
    have h_pos : 2^D > 0 := by positivity
    have h_div_add : 2^D * (M^2 / 2^D) + M^2 % 2^D = M^2 := Nat.div_add_mod (M^2) (2^D)
    have h_comm : (M^2 / 2^D) * 2^D = 2^D * (M^2 / 2^D) := Nat.mul_comm _ _
    have h_eq : M^2 + M = (M^2 % 2^D + M) + (M^2 / 2^D) * 2^D := by rw [h_comm]; omega
    rw [h_eq]
    rw [Nat.add_mul_div_right _ _ h_pos]
    have h_div_zero : (M^2 % 2^D + M) / 2^D = 0 := Nat.div_eq_of_lt h_carry
    rw [h_div_zero, Nat.zero_add]
  exact xor_lt_of_div_eq (M^2) (M^2 + M) D h_div_eq

theorem f_odd_lt_of_carry_one (M D M' : ℕ) (h_M : M < 2^D) (hM' : M' = 2^D - M) (h_carry : M^2 % 2^D + M ≥ 2^D) :
  f (2 * M' - 1) < 2^D := by
  have hM'_pos : M' ≥ 1 := by omega
  rw [f_odd_eq_xor M' hM'_pos]
  have h_div_eq : (M'^2) / 2^D = (M' * (M' - 1)) / 2^D := by
    have h_D_pos : 2^D > 0 := by positivity
    generalize hR : M^2 % 2^D = R
    generalize hW : M^2 / 2^D = W
    have h_div_add : 2^D * W + R = M^2 := by
      rw [← hW, ← hR]
      exact Nat.div_add_mod (M^2) (2^D)
    have h_sum : 2^D = M' + M := by omega
    have h_sub_add : M' * (M' - 1) + M' = M'^2 := by
      have h_eq : M' * (M' - 1) + M' = M' * (M' - 1) + M' * 1 := by omega
      rw [h_eq]
      rw [← Nat.mul_add]
      rw [Nat.sub_add_cancel hM'_pos]
      rw [Nat.pow_two]
    have h_eq1 : M'^2 + 2 * M * 2^D = R + (2^D + W) * 2^D := by
      rw [show R + (2^D + W) * 2^D = (2^D * W + R) + 2^D * 2^D by ring]
      rw [h_div_add]
      rw [h_sum]
      ring
    have h_eq2 : M' * (M' - 1) + 2 * M * 2^D = (R + M - 2^D) + (2^D + W) * 2^D := by
      have h_id : M' * (M' - 1) + 2 * M * 2^D + M' + 2^D = (R + M - 2^D) + (2^D + W) * 2^D + M' + 2^D := by
        have h_carry_eq : R + M - 2^D + 2^D = R + M := by omega
        rw [show M' * (M' - 1) + 2 * M * 2^D + M' + 2^D = (M' * (M' - 1) + M') + 2 * M * 2^D + 2^D by omega]
        rw [h_sub_add]
        rw [show R + M - 2^D + (2^D + W) * 2^D + M' + 2^D =
                  (R + M - 2^D + 2^D) + (2^D + W) * 2^D + M' by omega]
        rw [h_carry_eq]
        have h_rw : R + M + ((M' + M) + W) * (M' + M) + M' = (2^D * W + R) + M + (M' + M) * (M' + M) + M' := by
          rw [h_sum]
          ring
        rw [h_sum]
        rw [h_rw]
        rw [h_div_add]
        ring
      omega
    have h_div_eq1 : (M'^2 + 2 * M * 2^D) / 2^D = 2^D + W := by
      rw [h_eq1]
      rw [Nat.add_mul_div_right _ _ h_D_pos]
      have : R / 2^D = 0 := by
        apply Nat.div_eq_of_lt
        rw [← hR]
        exact Nat.mod_lt _ h_D_pos
      rw [this, Nat.zero_add]
    have h_div_eq2 : (M' * (M' - 1) + 2 * M * 2^D) / 2^D = 2^D + W := by
      rw [h_eq2]
      rw [Nat.add_mul_div_right _ _ h_D_pos]
      have : (R + M - 2^D) / 2^D = 0 := by
        apply Nat.div_eq_of_lt
        omega
      rw [this, Nat.zero_add]
    have h_add_div1 : (M'^2 + 2 * M * 2^D) / 2^D = M'^2 / 2^D + 2 * M := by
      rw [Nat.add_mul_div_right _ _ h_D_pos]
    have h_add_div2 : (M' * (M' - 1) + 2 * M * 2^D) / 2^D = M' * (M' - 1) / 2^D + 2 * M := by
      rw [Nat.add_mul_div_right _ _ h_D_pos]
    omega
  exact xor_lt_of_div_eq (M'^2) (M' * (M' - 1)) D h_div_eq

theorem A224515_conjecture_existence (n : ℕ) :
  ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  have h_target : (2 * n + 1) ^ 2 = 4 * (n * (n + 1)) + 1 := by ring
  let Y := n * (n + 1)
  let D := n + 1
  have hY_even : Y % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [Nat.mul_mod, hn, Nat.zero_mul, Nat.zero_mod]
    · have h_mod : (n + 1) % 2 = 0 := by omega
      rw [Nat.mul_mod, h_mod, Nat.mul_zero, Nat.zero_mod]
  have hD : D ≥ 1 := by omega
  have h_solve : g (solve_m D Y) % 2^D = Y % 2^D := solve_m_correct D Y hD hY_even
  have h_lt : Y < 2^D := pronic_lt_two_pow n
  rw [Nat.mod_eq_of_lt h_lt] at h_solve
  let M := solve_m D Y
  have h_M_lt : M < 2^D := solve_m_lt D Y
  by_cases h_carry : M^2 % 2^D + M < 2^D
  · use 2 * M
    rw [h_target]
    rw [xor_sq_succ_sq]
    have h_even : (2 * M) % 2 = 0 := by omega
    have h_f : f (2 * M) = g M := by
      unfold f
      rw [if_pos h_even]
      have : (2 * M) / 2 = M := by omega
      rw [this]
      rfl
    rw [h_f]
    have h_g_lt : g M < 2^D := g_lt_of_carry_zero M D h_carry
    have h_mod_g : g M % 2^D = g M := Nat.mod_eq_of_lt h_g_lt
    rw [← h_mod_g, h_solve]
  · have h_carry_ge : M^2 % 2^D + M ≥ 2^D := by omega
    let M' := 2^D - M
    have hM'_pos : M' ≥ 1 := by omega
    use 2 * M' - 1
    rw [h_target]
    rw [xor_sq_succ_sq]
    have h_f_lt : f (2 * M' - 1) < 2^D := f_odd_lt_of_carry_one M D M' h_M_lt rfl h_carry_ge
    have h_f_mod : f (2 * M' - 1) % 2^D = f (2 * M' - 1) := Nat.mod_eq_of_lt h_f_lt
    rw [← h_f_mod]
    have hM'_le : M' ≤ 2^D := by omega
    rw [f_odd_mod_comp M' D hM'_pos hM'_le]
    have h_eq : 2^D - M' = M := by omega
    rw [h_eq, h_solve]

