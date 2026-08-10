import FormalConjectures.Util.ProblemImports

open Nat

theorem testBit_mod_two_pow (n i d : ℕ) (h : i < d) :
  (n % 2^d).testBit i = n.testBit i := by
  exact Nat.testBit_mod_two_pow n i d h

theorem xor_mod_two_pow (A B d : ℕ) : (Nat.xor A B) % 2^d = Nat.xor (A % 2^d) (B % 2^d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < d
  · rw [Nat.testBit_mod_two_pow _ _ _ h]
    rw [Nat.testBit_xor]
    rw [Nat.testBit_mod_two_pow _ _ _ h]
    rw [Nat.testBit_mod_two_pow _ _ _ h]
    rfl
  · have h_ge : d ≤ i := omega
    have h_lt1 : (Nat.xor A B) % 2^d < 2^i := by
      calc
        (Nat.xor A B) % 2^d < 2^d := Nat.mod_lt _ (by positivity)
        _ ≤ 2^i := Nat.pow_le_pow_right (by decide) h_ge
    rw [Nat.testBit_eq_false_of_lt h_lt1]
    have h_lt2 : Nat.xor (A % 2^d) (B % 2^d) < 2^i := by
      calc
        Nat.xor (A % 2^d) (B % 2^d) < 2^d := Nat.xor_lt (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
        _ ≤ 2^i := Nat.pow_le_pow_right (by decide) h_ge
    rw [Nat.testBit_eq_false_of_lt h_lt2]

theorem mod_two_pow_eq_iff_testBit_eq (A B d : ℕ) :
  A % 2^d = B % 2^d ↔ (∀ i < d, A.testBit i = B.testBit i) := by
  constructor
  · intro h i hi
    rw [← Nat.testBit_mod_two_pow _ _ _ hi, h, Nat.testBit_mod_two_pow _ _ _ hi]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < d
    · rw [Nat.testBit_mod_two_pow _ _ _ hi, Nat.testBit_mod_two_pow _ _ _ hi]
      exact h i hi
    · have h_ge : d ≤ i := omega
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
  rw [xor_mod_two_pow, xor_mod_two_pow]
  congr 1
  · rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod, Nat.mod_mod]
  · rw [Nat.mul_mod, Nat.mul_mod]
    rw [Nat.mod_mod]
    congr 1
    rw [Nat.add_mod, Nat.add_mod, Nat.mod_mod]

theorem test_mod (m s : ℕ) : (m + 2^s) % 2^s = m % 2^s := by
  have : 2^s > 0 := Nat.pos_of_ne_zero (by positivity)
  omega

theorem comp_sq_mod (x D : ℕ) (hx : x ≤ 2^D) : (2^D - x)^2 % 2^D = x^2 % 2^D := by
  by_cases hD : 2^D = 0
  · rw [hD]; rfl
  · have : 2^D > 0 := Nat.pos_of_ne_zero hD
    -- (2^D - x)^2 + 2 * 2^D * x = (2^D)^2 + x^2
    have h_eq : (2^D - x)^2 + 2 * 2^D * x = (2^D)^2 + x^2 := by
      -- we can use omega to prove this because it is an equality of natural numbers
      omega
    rw [show (2^D)^2 = 2^D * 2^D by ring] at h_eq
    have h_mod : ((2^D - x)^2 + 2 * 2^D * x) % 2^D = ((2^D * 2^D) + x^2) % 2^D := by rw [h_eq]
    rw [Nat.add_mul_mod_self_left] at h_mod
    rw [Nat.add_mul_mod_self_left] at h_mod
    exact h_mod

theorem comp_mul_mod (x D : ℕ) (hx : x ≤ 2^D) (hx1 : x ≥ 1) :
  (2^D - x) * (2^D - x + 1) % 2^D = x * (x - 1) % 2^D := by
  by_cases hD : 2^D = 0
  · rw [hD]; rfl
  · have : 2^D > 0 := Nat.pos_of_ne_zero hD
    have h_eq : (2^D - x) * (2^D - x + 1) + 2 * 2^D * x = (2^D)^2 + 2^D + x * (x - 1) := by
      omega
    rw [show (2^D)^2 = 2^D * 2^D by ring] at h_eq
    have h_mod : ((2^D - x) * (2^D - x + 1) + 2 * 2^D * x) % 2^D = ((2^D * 2^D) + 2^D + x * (x - 1)) % 2^D := by rw [h_eq]
    rw [Nat.add_mul_mod_self_left] at h_mod
    rw [Nat.add_mul_mod_self_left] at h_mod
    rw [show 2^D * 2^D + 2^D + x * (x - 1) = 2^D * (2^D + 1) + x * (x - 1) by ring] at h_mod
    rw [Nat.add_mul_mod_self_left] at h_mod
    exact h_mod

theorem g_lt (m d : ℕ) (hm : m < 2^d) : g m < 2^(2 * d) := by
  unfold g
  have h1 : m^2 < 2^(2 * d) := by
    rw [Nat.pow_two, ← Nat.pow_add]
    have : d + d = 2 * d := by ring
    rw [this]
    nlinarith
  have h2 : m * (m + 1) < 2^(2 * d) := by
    rw [← Nat.pow_add]
    have : d + d = 2 * d := by ring
    rw [this]
    nlinarith
  exact Nat.xor_lt h1 h2

theorem sq_mod_even (m K : ℕ) (hK : K % 2 = 0) :
  (m + K)^2 % (2 * K) = m^2 % (2 * K) := by
  by_cases hK0 : K = 0
  · subst hK0; rfl
  · have hK2 : K = 2 * (K / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hK)).symm
    have h_exp : (m + K)^2 = m^2 + (2 * K) * (m + K / 2) := by
      rw [hK2]
      ring
    rw [h_exp]
    have : 2 * K > 0 := by omega
    omega

theorem mul_mod_even (m K : ℕ) (hK : K % 2 = 0) :
  (m + K) * (m + K + 1) % (2 * K) = (m * (m + 1) + K) % (2 * K) := by
  by_cases hK0 : K = 0
  · subst hK0; rfl
  · have hK2 : K = 2 * (K / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hK)).symm
    have h_exp : (m + K) * (m + K + 1) = m * (m + 1) + K + (2 * K) * (m + K / 2) := by
      rw [hK2]
      ring
    rw [h_exp]
    have : 2 * K > 0 := by omega
    omega

theorem add_two_pow_eq_xor (B s : ℕ) (hB : B < 2^s) :
  B + 2^s = Nat.xor B (2^s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < s
  · have h_mod : (B + 2^s) % 2^(i + 1) = B % 2^(i + 1) := by
      have : 2^s = 2^(i+1) * 2^(s - (i+1)) := by
        rw [← Nat.pow_add]
        congr
        omega
      rw [this]
      rw [Nat.add_mul_mod_self_left]
    -- wait, we have B.testBit i and (B + 2^s).testBit i.
    -- since i < i + 1, we can use Nat.testBit_mod_two_pow
    rw [← Nat.testBit_mod_two_pow _ _ (i+1) (by omega)]
    rw [h_mod]
    rw [Nat.testBit_mod_two_pow _ _ (i+1) (by omega)]
    rw [Nat.testBit_xor]
    have h_2s : (2^s : ℕ).testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact Nat.pow_lt_pow_right (by decide) hi
    rw [h_2s]
    rfl
  · by_cases h_eq : i = s
    · subst h_eq
      rw [Nat.testBit_xor]
      have h_2s : (2^s : ℕ).testBit s = true := by
        exact Nat.testBit_self s
      rw [h_2s]
      have hB_s : B.testBit s = false := by
        apply Nat.testBit_eq_false_of_lt
        exact hB
      rw [hB_s]
      change (B + 2^s).testBit s = (false ^^^ true)
      simp only [Bool.xor_false, Bool.xor_true]
      have h_div : (B + 2^s) >>> s = 1 := by
        change (B + 2^s) / 2^s = 1
        have h_pos : 2^s > 0 := by positivity
        rw [show B + 2^s = 2^s * 1 + B by omega]
        rw [Nat.add_mul_div_right B 1 h_pos]
        have : B / 2^s = 0 := Nat.div_eq_of_lt hB
        rw [this, Nat.add_zero]
      rw [show (B + 2^s).testBit s = (((B + 2^s) >>> s) &&& 1 != 0) by rfl]
      rw [h_div]
      rfl
    · have hi_gt : s < i := omega
      have h_lt1 : B + 2^s < 2^i := by
        calc
          B + 2^s < 2^s + 2^s := by omega
          _ = 2^(s + 1) := by ring
          _ ≤ 2^i := Nat.pow_le_pow_right (by decide) hi_gt
      rw [Nat.testBit_eq_false_of_lt h_lt1]
      rw [Nat.testBit_xor]
      have hB_i : B.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        exact lt_trans hB (Nat.pow_lt_pow_right (by decide) hi_gt)
      have h_2s : (2^s : ℕ).testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        exact Nat.pow_lt_pow_right (by decide) hi_gt
      rw [hB_i, h_2s]
      rfl

theorem testBit_add_two_pow_of_lt (B s i : ℕ) (hi : i < s) :
  (B + 2^s).testBit i = B.testBit i := by
  have h_mod : (B + 2^s) % 2^(i + 1) = B % 2^(i + 1) := by
    have : 2^s = 2^(i+1) * 2^(s - (i+1)) := by
      rw [← Nat.pow_add]
      congr
      omega
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  rw [← Nat.testBit_mod_two_pow _ _ (i+1) (by omega)]
  rw [h_mod]
  rw [Nat.testBit_mod_two_pow _ _ (i+1) (by omega)]

theorem testBit_add_two_pow_self (X s : ℕ) :
  (X + 2^s).testBit s = !X.testBit s := by
  rw [show (X + 2^s).testBit s = (((X + 2^s) >>> s) &&& 1 != 0) by rfl]
  rw [show X.testBit s = ((X >>> s) &&& 1 != 0) by rfl]
  have h_div : (X + 2^s) / 2^s = X / 2^s + 1 := by
    have h_pos : 2^s > 0 := by positivity
    rw [show X + 2^s = 2^s * 1 + X by omega]
    rw [Nat.add_mul_div_right X 1 h_pos]
  change ((X + 2^s) / 2^s) &&& 1 != 0 = !((X / 2^s) &&& 1 != 0)
  rw [h_div]
  have h_mod (Y : ℕ) : (Y &&& 1 != 0) = (Y % 2 = 1) := by
    rw [Nat.and_one_eq_mod_two]
    have : Y % 2 = 0 ∨ Y % 2 = 1 := Nat.mod_two_eq_zero_or_one Y
    rcases this with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  rw [h_mod, h_mod]
  have : (X / 2^s) % 2 = 0 ∨ (X / 2^s) % 2 = 1 := Nat.mod_two_eq_zero_or_one (X / 2^s)
  rcases this with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem xor_add_two_pow (A B s : ℕ) (hA : A < 2^s) (hB : B < 2^s) :
  Nat.xor A (B + 2^s) = Nat.xor A B + 2^s := by
  rw [add_two_pow_eq_xor B s hB]
  rw [Nat.xor_assoc]
  rw [← add_two_pow_eq_xor (Nat.xor A B) s (Nat.xor_lt hA hB)]

theorem xor_add_two_pow_mod (A B s : ℕ) :
  Nat.xor A (B + 2^s) % 2^(s+1) = (Nat.xor A B + 2^s) % 2^(s+1) := by
  rw [mod_two_pow_eq_iff_testBit_eq]
  intro i hi
  by_cases h_lt : i < s
  · rw [testBit_add_two_pow_of_lt _ _ _ h_lt]
    rw [Nat.testBit_xor]
    rw [testBit_add_two_pow_of_lt _ _ _ h_lt]
  · have : i = s := by omega
    subst this
    rw [Nat.testBit_xor]
    rw [testBit_add_two_pow_self]
    rw [testBit_add_two_pow_self]
    rfl

theorem g_lift (m s : ℕ) (hs : s ≥ 1) : g (m + 2^s) % 2^(s+1) = (g m + 2^s) % 2^(s+1) := by
  unfold g
  rw [xor_mod_two_pow]
  have h_even : 2^s % 2 = 0 := by omega
  rw [sq_mod_even m (2^s) h_even]
  rw [mul_mod_even m (2^s) h_even]
  rw [← xor_mod_two_pow]
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

theorem solve_m_correct (d : ℕ) (Y : ℕ) (hd : d ≥ 1) (hY : Y % 2 = 0) :
  g (solve_m d Y) % 2^d = Y % 2^d := by
  induction d, hd using Nat.le_induction with
  | base =>
    unfold solve_m
    unfold g
    omega
  | succ d' hd' ih =>
    have h_solve : solve_m (d' + 1) Y =
      let prev := solve_m d' Y
      if g prev % 2^(d' + 1) = Y % 2^(d' + 1) then prev else prev + 2^d' := rfl
    rw [h_solve]
    dsimp only
    by_cases h_eq : g (solve_m d' Y) % 2^(d' + 1) = Y % 2^(d' + 1)
    · rw [if_pos h_eq]
      exact h_eq
    · rw [if_neg h_eq]
      rw [g_lift _ _ hd']
      -- now we have: (g (solve_m d' Y) + 2^d') % 2^(d' + 1) = Y % 2^(d' + 1)
      -- we know by ih: g (solve_m d' Y) % 2^d' = Y % 2^d'
      -- since d' >= 1, 2^d' > 0.
      have h_pow : 2^d' > 0 := by positivity
      have h_split : g (solve_m d' Y) % 2^(d' + 1) = Y % 2^(d' + 1) ∨
                     g (solve_m d' Y) % 2^(d' + 1) = (Y + 2^d') % 2^(d' + 1) := by
        -- omega can prove this!
        have : 2^(d' + 1) = 2 * 2^d' := by ring
        omega
      rcases h_split with h_left | h_right
      · exact False.elim (h_eq h_left)
      · rw [h_right]
        have : (Y + 2^d' + 2^d') % 2^(d' + 1) = Y % 2^(d' + 1) := by
          have : 2^(d' + 1) = 2 * 2^d' := by ring
          omega
        exact this
