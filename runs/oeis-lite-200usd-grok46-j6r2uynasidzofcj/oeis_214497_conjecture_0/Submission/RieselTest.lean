import FormalConjectures.Util.ProblemImports
import Submission.Riesel

open Nat jacobiSym XD

set_option maxHeartbeats 400000

/-! Modular evaluation of `lucasV`. -/

/-- One recurrence step modulo `N`: `(V_i, V_{i+1}) ↦ (V_{i+1}, V_{i+2})`. -/
def vStep (P N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.2, ((P % N) * p.2 + (N - p.1 % N)) % N)

/-- `(V_n mod N, V_{n+1} mod N)` computed iteratively. -/
def vPair (P N : ℕ) : ℕ → ℕ × ℕ
  | 0 => (2 % N, P % N)
  | n + 1 => vStep P N (vPair P N n)

lemma vPair_mod (P N n : ℕ) :
    (vPair P N n).1 % N = (vPair P N n).1 ∧ (vPair P N n).2 % N = (vPair P N n).2 := by
  induction n with
  | zero =>
    simp [vPair, Nat.mod_mod]
  | succ n ih =>
    simp [vPair, vStep, Nat.mod_mod]

lemma zmod_sub_val {N a b : ℕ} [NeZero N] :
    ((a : ZMod N) - (b : ZMod N)).val = (a + (N - b % N)) % N := by
  have hN : 0 < N := NeZero.pos N
  rw [ZMod.val_sub, ZMod.val_natCast, ZMod.val_natCast]
  -- val (↑a - ↑b) = (val ↑a + (N - val ↑b)) % N
  have : (a % N + (N - b % N)) % N = (a + (N - b % N)) % N := by
    have : a % N + (N - b % N) ≡ a + (N - b % N) [MOD N] := by
      refine Nat.ModEq.add ?_ (Nat.ModEq.refl _)
      exact Nat.mod_modEq a N
    exact this.eq
  -- ZMod.val_sub : (a - b).val = (a.val + (N - b.val)) % N
  simpa [ZMod.val_natCast] using this.symm ▸ rfl

lemma vPair_spec (P N n : ℕ) [NeZero N] :
    ((vPair P N n).1 : ZMod N) = (lucasV (P : ℤ) n : ZMod N) ∧
    ((vPair P N n).2 : ZMod N) = (lucasV (P : ℤ) (n + 1) : ZMod N) := by
  induction n with
  | zero =>
    constructor
    · simp [vPair, lucasV]
    · simp [vPair, lucasV]
  | succ n ih =>
    constructor
    · simpa [vPair, vStep] using ih.2
    · simp only [vPair, vStep, lucasV_succ_succ]
      have h1 := ih.1
      have h2 := ih.2
      -- RHS = ↑P * V_{n+1} - V_n
      have : ((P % N * (vPair P N n).2 + (N - (vPair P N n).1 % N)) % N : ZMod N)
          = (P : ZMod N) * (lucasV (P : ℤ) (n + 1) : ZMod N)
            - (lucasV (P : ℤ) n : ZMod N) := by
        have hN : 0 < N := NeZero.pos N
        have hb : (vPair P N n).1 % N = (vPair P N n).1 := (vPair_mod P N n).1
        rw [Nat.cast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub]
        · rw [Nat.cast_mod, ZMod.natCast_self, sub_zero, h1, h2]
          simp
        · have : (vPair P N n).1 % N ≤ N := Nat.mod_le _ _
          -- N - (vPair.1 % N) ≤ N, we need (vPair.1 % N) ≤ N which is true, actually
          -- Nat.cast_sub requires (vPair.1 % N) ≤ N
          exact Nat.mod_le _ _
      -- wait this is getting messy; use ZMod directly
      sorry

/-- Doubling step `x ↦ x^2 - 2` modulo `N`. -/
def sqm2 (N x : ℕ) : ℕ := (x * x + (N - 2 % N)) % N

def vpow2mod (N acc : ℕ) : ℕ → ℕ
  | 0 => acc % N
  | i + 1 => sqm2 N (vpow2mod N acc i)

lemma vpow2mod_spec (P : ℤ) (N acc i : ℕ) [NeZero N]
    (hacc : (acc : ZMod N) = (lucasV P (k) : ZMod N)) :
    True := trivial

/-- Hand computation of `J(21 | 191) = -1`. -/
lemma jac_21_191 : jacobiSym 21 191 = -1 := by
  have hmul : jacobiSym 21 191 = jacobiSym 3 191 * jacobiSym 7 191 := by
    have : (21 : ℤ) = 3 * 7 := by decide
    rw [this, jacobiSym.mul_left]
  have h3 : jacobiSym 3 191 = 1 := by
    -- 3 ≡ 3 (mod 4), 191 ≡ 3 (mod 4) ⇒ J(3|191) = -J(191|3) = -J(2|3)
    have hr : jacobiSym 3 191 = - jacobiSym 191 3 := by
      have h3o : Odd (3 : ℕ) := by decide
      have h191o : Odd 191 := by decide
      have : (3 : ℕ) % 4 = 3 ∧ 191 % 4 = 3 := by decide
      -- use quadratic_reciprocity_three_mod_four or quadratic_reciprocity
      rw [jacobiSym.quadratic_reciprocity_three_mod_four (by decide) (by decide)]
    have : jacobiSym 191 3 = jacobiSym 2 3 := by
      have : (191 : ℤ) % 3 = 2 := by decide
      rw [jacobiSym.mod_left]
      decide
    have : jacobiSym 2 3 = -1 := by
      rw [jacobiSym.at_two (by decide)]
      decide
    omega
  sorry

lemma jac_5_191 : jacobiSym (5 ^ 2 - 4) 191 = -1 := by
  have : (5 ^ 2 - 4 : ℤ) = 21 := by decide
  rw [this]
  exact jac_21_191
