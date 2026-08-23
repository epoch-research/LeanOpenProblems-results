import FormalConjectures.Util.ProblemImports

open Nat

def lucasV (P : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P (n + 1) - lucasV P n

theorem lucasV_zero (P : ℤ) : lucasV P 0 = 2 := rfl
theorem lucasV_one (P : ℤ) : lucasV P 1 = P := rfl
theorem lucasV_succ_succ (P : ℤ) (n : ℕ) :
    lucasV P (n + 2) = P * lucasV P (n + 1) - lucasV P n := rfl

theorem lucasV_succ (P : ℤ) {j : ℕ} (hj : 1 ≤ j) :
    lucasV P (j + 1) = P * lucasV P j - lucasV P (j - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [Nat.add_sub_cancel]
  exact lucasV_succ_succ P n

theorem lucasV_add (P : ℤ) : ∀ n m, n ≤ m →
    lucasV P (m + n) + lucasV P (m - n) = lucasV P m * lucasV P n
  | 0, m, _ => by simp [lucasV]; ring
  | 1, m, hm => by
    have : lucasV P (m + 1) = P * lucasV P m - lucasV P (m - 1) := lucasV_succ P hm
    simp only [lucasV_one]
    rw [this]; ring
  | n + 2, m, hm => by
    have hn1 : n + 1 ≤ m := by omega
    have hn0 : n ≤ m := by omega
    have hstep1 := lucasV_add P (n + 1) m hn1
    have hstep0 := lucasV_add P n m hn0
    have hL : lucasV P (m + (n + 2)) = P * lucasV P (m + (n + 1)) - lucasV P (m + n) := by
      rw [show m + (n + 2) = (m + n) + 2 from add_assoc _ n 2]
      rw [lucasV_succ_succ, add_assoc]
    have hr : 1 ≤ m - (n + 1) := by omega
    have hR : lucasV P (m - (n + 2)) = P * lucasV P (m - (n + 1)) - lucasV P (m - n) := by
      have := lucasV_succ P hr
      have h1 : (m - (n + 1)) + 1 = m - n := by omega
      have h2 : m - (n + 1) - 1 = m - (n + 2) := by omega
      rw [h1, h2] at this
      linarith
    rw [hL, hR]
    have : P * lucasV P (m + (n + 1)) - lucasV P (m + n)
         + (P * lucasV P (m - (n + 1)) - lucasV P (m - n))
         = P * (lucasV P (m + (n + 1)) + lucasV P (m - (n + 1)))
           - (lucasV P (m + n) + lucasV P (m - n)) := by ring
    rw [this, hstep1, hstep0, lucasV_succ_succ]
    ring

theorem lucasV_dbl (P : ℤ) (m : ℕ) : lucasV P (2 * m) = lucasV P m ^ 2 - 2 := by
  have h := lucasV_add P m m le_rfl
  rw [Nat.sub_self, lucasV_zero] at h
  rw [two_mul]
  linarith

lemma lucasV_odd_step (P : ℤ) (d : ℕ) :
    lucasV P (2 * d + 1) = lucasV P d * lucasV P (d + 1) - P := by
  have h := lucasV_add P d (d + 1) (Nat.le_succ d)
  have h1 : d + 1 + d = 2 * d + 1 := by ring
  have h2 : d + 1 - d = 1 := by omega
  rw [h1, h2, lucasV_one] at h
  linarith

def sqm2 (N x : ℕ) : ℕ := (x * x + (N - 2)) % N

lemma sqm2_zmod (N x : ℕ) [NeZero N] (hN : 2 ≤ N) :
    (sqm2 N x : ZMod N) = (x : ZMod N) ^ 2 - 2 := by
  change (((x * x + (N - 2)) % N : ZMod N) = _)
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN, ZMod.natCast_self, zero_sub]
  simp [pow_two, sub_eq_add_neg]

lemma nat_cast_sub_mod (N a : ℕ) [NeZero N] :
    ((N - a % N : ℕ) : ZMod N) = - (a : ZMod N) := by
  have hN : 0 < N := NeZero.pos N
  have hle : a % N ≤ N := Nat.le_of_lt (Nat.mod_lt a hN)
  have hcast : ((a % N : ℕ) : ZMod N) = (a : ZMod N) := ZMod.natCast_mod a N
  rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, hcast]

def mulsub (P N v0 v1 : ℕ) : ℕ :=
  ((v0 % N) * (v1 % N) + (N - P % N)) % N

lemma mulsub_zmod (P N v0 v1 : ℕ) [NeZero N] :
    (mulsub P N v0 v1 : ZMod N) =
      (v0 : ZMod N) * (v1 : ZMod N) - (P : ZMod N) := by
  change ((((v0 % N) * (v1 % N) + (N - P % N)) % N : ZMod N) = _)
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, nat_cast_sub_mod, ZMod.natCast_mod,
    ZMod.natCast_mod]
  ring

def vBin (P N : ℕ) : ℕ → ℕ × ℕ
  | 0 => (2 % N, P % N)
  | n + 1 =>
    let p := vBin P N ((n + 1) / 2)
    if (n + 1) % 2 = 0 then
      (sqm2 N p.1, mulsub P N p.1 p.2)
    else
      (mulsub P N p.1 p.2, sqm2 N p.2)
termination_by vBin P N k => k

lemma vBin_spec (P N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∀ k,
      ((vBin P N k).1 : ZMod N) = (lucasV (P : ℤ) k : ZMod N) ∧
      ((vBin P N k).2 : ZMod N) = (lucasV (P : ℤ) (k + 1) : ZMod N) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => constructor <;> simp [vBin, lucasV]
    | k + 1 =>
      have hlt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (by omega) (by decide)
      have hp := ih ((k + 1) / 2) hlt
      by_cases he : (k + 1) % 2 = 0
      · have hd : k + 1 = 2 * ((k + 1) / 2) := by omega
        constructor
        · have : (vBin P N (k + 1)).1 = sqm2 N (vBin P N ((k + 1) / 2)).1 := by
            simp [vBin, he]
          rw [this, sqm2_zmod N _ hN, hp.1, hd, lucasV_dbl, pow_two]
        · have : (vBin P N (k + 1)).2 =
              mulsub P N (vBin P N ((k + 1) / 2)).1 (vBin P N ((k + 1) / 2)).2 := by
            simp [vBin, he]
          rw [this, mulsub_zmod, hp.1, hp.2, hd, lucasV_odd_step]
          simp [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      · have hd : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        constructor
        · have : (vBin P N (k + 1)).1 =
              mulsub P N (vBin P N ((k + 1) / 2)).1 (vBin P N ((k + 1) / 2)).2 := by
            simp [vBin, he]
          rw [this, mulsub_zmod, hp.1, hp.2, hd, lucasV_odd_step]
          simp [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        · have : (vBin P N (k + 1)).2 = sqm2 N (vBin P N ((k + 1) / 2)).2 := by
            simp [vBin, he]
          have h2 : k + 1 + 1 = 2 * ((k + 1) / 2 + 1) := by omega
          rw [this, sqm2_zmod N _ hN, hp.2, h2, lucasV_dbl]
          simp [pow_two, Int.cast_sub, Int.cast_mul, Int.cast_pow]

-- sanity: V_3(5) = 110
example : lucasV 5 3 = 110 := by decide

example : (vBin 5 191 3).1 % 191 = 110 % 191 := rfl
