import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))
example
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp hp5 n r hn hr
  have hpowne : p ^ r ≠ p ^ (r - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr) with ⟨s, rfl⟩
    simp only [Nat.succ_sub_one]
    intro h
    rw [pow_succ'] at h
    have h' : p * p ^ s = 1 * p ^ s := by simpa using h
    have hp1 : p = 1 := Nat.mul_right_cancel (pow_pos hp.pos s) h'
    omega
  have hmulne : n * p ^ r ≠ n * p ^ (r - 1) := by
    intro h
    exact hpowne (Nat.mul_left_cancel (by omega : 0 < n) h)
  have hrpowne : r ≠ p ^ r := by
    have hp2 : 2 ≤ p := hp.two_le
    have h2pow : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp2 r
    have hrlt2 : r < 2 ^ r := Nat.lt_two_pow_self r
    omega
  have hrpowpredne : r ≠ p ^ (r - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr) with ⟨s, rfl⟩
    simp only [Nat.succ_sub_one]
    have hp2 : 2 ≤ p := hp.two_le
    have hge : 2 ^ s ≤ p ^ s := Nat.pow_le_pow_left hp2 s
    intro h
    -- s+1 = p^s >= 2^s; false for s? not false for s=1 p=2, but p>=5 gives p^s much larger. for s=0, 1=1 possible!
    cases s with
    | zero => norm_num at h
    | succ t =>
      have hbig : t+2 < p ^ (t+1) := by
        have h5 : 5 ≤ p := hp5
        -- crude: p^(t+1) >= 5^(t+1) > t+2
        have h5pow : 5 ^ (t+1) ≤ p ^ (t+1) := Nat.pow_le_pow_left h5 (t+1)
        have hlt : t+2 < 5 ^ (t+1) := by
          -- use Nat.lt_two_pow_self and 2^ <=5^
          have h2 : t+2 < 2 ^ (t+2) := Nat.lt_two_pow_self (t+2)
          have h2le5 : 2 ^ (t+2) ≤ 5 ^ (t+2) := Nat.pow_le_pow_left (by decide : 2 ≤ 5) (t+2)
          have hmono : 5 ^ (t+1) < 5 ^ (t+2) := Nat.pow_lt_pow_right (by decide : 1 < 5) (by omega : t+1 < t+2)
          -- wrong direction; just use omega? no
          nlinarith [h2, h2le5]
        exact lt_of_lt_of_le hlt h5pow
      omega
  grind [Int.ModEq]
