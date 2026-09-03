import FormalConjecturesUtil

/-!
# Clearing an individual factorial-minus-one denominator

For every fixed C, the denominator k!-1 eventually cannot divide (C*k)!.
This is an arithmetic obstruction to a denominator-clearing strategy, not a
proof or disproof of Erdős 68. It makes no assertion about prime factors
larger than C*k: an excessive prime-power multiplicity is also possible.
-/

namespace FactorialClearingIndex

open Filter

def blockCoefficient : ℕ → ℕ → ℕ
  | 0, _ => 1
  | C + 1, k => blockCoefficient C k * ((C + 1) * k).choose k

lemma blockCoefficient_identity (C k : ℕ) :
    blockCoefficient C k * k.factorial ^ C = (C * k).factorial := by
  induction C with
  | zero => simp [blockCoefficient]
  | succ C ih =>
    calc
      blockCoefficient (C + 1) k * k.factorial ^ (C + 1) =
          ((C + 1) * k).choose k *
            (blockCoefficient C k * k.factorial ^ C) * k.factorial := by
        simp only [blockCoefficient, pow_succ]
        ring
      _ = ((C + 1) * k).choose k * (C * k).factorial * k.factorial := by rw [ih]
      _ = ((C + 1) * k).factorial := by
        rw [show (C + 1) * k = C * k + k by ring]
        exact Nat.add_choose_mul_factorial_mul_factorial (C * k) k

lemma blockCoefficient_pos (C k : ℕ) : 0 < blockCoefficient C k := by
  have h := Nat.factorial_pos (C * k)
  rw [← blockCoefficient_identity] at h
  by_contra hn
  have hz : blockCoefficient C k = 0 := by omega
  simp [hz] at h

lemma blockCoefficient_bound (C k : ℕ) :
    blockCoefficient C k ≤ 2 ^ (C ^ 2 * k) := by
  induction C with
  | zero => simp [blockCoefficient]
  | succ C ih =>
    calc
      blockCoefficient (C + 1) k ≤
          2 ^ (C ^ 2 * k) * 2 ^ ((C + 1) * k) := by
        exact Nat.mul_le_mul ih (Nat.choose_le_two_pow _ _)
      _ = 2 ^ (C ^ 2 * k + (C + 1) * k) := (pow_add _ _ _).symm
      _ ≤ 2 ^ ((C + 1) ^ 2 * k) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith

lemma pred_factorial_coprime (k : ℕ) :
    (k.factorial - 1).Coprime k.factorial := by
  apply Nat.Coprime.symm
  exact (Nat.coprime_self_sub_right (Nat.factorial_pos _)).mpr
    (Nat.coprime_one_right _)

lemma pred_factorial_dvd_blockCoefficient {C k : ℕ}
    (h : k.factorial - 1 ∣ (C * k).factorial) :
    k.factorial - 1 ∣ blockCoefficient C k := by
  rw [← blockCoefficient_identity] at h
  exact ((pred_factorial_coprime k).pow_right C).dvd_of_dvd_mul_right h

lemma clearing_forces_exponential_bound {C k : ℕ}
    (h : k.factorial - 1 ∣ (C * k).factorial) :
    k.factorial - 1 ≤ 2 ^ (C ^ 2 * k) :=
  (Nat.le_of_dvd (blockCoefficient_pos C k)
    (pred_factorial_dvd_blockCoefficient h)).trans (blockCoefficient_bound C k)

theorem eventually_not_dvd_linear_factorial (C : ℕ) :
    ∀ᶠ k : ℕ in atTop, ¬k.factorial - 1 ∣ (C * k).factorial := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub 2 (2 ^ (C ^ 2)) 0]
    with k hk
  simp only [Nat.sub_zero, ← pow_mul] at hk
  intro h
  have hb := clearing_forces_exponential_bound h
  have hp : 0 < (2 : ℕ) ^ (C ^ 2 * k) := by positivity
  omega

/-- Any factorial index clearing k!-1 grows faster than every fixed linear
multiple of k. This does not control reduced denominators of sums. -/
theorem eventual_clearing_index_gt_linear (C : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,
      k.factorial - 1 ∣ N.factorial → C * k < N := by
  filter_upwards [eventually_not_dvd_linear_factorial C] with k hk
  intro N hN
  by_contra h
  exact hk (hN.trans (Nat.factorial_dvd_factorial (by omega)))

lemma four_pow_lt_pred_factorial {k : ℕ} (hk : 9 ≤ k) :
    4 ^ k < k.factorial - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 9 := ⟨k - 9, by omega⟩
  clear hk
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 9 = (n + 9) + 1 by omega, pow_succ, Nat.factorial_succ]
    have hp : 0 < (4 : ℕ) ^ (n + 9) := by positivity
    have hf : 1 ≤ (n + 9).factorial := Nat.factorial_pos _
    have hm := Nat.mul_le_mul_right (n + 9).factorial (show 4 ≤ n + 9 + 1 by omega)
    have hs : (n + 9).factorial - 1 + 1 = (n + 9).factorial :=
      Nat.sub_add_cancel hf
    have hh : 4 ^ (n + 9) * 4 + 1 < (n + 9 + 1) * (n + 9).factorial := by
      nlinarith
    omega

/-- An explicit initial bound: doubling the factorial index is insufficient
for every k>=9. -/
theorem not_dvd_double_factorial {k : ℕ} (hk : 9 ≤ k) :
    ¬k.factorial - 1 ∣ (2 * k).factorial := by
  intro h
  have hid := Nat.add_choose_mul_factorial_mul_factorial k k
  rw [← two_mul k] at hid
  rw [← hid, mul_assoc] at h
  have hd := ((pred_factorial_coprime k).mul_right
    (pred_factorial_coprime k)).dvd_of_dvd_mul_right h
  have hl := Nat.le_of_dvd (Nat.choose_pos (by omega : k ≤ 2 * k)) hd
  have hu : (2 * k).choose k ≤ 4 ^ k := by
    have hh := Nat.choose_le_two_pow (2 * k) k
    simpa only [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] using hh
  exact (not_le_of_gt (four_pow_lt_pred_factorial hk)) (hl.trans hu)

#print axioms eventual_clearing_index_gt_linear
#print axioms not_dvd_double_factorial

end FactorialClearingIndex
