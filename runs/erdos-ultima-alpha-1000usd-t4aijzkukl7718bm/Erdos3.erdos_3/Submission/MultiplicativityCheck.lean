import FormalConjecturesUtil

/-! Checking an attempted multiplicative recurrence for AP-free extremal sizes.
This is not a proof or disproof of the original conjecture. -/

namespace Erdos3MultiplicativityCheck

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem roth_three : rothNumberNat 3 = 2 := by decide

theorem roth_nine_lower : 5 ≤ rothNumberNat 9 := by
  have h : ThreeAPFree (({0, 1, 3, 7, 8} : Finset ℕ) : Set ℕ) := by decide
  exact h.le_rothNumberNat _ (by simp) (by decide)

theorem not_submultiplicative :
    ¬ (∀ m n : ℕ, rothNumberNat (m * n) ≤ rothNumberNat m * rothNumberNat n) := by
  intro h
  have h33 := h 3 3
  rw [roth_three] at h33
  have h9 := roth_nine_lower
  norm_num at h33
  omega


theorem roth_lt_self {m : ℕ} (hm : 3 ≤ m) : rothNumberNat m < m := by
  have h := rothNumberNat_add_le 3 (m - 3)
  have hb := rothNumberNat_le (m - 3)
  rw [roth_three, Nat.add_sub_of_le hm] at h
  omega

theorem roth_pos {m : ℕ} (hm : 1 ≤ m) : 0 < rothNumberNat m := by
  have h := rothNumberNat.mono hm
  have h1 : rothNumberNat 1 = 1 := by decide
  rw [h1] at h
  omega

theorem not_eventually_submultiplicative :
    ¬ (∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      rothNumberNat (m * n) ≤ rothNumberNat m * rothNumberNat n) := by
  rintro ⟨N, h⟩
  let m := max N 3
  have hmN : N ≤ m := le_max_left _ _
  have hm3 : 3 ≤ m := le_max_right _ _
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by positivity
  have hrpos : (0 : ℝ) < rothNumberNat m := by exact_mod_cast roth_pos hm1
  have hlt : (rothNumberNat m : ℝ) < m := by exact_mod_cast roth_lt_self hm3
  let d : ℝ := Real.log m - Real.log (rothNumberNat m)
  have hd : 0 < d := sub_pos.mpr (Real.log_lt_log hrpos hlt)
  have hmpow (j : ℕ) : m ≤ m ^ (j + 1) := by
    calc
      m = m * 1 := by simp
      _ ≤ m * m ^ j := Nat.mul_le_mul_left _ (one_le_pow₀ hm1)
      _ = m ^ (j + 1) := by rw [pow_succ, mul_comm]
  have hp (j : ℕ) : rothNumberNat (m ^ (j + 1)) ≤ rothNumberNat m ^ (j + 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        rothNumberNat (m ^ (j + 1 + 1)) = rothNumberNat (m * m ^ (j + 1)) := by
          rw [pow_succ, mul_comm]
        _ ≤ rothNumberNat m * rothNumberNat (m ^ (j + 1)) :=
          h m hmN _ (hmN.trans (hmpow j))
        _ ≤ rothNumberNat m * rothNumberNat m ^ (j + 1) := Nat.mul_le_mul_left _ ih
        _ = rothNumberNat m ^ (j + 1 + 1) := by
          simp [pow_succ, mul_comm]
  obtain ⟨j, hj⟩ := exists_nat_gt (16 * Real.log m / d ^ 2)
  have hj' : 16 * Real.log m < (j + 1 : ℕ) * d ^ 2 := by
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have := (div_lt_iff₀ hd2).mp hj
    push_cast
    nlinarith
  have hlower := Behrend.roth_lower_bound (N := m ^ (j + 1))
  have hupper : ((m ^ (j + 1) : ℕ) : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log ((m ^ (j + 1) : ℕ) : ℝ))) ≤
        (rothNumberNat m : ℝ) ^ (j + 1) :=
    hlower.trans (by exact_mod_cast hp j)
  push_cast at hupper
  have hlog := Real.log_le_log (by positivity) hupper
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_pow, Real.log_pow] at hlog
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hsqrt := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg (j + 1)) hlogm)
  have hsqrtpos := Real.sqrt_nonneg ((j + 1 : ℕ) * Real.log (m : ℝ))
  have hineq : (j + 1 : ℕ) * d ≤ 4 * Real.sqrt ((j + 1 : ℕ) * Real.log (m : ℝ)) := by
    dsimp [d]
    linarith
  have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hsq : ((j + 1 : ℕ) * d) ^ 2 ≤
      (4 * Real.sqrt ((j + 1 : ℕ) * Real.log (m : ℝ))) ^ 2 := by
    exact sq_le_sq₀ (by positivity) (by positivity) |>.mpr hineq
  nlinarith [mul_pos hjpos (sub_pos.mpr hj')]

/-- Even an arbitrary fixed multiplicative loss cannot make the proposed recurrence valid
at all sufficiently large scales. Roth's qualitative upper bound and Behrend's lower bound
already rule this out. -/
theorem not_eventually_submultiplicative_up_to_constant :
    ¬ (∃ C : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (rothNumberNat (m * n) : ℝ) ≤ C * rothNumberNat m * rothNumberNat n) := by
  rintro ⟨C, N, h⟩
  let q : ℝ := max C 1
  have hq1 : 1 ≤ q := le_max_right _ _
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  let F : ℕ → ℝ := fun n ↦ q * rothNumberNat n
  have hF (m n : ℕ) (hm : N ≤ m) (hn : N ≤ n) : F (m * n) ≤ F m * F n := by
    have hCq : C ≤ q := le_max_left _ _
    have h' : (rothNumberNat (m * n) : ℝ) ≤ q * rothNumberNat m * rothNumberNat n :=
      (h m hm n hn).trans (by gcongr)
    have := mul_le_mul_of_nonneg_left h' hq.le
    dsimp [F]
    nlinarith
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (rothNumberNat_isLittleO_id.bound (show (0 : ℝ) < 1 / (2 * q) by positivity))
  let m := max N (max M 3)
  have hmN : N ≤ m := le_max_left _ _
  have hmM : M ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm3 : 3 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrpos : 0 < F m := mul_pos hq (by exact_mod_cast roth_pos hm1)
  have hlt : F m < m := by
    have hb := hM m hmM
    simp only [Real.norm_natCast] at hb
    have hb' : (2 * q) * rothNumberNat m ≤ m := by
      have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2 * q)
      field_simp at this
      nlinarith
    dsimp [F]
    nlinarith
  let d : ℝ := Real.log m - Real.log (F m)
  have hd : 0 < d := sub_pos.mpr (Real.log_lt_log hrpos hlt)
  have hmpow (j : ℕ) : m ≤ m ^ (j + 1) := by
    calc
      m = m * 1 := by simp
      _ ≤ m * m ^ j := Nat.mul_le_mul_left _ (one_le_pow₀ hm1)
      _ = m ^ (j + 1) := by rw [pow_succ, mul_comm]
  have hp (j : ℕ) : F (m ^ (j + 1)) ≤ (F m) ^ (j + 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        F (m ^ (j + 1 + 1)) = F (m * m ^ (j + 1)) := by rw [pow_succ, mul_comm]
        _ ≤ F m * F (m ^ (j + 1)) := hF m _ hmN (hmN.trans (hmpow j))
        _ ≤ F m * (F m) ^ (j + 1) := mul_le_mul_of_nonneg_left ih hrpos.le
        _ = (F m) ^ (j + 1 + 1) := (pow_succ' (F m) (j + 1)).symm
  obtain ⟨j, hj⟩ := exists_nat_gt (16 * Real.log m / d ^ 2)
  have hj' : 16 * Real.log m < (j + 1 : ℕ) * d ^ 2 := by
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have := (div_lt_iff₀ hd2).mp hj
    push_cast
    nlinarith
  have hupper : ((m ^ (j + 1) : ℕ) : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log ((m ^ (j + 1) : ℕ) : ℝ))) ≤
        (F m) ^ (j + 1) := by
    calc
      _ ≤ (rothNumberNat (m ^ (j + 1)) : ℝ) := Behrend.roth_lower_bound
      _ ≤ F (m ^ (j + 1)) := by
        simpa [F] using mul_le_mul_of_nonneg_right hq1
          (show (0 : ℝ) ≤ rothNumberNat (m ^ (j + 1)) by positivity)
      _ ≤ _ := hp j
  push_cast at hupper
  have hlog := Real.log_le_log (by positivity) hupper
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_pow, Real.log_pow] at hlog
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hsqrt := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg (j + 1)) hlogm)
  have hsqrtpos := Real.sqrt_nonneg ((j + 1 : ℕ) * Real.log (m : ℝ))
  have hineq : (j + 1 : ℕ) * d ≤ 4 * Real.sqrt ((j + 1 : ℕ) * Real.log (m : ℝ)) := by
    dsimp [d]
    linarith
  have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hsq : ((j + 1 : ℕ) * d) ^ 2 ≤
      (4 * Real.sqrt ((j + 1 : ℕ) * Real.log (m : ℝ))) ^ 2 := by
    exact sq_le_sq₀ (by positivity) (by positivity) |>.mpr hineq
  nlinarith [mul_pos hjpos (sub_pos.mpr hj')]

#print axioms not_eventually_submultiplicative_up_to_constant

#print axioms not_eventually_submultiplicative

#print axioms not_submultiplicative

end Erdos3MultiplicativityCheck
