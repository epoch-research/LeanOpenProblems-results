import Mathlib

/-! Recursive bounds and their inverse budget for the Erdős 74 argument. -/

namespace E74

/-- The radius used by the localized induction. -/
def radiusBound : ℕ → ℕ
  | 0 => 0
  | t + 1 => (t + 1) * (16 * (t + 1) * (radiusBound t + 2)) + radiusBound t + 3

/-- The short-cycle length at stage `t`. -/
def lengthBound (t : ℕ) : ℕ := 16 * t * (radiusBound (t - 1) + 2)

/-- The vertex bound for a certificate of order `t`. -/
def certificateBound (t : ℕ) : ℕ := 2 * lengthBound t ^ t

@[simp] theorem radiusBound_zero : radiusBound 0 = 0 := rfl

@[simp] theorem lengthBound_zero : lengthBound 0 = 0 := rfl

@[simp] theorem lengthBound_succ (t : ℕ) :
    lengthBound (t + 1) = 16 * (t + 1) * (radiusBound t + 2) := by
  simp [lengthBound]

@[simp] theorem certificateBound_zero : certificateBound 0 = 2 := rfl

theorem radiusBound_succ (t : ℕ) :
    radiusBound (t + 1) = (t + 1) * lengthBound (t + 1) + radiusBound t + 3 := by
  rw [lengthBound_succ]
  rfl

theorem radiusBound_monotone : Monotone radiusBound := by
  apply monotone_nat_of_le_succ
  intro t
  rw [radiusBound_succ]
  omega

theorem lengthBound_monotone : Monotone lengthBound := by
  intro s t h
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 h)
    (Nat.add_le_add_right (radiusBound_monotone (Nat.sub_le_sub_right h 1)) 2)

theorem radiusBound_eq {t : ℕ} (ht : 0 < t) :
    radiusBound t = t * lengthBound t + radiusBound (t - 1) + 3 := by
  cases t with
  | zero => omega
  | succ t => simpa using radiusBound_succ t

theorem le_lengthBound (t : ℕ) : t ≤ lengthBound t := by
  unfold lengthBound
  nlinarith [Nat.zero_le (t * radiusBound (t - 1))]

theorem two_le_lengthBound {t : ℕ} (ht : 0 < t) : 2 ≤ lengthBound t := by
  unfold lengthBound
  nlinarith [Nat.zero_le (t * radiusBound (t - 1))]

theorem lengthBound_pos {t : ℕ} (ht : 0 < t) : 0 < lengthBound t :=
  lt_of_lt_of_le (by decide : 0 < 2) (two_le_lengthBound ht)

theorem radiusBound_le_pred {s t : ℕ} (h : s < t) :
    radiusBound s ≤ radiusBound (t - 1) :=
  radiusBound_monotone (by omega)

theorem radiusBound_comp_le {s t : ℕ} (ht : 0 < t) (h : s ≤ t) :
    s * lengthBound t + radiusBound (t - 1) + 3 ≤ radiusBound t := by
  rw [radiusBound_eq ht]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right (lengthBound t) h) _) _

theorem radiusBound_comp {s t : ℕ} (h : s < t) :
    s * lengthBound t + radiusBound (t - 1) + 3 ≤ radiusBound t :=
  radiusBound_comp_le (by omega) h.le

theorem two_le_certificateBound (t : ℕ) : 2 ≤ certificateBound t := by
  cases t with
  | zero => simp
  | succ t =>
    exact Nat.mul_le_mul_left 2
      (Nat.one_le_pow (t + 1) (lengthBound (t + 1)) (lengthBound_pos (by omega)))

theorem certificateBound_monotone : Monotone certificateBound := by
  intro s t h
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa using two_le_certificateBound t
  · exact Nat.mul_le_mul_left 2
      ((Nat.pow_le_pow_left (lengthBound_monotone h) s).trans
        (Nat.pow_le_pow_right (lengthBound_pos (hs.trans_le h)) h))

theorem le_certificateBound (t : ℕ) : t ≤ certificateBound t := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ t =>
    calc
      t + 1 ≤ lengthBound (t + 1) := le_lengthBound _
      _ ≤ lengthBound (t + 1) ^ (t + 1) := Nat.le_pow (Nat.succ_pos t)
      _ ≤ certificateBound (t + 1) := Nat.le_mul_of_pos_left _ (by decide)

theorem certificateBound_unbounded (n : ℕ) : n ≤ certificateBound (n + 1) :=
  (Nat.le_succ n).trans (le_certificateBound (n + 1))

/-- The least `k` for which `n ≤ certificateBound (k + 1)`. -/
noncomputable def budget (n : ℕ) : ℕ :=
  Nat.find (show ∃ k, n ≤ certificateBound (k + 1) from
    ⟨n, certificateBound_unbounded n⟩)

theorem budget_spec (n : ℕ) : n ≤ certificateBound (budget n + 1) :=
  Nat.find_spec (p := fun k => n ≤ certificateBound (k + 1)) _

theorem budget_le {n k : ℕ} (h : n ≤ certificateBound (k + 1)) : budget n ≤ k :=
  Nat.find_min' _ h

theorem budget_le_iff {n k : ℕ} : budget n ≤ k ↔ n ≤ certificateBound (k + 1) :=
  ⟨fun h => (budget_spec n).trans (certificateBound_monotone (Nat.add_le_add_right h 1)),
    budget_le⟩

theorem budget_monotone : Monotone budget := by
  intro m n h
  exact budget_le (h.trans (budget_spec n))

theorem budget_lt {n t : ℕ} (ht : 0 < t) (h : n ≤ certificateBound t) : budget n < t := by
  have hb : budget n ≤ t - 1 := budget_le (by simpa [Nat.sub_add_cancel ht] using h)
  omega

theorem budget_tendsto_atTop : Filter.Tendsto budget Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun t => ⟨certificateBound t + 1, ?_⟩
  intro n hn
  by_contra h
  have hb : budget n + 1 ≤ t := by omega
  have := (budget_spec n).trans (certificateBound_monotone hb)
  omega

end E74
