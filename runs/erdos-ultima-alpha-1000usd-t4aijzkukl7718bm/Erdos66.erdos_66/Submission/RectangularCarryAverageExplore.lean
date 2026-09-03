import FormalConjecturesUtil

/-! Averaging an endpoint-dependent one-unit carry over a rectangle loses
only a boundary strip. This is a finite scalar identity and bound. -/
namespace Erdos66RectangularCarryAverage
open scoped Classical
set_option maxHeartbeats 1400000
variable {p : ℕ}

noncomputable def carriedRow (K : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  ∑ i∈Finset.range K, (f (z-i)+g (z-i-1))

lemma carriedRow_identity (K : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) :
    carriedRow K f g z = (∑ i∈Finset.range K, (f (z-i)+g (z-i))) + g (z-K)-g z := by
  have hh := Finset.sum_range_sub (fun i : ℕ ↦ g (z-(i:ZMod p))) K
  simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, Nat.cast_zero, sub_zero] at hh
  rw [Finset.sum_sub_distrib] at hh
  unfold carriedRow
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

theorem carriedRow_error (K : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) (μ E : ℝ)
    (hflat : ∀ w, |f w+g w-μ| ≤ E)
    (hg : ∀ w, 0≤g w ∧ g w≤μ+E) :
    |carriedRow K f g z-K*μ| ≤ K*E+μ+E := by
  have hs : |(∑ i∈Finset.range K, (f (z-i)+g (z-i)))-(K:ℝ)*μ| ≤ K*E := by
    have hh : |∑ i∈Finset.range K, (f (z-i)+g (z-i)-μ)| ≤ (K:ℝ)*E := by
      calc
        _ ≤ ∑ i∈Finset.range K, |f (z-i)+g (z-i)-μ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i∈Finset.range K, E := Finset.sum_le_sum (fun i _ ↦ hflat (z-i))
        _ = _ := by simp
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hd : |g (z-K)-g z| ≤ μ+E := by
    rw [abs_le]
    constructor <;> linarith [(hg (z-K)).1, (hg (z-K)).2, (hg z).1, (hg z).2]
  calc
    _ = |((∑ i∈Finset.range K, (f (z-i)+g (z-i)))-(K:ℝ)*μ) + (g (z-K)-g z)| := by
      rw [carriedRow_identity]
      congr 1
      ring
    _ ≤ |(∑ i∈Finset.range K, (f (z-i)+g (z-i)))-(K:ℝ)*μ| + |g (z-K)-g z| := abs_add_le _ _
    _ ≤ _ := by linarith

noncomputable def carriedBox (K L : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  ∑ j∈Finset.range L, carriedRow K f g (z-j)

lemma carriedBox_comm (K L : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) :
    carriedBox K L f g z = carriedBox L K f g z := by
  unfold carriedBox carriedRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he : z-(j:ZMod p)-i = z-i-j := by ring
  rw [he]

lemma carriedBox_error_one_side (K L : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) (μ E : ℝ)
    (hflat : ∀ w, |f w+g w-μ| ≤ E)
    (hg : ∀ w, 0≤g w ∧ g w≤μ+E) :
    |carriedBox K L f g z-(K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+L*(μ+E) := by
  have hh : |∑ j∈Finset.range L, (carriedRow K f g (z-j)-(K:ℝ)*μ)| ≤
      (L:ℝ)*((K:ℝ)*E+μ+E) := by
    calc
      _ ≤ ∑ j∈Finset.range L, |carriedRow K f g (z-j)-(K:ℝ)*μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j∈Finset.range L, ((K:ℝ)*E+μ+E) :=
        Finset.sum_le_sum (fun j _ ↦ carriedRow_error K f g (z-j) μ E hflat hg)
      _ = _ := by simp <;> ring
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  convert hh using 1
  · congr 1
    unfold carriedBox
    ring
  · ring

/-- The carry cost is the smaller boundary length, not the area. -/
theorem carriedBox_error (K L : ℕ) (f g : ZMod p → ℝ) (z : ZMod p) (μ E : ℝ)
    (hflat : ∀ w, |f w+g w-μ| ≤ E)
    (hg : ∀ w, 0≤g w ∧ g w≤μ+E) :
    |carriedBox K L f g z-(K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+(min K L:ℕ)*(μ+E) := by
  by_cases hKL : K≤L
  · rw [min_eq_left hKL, carriedBox_comm]
    have hh := carriedBox_error_one_side L K f g z μ E hflat hg
    have he : (L:ℝ)*K=(K:ℝ)*L := by ring
    simpa only [he] using hh
  · rw [min_eq_right (by omega)]
    exact carriedBox_error_one_side K L f g z μ E hflat hg

end Erdos66RectangularCarryAverage
