import Submission.Common

/-! Integer arithmetic underlying the odd cyclic blocks. -/

namespace Erdos1Aux

private theorem chain_pos (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (a b : ℤ) (hab : |(a : ℚ) + t * b| < 1) (ha : 0 < a) :
    b < 0 ∧ a ≤ -b := by
  have hupper := (abs_lt.mp hab).2
  have ha1 : (1 : ℚ) ≤ a := by exact_mod_cast (show (1 : ℤ) ≤ a by omega)
  have hb : b < 0 := by
    by_contra h
    have hb0 : (0 : ℚ) ≤ b := by exact_mod_cast (show (0 : ℤ) ≤ b by omega)
    nlinarith [mul_nonneg (le_of_lt ht0) hb0]
  have hmag : a ≤ -b := by
    by_contra h
    have hsum : (1 : ℚ) ≤ (a : ℚ) + b := by
      exact_mod_cast (show (1 : ℤ) ≤ a + b by omega)
    have hbc : (b : ℚ) < 0 := by exact_mod_cast hb
    have hmul : (0 : ℚ) ≤ (1 - t) * (-(b : ℚ)) :=
      mul_nonneg (sub_nonneg.mpr ht1.le) (neg_nonneg.mpr hbc.le)
    nlinarith
  exact ⟨hb, hmag⟩

private theorem chain_neg (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (a b : ℤ) (hab : |(a : ℚ) + t * b| < 1) (ha : a < 0) :
    0 < b ∧ -a ≤ b := by
  have hab' : |((-a : ℤ) : ℚ) + t * ((-b : ℤ) : ℚ)| < 1 := by
    have hneg : ((-a : ℤ) : ℚ) + t * ((-b : ℤ) : ℚ) =
        -((a : ℚ) + t * b) := by push_cast; ring
    rw [hneg, abs_neg]
    exact hab
  obtain ⟨hneg, hmag⟩ := chain_pos t ht0 ht1 (-a) (-b) hab' (by omega)
  omega


/-- A prefix of an alternating integer chain is between zero and its final entry. -/
theorem chain_prefix_bound (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : ℕ → ℤ) (n : ℕ)
    (h : ∀ i < n, |(z i : ℚ) + t * z (i + 1)| < 1) :
    ∀ i ≤ n,
      (z i ≤ 0 → z i ≤ ∑ j ∈ Finset.range (i + 1), z j ∧
        (∑ j ∈ Finset.range (i + 1), z j) ≤ 0) ∧
      (0 ≤ z i → 0 ≤ ∑ j ∈ Finset.range (i + 1), z j ∧
        (∑ j ∈ Finset.range (i + 1), z j) ≤ z i) := by
  intro i
  induction i with
  | zero =>
      intro _
      simp
  | succ i ih =>
      intro hi
      have hbefore := ih (by omega)
      have hstep := h i (by omega)
      rw [Finset.sum_range_succ]
      by_cases hp : 0 < z i
      · obtain ⟨hn, hm⟩ := chain_pos t ht0 ht1 (z i) (z (i + 1)) hstep hp
        have hh := hbefore.2 (by omega)
        constructor <;> intro hz <;> omega
      · by_cases hn : z i < 0
        · obtain ⟨hp', hm⟩ := chain_neg t ht0 ht1 (z i) (z (i + 1)) hstep hn
          have hh := hbefore.1 (by omega)
          constructor <;> intro hz <;> omega
        · have hh := hbefore.1 (by omega)
          constructor <;> intro hz <;> omega

/-- With an odd number of links, a negative first entry forces a positive last entry. -/
theorem chain_odd_sign (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : ℕ → ℤ) (n : ℕ)
    (h : ∀ i < 2 * n + 1, |(z i : ℚ) + t * z (i + 1)| < 1)
    (hz : z 0 < 0) : 0 < z (2 * n + 1) := by
  have aux (j : ℕ) (hj : j ≤ n) : z (2 * j) < 0 ∧ 0 < z (2 * j + 1) := by
    induction j with
    | zero =>
        simpa using ⟨hz, (chain_neg t ht0 ht1 (z 0) (z 1) (h 0 (by omega)) hz).1⟩
    | succ j ih =>
        have hprev := ih (by omega)
        have h1 := (chain_pos t ht0 ht1 (z (2 * j + 1)) (z (2 * j + 2))
          (h (2 * j + 1) (by omega)) hprev.2).1
        have h2 := (chain_neg t ht0 ht1 (z (2 * j + 2)) (z (2 * j + 3))
          (h (2 * j + 2) (by omega)) h1).1
        convert And.intro h1 h2 using 1 <;> congr 2 <;> omega
  exact (aux n le_rfl).2

/-- The last two cyclic coordinates cannot both be negative when the preceding chain is short. -/
theorem chain_last_nonnegative (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : ℕ → ℤ) (n : ℕ)
    (h : ∀ i < 2 * n + 1, |(z i : ℚ) + t * z (i + 1)| < 1)
    (hsum : ∑ i ∈ Finset.range (2 * n + 3), z i = 0) :
    0 ≤ (z (2 * n + 1) : ℚ) + t * z (2 * n + 2) ∨
      0 ≤ (z (2 * n + 2) : ℚ) + t * z 0 := by
  have hpre := chain_prefix_bound t ht0 ht1 z (2 * n + 1)
    (fun i hi => h i (by omega)) (2 * n + 1) le_rfl
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega] at hpre
  have hsum' : (∑ i ∈ Finset.range (2 * n + 2), z i) + z (2 * n + 2) = 0 := by
    simpa only [show 2 * n + 3 = (2 * n + 2) + 1 by omega,
      Finset.sum_range_succ] using hsum
  rcases le_or_gt 0 (z (2 * n + 1)) with hp | hn
  · left
    have hb := (hpre.2 hp).2
    have hsumle : 0 ≤ z (2 * n + 1) + z (2 * n + 2) := by omega
    have hpq : (0 : ℚ) ≤ z (2 * n + 1) := by exact_mod_cast hp
    have hsumq : (0 : ℚ) ≤ (z (2 * n + 1) : ℚ) + z (2 * n + 2) := by
      exact_mod_cast hsumle
    have h1 : 0 ≤ (1 - t) * (z (2 * n + 1) : ℚ) :=
      mul_nonneg (sub_nonneg.mpr ht1.le) hpq
    have h2 : 0 ≤ t * ((z (2 * n + 1) : ℚ) + z (2 * n + 2)) :=
      mul_nonneg ht0.le hsumq
    nlinarith
  · right
    have hb := (hpre.1 hn.le).2
    have hlast : 0 ≤ z (2 * n + 2) := by omega
    have hfirst : 0 ≤ z 0 := by
      by_contra hh
      have := chain_odd_sign t ht0 ht1 z n h (by omega)
      omega
    have hlastq : (0 : ℚ) ≤ z (2 * n + 2) := by exact_mod_cast hlast
    have hfirstq : (0 : ℚ) ≤ z 0 := by exact_mod_cast hfirst
    nlinarith [mul_nonneg ht0.le hfirstq]

/-- An odd cyclic integer chain is cube separated. -/
theorem odd_cycle_cube (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : ℕ → ℤ) (n : ℕ)
    (h : ∀ i < 2 * n + 2, |(z i : ℚ) + t * z (i + 1)| < 1)
    (hw : |(z (2 * n + 2) : ℚ) + t * z 0| < 1) :
    ∀ i < 2 * n + 3, z i = 0 := by
  have hzero : z 0 = 0 := by
    rcases lt_trichotomy (z 0) 0 with hn | he | hp
    · have hpen : 0 < z (2 * n + 1) :=
        chain_odd_sign t ht0 ht1 z n (fun i hi => h i (by omega)) hn
      have hlast := (chain_pos t ht0 ht1 (z (2 * n + 1)) (z (2 * n + 2))
        (h (2 * n + 1) (by omega)) hpen).1
      have hwrap := (chain_neg t ht0 ht1 (z (2 * n + 2)) (z 0) hw hlast).1
      omega
    · exact he
    · have h' : ∀ i < 2 * n + 1,
          |((-(z i) : ℤ) : ℚ) + t * (-(z (i + 1)))| < 1 := by
        intro i hi
        have heq : ((-(z i) : ℤ) : ℚ) + t * ((-(z (i + 1)) : ℤ) : ℚ) =
            -((z i : ℚ) + t * z (i + 1)) := by push_cast; ring
        change |((-(z i) : ℤ) : ℚ) + t * ((-(z (i + 1)) : ℤ) : ℚ)| < 1
        rw [heq, abs_neg]
        exact h i (by omega)
      have hpen : z (2 * n + 1) < 0 := by
        have hh := chain_odd_sign t ht0 ht1 (fun i => -z i) n h'
          (show -(z 0) < 0 by omega)
        change 0 < -(z (2 * n + 1)) at hh
        omega
      have hlast := (chain_neg t ht0 ht1 (z (2 * n + 1)) (z (2 * n + 2))
        (h (2 * n + 1) (by omega)) hpen).1
      have hwrap := (chain_pos t ht0 ht1 (z (2 * n + 2)) (z 0) hw hlast).1
      omega
  have hlast : z (2 * n + 2) = 0 := by
    rcases lt_trichotomy (z (2 * n + 2)) 0 with hn | he | hp
    · have hh := (chain_neg t ht0 ht1 (z (2 * n + 2)) (z 0) hw hn).1
      omega
    · exact he
    · have hh := (chain_pos t ht0 ht1 (z (2 * n + 2)) (z 0) hw hp).1
      omega
  intro i hi
  have aux (j : ℕ) (hj : j ≤ 2 * n + 2) : z j = 0 := by
    induction hj using Nat.decreasingInduction with
    | self => exact hlast
    | of_succ j hj ih =>
        rcases lt_trichotomy (z j) 0 with hn | he | hp
        · have hh := (chain_neg t ht0 ht1 (z j) (z (j + 1))
            (h j (by omega)) hn).1
          omega
        · exact he
        · have hh := (chain_pos t ht0 ht1 (z j) (z (j + 1))
            (h j (by omega)) hp).1
          omega
  exact aux i (by omega)



/-- The odd cyclic map `I + tP`. -/
def oddCycle (n : ℕ) (t : ℚ) :
    Matrix (Fin (2 * n + 3)) (Fin (2 * n + 3)) ℚ :=
  1 + t • (finRotate (2 * n + 3)).permMatrix ℚ

/-- Replace the final input coordinate by the height, and use difference
    vectors for all preceding coordinates. -/
def heightCoordinates (n : ℕ) (t : ℚ) :
    Matrix (Fin (2 * n + 3)) (Fin (2 * n + 3)) ℚ :=
  fun i j => if i = Fin.last (2 * n + 2) then
    if j = Fin.last (2 * n + 2) then (1 + t)⁻¹ else -1
    else if i = j then 1 else 0

def oddBlock (n : ℕ) (t : ℚ) :
    Matrix (Fin (2 * n + 3)) (Fin (2 * n + 3)) ℚ :=
  oddCycle n t * heightCoordinates n t

private theorem oddCycle_apply (n : ℕ) (t : ℚ) (x : Fin (2 * n + 3) → ℚ)
    (i : Fin (2 * n + 3)) :
    (oddCycle n t).mulVec x i = x i + t * x ((finRotate (2 * n + 3)) i) := by
  simp [oddCycle, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.permMatrix_mulVec]


private theorem heightCoordinates_nonlast (n : ℕ) (t : ℚ)
    (x : Fin (2 * n + 3) → ℚ) (i : Fin (2 * n + 3))
    (hi : i ≠ Fin.last (2 * n + 2)) :
    (heightCoordinates n t).mulVec x i = x i := by
  simp [Matrix.mulVec, dotProduct, heightCoordinates, hi]

private theorem heightCoordinates_last (n : ℕ) (t : ℚ)
    (x : Fin (2 * n + 3) → ℚ) :
    (heightCoordinates n t).mulVec x (Fin.last (2 * n + 2)) =
      (1 + t)⁻¹ * x (Fin.last (2 * n + 2)) -
        (∑ i : Fin (2 * n + 2), x i.castSucc) := by
  simp only [Matrix.mulVec, dotProduct, heightCoordinates, ite_true]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte, Finset.sum_neg_distrib,
    neg_one_mul]
  ring


/-- Every nonzero integral vector has a cyclic image with a coordinate of magnitude at least one. -/
theorem oddCycle_cube (n : ℕ) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : Fin (2 * n + 3) → ℤ)
    (h : ∀ i, |(oddCycle n t).mulVec (fun j => (x j : ℚ)) i| < 1) : x = 0 := by
  let xn : ℕ → ℤ := fun j => if hj : j < 2 * n + 3 then x ⟨j, hj⟩ else 0
  have hx (j : ℕ) (hj : j < 2 * n + 3) : xn j = x ⟨j, hj⟩ := by
    simp [xn, dif_pos hj]
  have hchain (j : ℕ) (hj : j < 2 * n + 2) :
      |(xn j : ℚ) + t * xn (j + 1)| < 1 := by
    have hh := h (⟨j, by omega⟩ : Fin (2 * n + 3))
    rw [oddCycle_apply] at hh
    have hnext : finRotate (2 * n + 3) (⟨j, by omega⟩ : Fin (2 * n + 3)) =
        ⟨j + 1, by omega⟩ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (by
        intro heq
        have heqv := congrArg Fin.val heq
        simp only [Fin.val_last] at heqv
        omega)]
    rw [hnext] at hh
    simpa only [hx j (by omega), hx (j + 1) (by omega)] using hh
  have hwrap : |(xn (2 * n + 2) : ℚ) + t * xn 0| < 1 := by
    have hh := h (Fin.last (2 * n + 2))
    rw [oddCycle_apply, finRotate_last] at hh
    simpa only [hx (2 * n + 2) (by omega), hx 0 (by omega)] using hh
  have hz := odd_cycle_cube t ht0 ht1 xn n hchain hwrap
  funext i
  have hi : xn i.val = x i := by simpa only [hx i.val i.isLt] using congrArg x (Fin.ext rfl)
  rw [← hi, hz i.val i.isLt]
  rfl


private theorem heightCoordinates_sum (n : ℕ) (t : ℚ)
    (x : Fin (2 * n + 3) → ℚ) :
    (∑ i, (heightCoordinates n t).mulVec x i) =
      (1 + t)⁻¹ * x (Fin.last (2 * n + 2)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [heightCoordinates_nonlast _ _ _ _ (Fin.castSucc_ne_last _),
    heightCoordinates_last]
  ring

private theorem oddCycle_sum (n : ℕ) (t : ℚ) (x : Fin (2 * n + 3) → ℚ) :
    (∑ i, (oddCycle n t).mulVec x i) = (1 + t) * ∑ i, x i := by
  simp_rw [oddCycle_apply]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Equiv.sum_comp]
  ring

/-- Sum of the coordinates of the block's output is its last input coordinate. -/
theorem oddBlock_height (n : ℕ) (t : ℚ) (ht : t ≠ -1)
    (x : Fin (2 * n + 3) → ℚ) :
    (∑ i, (oddBlock n t).mulVec x i) = x (Fin.last (2 * n + 2)) := by
  rw [oddBlock, ← Matrix.mulVec_mulVec, oddCycle_sum, heightCoordinates_sum]
  have ht' : 1 + t ≠ 0 := by intro h; apply ht; linarith
  field_simp

private def kernelInt (n : ℕ) (x : Fin (2 * n + 3) → ℤ) :
    Fin (2 * n + 3) → ℤ :=
  fun i => if i = Fin.last (2 * n + 2) then
    -(∑ j : Fin (2 * n + 2), x j.castSucc) else x i

private theorem kernelInt_sum (n : ℕ) (x : Fin (2 * n + 3) → ℤ) :
    (∑ i, kernelInt n x i) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [kernelInt, Fin.castSucc_ne_last, ↓reduceIte]
  exact add_neg_cancel _

private theorem kernelInt_coordinates (n : ℕ) (t : ℚ)
    (x : Fin (2 * n + 3) → ℤ) (hx : x (Fin.last (2 * n + 2)) = 0) :
    (heightCoordinates n t).mulVec (fun i => (x i : ℚ)) =
      (fun i => (kernelInt n x i : ℚ)) := by
  funext i
  by_cases hi : i = Fin.last (2 * n + 2)
  · subst i
    rw [heightCoordinates_last, hx]
    simp [kernelInt]
  · rw [heightCoordinates_nonlast n t _ i hi]
    simp [kernelInt, hi]

/-- Kernel columns of the block are cube separated. -/
theorem oddBlock_cube (n : ℕ) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : Fin (2 * n + 3) → ℤ) (hx : x (Fin.last (2 * n + 2)) = 0)
    (h : ∀ i, |(oddBlock n t).mulVec (fun j => (x j : ℚ)) i| < 1) : x = 0 := by
  have h' (i : Fin (2 * n + 3)) :
      |(oddCycle n t).mulVec (fun j => (kernelInt n x j : ℚ)) i| < 1 := by
    rw [oddBlock, ← Matrix.mulVec_mulVec, kernelInt_coordinates n t x hx] at h
    exact h i
  have hz := oddCycle_cube n t ht0 ht1 (kernelInt n x) h'
  funext i
  by_cases hi : i = Fin.last (2 * n + 2)
  · simpa [hi] using hx
  · have hh := congrFun hz i
    simpa [kernelInt, hi] using hh


private theorem heightCoordinates_unit (n : ℕ) (t : ℚ) :
    (heightCoordinates n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) =
      Pi.single (Fin.last (2 * n + 2)) (1 + t)⁻¹ := by
  funext i
  by_cases hi : i = Fin.last (2 * n + 2)
  · subst i
    rw [heightCoordinates_last]
    simp
  · rw [heightCoordinates_nonlast n t _ i hi]
    simp [Pi.single_eq_of_ne hi]


private def oddBlockWeight (n : ℕ) (t : ℚ) : Fin (2 * n + 3) → ℚ :=
  Pi.single (Fin.last (2 * n + 2)) (1 + t)⁻¹

private theorem oddBlock_unit (n : ℕ) (t : ℚ) (i : Fin (2 * n + 3)) :
    (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i =
      oddBlockWeight n t i + t * oddBlockWeight n t (finRotate _ i) := by
  rw [oddBlock, ← Matrix.mulVec_mulVec, heightCoordinates_unit, oddCycle_apply]
  rfl

private theorem oddBlock_unit_before (n : ℕ) (t : ℚ)
    (i : Fin (2 * n + 3)) (hi : (i : ℕ) < 2 * n + 1) :
    (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i = 0 := by
  rw [oddBlock_unit]
  have hne : i ≠ Fin.last (2 * n + 2) := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_last] at this
    omega
  have hr : finRotate (2 * n + 3) i ≠ Fin.last (2 * n + 2) := by
    intro heq
    have hv := congrArg Fin.val heq
    rw [coe_finRotate_of_ne_last hne] at hv
    simp only [Fin.val_last] at hv
    omega
  simp [oddBlockWeight, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hr]

private theorem oddBlock_unit_pen (n : ℕ) (t : ℚ) :
    (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1)
      (⟨2 * n + 1, by omega⟩ : Fin (2 * n + 3)) = t * (1 + t)⁻¹ := by
  rw [oddBlock_unit]
  have hne : (⟨2 * n + 1, by omega⟩ : Fin (2 * n + 3)) ≠
      Fin.last (2 * n + 2) := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_last] at this
    omega
  have hr : finRotate (2 * n + 3) (⟨2 * n + 1, by omega⟩ : Fin (2 * n + 3)) =
      Fin.last (2 * n + 2) := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last hne]
    simp
  rw [hr]
  simp [oddBlockWeight, Pi.single_eq_of_ne hne]

private theorem oddBlock_unit_last (n : ℕ) (t : ℚ) :
    (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1)
      (Fin.last (2 * n + 2)) = (1 + t)⁻¹ := by
  rw [oddBlock_unit, finRotate_last]
  have hne : (0 : Fin (2 * n + 3)) ≠ Fin.last (2 * n + 2) := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  simp [oddBlockWeight, Pi.single_eq_of_ne hne]

private theorem oddBlock_kernel_apply (n : ℕ) (t : ℚ)
    (z : Fin (2 * n + 3) → ℤ) (hz : z (Fin.last (2 * n + 2)) = 0)
    (i : Fin (2 * n + 3)) :
    (oddBlock n t).mulVec (fun j => (z j : ℚ)) i =
      (kernelInt n z i : ℚ) + t * kernelInt n z (finRotate _ i) := by
  rw [oddBlock, ← Matrix.mulVec_mulVec, kernelInt_coordinates n t z hz,
    oddCycle_apply]

private theorem oddBlock_escape_pos (n : ℕ) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : Fin (2 * n + 3) → ℤ) (hz : z (Fin.last (2 * n + 2)) = 0)
    (a : ℚ) (ha : (1 + t) / t ≤ a)
    (hshort : ∀ i : Fin (2 * n + 3),
      |(oddBlock n t).mulVec (fun j => (z j : ℚ)) i +
        a * (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i| < 1) :
    False := by
  let xn : ℕ → ℤ := fun j => if hj : j < 2 * n + 3 then kernelInt n z ⟨j, hj⟩ else 0
  have hx (j : ℕ) (hj : j < 2 * n + 3) : xn j = kernelInt n z ⟨j, hj⟩ := by
    simp [xn, dif_pos hj]
  have hsum : (∑ j ∈ Finset.range (2 * n + 3), xn j) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [xn] using kernelInt_sum n z
  have hchain (j : ℕ) (hj : j < 2 * n + 1) :
      |(xn j : ℚ) + t * xn (j + 1)| < 1 := by
    let i : Fin (2 * n + 3) := ⟨j, by omega⟩
    have hh := hshort i
    rw [oddBlock_kernel_apply n t z hz, oddBlock_unit_before n t i (by dsimp [i]; omega),
      mul_zero, add_zero] at hh
    have hn : finRotate (2 * n + 3) i = (⟨j + 1, by omega⟩ : Fin (2 * n + 3)) := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (by
        intro heq
        have hv := congrArg Fin.val heq
        simp [i] at hv
        omega)]
    rw [hn] at hh
    simpa only [hx j (by omega), hx (j + 1) (by omega)] using hh
  have hbase := chain_last_nonnegative t ht0 ht1 xn n hchain hsum
  have htpos : 0 < (1 + t : ℚ) := by linarith
  have hprod : 1 + t ≤ a * t := (div_le_iff₀ ht0).mp ha
  have ha0 : 0 ≤ a := (div_pos htpos ht0).le.trans ha
  have hAt : 1 ≤ a * (t * (1 + t)⁻¹) := by
    calc
      1 = (1 + t) * (1 + t)⁻¹ := (mul_inv_cancel₀ (ne_of_gt htpos)).symm
      _ ≤ (a * t) * (1 + t)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr htpos.le)
      _ = a * (t * (1 + t)⁻¹) := by ring
  have hA : 1 ≤ a * (1 + t)⁻¹ := by
    have hle : 1 + t ≤ a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ht1.le)]
    calc
      1 = (1 + t) * (1 + t)⁻¹ := (mul_inv_cancel₀ (ne_of_gt htpos)).symm
      _ ≤ a * (1 + t)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr htpos.le)
  have hpen : |(xn (2 * n + 1) : ℚ) + t * xn (2 * n + 2) +
      a * (t * (1 + t)⁻¹)| < 1 := by
    have hh := hshort (⟨2 * n + 1, by omega⟩ : Fin (2 * n + 3))
    rw [oddBlock_kernel_apply n t z hz, oddBlock_unit_pen] at hh
    have hr : finRotate (2 * n + 3) (⟨2 * n + 1, by omega⟩ : Fin (2 * n + 3)) =
        Fin.last (2 * n + 2) := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_last] at hv
        omega)]
      simp
    have hlastx : kernelInt n z (Fin.last (2 * n + 2)) = xn (2 * n + 2) := by
      rw [hx (2 * n + 2) (by omega)]
      congr 1
    rw [hr, hlastx, ← hx (2 * n + 1) (by omega)] at hh
    exact hh
  have hlast : |(xn (2 * n + 2) : ℚ) + t * xn 0 +
      a * (1 + t)⁻¹| < 1 := by
    have hh := hshort (Fin.last (2 * n + 2))
    rw [oddBlock_kernel_apply n t z hz, oddBlock_unit_last, finRotate_last] at hh
    have hlastx : kernelInt n z (Fin.last (2 * n + 2)) = xn (2 * n + 2) := by
      rw [hx (2 * n + 2) (by omega)]
      congr 1
    have hzero : kernelInt n z (0 : Fin (2 * n + 3)) = xn 0 := by
      rw [hx 0 (by omega)]
      congr 1
    rwa [hlastx, hzero] at hh
  rcases hbase with hp | hp
  · have hh := (abs_lt.mp hpen).2
    linarith
  · have hh := (abs_lt.mp hlast).2
    linarith

/-- Escape from the odd-cycle zero-height lattice, for arbitrary rational translations. -/
theorem oddBlock_escape (n : ℕ) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (z : Fin (2 * n + 3) → ℤ) (hz : z (Fin.last (2 * n + 2)) = 0)
    (a : ℚ) (ha : (1 + t) / t ≤ |a|) :
    ¬ ∀ i : Fin (2 * n + 3),
      |(oddBlock n t).mulVec (fun j => (z j : ℚ)) i +
        a * (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i| < 1 := by
  intro hshort
  rcases le_total 0 a with hnonneg | hnonpos
  · exact oddBlock_escape_pos n t ht0 ht1 z hz a
      (by simpa only [abs_of_nonneg hnonneg] using ha) hshort
  · have hz' : (fun j => -z j) (Fin.last (2 * n + 2)) = 0 := by simp [hz]
    apply oddBlock_escape_pos n t ht0 ht1 (fun j => -z j) hz' (-a)
      (by simpa only [abs_of_nonpos hnonpos] using ha)
    intro i
    have hh := hshort i
    have hneg : (oddBlock n t).mulVec (fun j => ((-z j : ℤ) : ℚ)) i =
        -(oddBlock n t).mulVec (fun j => (z j : ℚ)) i := by
      have heq : (fun j => ((-z j : ℤ) : ℚ)) = -(fun j => (z j : ℚ)) := by
        ext j
        simp
      rw [heq, Matrix.mulVec_neg]
      rfl
    rw [hneg]

    have heq : -(oddBlock n t).mulVec (fun j => (z j : ℚ)) i +
        -a * (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i =
        -((oddBlock n t).mulVec (fun j => (z j : ℚ)) i +
          a * (oddBlock n t).mulVec (Pi.single (Fin.last (2 * n + 2)) 1) i) := by ring
    rw [heq, abs_neg]
    exact hh






/-- The height coordinate change is lower triangular with last diagonal entry `(1+t)⁻¹`. -/
theorem heightCoordinates_det (n : ℕ) (t : ℚ) :
    (heightCoordinates n t).det = (1 + t)⁻¹ := by
  have htri : (heightCoordinates n t).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hne : i ≠ Fin.last (2 * n + 2) := by
      intro heq
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hij'
    have hne' : i ≠ j := ne_of_lt hij'
    simp [heightCoordinates, hne, hne']
  rw [Matrix.det_of_lowerTriangular _ htri, Fin.prod_univ_castSucc]
  simp [heightCoordinates, Fin.castSucc_ne_last]

private theorem oddCycle_entry (n : ℕ) (t : ℚ) (i j : Fin (2 * n + 3)) :
    oddCycle n t i j = (if i = j then 1 else 0) +
      t * (if finRotate (2 * n + 3) i = j then 1 else 0) := by
  have hh := congrFun (Matrix.mulVec_single_one (oddCycle n t) j) i
  rw [oddCycle_apply] at hh
  simpa only [Matrix.col_apply, Pi.single_apply] using hh.symm

private theorem oddCycle_last_entry (n : ℕ) (t : ℚ) (j : Fin (2 * n + 3)) :
    oddCycle n t (Fin.last (2 * n + 2)) j =
      (if j = Fin.last (2 * n + 2) then 1 else 0) +
        t * (if j = 0 then 1 else 0) := by
  rw [oddCycle_entry, finRotate_last]
  simp only [eq_comm]

private theorem oddCycle_rotate_castSucc (n : ℕ) (i : Fin (2 * n + 2)) :
    finRotate (2 * n + 3) i.castSucc = i.succ := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

private theorem oddCycle_minor_last_det (n : ℕ) (t : ℚ) :
    ((oddCycle n t).submatrix (Fin.last (2 * n + 2)).succAbove
      (Fin.last (2 * n + 2)).succAbove).det = 1 := by
  have htri : ((oddCycle n t).submatrix (Fin.last (2 * n + 2)).succAbove
      (Fin.last (2 * n + 2)).succAbove).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    rw [Matrix.submatrix_apply, Fin.succAbove_last,
      oddCycle_entry, oddCycle_rotate_castSucc]
    have hne : (i.castSucc : Fin (2 * n + 3)) ≠ j.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc] at hv
      omega
    have hne' : (i.succ : Fin (2 * n + 3)) ≠ j.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    simp [hne, hne']
  rw [Matrix.det_of_upperTriangular htri]
  apply Finset.prod_eq_one
  intro i _
  rw [Matrix.submatrix_apply, Fin.succAbove_last,
    oddCycle_entry, oddCycle_rotate_castSucc]
  have hne : (i.castSucc : Fin (2 * n + 3)) ≠ i.succ := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  simp [hne.symm]

private theorem oddCycle_minor_zero_det (n : ℕ) (t : ℚ) :
    ((oddCycle n t).submatrix (Fin.last (2 * n + 2)).succAbove
      (0 : Fin (2 * n + 3)).succAbove).det = t ^ (2 * n + 2) := by
  have htri : ((oddCycle n t).submatrix (Fin.last (2 * n + 2)).succAbove
      (0 : Fin (2 * n + 3)).succAbove).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero,
      oddCycle_entry, oddCycle_rotate_castSucc]
    have hne : (i.castSucc : Fin (2 * n + 3)) ≠ j.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    have hne' : (i.succ : Fin (2 * n + 3)) ≠ j.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_succ] at hv
      omega
    simp [hne, hne']
  rw [Matrix.det_of_lowerTriangular _ htri]
  have hdiag (i : Fin (2 * n + 2)) :
      ((oddCycle n t).submatrix (Fin.last (2 * n + 2)).succAbove
        (0 : Fin (2 * n + 3)).succAbove) i i = t := by
    rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero,
      oddCycle_entry, oddCycle_rotate_castSucc]
    have hne : (i.castSucc : Fin (2 * n + 3)) ≠ i.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    simp [hne]
  simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The determinant of the odd cyclic bidiagonal matrix. -/
theorem oddCycle_det (n : ℕ) (t : ℚ) :
    (oddCycle n t).det = 1 + t ^ (2 * n + 3) := by
  let A := oddCycle n t
  let f : Fin (2 * n + 3) → ℚ := fun j =>
    (-1) ^ ((Fin.last (2 * n + 2) : Fin (2 * n + 3)).val + j.val) *
      A (Fin.last (2 * n + 2)) j *
        (A.submatrix (Fin.last (2 * n + 2)).succAbove j.succAbove).det
  have hsum : (∑ j : Fin (2 * n + 3), f j) = f 0 + f (Fin.last (2 * n + 2)) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have hinterior (j : Fin (2 * n + 1)) : f (j.castSucc.succ) = 0 := by
      have hne : (j.castSucc.succ : Fin (2 * n + 3)) ≠ Fin.last (2 * n + 2) := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
        omega
      have hne' : (j.castSucc.succ : Fin (2 * n + 3)) ≠ 0 := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hv
        omega
      simp [f, A, oddCycle_last_entry, hne, hne']
    simp only [hinterior, Finset.sum_const_zero, zero_add]
    congr 1
  have hzero : f 0 = t ^ (2 * n + 3) := by
    simp only [f, A, Fin.val_last, Fin.val_zero, add_zero, oddCycle_last_entry,
      oddCycle_minor_zero_det]
    have hne : (0 : Fin (2 * n + 3)) ≠ Fin.last (2 * n + 2) := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    simp [hne.symm, pow_add, pow_mul]
    ring
  have hlast : f (Fin.last (2 * n + 2)) = 1 := by
    simp only [f, A, oddCycle_last_entry, oddCycle_minor_last_det,
      Fin.val_last]
    have hne : (Fin.last (2 * n + 2) : Fin (2 * n + 3)) ≠ 0 := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    simp [hne, pow_add, pow_mul]
  rw [Matrix.det_succ_row A (Fin.last (2 * n + 2))]
  change (∑ j : Fin (2 * n + 3), f j) = _
  rw [hsum, hzero, hlast]
  ring

/-- The height-normalized odd block has rational covolume `(1+t^m)/(1+t)`. -/
theorem oddBlock_det (n : ℕ) (t : ℚ) :
    (oddBlock n t).det = (1 + t ^ (2 * n + 3)) / (1 + t) := by
  rw [oddBlock, Matrix.det_mul, oddCycle_det, heightCoordinates_det]
  ring





end Erdos1Aux
