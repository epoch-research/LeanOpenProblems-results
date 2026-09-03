import FormalConjecturesUtil

/-!
# A partial quartic lower bound for Erdős Problem 322

This independent development proves
`t + 1 ≤ representationCount 4 (3 * 7 ^ (4 * t))` for every natural `t`.
The argument uses integer coefficient pairs with quadratic norm `49 ^ j`,
then distinguishes the scaled representations by divisibility by `7`.

This is only a partial lower bound: the arguments `3 * 7 ^ (4 * t)` grow
exponentially in `t`, so the result does not give a positive-power lower
bound in the represented integer and does not resolve the conjecture.
-/

namespace Erdos322QuarticProgress

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of nonnegative integers. The bases can be restricted to the interval from `0` to `n`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The integer coefficient pairs used in the representations. -/
def coeff : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | j + 1 => (3 * (coeff j).1 - 5 * (coeff j).2,
      5 * (coeff j).1 + 8 * (coeff j).2)

def a (j : ℕ) : ℤ := (coeff j).1

def b (j : ℕ) : ℤ := (coeff j).2

@[simp] lemma a_zero : a 0 = 1 := rfl
@[simp] lemma b_zero : b 0 = 0 := rfl

lemma a_succ (j : ℕ) : a (j + 1) = 3 * a j - 5 * b j := rfl
lemma b_succ (j : ℕ) : b (j + 1) = 5 * a j + 8 * b j := rfl

/-- The binary quadratic form controlling the fourth-power identity. -/
def Q (x y : ℤ) : ℤ := x^2 + x*y + y^2

lemma Q_step (x y : ℤ) : Q (3*x - 5*y) (5*x + 8*y) = 49 * Q x y := by
  dsimp [Q]
  ring

lemma Q_coeff (j : ℕ) : Q (a j) (b j) = 49^j := by
  induction j with
  | zero => norm_num [Q]
  | succ j ih =>
    rw [a_succ, b_succ, Q_step, ih, pow_succ]
    ring

lemma coeff_mod_seven (j : ℕ) :
    (a (j + 1) : ZMod 7) = 3 * 4^j ∧ (b (j + 1) : ZMod 7) = 5 * 4^j := by
  induction j with
  | zero => norm_num [a_succ, b_succ]
  | succ j ih =>
    constructor
    · rw [a_succ]
      push_cast
      rw [ih.1, ih.2, pow_succ]
      ring_nf
      rw [← mul_neg]
      congr 1
    · rw [b_succ]
      push_cast
      rw [ih.1, ih.2, pow_succ]
      ring_nf
      congr 1

lemma seven_not_dvd_a (j : ℕ) : ¬ (7 : ℤ) ∣ a j := by
  intro h
  have hz : (a j : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  cases j with
  | zero => norm_num at hz
  | succ j =>
    rw [(coeff_mod_seven j).1] at hz
    exact (mul_ne_zero (by decide : (3 : ZMod 7) ≠ 0)
      (pow_ne_zero _ (by decide : (4 : ZMod 7) ≠ 0))) hz

lemma seven_not_dvd_natAbs_a (j : ℕ) : ¬ 7 ∣ (a j).natAbs := by
  intro h
  exact seven_not_dvd_a j (Int.natCast_dvd.mpr h)

lemma quartic_identity (x y : ℤ) : x^4 + y^4 + (x+y)^4 = 2 * (Q x y)^2 := by
  dsimp [Q]
  ring

lemma natAbs_fourth (z : ℤ) : (z.natAbs : ℤ)^4 = z^4 := by
  calc
    _ = ((z.natAbs : ℤ)^2)^2 := by ring
    _ = (z^2)^2 := by rw [Int.natAbs_pow_two]
    _ = z^4 := by ring

lemma unscaled_sum (j : ℕ) :
    (a j).natAbs^4 + (b j).natAbs^4 + (a j + b j).natAbs^4 = 2 * 7^(4*j) := by
  apply Int.ofNat_inj.mp
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [natAbs_fourth, natAbs_fourth, natAbs_fourth, quartic_identity, Q_coeff]
  rw [show (49 : ℤ) = 7^2 by norm_num]
  simp only [← pow_mul]
  congr 2
  omega

/-- A scaled four-tuple of nonnegative bases. -/
def quarticTuple (t j : ℕ) : Fin 4 → ℕ :=
  ![7^(t-j) * (a j).natAbs, 7^(t-j) * (b j).natAbs,
    7^(t-j) * (a j + b j).natAbs, 7^t]

lemma quarticTuple_sum {t j : ℕ} (hj : j ≤ t) :
    ∑ i, (quarticTuple t j i)^4 = 3 * 7^(4*t) := by
  have hscale : (7^(t-j))^4 * 7^(4*j) = (7 : ℕ)^(4*t) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hlast : ((7 : ℕ)^t)^4 = 7^(4*t) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    _ = (7^(t-j))^4 *
        ((a j).natAbs^4 + (b j).natAbs^4 + (a j + b j).natAbs^4) + (7^t)^4 := by
      simp [quarticTuple, Fin.sum_univ_succ]
      ring
    _ = 2 * ((7^(t-j))^4 * 7^(4*j)) + (7^t)^4 := by
      rw [unscaled_sum]
      ring
    _ = 3 * 7^(4*t) := by rw [hscale, hlast]; ring

lemma quarticTuple_bound {t j : ℕ} (hj : j ≤ t) (i : Fin 4) :
    quarticTuple t j i ≤ 3 * 7^(4*t) := by
  calc
    quarticTuple t j i ≤ (quarticTuple t j i)^4 := Nat.le_self_pow (by decide) _
    _ ≤ ∑ l, (quarticTuple t j l)^4 :=
      Finset.single_le_sum (f := fun l : Fin 4 ↦ (quarticTuple t j l)^4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = 3 * 7^(4*t) := quarticTuple_sum hj

/-- Cancelling the common power of `7` separates different coefficient indices. -/
lemma scaled_first_ne {t j l : ℕ} (hjl : j < l) (hlt : l ≤ t) :
    7^(t-j) * (a j).natAbs ≠ 7^(t-l) * (a l).natAbs := by
  intro h
  have hexp : t-j = (t-l)+(l-j) := by omega
  rw [hexp, pow_add, mul_assoc] at h
  have he : 7^(l-j) * (a j).natAbs = (a l).natAbs :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h
  apply seven_not_dvd_natAbs_a l
  rw [← he]
  exact dvd_mul_of_dvd_left (dvd_pow_self 7 (by omega)) _

lemma scaled_first_injective (t : ℕ) :
    Function.Injective (fun j : Fin (t+1) ↦ 7^(t-j.val) * (a j.val).natAbs) := by
  intro j l h
  apply Fin.ext
  rcases lt_trichotomy j.val l.val with hjl | hjl | hlj
  · exact False.elim (scaled_first_ne hjl (Nat.le_of_lt_succ l.isLt) h)
  · exact hjl
  · exact False.elim (scaled_first_ne hlj (Nat.le_of_lt_succ j.isLt) h.symm)

/-- A partial lower bound along an explicit exponential sequence. -/
theorem quartic_lower_bound (t : ℕ) :
    t + 1 ≤ representationCount 4 (3 * 7^(4*t)) := by
  let f : Fin (t+1) → (Fin 4 → Fin (3 * 7^(4*t)+1)) :=
    fun j i ↦ ⟨quarticTuple t j i, Nat.lt_succ_of_le
      (quarticTuple_bound (Nat.le_of_lt_succ j.isLt) i)⟩
  have hf : Function.Injective f := by
    intro j l h
    apply scaled_first_injective t
    exact congrArg (fun v ↦ (v 0).val) h
  have hmem (j : Fin (t+1)) :
      f j ∈ ((Finset.univ : Finset (Fin 4 → Fin (3 * 7^(4*t)+1))).filter
        (fun v ↦ ∑ i, (v i : ℕ)^4 = 3 * 7^(4*t))) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, quarticTuple_sum (Nat.le_of_lt_succ j.isLt)⟩
  have h := Finset.card_le_card_of_injOn (s := Finset.univ) f
    (fun j _ ↦ hmem j) hf.injOn
  simpa [representationCount] using h

/-- The number of representations as a sum of four fourth powers is unbounded. -/
theorem quartic_unbounded :
    ∀ B : ℕ, ∃ n : ℕ, B < representationCount 4 n := by
  intro B
  exact ⟨3 * 7^(4*B), (Nat.lt_succ_self B).trans_le (quartic_lower_bound B)⟩

/-- Every fixed representation-count threshold is exceeded at infinitely many arguments. -/
theorem quartic_large_counts_infinite (B : ℕ) :
    {n : ℕ | B < representationCount 4 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun s : ℕ ↦ 3 * 7^(4*(B+s)))
  · intro s u h
    have hp : 7^(4*(B+s)) = 7^(4*(B+u)) :=
      Nat.eq_of_mul_eq_mul_left (by decide) h
    have he := Nat.pow_right_injective (by decide : 2 ≤ 7) hp
    omega
  · intro s
    change B < representationCount 4 (3 * 7^(4*(B+s)))
    have h := quartic_lower_bound (B+s)
    omega

#print axioms quartic_lower_bound
#print axioms quartic_unbounded
#print axioms quartic_large_counts_infinite

end Erdos322QuarticProgress
