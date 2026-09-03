import Submission.ContinuousIntervalSeeded
import Submission.ContinuousIntervalOrdering

/-! Dilation comparisons for the unpatched interval recursion. These results
compare fixed regular seeds; they do not assert quadratic positivity. -/
namespace Erdos970.ContinuousInterval

noncomputable def coarseError : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 * coarseError k + 1

lemma coarseError_nonneg (k : ℕ) : 0 ≤ coarseError k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => dsimp [coarseError]; positivity

lemma density_le_one (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) : density q k ≤ 1 := by
  apply Finset.prod_le_one
  · intro i hi
    exact sub_nonneg.mpr (hq i (Finset.mem_range.mp hi)).2
  · intro i hi
    linarith [(hq i (Finset.mem_range.mp hi)).1]

/-- A deliberately coarse finite-stage discrepancy estimate. -/
theorem envelope_affine_bound (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ x, density q k * x - coarseError k ≤ (envelope q k x).1) ∧
      (∀ x, 0 ≤ x → (envelope q k x).2 ≤ density q k * x + coarseError k) := by
  induction k with
  | zero =>
    simp only [density, Finset.range_zero, Finset.prod_empty, coarseError, envelope,
      one_mul, sub_zero, add_zero]
    exact ⟨fun x => le_max_right _ _, fun x _ => le_rfl⟩
  | succ k ih =>
    have hqq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (by omega)
    have hb := ih hqq
    have hreg := envelope_regular q k hqq
    have hqk := hq k (by omega)
    have hd0 : 0 ≤ density q k * (1 - q k) :=
      mul_nonneg hreg.density_nonneg (sub_nonneg.mpr hqk.2)
    have hd1 : density q k * (1 - q k) ≤ 1 := by
      calc
        _ ≤ density q k * 1 := mul_le_mul_of_nonneg_left (by linarith) hreg.density_nonneg
        _ ≤ 1 := by simpa using density_le_one q k hqq
    have hds : density q (k + 1) = density q k * (1 - q k) := by
      simp [density, Finset.prod_range_succ]
    constructor
    · intro x
      have hm := mul_le_mul_of_nonneg_left (le_max_right 0 x) hd0
      have hl := hb.1 (max 0 x)
      have hu := hb.2 (upperArg (q k) (max 0 x))
        (upperArg_nonneg hqk.1 hqk.2 (le_max_left _ _))
      rw [hds, coarseError]
      change _ ≤ max 0 ((envelope q k (max 0 x)).1 -
        (envelope q k (upperArg (q k) (max 0 x))).2)
      apply le_trans _ (le_max_right _ _)
      dsimp [upperArg] at hu ⊢
      nlinarith
    · intro x hx
      have hu := hb.2 x hx
      have hl := hb.1 (lowerArg (q k) x)
      rw [hds, coarseError]
      change (envelope q k x).2 - (envelope q k (lowerArg (q k) x)).1 ≤ _
      dsimp [lowerArg] at hl ⊢
      nlinarith

lemma envelope_upper_le_input (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    (envelope q k x).2 ≤ x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hqq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (by omega)
    have h := (envelope_regular q k hqq).lower_nonneg ((x + 1) * q k - 1)
    have hh := ih hqq
    change (envelope q k x).2 - (envelope q k ((x + 1) * q k - 1)).1 ≤ x
    linarith

/-- At a fixed nonnegative length, adding a sieve stage cannot improve the
ordinary lower envelope. -/
lemma envelope_lower_antitone (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    Antitone (fun k => (envelope q k x).1) := by
  apply antitone_nat_of_succ_le
  intro k
  have hr := envelope_regular q k (fun i _ => hq i)
  change max 0 ((envelope q k (max 0 x)).1 -
    (envelope q k (upperArg (q k) (max 0 x))).2) ≤ _
  rw [max_eq_right hx]
  apply max_le (hr.lower_nonneg x)
  exact sub_le_self _ (hr.upper_nonneg _ (upperArg_nonneg (hq k).1 (hq k).2 hx))

lemma Dominates.trans {L U L' U' L'' U'' : ℝ → ℝ}
    (h : Dominates L U L' U') (h' : Dominates L' U' L'' U'') :
    Dominates L U L'' U'' :=
  ⟨fun x => (h'.1 x).trans (h.1 x), fun x hx => (h.2 x hx).trans (h'.2 x hx)⟩

/-- Dilation reduces the rounding errors in a sieve stage. -/
theorem Regular.dilation_step {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 1 ≤ c) :
    Dominates (fun x => stepLower q L U (c * x) / c)
      (fun x => stepUpper q L U (c * x) / c)
      (stepLower q (fun x => L (c * x) / c) (fun x => U (c * x) / c))
      (stepUpper q (fun x => L (c * x) / c) (fun x => U (c * x) / c)) := by
  have hc0 : 0 < c := by linarith
  have hcerr : 0 ≤ (c - 1) * (1 - q) := mul_nonneg (by linarith) (by linarith)
  constructor
  · intro x
    have hm : max 0 (c * x) = c * max 0 x := by
      rw [mul_max_of_nonneg _ _ hc0.le, mul_zero]
    have hA : upperArg q (c * max 0 x) ≤ c * upperArg q (max 0 x) := by
      dsimp [upperArg]
      nlinarith
    have hA0 := upperArg_nonneg hq0 hq1
      (mul_nonneg hc0.le (le_max_left 0 x))
    have hu := h.upper_mono hA0 (hA0.trans hA) hA
    dsimp [stepLower, clip]
    rw [hm, ← max_div_div_right hc0.le, zero_div]
    apply max_le_max_left
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (sub_le_sub_left hu _) hc0.le
  · intro x hx
    have hB : c * lowerArg q x ≤ lowerArg q (c * x) := by
      dsimp [lowerArg]
      nlinarith
    have hl := h.lower_mono hB
    dsimp [stepUpper]
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (sub_le_sub_left hl _) hc0.le

/-- A comparison at one fixed prefix propagates through every unpatched tail.
The lattice is not scaled here: no statement about later chord patches is made. -/
theorem seedRun_dilation_dominates (q : ℕ → ℝ) (b t : ℕ) (c : ℝ)
    (L U : ℝ → ℝ) (hc : 1 ≤ c)
    (hq : ∀ i < b + t, 0 ≤ q i ∧ q i ≤ 1)
    (hbase : Dominates (fun x => (envelope q b (c * x)).1 / c)
      (fun x => (envelope q b (c * x)).2 / c) L U) :
    Dominates (fun x => (envelope q (b + t) (c * x)).1 / c)
      (fun x => (envelope q (b + t) (c * x)).2 / c)
      (seedRun q (fun _ => []) b L U t).1
      (seedRun q (fun _ => []) b L U t).2 := by
  induction t with
  | zero => simpa only [Nat.add_zero, seedRun] using hbase
  | succ t ih =>
    have hqq : ∀ i < b + t, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (by omega)
    have hqt := hq (b + t) (by omega)
    have hs := (ih hqq).step (q (b + t)) hqt.1 hqt.2
    have hd := (envelope_regular q (b + t) hqq).dilation_step
      (q (b + t)) c hqt.1 hqt.2 hc
    simpa only [Nat.add_assoc, envelope, seedRun, chordPatches] using hd.trans hs

#print axioms envelope_affine_bound
#print axioms seedRun_dilation_dominates
end Erdos970.ContinuousInterval
