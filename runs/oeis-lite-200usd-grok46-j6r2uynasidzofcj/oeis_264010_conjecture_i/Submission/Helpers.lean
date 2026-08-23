import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

def primeCond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

def T (z : ℕ) : ℕ := z * (z + 1) / 2

def A264010 (n : ℕ) : ℕ :=
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z then 1 else 0

lemma T_spec (z : ℕ) : 2 * T z = z * (z + 1) := by
  simp [T]
  have : 2 ∣ z * (z + 1) := Nat.dvd_mul_right_of_dvd (even_or_odd z |>.elim
    (fun h => h.two_dvd) (fun h => (h.add_odd odd_one).two_dvd.mul_left _))
  -- simpler:
  sorry

-- Let's do T_spec more carefully
lemma two_dvd_mul_succ (z : ℕ) : 2 ∣ z * (z + 1) := by
  cases Nat.even_or_odd z with
  | inl h => exact h.two_dvd.mul_right _
  | inr h =>
    have : Even (z + 1) := h.add_odd odd_one
    exact this.two_dvd.mul_left _

lemma T_mul_two (z : ℕ) : T z * 2 = z * (z + 1) := by
  rw [T, Nat.div_mul_cancel (two_dvd_mul_succ z)]

lemma T_mono : Monotone T := by
  intro a b hab
  simp only [T]
  exact Nat.div_le_div_right (Nat.mul_le_mul hab (Nat.succ_le_succ hab))

lemma T_le_of_T_le {z n : ℕ} (h : T z ≤ n) : z ≤ 2 * n + 1 := by
  have h2 : z * (z + 1) ≤ 2 * n := by
    rw [← T_mul_two]
    exact Nat.mul_le_mul_right 2 h
  -- z^2 ≤ z(z+1) ≤ 2n so z ≤ sqrt(2n) ≤ 2n+1
  have : z * z ≤ z * (z + 1) := Nat.mul_le_mul_left z (Nat.le_succ z)
  have : z * z ≤ 2 * n := this.trans h2
  have hz : z ≤ n + 1 ∨ n < z := le_or_gt _ _
  cases hz with
  | inl h => omega
  | inr h =>
    have : (n + 1) * (n + 1) ≤ z * z := Nat.mul_le_mul (Nat.succ_le_of_lt h) (Nat.succ_le_of_lt h)
    have : (n + 1) * (n + 1) ≤ 2 * n := this.trans ‹_›
    nlinarith

instance : DecidablePred primeCond := fun k =>
  inferInstanceAs (Decidable (k.Prime ∨ (k + 1).Prime))

/-- A valid triple for n. -/
structure ValidTriple (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  hx : x < 2 * n + 2
  hy : y < 2 * n + 2
  hz : z < 2 * n + 2
  heq : x * x + y * (y + 1) + T z = n
  hyP : primeCond y
  hzP : primeCond z

lemma one_le_A_of_triple {n : ℕ} (t : ValidTriple n) : 1 ≤ A264010 n := by
  simp only [A264010]
  have hx : t.x ∈ range (2 * n + 2) := by simp [t.hx]
  have hy : t.y ∈ range (2 * n + 2) := by simp [t.hy]
  have hz : t.z ∈ range (2 * n + 2) := by simp [t.hz]
  refine Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx |>.trans' ?_
  simp only [ge_iff_le]
  refine Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy |>.trans' ?_
  refine Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz |>.trans' ?_
  simp [t.heq, t.hyP, t.hzP]

lemma two_le_A_of_two_triples {n : ℕ} (t₁ t₂ : ValidTriple n) (hne : t₁.x ≠ t₂.x ∨ t₁.y ≠ t₂.y ∨ t₁.z ≠ t₂.z) :
    2 ≤ A264010 n := by
  sorry
