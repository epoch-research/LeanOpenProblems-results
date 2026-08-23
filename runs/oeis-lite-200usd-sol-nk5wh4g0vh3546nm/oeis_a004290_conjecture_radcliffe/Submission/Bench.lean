import FormalConjectures.Util.ProblemImports
open Nat Set

noncomputable def AA (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

def Good (n m : ℕ) : Prop := 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

def repunit (L : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate L 1)

lemma repunit_zero : repunit 0 = 0 := by simp [repunit]
lemma repunit_succ (L : ℕ) : repunit (L+1) = 1 + 10 * repunit L := by
  simp [repunit, List.replicate_succ, Nat.ofDigits_cons]

lemma repunit_digits {L : ℕ} (hL : 0 < L) : Nat.digits 10 (repunit L) = List.replicate L 1 := by
  apply Nat.digits_ofDigits
  · norm_num
  · simp
  · simpa using hL.ne'

lemma repunit_pos {L : ℕ} (hL : 0 < L) : 0 < repunit L := by
  rw [repunit]
  cases L with
  | zero => simp at hL
  | succ L => simp [List.replicate_succ, Nat.ofDigits_cons]

lemma repunit_mul_nine (L : ℕ) : 9 * repunit L = 10^L - 1 := by
  induction L with
  | zero => simp [repunit]
  | succ L ih =>
    have hp : 0 < 10^L := by positivity
    have he : 10^L = 9 * repunit L + 1 := by omega
    rw [show L+1 = L + 1 by omega, repunit_succ, pow_succ, he]
    omega

lemma repunit_eq (L : ℕ) : repunit L = (10^L - 1) / 9 := by
  exact Nat.eq_div_of_mul_eq_right (by norm_num) (repunit_mul_nine L)

lemma repunit_good_digits {L : ℕ} (hL : 0 < L) :
    ∀ d ∈ Nat.digits 10 (repunit L), d = 0 ∨ d = 1 := by
  rw [repunit_digits hL]
  simp

lemma nine_dvd_geom_nine (k : ℕ) :
    9 ∣ ∑ j ∈ Finset.range 9, 10 ^ (k * j) := by
  norm_num [Nat.dvd_iff_mod_eq_zero, Finset.sum_range_succ,
    Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

lemma repunit_add (a b : ℕ) :
    repunit (a+b) = repunit a + 10^a * repunit b := by
  unfold repunit
  rw [List.replicate_add, Nat.ofDigits_append]
  simp

lemma repunit_mul_geom (k q : ℕ) :
    repunit (q*k) = repunit k * (∑ j ∈ Finset.range q, 10^(k*j)) := by
  induction q with
  | zero => simp [repunit]
  | succ q ih =>
    rw [Nat.succ_mul, repunit_add, ih, Finset.sum_range_succ]
    simp only [pow_mul]
    ring

