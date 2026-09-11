import FormalConjectures.Util.ProblemImports
open Nat
open Classical

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if h : partners.Nonempty then
    sInf partners
  else
    0

namespace Harshad

def ds (n : ℕ) : ℕ := (digits 10 n).sum

lemma ds_step (n : ℕ) : ds n = n % 10 + ds (n / 10) := by
  by_cases hn : n = 0
  · simp [hn, ds]
  · simp [ds, digits_eq_cons_digits_div (by decide : 1 < 10) hn]

lemma ds_small {n : ℕ} (hn : n < 10) : ds n = n := by
  rw [ds_step, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn]
  simp [ds]

lemma ds_pos {n : ℕ} (hn : 0 < n) : 0 < ds n := by
  have hmem := List.getLast_mem (digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hn) : digits 10 n ≠ [])
  have hne := getLast_digit_ne_zero 10 (Nat.ne_of_gt hn)
  have hle := List.single_le_sum (fun x (_ : x ∈ digits 10 n) => Nat.zero_le x) _ hmem
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hne) hle

/-- Separate decimal blocks have additive digit sums. -/
lemma ds_add_pow {x t : ℕ} (hx : x < 10 ^ t) (y : ℕ) :
    ds (x + 10 ^ t * y) = ds x + ds y := by
  by_cases hy : y = 0
  · simp [hy, ds]
  have hlen : (digits 10 x).length ≤ t := (digits_length_le_iff (by decide) x).mpr hx
  have hh := digits_append_zeroes_append_digits (b := 10) (n := x)
    (k := t - (digits 10 x).length) (by decide) (Nat.pos_of_ne_zero hy)
  rw [Nat.add_sub_of_le hlen] at hh
  unfold ds
  rw [← hh]
  simp

/-- Complementary decimal digits sum to nine in each position. -/
lemma ds_complement (t x : ℕ) (hx : x < 10 ^ t) :
    ds (10 ^ t - 1 - x) + ds x = 9 * t := by
  induction t generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, ds]
  | succ t ih =>
    have hq : x / 10 < 10 ^ t := by
      rw [pow_succ] at hx
      omega
    have hr := Nat.mod_lt x (by decide : 0 < 10)
    have heq := Nat.mod_add_div x 10
    have hpow : 0 < 10 ^ t := by positivity
    have hcomp : 10 ^ (t + 1) - 1 - x =
        (9 - x % 10) + 10 * (10 ^ t - 1 - x / 10) := by
      rw [pow_succ]
      omega
    rw [hcomp, show 10 * (10 ^ t - 1 - x / 10) =
      10 ^ 1 * (10 ^ t - 1 - x / 10) by simp,
      ds_add_pow (by omega : 9 - x % 10 < 10 ^ 1), ds_small (by omega)]
    rw [ds_step x]
    have := ih (x / 10) hq
    omega

/-- Multiplying a sufficiently long block of nines by `d` preserves its digit sum. -/
lemma ds_nines_mul {d t : ℕ} (hd : 0 < d) (hdt : d ≤ 10 ^ t) :
    ds (d * (10 ^ t - 1)) = 9 * t := by
  have hpow : 0 < 10 ^ t := by positivity
  have heq : d * (10 ^ t - 1) = (10 ^ t - d) + 10 ^ t * (d - 1) := by
    have h1 : d - 1 + 1 = d := by omega
    have h2 : 10 ^ t - 1 + 1 = 10 ^ t := by omega
    have h3 : 10 ^ t - d + d = 10 ^ t := by omega
    nlinarith
  rw [heq, ds_add_pow (by omega : 10 ^ t - d < 10 ^ t)]
  have hcomp := ds_complement t (d - 1) (by omega)
  have : 10 ^ t - 1 - (d - 1) = 10 ^ t - d := by omega
  rwa [this] at hcomp

lemma ds_bound (n : ℕ) : ds n ≤ n / 10 + 9 := by
  rw [ds_step]
  have hle := digit_sum_le 10 (n / 10)
  have hmod := Nat.mod_lt n (by decide : 0 < 10)
  unfold ds
  omega

lemma pow_bound {t : ℕ} (ht : 2 ≤ t) : t + 10 ≤ 10 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

/-- Construct a multiple of `D(n)` with digit sum exactly `n`. -/
lemma exists_multiple (n : ℕ) (hn : 21 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ ds n ∣ k ∧ ds k = n := by
  let d := ds n
  let r := ds d
  let t := (n - r) / 9
  have hd : 0 < d := ds_pos (by omega)
  have hr : r ≤ d := digit_sum_le 10 d
  have hdn : d ≤ n := digit_sum_le 10 n
  have hmod : n % 9 = r % 9 :=
    (modEq_nine_digits_sum n).trans (modEq_nine_digits_sum d)
  have hnt : n = 9 * t + r := by
    dsimp [t]
    omega
  have hdb : d ≤ n / 10 + 9 := ds_bound n
  have ht : 2 ≤ t := by omega
  have hdt : d ≤ 10 ^ t := by
    have : d ≤ t + 10 := by omega
    exact this.trans (pow_bound ht)
  let b := d * (10 ^ t - 1)
  let k := b + 10 ^ (digits 10 b).length * d
  have hdsb : ds b = 9 * t := ds_nines_mul hd hdt
  have hdsk : ds k = n := by
    rw [ds_add_pow (lt_base_pow_length_digits (by decide : 1 < 10)) d]
    change ds b + r = n
    omega
  have hdk : d ∣ k := by
    exact dvd_add (dvd_mul_right d _) (dvd_mul_left d _)
  have hk : 0 < k := by
    have := digit_sum_le 10 k
    change ds k ≤ k at this
    omega
  exact ⟨k, hk, hdk, hdsk⟩

lemma exists_partner (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≠ n ∧ ds n ∣ k ∧ ds k ∣ n := by
  by_cases hlarge : 21 ≤ n
  · obtain ⟨k, hk, hdk, hdsk⟩ := exists_multiple n hlarge
    by_cases hkn : k = n
    · refine ⟨10 * k, by positivity, ?_, dvd_mul_of_dvd_right hdk 10, ?_⟩
      · omega
      · have hh : ds (10 * k) = ds k := by
          simp [ds, digits_base_mul (by decide : 1 < 10) hk]
        rw [hh, hdsk]
    · exact ⟨k, hk, hkn, hdk, hdsk ▸ dvd_refl n⟩
  · refine ⟨[0, 10, 20, 30, 40, 50, 60, 70, 80, 90, 1, 10, 3, 100,
        10, 12, 35, 1000, 9, 10, 2][n]!, ?_⟩
    interval_cases n <;> norm_num [ds, Nat.digits_eq_cons_digits_div]

end Harshad

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  have hp : {k : ℕ | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧
      (digits 10 k).sum ∣ n}.Nonempty := Harshad.exists_partner n hn
  unfold a
  dsimp only
  rw [dif_pos hp]
  exact Nat.ne_of_gt (Nat.sInf_mem hp).1

theorem oeis_272479_conjecture_0.disproof : ¬ (type_of% @oeis_272479_conjecture_0) := sorry
