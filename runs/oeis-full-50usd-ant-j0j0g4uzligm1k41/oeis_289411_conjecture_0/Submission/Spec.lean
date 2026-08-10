import FormalConjectures.Util.ProblemImports

open Nat
open scoped BigOperators

/--
A289411: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def A289411 (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

namespace OEIS289411

/-- digit sum base 10 -/
def ds (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- digit recursion for `ds` -/
lemma ds_rec (n : ℕ) : ds n = n % 10 + ds (n / 10) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [ds]
  · unfold ds
    rw [Nat.digits_def' (by norm_num) h]
    simp

/-- adding a small amount that doesn't cause a carry preserves the additive
structure of the digit sum -/
lemma ds_add_no_carry (m c : ℕ) (h : m % 10 + c < 10) : ds (m + c) = ds m + c := by
  rw [ds_rec (m + c), ds_rec m]
  have h1 : (m + c) % 10 = m % 10 + c := by omega
  have h2 : (m + c) / 10 = m / 10 := by omega
  rw [h1, h2]; ring

/-- the per-digit contribution of `5 * n`'s digit sum -/
def g (r : ℕ) : ℕ := 5 * (r % 2) + r / 2

/-- key recursion: multiplying by 5 contributes `g` per digit (no carries propagate) -/
lemma ds5_rec (n : ℕ) : ds (5 * n) = g (n % 10) + ds (5 * (n / 10)) := by
  set q := n / 10 with hq
  set r := n % 10 with hr
  have hr10 : r < 10 := by omega
  have hdec : 5 * n = 10 * (5 * q + r / 2) + 5 * (r % 2) := by omega
  have hlt : 5 * (r % 2) < 10 := by omega
  rw [hdec]
  have step1 : ds (10 * (5 * q + r / 2) + 5 * (r % 2))
      = 5 * (r % 2) + ds (5 * q + r / 2) := by
    rw [ds_rec (10 * (5 * q + r / 2) + 5 * (r % 2))]
    have e1 : (10 * (5 * q + r / 2) + 5 * (r % 2)) % 10 = 5 * (r % 2) := by omega
    have e2 : (10 * (5 * q + r / 2) + 5 * (r % 2)) / 10 = 5 * q + r / 2 := by omega
    rw [e1, e2]
  rw [step1]
  have hcarry : (5 * q) % 10 + r / 2 < 10 := by omega
  have step2 : ds (5 * q + r / 2) = ds (5 * q) + r / 2 :=
    ds_add_no_carry (5 * q) (r / 2) hcarry
  rw [step2]
  unfold g
  ring

/-- the signed quantity `ds(5n) - ds(n)` -/
def D (n : ℕ) : ℤ := (ds (5 * n) : ℤ) - (ds n : ℤ)

/-- per-digit contribution of `D` -/
def h (r : ℕ) : ℤ := (g r : ℤ) - (r : ℤ)

lemma D_zero : D 0 = 0 := by simp [D, ds]

/-- recursion for `D` -/
lemma D_rec (n : ℕ) : D n = h (n % 10) + D (n / 10) := by
  unfold D h
  rw [ds5_rec n, ds_rec n]
  push_cast
  ring

/-- complement property of `h`: `h(9-r) = -h(r)` -/
lemma h_compl (r : ℕ) (hr : r < 10) : h (9 - r) = - h r := by
  interval_cases r <;> decide

/-- the central antisymmetry: `D` is anti-symmetric under the `k`-digit
9's complement `j ↦ 10^k - 1 - j`. -/
lemma KEY (k : ℕ) : ∀ j, j < 10 ^ k → D (10 ^ k - 1 - j) = - D j := by
  induction k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    rw [D_zero]
    norm_num [D_zero]
  | succ k ih =>
    intro j hj
    set N := 10 ^ k with hN
    have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (by norm_num)
    have hj' : j < 10 * N := by rw [pow_succ] at hj; omega
    set q := j / 10 with hq
    set r := j % 10 with hr
    have hqN : q < N := by omega
    have hr10 : r < 10 := by omega
    have hcomp : 10 ^ (k + 1) - 1 - j = 10 * (N - 1 - q) + (9 - r) := by
      rw [pow_succ]; omega
    rw [hcomp]
    rw [D_rec (10 * (N - 1 - q) + (9 - r))]
    have e1 : (10 * (N - 1 - q) + (9 - r)) % 10 = 9 - r := by omega
    have e2 : (10 * (N - 1 - q) + (9 - r)) / 10 = N - 1 - q := by omega
    rw [e1, e2]
    rw [h_compl r hr10]
    have iheq : D (N - 1 - q) = - D q := ih q hqN
    rw [iheq]
    rw [D_rec j]
    ring

/-- partial sum of signs (the `ℤ`-valued version of `A289411` before `toNat`) -/
def P (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), Int.sign (D k)

lemma P_succ (n : ℕ) : P (n + 1) = P n + Int.sign (D (n + 1)) := by
  unfold P
  rw [Finset.sum_range_succ]

/-- symmetry of the partial sums around `m = 10^k/2 - 1` -/
lemma P_symm (k : ℕ) (hk : 0 < k) :
    ∀ i, i ≤ (10 ^ k / 2 - 1) →
      P ((10 ^ k / 2 - 1) + i) = P ((10 ^ k / 2 - 1) - i) := by
  set m := 10 ^ k / 2 - 1 with hm
  have heven : 2 * (10 ^ k / 2) = 10 ^ k := by
    have hdvd : 2 ∣ 10 ^ k := by
      have : (2 : ℕ) ∣ 10 := by norm_num
      exact Dvd.dvd.pow this (by omega)
    omega
  have hmval : 2 * m + 2 = 10 ^ k := by
    have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h1 : 1 ≤ 10 ^ k / 2 := by omega
    omega
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have hile : i ≤ m := by omega
    have ihq := ih hile
    have hL : P (m + (i + 1)) = P (m + i) + Int.sign (D (m + i + 1)) := by
      have he : m + (i + 1) = (m + i) + 1 := by ring
      rw [he, P_succ]
    have hmi1 : m - i = (m - (i + 1)) + 1 := by omega
    have hR : P (m - i) = P (m - (i + 1)) + Int.sign (D (m - i)) := by
      rw [hmi1, P_succ]
    have hcompl : 10 ^ k - 1 - (m - i) = m + i + 1 := by omega
    have hjlt : (m - i) < 10 ^ k := by omega
    have hkey := KEY k (m - i) hjlt
    rw [hcompl] at hkey
    have hsign : Int.sign (D (m + i + 1)) = - Int.sign (D (m - i)) := by
      rw [hkey, Int.sign_neg]
    rw [hL, ihq, hsign, hR]
    ring

/-- `A289411` equals the `toNat` of the `ℤ`-valued partial sum `P` -/
lemma A_eq_P (n : ℕ) : A289411 n = (P n).toNat := by
  unfold A289411 P D ds
  rfl

end OEIS289411

/--
this relation is conjectured to hold for any k > 0, where $m_k = 10^k/2 - 1$.
The relation is $a(m_k - i) = a(m_k + i)$ for $i = 0 \dots m_k$.
-/
theorem oeis_289411_conjecture_0 (k : ℕ) (hk : 0 < k) :
  let m_k : ℕ := (10 ^ k) / 2 - 1
  ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) :=
by
  intro m_k i hi
  show A289411 ((10 ^ k) / 2 - 1 - i) = A289411 ((10 ^ k) / 2 - 1 + i)
  rw [OEIS289411.A_eq_P, OEIS289411.A_eq_P]
  rw [OEIS289411.P_symm k hk i hi]
