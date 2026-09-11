import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

/- ## Section: V -/
namespace A357674Proof

/-- `V p n x` : the rational `x` is divisible by `p^n` in the `p`-adic sense. -/
@[irreducible] def V (p : ℕ) (n : ℕ) (x : ℚ) : Prop := padicNorm p x ≤ ((p : ℚ) ^ n)⁻¹

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime]

lemma p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
lemma p_pow_pos (n : ℕ) : (0 : ℚ) < (p : ℚ) ^ n := pow_pos p_pos n
lemma one_lt_p : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt

lemma V_zero (n : ℕ) : V p n (0 : ℚ) := by
  unfold V; rw [padicNorm.zero]; positivity

lemma V_mono {m n : ℕ} (h : m ≤ n) {x : ℚ} (hx : V p n x) : V p m x := by
  unfold V at *
  refine hx.trans ?_
  rw [inv_le_inv₀ (p_pow_pos n) (p_pow_pos m)]
  exact pow_le_pow_right₀ one_lt_p.le h

lemma V_add {n : ℕ} {x y : ℚ} (hx : V p n x) (hy : V p n y) : V p n (x + y) := by
  unfold V at *
  exact padicNorm.nonarchimedean.trans (max_le hx hy)

lemma V_neg {n : ℕ} {x : ℚ} (hx : V p n x) : V p n (-x) := by
  unfold V at *; rwa [padicNorm.neg]

lemma V_sub {n : ℕ} {x y : ℚ} (hx : V p n x) (hy : V p n y) : V p n (x - y) := by
  rw [sub_eq_add_neg]; exact V_add hx (V_neg hy)

lemma V_mul {m n : ℕ} {x y : ℚ} (hx : V p m x) (hy : V p n y) : V p (m + n) (x * y) := by
  unfold V at *
  rw [padicNorm.mul, pow_add, mul_inv]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (by positivity)

lemma V_mul0 {n : ℕ} {x y : ℚ} (hx : V p 0 x) (hy : V p n y) : V p n (x * y) := by
  simpa using V_mul hx hy

lemma V_mul0' {n : ℕ} {x y : ℚ} (hx : V p n x) (hy : V p 0 y) : V p n (x * y) := by
  simpa using V_mul hx hy

lemma V_pow {n : ℕ} {x : ℚ} (hx : V p n x) (k : ℕ) : V p (n * k) (x ^ k) := by
  induction k with
  | zero => unfold V; simp
  | succ k ih => rw [pow_succ, mul_add, mul_one]; exact V_mul ih hx

lemma V_sum {n : ℕ} {α : Type*} {s : Finset α} {f : α → ℚ}
    (h : ∀ i ∈ s, V p n (f i)) : V p n (∑ i ∈ s, f i) := by
  unfold V at *
  exact padicNorm.sum_le' h (by positivity)

lemma V_prod {α : Type*} {s : Finset α} {f : α → ℚ}
    (h : ∀ i ∈ s, V p 0 (f i)) : V p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold V; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact V_mul0 (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma V_int (z : ℤ) : V p 0 (z : ℚ) := by
  unfold V; simpa using padicNorm.of_int (p := p) z

lemma V_nat (m : ℕ) : V p 0 (m : ℚ) := by
  unfold V; simpa using padicNorm.of_nat (p := p) m

lemma V_one : V p 0 (1 : ℚ) := by simpa using V_nat (p := p) 1

lemma V_ofNat (m : ℕ) [m.AtLeastTwo] : V p 0 (OfNat.ofNat m : ℚ) := by
  simpa using V_nat (p := p) m

lemma V_p : V p 1 (p : ℚ) := by
  unfold V; rw [padicNorm.padicNorm_p hp.out.one_lt, pow_one]

lemma V_p_pow (n : ℕ) : V p n ((p : ℚ) ^ n) := by
  simpa using V_pow (V_p (p := p)) n

lemma V_p_mul {n : ℕ} {x : ℚ} (hx : V p n x) : V p (n + 1) ((p : ℚ) * x) := by
  rw [add_comm]; exact V_mul V_p hx

lemma V_p_pow_mul {n m : ℕ} {x : ℚ} (hx : V p n x) : V p (m + n) ((p : ℚ) ^ m * x) :=
  V_mul (V_p_pow m) hx

lemma padicNorm_nat_of_not_dvd {k : ℕ} (hk : ¬ p ∣ k) : padicNorm p (k : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff k).2 hk

lemma V_inv_nat {k : ℕ} (hk : ¬ p ∣ k) : V p 0 ((k : ℚ)⁻¹) := by
  unfold V
  rw [pow_zero, inv_one, ← one_div, padicNorm.div, padicNorm.one, padicNorm_nat_of_not_dvd hk]
  norm_num

lemma V_div_nat {n : ℕ} {x : ℚ} (hx : V p n x) {k : ℕ} (hk : ¬ p ∣ k) : V p n (x / k) := by
  rw [div_eq_mul_inv]; exact V_mul0' hx (V_inv_nat hk)

lemma V_inv_nat_pow {k : ℕ} (hk : ¬ p ∣ k) (s : ℕ) : V p 0 (((k : ℚ) ^ s)⁻¹) := by
  rw [← inv_pow]; simpa using V_pow (V_inv_nat (p := p) hk) s

lemma V_div_nat_pow {n : ℕ} {x : ℚ} (hx : V p n x) {k : ℕ} (hk : ¬ p ∣ k) (s : ℕ) :
    V p n (x / (k : ℚ) ^ s) := by
  rw [div_eq_mul_inv]; exact V_mul0' hx (V_inv_nat_pow hk s)

lemma V_int_iff (n : ℕ) (z : ℤ) : V p n (z : ℚ) ↔ (p : ℤ) ^ n ∣ z := by
  unfold V
  have := padicNorm.dvd_iff_norm_le (p := p) (n := n) (z := z)
  rw [zpow_neg, zpow_natCast] at this
  push_cast at this
  exact this.symm

lemma V_nat_iff (n : ℕ) (m : ℕ) : V p n (m : ℚ) ↔ p ^ n ∣ m := by
  have := V_int_iff (p := p) n (m : ℤ)
  push_cast at this
  rw [this]; exact Int.natCast_dvd_natCast

/-- Cancel a factor of `p`. -/
lemma V_of_p_mul {n : ℕ} {x : ℚ} (h : V p (n + 1) ((p : ℚ) * x)) : V p n x := by
  unfold V at *
  rw [padicNorm.mul, padicNorm.padicNorm_p hp.out.one_lt, pow_succ, mul_inv] at h
  have hp0 : (0 : ℚ) < (p : ℚ)⁻¹ := inv_pos.2 p_pos
  rw [mul_comm] at h
  exact le_of_mul_le_mul_right h hp0

lemma V_of_p_pow_mul {n m : ℕ} {x : ℚ} (h : V p (n + m) ((p : ℚ) ^ m * x)) : V p n x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    apply V_of_p_mul
    have : (p : ℚ) * ((p : ℚ) ^ m * x) = (p : ℚ) ^ (m + 1) * x := by ring
    rw [this]
    have e : n + m + 1 = n + (m + 1) := by ring
    rw [e]; exact h

/-- Multiplication by a `p`-adic unit does not change the valuation bound. -/
lemma V_unit_mul_iff {n : ℕ} {u x : ℚ} (hu : padicNorm p u = 1) : V p n (u * x) ↔ V p n x := by
  unfold V; rw [padicNorm.mul, hu, one_mul]

lemma V_unit_div_iff {n : ℕ} {u x : ℚ} (hu : padicNorm p u = 1) : V p n (x / u) ↔ V p n x := by
  unfold V; rw [padicNorm.div, hu, div_one]

lemma V_nat_div_iff {n : ℕ} {x : ℚ} {k : ℕ} (hk : ¬ p ∣ k) : V p n (x / k) ↔ V p n x :=
  V_unit_div_iff (padicNorm_nat_of_not_dvd hk)

lemma V_nat_mul_iff {n : ℕ} {x : ℚ} {k : ℕ} (hk : ¬ p ∣ k) : V p n ((k : ℚ) * x) ↔ V p n x :=
  V_unit_mul_iff (padicNorm_nat_of_not_dvd hk)

lemma V_ofNat_mul_iff {n : ℕ} {x : ℚ} {k : ℕ} [k.AtLeastTwo] (hk : ¬ p ∣ k) :
    V p n ((OfNat.ofNat k : ℚ) * x) ↔ V p n x := by
  have := V_nat_mul_iff (p := p) (n := n) (x := x) hk
  simpa using this

lemma V_ofNat_div_iff {n : ℕ} {x : ℚ} {k : ℕ} [k.AtLeastTwo] (hk : ¬ p ∣ k) :
    V p n (x / (OfNat.ofNat k : ℚ)) ↔ V p n x := by
  have := V_nat_div_iff (p := p) (n := n) (x := x) hk
  simpa using this

/-- A p-integral element: convenient form for `1/k`. -/
lemma V_one_div_nat {k : ℕ} (hk : ¬ p ∣ k) : V p 0 (1 / (k : ℚ)) := by
  rw [one_div]; exact V_inv_nat hk

lemma not_dvd_of_lt {k : ℕ} (h0 : 0 < k) (h : k < p) : ¬ p ∣ k := fun hd =>
  absurd (Nat.le_of_dvd h0 hd) (not_le.2 h)

lemma not_dvd_succ_of_lt {k : ℕ} (h : k + 1 < p) : ¬ p ∣ k + 1 :=
  not_dvd_of_lt (Nat.succ_pos k) h

/-- congruence-style helper: `V n (a - b)` and `V n (b - c)` give `V n (a - c)`. -/
lemma V_sub_trans {n : ℕ} {a b c : ℚ} (h1 : V p n (a - b)) (h2 : V p n (b - c)) : V p n (a - c) := by
  have := V_add h1 h2; rwa [sub_add_sub_cancel] at this

lemma V_congr_mul {n : ℕ} {a b c d : ℚ} (hab : V p n (a - b)) (hcd : V p n (c - d))
    (hb : V p 0 b) (hc : V p 0 c) : V p n (a * c - b * d) := by
  have : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [this]; exact V_add (V_mul0' hab hc) (V_mul0 hb hcd)

lemma V_of_eq {n : ℕ} {a b : ℚ} (h : a = b) (hb : V p n b) : V p n a := h ▸ hb

end A357674Proof

/- ## Section: Harm -/
namespace A357674Proof

/- ### Harmonic-type prefix sums -/

/-- `H1 n = ∑_{k=1}^{n} 1/k` -/
def H1 (n : ℕ) : ℚ := ∑ k ∈ range n, 1 / ((k : ℚ) + 1)
def H2 (n : ℕ) : ℚ := ∑ k ∈ range n, 1 / ((k : ℚ) + 1) ^ 2
def H3 (n : ℕ) : ℚ := ∑ k ∈ range n, 1 / ((k : ℚ) + 1) ^ 3
def H4 (n : ℕ) : ℚ := ∑ k ∈ range n, 1 / ((k : ℚ) + 1) ^ 4
/-- `E2 n = ∑_{j<k≤n} 1/(jk)` -/
def E2 (n : ℕ) : ℚ := ∑ k ∈ range n, H1 k / ((k : ℚ) + 1)
def E3 (n : ℕ) : ℚ := ∑ k ∈ range n, E2 k / ((k : ℚ) + 1)
def E4 (n : ℕ) : ℚ := ∑ k ∈ range n, E3 k / ((k : ℚ) + 1)
def H12 (n : ℕ) : ℚ := ∑ k ∈ range n, H1 k / ((k : ℚ) + 1) ^ 2
def H13 (n : ℕ) : ℚ := ∑ k ∈ range n, H1 k / ((k : ℚ) + 1) ^ 3
def H21 (n : ℕ) : ℚ := ∑ k ∈ range n, H2 k / ((k : ℚ) + 1)
def H22 (n : ℕ) : ℚ := ∑ k ∈ range n, H2 k / ((k : ℚ) + 1) ^ 2
def H31 (n : ℕ) : ℚ := ∑ k ∈ range n, H3 k / ((k : ℚ) + 1)
def H112 (n : ℕ) : ℚ := ∑ k ∈ range n, E2 k / ((k : ℚ) + 1) ^ 2
def H211 (n : ℕ) : ℚ := ∑ k ∈ range n, H21 k / ((k : ℚ) + 1)
def H121 (n : ℕ) : ℚ := ∑ k ∈ range n, H12 k / ((k : ℚ) + 1)

@[simp] lemma H1_zero : H1 0 = 0 := by simp [H1]
@[simp] lemma H2_zero : H2 0 = 0 := by simp [H2]
@[simp] lemma H3_zero : H3 0 = 0 := by simp [H3]
@[simp] lemma H4_zero : H4 0 = 0 := by simp [H4]
@[simp] lemma E2_zero : E2 0 = 0 := by simp [E2]
@[simp] lemma E3_zero : E3 0 = 0 := by simp [E3]
@[simp] lemma E4_zero : E4 0 = 0 := by simp [E4]
@[simp] lemma H12_zero : H12 0 = 0 := by simp [H12]
@[simp] lemma H13_zero : H13 0 = 0 := by simp [H13]
@[simp] lemma H21_zero : H21 0 = 0 := by simp [H21]
@[simp] lemma H22_zero : H22 0 = 0 := by simp [H22]
@[simp] lemma H31_zero : H31 0 = 0 := by simp [H31]
@[simp] lemma H112_zero : H112 0 = 0 := by simp [H112]
@[simp] lemma H211_zero : H211 0 = 0 := by simp [H211]
@[simp] lemma H121_zero : H121 0 = 0 := by simp [H121]

lemma H1_succ (n : ℕ) : H1 (n + 1) = H1 n + 1 / ((n : ℚ) + 1) := by simp [H1, sum_range_succ]
lemma H2_succ (n : ℕ) : H2 (n + 1) = H2 n + 1 / ((n : ℚ) + 1) ^ 2 := by simp [H2, sum_range_succ]
lemma H3_succ (n : ℕ) : H3 (n + 1) = H3 n + 1 / ((n : ℚ) + 1) ^ 3 := by simp [H3, sum_range_succ]
lemma H4_succ (n : ℕ) : H4 (n + 1) = H4 n + 1 / ((n : ℚ) + 1) ^ 4 := by simp [H4, sum_range_succ]
lemma E2_succ (n : ℕ) : E2 (n + 1) = E2 n + H1 n / ((n : ℚ) + 1) := by simp [E2, sum_range_succ]
lemma E3_succ (n : ℕ) : E3 (n + 1) = E3 n + E2 n / ((n : ℚ) + 1) := by simp [E3, sum_range_succ]
lemma E4_succ (n : ℕ) : E4 (n + 1) = E4 n + E3 n / ((n : ℚ) + 1) := by simp [E4, sum_range_succ]
lemma H12_succ (n : ℕ) : H12 (n + 1) = H12 n + H1 n / ((n : ℚ) + 1) ^ 2 := by
  simp [H12, sum_range_succ]
lemma H13_succ (n : ℕ) : H13 (n + 1) = H13 n + H1 n / ((n : ℚ) + 1) ^ 3 := by
  simp [H13, sum_range_succ]
lemma H21_succ (n : ℕ) : H21 (n + 1) = H21 n + H2 n / ((n : ℚ) + 1) := by
  simp [H21, sum_range_succ]
lemma H22_succ (n : ℕ) : H22 (n + 1) = H22 n + H2 n / ((n : ℚ) + 1) ^ 2 := by
  simp [H22, sum_range_succ]
lemma H31_succ (n : ℕ) : H31 (n + 1) = H31 n + H3 n / ((n : ℚ) + 1) := by
  simp [H31, sum_range_succ]
lemma H112_succ (n : ℕ) : H112 (n + 1) = H112 n + E2 n / ((n : ℚ) + 1) ^ 2 := by
  simp [H112, sum_range_succ]
lemma H211_succ (n : ℕ) : H211 (n + 1) = H211 n + H21 n / ((n : ℚ) + 1) := by
  simp [H211, sum_range_succ]
lemma H121_succ (n : ℕ) : H121 (n + 1) = H121 n + H12 n / ((n : ℚ) + 1) := by
  simp [H121, sum_range_succ]

lemma nat_succ_ne_zero (n : ℕ) : ((n : ℚ) + 1) ≠ 0 := by positivity

/- ### Newton / stuffle identities -/

/-- `H1^2 = 2 E2 + H2` -/
lemma newton2 (n : ℕ) : H1 n ^ 2 = 2 * E2 n + H2 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, E2_succ, H2_succ]
    have := nat_succ_ne_zero n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 2 * ih

/-- `6 E3 = H1^3 - 3 H1 H2 + 2 H3` -/
lemma newton3 (n : ℕ) : 6 * E3 n = H1 n ^ 3 - 3 * H1 n * H2 n + 2 * H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, E3_succ, H2_succ, H3_succ]
    have := nat_succ_ne_zero n
    have h2 := newton2 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 3 * ih - 3 * ((n : ℚ) + 1) ^ 2 * h2

/-- `24 E4 = H1^4 - 6 H1^2 H2 + 3 H2^2 + 8 H1 H3 - 6 H4` -/
lemma newton4 (n : ℕ) : 24 * E4 n =
    H1 n ^ 4 - 6 * H1 n ^ 2 * H2 n + 3 * H2 n ^ 2 + 8 * H1 n * H3 n - 6 * H4 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, E4_succ, H2_succ, H3_succ, H4_succ]
    have := nat_succ_ne_zero n
    have h3 := newton3 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 4 * ih + 4 * ((n : ℚ) + 1) ^ 3 * h3

/-- `H1 * H2 = H12 + H21 + H3` -/
lemma stuffle12 (n : ℕ) : H1 n * H2 n = H12 n + H21 n + H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, H2_succ, H12_succ, H21_succ, H3_succ]
    have := nat_succ_ne_zero n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 3 * ih

/-- `H2^2 = 2 H22 + H4` -/
lemma stuffle22 (n : ℕ) : H2 n ^ 2 = 2 * H22 n + H4 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H2_succ, H22_succ, H4_succ]
    have := nat_succ_ne_zero n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 4 * ih

/-- `H1 * H3 = H13 + H31 + H4` -/
lemma stuffle13 (n : ℕ) : H1 n * H3 n = H13 n + H31 n + H4 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, H3_succ, H13_succ, H31_succ, H4_succ]
    have := nat_succ_ne_zero n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 4 * ih

/-- `H1 * E2 = 3 E3 + H21 + H12` -/
lemma stuffle1_11 (n : ℕ) : H1 n * E2 n = 3 * E3 n + H21 n + H12 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H1_succ, E2_succ, E3_succ, H21_succ, H12_succ]
    have := nat_succ_ne_zero n
    have h2 := newton2 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 2 * ih + ((n : ℚ) + 1) * h2

/-- `H2 * E2 = H211 + H121 + H112 + H31 + H13` -/
lemma stuffle2_11 (n : ℕ) : H2 n * E2 n = H211 n + H121 n + H112 n + H31 n + H13 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H2_succ, E2_succ, H211_succ, H121_succ, H112_succ, H31_succ, H13_succ]
    have := nat_succ_ne_zero n
    have h := stuffle12 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 3 * ih + ((n : ℚ) + 1) ^ 2 * h

/- ### Sums with inclusive harmonic numbers (needed for the binomial identities) -/

lemma sum_H1_succ_div (n : ℕ) :
    ∑ k ∈ range n, H1 (k + 1) / ((k : ℚ) + 1) = E2 n + H2 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, E2_succ, H2_succ, H1_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

lemma sum_H1_succ_div_sq (n : ℕ) :
    ∑ k ∈ range n, H1 (k + 1) / ((k : ℚ) + 1) ^ 2 = H12 n + H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, H12_succ, H3_succ, H1_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

lemma sum_H1_succ_div_cube (n : ℕ) :
    ∑ k ∈ range n, H1 (k + 1) / ((k : ℚ) + 1) ^ 3 = H13 n + H4 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, H13_succ, H4_succ, H1_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

lemma sum_E2_succ_div_sq (n : ℕ) :
    ∑ k ∈ range n, E2 (k + 1) / ((k : ℚ) + 1) ^ 2 = H112 n + H13 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, H112_succ, H13_succ, E2_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

lemma sum_H1_succ_sq_div (n : ℕ) :
    ∑ k ∈ range n, H1 (k + 1) ^ 2 / ((k : ℚ) + 1) = 2 * E3 n + H21 n + 2 * H12 n + H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, E3_succ, H21_succ, H12_succ, H3_succ, H1_succ]
    have := nat_succ_ne_zero n
    have h2 := newton2 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 2 * h2

lemma sum_E2_H1_succ_div (n : ℕ) :
    ∑ k ∈ range n, E2 (k + 1) * H1 (k + 1) / ((k : ℚ) + 1) =
      3 * E4 n + H211 n + H121 n + 3 * H112 n + H22 n + H13 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, E4_succ, H211_succ, H121_succ, H112_succ, H22_succ, H13_succ,
      E2_succ, H1_succ]
    have := nat_succ_ne_zero n
    have h2 := newton2 n
    have h := stuffle1_11 n
    field_simp
    linear_combination ((n : ℚ) + 1) ^ 2 * h + ((n : ℚ) + 1) * h2

/-- Partial sums of `H_k / k`: `∑_{j<m} H1 (j+1)/(j+1) = E2 m + H2 m`; then summing again. -/
lemma sum_E2_add_H2_succ_div (n : ℕ) :
    ∑ k ∈ range n, (E2 (k + 1) + H2 (k + 1)) / ((k : ℚ) + 1) = E3 n + H12 n + H21 n + H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, E3_succ, H12_succ, H21_succ, H3_succ, E2_succ, H2_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

end A357674Proof

/- ## Section: Binom -/
namespace A357674Proof

/-- Pascal step for alternating binomial transforms. -/
lemma pascal_alt (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) * f k =
      ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * f k +
        ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * f k := by
  have h : ∀ k, ((n + 1).choose (k + 1) : ℚ) = (n.choose k : ℚ) + (n.choose (k + 1) : ℚ) := by
    intro k; rw [Nat.choose_succ_succ]; push_cast; ring
  have h2 : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) * f k =
      (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * f k + (-1 : ℚ) ^ k * (n.choose k : ℚ) * f k := by
    intro k _; rw [h]; ring
  rw [sum_congr rfl h2, sum_add_distrib,
    sum_range_succ (fun k => (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * f k), Nat.choose_succ_self]
  simp

lemma alt_sum_choose (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) = 0 := by
  have := Int.alternating_sum_range_choose_of_ne hn
  have h2 : ((∑ m ∈ range (n + 1), ((-1 : ℤ) ^ m * (n.choose m : ℤ)) : ℤ) : ℚ) = 0 := by
    rw [this]; simp
  push_cast at h2
  exact h2

lemma alt_sum_choose_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) = 1 := by
  have h := alt_sum_choose (n + 1) (Nat.succ_ne_zero n)
  rw [sum_range_succ'] at h
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h
  have : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℚ) =
      -∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) := by
    rw [← sum_neg_distrib]; congr 1; ext k; ring
  rw [this] at h
  linarith

lemma choose_div_succ (n k : ℕ) :
    (n.choose k : ℚ) / ((k : ℚ) + 1) = ((n + 1).choose (k + 1) : ℚ) / ((n : ℚ) + 1) := by
  have h := Nat.add_one_mul_choose_eq n k
  have h' : ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast h
  rw [div_eq_div_iff (nat_succ_ne_zero k) (nat_succ_ne_zero n)]
  linear_combination h'

/-- L1 -/
lemma alt_sum_choose_div (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) = 1 / ((n : ℚ) + 1) := by
  have : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) =
      (-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) * (1 / ((n : ℚ) + 1)) := by
    intro k _
    rw [mul_div_assoc, choose_div_succ]; ring
  rw [sum_congr rfl this, ← sum_mul, alt_sum_choose_succ, one_mul]

/-- L2 -/
lemma alt_sum_choose_succ_div (n : ℕ) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) / ((k : ℚ) + 1) = H1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP := pascal_alt n (fun k => 1 / ((k : ℚ) + 1))
    simp only [mul_one_div] at hP
    rw [hP, ih, H1_succ]
    congr 1
    have := alt_sum_choose_div n
    simpa [mul_one_div] using this

/-- L3 -/
lemma alt_sum_choose_succ_H1 (n : ℕ) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * H1 (k + 1) = 1 / (n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pascal_alt n (fun k => H1 (k + 1)), ih]
    have h1 : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 (k + 1) =
        ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 k +
          ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) := by
      rw [← sum_add_distrib]; congr 1; ext k; rw [H1_succ]; ring
    have h2 : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 k =
        - ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * H1 (k + 1) := by
      rw [sum_range_succ', H1_zero, mul_zero, add_zero, ← sum_neg_distrib]
      congr 1; ext k; ring
    rw [h1, h2, ih, alt_sum_choose_div]
    push_cast; ring

/-- L4 -/
lemma alt_sum_choose_div_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 2 =
      H1 (n + 1) / ((n : ℚ) + 1) := by
  have : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 2 =
      ((-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) / ((k : ℚ) + 1)) * (1 / ((n : ℚ) + 1)) := by
    intro k _
    have e : (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 2 =
        (-1 : ℚ) ^ k * ((n.choose k : ℚ) / ((k : ℚ) + 1)) / ((k : ℚ) + 1) := by
      have hk := nat_succ_ne_zero k
      field_simp
    rw [e, choose_div_succ]; ring
  rw [sum_congr rfl this, ← sum_mul, alt_sum_choose_succ_div (n + 1)]
  ring

/-- B1 : `∑_{k=1}^n (-1)^(k-1) C(n,k)/k^2 = ∑_{k=1}^n H_k/k` -/
lemma binom_B1 (n : ℕ) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) / ((k : ℚ) + 1) ^ 2 =
      ∑ k ∈ range n, H1 (k + 1) / ((k : ℚ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP := pascal_alt n (fun k => 1 / ((k : ℚ) + 1) ^ 2)
    simp only [mul_one_div] at hP
    rw [hP, ih, sum_range_succ (fun k => H1 (k + 1) / ((k : ℚ) + 1))]
    congr 1
    have := alt_sum_choose_div_sq n
    simpa [mul_one_div] using this

/-- L5 -/
lemma alt_sum_choose_H1_div (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 (k + 1) / ((k : ℚ) + 1) =
      1 / ((n : ℚ) + 1) ^ 2 := by
  have : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 (k + 1) / ((k : ℚ) + 1) =
      ((-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) * H1 (k + 1)) * (1 / ((n : ℚ) + 1)) := by
    intro k _
    have e : (-1 : ℚ) ^ k * (n.choose k : ℚ) * H1 (k + 1) / ((k : ℚ) + 1) =
        (-1 : ℚ) ^ k * ((n.choose k : ℚ) / ((k : ℚ) + 1)) * H1 (k + 1) := by ring
    rw [e, choose_div_succ]; ring
  rw [sum_congr rfl this, ← sum_mul, alt_sum_choose_succ_H1 (n + 1)]
  push_cast
  have := nat_succ_ne_zero n
  field_simp

/-- B2 : `∑_{k=1}^n (-1)^(k-1) C(n,k) H_k/k = H_n^{(2)}` -/
lemma binom_B2 (n : ℕ) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * H1 (k + 1) / ((k : ℚ) + 1) = H2 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP := pascal_alt n (fun k => H1 (k + 1) / ((k : ℚ) + 1))
    simp only [← mul_div_assoc] at hP
    rw [hP, ih, H2_succ]
    congr 1
    exact alt_sum_choose_H1_div n

/-- L6 -/
lemma alt_sum_choose_div_cube (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 3 =
      (E2 (n + 1) + H2 (n + 1)) / ((n : ℚ) + 1) := by
  have : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 3 =
      ((-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) / ((k : ℚ) + 1) ^ 2) * (1 / ((n : ℚ) + 1)) := by
    intro k _
    have e : (-1 : ℚ) ^ k * (n.choose k : ℚ) / ((k : ℚ) + 1) ^ 3 =
        (-1 : ℚ) ^ k * ((n.choose k : ℚ) / ((k : ℚ) + 1)) / ((k : ℚ) + 1) ^ 2 := by
      have hk := nat_succ_ne_zero k
      field_simp
    rw [e, choose_div_succ]; ring
  rw [sum_congr rfl this, ← sum_mul, binom_B1 (n + 1), sum_H1_succ_div]
  ring

/-- B3 : `∑_{k=1}^n (-1)^(k-1) C(n,k)/k^3 = ∑_{k=1}^n (∑_{j≤k} H_j/j)/k` -/
lemma binom_B3 (n : ℕ) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) / ((k : ℚ) + 1) ^ 3 =
      E3 n + H12 n + H21 n + H3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP := pascal_alt n (fun k => 1 / ((k : ℚ) + 1) ^ 3)
    simp only [mul_one_div] at hP
    rw [hP, ih, E3_succ, H12_succ, H21_succ, H3_succ]
    have := alt_sum_choose_div_cube n
    rw [this, E2_succ, H2_succ]
    have := nat_succ_ne_zero n
    field_simp
    ring

end A357674Proof

/- ## Section: Padic1 -/
namespace A357674Proof

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime]

/- ### p-integrality of the harmonic sums -/

lemma V_div_succ_pow {n : ℕ} {x : ℚ} (hx : V p n x) {k : ℕ} (hk : k + 1 < p) (s : ℕ) :
    V p n (x / ((k : ℚ) + 1) ^ s) := by
  have := V_div_nat_pow hx (not_dvd_succ_of_lt hk) s
  push_cast at this; exact this

lemma V_div_succ {n : ℕ} {x : ℚ} (hx : V p n x) {k : ℕ} (hk : k + 1 < p) :
    V p n (x / ((k : ℚ) + 1)) := by
  simpa using V_div_succ_pow hx hk 1

lemma V_one_div_succ_pow {k : ℕ} (hk : k + 1 < p) (s : ℕ) : V p 0 (1 / ((k : ℚ) + 1) ^ s) :=
  V_div_succ_pow V_one hk s

lemma V_one_div_succ {k : ℕ} (hk : k + 1 < p) : V p 0 (1 / ((k : ℚ) + 1)) :=
  V_div_succ V_one hk

/-- generic: a prefix sum of p-integral terms divided by `(k+1)^s` is p-integral. -/
lemma V0_sum_div {m : ℕ} (hm : m ≤ p - 1) {g : ℕ → ℚ} (hg : ∀ k, k < m → V p 0 (g k)) (s : ℕ) :
    V p 0 (∑ k ∈ range m, g k / ((k : ℚ) + 1) ^ s) := by
  apply V_sum
  intro k hk
  rw [mem_range] at hk
  have hk' : k + 1 < p := by have := hp.out.pos; omega
  exact V_div_succ_pow (hg k hk) hk' s

lemma V0_H1 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H1 m) := by
  unfold H1; simpa using V0_sum_div hm (g := fun _ => 1) (fun _ _ => V_one) 1
lemma V0_H2 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H2 m) := by
  unfold H2; exact V0_sum_div hm (g := fun _ => 1) (fun _ _ => V_one) 2
lemma V0_H3 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H3 m) := by
  unfold H3; exact V0_sum_div hm (g := fun _ => 1) (fun _ _ => V_one) 3
lemma V0_H4 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H4 m) := by
  unfold H4; exact V0_sum_div hm (g := fun _ => 1) (fun _ _ => V_one) 4
lemma V0_E2 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (E2 m) := by
  unfold E2; simpa using V0_sum_div hm (g := H1) (fun k hk => V0_H1 (by omega)) 1
lemma V0_E3 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (E3 m) := by
  unfold E3; simpa using V0_sum_div hm (g := E2) (fun k hk => V0_E2 (by omega)) 1
lemma V0_E4 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (E4 m) := by
  unfold E4; simpa using V0_sum_div hm (g := E3) (fun k hk => V0_E3 (by omega)) 1
lemma V0_H12 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H12 m) := by
  unfold H12; exact V0_sum_div hm (g := H1) (fun k hk => V0_H1 (by omega)) 2
lemma V0_H13 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H13 m) := by
  unfold H13; exact V0_sum_div hm (g := H1) (fun k hk => V0_H1 (by omega)) 3
lemma V0_H21 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H21 m) := by
  unfold H21; simpa using V0_sum_div hm (g := H2) (fun k hk => V0_H2 (by omega)) 1
lemma V0_H22 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H22 m) := by
  unfold H22; exact V0_sum_div hm (g := H2) (fun k hk => V0_H2 (by omega)) 2
lemma V0_H31 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H31 m) := by
  unfold H31; simpa using V0_sum_div hm (g := H3) (fun k hk => V0_H3 (by omega)) 1
lemma V0_H112 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H112 m) := by
  unfold H112; exact V0_sum_div hm (g := E2) (fun k hk => V0_E2 (by omega)) 2
lemma V0_H211 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H211 m) := by
  unfold H211; simpa using V0_sum_div hm (g := H21) (fun k hk => V0_H21 (by omega)) 1
lemma V0_H121 {m : ℕ} (hm : m ≤ p - 1) : V p 0 (H121 m) := by
  unfold H121; simpa using V0_sum_div hm (g := H12) (fun k hk => V0_H12 (by omega)) 1

/- ### Power sums and `H2 ≡ H4 ≡ 0 (mod p)` -/

lemma sum_range_sq (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_pow4 (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 4 =
      (n : ℚ) * (n - 1) * (2 * n - 1) * (3 * (n : ℚ) ^ 2 - 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- the inverse of `k` modulo `p`, as a natural number -/
def pinv (p : ℕ) (k : ℕ) : ℕ := ((k : ZMod p)⁻¹).val

lemma pinv_mem {k : ℕ} (hk : k ∈ Ico 1 p) : pinv p k ∈ Ico 1 p := by
  rw [mem_Ico] at hk ⊢
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨?_, ZMod.val_lt _⟩
  have h0 : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_of_lt (by omega) hk.2
  have : ((k : ZMod p)⁻¹) ≠ 0 := inv_ne_zero h0
  have : ((k : ZMod p)⁻¹).val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  unfold pinv; omega

lemma pinv_pinv {k : ℕ} (hk : k ∈ Ico 1 p) : pinv p (pinv p k) = k := by
  rw [mem_Ico] at hk
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold pinv
  rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_cast_of_lt hk.2]

lemma pinv_mul_congr {k : ℕ} (hk : k ∈ Ico 1 p) : (p : ℤ) ∣ ((k : ℤ) * (pinv p k : ℤ) - 1) := by
  rw [mem_Ico] at hk
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  unfold pinv
  rw [ZMod.natCast_zmod_val]
  have h0 : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_of_lt (by omega) hk.2
  rw [mul_inv_cancel₀ h0]; ring

lemma V_congr_pow {n : ℕ} {a b : ℚ} (hab : V p n (a - b)) (ha : V p 0 a) (hb : V p 0 b) (s : ℕ) :
    V p n (a ^ s - b ^ s) := by
  induction s with
  | zero => simpa using V_zero n
  | succ s ih =>
    rw [pow_succ, pow_succ]
    exact V_congr_mul ih hab (V_pow hb s |> fun h => by simpa using h) ha

lemma V_inv_sub_pinv {k : ℕ} (hk : k ∈ Ico 1 p) : V p 1 (1 / (k : ℚ) - (pinv p k : ℚ)) := by
  have hk' := hk
  rw [mem_Ico] at hk'
  have hkne : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have e : 1 / (k : ℚ) - (pinv p k : ℚ) = -(((k : ℤ) * (pinv p k : ℤ) - 1 : ℤ) : ℚ) / (k : ℚ) := by
    push_cast; field_simp; ring
  rw [e]
  apply V_div_nat _ (not_dvd_of_lt (by omega) hk'.2)
  apply V_neg
  rw [V_int_iff]
  simpa using pinv_mul_congr hk

lemma sum_pinv_pow (s : ℕ) :
    ∑ k ∈ Ico 1 p, ((pinv p k : ℕ) : ℚ) ^ s = ∑ k ∈ Ico 1 p, (k : ℚ) ^ s := by
  apply sum_nbij' (pinv p) (pinv p)
  · intro a ha; exact pinv_mem ha
  · intro a ha; exact pinv_mem ha
  · intro a ha; exact pinv_pinv ha
  · intro a ha; exact pinv_pinv ha
  · intro a ha; rfl

/-- `∑_{k=1}^{p-1} 1/k^s ≡ ∑_{k=1}^{p-1} k^s (mod p)` -/
lemma sum_inv_pow_congr_pow (s : ℕ) :
    V p 1 (∑ k ∈ Ico 1 p, 1 / (k : ℚ) ^ s - ∑ k ∈ Ico 1 p, (k : ℚ) ^ s) := by
  rw [← sum_pinv_pow, ← sum_sub_distrib]
  apply V_sum
  intro k hk
  have hk' := hk
  rw [mem_Ico] at hk'
  rw [← one_div_pow]
  exact V_congr_pow (V_inv_sub_pinv hk) (V_one_div_nat (not_dvd_of_lt (by omega) hk'.2)) (V_nat _) s

lemma Hs_eq_sum_Ico (s : ℕ) (hp1 : 1 ≤ p) :
    ∑ k ∈ range (p - 1), 1 / ((k : ℚ) + 1) ^ s = ∑ k ∈ Ico 1 p, 1 / (k : ℚ) ^ s := by
  rw [sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro k _
  push_cast; ring

lemma sum_Ico_pow_eq_range (s : ℕ) (hs : s ≠ 0) :
    ∑ k ∈ Ico 1 p, (k : ℚ) ^ s = ∑ k ∈ range p, (k : ℚ) ^ s := by
  have := hp.out.pos
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot this]
  simp [zero_pow hs]

lemma V1_H2 (hp5 : 5 ≤ p) : V p 1 (H2 (p - 1)) := by
  unfold H2
  rw [Hs_eq_sum_Ico 2 hp.out.one_lt.le]
  have h1 := sum_inv_pow_congr_pow (p := p) 2
  have h2 : V p 1 (∑ k ∈ Ico 1 p, (k : ℚ) ^ 2) := by
    rw [sum_Ico_pow_eq_range 2 (by norm_num), sum_range_sq]
    have e : (p : ℚ) * (p - 1) * (2 * p - 1) / 6 =
        (p : ℚ) * ((((p : ℤ) - 1) * (2 * p - 1) : ℤ) : ℚ) / (6 : ℕ) := by push_cast; ring
    rw [e]
    apply V_div_nat _ (fun h => by
      have hle := Nat.le_of_dvd (by norm_num) h
      have hpr := hp.out
      interval_cases p <;> revert h hpr <;> norm_num)
    exact V_p_mul (V_int _)
  have := V_add h1 h2
  simpa using this

lemma V1_H4 (hp7 : 7 ≤ p) : V p 1 (H4 (p - 1)) := by
  unfold H4
  rw [Hs_eq_sum_Ico 4 hp.out.one_lt.le]
  have h1 := sum_inv_pow_congr_pow (p := p) 4
  have h2 : V p 1 (∑ k ∈ Ico 1 p, (k : ℚ) ^ 4) := by
    rw [sum_Ico_pow_eq_range 4 (by norm_num), sum_range_pow4]
    have e : (p : ℚ) * (p - 1) * (2 * p - 1) * (3 * (p : ℚ) ^ 2 - 3 * p - 1) / 30 =
        (p : ℚ) * ((((p : ℤ) - 1) * (2 * p - 1) * (3 * (p : ℤ) ^ 2 - 3 * p - 1) : ℤ) : ℚ) /
          (30 : ℕ) := by push_cast; ring
    rw [e]
    apply V_div_nat _ (fun h => by
      have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) h
      have hpr := hp.out
      interval_cases p <;> revert h hpr <;> norm_num)
    exact V_p_mul (V_int _)
  have := V_add h1 h2
  simpa using this

/- ### Reflection `k ↦ p - k` -/

/-- reflect a sum over `1..p-1`. -/
lemma sum_reflect_succ (f : ℕ → ℚ) :
    ∑ j ∈ range (p - 1), f (p - (j + 1)) = ∑ j ∈ range (p - 1), f (j + 1) := by
  have := sum_range_reflect (fun i => f (i + 1)) (p - 1)
  simp only at this
  rw [← this]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  congr 1; omega

lemma cast_p_sub {j : ℕ} (hj : j + 1 < p) : ((p - (j + 1) : ℕ) : ℚ) = (p : ℚ) - ((j : ℚ) + 1) := by
  rw [Nat.cast_sub hj.le]; push_cast; ring

lemma not_dvd_p_sub {j : ℕ} (hj : j + 1 < p) : ¬ p ∣ (p - (j + 1)) :=
  not_dvd_of_lt (by omega) (by omega)

/-- `2 H1 + p H2 ≡ 0 (mod p^4)` given `H3 ≡ 0 (mod p^2)` and `H4 ≡ 0 (mod p)`. -/
lemma V4_H1 (h3 : V p 2 (H3 (p - 1))) (h4 : V p 1 (H4 (p - 1))) :
    V p 4 (2 * H1 (p - 1) + (p : ℚ) * H2 (p - 1)) := by
  -- 2 H1 = ∑ (1/k + 1/(p-k))
  have hrefl : ∑ j ∈ range (p - 1), 1 / ((p - (j + 1) : ℕ) : ℚ) = H1 (p - 1) := by
    unfold H1
    have := sum_reflect_succ (p := p) (fun i => 1 / (i : ℚ))
    rw [this]; apply sum_congr rfl; intro j _; push_cast; ring
  have key : ∀ j ∈ range (p - 1),
      1 / ((j : ℚ) + 1) + 1 / ((p - (j + 1) : ℕ) : ℚ) =
        -(p : ℚ) / ((j : ℚ) + 1) ^ 2 - (p : ℚ) ^ 2 / ((j : ℚ) + 1) ^ 3
          - (p : ℚ) ^ 3 / ((j : ℚ) + 1) ^ 4
          + (p : ℚ) ^ 4 * (1 / (((j : ℚ) + 1) ^ 4 * ((p - (j + 1) : ℕ) : ℚ))) := by
    intro j hj
    rw [mem_range] at hj
    have hj' : j + 1 < p := by omega
    rw [cast_p_sub hj']
    have h1 : ((j : ℚ) + 1) ≠ 0 := nat_succ_ne_zero j
    have h2 : (p : ℚ) - ((j : ℚ) + 1) ≠ 0 := by
      have : ((j : ℚ) + 1) < p := by exact_mod_cast hj'
      linarith
    field_simp
    ring
  have e : 2 * H1 (p - 1) + (p : ℚ) * H2 (p - 1) =
      -(p : ℚ) ^ 2 * H3 (p - 1) - (p : ℚ) ^ 3 * H4 (p - 1) +
        (p : ℚ) ^ 4 * ∑ j ∈ range (p - 1), 1 / (((j : ℚ) + 1) ^ 4 * ((p - (j + 1) : ℕ) : ℚ)) := by
    have : 2 * H1 (p - 1) = ∑ j ∈ range (p - 1),
        (1 / ((j : ℚ) + 1) + 1 / ((p - (j + 1) : ℕ) : ℚ)) := by
      rw [sum_add_distrib, hrefl]; unfold H1; ring
    rw [this]
    unfold H2 H3 H4
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    linear_combination key j hj
  rw [e]
  refine V_add (V_sub ?_ ?_) ?_
  · have := V_p_pow_mul (m := 2) h3
    exact V_of_eq (by ring) (V_neg this)
  · exact V_p_pow_mul (m := 3) h4
  · apply V_p_pow_mul (m := 4) (n := 0)
    apply V_sum
    intro j hj
    rw [mem_range] at hj
    have hj' : j + 1 < p := by omega
    rw [one_div, mul_inv]
    exact V_mul0 (V_one_div_succ_pow hj' 4 |> fun h => by simpa using h)
      (V_inv_nat (not_dvd_p_sub hj'))

/-- `2 H3 + 3 p H4 ≡ 0 (mod p^2)` -/
lemma V2_H3_aux : V p 2 (2 * H3 (p - 1) + 3 * (p : ℚ) * H4 (p - 1)) := by
  have hrefl : ∑ j ∈ range (p - 1), 1 / ((p - (j + 1) : ℕ) : ℚ) ^ 2 = H2 (p - 1) := by
    unfold H2
    have := sum_reflect_succ (p := p) (fun i => 1 / (i : ℚ) ^ 2)
    rw [this]; apply sum_congr rfl; intro j _; push_cast; ring
  have key : ∀ j ∈ range (p - 1),
      1 / ((p - (j + 1) : ℕ) : ℚ) ^ 2 - 1 / ((j : ℚ) + 1) ^ 2 =
        2 * (p : ℚ) / ((j : ℚ) + 1) ^ 3 + 3 * (p : ℚ) ^ 2 / ((j : ℚ) + 1) ^ 4
          + (p : ℚ) ^ 3 * ((4 * ((j : ℚ) + 1) - 3 * p) /
              (((j : ℚ) + 1) ^ 4 * ((p - (j + 1) : ℕ) : ℚ) ^ 2)) := by
    intro j hj
    rw [mem_range] at hj
    have hj' : j + 1 < p := by omega
    rw [cast_p_sub hj']
    have h1 : ((j : ℚ) + 1) ≠ 0 := nat_succ_ne_zero j
    have h2 : (p : ℚ) - ((j : ℚ) + 1) ≠ 0 := by
      have : ((j : ℚ) + 1) < p := by exact_mod_cast hj'
      linarith
    field_simp
    ring
  have e : 2 * (p : ℚ) * H3 (p - 1) + 3 * (p : ℚ) ^ 2 * H4 (p - 1) +
      (p : ℚ) ^ 3 * ∑ j ∈ range (p - 1), (4 * ((j : ℚ) + 1) - 3 * p) /
              (((j : ℚ) + 1) ^ 4 * ((p - (j + 1) : ℕ) : ℚ) ^ 2) = 0 := by
    have : (0 : ℚ) = ∑ j ∈ range (p - 1),
        (1 / ((p - (j + 1) : ℕ) : ℚ) ^ 2 - 1 / ((j : ℚ) + 1) ^ 2) := by
      rw [sum_sub_distrib, hrefl]; unfold H2; ring
    rw [this]
    unfold H3 H4
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    linear_combination -(key j hj)
  have h3 : V p 3 (2 * (p : ℚ) * H3 (p - 1) + 3 * (p : ℚ) ^ 2 * H4 (p - 1)) := by
    have : 2 * (p : ℚ) * H3 (p - 1) + 3 * (p : ℚ) ^ 2 * H4 (p - 1) =
        -((p : ℚ) ^ 3 * ∑ j ∈ range (p - 1), (4 * ((j : ℚ) + 1) - 3 * p) /
              (((j : ℚ) + 1) ^ 4 * ((p - (j + 1) : ℕ) : ℚ) ^ 2)) := by
      linear_combination e
    rw [this]
    apply V_neg
    apply V_p_pow_mul (m := 3) (n := 0)
    apply V_sum
    intro j hj
    rw [mem_range] at hj
    have hj' : j + 1 < p := by omega
    rw [div_eq_mul_inv, mul_inv]
    refine V_mul0 ?_ (V_mul0 (V_inv_nat_pow (not_dvd_succ_of_lt hj') 4 |> fun h => by
      push_cast at h; exact h) (V_inv_nat_pow (not_dvd_p_sub hj') 2))
    exact V_sub (V_mul0 (V_ofNat 4) (by exact_mod_cast V_nat (p := p) (j + 1)))
      (V_mul0 (V_ofNat 3) (V_nat p))
  have : 2 * (p : ℚ) * H3 (p - 1) + 3 * (p : ℚ) ^ 2 * H4 (p - 1) =
      (p : ℚ) * (2 * H3 (p - 1) + 3 * (p : ℚ) * H4 (p - 1)) := by ring
  rw [this] at h3
  exact V_of_p_mul h3

lemma V2_H3 (hp3 : 3 ≤ p) (h4 : V p 1 (H4 (p - 1))) : V p 2 (H3 (p - 1)) := by
  have h := V2_H3_aux (p := p)
  have h' : V p 2 (3 * (p : ℚ) * H4 (p - 1)) := by
    have := V_p_mul h4
    exact V_of_eq (by ring) (V_mul0 (V_ofNat 3) this)
  have := V_sub h h'
  have e : 2 * H3 (p - 1) + 3 * (p : ℚ) * H4 (p - 1) - 3 * (p : ℚ) * H4 (p - 1) =
      (2 : ℕ) * H3 (p - 1) := by push_cast; ring
  rw [e] at this
  exact (V_nat_mul_iff (by
    intro h2; have := Nat.le_of_dvd (by norm_num) h2; have := hp.out.two_le; omega)).1 this

end A357674Proof

/- ## Section: Padic2 -/
namespace A357674Proof

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime]

/- ### Binomial coefficients as products -/

/-- `Qprod N k = ∏_{j<k} (1 - N/(j+1))` -/
def Qprod (N k : ℕ) : ℚ := ∏ j ∈ range k, (1 - (N : ℚ) / ((j : ℚ) + 1))

lemma Qprod_succ (N k : ℕ) : Qprod N (k + 1) = Qprod N k * (1 - (N : ℚ) / ((k : ℚ) + 1)) := by
  simp [Qprod, prod_range_succ]

/-- `C(N-1, k) = (-1)^k ∏_{j<k} (1 - N/(j+1))` for `k ≤ N - 1`. -/
lemma choose_pred_eq_Qprod (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N - 1) :
    ((N - 1).choose k : ℚ) = (-1) ^ k * Qprod N k := by
  induction k with
  | zero => simp [Qprod]
  | succ k ih =>
    have hk' : k ≤ N - 1 := by omega
    have h := Nat.choose_succ_right_eq (N - 1) k
    have hcast : (((N - 1 - k : ℕ) : ℚ)) = (N : ℚ) - ((k : ℚ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hN]; push_cast; ring
    have h' : ((N - 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) =
        ((N - 1).choose k : ℚ) * ((N : ℚ) - ((k : ℚ) + 1)) := by
      rw [← hcast]; exact_mod_cast h
    rw [ih hk'] at h'
    rw [Qprod_succ]
    have hne := nat_succ_ne_zero k
    field_simp
    field_simp at h'
    linear_combination h'

/-- `C(a + m, m) = ∏_{k<m} (1 + a/(k+1))`. -/
lemma choose_add_eq_prod (a m : ℕ) :
    ((a + m).choose m : ℚ) = ∏ k ∈ range m, (1 + (a : ℚ) / ((k : ℚ) + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← ih]
    have h := Nat.add_one_mul_choose_eq (a + m) m
    have h' : ((a : ℚ) + m + 1) * ((a + m).choose m : ℚ) =
        ((a + m + 1).choose (m + 1) : ℚ) * ((m : ℚ) + 1) := by exact_mod_cast h
    have e : a + (m + 1) = a + m + 1 := by ring
    rw [e]
    have hne := nat_succ_ne_zero m
    field_simp
    linear_combination -h'

/- ### p-adic expansions of the products -/

/-- `∏_{j<m} (1 - p/(j+1)) ≡ 1 - p H1 m + p^2 E2 m  (mod p^3)` for `m ≤ p - 1`. -/
lemma V3_Qprod {m : ℕ} (hm : m ≤ p - 1) :
    V p 3 (Qprod p m - (1 - (p : ℚ) * H1 m + (p : ℚ) ^ 2 * E2 m)) := by
  induction m with
  | zero => simp [Qprod]; exact V_zero 3
  | succ m ih =>
    have hm' : m ≤ p - 1 := by omega
    have hlt : m + 1 < p := by have := hp.out.pos; omega
    have e : Qprod p (m + 1) - (1 - (p : ℚ) * H1 (m + 1) + (p : ℚ) ^ 2 * E2 (m + 1)) =
        (Qprod p m - (1 - (p : ℚ) * H1 m + (p : ℚ) ^ 2 * E2 m)) * (1 - (p : ℚ) / ((m : ℚ) + 1))
          + (p : ℚ) ^ 3 * (-(E2 m / ((m : ℚ) + 1))) := by
      rw [Qprod_succ, H1_succ, E2_succ]; ring
    rw [e]
    refine V_add (V_mul0' (ih hm') ?_) (V_p_pow_mul (n := 0) (V_neg (V_div_succ (V0_E2 hm') hlt)))
    exact V_sub V_one (V_div_succ (V_mono (Nat.zero_le _) V_p) hlt)

/-- `Phi m = ∏_{j<m} (1 - 2p/(j+1)) (1 - p/(j+1))` -/
def Phi (p m : ℕ) : ℚ :=
  ∏ j ∈ range m, ((1 - 2 * (p : ℚ) / ((j : ℚ) + 1)) * (1 - (p : ℚ) / ((j : ℚ) + 1)))

lemma Phi_succ (m : ℕ) : Phi p (m + 1) =
    Phi p m * ((1 - 2 * (p : ℚ) / ((m : ℚ) + 1)) * (1 - (p : ℚ) / ((m : ℚ) + 1))) := by
  simp [Phi, prod_range_succ]

/-- `Phi m ≡ 1 - 3p H1 + 2p^2 H2 + 9 p^2 E2 (mod p^3)` for `m ≤ p-1`. -/
lemma V3_Phi {m : ℕ} (hm : m ≤ p - 1) :
    V p 3 (Phi p m - (1 - 3 * (p : ℚ) * H1 m + 2 * (p : ℚ) ^ 2 * H2 m + 9 * (p : ℚ) ^ 2 * E2 m)) := by
  induction m with
  | zero => simp [Phi]; exact V_zero 3
  | succ m ih =>
    have hm' : m ≤ p - 1 := by omega
    have hlt : m + 1 < p := by have := hp.out.pos; omega
    have e : Phi p (m + 1) -
        (1 - 3 * (p : ℚ) * H1 (m + 1) + 2 * (p : ℚ) ^ 2 * H2 (m + 1) + 9 * (p : ℚ) ^ 2 * E2 (m + 1)) =
        (Phi p m - (1 - 3 * (p : ℚ) * H1 m + 2 * (p : ℚ) ^ 2 * H2 m + 9 * (p : ℚ) ^ 2 * E2 m)) *
            ((1 - 2 * (p : ℚ) / ((m : ℚ) + 1)) * (1 - (p : ℚ) / ((m : ℚ) + 1)))
          + (p : ℚ) ^ 3 * (-6 * (H2 m / ((m : ℚ) + 1)) - 27 * (E2 m / ((m : ℚ) + 1))
              - 6 * (H1 m / ((m : ℚ) + 1) ^ 2) + 4 * (p : ℚ) * (H2 m / ((m : ℚ) + 1) ^ 2)
              + 18 * (p : ℚ) * (E2 m / ((m : ℚ) + 1) ^ 2)) := by
      rw [Phi_succ, H1_succ, H2_succ, E2_succ]
      have := nat_succ_ne_zero m
      field_simp
      ring
    rw [e]
    have hu : V p 0 ((1 - 2 * (p : ℚ) / ((m : ℚ) + 1)) * (1 - (p : ℚ) / ((m : ℚ) + 1))) := by
      refine V_mul0 (V_sub V_one (V_div_succ ?_ hlt)) (V_sub V_one (V_div_succ (V_mono (Nat.zero_le _) V_p) hlt))
      exact V_mul0 (V_ofNat 2) (V_mono (Nat.zero_le _) V_p)
    refine V_add (V_mul0' (ih hm') hu) (V_p_pow_mul (n := 0) ?_)
    have hp0 : V p 0 (p : ℚ) := V_mono (Nat.zero_le _) V_p
    refine V_add (V_add (V_sub (V_sub (V_mul0 (V_neg (V_ofNat 6)) (V_div_succ (V0_H2 hm') hlt))
      (V_mul0 (V_ofNat 27) (V_div_succ (V0_E2 hm') hlt)))
      (V_mul0 (V_ofNat 6) (V_div_succ_pow (V0_H1 hm') hlt 2)))
      (V_mul0 (V_mul0 (V_ofNat 4) hp0) (V_div_succ_pow (V0_H2 hm') hlt 2)))
      (V_mul0 (V_mul0 (V_ofNat 18) hp0) (V_div_succ_pow (V0_E2 hm') hlt 2))

/-- `Wprod m = ∏_{j<m} (1 + 2p/(j+1))` -/
def Wprod (p m : ℕ) : ℚ := ∏ j ∈ range m, (1 + 2 * (p : ℚ) / ((j : ℚ) + 1))

lemma Wprod_succ (m : ℕ) : Wprod p (m + 1) = Wprod p m * (1 + 2 * (p : ℚ) / ((m : ℚ) + 1)) := by
  simp [Wprod, prod_range_succ]

/-- `Wprod m ≡ 1 + 2p H1 + 4p^2 E2 + 8p^3 E3 + 16 p^4 E4 (mod p^5)` for `m ≤ p-1`. -/
lemma V5_Wprod {m : ℕ} (hm : m ≤ p - 1) :
    V p 5 (Wprod p m - (1 + 2 * (p : ℚ) * H1 m + 4 * (p : ℚ) ^ 2 * E2 m + 8 * (p : ℚ) ^ 3 * E3 m
      + 16 * (p : ℚ) ^ 4 * E4 m)) := by
  induction m with
  | zero => simp [Wprod]; exact V_zero 5
  | succ m ih =>
    have hm' : m ≤ p - 1 := by omega
    have hlt : m + 1 < p := by have := hp.out.pos; omega
    have e : Wprod p (m + 1) - (1 + 2 * (p : ℚ) * H1 (m + 1) + 4 * (p : ℚ) ^ 2 * E2 (m + 1)
        + 8 * (p : ℚ) ^ 3 * E3 (m + 1) + 16 * (p : ℚ) ^ 4 * E4 (m + 1)) =
        (Wprod p m - (1 + 2 * (p : ℚ) * H1 m + 4 * (p : ℚ) ^ 2 * E2 m + 8 * (p : ℚ) ^ 3 * E3 m
          + 16 * (p : ℚ) ^ 4 * E4 m)) * (1 + 2 * (p : ℚ) / ((m : ℚ) + 1))
          + (p : ℚ) ^ 5 * (32 * (E4 m / ((m : ℚ) + 1))) := by
      rw [Wprod_succ, H1_succ, E2_succ, E3_succ, E4_succ]; ring
    rw [e]
    have hu : V p 0 (1 + 2 * (p : ℚ) / ((m : ℚ) + 1)) :=
      V_add V_one (V_div_succ (V_mul0 (V_ofNat 2) (V_mono (Nat.zero_le _) V_p)) hlt)
    exact V_add (V_mul0' (ih hm') hu)
      (V_p_pow_mul (n := 0) (V_mul0 (V_ofNat 32) (V_div_succ (V0_E4 hm') hlt)))

/-- The alternating binomial sums at `n = p-1` in terms of `Qprod`. -/
lemma alt_choose_eq_Qprod {n k : ℕ} (hn : n = p - 1) (hk : k < n) :
    (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) = -Qprod p (k + 1) := by
  subst hn
  rw [choose_pred_eq_Qprod p hp.out.one_lt.le (k + 1) (by omega)]
  have h1 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ]
  linear_combination (-Qprod p (k + 1)) * h1

/- ### Derived congruences at `n = p - 1` -/

section derived

variable (hp7 : 7 ≤ p)
include hp7

lemma p_sub_one_le : p - 1 ≤ p - 1 := le_refl _

lemma not_dvd_small {k : ℕ} (hk0 : 0 < k) (hk : k < 7) : ¬ p ∣ k :=
  not_dvd_of_lt hk0 (by omega)

lemma not_dvd_24 : ¬ p ∣ 24 := fun h => by
  have hle : p ≤ 24 := Nat.le_of_dvd (by norm_num) h
  have hpr := hp.out
  interval_cases p <;> revert h hpr <;> norm_num

lemma hV1_H2 : V p 1 (H2 (p - 1)) := V1_H2 (by omega)
lemma hV1_H4 : V p 1 (H4 (p - 1)) := V1_H4 hp7
lemma hV2_H3 : V p 2 (H3 (p - 1)) := V2_H3 (by omega) (hV1_H4 hp7)
lemma hV4_H1 : V p 4 (2 * H1 (p - 1) + (p : ℚ) * H2 (p - 1)) := V4_H1 (hV2_H3 hp7) (hV1_H4 hp7)

lemma hV2_H1 : V p 2 (H1 (p - 1)) := by
  have h := V_sub (V_mono (by norm_num) (hV4_H1 hp7)) (V_p_mul (hV1_H2 hp7))
  have e : 2 * H1 (p - 1) + (p : ℚ) * H2 (p - 1) - (p : ℚ) * H2 (p - 1) = (2 : ℕ) * H1 (p - 1) := by
    push_cast; ring
  rw [e] at h
  exact (V_nat_mul_iff (not_dvd_small hp7 (by norm_num) (by norm_num))).1 h

lemma hV2_E3 : V p 2 (E3 (p - 1)) := by
  have h := newton3 (p - 1)
  have h1 := hV2_H1 hp7
  have : V p 2 ((6 : ℕ) * E3 (p - 1)) := by
    push_cast; rw [h]
    refine V_add (V_sub ?_ ?_) ?_
    · exact V_mono (by norm_num) (V_pow h1 3)
    · exact V_mono (by norm_num) (V_mul (V_mul0 (V_ofNat 3) h1) (hV1_H2 hp7))
    · exact V_mul0 (V_ofNat 2) (hV2_H3 hp7)
  exact (V_nat_mul_iff (not_dvd_small hp7 (by norm_num) (by norm_num))).1 this

lemma hV1_E4 : V p 1 (E4 (p - 1)) := by
  have h := newton4 (p - 1)
  have h1 := hV2_H1 hp7
  have h2 := hV1_H2 hp7
  have : V p 1 ((24 : ℕ) * E4 (p - 1)) := by
    push_cast; rw [h]
    refine V_sub (V_add (V_add (V_sub ?_ ?_) ?_) ?_) ?_
    · exact V_mono (by norm_num) (V_pow h1 4)
    · exact V_mono (by norm_num) (V_mul (V_mul0 (V_ofNat 6) (V_pow h1 2)) h2)
    · exact V_mono (by norm_num) (V_mul0 (V_ofNat 3) (V_pow h2 2))
    · exact V_mono (by norm_num) (V_mul (V_mul0 (V_ofNat 8) h1) (hV2_H3 hp7))
    · exact V_mul0 (V_ofNat 6) (hV1_H4 hp7)
  exact (V_nat_mul_iff (not_dvd_24 hp7)).1 this

lemma hV1_H22 : V p 1 (H22 (p - 1)) := by
  have h := stuffle22 (p - 1)
  have : V p 1 ((2 : ℕ) * H22 (p - 1)) := by
    push_cast
    have e : 2 * H22 (p - 1) = H2 (p - 1) ^ 2 - H4 (p - 1) := by linear_combination -h
    rw [e]
    exact V_sub (V_mono (by norm_num) (V_pow (hV1_H2 hp7) 2)) (hV1_H4 hp7)
  exact (V_nat_mul_iff (not_dvd_small hp7 (by norm_num) (by norm_num))).1 this

lemma hV1_H13_H31 : V p 1 (H13 (p - 1) + H31 (p - 1)) := by
  have h := stuffle13 (p - 1)
  have e : H13 (p - 1) + H31 (p - 1) = H1 (p - 1) * H3 (p - 1) - H4 (p - 1) := by linear_combination -h
  rw [e]
  exact V_sub (V_mono (by norm_num) (V_mul (hV2_H1 hp7) (hV2_H3 hp7))) (hV1_H4 hp7)

lemma hV1_H211_H121_H112 : V p 1 (H211 (p - 1) + H121 (p - 1) + H112 (p - 1)) := by
  have h := stuffle2_11 (p - 1)
  have e : H211 (p - 1) + H121 (p - 1) + H112 (p - 1) =
      H2 (p - 1) * E2 (p - 1) - (H13 (p - 1) + H31 (p - 1)) := by linear_combination -h
  rw [e]
  exact V_sub (V_mul0' (hV1_H2 hp7) (V0_E2 le_rfl)) (hV1_H13_H31 hp7)

/-- I5 : `p H12 ≡ 3/2 H2 + p^2 H112 + p^2 H13 (mod p^3)` -/
lemma hI5 : V p 3 ((p : ℚ) * H12 (p - 1) - 3 / 2 * H2 (p - 1)
    - (p : ℚ) ^ 2 * H112 (p - 1) - (p : ℚ) ^ 2 * H13 (p - 1)) := by
  set n := p - 1 with hn
  have hB1 := binom_B1 n
  -- LHS in terms of Qprod
  have hL : ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) / ((k : ℚ) + 1) ^ 2 =
      -∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 2 := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [alt_choose_eq_Qprod hn hk]; ring
  -- approximate
  have hA : V p 3 (∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 2 -
      (H2 n - (p : ℚ) * (H12 n + H3 n) + (p : ℚ) ^ 2 * (H112 n + H13 n))) := by
    have e : H2 n - (p : ℚ) * (H12 n + H3 n) + (p : ℚ) ^ 2 * (H112 n + H13 n) =
        ∑ k ∈ range n, (1 - (p : ℚ) * H1 (k + 1) + (p : ℚ) ^ 2 * E2 (k + 1)) / ((k : ℚ) + 1) ^ 2 := by
      rw [← sum_H1_succ_div_sq, ← sum_E2_succ_div_sq]
      unfold H2
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro k _; ring
    rw [e, ← sum_sub_distrib]
    apply V_sum
    intro k hk
    rw [mem_range] at hk
    rw [← sub_div]
    exact V_div_succ_pow (V3_Qprod (by omega)) (by omega) 2
  rw [hL, sum_H1_succ_div] at hB1
  -- hB1 : -∑ Qprod/(k+1)^2 = E2 n + H2 n
  have hS : ∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 2 = -(E2 n + H2 n) := by
    linear_combination -hB1
  rw [hS] at hA
  have h2 := newton2 n
  have hE2 : E2 n = (H1 n ^ 2 - H2 n) / 2 := by linear_combination -h2 / 2
  rw [hE2] at hA
  have e : (p : ℚ) * H12 n - 3 / 2 * H2 n - (p : ℚ) ^ 2 * H112 n - (p : ℚ) ^ 2 * H13 n =
      H1 n ^ 2 / 2 - (p : ℚ) * H3 n +
        (-((H1 n ^ 2 - H2 n) / 2 + H2 n) - (H2 n - (p : ℚ) * (H12 n + H3 n) +
          (p : ℚ) ^ 2 * (H112 n + H13 n))) := by ring
  rw [e]
  refine V_add (V_sub ?_ ?_) hA
  · have := V_pow (hV2_H1 hp7) 2
    exact V_mono (by norm_num) (V_div_nat this (not_dvd_small hp7 (by norm_num) (by norm_num)))
  · exact V_p_mul (hV2_H3 hp7)

/-- `H13 ≡ 0 (mod p)` -/
lemma hV1_H13 : V p 1 (H13 (p - 1)) := by
  set n := p - 1 with hn
  have hB3 := binom_B3 n
  have hL : ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) / ((k : ℚ) + 1) ^ 3 =
      -∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 3 := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [alt_choose_eq_Qprod hn hk]; ring
  have hA : V p 2 (∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 3 -
      (H3 n - (p : ℚ) * (H13 n + H4 n))) := by
    have e : H3 n - (p : ℚ) * (H13 n + H4 n) =
        ∑ k ∈ range n, (1 - (p : ℚ) * H1 (k + 1)) / ((k : ℚ) + 1) ^ 3 := by
      rw [← sum_H1_succ_div_cube]
      unfold H3
      simp only [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro k _; ring
    rw [e, ← sum_sub_distrib]
    apply V_sum
    intro k hk
    rw [mem_range] at hk
    rw [← sub_div]
    apply V_div_succ_pow _ (by omega) 3
    have h3 := V3_Qprod (p := p) (m := k + 1) (by omega)
    have : Qprod p (k + 1) - (1 - (p : ℚ) * H1 (k + 1)) =
        (Qprod p (k + 1) - (1 - (p : ℚ) * H1 (k + 1) + (p : ℚ) ^ 2 * E2 (k + 1))) +
          (p : ℚ) ^ 2 * E2 (k + 1) := by ring
    rw [this]
    exact V_add (V_mono (by norm_num) h3) (V_p_pow_mul (n := 0) (V0_E2 (by omega)))
  rw [hL] at hB3
  have hS : ∑ k ∈ range n, Qprod p (k + 1) / ((k : ℚ) + 1) ^ 3 = -(E3 n + H12 n + H21 n + H3 n) := by
    linear_combination -hB3
  rw [hS] at hA
  have h12 := stuffle12 n
  have e : (p : ℚ) * H13 n = E3 n + H1 n * H2 n + H3 n - (p : ℚ) * H4 n +
      (-(E3 n + H12 n + H21 n + H3 n) - (H3 n - (p : ℚ) * (H13 n + H4 n))) := by
    linear_combination -h12
  have : V p 2 ((p : ℚ) * H13 n) := by
    rw [e]
    refine V_add (V_sub (V_add (V_add (hV2_E3 hp7) ?_) (hV2_H3 hp7)) (V_p_mul (hV1_H4 hp7))) hA
    exact V_mono (by norm_num) (V_mul (hV2_H1 hp7) (hV1_H2 hp7))
  exact V_of_p_mul this

/-- `H112 ≡ 0 (mod p)` -/
lemma hV1_H112 : V p 1 (H112 (p - 1)) := by
  set n := p - 1 with hn
  have hB2 := binom_B2 n
  have hL : ∑ k ∈ range n, (-1 : ℚ) ^ k * (n.choose (k + 1) : ℚ) * H1 (k + 1) / ((k : ℚ) + 1) =
      -∑ k ∈ range n, Qprod p (k + 1) * H1 (k + 1) / ((k : ℚ) + 1) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [alt_choose_eq_Qprod hn hk]; ring
  have hA : V p 3 (∑ k ∈ range n, Qprod p (k + 1) * H1 (k + 1) / ((k : ℚ) + 1) -
      ((E2 n + H2 n) - (p : ℚ) * (2 * E3 n + H21 n + 2 * H12 n + H3 n) +
        (p : ℚ) ^ 2 * (3 * E4 n + H211 n + H121 n + 3 * H112 n + H22 n + H13 n))) := by
    have e : (E2 n + H2 n) - (p : ℚ) * (2 * E3 n + H21 n + 2 * H12 n + H3 n) +
        (p : ℚ) ^ 2 * (3 * E4 n + H211 n + H121 n + 3 * H112 n + H22 n + H13 n) =
        ∑ k ∈ range n, (1 - (p : ℚ) * H1 (k + 1) + (p : ℚ) ^ 2 * E2 (k + 1)) * H1 (k + 1) /
          ((k : ℚ) + 1) := by
      rw [← sum_H1_succ_div, ← sum_H1_succ_sq_div, ← sum_E2_H1_succ_div]
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro k _; ring
    rw [e, ← sum_sub_distrib]
    apply V_sum
    intro k hk
    rw [mem_range] at hk
    rw [← sub_div, ← sub_mul]
    exact V_div_succ (V_mul0' (V3_Qprod (by omega)) (V0_H1 (by omega))) (by omega)
  rw [hL] at hB2
  have hS : ∑ k ∈ range n, Qprod p (k + 1) * H1 (k + 1) / ((k : ℚ) + 1) = -H2 n := by
    linear_combination -hB2
  rw [hS] at hA
  have h2 := newton2 n
  have h12 := stuffle12 n
  have hI := hI5 hp7
  -- combine
  have key : V p 3 ((p : ℚ) ^ 2 * (3 * E4 n + H211 n + H121 n + 2 * H112 n + H22 n)) := by
    have e : (p : ℚ) ^ 2 * (3 * E4 n + H211 n + H121 n + 2 * H112 n + H22 n) =
        -(-H2 n - ((E2 n + H2 n) - (p : ℚ) * (2 * E3 n + H21 n + 2 * H12 n + H3 n) +
          (p : ℚ) ^ 2 * (3 * E4 n + H211 n + H121 n + 3 * H112 n + H22 n + H13 n)))
        + ((p : ℚ) * H12 n - 3 / 2 * H2 n - (p : ℚ) ^ 2 * H112 n - (p : ℚ) ^ 2 * H13 n)
        - H1 n ^ 2 / 2 + 2 * (p : ℚ) * E3 n + (p : ℚ) * (H1 n * H2 n) := by
      linear_combination (1/2 : ℚ) * h2 - (p : ℚ) * h12
    rw [e]
    refine V_add (V_add (V_sub (V_add (V_neg hA) hI) ?_) ?_) ?_
    · have := V_pow (hV2_H1 hp7) 2
      exact V_mono (by norm_num) (V_div_nat this (not_dvd_small hp7 (by norm_num) (by norm_num)))
    · have := V_p_mul (hV2_E3 hp7)
      exact V_of_eq (by ring) (V_mul0 (V_ofNat 2) this)
    · exact V_mono (by norm_num) (V_p_mul (V_mul (hV2_H1 hp7) (hV1_H2 hp7)))
  have key1 : V p 1 (3 * E4 n + H211 n + H121 n + 2 * H112 n + H22 n) :=
    V_of_p_pow_mul (m := 2) key
  have e : H112 n = (3 * E4 n + H211 n + H121 n + 2 * H112 n + H22 n)
      - 3 * E4 n - H22 n - (H211 n + H121 n + H112 n) := by ring
  rw [e]
  exact V_sub (V_sub (V_sub key1 (V_mul0 (V_ofNat 3) (hV1_E4 hp7))) (hV1_H22 hp7))
    (hV1_H211_H121_H112 hp7)

end derived

end A357674Proof

/- ## Section: Padic3 -/
namespace A357674Proof

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime]

section main

variable (hp7 : 7 ≤ p)
include hp7

/-- M1 : `C(3p-1,p-1) = Wprod p (p-1) ≡ 1 - 3 p^2 H2 (mod p^5)`. -/
lemma hM1 : V p 5 (Wprod p (p - 1) - 1 + 3 * (p : ℚ) ^ 2 * H2 (p - 1)) := by
  have hW := V5_Wprod (p := p) (m := p - 1) le_rfl
  have h2 := newton2 (p - 1)
  have e : Wprod p (p - 1) - 1 + 3 * (p : ℚ) ^ 2 * H2 (p - 1) =
      (Wprod p (p - 1) - (1 + 2 * (p : ℚ) * H1 (p - 1) + 4 * (p : ℚ) ^ 2 * E2 (p - 1)
        + 8 * (p : ℚ) ^ 3 * E3 (p - 1) + 16 * (p : ℚ) ^ 4 * E4 (p - 1)))
      + (p : ℚ) * (2 * H1 (p - 1) + (p : ℚ) * H2 (p - 1))
      + 2 * ((p : ℚ) ^ 2 * H1 (p - 1) ^ 2)
      + 8 * ((p : ℚ) ^ 3 * E3 (p - 1)) + 16 * ((p : ℚ) ^ 4 * E4 (p - 1)) := by
    linear_combination (-2 * (p : ℚ) ^ 2) * h2
  rw [e]
  refine V_add (V_add (V_add (V_add hW ?_) ?_) ?_) ?_
  · exact V_p_mul (hV4_H1 hp7)
  · exact V_mul0 (V_ofNat 2) (V_mono (by norm_num) (V_p_pow_mul (m := 2) (V_pow (hV2_H1 hp7) 2)))
  · exact V_mul0 (V_ofNat 8) (V_p_pow_mul (m := 3) (hV2_E3 hp7))
  · exact V_mul0 (V_ofNat 16) (V_p_pow_mul (m := 4) (hV1_E4 hp7))

end main

/-- The key sum `R = ∑_{k<p-1} C(2p-1,k) C(p-1,k+1) / ((k+1)(p+k+1))`. -/
def Rsum (p : ℕ) : ℚ :=
  ∑ k ∈ range (p - 1), ((2 * p - 1).choose k : ℚ) * ((p - 1).choose (k + 1) : ℚ) /
    (((k : ℚ) + 1) * ((p : ℚ) + ((k : ℚ) + 1)))

lemma Qprod_mul_Qprod (k : ℕ) : Qprod (2 * p) k * Qprod p k = Phi p k := by
  unfold Qprod Phi
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  push_cast; ring

lemma Rsum_term {k : ℕ} (hk : k < p - 1) :
    ((2 * p - 1).choose k : ℚ) * ((p - 1).choose (k + 1) : ℚ) /
      (((k : ℚ) + 1) * ((p : ℚ) + ((k : ℚ) + 1))) =
    -(Phi p k * ((1 - (p : ℚ) / ((k : ℚ) + 1)) / (((k : ℚ) + 1) * ((p : ℚ) + ((k : ℚ) + 1))))) := by
  have hp1 := hp.out.one_lt
  rw [choose_pred_eq_Qprod (2 * p) (by omega) k (by omega),
    choose_pred_eq_Qprod p (by omega) (k + 1) (by omega), Qprod_succ, ← Qprod_mul_Qprod]
  have h1 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ]
  linear_combination (-(Qprod (2 * p) k * Qprod p k * (1 - (p : ℚ) / ((k : ℚ) + 1)) /
    (((k : ℚ) + 1) * ((p : ℚ) + ((k : ℚ) + 1))))) * h1

lemma not_dvd_p_add_succ {k : ℕ} (hk : k + 1 < p) : ¬ p ∣ (p + (k + 1)) := by
  intro h
  have h2 : p ∣ (p + (k + 1)) - p := Nat.dvd_sub h (dvd_refl p)
  rw [Nat.add_sub_cancel_left] at h2
  exact not_dvd_succ_of_lt hk h2

/-- The approximation of a single term. -/
lemma Rsum_term_approx {k : ℕ} (hk : k < p - 1) :
    V p 3 (Phi p k * ((1 - (p : ℚ) / ((k : ℚ) + 1)) / (((k : ℚ) + 1) * ((p : ℚ) + ((k : ℚ) + 1))))
      - (1 / ((k : ℚ) + 1) ^ 2 - 3 * (p : ℚ) * (H1 k / ((k : ℚ) + 1) ^ 2)
          + 2 * (p : ℚ) ^ 2 * (H2 k / ((k : ℚ) + 1) ^ 2) + 9 * (p : ℚ) ^ 2 * (E2 k / ((k : ℚ) + 1) ^ 2)
          - 2 * (p : ℚ) * (1 / ((k : ℚ) + 1) ^ 3) + 6 * (p : ℚ) ^ 2 * (H1 k / ((k : ℚ) + 1) ^ 3)
          + 2 * (p : ℚ) ^ 2 * (1 / ((k : ℚ) + 1) ^ 4))) := by
  have hlt : k + 1 < p := by have := hp.out.pos; omega
  have hkm : k ≤ p - 1 := by omega
  have hp0 : V p 0 (p : ℚ) := V_mono (Nat.zero_le _) V_p
  set x : ℚ := (k : ℚ) + 1 with hx
  have hxne : x ≠ 0 := nat_succ_ne_zero k
  have hyne : (p : ℚ) + x ≠ 0 := by positivity
  -- the "unit" factors
  have hVy : V p 0 (1 / ((p : ℚ) + x)) := by
    have := V_one_div_nat (p := p) (not_dvd_p_add_succ hlt)
    push_cast at this; exact this
  have hV1x : V p 0 (1 / x) := V_one_div_succ hlt
  have hVxs : ∀ s : ℕ, V p 0 (1 / x ^ s) := fun s => V_one_div_succ_pow hlt s
  -- a_k ≈ b_k
  set a : ℚ := (1 - (p : ℚ) / x) / (x * ((p : ℚ) + x)) with ha
  set b : ℚ := (1 / x ^ 2) * (1 - 2 * (p : ℚ) / x + 2 * (p : ℚ) ^ 2 / x ^ 2) with hb
  have hab : V p 3 (a - b) := by
    have e : a - b = (p : ℚ) ^ 3 * (-2 * ((1 / x ^ 4) * (1 / ((p : ℚ) + x)))) := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact V_p_pow_mul (n := 0) (V_mul0 (V_neg (V_ofNat 2)) (V_mul0 (hVxs 4) hVy))
  have hVb : V p 0 b := by
    rw [hb]
    refine V_mul0 (hVxs 2) (V_add (V_sub V_one ?_) ?_)
    · rw [div_eq_mul_inv, ← one_div]; exact V_mul0 (V_mul0 (V_ofNat 2) hp0) hV1x
    · rw [div_eq_mul_inv, ← one_div]; exact V_mul0 (V_mul0 (V_ofNat 2) (V_pow hp0 2)) (hVxs 2)
  -- Phi ≈ T
  set T : ℚ := 1 - 3 * (p : ℚ) * H1 k + 2 * (p : ℚ) ^ 2 * H2 k + 9 * (p : ℚ) ^ 2 * E2 k with hT
  have hPT : V p 3 (Phi p k - T) := V3_Phi hkm
  have hVT : V p 0 T := by
    rw [hT]
    refine V_add (V_add (V_sub V_one ?_) ?_) ?_
    · exact V_mul0 (V_mul0 (V_ofNat 3) hp0) (V0_H1 hkm)
    · exact V_mul0 (V_mul0 (V_ofNat 2) (V_pow hp0 2)) (V0_H2 hkm)
    · exact V_mul0 (V_mul0 (V_ofNat 9) (V_pow hp0 2)) (V0_E2 hkm)
  have hVa : V p 0 a := by
    rw [ha, div_eq_mul_inv, mul_inv, ← one_div, ← one_div]
    refine V_mul0 (V_sub V_one ?_) (V_mul0 hV1x hVy)
    rw [div_eq_mul_inv, ← one_div]; exact V_mul0 hp0 hV1x
  have hmain : V p 3 (Phi p k * a - T * b) := V_congr_mul hPT hab hVT hVa
  -- T * b ≈ c
  have hTb : V p 3 (T * b - (1 / x ^ 2 - 3 * (p : ℚ) * (H1 k / x ^ 2)
          + 2 * (p : ℚ) ^ 2 * (H2 k / x ^ 2) + 9 * (p : ℚ) ^ 2 * (E2 k / x ^ 2)
          - 2 * (p : ℚ) * (1 / x ^ 3) + 6 * (p : ℚ) ^ 2 * (H1 k / x ^ 3)
          + 2 * (p : ℚ) ^ 2 * (1 / x ^ 4))) := by
    have e : T * b - (1 / x ^ 2 - 3 * (p : ℚ) * (H1 k / x ^ 2)
          + 2 * (p : ℚ) ^ 2 * (H2 k / x ^ 2) + 9 * (p : ℚ) ^ 2 * (E2 k / x ^ 2)
          - 2 * (p : ℚ) * (1 / x ^ 3) + 6 * (p : ℚ) ^ 2 * (H1 k / x ^ 3)
          + 2 * (p : ℚ) ^ 2 * (1 / x ^ 4)) =
        (p : ℚ) ^ 3 * (-6 * (H1 k / x ^ 4) - 4 * (H2 k / x ^ 3) + 4 * (p : ℚ) * (H2 k / x ^ 4)
          - 18 * (E2 k / x ^ 3) + 18 * (p : ℚ) * (E2 k / x ^ 4)) := by
      rw [hT, hb]; field_simp; ring
    rw [e]
    apply V_p_pow_mul (n := 0)
    refine V_add (V_sub (V_add (V_sub (V_mul0 (V_neg (V_ofNat 6)) (V_div_succ_pow (V0_H1 hkm) hlt 4))
      (V_mul0 (V_ofNat 4) (V_div_succ_pow (V0_H2 hkm) hlt 3)))
      (V_mul0 (V_mul0 (V_ofNat 4) hp0) (V_div_succ_pow (V0_H2 hkm) hlt 4)))
      (V_mul0 (V_ofNat 18) (V_div_succ_pow (V0_E2 hkm) hlt 3)))
      (V_mul0 (V_mul0 (V_ofNat 18) hp0) (V_div_succ_pow (V0_E2 hkm) hlt 4))
  have := V_add hmain hTb
  exact V_of_eq (by ring) this

/-- The approximating sum equals `E`. -/
lemma Rsum_E_eq :
    ∑ k ∈ range (p - 1), (1 / ((k : ℚ) + 1) ^ 2 - 3 * (p : ℚ) * (H1 k / ((k : ℚ) + 1) ^ 2)
          + 2 * (p : ℚ) ^ 2 * (H2 k / ((k : ℚ) + 1) ^ 2) + 9 * (p : ℚ) ^ 2 * (E2 k / ((k : ℚ) + 1) ^ 2)
          - 2 * (p : ℚ) * (1 / ((k : ℚ) + 1) ^ 3) + 6 * (p : ℚ) ^ 2 * (H1 k / ((k : ℚ) + 1) ^ 3)
          + 2 * (p : ℚ) ^ 2 * (1 / ((k : ℚ) + 1) ^ 4)) =
      H2 (p - 1) - 3 * (p : ℚ) * H12 (p - 1) + 2 * (p : ℚ) ^ 2 * H22 (p - 1)
        + 9 * (p : ℚ) ^ 2 * H112 (p - 1) - 2 * (p : ℚ) * H3 (p - 1)
        + 6 * (p : ℚ) ^ 2 * H13 (p - 1) + 2 * (p : ℚ) ^ 2 * H4 (p - 1) := by
  conv_rhs => unfold H2
  conv_rhs => unfold H12 H22 H112 H3 H13 H4
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]

section main2

variable (hp7 : 7 ≤ p)
include hp7

/-- M2 : `Rsum ≡ 7/2 H2 (mod p^3)`. -/
lemma hM2 : V p 3 (Rsum p - 7 / 2 * H2 (p - 1)) := by
  have hRE : V p 3 (Rsum p + (H2 (p - 1) - 3 * (p : ℚ) * H12 (p - 1) + 2 * (p : ℚ) ^ 2 * H22 (p - 1)
        + 9 * (p : ℚ) ^ 2 * H112 (p - 1) - 2 * (p : ℚ) * H3 (p - 1)
        + 6 * (p : ℚ) ^ 2 * H13 (p - 1) + 2 * (p : ℚ) ^ 2 * H4 (p - 1))) := by
    rw [← Rsum_E_eq]
    unfold Rsum
    rw [sum_congr rfl (fun k hk => Rsum_term (mem_range.1 hk)), ← sum_add_distrib]
    apply V_sum
    intro k hk
    rw [mem_range] at hk
    have := Rsum_term_approx (p := p) hk
    exact V_of_eq (by ring) (V_neg this)
  have hI := hI5 hp7
  have hE : V p 3 ((H2 (p - 1) - 3 * (p : ℚ) * H12 (p - 1) + 2 * (p : ℚ) ^ 2 * H22 (p - 1)
        + 9 * (p : ℚ) ^ 2 * H112 (p - 1) - 2 * (p : ℚ) * H3 (p - 1)
        + 6 * (p : ℚ) ^ 2 * H13 (p - 1) + 2 * (p : ℚ) ^ 2 * H4 (p - 1)) + 7 / 2 * H2 (p - 1)) := by
    have e : (H2 (p - 1) - 3 * (p : ℚ) * H12 (p - 1) + 2 * (p : ℚ) ^ 2 * H22 (p - 1)
        + 9 * (p : ℚ) ^ 2 * H112 (p - 1) - 2 * (p : ℚ) * H3 (p - 1)
        + 6 * (p : ℚ) ^ 2 * H13 (p - 1) + 2 * (p : ℚ) ^ 2 * H4 (p - 1)) + 7 / 2 * H2 (p - 1) =
        -3 * ((p : ℚ) * H12 (p - 1) - 3 / 2 * H2 (p - 1)
          - (p : ℚ) ^ 2 * H112 (p - 1) - (p : ℚ) ^ 2 * H13 (p - 1))
        + (p : ℚ) ^ 2 * (6 * H112 (p - 1) + 3 * H13 (p - 1) + 2 * H22 (p - 1))
        - 2 * ((p : ℚ) * H3 (p - 1)) + 2 * ((p : ℚ) ^ 2 * H4 (p - 1)) := by ring
    rw [e]
    refine V_add (V_sub (V_add (V_mul0 (V_neg (V_ofNat 3)) hI) ?_) ?_) ?_
    · apply V_p_pow_mul (m := 2) (n := 1)
      exact V_add (V_add (V_mul0 (V_ofNat 6) (hV1_H112 hp7)) (V_mul0 (V_ofNat 3) (hV1_H13 hp7)))
        (V_mul0 (V_ofNat 2) (hV1_H22 hp7))
    · exact V_mul0 (V_ofNat 2) (V_p_mul (hV2_H3 hp7))
    · exact V_mul0 (V_ofNat 2) (V_p_pow_mul (m := 2) (hV1_H4 hp7))
  have := V_sub hRE hE
  exact V_of_eq (by ring) this

end main2

end A357674Proof

/- ## Section: NatId -/
namespace A357674Proof

/- ### Hockey-stick identities -/

lemma hockey1 (a m : ℕ) : ∑ k ∈ range (m + 1), (a + k).choose k = (a + m + 1).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have : a + (m + 1) + 1 = (a + m + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ', Nat.add_assoc]

lemma hockey2 (a m r : ℕ) (h : a ≤ r) :
    ∑ k ∈ range (m + 1), (a + k).choose r = (a + m + 1).choose (r + 1) := by
  induction m with
  | zero =>
    simp only [range_one, sum_singleton, add_zero, zero_add]
    rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; simp
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
  | succ m ih =>
    rw [sum_range_succ, ih]
    have : a + (m + 1) + 1 = (a + m + 1) + 1 := by ring
    rw [this]
    conv_rhs => rw [Nat.choose_succ_succ']
    rw [add_comm, Nat.add_assoc]

/-- `S1 = C(3p, p)` -/
lemma S1_eq (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ range (2 * p + 1), (p + k - 1).choose k = (3 * p).choose p := by
  have h : ∀ k, p + k - 1 = (p - 1) + k := fun k => by omega
  simp_rw [h]
  rw [hockey1 (p - 1) (2 * p)]
  have e : p - 1 + 2 * p + 1 = p + 2 * p := by omega
  rw [e, ← Nat.choose_symm_add]
  congr 1; ring

/-- Vandermonde in the needed form -/
lemma vandermonde' (p k : ℕ) (hp : 1 ≤ p) :
    (p - 1 + k).choose (p - 1) = ∑ i ∈ range p, (p - 1).choose i * k.choose i := by
  rw [add_comm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have e : p - 1 + 1 = p := by omega
  rw [Nat.succ_eq_add_one, e]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  dsimp only
  rw [Nat.choose_symm (by omega), mul_comm]

lemma choose_mul_choose (p k i : ℕ) :
    (p - 1 + k).choose k * k.choose i = (p - 1 + k).choose (p - 1 + i) * (p - 1 + i).choose i := by
  rcases le_or_gt i k with h | h
  · rw [Nat.choose_mul h, Nat.choose_mul (by omega : i ≤ p - 1 + i)]
    have e1 : p - 1 + k - i = (p - 1) + (k - i) := by omega
    have e2 : p - 1 + i - i = p - 1 := by omega
    rw [e1, e2, Nat.choose_symm_add]
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : p - 1 + k < p - 1 + i)]
    simp

/-- `S2 = ∑_{i<p} C(p-1,i) C(p-1+i,i) C(3p,p+i)` -/
lemma S2_eq (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k) ^ 2 =
      ∑ i ∈ range p, (p - 1).choose i * (p - 1 + i).choose i * (3 * p).choose (p + i) := by
  have h : ∀ k, p + k - 1 = (p - 1) + k := fun k => by omega
  simp_rw [h]
  have hterm : ∀ k, ((p - 1 + k).choose k) ^ 2 =
      ∑ i ∈ range p, (p - 1).choose i * (p - 1 + i).choose i * (p - 1 + k).choose (p - 1 + i) := by
    intro k
    have hs : (p - 1 + k).choose k = (p - 1 + k).choose (p - 1) := Nat.choose_symm_add.symm
    rw [sq]
    nth_rewrite 2 [hs]
    rw [vandermonde' p k hp, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_left_comm, choose_mul_choose]
    ring
  simp_rw [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum, hockey2 (p - 1) (2 * p) (p - 1 + i) (by omega)]
  congr 2 <;> omega

/-- `C(3p, p+i) C(p-1+i, i) (p+i) = C(3p,p) C(2p,i) p` -/
lemma T_formula (p i : ℕ) (hp : 1 ≤ p) :
    (3 * p).choose (p + i) * (p - 1 + i).choose i * (p + i) =
      (3 * p).choose p * (2 * p).choose i * p := by
  have h1 : (3 * p).choose (p + i) * (p + i).choose p = (3 * p).choose p * (2 * p).choose i := by
    have := Nat.choose_mul (n := 3 * p) (k := p + i) (s := p) (by omega)
    rw [this]
    congr 2 <;> omega
  have h2 : (p - 1 + i).choose i * (p + i) = (p + i).choose i * p := by
    have := Nat.choose_mul_succ_eq (p - 1 + i) i
    have e1 : p - 1 + i + 1 = p + i := by omega
    have e2 : p + i - i = p := by omega
    rw [e1, e2] at this
    exact this
  have h3 : (p + i).choose p = (p + i).choose i := Nat.choose_symm_add
  calc (3 * p).choose (p + i) * (p - 1 + i).choose i * (p + i)
      = (3 * p).choose (p + i) * ((p - 1 + i).choose i * (p + i)) := by ring
    _ = (3 * p).choose (p + i) * ((p + i).choose p * p) := by rw [h2, h3]
    _ = ((3 * p).choose (p + i) * (p + i).choose p) * p := by ring
    _ = (3 * p).choose p * (2 * p).choose i * p := by rw [h1]

lemma choose_2p_succ (p k : ℕ) (hp : 1 ≤ p) :
    (2 * p).choose (k + 1) * (k + 1) = 2 * p * (2 * p - 1).choose k := by
  have := Nat.add_one_mul_choose_eq (2 * p - 1) k
  have e : 2 * p - 1 + 1 = 2 * p := by omega
  rw [e] at this
  exact this.symm

lemma choose_3p (p : ℕ) (hp : 1 ≤ p) : (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
  have := Nat.add_one_mul_choose_eq (3 * p - 1) (p - 1)
  have e1 : 3 * p - 1 + 1 = 3 * p := by omega
  have e2 : p - 1 + 1 = p := by omega
  rw [e1, e2] at this
  -- this : 3 * p * C(3p-1,p-1) = C(3p,p) * p
  have hp0 : 0 < p := hp
  have : (3 * (3 * p - 1).choose (p - 1)) * p = (3 * p).choose p * p := by
    rw [← this]; ring
  exact (Nat.eq_of_mul_eq_mul_right hp0 this).symm

/-- `C(3p-1, p-1) = Wprod p (p-1)` -/
lemma choose_3p_eq_Wprod (p : ℕ) (hp : 1 ≤ p) :
    ((3 * p - 1).choose (p - 1) : ℚ) = Wprod p (p - 1) := by
  have e : 3 * p - 1 = 2 * p + (p - 1) := by omega
  rw [e, choose_add_eq_prod]
  unfold Wprod
  apply prod_congr rfl
  intro k _
  push_cast; ring

/-- The rational identity `S2 = S1 * (1 + 2 p^2 Rsum)`. -/
lemma S2_rat (p : ℕ) (hp : 1 ≤ p) :
    ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k) ^ 2 : ℕ) : ℚ) =
      ((3 * p).choose p : ℚ) * (1 + 2 * (p : ℚ) ^ 2 * Rsum p) := by
  rw [S2_eq p hp]
  have hsplit := sum_range_succ' (fun i => ((p - 1).choose i * (p - 1 + i).choose i *
    (3 * p).choose (p + i) : ℚ)) (p - 1)
  have e : p - 1 + 1 = p := by omega
  rw [e] at hsplit
  push_cast
  rw [hsplit]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero]
  unfold Rsum
  rw [mul_add, mul_one, mul_sum, mul_sum, add_comm]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have hT := T_formula p (k + 1) hp
  have hC := choose_2p_succ p k hp
  have hT' : ((3 * p).choose (p + (k + 1)) : ℚ) * ((p - 1 + (k + 1)).choose (k + 1) : ℚ) *
      ((p : ℚ) + ((k : ℚ) + 1)) = ((3 * p).choose p : ℚ) * ((2 * p).choose (k + 1) : ℚ) * p := by
    exact_mod_cast hT
  have hC' : ((2 * p).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = 2 * (p : ℚ) * ((2 * p - 1).choose k : ℚ) := by
    exact_mod_cast hC
  have hx : ((k : ℚ) + 1) ≠ 0 := nat_succ_ne_zero k
  have hy : (p : ℚ) + ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination ((p - 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) * hT' +
    ((p - 1).choose (k + 1) : ℚ) * ((3 * p).choose p : ℚ) * (p : ℚ) * hC'

end A357674Proof

/- ## Section: Main -/
namespace A357674Proof

set_option linter.unusedSectionVars false

/-- the polynomial identity used in the final step -/
lemma poly_identity (u v : ℚ) :
    (1 + u) ^ 4 * (1 + u + v) ^ 3 - 1 =
      (7 * u + 3 * v) +
      u ^ 2 * (u ^ 5 + 7 * u ^ 4 + 21 * u ^ 3 + 35 * u ^ 2 + 35 * u + 21) +
      u * v * (3 * u ^ 5 + 18 * u ^ 4 + 45 * u ^ 3 + 60 * u ^ 2 + 45 * u + 18) +
      v ^ 2 * (3 * u ^ 5 + u ^ 4 * v + 15 * u ^ 4 + 4 * u ^ 3 * v + 30 * u ^ 3 + 6 * u ^ 2 * v
        + 30 * u ^ 2 + 4 * u * v + 15 * u + v + 3) := by
  ring

variable {p : ℕ} [hp : Fact p.Prime]

lemma V0_poly (u v : ℚ) (hu : V p 0 u) (hv : V p 0 v) :
    V p 0 (u ^ 5 + 7 * u ^ 4 + 21 * u ^ 3 + 35 * u ^ 2 + 35 * u + 21) ∧
    V p 0 (3 * u ^ 5 + 18 * u ^ 4 + 45 * u ^ 3 + 60 * u ^ 2 + 45 * u + 18) ∧
    V p 0 (3 * u ^ 5 + u ^ 4 * v + 15 * u ^ 4 + 4 * u ^ 3 * v + 30 * u ^ 3 + 6 * u ^ 2 * v
        + 30 * u ^ 2 + 4 * u * v + 15 * u + v + 3) := by
  have hu' : ∀ k : ℕ, V p 0 (u ^ k) := fun k => by simpa using V_pow hu k
  refine ⟨?_, ?_, ?_⟩
  · refine V_add (V_add (V_add (V_add (V_add (hu' 5) (V_mul0 (V_ofNat 7) (hu' 4)))
      (V_mul0 (V_ofNat 21) (hu' 3))) (V_mul0 (V_ofNat 35) (hu' 2))) (V_mul0 (V_ofNat 35) hu))
      (V_ofNat 21)
  · refine V_add (V_add (V_add (V_add (V_add (V_mul0 (V_ofNat 3) (hu' 5))
      (V_mul0 (V_ofNat 18) (hu' 4))) (V_mul0 (V_ofNat 45) (hu' 3)))
      (V_mul0 (V_ofNat 60) (hu' 2))) (V_mul0 (V_ofNat 45) hu)) (V_ofNat 18)
  · refine V_add (V_add (V_add (V_add (V_add (V_add (V_add (V_add (V_add (V_add
      (V_mul0 (V_ofNat 3) (hu' 5)) (V_mul0' (hu' 4) hv)) (V_mul0 (V_ofNat 15) (hu' 4)))
      (V_mul0' (V_mul0 (V_ofNat 4) (hu' 3)) hv)) (V_mul0 (V_ofNat 30) (hu' 3)))
      (V_mul0' (V_mul0 (V_ofNat 6) (hu' 2)) hv)) (V_mul0 (V_ofNat 30) (hu' 2)))
      (V_mul0' (V_mul0 (V_ofNat 4) hu) hv)) (V_mul0 (V_ofNat 15) hu)) hv) (V_ofNat 3)

lemma V0_Wprod (m : ℕ) (hm : m ≤ p - 1) : V p 0 (Wprod p m) := by
  unfold Wprod
  apply V_prod
  intro k hk
  rw [mem_range] at hk
  have hlt : k + 1 < p := by have := hp.out.pos; omega
  exact V_add V_one (V_div_succ (V_mul0 (V_ofNat 2) (V_mono (Nat.zero_le _) V_p)) hlt)

/-- The main congruence for primes `p ≥ 7`. -/
theorem main_ge7 (hp7 : 7 ≤ p) : V p 5 ((2187 : ℚ) - (A357674 p : ℚ)) := by
  have hp1 : 1 ≤ p := hp.out.pos
  -- rewrite A357674 p
  have hA : A357674 p = ((3 * p).choose p) ^ 4 *
      (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k) ^ 2) ^ 3 := by
    simp only [A357674]
    rw [S1_eq p hp1]
  have hS2 := S2_rat p hp1
  have hC : ((3 * p).choose p : ℚ) = 3 * Wprod p (p - 1) := by
    rw [choose_3p p hp1, ← choose_3p_eq_Wprod p hp1]; push_cast; ring
  rw [hA, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, hS2, hC]
  set W := Wprod p (p - 1) with hW
  set R := Rsum p with hR
  set H := H2 (p - 1) with hH
  have h1 := hM1 hp7
  have h2 := hM2 hp7
  have hH2 := hV1_H2 hp7
  rw [← hW] at h1
  rw [← hR, ← hH] at h2
  rw [← hH] at h1 hH2
  -- u, v
  set u := W - 1 with hu
  set v := 2 * (p : ℚ) ^ 2 * R * W with hv
  have hp0 : V p 0 (p : ℚ) := V_mono (Nat.zero_le _) V_p
  have hV0W : V p 0 W := V0_Wprod (p - 1) le_rfl
  have hV1R : V p 1 R := by
    have : R = (R - 7 / 2 * H) + 7 / 2 * H := by ring
    rw [this]
    refine V_add (V_mono (by norm_num) h2) ?_
    have : (7 / 2 : ℚ) * H = (7 : ℕ) * H / (2 : ℕ) := by push_cast; ring
    rw [this]
    exact V_div_nat (V_mul0 (V_nat 7) hH2) (not_dvd_of_lt (by norm_num) (by omega))
  have hV3u : V p 3 u := by
    have : u = (W - 1 + 3 * (p : ℚ) ^ 2 * H) - 3 * (p : ℚ) ^ 2 * H := by rw [hu]; ring
    rw [this]
    refine V_sub (V_mono (by norm_num) h1) ?_
    have := V_p_pow_mul (m := 2) hH2
    exact V_of_eq (by ring) (V_mul0 (V_ofNat 3) this)
  have hV3v : V p 3 v := by
    rw [hv]
    have := V_mul0' (V_mul0 (V_ofNat 2) (V_p_pow_mul (m := 2) hV1R)) hV0W
    exact V_of_eq (by ring) this
  have hV0u : V p 0 u := V_mono (Nat.zero_le _) hV3u
  have hV0v : V p 0 v := V_mono (Nat.zero_le _) hV3v
  -- the linear part
  have hlin : V p 5 (7 * u + 3 * v) := by
    have e : 7 * u + 3 * v = 7 * (W - 1 + 3 * (p : ℚ) ^ 2 * H)
        + 6 * ((p : ℚ) ^ 2 * (R - 7 / 2 * H)) + 6 * ((p : ℚ) ^ 2 * (R * u)) := by
      rw [hu, hv]; ring
    rw [e]
    refine V_add (V_add (V_mul0 (V_ofNat 7) h1) ?_) ?_
    · exact V_mul0 (V_ofNat 6) (V_p_pow_mul (m := 2) h2)
    · exact V_mul0 (V_ofNat 6) (V_p_pow_mul (m := 2)
        (V_mul0 (V_mono (Nat.zero_le _) hV1R) hV3u))
  -- assemble
  have e : (2187 : ℚ) - (3 * W) ^ 4 * (3 * W * (1 + 2 * (p : ℚ) ^ 2 * R)) ^ 3 =
      -(2187 : ℚ) * ((1 + u) ^ 4 * (1 + u + v) ^ 3 - 1) := by
    rw [hu, hv]; ring
  rw [e, poly_identity]
  obtain ⟨hP1, hP2, hP3⟩ := V0_poly (p := p) u v hV0u hV0v
  apply V_mul0 (V_neg (V_ofNat 2187))
  refine V_add (V_add (V_add hlin ?_) ?_) ?_
  · exact V_mono (by norm_num) (V_mul0' (V_pow hV3u 2) hP1)
  · exact V_mono (by norm_num) (V_mul0' (V_mul hV3u hV3v) hP2)
  · exact V_mono (by norm_num) (V_mul0' (V_pow hV3v 2) hP3)

end A357674Proof

/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases lt_or_ge p 7 with h7 | h7
  · interval_cases p
    · decide
    · exact absurd hp (by decide)
    · decide
    · exact absurd hp (by decide)
  · have hA1 : A357674 1 = 2187 := by decide
    rw [hA1, Nat.modEq_iff_dvd]
    have key := A357674Proof.main_ge7 (p := p) h7
    have := (A357674Proof.V_int_iff (p := p) 5 ((2187 : ℤ) - (A357674 p : ℤ))).1
      (by push_cast; exact key)
    push_cast
    exact this

theorem A357674_conjecture_1.disproof : ¬ (type_of% @A357674_conjecture_1) := sorry
