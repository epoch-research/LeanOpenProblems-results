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

set_option Elab.async true
set_option linter.all false
set_option linter.unusedSectionVars false


-- ===== From Dev/P1.lean =====

/- # Foundations: p-adic smallness calculus -/


namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

/- Shortcut instances: keep typeclass search on `ℚ_[p]` fast. -/

noncomputable instance : Field ℚ_[p] := inferInstance
noncomputable instance : DivisionRing ℚ_[p] := inferInstance
noncomputable instance : CommRing ℚ_[p] := inferInstance
noncomputable instance : Ring ℚ_[p] := inferInstance
noncomputable instance : CommSemiring ℚ_[p] := inferInstance
noncomputable instance : Semiring ℚ_[p] := inferInstance
noncomputable instance : CommMonoid ℚ_[p] := inferInstance
noncomputable instance : Monoid ℚ_[p] := inferInstance
noncomputable instance : AddCommGroup ℚ_[p] := inferInstance
noncomputable instance : AddCommMonoid ℚ_[p] := inferInstance
noncomputable instance : MonoidWithZero ℚ_[p] := inferInstance
noncomputable instance : HPow ℚ_[p] ℕ ℚ_[p] := inferInstance
noncomputable instance : CharZero ℚ_[p] := inferInstance
noncomputable instance : IsRightCancelMulZero ℚ_[p] := inferInstance
noncomputable instance : NoZeroDivisors ℚ_[p] := inferInstance

/-- `(p : ℝ) ^ (-n)`, the target bound for "divisible by `p^n`". -/
noncomputable def pw (p : ℕ) (n : ℕ) : ℝ := (p : ℝ) ^ (-(n : ℤ))

lemma one_lt_pR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt

lemma pR_pos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos one_lt_pR

lemma pw_pos (n : ℕ) : 0 < pw p n := zpow_pos pR_pos _

lemma pw_nonneg (n : ℕ) : 0 ≤ pw p n := (pw_pos n).le

omit hp in lemma pw_zero : pw p 0 = 1 := by simp [pw]


lemma pw_add (a b : ℕ) : pw p (a + b) = pw p a * pw p b := by
  unfold pw
  rw [← zpow_add₀ (_root_.ne_of_gt pR_pos)]
  congr 1
  push_cast
  ring

lemma pw_anti {a b : ℕ} (h : a ≤ b) : pw p b ≤ pw p a :=
  zpow_le_zpow_right₀ (le_of_lt one_lt_pR) (by omega)

/-- `SM n x` means `x` is "small": `‖x‖ ≤ p^(-n)`, i.e. morally `p^n ∣ x`. -/
def SM (n : ℕ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ pw p n

lemma sm_def {n : ℕ} {x : ℚ_[p]} : SM n x ↔ ‖x‖ ≤ pw p n := Iff.rfl

lemma SM.mono {n m : ℕ} {x : ℚ_[p]} (h : SM n x) (hmn : m ≤ n) : SM m x :=
  le_trans h (pw_anti hmn)

lemma sm_zero_iff {x : ℚ_[p]} : SM 0 x ↔ ‖x‖ ≤ 1 := by
  unfold SM
  rw [pw_zero]

lemma SM.zero (n : ℕ) : SM n (0 : ℚ_[p]) := by
  unfold SM
  rw [norm_zero]
  exact pw_nonneg n

lemma SM.neg {n : ℕ} {x : ℚ_[p]} (h : SM n x) : SM n (-x) := by
  unfold SM at h ⊢
  rwa [norm_neg]

lemma SM.add {n : ℕ} {x y : ℚ_[p]} (hx : SM n x) (hy : SM n y) : SM n (x + y) :=
  le_trans (Padic.nonarchimedean x y) (max_le hx hy)

lemma SM.sub {n : ℕ} {x y : ℚ_[p]} (hx : SM n x) (hy : SM n y) : SM n (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma SM.mul {a b : ℕ} {x y : ℚ_[p]} (hx : SM a x) (hy : SM b y) : SM (a + b) (x * y) := by
  unfold SM at *
  rw [norm_mul, pw_add]
  exact mul_le_mul hx hy (norm_nonneg y) (pw_nonneg a)

lemma SM.mul_left {a : ℕ} {x y : ℚ_[p]} (hy : SM a y) (hx : SM 0 x) : SM a (x * y) := by
  simpa using hx.mul hy

lemma SM.mul_right {a : ℕ} {x y : ℚ_[p]} (hx : SM a x) (hy : SM 0 y) : SM a (x * y) := by
  simpa using hx.mul hy

lemma SM.sum {n : ℕ} {s : Finset ℕ} {f : ℕ → ℚ_[p]} (h : ∀ i ∈ s, SM n (f i)) :
    SM n (∑ i ∈ s, f i) :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pw_nonneg n) h

lemma SM.prod_zero {s : Finset ℕ} {f : ℕ → ℚ_[p]} (h : ∀ i ∈ s, SM 0 (f i)) :
    SM 0 (∏ i ∈ s, f i) := by
  rw [sm_zero_iff, norm_prod]
  apply Finset.prod_le_one
  · intro i _; exact norm_nonneg _
  · intro i hi; exact sm_zero_iff.mp (h i hi)

lemma sm_p : SM 1 (p : ℚ_[p]) := by
  unfold SM pw
  rw [Padic.norm_p]
  norm_num

lemma SM.of_eq {n : ℕ} {x y : ℚ_[p]} (h : SM n x) (e : x = y) : SM n y := e ▸ h

lemma sm_one : SM 0 (1 : ℚ_[p]) := by rw [sm_zero_iff]; exact _root_.le_of_eq norm_one

lemma sm_pow0 {x : ℚ_[p]} (hx : SM 0 x) : ∀ k, SM 0 (x^k)
  | 0 => sm_one.of_eq (pow_zero x).symm
  | (k+1) => ((sm_pow0 hx k).mul hx).of_eq (pow_succ x k).symm

lemma sm_natCast (k : ℕ) : SM 0 (k : ℚ_[p]) := by
  rw [sm_zero_iff]
  exact_mod_cast Padic.norm_int_le_one (k : ℤ)


lemma sm_ofNat (n : ℕ) [n.AtLeastTwo] : SM 0 (OfNat.ofNat n : ℚ_[p]) := by
  have := sm_natCast (p := p) n
  simpa using this

lemma norm_natCast_eq_one {k : ℕ} (h : ¬ p ∣ k) : ‖(k : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma norm_natCast_inv_eq_one {k : ℕ} (h : ¬ p ∣ k) : ‖((k : ℚ_[p]))⁻¹‖ = 1 := by
  rw [norm_inv, norm_natCast_eq_one h]
  norm_num

lemma sm_natCast_inv {k : ℕ} (h : ¬ p ∣ k) : SM 0 ((k : ℚ_[p]))⁻¹ := by
  rw [sm_zero_iff, norm_natCast_inv_eq_one h]

lemma sm_ppow (k : ℕ) : SM k ((p : ℚ_[p])^k) := by
  induction k with
  | zero => simpa using sm_one
  | succ m ih =>
    have h := (sm_p (p := p)).mul ih
    rw [pow_succ]
    have e : (p:ℚ_[p]) * (p:ℚ_[p])^m = (p:ℚ_[p])^m * (p:ℚ_[p]) := by ring
    have h2 : SM (1 + m) ((p:ℚ_[p])^m * (p:ℚ_[p])) := h.of_eq e
    have h3 : SM (m + 1) ((p:ℚ_[p])^m * (p:ℚ_[p])) := h2.mono (by omega)
    exact h3

/-- Division by `p^k`: from `SM (n+k) (p^k * x)` deduce `SM n x`. -/
lemma SM.cancel_ppow {n k : ℕ} {x : ℚ_[p]} (h : SM (n + k) ((p : ℚ_[p])^k * x)) : SM n x := by
  unfold SM at *
  rw [norm_mul, norm_pow, Padic.norm_p, pw_add] at h
  have hpk : pw p k = ((p:ℝ)⁻¹)^k := by
    unfold pw
    rw [zpow_neg, ← inv_zpow, zpow_natCast]
  rw [hpk, mul_comm (pw p n) _] at h
  have hpos : (0:ℝ) < ((p:ℝ)⁻¹)^k := by
    apply pow_pos
    exact inv_pos.mpr pR_pos
  exact le_of_mul_le_mul_left h hpos


/-- Congruence: `MC n x y` means `x ≡ y` mod `p^n` (in norm form). -/
def MC (n : ℕ) (x y : ℚ_[p]) : Prop := SM n (x - y)

lemma mc_def {n : ℕ} {x y : ℚ_[p]} : MC n x y ↔ SM n (x - y) := Iff.rfl

lemma MC.rfl {n : ℕ} {x : ℚ_[p]} : MC n x x := by
  unfold MC; simpa using SM.zero n

lemma MC.of_eq {n : ℕ} {x y : ℚ_[p]} (h : x = y) : MC n x y := by
  unfold MC; rw [h]; simpa using SM.zero n


lemma MC.trans {n : ℕ} {x y z : ℚ_[p]} (h1 : MC n x y) (h2 : MC n y z) : MC n x z := by
  unfold MC at *
  have := SM.add h1 h2
  exact this.of_eq (by ring)

lemma MC.add {n : ℕ} {x x' y y' : ℚ_[p]} (h1 : MC n x x') (h2 : MC n y y') :
    MC n (x + y) (x' + y') := by
  unfold MC at *
  have := SM.add h1 h2
  exact this.of_eq (by ring)



lemma MC.mul {n : ℕ} {x x' y y' : ℚ_[p]} (h1 : MC n x x') (h2 : MC n y y')
    (hx : SM 0 x) (hy' : SM 0 y') : MC n (x * y) (x' * y') := by
  unfold MC at *
  have t1 : SM n (x * (y - y')) := SM.mul_left h2 hx
  have t2 : SM n ((x - x') * y') := SM.mul_right h1 hy'
  have := SM.add t1 t2
  exact this.of_eq (by ring)

lemma MC.mul_left {n : ℕ} {y y' : ℚ_[p]} (z : ℚ_[p]) (h : MC n y y') (hz : SM 0 z) :
    MC n (z * y) (z * y') := by
  unfold MC at *
  have := SM.mul_left h hz
  exact this.of_eq (by ring)

lemma MC.mul_sm {n a : ℕ} {y y' : ℚ_[p]} (z : ℚ_[p]) (h : MC n y y') (hz : SM a z) :
    MC (a + n) (z * y) (z * y') := by
  unfold MC at *
  have := SM.mul hz h
  exact this.of_eq (by ring)

lemma MC.sum {n : ℕ} {s : Finset ℕ} {f g : ℕ → ℚ_[p]} (h : ∀ i ∈ s, MC n (f i) (g i)) :
    MC n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  unfold MC at *
  have : SM n (∑ i ∈ s, (f i - g i)) := SM.sum h
  exact this.of_eq (by rw [Finset.sum_sub_distrib])

lemma MC.mono {n m : ℕ} {x y : ℚ_[p]} (h : MC n x y) (hmn : m ≤ n) : MC m x y :=
  SM.mono h hmn





end A357674


-- ===== From Dev/P2.lean =====

/- # Definitions of harmonic-type sums and Finset manipulation lemmas -/



namespace A357674

variable (p : ℕ) [hp : Fact p.Prime]

/-- `1/k` in `ℚ_p`. -/
noncomputable def iv (k : ℕ) : ℚ_[p] := (k : ℚ_[p])⁻¹

/-- partial harmonic sum `h_{k-1} = ∑_{1 ≤ i < k} 1/i`. -/
noncomputable def hh (k : ℕ) : ℚ_[p] := ∑ i ∈ Ico 1 k, iv p i
noncomputable def qq (k : ℕ) : ℚ_[p] := ∑ i ∈ Ico 1 k, (iv p i)^2
noncomputable def cc (k : ℕ) : ℚ_[p] := ∑ i ∈ Ico 1 k, (iv p i)^3
noncomputable def rr (k : ℕ) : ℚ_[p] := ∑ i ∈ Ico 1 k, (iv p i)^4

/-- tail harmonic sum `∑_{j < t < p} 1/t`. -/
noncomputable def hy (j : ℕ) : ℚ_[p] := ∑ t ∈ Ico (j+1) p, iv p t
noncomputable def qy (j : ℕ) : ℚ_[p] := ∑ t ∈ Ico (j+1) p, (iv p t)^2

/-- second elementary symmetric function of `{1/i : i < k}`. -/
noncomputable def ee2 (k : ℕ) : ℚ_[p] := ((hh p k)^2 - qq p k)/2
/-- second elementary symmetric function of the tail `{1/t : j < t < p}`. -/
noncomputable def ey2 (j : ℕ) : ℚ_[p] := ((hy p j)^2 - qy p j)/2

noncomputable def T1 : ℚ_[p] := ∑ k ∈ Ico 1 p, (iv p k)^2 * hh p k
noncomputable def H21 : ℚ_[p] := ∑ k ∈ Ico 1 p, iv p k * qq p k
noncomputable def H22 : ℚ_[p] := ∑ k ∈ Ico 1 p, (iv p k)^2 * qq p k
noncomputable def H13 : ℚ_[p] := ∑ k ∈ Ico 1 p, (iv p k)^3 * hh p k
noncomputable def H31 : ℚ_[p] := ∑ k ∈ Ico 1 p, iv p k * cc p k
noncomputable def A2 : ℚ_[p] := ∑ k ∈ Ico 1 p, (iv p k)^2 * (hh p k)^2
noncomputable def E2s : ℚ_[p] := ∑ k ∈ Ico 1 p, (iv p k)^2 * ee2 p k

variable {p}

/- ## Basic norm facts -/

lemma not_dvd_of_mem_Ico {i : ℕ} (h : i ∈ Ico 1 p) : ¬ p ∣ i := by
  rw [mem_Ico] at h
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

lemma sm_iv {i : ℕ} (h : i ∈ Ico 1 p) : SM 0 (iv p i) :=
  sm_natCast_inv (not_dvd_of_mem_Ico h)

lemma sm_iv_pow {i : ℕ} (h : i ∈ Ico 1 p) (m : ℕ) : SM 0 ((iv p i)^m) := by
  rw [sm_zero_iff, norm_pow]
  unfold iv
  rw [norm_natCast_inv_eq_one (not_dvd_of_mem_Ico h)]
  exact _root_.le_of_eq (_root_.one_pow m)

lemma iv_ne_zero {i : ℕ} (h : i ∈ Ico 1 p) : (i : ℚ_[p]) ≠ 0 := by
  intro h0
  have := norm_natCast_eq_one (p := p) (not_dvd_of_mem_Ico h)
  rw [h0, norm_zero] at this
  exact zero_ne_one this

lemma Ico_subset_of_le {k : ℕ} (h : k ≤ p) : Ico 1 k ⊆ Ico 1 p := by
  apply Finset.Ico_subset_Ico le_rfl h

lemma sm_hh {k : ℕ} (h : k ≤ p) : SM 0 (hh p k) :=
  SM.sum fun i hi => sm_iv (Ico_subset_of_le h hi)

lemma sm_qq {k : ℕ} (h : k ≤ p) : SM 0 (qq p k) :=
  SM.sum fun i hi => sm_iv_pow (Ico_subset_of_le h hi) 2



lemma sm_hy (j : ℕ) : SM 0 (hy p j) := by
  apply SM.sum
  intro t ht
  rw [mem_Ico] at ht
  exact sm_iv (by rw [mem_Ico]; omega)

lemma sm_qy (j : ℕ) : SM 0 (qy p j) := by
  apply SM.sum
  intro t ht
  rw [mem_Ico] at ht
  exact sm_iv_pow (by rw [mem_Ico]; omega) 2

lemma sm_two_inv (hp2 : p ≠ 2) : SM 0 ((2 : ℚ_[p]))⁻¹ := by
  have h := sm_natCast_inv (p := p) (k := 2) (by
    intro hdvd
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 := hp.out.two_le
    omega)
  rwa [Nat.cast_ofNat] at h

/- ## Sum splitting: `(∑f)(∑g) = ∑ f·(prefix g) + ∑ g·(prefix f) + ∑ fg` -/

lemma sum_mul_sum_split (n : ℕ) (f g : ℕ → ℚ_[p]) :
    (∑ k ∈ Ico 1 n, f k) * (∑ k ∈ Ico 1 n, g k)
      = (∑ k ∈ Ico 1 n, f k * ∑ i ∈ Ico 1 k, g i)
        + (∑ k ∈ Ico 1 n, g k * ∑ i ∈ Ico 1 k, f i)
        + ∑ k ∈ Ico 1 n, f k * g k := by
  induction n with
  | zero =>
    rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1)]
    simp only [Finset.sum_empty, mul_zero, add_zero]
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with hm | hm
    · have h0 : m = 0 := by omega
      subst h0
      rw [show (0:ℕ)+1 = 1 from rfl, Finset.Ico_self]
      simp only [Finset.sum_empty, mul_zero, add_zero]
    · rw [Finset.sum_Ico_succ_top hm f, Finset.sum_Ico_succ_top hm g,
        Finset.sum_Ico_succ_top hm (fun k => f k * ∑ i ∈ Ico 1 k, g i),
        Finset.sum_Ico_succ_top hm (fun k => g k * ∑ i ∈ Ico 1 k, f i),
        Finset.sum_Ico_succ_top hm (fun k => f k * g k)]
      rw [add_mul, mul_add, mul_add, ih]
      ring

/- ## Prefix-sum swap -/

lemma sum_swap_prefix (N : ℕ) (F : ℕ → ℚ_[p]) :
    ∑ k ∈ range N, ∑ j ∈ Ico 1 (k+1), F j
      = ∑ j ∈ Ico 1 N, ((N : ℚ_[p]) - (j : ℚ_[p])) * F j := by
  induction N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty,
      Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge m 1 with hm | hm
    · have h0 : m = 0 := by omega
      subst h0
      rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), show (0:ℕ)+1 = 1 from rfl,
        Finset.Ico_self]
      simp only [Finset.sum_empty, add_zero]
    · rw [Finset.sum_Ico_succ_top hm F,
        Finset.sum_Ico_succ_top hm (fun j => (((m+1:ℕ) : ℚ_[p]) - (j:ℚ_[p])) * F j)]
      have hA : ∑ j ∈ Ico 1 m, (((m+1:ℕ):ℚ_[p]) - (j:ℚ_[p])) * F j
          = (∑ j ∈ Ico 1 m, ((m:ℚ_[p]) - (j:ℚ_[p])) * F j) + ∑ j ∈ Ico 1 m, F j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        ring
      have hB : (((m+1:ℕ):ℚ_[p]) - ((m:ℕ):ℚ_[p])) * F m = F m := by
        push_cast
        ring
      rw [hA, hB]
      ring

/- ## Reflection `k ↦ p - k` -/

lemma sum_reflect (F : ℕ → ℚ_[p]) :
    ∑ k ∈ Ico 1 p, F k = ∑ k ∈ Ico 1 p, F (p - k) := by
  apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
  · intro a ha; rw [mem_Ico] at *; omega
  · intro a ha; rw [mem_Ico] at *; omega
  · intro a ha; rw [mem_Ico] at ha; omega
  · intro a ha; rw [mem_Ico] at ha; omega
  · intro a ha
    rw [mem_Ico] at ha
    rw [show p - (p - a) = a by omega]

/-- Double reflection for strictly-nested double sums. -/
lemma sum_reflect2 (F : ℕ → ℕ → ℚ_[p]) :
    ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, F a b
      = ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, F (p - b) (p - a) := by
  rw [Finset.sum_sigma' (Ico 1 p) (fun b => Ico 1 b) (fun b a => F a b),
    Finset.sum_sigma' (Ico 1 p) (fun b => Ico 1 b) (fun b a => F (p - b) (p - a))]
  apply Finset.sum_nbij' (fun x => ⟨p - x.2, p - x.1⟩) (fun x => ⟨p - x.2, p - x.1⟩)
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, mem_Ico] at *
    omega
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, mem_Ico] at *
    omega
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, mem_Ico] at hx
    simp only [Sigma.mk.inj_iff, heq_eq_eq]
    constructor <;> omega
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, mem_Ico] at hx
    simp only [Sigma.mk.inj_iff, heq_eq_eq]
    constructor <;> omega
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, mem_Ico] at hx
    show F a b = F (p - (p - a)) (p - (p - b))
    rw [show p - (p - a) = a by omega, show p - (p - b) = b by omega]

/- ## Prefix recurrences -/

lemma hh_succ {k : ℕ} (hk : 1 ≤ k) : hh p (k+1) = hh p k + iv p k := by
  unfold hh
  rw [Finset.sum_Ico_succ_top hk]

lemma qq_succ {k : ℕ} (hk : 1 ≤ k) : qq p (k+1) = qq p k + (iv p k)^2 := by
  unfold qq
  rw [Finset.sum_Ico_succ_top hk]

lemma hh_split {j : ℕ} (h1 : 1 ≤ j + 1) (h2 : j + 1 ≤ p) : hh p p = hh p (j+1) + hy p j := by
  unfold hh hy
  rw [← Finset.sum_Ico_consecutive _ h1 h2]

lemma qq_split {j : ℕ} (h1 : 1 ≤ j + 1) (h2 : j + 1 ≤ p) : qq p p = qq p (j+1) + qy p j := by
  unfold qq qy
  rw [← Finset.sum_Ico_consecutive _ h1 h2]

/- ## Stuffle-type exact identities -/

/-- `qq² = 2·H22 + rr` (square splitting). -/
lemma H22_eq : H22 p = ((qq p p)^2 - rr p p) / 2 := by
  have h := sum_mul_sum_split p (fun k => (iv p k)^2) (fun k => (iv p k)^2)
  have e : (∑ k ∈ Ico 1 p, (iv p k)^2 * (iv p k)^2) = rr p p := by
    unfold rr
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h1 : (∑ k ∈ Ico 1 p, (iv p k)^2 * ∑ i ∈ Ico 1 k, (iv p i)^2) = H22 p := rfl
  have h2 : (∑ k ∈ Ico 1 p, (iv p k)^2) = qq p p := rfl
  rw [e, h1, h2] at h
  linear_combination -h / 2

/-- `hh·cc = H31 + H13 + rr`. -/
lemma H31_add_H13 : H31 p + H13 p = hh p p * cc p p - rr p p := by
  have h := sum_mul_sum_split p (fun k => iv p k) (fun k => (iv p k)^3)
  have e : (∑ k ∈ Ico 1 p, iv p k * (iv p k)^3) = rr p p := by
    unfold rr
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h1 : (∑ k ∈ Ico 1 p, iv p k * ∑ i ∈ Ico 1 k, (iv p i)^3) = H31 p := rfl
  have h2 : (∑ k ∈ Ico 1 p, (iv p k)^3 * ∑ i ∈ Ico 1 k, iv p i) = H13 p := rfl
  have h3 : (∑ k ∈ Ico 1 p, iv p k) = hh p p := rfl
  have h4 : (∑ k ∈ Ico 1 p, (iv p k)^3) = cc p p := rfl
  rw [e, h1, h2, h3, h4] at h
  linear_combination -h

/-- `A2 = H22 + 2·E2s` (definitional unfolding of `ee2`). -/
lemma A2_eq : A2 p = H22 p + 2 * E2s p := by
  unfold A2 H22 E2s ee2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end A357674


-- ===== From Dev/P3.lean =====

/- # Product truncation lemmas -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

/- ## Symmetric function shorthands -/

noncomputable def ES1 (S : Finset ℕ) (f : ℕ → ℚ_[p]) : ℚ_[p] := ∑ i ∈ S, f i
noncomputable def PS (m : ℕ) (S : Finset ℕ) (f : ℕ → ℚ_[p]) : ℚ_[p] := ∑ i ∈ S, (f i)^m
noncomputable def ES2 (S : Finset ℕ) (f : ℕ → ℚ_[p]) : ℚ_[p] :=
  ((ES1 S f)^2 - PS 2 S f)/2
noncomputable def ES3 (S : Finset ℕ) (f : ℕ → ℚ_[p]) : ℚ_[p] :=
  ((ES1 S f)^3 - 3*(ES1 S f)*(PS 2 S f) + 2*(PS 3 S f))/6
noncomputable def ES4 (S : Finset ℕ) (f : ℕ → ℚ_[p]) : ℚ_[p] :=
  ((ES1 S f)^4 - 6*(ES1 S f)^2*(PS 2 S f) + 3*(PS 2 S f)^2
    + 8*(ES1 S f)*(PS 3 S f) - 6*(PS 4 S f))/24

lemma ES1_cons {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : ℕ → ℚ_[p]) :
    ES1 (cons a S ha) f = ES1 S f + f a := by
  unfold ES1; rw [Finset.sum_cons]; ring

lemma PS_cons {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (m : ℕ) (f : ℕ → ℚ_[p]) :
    PS m (cons a S ha) f = PS m S f + (f a)^m := by
  unfold PS; rw [Finset.sum_cons]; ring

lemma ES2_cons {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : ℕ → ℚ_[p]) :
    ES2 (cons a S ha) f = ES2 S f + f a * ES1 S f := by
  unfold ES2
  rw [ES1_cons ha, PS_cons ha]
  ring

lemma ES3_cons {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : ℕ → ℚ_[p]) :
    ES3 (cons a S ha) f = ES3 S f + f a * ES2 S f := by
  unfold ES3 ES2
  rw [ES1_cons ha, PS_cons ha, PS_cons ha]
  ring

lemma ES4_cons {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : ℕ → ℚ_[p]) :
    ES4 (cons a S ha) f = ES4 S f + f a * ES3 S f := by
  unfold ES4 ES3
  rw [ES1_cons ha, PS_cons ha, PS_cons ha, PS_cons ha]
  ring

/- ## Norm bounds on symmetric functions -/

lemma not_dvd_two (hp7 : 7 ≤ p) : ¬ (p ∣ 2) := by
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

lemma not_dvd_six (hp7 : 7 ≤ p) : ¬ (p ∣ 6) := by
  intro h
  have h1 : p ∣ 2 * 3 := by norm_num at h ⊢; exact h
  rcases (Nat.Prime.dvd_mul hp.out).mp h1 with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega

lemma not_dvd_24 (hp7 : 7 ≤ p) : ¬ (p ∣ 24) := by
  intro h
  have h1 : p ∣ 2^3 * 3 := by norm_num at h ⊢; exact h
  rcases (Nat.Prime.dvd_mul hp.out).mp h1 with h2 | h3
  · have hd := Nat.Prime.dvd_of_dvd_pow hp.out h2
    have := Nat.le_of_dvd (by norm_num) hd; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega

lemma sm_div_nat {n : ℕ} {x : ℚ_[p]} {c : ℕ} (hx : SM n x) (hc : ¬ p ∣ c) :
    SM n (x / (c : ℚ_[p])) := by
  rw [div_eq_mul_inv]
  exact hx.mul_right (sm_natCast_inv hc)

lemma sm_ES1 {S : Finset ℕ} {f : ℕ → ℚ_[p]} (hf : ∀ i ∈ S, SM 0 (f i)) : SM 0 (ES1 S f) :=
  SM.sum hf

lemma sm_PS {S : Finset ℕ} {f : ℕ → ℚ_[p]} (hf : ∀ i ∈ S, SM 0 (f i)) (m : ℕ) :
    SM 0 (PS m S f) := by
  apply SM.sum
  intro i hi
  rw [sm_zero_iff, norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  exact sm_zero_iff.mp (hf i hi)

lemma sm_ES2 (hp7 : 7 ≤ p) {S : Finset ℕ} {f : ℕ → ℚ_[p]} (hf : ∀ i ∈ S, SM 0 (f i)) :
    SM 0 (ES2 S f) := by
  have e1 := sm_ES1 hf
  have t1 : SM 0 ((ES1 S f)^2) := (e1.mul e1).of_eq (by ring)
  have h : SM 0 ((ES1 S f)^2 - PS 2 S f) := t1.sub (sm_PS hf 2)
  have := sm_div_nat (c := 2) h (not_dvd_two hp7)
  unfold ES2
  exact this.of_eq (by push_cast; ring)


lemma sm_ES4 (hp7 : 7 ≤ p) {S : Finset ℕ} {f : ℕ → ℚ_[p]} (hf : ∀ i ∈ S, SM 0 (f i)) :
    SM 0 (ES4 S f) := by
  have e1 := sm_ES1 hf
  have p2 := sm_PS hf 2
  have p3 := sm_PS hf 3
  have p4 := sm_PS hf 4
  have t1 : SM 0 ((ES1 S f)^4) := (((e1.mul e1).mul e1).mul e1).of_eq (by ring)
  have t2 : SM 0 (6*(ES1 S f)^2*(PS 2 S f)) :=
    ((((sm_ofNat 6).mul e1).mul e1).mul p2).of_eq (by ring)
  have t3 : SM 0 (3*(PS 2 S f)^2) := (((sm_ofNat 3).mul p2).mul p2).of_eq (by ring)
  have t4 : SM 0 (8*(ES1 S f)*(PS 3 S f)) := (((sm_ofNat 8).mul e1).mul p3).of_eq (by ring)
  have t5 : SM 0 (6*(PS 4 S f)) := ((sm_ofNat 6).mul p4).of_eq (by ring)
  have h : SM 0 ((ES1 S f)^4 - 6*(ES1 S f)^2*(PS 2 S f) + 3*(PS 2 S f)^2
      + 8*(ES1 S f)*(PS 3 S f) - 6*(PS 4 S f)) := (((t1.sub t2).add t3).add t4).sub t5
  have := sm_div_nat (c := 24) h (not_dvd_24 hp7)
  unfold ES4
  exact this.of_eq (by push_cast; ring)

lemma sm_prod_one_add {S : Finset ℕ} {f : ℕ → ℚ_[p]} {c : ℚ_[p]}
    (hf : ∀ i ∈ S, SM 0 (f i)) (hc : SM 0 c) :
    SM 0 (∏ i ∈ S, (1 + c * f i)) := by
  apply SM.prod_zero
  intro i hi
  exact (sm_one.add (hc.mul_left (hf i hi) |>.of_eq (by ring)))

/- ## The truncation lemmas -/

lemma MC.of_sub {n : ℕ} {x y d : ℚ_[p]} (h : x - y = d) (hd : SM n d) : MC n x y :=
  mc_def.mpr (hd.of_eq h.symm)

/-- Order-2 truncation: `∏(1+c·fᵢ) ≡ 1 + c·e₁ + c²·e₂ (mod c³)`. -/
lemma prod_trunc2 {a : ℕ} {S : Finset ℕ} {f : ℕ → ℚ_[p]} {c : ℚ_[p]} (hp7 : 7 ≤ p)
    (hf : ∀ i ∈ S, SM 0 (f i)) (hc : SM a c) :
    MC (3*a) (∏ i ∈ S, (1 + c * f i)) (1 + c * ES1 S f + c^2 * ES2 S f) := by
  induction S using Finset.cons_induction with
  | empty =>
    apply MC.of_eq
    simp only [ES1, ES2, PS, Finset.prod_empty, Finset.sum_empty]
    ring
  | cons b S hb ih =>
    have hfb : SM 0 (f b) := hf b (Finset.mem_cons_self b S)
    have hfS : ∀ i ∈ S, SM 0 (f i) := fun i hi => hf i (Finset.mem_cons_of_mem hi)
    have hc0 : SM 0 c := hc.mono (Nat.zero_le a)
    have h1pc : SM 0 (1 + c * f b) := sm_one.add (hc0.mul_left hfb |>.of_eq (by ring))
    rw [Finset.prod_cons, ES1_cons hb, ES2_cons hb]
    have step1 : MC (3*a) ((1 + c * f b) * ∏ i ∈ S, (1 + c * f i))
        ((1 + c * f b) * (1 + c * ES1 S f + c^2 * ES2 S f)) :=
      MC.mul_left _ (ih hfS) h1pc
    have herr : SM (3*a) (c * (c * c) * (f b * ES2 S f)) := by
      have h1 : SM (a + (a + a)) (c * (c * c)) := hc.mul (hc.mul hc)
      have h2 : SM 0 (f b * ES2 S f) := hfb.mul (sm_ES2 hp7 hfS)
      have := h1.mul h2
      have e : a + (a + a) + 0 = 3 * a := by ring
      exact (e ▸ this)
    have step2 : MC (3*a) ((1 + c * f b) * (1 + c * ES1 S f + c^2 * ES2 S f))
        (1 + c * (ES1 S f + f b) + c^2 * (ES2 S f + f b * ES1 S f)) :=
      MC.of_sub (by ring) herr
    exact step1.trans step2

/-- Order-4 truncation: `∏(1+c·fᵢ) ≡ 1 + c·e₁ + c²·e₂ + c³·e₃ + c⁴·e₄ (mod c⁵)`. -/
lemma prod_trunc4 {a : ℕ} {S : Finset ℕ} {f : ℕ → ℚ_[p]} {c : ℚ_[p]} (hp7 : 7 ≤ p)
    (hf : ∀ i ∈ S, SM 0 (f i)) (hc : SM a c) :
    MC (5*a) (∏ i ∈ S, (1 + c * f i))
      (1 + c * ES1 S f + c^2 * ES2 S f + c^3 * ES3 S f + c^4 * ES4 S f) := by
  induction S using Finset.cons_induction with
  | empty =>
    apply MC.of_eq
    simp only [ES1, ES2, ES3, ES4, PS, Finset.prod_empty, Finset.sum_empty]
    ring
  | cons b S hb ih =>
    have hfb : SM 0 (f b) := hf b (Finset.mem_cons_self b S)
    have hfS : ∀ i ∈ S, SM 0 (f i) := fun i hi => hf i (Finset.mem_cons_of_mem hi)
    have hc0 : SM 0 c := hc.mono (Nat.zero_le a)
    have h1pc : SM 0 (1 + c * f b) := sm_one.add (hc0.mul_left hfb |>.of_eq (by ring))
    rw [Finset.prod_cons, ES1_cons hb, ES2_cons hb, ES3_cons hb, ES4_cons hb]
    have step1 : MC (5*a) ((1 + c * f b) * ∏ i ∈ S, (1 + c * f i))
        ((1 + c * f b) * (1 + c * ES1 S f + c^2 * ES2 S f + c^3 * ES3 S f + c^4 * ES4 S f)) :=
      MC.mul_left _ (ih hfS) h1pc
    have herr : SM (5*a) (c * (c * (c * (c * c))) * (f b * ES4 S f)) := by
      have h1 : SM (a + (a + (a + (a + a)))) (c * (c * (c * (c * c)))) :=
        hc.mul (hc.mul (hc.mul (hc.mul hc)))
      have h2 : SM 0 (f b * ES4 S f) := hfb.mul (sm_ES4 hp7 hfS)
      have := h1.mul h2
      have e : a + (a + (a + (a + a))) + 0 = 5 * a := by ring
      exact (e ▸ this)
    have step2 : MC (5*a) ((1 + c * f b) *
          (1 + c * ES1 S f + c^2 * ES2 S f + c^3 * ES3 S f + c^4 * ES4 S f))
        (1 + c * (ES1 S f + f b) + c^2 * (ES2 S f + f b * ES1 S f)
          + c^3 * (ES3 S f + f b * ES2 S f) + c^4 * (ES4 S f + f b * ES3 S f)) :=
      MC.of_sub (by ring) herr
    exact step1.trans step2

end A357674


-- ===== From Dev/P4.lean =====

/- # Binomial coefficients as products -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma cast_nat_ne_zero {n : ℕ} (h : n ≠ 0) : ((n : ℚ_[p])) ≠ 0 :=
  Nat.cast_ne_zero.mpr h

lemma iv_mul_cancel {k : ℕ} (h : k ≠ 0) : iv p k * (k : ℚ_[p]) = 1 := by
  unfold iv
  exact inv_mul_cancel₀ (cast_nat_ne_zero h)

/-- `C(N+k, k) = ∏_{i=1}^{k} (1 + N/i)`, valid for all `N, k`. -/
lemma choose_prod_gen (N : ℕ) : ∀ k : ℕ,
    (((N + k).choose k : ℕ) : ℚ_[p]) = ∏ i ∈ Ico 1 (k+1), (1 + (N:ℚ_[p]) * iv p i) := by
  intro k
  induction k with
  | zero => rw [Nat.choose_zero_right, Nat.cast_one, Finset.Ico_self, Finset.prod_empty]
  | succ m ih =>
    have hrec : (N + m + 1) * ((N + m).choose m) = ((N + m + 1).choose (m+1)) * (m+1) :=
      Nat.add_one_mul_choose_eq (N + m) m
    have hcast : ((N + m + 1 : ℕ) : ℚ_[p]) * (((N + m).choose m : ℕ) : ℚ_[p])
        = (((N + m + 1).choose (m+1) : ℕ) : ℚ_[p]) * ((m + 1 : ℕ) : ℚ_[p]) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hrec]
    have hm1 : ((m + 1 : ℕ) : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
    have hivj : iv p (m+1) * ((m+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
    have hx : (1 + (N:ℚ_[p]) * iv p (m+1)) * ((m+1 : ℕ) : ℚ_[p])
        = ((m+1 : ℕ) : ℚ_[p]) + N := by
      have : (1 + (N:ℚ_[p]) * iv p (m+1)) * ((m+1 : ℕ) : ℚ_[p])
          = ((m+1 : ℕ) : ℚ_[p]) + (N:ℚ_[p]) * (iv p (m+1) * ((m+1 : ℕ) : ℚ_[p])) := by ring
      rw [this, hivj]
      ring
    rw [show N + (m+1) = N + m + 1 by omega, Finset.prod_Ico_succ_top (by omega : 1 ≤ m + 1),
      ← ih]
    apply mul_right_cancel₀ hm1
    push_cast at hcast hx ⊢
    linear_combination -hcast - (((N + m).choose m : ℕ) : ℚ_[p]) * hx

/-- `C(p-1, k) = (-1)^k ∏_{i=1}^{k} (1 - p/i)` for `k ≤ p - 1`. -/
lemma choose_prod_sign : ∀ k : ℕ, k ≤ p - 1 →
    (((p - 1).choose k : ℕ) : ℚ_[p])
      = (-1)^k * ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.choose_zero_right, Nat.cast_one, pow_zero, Finset.Ico_self,
      Finset.prod_empty, mul_one]
  | succ m ih =>
    intro hm1
    have hm : m ≤ p - 1 := by omega
    have hp1 : 1 ≤ p := hp.out.pos
    have hrec : ((p-1).choose (m+1)) * (m+1) = ((p-1).choose m) * (p - 1 - m) :=
      Nat.choose_succ_right_eq (p-1) m
    have hcast : (((p-1).choose (m+1) : ℕ) : ℚ_[p]) * ((m+1 : ℕ) : ℚ_[p])
        = (((p-1).choose m : ℕ) : ℚ_[p]) * ((p - 1 - m : ℕ) : ℚ_[p]) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hrec]
    have hsub : ((p - 1 - m : ℕ) : ℚ_[p]) = (p : ℚ_[p]) - 1 - (m : ℚ_[p]) := by
      have h1 : ((p - 1 - m : ℕ) : ℚ_[p]) = ((p - 1 : ℕ) : ℚ_[p]) - (m : ℚ_[p]) :=
        Nat.cast_sub (by omega)
      have h2 : ((p - 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) - 1 := by
        rw [Nat.cast_sub hp1, Nat.cast_one]
      rw [h1, h2]
    have hm1' : ((m + 1 : ℕ) : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
    have hivj : iv p (m+1) * ((m+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
    have hx : (1 - (p:ℚ_[p]) * iv p (m+1)) * ((m+1 : ℕ) : ℚ_[p])
        = ((m+1 : ℕ) : ℚ_[p]) - p := by
      have : (1 - (p:ℚ_[p]) * iv p (m+1)) * ((m+1 : ℕ) : ℚ_[p])
          = ((m+1 : ℕ) : ℚ_[p]) - (p:ℚ_[p]) * (iv p (m+1) * ((m+1 : ℕ) : ℚ_[p])) := by ring
      rw [this, hivj]
      ring
    rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ m + 1)]
    apply mul_right_cancel₀ hm1'
    rw [hcast, hsub, ih hm]
    push_cast at hx ⊢
    linear_combination ((-1:ℚ_[p]))^m * (∏ i ∈ Ico 1 (m+1), (1 - (p:ℚ_[p]) * iv p i)) * hx

/- ## Specific product forms -/

/-- `C(2p-1, p-1) = ∏_{i<p}(1+p/i)`. -/
lemma binom_2pm1 : (((2*p - 1).choose (p-1) : ℕ) : ℚ_[p])
    = ∏ i ∈ Ico 1 p, (1 + (p:ℚ_[p]) * iv p i) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have h := choose_prod_gen (p := p) p (p - 1)
  rw [show p + (p - 1) = 2*p - 1 by omega] at h
  rw [show (p - 1) + 1 = p by omega] at h
  exact h

/-- `C(3p, p) = 3 ∏_{i<p}(1+2p/i)`. -/
lemma binom_3p : (((3*p).choose p : ℕ) : ℚ_[p])
    = 3 * ∏ i ∈ Ico 1 p, (1 + (2*p:ℚ_[p]) * iv p i) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have h := choose_prod_gen (p := p) (2*p) p
  rw [show 2*p + p = 3*p by omega] at h
  rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ p)] at h
  have hivp : iv p p * ((p : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
  have hiv : (1 + ((2*p : ℕ):ℚ_[p]) * iv p p) = 3 := by
    have e : (1 + ((2*p : ℕ):ℚ_[p]) * iv p p)
        = 1 + 2 * (iv p p * ((p:ℕ) : ℚ_[p])) := by push_cast; ring
    rw [e, hivp]
    norm_num
  rw [hiv] at h
  rw [h]
  have : ((2*p : ℕ) : ℚ_[p]) = (2*p : ℚ_[p]) := by push_cast; ring
  rw [this]
  ring

/-- `C(3p-1, 2p) = ∏_{i<p}(1+2p/i)`. -/
lemma binom_3pm1 : (((3*p - 1).choose (2*p) : ℕ) : ℚ_[p])
    = ∏ i ∈ Ico 1 p, (1 + (2*p:ℚ_[p]) * iv p i) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have hsymm : (3*p - 1).choose (2*p) = (3*p - 1).choose (p - 1) := by
    rw [← Nat.choose_symm (by omega : 2*p ≤ 3*p - 1)]
    congr 1
    omega
  rw [hsymm]
  have h := choose_prod_gen (p := p) (2*p) (p - 1)
  rw [show 2*p + (p - 1) = 3*p - 1 by omega] at h
  rw [show (p - 1) + 1 = p by omega] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  have : ((2*p : ℕ) : ℚ_[p]) = (2*p : ℚ_[p]) := by push_cast; ring
  rw [this]

/-- Main-range: `C(p+k-1, k) = (p/k)·∏_{i<k}(1+p/i)` for `1 ≤ k`. -/
lemma binom_main {k : ℕ} (hk : 1 ≤ k) : (((p + k - 1).choose k : ℕ) : ℚ_[p])
    = (p:ℚ_[p]) * iv p k * ∏ i ∈ Ico 1 k, (1 + (p:ℚ_[p]) * iv p i) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hrec : ((p + j).choose (j+1)) * (j+1) = ((p + j).choose j) * (p + j - j) :=
    Nat.choose_succ_right_eq (p + j) j
  rw [show p + j - j = p by omega] at hrec
  have h := choose_prod_gen (p := p) p j
  have hcast : (((p + j).choose (j+1) : ℕ) : ℚ_[p]) * ((j+1 : ℕ) : ℚ_[p])
      = (((p + j).choose j : ℕ) : ℚ_[p]) * ((p : ℕ) : ℚ_[p]) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ_[p])) hrec
  have hj1 : ((j + 1 : ℕ) : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
  have hivj : iv p (j+1) * ((j+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
  rw [show p + (j+1) - 1 = p + j by omega]
  apply mul_right_cancel₀ hj1
  rw [hcast, h]
  push_cast at hivj ⊢
  linear_combination
    -((p:ℚ_[p]) * ∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i)) * hivj

end A357674


-- ===== From Dev/P4b.lean =====

/- # The k = p+j binomial product formula and hockey stick -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma cast_factorial_ne_zero (n : ℕ) : ((Nat.factorial n : ℕ) : ℚ_[p]) ≠ 0 :=
  cast_nat_ne_zero (Nat.factorial_ne_zero n)

/-- Factorial-based identity:
`C(2p+j-1, p+j) * j * C(p+j, j) = 2p * C(2p+j-1, j-1) * C(2p-1, p-1)` for `1 ≤ j`. -/
lemma td_factorial_identity {j : ℕ} (hj : 1 ≤ j) :
    (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p]) * (j : ℚ_[p])
        * (((p + j).choose j : ℕ) : ℚ_[p])
      = 2 * (p:ℚ_[p]) * (((2*p + j - 1).choose (j - 1) : ℕ) : ℚ_[p])
        * (((2*p - 1).choose (p - 1) : ℕ) : ℚ_[p]) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have c1 : (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])
      = ((2*p + j - 1)! : ℚ_[p]) / (((p+j)! : ℚ_[p]) * ((p-1)! : ℚ_[p])) := by
    rw [Nat.cast_choose ℚ_[p] (by omega : p + j ≤ 2*p + j - 1),
      show 2*p + j - 1 - (p + j) = p - 1 by omega]
  have c2 : (((p + j).choose j : ℕ) : ℚ_[p])
      = ((p+j)! : ℚ_[p]) / ((j ! : ℚ_[p]) * ((p)! : ℚ_[p])) := by
    rw [Nat.cast_choose ℚ_[p] (by omega : j ≤ p + j),
      show p + j - j = p by omega]
  have c3 : (((2*p + j - 1).choose (j - 1) : ℕ) : ℚ_[p])
      = ((2*p + j - 1)! : ℚ_[p]) / (((j-1)! : ℚ_[p]) * ((2*p)! : ℚ_[p])) := by
    rw [Nat.cast_choose ℚ_[p] (by omega : j - 1 ≤ 2*p + j - 1),
      show 2*p + j - 1 - (j - 1) = 2*p by omega]
  have c4 : (((2*p - 1).choose (p - 1) : ℕ) : ℚ_[p])
      = ((2*p - 1)! : ℚ_[p]) / (((p-1)! : ℚ_[p]) * ((p)! : ℚ_[p])) := by
    rw [Nat.cast_choose ℚ_[p] (by omega : p - 1 ≤ 2*p - 1),
      show 2*p - 1 - (p - 1) = p by omega]
  have fj : (j ! : ℚ_[p]) = (j : ℚ_[p]) * ((j-1)! : ℚ_[p]) := by
    have h := Nat.mul_factorial_pred (by omega : j ≠ 0)
    rw [← h, Nat.cast_mul]
  have f2p : ((2*p)! : ℚ_[p]) = 2 * (p:ℚ_[p]) * ((2*p - 1)! : ℚ_[p]) := by
    have h := Nat.mul_factorial_pred (by omega : 2*p ≠ 0)
    rw [← h, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [c1, c2, c3, c4, fj, f2p]
  have n1 := cast_factorial_ne_zero (p := p) (2*p + j - 1)
  have n2 := cast_factorial_ne_zero (p := p) (p + j)
  have n3 := cast_factorial_ne_zero (p := p) (p - 1)
  have n4 := cast_factorial_ne_zero (p := p) (j - 1)
  have n5 := cast_factorial_ne_zero (p := p) (2*p - 1)
  have n6 := cast_factorial_ne_zero (p := p) p
  have nj : (j : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
  have np : ((p : ℕ) : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
  field_simp

/-- The `k = p+j` product form, `1 ≤ j < p`:
`C(2p+j-1, p+j) = 2p·(1/j)·∏_{u<j}(1+2p/u)·∏_{j<t<p}(1+p/t)`. -/
lemma binom_td {j : ℕ} (hj : j ∈ Ico 1 p) :
    (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])
      = 2 * (p:ℚ_[p]) * iv p j * (∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
        * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t) := by
  rw [mem_Ico] at hj
  have hp1 : 1 ≤ p := hp.out.pos
  have key := td_factorial_identity (p := p) (j := j) (by omega)
  -- C(p+j, j) = ∏_{i ∈ Ico 1 (j+1)}
  have hJ : (((p + j).choose j : ℕ) : ℚ_[p]) = ∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i) :=
    choose_prod_gen p j
  -- C(2p+j-1, j-1) = ∏_{u ∈ Ico 1 j}
  have hK : (((2*p + j - 1).choose (j - 1) : ℕ) : ℚ_[p])
      = ∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u) := by
    have h := choose_prod_gen (p := p) (2*p) (j - 1)
    rw [show 2*p + (j-1) = 2*p + j - 1 by omega, show (j-1)+1 = j by omega] at h
    rw [h]
    apply Finset.prod_congr rfl
    intro u _
    norm_num
  -- C(2p-1, p-1) = ∏_{Ico 1 p} = ∏_{Ico 1 (j+1)} * ∏_{Ico (j+1) p}
  have hsplit : (∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i))
        * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t)
      = ∏ i ∈ Ico 1 p, (1 + (p:ℚ_[p]) * iv p i) :=
    Finset.prod_Ico_consecutive _ (by omega) (by omega)
  have hD : (((2*p - 1).choose (p - 1) : ℕ) : ℚ_[p])
      = (∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i))
        * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t) := by
    rw [binom_2pm1, ← hsplit]
  rw [hJ, hK, hD] at key
  -- key : C · j · ∏J = 2p · ∏K · (∏J · ∏Y)
  have hJne : (∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i)) ≠ 0 := by
    have := hJ ▸ cast_nat_ne_zero (p := p) (Nat.choose_pos (by omega : j ≤ p + j)).ne'
    exact this
  have hjne : (j : ℚ_[p]) ≠ 0 := cast_nat_ne_zero (by omega)
  have hivj : iv p j * (j : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
  apply mul_right_cancel₀ hjne
  apply mul_right_cancel₀ hJne
  calc (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p]) * (j:ℚ_[p])
        * ∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i)
      = 2 * (p:ℚ_[p]) * (∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
        * ((∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i))
          * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t)) := by
        linear_combination key
    _ = 2 * (p:ℚ_[p]) * iv p j * (∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
        * (∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t)) * (j:ℚ_[p])
        * ∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i) := by
        linear_combination -(2 * (p:ℚ_[p]) * (∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
          * (∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t))
          * ∏ i ∈ Ico 1 (j+1), (1 + (p:ℚ_[p]) * iv p i)) * hivj

/-- Hockey stick: `∑_{k=0}^{2n} C(n+k-1, k) = C(3n, n)` for `1 ≤ n`. -/
lemma hockey_stick {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (2*n + 1), (n + k - 1).choose k = (3*n).choose n := by
  have e1 : ∀ k ∈ range (2*n + 1), (n + k - 1).choose k = (n + k - 1).choose (n-1) := by
    intro k _
    rw [← Nat.choose_symm (by omega : k ≤ n + k - 1)]
    congr 1
    omega
  rw [Finset.sum_congr rfl e1]
  have e2 : ∑ k ∈ range (2*n + 1), (n + k - 1).choose (n-1)
      = ∑ m ∈ Icc (n-1) (3*n - 1), m.choose (n-1) := by
    apply Finset.sum_nbij' (fun k => n + k - 1) (fun m => m - (n-1))
    · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; rw [Finset.mem_range]; omega
    · intro a ha; rw [Finset.mem_range] at ha; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; omega
    · intro a ha; rfl
  rw [e2, Nat.sum_Icc_choose]
  congr 1 <;> omega

end A357674


-- ===== From Dev/P5.lean =====

/- # The alternating-sum identity `∑ (-1)^(k-1) C(n,k)/k = H_n` and its p-instantiation -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∑_{k=0}^{n} (-1)^k C(n+1, k+1) = 1` (cast to `ℚ_p`). -/
lemma alt_choose_shift (m : ℕ) :
    ∑ k ∈ range (m+1), ((-1:ℚ_[p]))^k * (((m+1).choose (k+1) : ℕ) : ℚ_[p]) = 1 := by
  have hZ := Int.alternating_sum_range_choose_of_ne (n := m+1) (by omega)
  have halt : (∑ k ∈ range (m+2), ((-1:ℚ_[p]))^k * (((m+1).choose k : ℕ):ℚ_[p])) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ℚ_[p])) hZ
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, Int.cast_zero] at h
    exact h
  have hsplit := Finset.sum_range_succ'
    (fun k => ((-1:ℚ_[p]))^k * (((m+1).choose k : ℕ):ℚ_[p])) (m+1)
  rw [halt] at hsplit
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at hsplit
  have e : ∀ i ∈ range (m+1),
      ((-1:ℚ_[p]))^(i+1) * (((m+1).choose (i+1):ℕ):ℚ_[p])
        = -(((-1:ℚ_[p]))^i * (((m+1).choose (i+1):ℕ):ℚ_[p])) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib] at hsplit
  linear_combination hsplit

/-- Dilcher m=1: `∑_{k=0}^{n-1} (-1)^k C(n, k+1)/(k+1) = ∑_{k=0}^{n-1} 1/(k+1)`. -/
lemma alt_sum_inv (n : ℕ) :
    ∑ k ∈ range n, ((-1:ℚ_[p]))^k * ((n.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
      = ∑ k ∈ range n, iv p (k+1) := by
  induction n with
  | zero => rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
  | succ m ih =>
    have pascal : ∀ k ∈ range (m+1),
        ((-1:ℚ_[p]))^k * (((m+1).choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
          = ((-1:ℚ_[p]))^k * ((m.choose k : ℕ) : ℚ_[p]) * iv p (k+1)
            + ((-1:ℚ_[p]))^k * ((m.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1) := by
      intro k _
      rw [Nat.choose_succ_succ' m k]
      push_cast
      ring
    rw [Finset.sum_congr rfl pascal, Finset.sum_add_distrib]
    have second : ∑ k ∈ range (m+1), ((-1:ℚ_[p]))^k * ((m.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
        = ∑ k ∈ range m, ((-1:ℚ_[p]))^k * ((m.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1) := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero,
        zero_mul, add_zero]
    have ptwise : ∀ k ∈ range (m+1),
        ((-1:ℚ_[p]))^k * ((m.choose k : ℕ) : ℚ_[p]) * iv p (k+1)
          = ((-1:ℚ_[p]))^k * (((m+1).choose (k+1) : ℕ) : ℚ_[p]) * iv p (m+1) := by
      intro k _
      have hrec : (m + 1) * (m.choose k) = ((m+1).choose (k+1)) * (k+1) :=
        Nat.add_one_mul_choose_eq m k
      have hcast : ((m + 1 : ℕ) : ℚ_[p]) * ((m.choose k : ℕ) : ℚ_[p])
          = (((m+1).choose (k+1) : ℕ) : ℚ_[p]) * ((k + 1 : ℕ) : ℚ_[p]) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, hrec]
      have hk1 : iv p (k+1) * ((k+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
      have hm1 : iv p (m+1) * ((m+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
      have key : ((m.choose k : ℕ) : ℚ_[p]) * iv p (k+1)
          = (((m+1).choose (k+1) : ℕ) : ℚ_[p]) * iv p (m+1) := by
        apply mul_right_cancel₀ (cast_nat_ne_zero (show k+1 ≠ 0 by omega))
        apply mul_right_cancel₀ (cast_nat_ne_zero (show m+1 ≠ 0 by omega))
        linear_combination (((m.choose k : ℕ):ℚ_[p]) * ((m+1:ℕ):ℚ_[p])) * hk1
          - ((((m+1).choose (k+1):ℕ):ℚ_[p]) * ((k+1:ℕ):ℚ_[p])) * hm1 + hcast
      linear_combination ((-1:ℚ_[p]))^k * key
    have first : ∑ k ∈ range (m+1), ((-1:ℚ_[p]))^k * ((m.choose k : ℕ) : ℚ_[p]) * iv p (k+1)
        = iv p (m+1) := by
      rw [Finset.sum_congr rfl ptwise, ← Finset.sum_mul, alt_choose_shift m, one_mul]
    rw [first, second, ih, Finset.sum_range_succ]
    ring

/-- The key exact identity: `H_1 = p ∑_{k=1}^{p-1} (1/k²) ∏_{i<k} (1 - p/i)`. -/
lemma key_identity_H1 (hp2 : p ≠ 2) :
    hh p p = (p:ℚ_[p]) * ∑ k ∈ Ico 1 p, (iv p k)^2 * ∏ i ∈ Ico 1 k, (1 - (p:ℚ_[p]) * iv p i) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h := alt_sum_inv (p := p) p
  -- RHS of h : ∑_{k ∈ range p} iv (k+1) = hh p + iv p
  have hRHS : ∑ k ∈ range p, iv p (k+1) = hh p p + iv p p := by
    have e1 : ∑ k ∈ Ico 1 (p+1), iv p k = ∑ k ∈ range (p+1-1), iv p (1+k) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have e2 : ∑ k ∈ range p, iv p (k+1) = ∑ k ∈ Ico 1 (p+1), iv p k := by
      rw [e1]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
    rw [e2]
    unfold hh
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ p)]
  -- LHS of h : peel the k = p-1 term
  have hLHS : ∑ k ∈ range p, ((-1:ℚ_[p]))^k * ((p.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
      = (∑ k ∈ range (p-1), ((-1:ℚ_[p]))^k * ((p.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1))
        + iv p p := by
    have hrange : range p = range ((p-1)+1) := by
      congr 1
      omega
    rw [hrange, Finset.sum_range_succ]
    have heven : Even (p-1) := by
      rcases hodd with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    rw [show (p-1)+1 = p by omega, Nat.choose_self, heven.neg_one_pow, Nat.cast_one,
      one_mul, one_mul]
  rw [hRHS, hLHS] at h
  have h2 : ∑ k ∈ range (p-1), ((-1:ℚ_[p]))^k * ((p.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
      = hh p p := by
    linear_combination h
  -- pointwise rewrite to product form
  have ptwise : ∀ k ∈ range (p-1),
      ((-1:ℚ_[p]))^k * ((p.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
        = (p:ℚ_[p]) * ((iv p (k+1))^2 * ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hrec : (p:ℕ) * ((p-1).choose k) = (p.choose (k+1)) * (k+1) := by
      have := Nat.add_one_mul_choose_eq (p-1) k
      rwa [show p-1+1 = p by omega] at this
    have hcast : ((p : ℕ) : ℚ_[p]) * (((p-1).choose k : ℕ) : ℚ_[p])
        = ((p.choose (k+1) : ℕ) : ℚ_[p]) * ((k + 1 : ℕ) : ℚ_[p]) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hrec]
    have hsign := choose_prod_sign (p := p) k (by omega)
    have hk1 : iv p (k+1) * ((k+1 : ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by omega)
    have e : ((-1:ℚ_[p]))^k * ((-1:ℚ_[p]))^k = 1 := by
      rw [← pow_add]
      have heven : Even (k+k) := ⟨k, by omega⟩
      exact heven.neg_one_pow
    have hprod : (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i))
        = (-1:ℚ_[p])^k * (((p-1).choose k : ℕ) : ℚ_[p]) := by
      linear_combination (-((-1:ℚ_[p]))^k) * hsign
        - (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i)) * e
    have t1 : ((p.choose (k+1) : ℕ) : ℚ_[p])
        = ((p:ℕ):ℚ_[p]) * (((p-1).choose k : ℕ):ℚ_[p]) * iv p (k+1) := by
      apply mul_right_cancel₀ (cast_nat_ne_zero (show k+1 ≠ 0 by omega))
      linear_combination -hcast
        - ((p:ℕ):ℚ_[p]) * (((p-1).choose k : ℕ):ℚ_[p]) * hk1
    calc ((-1:ℚ_[p]))^k * ((p.choose (k+1) : ℕ) : ℚ_[p]) * iv p (k+1)
        = ((-1:ℚ_[p]))^k * (((p:ℕ):ℚ_[p]) * (((p-1).choose k : ℕ):ℚ_[p]) * iv p (k+1))
            * iv p (k+1) := by rw [t1]
      _ = ((p:ℕ):ℚ_[p]) * ((iv p (k+1))^2
            * (((-1:ℚ_[p]))^k * (((p-1).choose k : ℕ):ℚ_[p]))) := by ring
      _ = (p:ℚ_[p]) * ((iv p (k+1))^2 * ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i)) := by
          rw [← hprod]
  rw [Finset.sum_congr rfl ptwise] at h2
  -- reindex range (p-1) → Ico 1 p
  have hreidx : ∑ k ∈ Ico 1 p, (p:ℚ_[p]) * ((iv p k)^2 * ∏ i ∈ Ico 1 k, (1 - (p:ℚ_[p]) * iv p i))
      = ∑ k ∈ range (p-1),
        (p:ℚ_[p]) * ((iv p (k+1))^2 * ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm 1 k]
  rw [← hreidx] at h2
  rw [← h2, Finset.mul_sum]

end A357674


-- ===== From Dev/P5b.lean =====

/- # Vandermonde-type alternating identity and its p-instantiation -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∑_{k=0}^{m} (-1)^k C(m,k) C(n+k, k+r) = (-1)^m C(n, m+r)` in `ℚ_p`. -/
lemma Fr_identity (m : ℕ) : ∀ n r : ℕ,
    ∑ k ∈ range (m+1),
      ((-1:ℚ_[p]))^k * ((m.choose k : ℕ) : ℚ_[p]) * (((n+k).choose (k+r) : ℕ) : ℚ_[p])
      = (-1:ℚ_[p])^m * ((n.choose (m+r) : ℕ) : ℚ_[p]) := by
  induction m with
  | zero =>
    intro n r
    simp only [Finset.sum_range_one, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.add_zero, Nat.zero_add]
  | succ m ih =>
    intro n r
    rw [Finset.sum_range_succ']
    have hA := ih (n+1) (r+1)
    -- B = F(m,n,r) - C(n,r)
    have hFull := ih n r
    have hFull2 : ∑ k ∈ range (m+2),
        ((-1:ℚ_[p]))^k * ((m.choose k : ℕ) : ℚ_[p]) * (((n+k).choose (k+r) : ℕ) : ℚ_[p])
        = (-1:ℚ_[p])^m * ((n.choose (m+r) : ℕ) : ℚ_[p]) := by
      rw [show m+2 = (m+1)+1 by rfl, Finset.sum_range_succ, hFull,
        Nat.choose_eq_zero_of_lt (by omega : m < m+1), Nat.cast_zero, mul_zero,
        zero_mul, add_zero]
    have hB : ∑ i ∈ range (m+1),
        ((-1:ℚ_[p]))^(i+1) * ((m.choose (i+1) : ℕ) : ℚ_[p])
          * (((n+(i+1)).choose ((i+1)+r) : ℕ) : ℚ_[p])
        = (-1:ℚ_[p])^m * ((n.choose (m+r) : ℕ) : ℚ_[p]) - ((n.choose r : ℕ) : ℚ_[p]) := by
      rw [Finset.sum_range_succ'] at hFull2
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_zero,
        Nat.zero_add] at hFull2
      linear_combination hFull2
    -- pointwise Pascal split
    have hsplit : ∀ i ∈ range (m+1),
        ((-1:ℚ_[p]))^(i+1) * (((m+1).choose (i+1) : ℕ) : ℚ_[p])
          * (((n+(i+1)).choose ((i+1)+r) : ℕ) : ℚ_[p])
        = -( ((-1:ℚ_[p]))^i * ((m.choose i : ℕ) : ℚ_[p])
              * ((((n+1)+i).choose (i+(r+1)) : ℕ) : ℚ_[p]) )
          + ((-1:ℚ_[p]))^(i+1) * ((m.choose (i+1) : ℕ) : ℚ_[p])
              * (((n+(i+1)).choose ((i+1)+r) : ℕ) : ℚ_[p]) := by
      intro i _
      have hpas : ((m+1).choose (i+1) : ℕ) = m.choose i + m.choose (i+1) :=
        Nat.choose_succ_succ m i
      have e1 : n+(i+1) = (n+1)+i := by omega
      have e2 : (i+1)+r = i+(r+1) := by omega
      have e3 : (((n+(i+1)).choose ((i+1)+r) : ℕ) : ℚ_[p])
          = ((((n+1)+i).choose (i+(r+1)) : ℕ) : ℚ_[p]) := by rw [e1, e2]
      rw [hpas, Nat.cast_add, e3]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_neg_distrib, hA, hB]
    have hpas2 : ((n+1).choose ((m+r)+1) : ℕ) = n.choose (m+r) + n.choose ((m+r)+1) :=
      Nat.choose_succ_succ n (m+r)
    have e4 : (((n+1).choose (m+(r+1)) : ℕ) : ℚ_[p]) = ((n+1).choose ((m+r)+1) : ℕ) := by
      rw [show m+(r+1) = (m+r)+1 by omega]
    have e5 : ((n.choose ((m+1)+r) : ℕ) : ℚ_[p]) = ((n.choose ((m+r)+1) : ℕ) : ℚ_[p]) := by
      rw [show (m+1)+r = (m+r)+1 by omega]
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_zero,
      Nat.zero_add, pow_succ]
    rw [e4, e5]
    have hc : (((n+1).choose ((m+r)+1) : ℕ) : ℚ_[p])
        = ((n.choose (m+r) : ℕ) : ℚ_[p]) + ((n.choose ((m+r)+1) : ℕ) : ℚ_[p]) := by
      rw [hpas2, Nat.cast_add]
    linear_combination -((-1:ℚ_[p])^m) * hc

/-- Instantiation: `p = ∑_{k=0}^{p-1} ∏_{i=1}^{k} (1 - p²/i²)` in `ℚ_p`. -/
lemma vandermonde_p (hp2 : p ≠ 2) :
    (p:ℚ_[p]) = ∑ k ∈ range p, ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p])^2 * (iv p i)^2) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have heven : Even (p-1) := Nat.Odd.sub_odd hodd odd_one
  have h := Fr_identity (p := p) (p-1) p 0
  simp only [Nat.add_zero] at h
  rw [show p-1+1 = p by have := hp.out.pos; omega] at h
  have hcs : p.choose (p-1) = p := by
    have h1 : p.choose (p - 1) = p.choose 1 := Nat.choose_symm hp.out.one_lt.le
    rw [h1, Nat.choose_one_right]
  have hpt : ∀ k ∈ range p,
      ((-1:ℚ_[p]))^k * (((p-1).choose k : ℕ) : ℚ_[p]) * (((p+k).choose k : ℕ) : ℚ_[p])
      = ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p])^2 * (iv p i)^2) := by
    intro k hk
    have hkp : k ≤ p - 1 := by
      have := Finset.mem_range.mp hk
      omega
    rw [choose_prod_sign k hkp, choose_prod_gen p k]
    have hev : Even (k+k) := ⟨k, rfl⟩
    have e : ((-1:ℚ_[p]))^k * ((-1:ℚ_[p]))^k = 1 := by
      rw [← pow_add]; exact hev.neg_one_pow
    have hAB : (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i))
        * (∏ i ∈ Ico 1 (k+1), (1 + (p:ℚ_[p]) * iv p i))
        = ∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p])^2 * (iv p i)^2) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    linear_combination (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p]) * iv p i))
      * (∏ i ∈ Ico 1 (k+1), (1 + (p:ℚ_[p]) * iv p i)) * e + hAB
  rw [Finset.sum_congr rfl hpt] at h
  rw [heven.neg_one_pow, one_mul, hcs] at h
  exact h.symm

end A357674


-- ===== From Dev/P6.lean =====

/- # Power-sum divisibility: `p ∣ ∑ 1/k^m` for `1 ≤ m ≤ p-2` -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma dvd_fact_of_mem {k : ℕ} (h : k ∈ Ico 1 p) : k ∣ (p-1)! := by
  rw [mem_Ico] at h
  exact Nat.dvd_factorial (by omega) (by omega)

lemma p_not_dvd_fact : ¬ p ∣ (p-1)! := by
  intro h
  have h2 := (Nat.Prime.dvd_factorial hp.out).mp h
  have := hp.out.two_le
  omega

/-- In `ZMod p`, the sum `∑_{k=1}^{p-1} ((p-1)!/k)^m` vanishes for `1 ≤ m ≤ p-2`. -/
lemma powsum_dvd (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ p - 2) :
    p ∣ ∑ k ∈ Ico 1 p, ((p-1)! / k)^m := by
  have hp5 : 3 ≤ p := by have := hp.out.two_le; omega
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_sum, Nat.cast_pow]
  -- pointwise: ((p-1)!/k : ZMod p) = F * (k)⁻¹
  have hpt : ∀ k ∈ Ico 1 p,
      ((((p-1)! / k : ℕ)) : ZMod p)^m
      = (((p-1)! : ℕ) : ZMod p)^m * (((k:ℕ) : ZMod p)⁻¹)^m := by
    intro k hk
    have hkne : ((k:ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact not_dvd_of_mem_Ico hk
    have hdvd : k ∣ (p-1)! := dvd_fact_of_mem hk
    have hmul : ((((p-1)! / k : ℕ)) : ZMod p) * ((k:ℕ) : ZMod p)
        = (((p-1)! : ℕ) : ZMod p) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    have : ((((p-1)! / k : ℕ)) : ZMod p)
        = (((p-1)! : ℕ) : ZMod p) * (((k:ℕ) : ZMod p))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hkne]
      exact hmul
    rw [this, mul_pow]
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  -- now show ∑_{k ∈ Ico 1 p} (k⁻¹)^m = 0
  have hinner : ∑ k ∈ Ico 1 p, ((((k:ℕ)) : ZMod p)⁻¹)^m = 0 := by
    -- rewrite each (k⁻¹)^m as k^(p-1-m)
    have hpt2 : ∀ k ∈ Ico 1 p,
        ((((k:ℕ)) : ZMod p)⁻¹)^m = (((k:ℕ)) : ZMod p)^(p-1-m) := by
      intro k hk
      have hkne : ((k:ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact not_dvd_of_mem_Ico hk
      have hfermat : (((k:ℕ)) : ZMod p)^(p-1) = 1 :=
        ZMod.pow_card_sub_one_eq_one hkne
      have hsplit : (((k:ℕ)) : ZMod p)^(p-1-m) * (((k:ℕ)) : ZMod p)^m
          = (((k:ℕ)) : ZMod p)^(p-1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hfermat] at hsplit
      rw [inv_pow]
      exact inv_eq_of_mul_eq_one_left hsplit
    rw [Finset.sum_congr rfl hpt2]
    -- extend to sum over range p (0 term vanishes since p-1-m ≥ 1)
    have h0 : ((0:ℕ) : ZMod p)^(p-1-m) = 0 := by
      rw [Nat.cast_zero]
      exact zero_pow (by omega)
    have hext : ∑ k ∈ range p, (((k:ℕ)) : ZMod p)^(p-1-m)
        = ∑ k ∈ Ico 1 p, (((k:ℕ)) : ZMod p)^(p-1-m) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
      rw [h0, zero_add]
    rw [← hext]
    -- bijection range p ≃ ZMod p
    have hbij : ∑ k ∈ range p, (((k:ℕ)) : ZMod p)^(p-1-m)
        = ∑ x : ZMod p, x^(p-1-m) := by
      apply Finset.sum_nbij' (i := fun k => ((k:ℕ) : ZMod p)) (j := fun x => x.val)
      · intro a _
        exact Finset.mem_univ _
      · intro b _
        exact Finset.mem_range.mpr (ZMod.val_lt b)
      · intro a ha
        exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
      · intro b _
        exact ZMod.natCast_zmod_val b
      · intro a _
        rfl
    rw [hbij]
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) (p-1-m)
      (by rw [hcard]; omega)
    exact this
  rw [hinner, mul_zero]

/-- `SM 1 (∑_{k=1}^{p-1} (1/k)^m)` for `1 ≤ m ≤ p-2`. -/
lemma sm_powsum (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ p - 2) :
    SM 1 (∑ k ∈ Ico 1 p, (iv p k)^m) := by
  set N : ℕ := ∑ k ∈ Ico 1 p, ((p-1)! / k)^m with hN
  have hdvd : p ∣ N := powsum_dvd m hm1 hm2
  have hFne : ¬ p ∣ (p-1)! := p_not_dvd_fact
  -- (N : ℚ_p) = F^m * ∑ (iv k)^m
  have hcast : ((N : ℕ) : ℚ_[p])
      = (((p-1)! : ℕ) : ℚ_[p])^m * ∑ k ∈ Ico 1 p, (iv p k)^m := by
    rw [hN]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hdvdk : k ∣ (p-1)! := dvd_fact_of_mem hk
    have hkne : (k : ℚ_[p]) ≠ 0 := iv_ne_zero hk
    have hterm : ((((p-1)! / k : ℕ)) : ℚ_[p])
        = (((p-1)! : ℕ) : ℚ_[p]) * iv p k := by
      apply mul_right_cancel₀ hkne
      have h1 : ((((p-1)! / k : ℕ)) : ℚ_[p]) * ((k:ℕ) : ℚ_[p])
          = (((p-1)! : ℕ) : ℚ_[p]) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdvdk]
      have h2 : iv p k * ((k:ℕ) : ℚ_[p]) = 1 := iv_mul_cancel (by
        rw [mem_Ico] at hk; omega)
      rw [h1]
      linear_combination -(((p-1)! : ℕ) : ℚ_[p]) * h2
    rw [hterm, mul_pow]
  -- SM 1 N
  have hsmN : SM 1 ((N : ℕ) : ℚ_[p]) := by
    rw [sm_def, pw]
    have hd : ((p:ℤ))^1 ∣ (N : ℤ) := by rw [pow_one]; exact_mod_cast hdvd
    have h := (Padic.norm_int_le_pow_iff_dvd (p := p) (N : ℤ) 1).mpr hd
    simpa only [Int.cast_natCast, Nat.cast_one] using h
  -- divide by F^m
  have hFne' : (((p-1)! : ℕ) : ℚ_[p]) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    exact Nat.factorial_ne_zero _ h
  have hFinv : SM 0 ((((p-1)! : ℕ) : ℚ_[p])⁻¹^m) := by
    rw [sm_zero_iff, norm_pow, norm_natCast_inv_eq_one hFne, one_pow]
  have : SM 1 ((((p-1)! : ℕ) : ℚ_[p])⁻¹^m * ((N : ℕ) : ℚ_[p])) :=
    SM.mul_left hsmN hFinv
  apply this.of_eq
  rw [hcast, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hFne', one_pow, one_mul]

lemma sm_qq_p (hp7 : 7 ≤ p) : SM 1 (qq p p) := by
  have := sm_powsum (p := p) 2 (by omega) (by omega)
  exact this

lemma sm_rr_p (hp7 : 7 ≤ p) : SM 1 (rr p p) := by
  have := sm_powsum (p := p) 4 (by omega) (by omega)
  exact this

end A357674


-- ===== From Dev/P7a.lean =====

/- # Reflection `k ↦ p-k` expansions and pairing bounds -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma refl_mem {k : ℕ} (hk : k ∈ Ico 1 p) : (p - k) ∈ Ico 1 p := by
  rw [mem_Ico] at *
  omega

lemma sm_cancel_unit {n : ℕ} {u x : ℚ_[p]} (hu : ‖u‖ = 1) (h : SM n (u * x)) : SM n x := by
  rw [sm_def] at h ⊢
  rwa [norm_mul, hu, one_mul] at h

lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2:ℚ_[p])‖ = 1 := by
  have h2 : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    have := hp.out.two_le
    interval_cases p
    · exact hp2 rfl
  have := norm_natCast_eq_one (p := p) (k := 2) h2
  rwa [Nat.cast_ofNat] at this

/-- Exact 4th-order reflection identity for `1/(p-k)`. -/
lemma iv_reflect_exact {k : ℕ} (hk : k ∈ Ico 1 p) :
    iv p (p-k) = -iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3
      - (p:ℚ_[p])^3*(iv p k)^4 + (p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k))) := by
  have hkne : (k:ℚ_[p]) ≠ 0 := iv_ne_zero hk
  have hpk : (p-k) ∈ Ico 1 p := refl_mem hk
  have hpkne : (((p-k : ℕ)):ℚ_[p]) ≠ 0 := iv_ne_zero hpk
  have hle : k ≤ p := by rw [mem_Ico] at hk; omega
  have hcast : (((p-k:ℕ)) : ℚ_[p]) = (p:ℚ_[p]) - (k:ℚ_[p]) := by
    push_cast [Nat.cast_sub hle]
    ring
  have hne2 : ((p:ℚ_[p]) - (k:ℚ_[p])) ≠ 0 := by rw [← hcast]; exact hpkne
  have h1 : iv p (p-k) = ((p:ℚ_[p]) - (k:ℚ_[p]))⁻¹ := by unfold iv; rw [hcast]
  have h2 : iv p k = ((k:ℚ_[p]))⁻¹ := rfl
  rw [h1, h2]
  field_simp
  ring

lemma mc_iv_reflect1 {k : ℕ} (hk : k ∈ Ico 1 p) :
    MC 1 (iv p (p-k)) (-iv p k) := by
  apply MC.of_sub (d := -((p:ℚ_[p])*(iv p k)^2) - (p:ℚ_[p])^2*(iv p k)^3
      - (p:ℚ_[p])^3*(iv p k)^4 + (p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k))))
  · linear_combination iv_reflect_exact hk
  · have t1 : SM 1 ((p:ℚ_[p])*(iv p k)^2) := sm_p.mul (sm_iv_pow hk 2)
    have t2 : SM 1 ((p:ℚ_[p])^2*(iv p k)^3) := ((sm_ppow 2).mul (sm_iv_pow hk 3)).mono (by decide)
    have t3 : SM 1 ((p:ℚ_[p])^3*(iv p k)^4) := ((sm_ppow 3).mul (sm_iv_pow hk 4)).mono (by decide)
    have t4 : SM 1 ((p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k)))) :=
      ((sm_ppow 4).mul ((sm_iv_pow hk 4).mul (sm_iv (refl_mem hk)))).mono (by decide)
    exact ((t1.neg.sub t2).sub t3).add t4

lemma mc_iv_reflect2 {k : ℕ} (hk : k ∈ Ico 1 p) :
    MC 2 (iv p (p-k)) (-iv p k - (p:ℚ_[p])*(iv p k)^2) := by
  apply MC.of_sub (d := -((p:ℚ_[p])^2*(iv p k)^3)
      - (p:ℚ_[p])^3*(iv p k)^4 + (p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k))))
  · linear_combination iv_reflect_exact hk
  · have t2 : SM 2 ((p:ℚ_[p])^2*(iv p k)^3) := (sm_ppow 2).mul (sm_iv_pow hk 3)
    have t3 : SM 2 ((p:ℚ_[p])^3*(iv p k)^4) := ((sm_ppow 3).mul (sm_iv_pow hk 4)).mono (by decide)
    have t4 : SM 2 ((p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k)))) :=
      ((sm_ppow 4).mul ((sm_iv_pow hk 4).mul (sm_iv (refl_mem hk)))).mono (by decide)
    exact (t2.neg.sub t3).add t4

lemma mc_iv_reflect3 {k : ℕ} (hk : k ∈ Ico 1 p) :
    MC 3 (iv p (p-k)) (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3) := by
  apply MC.of_sub (d := -((p:ℚ_[p])^3*(iv p k)^4) + (p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k))))
  · linear_combination iv_reflect_exact hk
  · have t3 : SM 3 ((p:ℚ_[p])^3*(iv p k)^4) := (sm_ppow 3).mul (sm_iv_pow hk 4)
    have t4 : SM 3 ((p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k)))) :=
      ((sm_ppow 4).mul ((sm_iv_pow hk 4).mul (sm_iv (refl_mem hk)))).mono (by decide)
    exact t3.neg.add t4

lemma mc_iv_reflect4 {k : ℕ} (hk : k ∈ Ico 1 p) :
    MC 4 (iv p (p-k)) (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3
      - (p:ℚ_[p])^3*(iv p k)^4) := by
  apply MC.of_sub (d := (p:ℚ_[p])^4*((iv p k)^4*(iv p (p-k))))
  · linear_combination iv_reflect_exact hk
  · exact (sm_ppow 4).mul ((sm_iv_pow hk 4).mul (sm_iv (refl_mem hk)))

lemma sum_expand4 :
    ∑ k ∈ Ico 1 p, (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3
        - (p:ℚ_[p])^3*(iv p k)^4)
      = -hh p p - (p:ℚ_[p])*qq p p - (p:ℚ_[p])^2*cc p p - (p:ℚ_[p])^3*rr p p := by
  unfold hh qq cc rr
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Pairing: `2·H₁ + p·H₂ + p²·H₃ + p³·H₄ ≡ 0 (mod p⁴)`. -/
lemma pair4 : SM 4 (2*hh p p + (p:ℚ_[p])*qq p p + (p:ℚ_[p])^2*cc p p
    + (p:ℚ_[p])^3*rr p p) := by
  have hrefl : hh p p = ∑ k ∈ Ico 1 p, iv p (p-k) := sum_reflect (iv p)
  have hmc : MC 4 (∑ k ∈ Ico 1 p, iv p (p-k))
      (∑ k ∈ Ico 1 p, (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3
        - (p:ℚ_[p])^3*(iv p k)^4)) :=
    MC.sum (fun k hk => mc_iv_reflect4 hk)
  rw [sum_expand4, ← hrefl] at hmc
  have h := mc_def.mp hmc
  exact h.of_eq (by ring)

lemma mc_iv_reflect_sq3 {k : ℕ} (hk : k ∈ Ico 1 p) :
    MC 3 ((iv p (p-k))^2) ((iv p k)^2 + 2*(p:ℚ_[p])*(iv p k)^3 + 3*(p:ℚ_[p])^2*(iv p k)^4) := by
  have d3 := mc_iv_reflect3 hk
  have hx : SM 0 (iv p (p-k)) := sm_iv (refl_mem hk)
  have hy : SM 0 (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3) := by
    have t1 : SM 0 (iv p k) := sm_iv hk
    have t2 : SM 0 ((p:ℚ_[p])*(iv p k)^2) := (sm_p.mul (sm_iv_pow hk 2)).mono (by decide)
    have t3 : SM 0 ((p:ℚ_[p])^2*(iv p k)^3) := ((sm_ppow 2).mul (sm_iv_pow hk 3)).mono (by decide)
    exact (t1.neg.sub t2).sub t3
  have hsq : MC 3 ((iv p (p-k)) * (iv p (p-k)))
      ((-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3)
        * (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3)) :=
    d3.mul d3 hx hy
  have hstep : MC 3 ((-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3)
        * (-iv p k - (p:ℚ_[p])*(iv p k)^2 - (p:ℚ_[p])^2*(iv p k)^3))
      ((iv p k)^2 + 2*(p:ℚ_[p])*(iv p k)^3 + 3*(p:ℚ_[p])^2*(iv p k)^4) := by
    apply MC.of_sub (d := (p:ℚ_[p])^3*(2*(iv p k)^5 + (p:ℚ_[p])*(iv p k)^6))
    · ring
    · have t1 : SM 0 (2*(iv p k)^5) := (sm_ofNat 2).mul (sm_iv_pow hk 5)
      have t2 : SM 0 ((p:ℚ_[p])*(iv p k)^6) :=
        (sm_p.mul (sm_iv_pow hk 6)).mono (by decide)
      have trest : SM 0 (2*(iv p k)^5 + (p:ℚ_[p])*(iv p k)^6) := t1.add t2
      exact (sm_ppow 3).mul trest
  have := hsq.trans hstep
  exact (MC.of_eq (by ring : (iv p (p-k))^2
      = (iv p (p-k)) * (iv p (p-k)))).trans this

lemma sum_expand_sq :
    ∑ k ∈ Ico 1 p, ((iv p k)^2 + 2*(p:ℚ_[p])*(iv p k)^3 + 3*(p:ℚ_[p])^2*(iv p k)^4)
      = qq p p + 2*(p:ℚ_[p])*cc p p + 3*(p:ℚ_[p])^2*rr p p := by
  unfold qq cc rr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma sm_cc_p (hp7 : 7 ≤ p) : SM 2 (cc p p) := by
  have hp2 : p ≠ 2 := by omega
  have hrefl : qq p p = ∑ k ∈ Ico 1 p, (iv p (p-k))^2 :=
    sum_reflect (fun k => (iv p k)^2)
  have hmc : MC 3 (∑ k ∈ Ico 1 p, (iv p (p-k))^2)
      (∑ k ∈ Ico 1 p, ((iv p k)^2 + 2*(p:ℚ_[p])*(iv p k)^3 + 3*(p:ℚ_[p])^2*(iv p k)^4)) :=
    MC.sum (fun k hk => mc_iv_reflect_sq3 hk)
  rw [sum_expand_sq, ← hrefl] at hmc
  have h : SM 3 (2*(p:ℚ_[p])*cc p p + 3*(p:ℚ_[p])^2*rr p p) := by
    have := mc_def.mp hmc
    exact this.neg.of_eq (by ring)
  have hrr : SM 3 (3*(p:ℚ_[p])^2*rr p p) := by
    have : SM 3 ((p:ℚ_[p])^2 * rr p p) := (sm_ppow 2).mul (sm_rr_p hp7)
    exact ((sm_ofNat 3).mul this).of_eq (by ring)
  have h2 : SM 3 (2*((p:ℚ_[p])*cc p p)) := (h.sub hrr).of_eq (by ring)
  have h3 : SM 3 ((p:ℚ_[p])*cc p p) := sm_cancel_unit (norm_two_eq_one hp2) h2
  exact SM.cancel_ppow (n := 2) (k := 1) (h3.of_eq (by ring))

/-- Refined pairing: `2·H₁ + p·H₂ ≡ 0 (mod p⁴)`. -/
lemma sm_pair_ref (hp7 : 7 ≤ p) : SM 4 (2*hh p p + (p:ℚ_[p])*qq p p) := by
  have h1 := pair4 (p := p)
  have h2 : SM 4 ((p:ℚ_[p])^2*cc p p) := (sm_ppow 2).mul (sm_cc_p hp7)
  have h3 : SM 4 ((p:ℚ_[p])^3*rr p p) := (sm_ppow 3).mul (sm_rr_p hp7)
  exact ((h1.sub h2).sub h3).of_eq (by ring)

lemma sm_hh_p (hp7 : 7 ≤ p) : SM 2 (hh p p) := by
  have hp2 : p ≠ 2 := by omega
  have h1 := (sm_pair_ref hp7).mono (by norm_num : 2 ≤ 4)
  have h2 : SM 2 ((p:ℚ_[p])*qq p p) := sm_p.mul (sm_qq_p hp7)
  have h3 : SM 2 (2*hh p p) := (h1.sub h2).of_eq (by ring)
  exact sm_cancel_unit (norm_two_eq_one hp2) h3

end A357674


-- ===== From Dev/P7b.lean =====

/- # Double-sum reversals, the key identity truncation, and `E2s ≡ 0 (mod p)` -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_of_inner {a b : ℕ} (ha : a ∈ Ico 1 b) (hb : b ∈ Ico 1 p) : a ∈ Ico 1 p := by
  rw [mem_Ico] at *
  omega

/- ## REV3 : `T1 + H21 + p·H22 + 2p·H31 ≡ 0 (mod p²)` -/

lemma mc_iv_reflect_sq2 {a : ℕ} (ha : a ∈ Ico 1 p) :
    MC 2 ((iv p (p-a))^2) ((iv p a)^2 + 2*(p:ℚ_[p])*(iv p a)^3) := by
  have h1 := (mc_iv_reflect_sq3 ha).mono (by norm_num : 2 ≤ 3)
  have h2 : MC 2 ((iv p a)^2 + 2*(p:ℚ_[p])*(iv p a)^3 + 3*(p:ℚ_[p])^2*(iv p a)^4)
      ((iv p a)^2 + 2*(p:ℚ_[p])*(iv p a)^3) := by
    apply MC.of_sub (d := 3*(p:ℚ_[p])^2*(iv p a)^4)
    · ring
    · have h3 : SM 0 (3 * (iv p a)^4) := (sm_ofNat 3).mul (sm_iv_pow ha 4)
      exact ((sm_ppow 2).mul h3).of_eq (by ring)
  exact h1.trans h2

lemma rev3_pointwise {a b : ℕ} (ha : a ∈ Ico 1 p) (hb : b ∈ Ico 1 p) :
    MC 2 ((iv p (p-a))^2 * iv p (p-b))
      (-(iv p b * (iv p a)^2) - (p:ℚ_[p])*((iv p b)^2*(iv p a)^2)
        - 2*(p:ℚ_[p])*(iv p b*(iv p a)^3)) := by
  have s1 := mc_iv_reflect_sq2 ha
  have s2 := mc_iv_reflect2 hb
  have hx : SM 0 ((iv p (p-a))^2) := sm_iv_pow (refl_mem ha) 2
  have hy' : SM 0 (-iv p b - (p:ℚ_[p])*(iv p b)^2) := by
    have t1 : SM 0 (iv p b) := sm_iv hb
    have t2 : SM 0 ((p:ℚ_[p])*(iv p b)^2) := (sm_p.mul (sm_iv_pow hb 2)).mono (by decide)
    exact t1.neg.sub t2
  have hprod := s1.mul s2 hx hy'
  refine hprod.trans (MC.of_sub
    (d := -(2*(p:ℚ_[p])^2*((iv p a)^3*(iv p b)^2))) ?_ ?_)
  · ring
  · have t1 : SM 2 (2*(p:ℚ_[p])^2*((iv p a)^3*(iv p b)^2)) := by
      have h3 : SM 0 (2 * ((iv p a)^3*(iv p b)^2)) :=
        (sm_ofNat 2).mul ((sm_iv_pow ha 3).mul (sm_iv_pow hb 2))
      exact ((sm_ppow 2).mul h3).of_eq (by ring)
    exact t1.neg

lemma rev3 (hp7 : 7 ≤ p) : SM 2 (T1 p + H21 p + (p:ℚ_[p])*H22 p + 2*(p:ℚ_[p])*H31 p) := by
  have hdouble : T1 p = ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, (iv p b)^2 * iv p a := by
    unfold T1 hh
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  have hrefl := sum_reflect2 (p := p) (fun a b => (iv p b)^2 * iv p a)
  -- pointwise on the reflected double sum
  have hmc : MC 2 (∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, (iv p (p-a))^2 * iv p (p-b))
      (∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b,
        (-(iv p b * (iv p a)^2) - (p:ℚ_[p])*((iv p b)^2*(iv p a)^2)
          - 2*(p:ℚ_[p])*(iv p b*(iv p a)^3))) := by
    apply MC.sum
    intro b hb
    apply MC.sum
    intro a ha
    exact rev3_pointwise (mem_of_inner ha hb) hb
  have hsum : ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b,
      (-(iv p b * (iv p a)^2) - (p:ℚ_[p])*((iv p b)^2*(iv p a)^2)
        - 2*(p:ℚ_[p])*(iv p b*(iv p a)^3))
      = -H21 p - (p:ℚ_[p])*H22 p - 2*(p:ℚ_[p])*H31 p := by
    unfold H21 H22 H31 qq cc
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [hsum] at hmc
  rw [← hrefl] at hmc
  rw [← hdouble] at hmc
  have h := mc_def.mp hmc
  exact h.of_eq (by ring)

/- ## REV4 : `H13 ≡ H31 (mod p)` -/

lemma rev4_pointwise {a b : ℕ} (ha : a ∈ Ico 1 p) (hb : b ∈ Ico 1 p) :
    MC 1 ((iv p (p-a))^3 * iv p (p-b)) (iv p b * (iv p a)^3) := by
  have ma := mc_iv_reflect1 ha
  have mb := mc_iv_reflect1 hb
  have hxa : SM 0 (iv p (p-a)) := sm_iv (refl_mem ha)
  have hya : SM 0 (-iv p a) := (sm_iv ha).neg
  have c1 : MC 1 (iv p (p-a) * iv p (p-a)) ((-iv p a) * (-iv p a)) := ma.mul ma hxa hya
  have c2 : MC 1 ((iv p (p-a) * iv p (p-a)) * iv p (p-a))
      (((-iv p a) * (-iv p a)) * (-iv p a)) := c1.mul ma (hxa.mul hxa) hya
  have c3 : MC 1 (((iv p (p-a) * iv p (p-a)) * iv p (p-a)) * iv p (p-b))
      ((((-iv p a) * (-iv p a)) * (-iv p a)) * (-iv p b)) :=
    c2.mul mb ((hxa.mul hxa).mul hxa) ((sm_iv hb).neg)
  refine (MC.of_eq (by ring)).trans (c3.trans (MC.of_eq (by ring)))

lemma rev4 (hp7 : 7 ≤ p) : SM 1 (H13 p - H31 p) := by
  have hdouble : H13 p = ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, (iv p b)^3 * iv p a := by
    unfold H13 hh
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  have hrefl := sum_reflect2 (p := p) (fun a b => (iv p b)^3 * iv p a)
  -- reflected form: F (p-b) (p-a) = (iv (p-a))^3 * iv (p-b)
  have hmc : MC 1 (∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, (iv p (p-a))^3 * iv p (p-b))
      (∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, iv p b * (iv p a)^3) := by
    apply MC.sum
    intro b hb
    apply MC.sum
    intro a ha
    exact rev4_pointwise (mem_of_inner ha hb) hb
  have hsum : ∑ b ∈ Ico 1 p, ∑ a ∈ Ico 1 b, iv p b * (iv p a)^3 = H31 p := by
    unfold H31 cc
    simp only [← Finset.mul_sum]
  rw [hsum] at hmc
  rw [← hrefl] at hmc
  rw [← hdouble] at hmc
  exact mc_def.mp hmc

/- ## Small bounds from stuffle identities -/

lemma sm_H22 (hp7 : 7 ≤ p) : SM 1 (H22 p) := by
  have h := H22_eq (p := p)
  have h1 : SM 2 ((qq p p)^2) := ((sm_qq_p hp7).mul (sm_qq_p hp7)).of_eq (by ring)
  have h2 : SM 1 ((qq p p)^2 - rr p p) := (h1.mono (by decide)).sub (sm_rr_p hp7)
  have h3 := h2.mul_right (sm_two_inv (p := p) (by omega))
  rw [h]
  exact h3.of_eq (div_eq_mul_inv _ _).symm

lemma sm_H31 (hp7 : 7 ≤ p) : SM 1 (H31 p) := by
  have hsum : SM 1 (H31 p + H13 p) := by
    rw [H31_add_H13]
    have h1 : SM 4 (hh p p * cc p p) := (sm_hh_p hp7).mul (sm_cc_p hp7)
    exact (h1.mono (by decide)).sub (sm_rr_p hp7)
  have hdiff := rev4 hp7
  have h2 : SM 1 (2 * H31 p) := (hsum.sub hdiff).of_eq (by ring)
  exact sm_cancel_unit (norm_two_eq_one (by omega)) h2

lemma sm_H13 (hp7 : 7 ≤ p) : SM 1 (H13 p) := by
  have := (rev4 hp7).add (sm_H31 hp7)
  exact this.of_eq (by ring)

/- ## R2 : truncation of the key identity -/

lemma ES1_iv (k : ℕ) : ES1 (Ico 1 k) (iv p) = hh p k := rfl

lemma PS2_iv (k : ℕ) : PS 2 (Ico 1 k) (iv p) = qq p k := rfl

lemma ES2_iv (k : ℕ) : ES2 (Ico 1 k) (iv p) = ee2 p k := rfl

lemma R2 (hp7 : 7 ≤ p) :
    MC 4 (hh p p) ((p:ℚ_[p])*qq p p - (p:ℚ_[p])^2*T1 p + (p:ℚ_[p])^3*E2s p) := by
  have hp2 : p ≠ 2 := by omega
  have hkey := key_identity_H1 (p := p) hp2
  have hpt : ∀ k ∈ Ico 1 p, MC 3 ((iv p k)^2 * ∏ i ∈ Ico 1 k, (1 - (p:ℚ_[p]) * iv p i))
      ((iv p k)^2 - (p:ℚ_[p])*((iv p k)^2 * hh p k)
        + (p:ℚ_[p])^2*((iv p k)^2 * ee2 p k)) := by
    intro k hk
    have hsub : k ≤ p := by rw [mem_Ico] at hk; omega
    have hf : ∀ i ∈ Ico 1 k, SM 0 (iv p i) := fun i hi => sm_iv (Ico_subset_of_le hsub hi)
    have hc : SM 1 (-(p:ℚ_[p])) := sm_p.neg
    have ht := prod_trunc2 (a := 1) hp7 hf hc
    have hprod_eq : (∏ i ∈ Ico 1 k, (1 - (p:ℚ_[p]) * iv p i))
        = ∏ i ∈ Ico 1 k, (1 + (-(p:ℚ_[p])) * iv p i) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [hprod_eq]
    have hml := MC.mul_left ((iv p k)^2) (ht.mono (by decide : 3 ≤ 3*1)) (sm_iv_pow hk 2)
    refine hml.trans (MC.of_eq ?_)
    rw [ES1_iv, ES2_iv]
    ring
  have hmc := MC.sum hpt
  have hsum : ∑ k ∈ Ico 1 p, ((iv p k)^2 - (p:ℚ_[p])*((iv p k)^2 * hh p k)
      + (p:ℚ_[p])^2*((iv p k)^2 * ee2 p k))
      = qq p p - (p:ℚ_[p])*T1 p + (p:ℚ_[p])^2*E2s p := by
    unfold qq T1 E2s
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum] at hmc
  have hfin := MC.mul_sm (a := 1) (p:ℚ_[p]) hmc sm_p
  rw [← hkey] at hfin
  refine hfin.trans (MC.of_eq (by ring))

/- ## (a′) : truncation of the Vandermonde identity -/

lemma ES1_sq (m : ℕ) : ES1 (Ico 1 m) (fun i => (iv p i)^2) = qq p m := rfl

lemma PS2_sq (m : ℕ) : PS 2 (Ico 1 m) (fun i => (iv p i)^2) = rr p m := by
  unfold PS rr
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma ES2_sq (m : ℕ) : ES2 (Ico 1 m) (fun i => (iv p i)^2)
    = ((qq p m)^2 - rr p m)/2 := by
  unfold ES2
  rw [ES1_sq, PS2_sq]

lemma e2q_eq (m : ℕ) : ((qq p m)^2 - rr p m)/2 = ∑ b ∈ Ico 1 m, (iv p b)^2 * qq p b := by
  have h := sum_mul_sum_split m (fun k => (iv p k)^2) (fun k => (iv p k)^2)
  have hC : ∑ k ∈ Ico 1 m, (iv p k)^2*(iv p k)^2 = ∑ k ∈ Ico 1 m, (iv p k)^4 := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold qq rr
  linear_combination h/2 + hC/2

lemma S1_eval : ∑ k ∈ range p, qq p (k+1) = (p:ℚ_[p]) * qq p p - hh p p := by
  have h := sum_swap_prefix p (fun j => (iv p j)^2)
  have hpt : ∀ j ∈ Ico 1 p, ((p:ℚ_[p]) - (j:ℚ_[p])) * (iv p j)^2
      = (p:ℚ_[p]) * (iv p j)^2 - iv p j := by
    intro j hj
    have h2 : iv p j * (j:ℚ_[p]) = 1 := iv_mul_cancel (by rw [mem_Ico] at hj; omega)
    linear_combination (-(iv p j)) * h2
  unfold qq hh
  rw [h, Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma S2_eval : ∑ k ∈ range p, ((qq p (k+1))^2 - rr p (k+1))/2
    = (p:ℚ_[p]) * H22 p - H21 p := by
  have he : ∀ k ∈ range p, ((qq p (k+1))^2 - rr p (k+1))/2
      = ∑ b ∈ Ico 1 (k+1), (iv p b)^2 * qq p b := fun k _ => e2q_eq (k+1)
  rw [Finset.sum_congr rfl he, sum_swap_prefix p (fun b => (iv p b)^2 * qq p b)]
  have hpt : ∀ b ∈ Ico 1 p, ((p:ℚ_[p]) - (b:ℚ_[p])) * ((iv p b)^2 * qq p b)
      = (p:ℚ_[p]) * ((iv p b)^2 * qq p b) - iv p b * qq p b := by
    intro b hb
    have h2 : iv p b * (b:ℚ_[p]) = 1 := iv_mul_cancel (by rw [mem_Ico] at hb; omega)
    linear_combination (-(iv p b) * qq p b) * h2
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold H22 H21
  rfl

lemma aprime (hp7 : 7 ≤ p) :
    SM 4 (((p:ℚ_[p])*qq p p - hh p p)
      - (p:ℚ_[p])^2*((p:ℚ_[p])*H22 p - H21 p)) := by
  have hp2 : p ≠ 2 := by omega
  have hvdm := vandermonde_p (p := p) hp2
  have hpt : ∀ k ∈ range p, MC 6 (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p])^2 * (iv p i)^2))
      (1 - (p:ℚ_[p])^2 * qq p (k+1)
        + (p:ℚ_[p])^4 * (((qq p (k+1))^2 - rr p (k+1))/2)) := by
    intro k hk
    have hsub : k+1 ≤ p := Finset.mem_range.mp hk
    have hf : ∀ i ∈ Ico 1 (k+1), SM 0 ((iv p i)^2) :=
      fun i hi => sm_iv_pow (Ico_subset_of_le hsub hi) 2
    have hc : SM 2 (-((p:ℚ_[p])^2)) := (sm_ppow 2).neg
    have ht := prod_trunc2 (a := 2) hp7 hf hc
    have hprod_eq : (∏ i ∈ Ico 1 (k+1), (1 - (p:ℚ_[p])^2 * (iv p i)^2))
        = ∏ i ∈ Ico 1 (k+1), (1 + (-((p:ℚ_[p])^2)) * (iv p i)^2) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [hprod_eq]
    refine (ht.mono (by norm_num : 6 ≤ 3*2)).trans (MC.of_eq ?_)
    rw [ES1_sq, ES2_sq]
    ring
  have hmc := MC.sum hpt
  have hsum_eq : ∑ k ∈ range p, (1 - (p:ℚ_[p])^2 * qq p (k+1)
      + (p:ℚ_[p])^4 * (((qq p (k+1))^2 - rr p (k+1))/2))
      = (p:ℚ_[p]) - (p:ℚ_[p])^2 * (∑ k ∈ range p, qq p (k+1))
        + (p:ℚ_[p])^4 * (∑ k ∈ range p, ((qq p (k+1))^2 - rr p (k+1))/2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum_eq, S1_eval, S2_eval, ← hvdm] at hmc
  have h := mc_def.mp hmc
  have h2 : SM 6 ((p:ℚ_[p])^2 * (((p:ℚ_[p])*qq p p - hh p p)
      - (p:ℚ_[p])^2*((p:ℚ_[p])*H22 p - H21 p))) := h.of_eq (by ring)
  exact SM.cancel_ppow (n := 4) (k := 2) h2

/- ## γ and the E2s bound -/

lemma gam (hp7 : 7 ≤ p) : SM 2 (T1 p + H21 p - (p:ℚ_[p])*(E2s p + H22 p)) := by
  have h1 := aprime hp7
  have h2 := mc_def.mp (R2 hp7)
  have h3 : SM 4 ((p:ℚ_[p])^2 * (T1 p + H21 p - (p:ℚ_[p])*(E2s p + H22 p))) :=
    (h1.add h2).of_eq (by ring)
  exact SM.cancel_ppow (n := 2) (k := 2) h3

lemma sm_E2s (hp7 : 7 ≤ p) : SM 1 (E2s p) := by
  have h1 := gam hp7
  have h2 := rev3 hp7
  have h3 : SM 2 ((p:ℚ_[p]) * (E2s p + 2*H22 p + 2*H31 p)) := (h2.sub h1).of_eq (by ring)
  have h4 : SM 1 (E2s p + 2*H22 p + 2*H31 p) :=
    SM.cancel_ppow (n := 1) (k := 1) (h3.of_eq (by ring))
  have h5 : SM 1 (2*H22 p) := ((sm_ofNat 2).mul (sm_H22 hp7)).of_eq rfl
  have h6 : SM 1 (2*H31 p) := ((sm_ofNat 2).mul (sm_H31 hp7)).of_eq rfl
  exact ((h4.sub h5).sub h6).of_eq (by ring)

end A357674


-- ===== From Dev/P8a.lean =====

/- # Part A (`C(3p,p)`) and the diagonal terms `T_c`, `T_e` of part B -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma SM.pow1 {c : ℚ_[p]} (hc : SM 1 c) : ∀ k, SM k (c^k)
  | 0 => sm_one.of_eq (pow_zero c).symm
  | (k+1) => ((SM.pow1 hc k).mul hc).of_eq (pow_succ c k).symm

lemma ee2_eq (k : ℕ) : ee2 p k = ((hh p k)^2 - qq p k)/2 := rfl

lemma ey2_eq (j : ℕ) : ey2 p j = ((hy p j)^2 - qy p j)/2 := rfl

lemma sm_ee2_p (hp7 : 7 ≤ p) : SM 1 (ee2 p p) := by
  have h1 : SM 1 ((hh p p)^2) :=
    (((sm_hh_p hp7).mul (sm_hh_p hp7)).of_eq (sq (hh p p)).symm).mono (by decide)
  have h2 : SM 1 ((hh p p)^2 - qq p p) := h1.sub (sm_qq_p hp7)
  have h3 := h2.mul_right (sm_two_inv (p := p) (by omega))
  exact h3.of_eq ((div_eq_mul_inv _ _).symm.trans (ee2_eq p).symm)

lemma sm_ee2_k (hp7 : 7 ≤ p) {k : ℕ} (hk : k ≤ p) : SM 0 (ee2 p k) := by
  have h1 : SM 0 ((hh p k)^2) := ((sm_hh hk).mul (sm_hh hk)).of_eq (sq (hh p k)).symm
  have h2 : SM 0 ((hh p k)^2 - qq p k) := h1.sub (sm_qq hk)
  have h3 := h2.mul_right (sm_two_inv (p := p) (by omega))
  exact h3.of_eq ((div_eq_mul_inv _ _).symm.trans (ee2_eq k).symm)

lemma sm_ey2_k (hp7 : 7 ≤ p) (j : ℕ) : SM 0 (ey2 p j) := by
  have h1 : SM 0 ((hy p j)^2) := ((sm_hy j).mul (sm_hy j)).of_eq (sq (hy p j)).symm
  have h2 : SM 0 ((hy p j)^2 - qy p j) := h1.sub (sm_qy j)
  have h3 := h2.mul_right (sm_two_inv (p := p) (by omega))
  exact h3.of_eq ((div_eq_mul_inv _ _).symm.trans (ey2_eq j).symm)

lemma PS3_iv (k : ℕ) : PS 3 (Ico 1 k) (iv p) = cc p k := rfl

lemma PS4_iv (k : ℕ) : PS 4 (Ico 1 k) (iv p) = rr p k := rfl

lemma sm_ES3iv (hp7 : 7 ≤ p) : SM 2 (ES3 (Ico 1 p) (iv p)) := by
  have t1 : SM 2 ((hh p p)^3) :=
    ((((sm_hh_p hp7).mul (sm_hh_p hp7)).mul (sm_hh_p hp7)).of_eq (by ring)).mono
      (by norm_num)
  have t2 : SM 2 (3*(hh p p)*(qq p p)) :=
    ((((sm_ofNat 3).mul (sm_hh_p hp7)).mul (sm_qq_p hp7)).of_eq (by ring)).mono
      (by norm_num)
  have t3 : SM 2 (2*(cc p p)) := (sm_ofNat 2).mul (sm_cc_p hp7)
  have h : SM 2 ((hh p p)^3 - 3*(hh p p)*(qq p p) + 2*(cc p p)) := (t1.sub t2).add t3
  have h6 := sm_div_nat (c := 6) h (not_dvd_six hp7)
  unfold ES3
  rw [ES1_iv, PS2_iv, PS3_iv]
  exact h6.of_eq (by push_cast; ring)

lemma sm_ES4iv (hp7 : 7 ≤ p) : SM 1 (ES4 (Ico 1 p) (iv p)) := by
  have t1 : SM 1 ((hh p p)^4) :=
    (((((sm_hh_p hp7).mul (sm_hh_p hp7)).mul (sm_hh_p hp7)).mul
      (sm_hh_p hp7)).of_eq (by ring)).mono (by decide)
  have t2 : SM 1 (6*(hh p p)^2*(qq p p)) :=
    (((((sm_ofNat 6).mul (sm_hh_p hp7)).mul (sm_hh_p hp7)).mul
      (sm_qq_p hp7)).of_eq (by ring)).mono (by decide)
  have t3 : SM 1 (3*(qq p p)^2) :=
    ((((sm_ofNat 3).mul (sm_qq_p hp7)).mul (sm_qq_p hp7)).of_eq (by ring)).mono
      (by norm_num)
  have t4 : SM 1 (8*(hh p p)*(cc p p)) :=
    ((((sm_ofNat 8).mul (sm_hh_p hp7)).mul (sm_cc_p hp7)).of_eq (by ring)).mono
      (by norm_num)
  have t5 : SM 1 (6*(rr p p)) := (sm_ofNat 6).mul (sm_rr_p hp7)
  have h : SM 1 ((hh p p)^4 - 6*(hh p p)^2*(qq p p) + 3*(qq p p)^2
      + 8*(hh p p)*(cc p p) - 6*(rr p p)) := (((t1.sub t2).add t3).add t4).sub t5
  have h24 := sm_div_nat (c := 24) h (not_dvd_24 hp7)
  unfold ES4
  rw [ES1_iv, PS2_iv, PS3_iv, PS4_iv]
  exact h24.of_eq (by push_cast; ring)

lemma MC.sq {n : ℕ} {x v : ℚ_[p]} (h : MC n x v) (hx : SM 0 x) (hv : SM 0 v) :
    MC n (x^2) (v^2) := by
  have h2 := h.mul h hx hv
  exact (MC.of_eq (pow_two x)).trans (h2.trans (MC.of_eq (pow_two v).symm))

lemma td_vred1 {H Y E F : ℚ_[p]} (hH : SM 0 H) (hY : SM 0 Y)
    (hE : SM 0 E) (hF : SM 0 F) :
    MC 3 ((1 + (2*p:ℚ_[p]) * H + (2*p:ℚ_[p])^2 * E) * (1 + (p:ℚ_[p]) * Y + (p:ℚ_[p])^2 * F))
      (1 + (p:ℚ_[p])*(2*H + Y) + (p:ℚ_[p])^2*(F + 4*E + 2*H*Y)) := by
  apply MC.of_sub (d := 2*(p:ℚ_[p])^3*(H*F) + 4*(p:ℚ_[p])^4*(E*F) + 4*(p:ℚ_[p])^3*(E*Y))
  · ring
  · have u1 : SM 3 (2*(p:ℚ_[p])^3*(H*F)) :=
      ((sm_ofNat 2).mul ((sm_ppow 3).mul (hH.mul hF))).of_eq (by ring)
    have u2 : SM 3 (4*(p:ℚ_[p])^4*(E*F)) :=
      (((sm_ofNat 4).mul ((sm_ppow 4).mul (hE.mul hF))).of_eq (by ring)).mono (by decide)
    have u3 : SM 3 (4*(p:ℚ_[p])^3*(E*Y)) :=
      ((sm_ofNat 4).mul ((sm_ppow 3).mul (hE.mul hY))).of_eq (by ring)
    exact (u1.add u2).add u3

lemma td_vred2 {U W : ℚ_[p]} (hU : SM 0 U) (hW : SM 0 W) :
    MC 3 ((1 + (p:ℚ_[p])*U + (p:ℚ_[p])^2*W)^2)
      (1 + 2*(p:ℚ_[p])*U + (p:ℚ_[p])^2*(U^2 + 2*W)) := by
  apply MC.of_sub (d := 2*(p:ℚ_[p])^3*(U*W) + (p:ℚ_[p])^4*W^2)
  · ring
  · have u1 : SM 3 (2*(p:ℚ_[p])^3*(U*W)) :=
      ((sm_ofNat 2).mul ((sm_ppow 3).mul (hU.mul hW))).of_eq (by ring)
    have u2 : SM 3 ((p:ℚ_[p])^4*W^2) :=
      ((sm_ppow 4).mul ((hW.mul hW).of_eq (pow_two W).symm)).mono (by decide)
    exact u1.add u2

lemma sm_1pUW {U W : ℚ_[p]} (hU : SM 0 U) (hW : SM 0 W) :
    SM 0 (1 + (p:ℚ_[p])*U + (p:ℚ_[p])^2*W) := by
  have u1 : SM 0 ((p:ℚ_[p])*U) := (sm_p.mono (by decide)).mul hU
  have u2 : SM 0 ((p:ℚ_[p])^2*W) := ((sm_ppow 2).mono (by decide)).mul hW
  exact (sm_one.add u1).add u2

lemma trunc_sq_v {c H E2 E3 E4 : ℚ_[p]} (hc0 : SM 0 c) (hH : SM 0 H)
    (hE2 : SM 0 E2) (hE3 : SM 0 E3) (hE4 : SM 0 E4) :
    SM 0 (1 + c * H + c^2 * E2 + c^3 * E3 + c^4 * E4) := by
  have u1 : SM 0 (c * H) := hc0.mul hH
  have u2 : SM 0 (c^2 * E2) := (sm_pow0 hc0 2).mul hE2
  have u3 : SM 0 (c^3 * E3) := (sm_pow0 hc0 3).mul hE3
  have u4 : SM 0 (c^4 * E4) := (sm_pow0 hc0 4).mul hE4
  exact (((sm_one.add u1).add u2).add u3).add u4

lemma trunc_sq_tail {c H E2 E3 E4 : ℚ_[p]} (hc : SM 1 c) (sH : SM 2 H)
    (sE2 : SM 1 E2) (sE3 : SM 2 E3) (sE4 : SM 1 E4) :
    SM 5 (2*c^2*H^2 + c^3*(2*E3 + 2*H*E2) + c^4*(2*E4 + 2*H*E3 + E2^2)
      + c^5*(2*H*E4 + 2*E2*E3) + c^6*(2*E2*E4 + E3^2) + c^7*(2*E3*E4) + c^8*E4^2) := by
  have hsmH : SM 0 H := sH.mono (by decide)
  have hsmE2 : SM 0 E2 := sE2.mono (by decide)
  have hsmE3 : SM 0 E3 := sE3.mono (by decide)
  have hsmE4 : SM 0 E4 := sE4.mono (by decide)
  have b1 : SM 5 (2*c^2*H^2) := by
    have := (sm_ofNat 2).mul ((SM.pow1 hc 2).mul (sH.mul sH))
    exact (this.of_eq (by ring)).mono (by decide)
  have b2 : SM 5 (c^3*(2*E3 + 2*H*E2)) := by
    have u1 : SM 2 (2*E3) := (sm_ofNat 2).mul sE3
    have u2 : SM 2 (2*H*E2) :=
      ((((sm_ofNat 2).mul sH).mul sE2).of_eq (by ring)).mono (by decide)
    exact (SM.pow1 hc 3).mul (u1.add u2)
  have b3 : SM 5 (c^4*(2*E4 + 2*H*E3 + E2^2)) := by
    have u1 : SM 1 (2*E4) := (sm_ofNat 2).mul sE4
    have u2 : SM 1 (2*H*E3) :=
      ((((sm_ofNat 2).mul sH).mul sE3).of_eq (by ring)).mono (by decide)
    have u3 : SM 1 (E2^2) := ((sE2.mul sE2).of_eq (sq E2).symm).mono (by decide)
    exact (SM.pow1 hc 4).mul ((u1.add u2).add u3)
  have b4 : SM 5 (c^5*(2*H*E4 + 2*E2*E3)) := by
    have u1 : SM 0 (2*H*E4) := (((sm_ofNat 2).mul hsmH).mul hsmE4).of_eq (by ring)
    have u2 : SM 0 (2*E2*E3) := (((sm_ofNat 2).mul hsmE2).mul hsmE3).of_eq (by ring)
    exact (SM.pow1 hc 5).mul (u1.add u2)
  have b5 : SM 5 (c^6*(2*E2*E4 + E3^2)) := by
    have u1 : SM 0 (2*E2*E4) := (((sm_ofNat 2).mul hsmE2).mul hsmE4).of_eq (by ring)
    have u2 : SM 0 (E3^2) := (hsmE3.mul hsmE3).of_eq (sq E3).symm
    exact (((SM.pow1 hc 6).mul (u1.add u2)).mono (by decide))
  have b6 : SM 5 (c^7*(2*E3*E4)) := by
    have u1 : SM 0 (2*E3*E4) := (((sm_ofNat 2).mul hsmE3).mul hsmE4).of_eq (by ring)
    exact ((SM.pow1 hc 7).mul u1).mono (by decide)
  have b7 : SM 5 (c^8*E4^2) := by
    have u1 : SM 0 (E4^2) := (hsmE4.mul hsmE4).of_eq (sq E4).symm
    exact ((SM.pow1 hc 8).mul u1).mono (by decide)
  exact (((((b1.add b2).add b3).add b4).add b5).add b6).add b7

/-- Squared truncated product: `(∏(1+c/i))² ≡ 1 + 2c·H₁ - c²·H₂ (mod p⁵)` for `SM 1 c`. -/
lemma trunc_sq (hp7 : 7 ≤ p) {c : ℚ_[p]} (hc : SM 1 c) :
    MC 5 ((∏ i ∈ Ico 1 p, (1 + c * iv p i))^2)
      (1 + 2*c*hh p p - c^2*qq p p) := by
  have hf : ∀ i ∈ Ico 1 p, SM 0 (iv p i) := fun i hi => sm_iv hi
  have ht := prod_trunc4 (a := 1) hp7 hf hc
  rw [ES1_iv, ES2_iv] at ht
  have hc0 : SM 0 c := hc.mono (by decide)
  have hx : SM 0 (∏ i ∈ Ico 1 p, (1 + c * iv p i)) := sm_prod_one_add hf hc0
  have hv := trunc_sq_v hc0 (sm_hh (le_refl p)) (sm_ee2_k hp7 (le_refl p))
    ((sm_ES3iv hp7).mono (by decide)) ((sm_ES4iv hp7).mono (by decide))
  have hsq := ht.sq hx hv
  set H := hh p p
  set E2 := ee2 p p
  set E3 := ES3 (Ico 1 p) (iv p)
  set E4 := ES4 (Ico 1 p) (iv p)
  refine hsq.trans (MC.of_sub
    (d := 2*c^2*H^2 + c^3*(2*E3 + 2*H*E2) + c^4*(2*E4 + 2*H*E3 + E2^2)
      + c^5*(2*H*E4 + 2*E2*E3) + c^6*(2*E2*E4 + E3^2) + c^7*(2*E3*E4) + c^8*E4^2)
    ?_ (trunc_sq_tail hc (sm_hh_p hp7) (sm_ee2_p hp7) (sm_ES3iv hp7) (sm_ES4iv hp7)))
  · have hee2 : E2 = (H^2 - qq p p)/2 := ee2_eq p
    linear_combination (2*c^2) * hee2

/-- `T_c = C(2p-1, p-1)² ≡ 1 + 2p·H₁ - p²·H₂ (mod p⁵)`. -/
lemma partTc (hp7 : 7 ≤ p) :
    MC 5 ((((2*p - 1).choose (p-1) : ℕ) : ℚ_[p])^2)
      (1 + 2*(p:ℚ_[p])*hh p p - (p:ℚ_[p])^2*qq p p) := by
  rw [binom_2pm1]
  exact trunc_sq hp7 sm_p

/-- `T_e = C(3p-1, 2p)² ≡ 1 + 4p·H₁ - 4p²·H₂ (mod p⁵)`. -/
lemma partTe (hp7 : 7 ≤ p) :
    MC 5 ((((3*p - 1).choose (2*p) : ℕ) : ℚ_[p])^2)
      (1 + 4*(p:ℚ_[p])*hh p p - 4*(p:ℚ_[p])^2*qq p p) := by
  rw [binom_3pm1]
  have hc : SM 1 (2*p:ℚ_[p]) := ((sm_ofNat 2).mul sm_p).of_eq rfl
  exact (trunc_sq hp7 hc).trans (MC.of_eq (by ring))

/-- Part A : `C(3p, p) ≡ 3 + 6p·H₁ - 6p²·H₂ (mod p⁵)`. -/
lemma partA (hp7 : 7 ≤ p) :
    MC 5 ((((3*p).choose p : ℕ) : ℚ_[p]))
      (3 + 6*(p:ℚ_[p])*hh p p - 6*(p:ℚ_[p])^2*qq p p) := by
  rw [binom_3p]
  have hf : ∀ i ∈ Ico 1 p, SM 0 (iv p i) := fun i hi => sm_iv hi
  have hc : SM 1 (2*p:ℚ_[p]) := ((sm_ofNat 2).mul sm_p).of_eq rfl
  have ht := prod_trunc4 (a := 1) hp7 hf hc
  rw [ES1_iv, ES2_iv] at ht
  have h3 := MC.mul_left (3:ℚ_[p]) ht (sm_ofNat 3)
  refine h3.trans (MC.of_sub
    (d := 6*(p:ℚ_[p])^2*(hh p p)^2 + 24*(p:ℚ_[p])^3*(ES3 (Ico 1 p) (iv p))
      + 48*(p:ℚ_[p])^4*(ES4 (Ico 1 p) (iv p))) ?_ ?_)
  · have hee2 : ee2 p p = ((hh p p)^2 - qq p p)/2 := ee2_eq p
    linear_combination (12*(p:ℚ_[p])^2) * hee2
  · have b1 : SM 5 (6*(p:ℚ_[p])^2*(hh p p)^2) := by
      have := (sm_ofNat 6).mul ((sm_ppow 2).mul ((sm_hh_p hp7).mul (sm_hh_p hp7)))
      exact (this.of_eq (by ring)).mono (by decide)
    have b2 : SM 5 (24*(p:ℚ_[p])^3*(ES3 (Ico 1 p) (iv p))) := by
      have := (sm_ofNat 24).mul ((sm_ppow 3).mul (sm_ES3iv hp7))
      exact this.of_eq (by ring)
    have b3 : SM 5 (48*(p:ℚ_[p])^4*(ES4 (Ico 1 p) (iv p))) := by
      have := (sm_ofNat 48).mul ((sm_ppow 4).mul (sm_ES4iv hp7))
      exact this.of_eq (by ring)
    exact (b1.add b2).add b3

end A357674


-- ===== From Dev/P8b.lean =====

/- # The `T_b` block of part B -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma partTb (hp7 : 7 ≤ p) :
    MC 5 (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
      ((p:ℚ_[p])^2*qq p p + 2*(p:ℚ_[p])^3*T1 p + (p:ℚ_[p])^4*A2 p
        + 2*(p:ℚ_[p])^4*E2s p) := by
  have hre : ∀ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = (p:ℚ_[p])^2 * ((iv p k)^2 * (∏ i ∈ Ico 1 k, (1 + (p:ℚ_[p]) * iv p i))^2) := by
    intro k hk
    rw [binom_main (by rw [mem_Ico] at hk; omega)]
    ring
  rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
  have hpt : ∀ k ∈ Ico 1 p,
      MC 3 ((iv p k)^2 * (∏ i ∈ Ico 1 k, (1 + (p:ℚ_[p]) * iv p i))^2)
        ((iv p k)^2 + 2*(p:ℚ_[p])*((iv p k)^2*hh p k)
          + (p:ℚ_[p])^2*((iv p k)^2*(hh p k)^2)
          + 2*(p:ℚ_[p])^2*((iv p k)^2*ee2 p k)) := by
    intro k hk
    have hkp : k ≤ p := by rw [mem_Ico] at hk; omega
    have hf : ∀ i ∈ Ico 1 k, SM 0 (iv p i) := fun i hi => sm_iv (Ico_subset_of_le hkp hi)
    have ht := prod_trunc2 (a := 1) hp7 hf (sm_p (p := p))
    rw [ES1_iv, ES2_iv] at ht
    have hx : SM 0 (∏ i ∈ Ico 1 k, (1 + (p:ℚ_[p]) * iv p i)) :=
      sm_prod_one_add hf (sm_p.mono (by decide))
    have hv : SM 0 (1 + (p:ℚ_[p]) * hh p k + (p:ℚ_[p])^2 * ee2 p k) :=
      sm_1pUW (sm_hh hkp) (sm_ee2_k hp7 hkp)
    have hsq := ((ht.mono (by decide : 3 ≤ 3*1)).sq hx hv)
    have hred : MC 3 ((1 + (p:ℚ_[p]) * hh p k + (p:ℚ_[p])^2 * ee2 p k)^2)
        (1 + 2*(p:ℚ_[p])*hh p k + (p:ℚ_[p])^2*((hh p k)^2 + 2*ee2 p k)) :=
      td_vred2 (sm_hh hkp) (sm_ee2_k hp7 hkp)
    have hmul := MC.mul_left ((iv p k)^2) (hsq.trans hred) (sm_iv_pow hk 2)
    exact hmul.trans (MC.of_eq (by ring))
  have hmc := MC.sum hpt
  have hsum : ∑ k ∈ Ico 1 p, ((iv p k)^2 + 2*(p:ℚ_[p])*((iv p k)^2*hh p k)
      + (p:ℚ_[p])^2*((iv p k)^2*(hh p k)^2) + 2*(p:ℚ_[p])^2*((iv p k)^2*ee2 p k))
      = qq p p + 2*(p:ℚ_[p])*T1 p + (p:ℚ_[p])^2*A2 p + 2*(p:ℚ_[p])^2*E2s p := by
    unfold qq T1 A2 E2s
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum] at hmc
  have hfin := MC.mul_sm (a := 2) ((p:ℚ_[p])^2) hmc (sm_ppow 2)
  exact hfin.trans (MC.of_eq (by ring))

end A357674


-- ===== From Dev/P8c.lean =====

/- # The `T_d` block of part B -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma ES1_hy (j : ℕ) : ES1 (Ico (j+1) p) (iv p) = hy p j := rfl

lemma ES2_hy (j : ℕ) : ES2 (Ico (j+1) p) (iv p) = ey2 p j := rfl

lemma mem_Ico_tail {i j : ℕ} (hi : i ∈ Ico (j+1) p) : i ∈ Ico 1 p := by
  rw [mem_Ico] at *
  omega

lemma sm_T1_0 : SM 0 (T1 p) := by
  apply SM.sum
  intro k hk
  exact (sm_iv_pow hk 2).mul (sm_hh (by rw [mem_Ico] at hk; omega))

lemma sm_A2_1 (hp7 : 7 ≤ p) : SM 1 (A2 p) := by
  rw [A2_eq]
  exact (sm_H22 hp7).add (((sm_ofNat 2).mul (sm_E2s hp7)).of_eq rfl)

/-- Truncation target for the `T_d` pointwise analysis. -/
private noncomputable def tdT (p : ℕ) [Fact p.Prime] (j : ℕ) : ℚ_[p] :=
  (iv p j)^2
    + 2*(p:ℚ_[p])*((iv p j)^2*hh p j)
    + 2*(p:ℚ_[p])*(hh p p*(iv p j)^2)
    - 2*(p:ℚ_[p])*(iv p j)^3
    + (p:ℚ_[p])^2*(2*((iv p j)^2*(hh p j)^2)
      - 4*((iv p j)^3*hh p j)
      + 3*(iv p j)^4
      - 3*((iv p j)^2*qq p j)
      + 4*(hh p p*((iv p j)^2*hh p j))
      - 4*(hh p p*(iv p j)^3)
      + (2*(hh p p)^2 - qq p p)*(iv p j)^2)

private lemma td_of_eq {j : ℕ} (hj1 : 1 ≤ j) (hjp' : j + 1 ≤ p) :
    (iv p j)^2 * (1 + 2*(p:ℚ_[p])*(2*hh p j + hy p j)
        + (p:ℚ_[p])^2*((2*hh p j + hy p j)^2
          + 2*(ey2 p j + 4*ee2 p j + 2*(hh p j)*(hy p j))))
      = tdT p j := by
  unfold tdT
  have hy_eq : hy p j = hh p p - hh p j - iv p j := by
    have h1 := hh_split (p := p) (j := j) (by omega) hjp'
    have h2 := hh_succ (p := p) (k := j) hj1
    rw [h2] at h1
    linear_combination -h1
  have qy_eq : qy p j = qq p p - qq p j - (iv p j)^2 := by
    have h1 := qq_split (p := p) (j := j) (by omega) hjp'
    have h2 := qq_succ (p := p) (k := j) hj1
    rw [h2] at h1
    linear_combination -h1
  rw [ey2_eq, ee2_eq, hy_eq, qy_eq]
  ring

private lemma td_pointwise (hp7 : 7 ≤ p) : ∀ j ∈ Ico 1 p,
    MC 3 ((iv p j)^2 *
        ((∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
          * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t))^2)
      (tdT p j) := by
  intro j hj
  have hj1 : 1 ≤ j := by rw [mem_Ico] at hj; omega
  have hjp : j ≤ p := by rw [mem_Ico] at hj; omega
  have hjp' : j + 1 ≤ p := by rw [mem_Ico] at hj; omega
  have hfA : ∀ i ∈ Ico 1 j, SM 0 (iv p i) := fun i hi => sm_iv (Ico_subset_of_le hjp hi)
  have hcA : SM 1 (2*p:ℚ_[p]) := ((sm_ofNat 2).mul sm_p).of_eq rfl
  have htA := prod_trunc2 (a := 1) hp7 hfA hcA
  rw [ES1_iv, ES2_iv] at htA
  have hfY : ∀ i ∈ Ico (j+1) p, SM 0 (iv p i) := fun i hi => sm_iv (mem_Ico_tail hi)
  have htY := prod_trunc2 (a := 1) hp7 hfY (sm_p (p := p))
  rw [ES1_hy, ES2_hy] at htY
  have hxA : SM 0 (∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u)) :=
    sm_prod_one_add hfA (hcA.mono (by decide))
  have hxY : SM 0 (∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t)) :=
    sm_prod_one_add hfY (sm_p.mono (by decide))
  have hsmhh : SM 0 (hh p j) := sm_hh hjp
  have hsmee : SM 0 (ee2 p j) := sm_ee2_k hp7 hjp
  have hsmhy : SM 0 (hy p j) := sm_hy j
  have hsmey : SM 0 (ey2 p j) := sm_ey2_k hp7 j
  have hvA : SM 0 (1 + (2*p:ℚ_[p]) * hh p j + (2*p:ℚ_[p])^2 * ee2 p j) := by
    have u1 : SM 0 ((2*p:ℚ_[p]) * hh p j) := ((hcA.mono (by decide)).mul hsmhh)
    have u2 : SM 0 ((2*p:ℚ_[p])^2 * ee2 p j) :=
      (((SM.pow1 hcA 2).mono (by decide)).mul hsmee)
    exact (sm_one.add u1).add u2
  have hvY : SM 0 (1 + (p:ℚ_[p]) * hy p j + (p:ℚ_[p])^2 * ey2 p j) := sm_1pUW hsmhy hsmey
  have hAY := (htA.mono (by decide : 3 ≤ 3*1)).mul (htY.mono (by decide : 3 ≤ 3*1)) hxA hvY
  have hu0 : SM 0 (2*hh p j + hy p j) :=
    (((sm_ofNat 2).mul hsmhh).of_eq rfl).add hsmhy
  have hw0 : SM 0 (ey2 p j + 4*ee2 p j + 2*(hh p j)*(hy p j)) := by
    have u1 : SM 0 (4*ee2 p j) := (sm_ofNat 4).mul hsmee
    have u2 : SM 0 (2*(hh p j)*(hy p j)) :=
      (((sm_ofNat 2).mul hsmhh).mul hsmhy).of_eq (by ring)
    exact (hsmey.add u1).add u2
  have hAY2 := ((hAY.trans (td_vred1 hsmhh hsmhy hsmee hsmey)).sq (hxA.mul hxY)
    (sm_1pUW hu0 hw0)).trans (td_vred2 hu0 hw0)
  exact (MC.mul_left ((iv p j)^2) hAY2 (sm_iv_pow hj 2)).trans
    (MC.of_eq (td_of_eq hj1 hjp'))

private lemma td_sum :
    ∑ j ∈ Ico 1 p, tdT p j
      = qq p p + 2*(p:ℚ_[p])*T1 p + 2*(p:ℚ_[p])*(hh p p*qq p p) - 2*(p:ℚ_[p])*cc p p
        + (p:ℚ_[p])^2*(2*A2 p - 4*H13 p + 3*rr p p - 3*H22 p
          + 4*(hh p p*T1 p) - 4*(hh p p*cc p p) + (2*(hh p p)^2 - qq p p)*qq p p) := by
  unfold tdT T1 cc A2 H13 rr H22 qq
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

private noncomputable def tdD (p : ℕ) [Fact p.Prime] : ℚ_[p] :=
  8*(p:ℚ_[p])^3*(hh p p*qq p p) - 8*(p:ℚ_[p])^3*cc p p
    + 4*(p:ℚ_[p])^4*(2*A2 p - 4*H13 p + 3*rr p p - 3*H22 p
      + 4*(hh p p*T1 p) - 4*(hh p p*cc p p) + (2*(hh p p)^2 - qq p p)*qq p p)

private lemma td_tail (hp7 : 7 ≤ p) : SM 5 (tdD p) := by
  unfold tdD
  have b1 : SM 5 (8*(p:ℚ_[p])^3*(hh p p*qq p p)) := by
    have := (sm_ofNat 8).mul ((sm_ppow 3).mul ((sm_hh_p hp7).mul (sm_qq_p hp7)))
    exact (this.of_eq (by ring)).mono (by decide)
  have b2 : SM 5 (8*(p:ℚ_[p])^3*cc p p) := by
    have := (sm_ofNat 8).mul ((sm_ppow 3).mul (sm_cc_p hp7))
    exact this.of_eq (by ring)
  have b3 : SM 5 (4*(p:ℚ_[p])^4*(2*A2 p - 4*H13 p + 3*rr p p - 3*H22 p
      + 4*(hh p p*T1 p) - 4*(hh p p*cc p p) + (2*(hh p p)^2 - qq p p)*qq p p)) := by
    have s1 : SM 1 (2*A2 p) := (sm_ofNat 2).mul (sm_A2_1 hp7)
    have s2 : SM 1 (4*H13 p) := (sm_ofNat 4).mul (sm_H13 hp7)
    have s3 : SM 1 (3*rr p p) := (sm_ofNat 3).mul (sm_rr_p hp7)
    have s4 : SM 1 (3*H22 p) := (sm_ofNat 3).mul (sm_H22 hp7)
    have s5 : SM 1 (4*(hh p p*T1 p)) :=
      ((sm_ofNat 4).mul ((sm_hh_p hp7).mul sm_T1_0)).mono (by decide)
    have s6 : SM 1 (4*(hh p p*cc p p)) :=
      ((sm_ofNat 4).mul ((sm_hh_p hp7).mul (sm_cc_p hp7))).mono (by decide)
    have s7 : SM 1 ((2*(hh p p)^2 - qq p p)*qq p p) := by
      have u1 : SM 1 (2*(hh p p)^2) :=
        ((sm_ofNat 2).mul (((sm_hh_p hp7).mul (sm_hh_p hp7)).of_eq
          (pow_two (hh p p)).symm)).mono (by decide)
      exact ((u1.sub (sm_qq_p hp7)).mul (sm_qq_p hp7)).mono (by decide)
    have hin : SM 1 (2*A2 p - 4*H13 p + 3*rr p p - 3*H22 p
        + 4*(hh p p*T1 p) - 4*(hh p p*cc p p) + (2*(hh p p)^2 - qq p p)*qq p p) :=
      (((((s1.sub s2).add s3).sub s4).add s5).sub s6).add s7
    have := (sm_ofNat 4).mul ((sm_ppow 4).mul hin)
    exact this.of_eq (by ring)
  exact (b1.sub b2).add b3

lemma partTd (hp7 : 7 ≤ p) :
    MC 5 (∑ j ∈ Ico 1 p, (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])^2)
      (4*(p:ℚ_[p])^2*qq p p + 8*(p:ℚ_[p])^3*T1 p) := by
  have hre : ∀ j ∈ Ico 1 p, (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])^2
      = 4*(p:ℚ_[p])^2 * ((iv p j)^2 *
        ((∏ u ∈ Ico 1 j, (1 + (2*p:ℚ_[p]) * iv p u))
          * ∏ t ∈ Ico (j+1) p, (1 + (p:ℚ_[p]) * iv p t))^2) := by
    intro j hj
    rw [binom_td hj]
    ring
  rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
  have hmc := MC.sum (td_pointwise hp7)
  rw [td_sum] at hmc
  have hfin := MC.mul_sm (a := 2) (4*(p:ℚ_[p])^2) hmc
    (((sm_ofNat 4).mul (sm_ppow 2)).of_eq rfl)
  refine hfin.trans (MC.of_sub (d := tdD p) ?_ ?_)
  · unfold tdD
    ring
  · exact td_tail hp7

end A357674


-- ===== From Dev/P9.lean =====

/- # Final assembly: `A357674 p ≡ A357674 1 [MOD p^5]` -/



namespace A357674

variable {p : ℕ} [hp : Fact p.Prime]

lemma MC.pow {n : ℕ} {x v : ℚ_[p]} (h : MC n x v) (hx : SM 0 x) (hv : SM 0 v) :
    ∀ k, MC n (x^k) (v^k)
  | 0 => MC.of_eq (by rw [pow_zero, pow_zero])
  | (k+1) => by
    have hk := MC.pow h hx hv k
    have hm := hk.mul h (sm_pow0 hx k) hv
    exact (MC.of_eq (pow_succ x k)).trans (hm.trans (MC.of_eq (pow_succ v k).symm))

/-- The nonlinear part of `(3+c)⁴(3+s)³` is `O(p⁶)` when `c,s = O(p³)`. -/
lemma sm_R {c s : ℚ_[p]} (hc3 : SM 3 c) (hs3 : SM 3 s) :
    SM 5 ((3+c)^4*(3+s)^3 - 2187 - 729*(4*c+3*s)) := by
  have hc0 : SM 0 c := hc3.mono (Nat.zero_le 3)
  have hs0 : SM 0 s := hs3.mono (Nat.zero_le 3)
  have hA : SM 0 (3+c) := (sm_ofNat 3).add hc0
  have hB : SM 0 (3+s) := (sm_ofNat 3).add hs0
  have hP : SM 0 ((3+s)^3*((3+c)^2 + 6*(3+c) + 27)) :=
    (sm_pow0 hB 3).mul (((sm_pow0 hA 2).add ((sm_ofNat 6).mul hA)).add (sm_ofNat 27))
  have hQ : SM 0 (108*((3+s)^2 + 3*(3+s) + 9)) :=
    (sm_ofNat 108).mul (((sm_pow0 hB 2).add ((sm_ofNat 3).mul hB)).add (sm_ofNat 9))
  have hR : SM 0 (81*((3+s) + 6)) := (sm_ofNat 81).mul (hB.add (sm_ofNat 6))
  have b1 : SM 5 (c*c*((3+s)^3*((3+c)^2 + 6*(3+c) + 27))) :=
    ((hc3.mul hc3).mul hP).mono (by decide)
  have b2 : SM 5 (c*s*(108*((3+s)^2 + 3*(3+s) + 9))) :=
    ((hc3.mul hs3).mul hQ).mono (by decide)
  have b3 : SM 5 (s*s*(81*((3+s) + 6))) :=
    ((hs3.mul hs3).mul hR).mono (by decide)
  exact ((b1.add b2).add b3).of_eq (by ring)

/-- Splitting the second sum into its five blocks. -/
lemma S2_split :
    ∑ k ∈ range (2*p + 1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = 1 + (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
        + (((2*p - 1).choose (p-1) : ℕ) : ℚ_[p])^2
        + (∑ j ∈ Ico 1 p, (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])^2)
        + (((3*p - 1).choose (2*p) : ℕ) : ℚ_[p])^2 := by
  have hp1 : 1 ≤ p := hp.out.pos
  have e0 : ∑ k ∈ range (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = (((p + 0 - 1).choose 0 : ℕ) : ℚ_[p])^2
        + ∑ k ∈ Ico 1 (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2 := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 2*p+1) _
  have e1 : ∑ k ∈ Ico 1 (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
        + ∑ k ∈ Ico p (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2 :=
    (Finset.sum_Ico_consecutive _ (by omega : 1 ≤ p) (by omega : p ≤ 2*p+1)).symm
  have e2 : ∑ k ∈ Ico p (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = (((p + p - 1).choose p : ℕ) : ℚ_[p])^2
        + ∑ k ∈ Ico (p+1) (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2 :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega : p < 2*p+1) _
  have e3 : ∑ k ∈ Ico (p+1) (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = (∑ k ∈ Ico (p+1) (2*p), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
        + (((p + 2*p - 1).choose (2*p) : ℕ) : ℚ_[p])^2 :=
    Finset.sum_Ico_succ_top (by omega : p+1 ≤ 2*p) _
  have e4 : ∑ k ∈ Ico (p+1) (2*p), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2
      = ∑ j ∈ Ico 1 p, (((2*p + j - 1).choose (p + j) : ℕ) : ℚ_[p])^2 := by
    apply Finset.sum_nbij' (i := fun k => k - p) (j := fun j => p + j)
    · intro a ha
      rw [mem_Ico] at *
      omega
    · intro a ha
      rw [mem_Ico] at *
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
    · intro a ha
      rw [mem_Ico] at ha
      rw [show 2*p + (a - p) - 1 = p + a - 1 by omega, show p + (a - p) = a by omega]
  have ef0 : (((p + 0 - 1).choose 0 : ℕ) : ℚ_[p])^2 = 1 := by
    rw [Nat.choose_zero_right, Nat.cast_one, one_pow]
  have efp : (((p + p - 1).choose p : ℕ) : ℚ_[p])^2
      = (((2*p - 1).choose (p-1) : ℕ) : ℚ_[p])^2 := by
    rw [show p + p - 1 = 2*p - 1 by omega]
    rw [show (2*p-1).choose p = (2*p-1).choose (p-1) by
      rw [← Nat.choose_symm (by omega : p ≤ 2*p-1), show 2*p-1-p = p-1 by omega]]
  have ef2p : (((p + 2*p - 1).choose (2*p) : ℕ) : ℚ_[p])^2
      = (((3*p - 1).choose (2*p) : ℕ) : ℚ_[p])^2 := by
    rw [show p + 2*p - 1 = 3*p - 1 by omega]
  rw [e0, e1, e2, e3, e4, ef0, efp, ef2p]
  ring

/-- `S2 ≡ 3 + 6p·H₁ + 10p³·T1 (mod p⁵)`. -/
lemma partS2 (hp7 : 7 ≤ p) :
    MC 5 (∑ k ∈ range (2*p + 1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
      (3 + 6*(p:ℚ_[p])*hh p p + 10*(p:ℚ_[p])^3*T1 p) := by
  rw [S2_split]
  have h := ((((MC.rfl (n := 5) (x := (1:ℚ_[p]))).add (partTb hp7)).add
    (partTc hp7)).add (partTd hp7)).add (partTe hp7)
  refine h.trans (MC.of_sub (d := (p:ℚ_[p])^4*A2 p + 2*(p:ℚ_[p])^4*E2s p) ?_ ?_)
  · ring
  · have b1 : SM 5 ((p:ℚ_[p])^4*A2 p) := (sm_ppow 4).mul (sm_A2_1 hp7)
    have b2 : SM 5 (2*(p:ℚ_[p])^4*E2s p) :=
      ((sm_ofNat 2).mul ((sm_ppow 4).mul (sm_E2s hp7))).of_eq (by ring)
    exact b1.add b2

private lemma sm_a3 (hp7 : 7 ≤ p) :
    SM 3 (6*(p:ℚ_[p])*hh p p - 6*(p:ℚ_[p])^2*qq p p) := by
  have u1 : SM 3 (6*(p:ℚ_[p])*hh p p) :=
    ((sm_ofNat 6).mul (sm_p.mul (sm_hh_p hp7))).of_eq (by ring)
  have u2 : SM 3 (6*(p:ℚ_[p])^2*qq p p) :=
    ((sm_ofNat 6).mul ((sm_ppow 2).mul (sm_qq_p hp7))).of_eq (by ring)
  exact u1.sub u2

private lemma sm_b3 (hp7 : 7 ≤ p) :
    SM 3 (6*(p:ℚ_[p])*hh p p + 10*(p:ℚ_[p])^3*T1 p) := by
  have u1 : SM 3 (6*(p:ℚ_[p])*hh p p) :=
    ((sm_ofNat 6).mul (sm_p.mul (sm_hh_p hp7))).of_eq (by ring)
  have u2 : SM 3 (10*(p:ℚ_[p])^3*T1 p) :=
    ((sm_ofNat 10).mul ((sm_ppow 3).mul sm_T1_0)).of_eq (by ring)
  exact u1.add u2

private lemma sm_Z (hp7 : 7 ≤ p) :
    SM 5 (4*(6*(p:ℚ_[p])*hh p p - 6*(p:ℚ_[p])^2*qq p p)
      + 3*(6*(p:ℚ_[p])*hh p p + 10*(p:ℚ_[p])^3*T1 p)) := by
  have hR2 := mc_def.mp (R2 hp7)
  have u1 : SM 5 (30*(p:ℚ_[p])*hh p p - 30*(p:ℚ_[p])^2*qq p p
      + 30*(p:ℚ_[p])^3*T1 p - 30*(p:ℚ_[p])^4*E2s p) :=
    ((sm_ofNat 30).mul (sm_p.mul hR2)).of_eq (by ring)
  have u2 : SM 5 (12*(p:ℚ_[p])*hh p p + 6*(p:ℚ_[p])^2*qq p p) :=
    ((sm_ofNat 6).mul (sm_p.mul (sm_pair_ref hp7))).of_eq (by ring)
  have u3 : SM 5 (30*(p:ℚ_[p])^4*E2s p) :=
    ((sm_ofNat 30).mul ((sm_ppow 4).mul (sm_E2s hp7))).of_eq (by ring)
  exact (((u1.add u2).add u3)).of_eq (by ring)

private lemma XY_bound {X Y a b : ℚ_[p]} (hA : MC 5 X (3+a)) (hS : MC 5 Y (3+b))
    (ha3 : SM 3 a) (hb3 : SM 3 b) (hX0 : SM 0 X) (hZ : SM 5 (4*a + 3*b)) :
    SM 5 (X^4 * Y^3 - 2187) := by
  have hY0 : SM 0 (3 + b) := (sm_ofNat 3).add (hb3.mono (by decide))
  have hA0 : SM 0 (3 + a) := (sm_ofNat 3).add (ha3.mono (by decide))
  have hY0' : SM 0 Y := by
    have := mc_def.mp (hS.mono (Nat.zero_le 5))
    exact (this.add hY0).of_eq (by ring)
  have hXY : MC 5 (X^4 * Y^3) ((3+a)^4 * (3+b)^3) :=
    (hA.pow hX0 hA0 4).mul (hS.pow hY0' hY0 3) (sm_pow0 hX0 4) (sm_pow0 hY0 3)
  have hVfin : SM 5 ((3+a)^4*(3+b)^3 - 2187) := by
    have h729 : SM 5 (729*(4*a+3*b)) := ((sm_ofNat 729).mul hZ).of_eq rfl
    exact ((sm_R ha3 hb3).add h729).of_eq (by ring)
  exact ((mc_def.mp hXY).add hVfin).of_eq (by ring)

/-- The main `p`-adic estimate. -/
lemma final_bound (hp7 : 7 ≤ p) :
    SM 5 (((A357674 p : ℕ) : ℚ_[p]) - ((A357674 1 : ℕ) : ℚ_[p])) := by
  have hp1 : 1 ≤ p := hp.out.pos
  have hAp : A357674 p = ((3*p).choose p)^4
      * (∑ k ∈ range (2*p+1), ((p + k - 1).choose k)^2)^3 := by
    show (∑ k ∈ range (2*p+1), (p + k - 1).choose k)^4
      * (∑ k ∈ range (2*p+1), ((p + k - 1).choose k)^2)^3 = _
    rw [hockey_stick (by omega : 1 ≤ p)]
  have hA1 : A357674 1 = 2187 := by decide
  have hcast : ((A357674 p : ℕ) : ℚ_[p]) = (((3*p).choose p : ℕ) : ℚ_[p])^4
      * (∑ k ∈ range (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)^3 := by
    rw [hAp]
    push_cast
    ring
  rw [hcast, hA1]
  have hA : MC 5 (((3*p).choose p : ℕ) : ℚ_[p])
      (3 + (6*(p:ℚ_[p])*hh p p - 6*(p:ℚ_[p])^2*qq p p)) :=
    (partA hp7).trans (MC.of_eq (by ring))
  have hS : MC 5 (∑ k ∈ range (2*p+1), (((p + k - 1).choose k : ℕ) : ℚ_[p])^2)
      (3 + (6*(p:ℚ_[p])*hh p p + 10*(p:ℚ_[p])^3*T1 p)) :=
    (partS2 hp7).trans (MC.of_eq (by ring))
  have hfin := XY_bound hA hS (sm_a3 hp7) (sm_b3 hp7) (sm_natCast _) (sm_Z hp7)
  exact hfin.of_eq (by push_cast; ring)

/-- The congruence for primes `p ≥ 7`. -/
lemma main_seven (hp7 : 7 ≤ p) : A357674 p ≡ A357674 1 [MOD p^5] := by
  have hb := final_bound (p := p) hp7
  have hnorm : ‖(((A357674 p : ℤ) - (A357674 1 : ℤ) : ℤ) : ℚ_[p])‖ ≤ (p:ℝ)^(-(5:ℕ):ℤ) := by
    have h2 : (((A357674 p : ℤ) - (A357674 1 : ℤ) : ℤ) : ℚ_[p])
        = ((A357674 p : ℕ) : ℚ_[p]) - ((A357674 1 : ℕ) : ℚ_[p]) := by push_cast; ring
    rw [h2]
    exact hb
  have hdvd : ((p:ℤ))^5 ∣ ((A357674 p : ℤ) - (A357674 1 : ℤ)) :=
    (Padic.norm_int_le_pow_iff_dvd _ 5).mp hnorm
  have hgoal : ((p^5 : ℕ) : ℤ) ∣ ((A357674 1 : ℤ) - (A357674 p : ℤ)) := by
    rw [dvd_sub_comm]
    exact_mod_cast hdvd
  exact (Nat.modEq_iff_dvd).mpr hgoal

/-- Conjecture 1. -/
theorem conjecture_main (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · subst h3
    decide
  by_cases h5 : p = 5
  · subst h5
    decide
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have h6 : p ≠ 6 := by rintro rfl; norm_num at hp
  exact main_seven (by omega)

end A357674


/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] :=
  A357674.conjecture_main p hp hp3
