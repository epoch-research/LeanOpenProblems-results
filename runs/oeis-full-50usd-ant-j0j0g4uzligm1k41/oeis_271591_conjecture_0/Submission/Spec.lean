import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000

/--
The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.
-/
def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

/--
A271591: Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.
-/
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  -- The index of the MSB is T.log2. The index of the second MSB is T.log2 - 1.
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

-- Definition for a maximal run of a value $v \in \{0, 1\}$ starting at index $n$ with length $L$.
-- We restrict $n \ge 2$ to account for "after the first two 0's" $a(0)=0, a(1)=0$.
def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  -- The run consists of L consecutive $v$'s starting at n
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  -- The run is not followed by $v$
  (a (n + L) ≠ v) ∧
  -- The run is not preceded by $v$
  (a (n - 1) ≠ v)

local notation "T" => tribonacci

theorem trib_rec (m : ℕ) : T (m+3) = T (m+2) + T (m+1) + T m := rfl

-- positivity and monotonicity
theorem trib_pos : ∀ n, 2 ≤ n → 1 ≤ T n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | (m+5), _ =>
      rw [show m+5 = (m+2)+3 from by ring, trib_rec]
      have := ih (m+2+2) (by omega) (by omega)
      omega

theorem trib_mono : ∀ n, T n ≤ T (n+1) := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | (m+2) =>
    rw [show m+2+1 = (m)+3 from by ring, trib_rec]
    have h1 : 1 ≤ T (m+1) ∨ m = 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · right; exact h
      · left; exact trib_pos (m+1) (by omega)
    rcases h1 with h | h
    · -- T(m+2) ≤ T(m+2)+T(m+1)+T m
      omega
    · subst h; decide

-- the ratio bounds for n ≥ 10
theorem Rbounds : ∀ n, 10 ≤ n → 1836 * T n ≤ 1000 * T (n+1) ∧ 1000 * T (n+1) ≤ 1842 * T n := by
  have key : ∀ n, (1836 * T (n+10) ≤ 1000 * T (n+11) ∧ 1000 * T (n+11) ≤ 1842 * T (n+10)) ∧
                  (1836 * T (n+11) ≤ 1000 * T (n+12) ∧ 1000 * T (n+12) ≤ 1842 * T (n+11)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_, ?_⟩
      · -- 1836 * T (k+12) ≤ 1000 * T (k+13)
        have hr : T (k+1+12) = T (k+12) + T (k+11) + T (k+10) := by
          rw [show k+1+12 = (k+10)+3 from by ring, trib_rec]
        rw [show k+1+11 = k+12 from by ring, show k+1+12 = k+13 from by ring] at *
        rw [hr]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      · have hr : T (k+1+12) = T (k+12) + T (k+11) + T (k+10) := by
          rw [show k+1+12 = (k+10)+3 from by ring, trib_rec]
        rw [show k+1+11 = k+12 from by ring, show k+1+12 = k+13 from by ring] at *
        rw [hr]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  exact (key k).1

theorem trib_le_of_le : ∀ a b : ℕ, a ≤ b → T a ≤ T b := by
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge a (k+1) with h | h
    · exact le_trans (ih (by omega)) (trib_mono k)
    · have : a = k+1 := by omega
      subst this; exact le_refl _

theorem trib_ge_two (n : ℕ) (h : 4 ≤ n) : 2 ≤ T n := by
  calc 2 = T 4 := by decide
    _ ≤ T n := trib_le_of_le 4 n h

/-- `m n` is `log2 (T n)`, the position of the most-significant bit. -/
def mm (n : ℕ) : ℕ := Nat.log2 (T n)

theorem mm_pow_le (n : ℕ) (h : 4 ≤ n) : 2 ^ (mm n) ≤ T n := by
  rw [mm, Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by have := trib_ge_two n h; omega)

theorem mm_lt_pow (n : ℕ) (h : 4 ≤ n) : T n < 2 ^ (mm n + 1) := by
  rw [mm, Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num) (T n)

theorem mm_ge_one (n : ℕ) (h : 4 ≤ n) : 1 ≤ mm n := by
  rw [mm, Nat.log2_eq_log_two, Nat.le_log_iff_pow_le (by norm_num)
    (by have := trib_ge_two n h; omega)]
  have := trib_ge_two n h; simpa using this

theorem bit_char (n : ℕ) (h : 4 ≤ n) :
    (T n).testBit (mm n - 1) = true ↔ 3 * 2 ^ (mm n) ≤ 2 * T n := by
  have hm := mm_ge_one n h
  have hle := mm_pow_le n h
  have hlt := mm_lt_pow n h
  have hdpos : 0 < 2 ^ (mm n - 1) := by positivity
  set d := 2 ^ (mm n - 1) with hd
  have e2 : 2 ^ (mm n) = 2 * d := by
    rw [hd]; conv_lhs => rw [show mm n = (mm n - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have e4 : 2 ^ (mm n + 1) = 4 * d := by
    rw [hd]; conv_lhs => rw [show mm n + 1 = (mm n - 1) + 2 from by omega]
    rw [pow_add]; ring
  have h2 : 2 * d ≤ T n := by rw [← e2]; exact hle
  have h4 : T n < 4 * d := by rw [← e4]; exact hlt
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  have hq2 : 2 ≤ T n / d := (Nat.le_div_iff_mul_le hdpos).2 (by omega)
  have hq4 : T n / d < 4 := (Nat.div_lt_iff_lt_mul hdpos).2 (by omega)
  have hkey3 : (3 ≤ T n / d) ↔ (3 * 2 ^ (mm n) ≤ 2 * T n) := by
    rw [Nat.le_div_iff_mul_le hdpos, e2]; omega
  rw [← hkey3]
  obtain ⟨q, hqdef⟩ : ∃ q, T n / d = q := ⟨_, rfl⟩
  rw [hqdef] at hq2 hq4 ⊢
  omega

theorem a_eq_one_iff (n : ℕ) (h : 4 ≤ n) : a n = 1 ↔ 3 * 2 ^ (mm n) ≤ 2 * T n := by
  have hT2 : 2 ≤ T n := trib_ge_two n h
  have hnle : ¬ (T n ≤ 1) := by omega
  rw [← bit_char n h]
  unfold a
  rw [dif_neg hnle]
  simp only [mm, Nat.log2_eq_log_two] at *
  by_cases hb : (T n).testBit (Nat.log 2 (T n) - 1) = true
  · rw [hb]; simp
  · simp only [Bool.not_eq_true] at hb; rw [hb]; simp

theorem a_le_one (n : ℕ) : a n ≤ 1 := by
  unfold a
  by_cases h : T n ≤ 1
  · rw [dif_pos h]; omega
  · rw [dif_neg h]; dsimp only; split <;> omega

/-- The mantissa `T n / 2 ^ (mm n) ∈ [1, 2)`. -/
noncomputable def uu (n : ℕ) : ℝ := (T n : ℝ) / 2 ^ (mm n)

theorem pow_pos_real (k : ℕ) : (0:ℝ) < 2 ^ k := by positivity

theorem u_ge_one (n : ℕ) (h : 4 ≤ n) : 1 ≤ uu n := by
  rw [uu, le_div_iff₀ (pow_pos_real _), one_mul]
  have := mm_pow_le n h
  exact_mod_cast this

theorem u_lt_two (n : ℕ) (h : 4 ≤ n) : uu n < 2 := by
  rw [uu, div_lt_iff₀ (pow_pos_real _)]
  have := mm_lt_pow n h
  have : (T n : ℝ) < 2 ^ (mm n + 1) := by exact_mod_cast this
  rw [pow_succ] at this; linarith

theorem a1_iff_u (n : ℕ) (h : 4 ≤ n) : a n = 1 ↔ 3/2 ≤ uu n := by
  rw [a_eq_one_iff n h, uu, le_div_iff₀ (pow_pos_real _)]
  constructor
  · intro hh
    have : (3 * 2 ^ (mm n) : ℝ) ≤ 2 * T n := by exact_mod_cast hh
    linarith
  · intro hh
    have : (3 / 2 * 2 ^ (mm n) : ℝ) ≤ T n := hh
    have h2 : (3 * 2 ^ (mm n) : ℝ) ≤ 2 * T n := by linarith
    exact_mod_cast h2

theorem a0_iff_u (n : ℕ) (h : 4 ≤ n) : a n = 0 ↔ uu n < 3/2 := by
  have hle := a_le_one n
  have := a1_iff_u n h
  constructor
  · intro h0
    by_contra hc
    push_neg at hc
    have : a n = 1 := (a1_iff_u n h).2 hc
    omega
  · intro hu
    rcases Nat.lt_or_ge (a n) 1 with h1 | h1
    · omega
    · have : a n = 1 := by omega
      rw [a1_iff_u n h] at this; linarith

theorem mm_step (n : ℕ) (h : 10 ≤ n) : mm (n+1) = mm n ∨ mm (n+1) = mm n + 1 := by
  have h4 : 4 ≤ n := by omega
  have hge : mm n ≤ mm (n+1) := by
    rw [mm, mm, Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (trib_mono n)
  have hTn := trib_ge_two n h4
  have hr := (Rbounds n h).2
  have hlt := mm_lt_pow n h4
  have hub : T (n+1) < 2 ^ (mm n + 2) := by
    have hd : T (n+1) < 2 * T n := by omega
    have h2 : 2 * T n < 2 * 2 ^ (mm n + 1) := by omega
    have h3 : 2 * 2 ^ (mm n + 1) = 2 ^ (mm n + 2) := by rw [pow_succ]; ring
    omega
  have hle : mm (n+1) ≤ mm n + 1 := by
    rw [mm, Nat.log2_eq_log_two]
    have : Nat.log 2 (T (n+1)) < mm n + 2 :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (by have := trib_ge_two (n+1) (by omega); omega)).2 hub
    omega
  omega

/-- `ww n = T (n+1) / 2 ^ (mm n) = R n * uu n`. -/
noncomputable def ww (n : ℕ) : ℝ := (T (n+1) : ℝ) / 2 ^ (mm n)

theorem ww_lb (n : ℕ) (h : 10 ≤ n) : 1836/1000 * uu n ≤ ww n := by
  have hP : (0:ℝ) < 2 ^ (mm n) := pow_pos_real _
  have key : (1836:ℝ) * T n ≤ 1000 * T (n+1) := by exact_mod_cast (Rbounds n h).1
  rw [uu, ww, ← mul_div_assoc, div_le_div_iff_of_pos_right hP]
  linarith

theorem ww_ub (n : ℕ) (h : 10 ≤ n) : ww n ≤ 1842/1000 * uu n := by
  have hP : (0:ℝ) < 2 ^ (mm n) := pow_pos_real _
  have key : (1000:ℝ) * T (n+1) ≤ 1842 * T n := by exact_mod_cast (Rbounds n h).2
  rw [uu, ww, ← mul_div_assoc, div_le_div_iff_of_pos_right hP]
  linarith

theorem uu_succ_eq (n : ℕ) (h : 10 ≤ n) : uu (n+1) = ww n ∨ uu (n+1) = ww n / 2 := by
  rcases mm_step n h with hs | hs
  · left; rw [uu, ww, hs]
  · right
    rw [uu, ww, hs, pow_succ, div_div]

/-- If the mantissa is large enough (`≥ 1.09`) the next step is a halving (decrease). -/
theorem big_dec (n : ℕ) (h : 10 ≤ n) (hb : 1090/1000 ≤ uu n) :
    918/1000 * uu n ≤ uu (n+1) ∧ uu (n+1) ≤ 921/1000 * uu n := by
  rcases uu_succ_eq n h with he | he
  · exfalso
    have hl := ww_lb n h
    have h2 := u_lt_two (n+1) (by omega)
    rw [he] at h2
    nlinarith [hl, hb, h2]
  · rw [he]
    refine ⟨?_, ?_⟩
    · have := ww_lb n h; linarith
    · have := ww_ub n h; linarith

/-- Inside a run of zeros (the next value is also `< 3/2`), the step is a halving. -/
theorem zero_dec (n : ℕ) (h : 10 ≤ n) (hz1 : uu (n+1) < 3/2) :
    uu (n+1) ≤ 921/1000 * uu n := by
  rcases uu_succ_eq n h with he | he
  · exfalso
    have hl := ww_lb n h
    have h1 := u_ge_one n (by omega)
    rw [he] at hz1
    nlinarith [hl, h1, hz1]
  · rw [he]; have := ww_ub n h; linarith

/-- Entering a one-run from a zero forces a jump (no halving). -/
theorem is_jump (n : ℕ) (h : 10 ≤ n) (hz : uu n < 3/2) (ho1 : 3/2 ≤ uu (n+1)) :
    uu (n+1) = ww n := by
  rcases uu_succ_eq n h with he | he
  · exact he
  · exfalso
    have hub := ww_ub n h
    rw [he] at ho1
    nlinarith [hub, hz, ho1]

-- No five consecutive ones.
theorem U_O5 (n : ℕ) (h : 10 ≤ n) :
    ¬ (3/2 ≤ uu n ∧ 3/2 ≤ uu (n+1) ∧ 3/2 ≤ uu (n+2) ∧ 3/2 ≤ uu (n+3) ∧ 3/2 ≤ uu (n+4)) := by
  rintro ⟨o0, o1, o2, o3, o4⟩
  have b0 := (big_dec n h (by linarith)).2
  have b1 := (big_dec (n+1) (by omega) (by linarith)).2
  have b2 := (big_dec (n+2) (by omega) (by linarith)).2
  have b3 := (big_dec (n+3) (by omega) (by linarith)).2
  have hu0 : uu n < 2 := u_lt_two n (by omega)
  have h1 : uu (n+1) < 1843/1000 := by linarith
  have h2 : uu (n+2) < 1698/1000 := by linarith
  have h3 : uu (n+3) < 1565/1000 := by linarith
  have h4 : uu (n+4) < 1442/1000 := by linarith
  linarith

-- One-runs have length ≥ 3 : entering at `m+1` forces ones at `m+2, m+3`.
theorem U_O12 (m : ℕ) (h : 10 ≤ m) (hz : uu m < 3/2) (ho : 3/2 ≤ uu (m+1)) :
    3/2 ≤ uu (m+2) ∧ 3/2 ≤ uu (m+3) := by
  have hj := is_jump m h hz ho
  have hentry : 1836/1000 ≤ uu (m+1) := by
    have hl := ww_lb m h
    have h1 := u_ge_one m (by omega)
    rw [← hj] at hl
    linarith
  have l2 := (big_dec (m+1) (by omega) (by linarith)).1
  have hlb2 : 1685/1000 ≤ uu (m+2) := by linarith
  have l3 := (big_dec (m+2) (by omega) (by linarith)).1
  have hlb3 : 1546/1000 ≤ uu (m+3) := by linarith
  exact ⟨by linarith, by linarith⟩

-- No six consecutive zeros.
theorem U_Z6 (n : ℕ) (h : 10 ≤ n) :
    ¬ (uu n < 3/2 ∧ uu (n+1) < 3/2 ∧ uu (n+2) < 3/2 ∧ uu (n+3) < 3/2 ∧
       uu (n+4) < 3/2 ∧ uu (n+5) < 3/2) := by
  rintro ⟨z0, z1, z2, z3, z4, z5⟩
  have b0 := zero_dec n h z1
  have b1 := zero_dec (n+1) (by omega) z2
  have b2 := zero_dec (n+2) (by omega) z3
  have b3 := zero_dec (n+3) (by omega) z4
  have b4 := zero_dec (n+4) (by omega) z5
  have h1 : uu (n+1) < 1382/1000 := by linarith
  have h2 : uu (n+2) < 1273/1000 := by linarith
  have h3 : uu (n+3) < 1173/1000 := by linarith
  have h4 : uu (n+4) < 1081/1000 := by linarith
  have h5 : uu (n+5) < 996/1000 := by linarith
  have h5lb : 1 ≤ uu (n+5) := u_ge_one (n+5) (by omega)
  linarith

-- Zero-runs have length ≥ 4 : entering at `m+1` forces zeros at `m+2, m+3, m+4`.
theorem U_Z123 (m : ℕ) (h : 10 ≤ m) (ho : 3/2 ≤ uu m) (hz : uu (m+1) < 3/2) :
    uu (m+2) < 3/2 ∧ uu (m+3) < 3/2 ∧ uu (m+4) < 3/2 := by
  -- entry value: uu (m+1) = ww m / 2 ≥ 0.918 * 1.5 = 1.377
  have hentry : 1377/1000 ≤ uu (m+1) := by
    have d := (big_dec m h (by linarith)).1
    linarith
  have d2 := big_dec (m+1) (by omega) (by linarith)
  have hub2 : uu (m+2) < 3/2 := by have := d2.2; linarith
  have hlb2 : 1264/1000 ≤ uu (m+2) := by have := d2.1; linarith
  have d3 := big_dec (m+2) (by omega) (by linarith)
  have hub3 : uu (m+3) < 3/2 := by have := d3.2; linarith
  have hlb3 : 1160/1000 ≤ uu (m+3) := by have := d3.1; linarith
  have d4 := big_dec (m+3) (by omega) (by linarith)
  have hub4 : uu (m+4) < 3/2 := by have := d4.2; linarith
  exact ⟨hub2, hub3, hub4⟩

theorem a_zo (k : ℕ) : a k = 0 ∨ a k = 1 := by
  have := a_le_one k; omega

-- a-level pattern lemmas, valid for all n ≥ 2.

theorem L_O5 : ∀ n, 2 ≤ n →
    ¬ (a n = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 1 ∧ a (n+3) = 1 ∧ a (n+4) = 1) := by
  intro n hn
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> decide
  · rintro ⟨e0, e1, e2, e3, e4⟩
    exact U_O5 n hge ⟨(a1_iff_u n (by omega)).1 e0, (a1_iff_u (n+1) (by omega)).1 e1,
      (a1_iff_u (n+2) (by omega)).1 e2, (a1_iff_u (n+3) (by omega)).1 e3,
      (a1_iff_u (n+4) (by omega)).1 e4⟩

theorem L_Z6 : ∀ n, 2 ≤ n →
    ¬ (a n = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 ∧ a (n+4) = 0 ∧ a (n+5) = 0) := by
  intro n hn
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> decide
  · rintro ⟨e0, e1, e2, e3, e4, e5⟩
    exact U_Z6 n hge ⟨(a0_iff_u n (by omega)).1 e0, (a0_iff_u (n+1) (by omega)).1 e1,
      (a0_iff_u (n+2) (by omega)).1 e2, (a0_iff_u (n+3) (by omega)).1 e3,
      (a0_iff_u (n+4) (by omega)).1 e4, (a0_iff_u (n+5) (by omega)).1 e5⟩

theorem L_O12 : ∀ n, 2 ≤ n → a (n-1) = 0 → a n = 1 → a (n+1) = 1 ∧ a (n+2) = 1 := by
  intro n hn hprev hcur
  rcases Nat.lt_or_ge n 11 with hlt | hge
  · interval_cases n <;> revert hprev hcur <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hprev
    have hzm : uu m < 3/2 := (a0_iff_u m (by omega)).1 hprev
    have hom : 3/2 ≤ uu (m+1) := (a1_iff_u (m+1) (by omega)).1 hcur
    obtain ⟨c2, c3⟩ := U_O12 m (by omega) hzm hom
    exact ⟨(a1_iff_u (m+2) (by omega)).2 c2, (a1_iff_u (m+3) (by omega)).2 c3⟩

theorem L_Z123 : ∀ n, 2 ≤ n → a (n-1) = 1 → a n = 0 →
    a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 := by
  intro n hn hprev hcur
  rcases Nat.lt_or_ge n 11 with hlt | hge
  · interval_cases n <;> revert hprev hcur <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hprev
    have hom : 3/2 ≤ uu m := (a1_iff_u m (by omega)).1 hprev
    have hzm : uu (m+1) < 3/2 := (a0_iff_u (m+1) (by omega)).1 hcur
    obtain ⟨c1, c2, c3⟩ := U_Z123 m (by omega) hom hzm
    exact ⟨(a0_iff_u (m+2) (by omega)).2 c1, (a0_iff_u (m+3) (by omega)).2 c2,
      (a0_iff_u (m+4) (by omega)).2 c3⟩

/--
It is conjectured that after the first two 0's, the number of consecutive 0's is only 4 or 5,
and the number of consecutive 1's is only 3 or 4 (tested up to n=10^4).
-/
theorem oeis_271591_conjecture_0 :
  (∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧
  (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4)) :=
by
  constructor
  · intro n L hrun
    obtain ⟨hn, hL, hru, hafter, hbefore⟩ := hrun
    have hprev : a (n-1) = 1 := by have := a_zo (n-1); omega
    have ha0 : a n = 0 := by simpa using hru 0 (by omega)
    obtain ⟨c1, c2, c3⟩ := L_Z123 n hn hprev ha0
    have hLle : L ≤ 5 := by
      by_contra hc
      push_neg at hc
      exact L_Z6 n hn ⟨ha0, c1, c2, c3, hru 4 (by omega), hru 5 (by omega)⟩
    have hLge : 4 ≤ L := by
      rcases Nat.lt_or_ge L 4 with h4 | h4
      · exfalso; interval_cases L
        · exact hafter c1
        · exact hafter c2
        · exact hafter c3
      · exact h4
    omega
  · intro n L hrun
    obtain ⟨hn, hL, hru, hafter, hbefore⟩ := hrun
    have hprev : a (n-1) = 0 := by have := a_zo (n-1); omega
    have ha1 : a n = 1 := by simpa using hru 0 (by omega)
    obtain ⟨c1, c2⟩ := L_O12 n hn hprev ha1
    have hLle : L ≤ 4 := by
      by_contra hc
      push_neg at hc
      exact L_O5 n hn ⟨ha1, c1, c2, hru 3 (by omega), hru 4 (by omega)⟩
    have hLge : 3 ≤ L := by
      rcases Nat.lt_or_ge L 3 with h3 | h3
      · exfalso; interval_cases L
        · exact hafter c1
        · exact hafter c2
      · exact h3
    omega



