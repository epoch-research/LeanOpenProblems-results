import FormalConjectures.Util.ProblemImports

/--
A120424: Having specified two initial terms, the "Half-Fibonacci" sequence proceeds like the
Fibonacci sequence, except that the terms are halved before being added if they are even.
$$a(n) = (\text{if } a(n-1) \text{ is odd then } a(n-1) \text{ else } a(n-1)/2) + (\text{if } a(n-2) \text{ is odd then } a(n-2) \text{ else } a(n-2)/2)$$
with $a(0)=1$ and $a(1)=3$.
-/
def A120424 : ℕ → ℕ
| 0     => 1
| 1     => 3
| n + 2 =>
  let f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x
  f (A120424 (n + 1)) + f (A120424 n)
namespace HalfFib

/-- The "halving" function. -/
def hf (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x

/-- The Half-Fibonacci sequence (same as `A120424`). -/
def a : ℕ → ℕ
| 0     => 1
| 1     => 3
| n + 2 => hf (a (n + 1)) + hf (a n)

@[simp] lemma a_zero : a 0 = 1 := rfl
@[simp] lemma a_one : a 1 = 3 := rfl
lemma a_succ_succ (n : ℕ) : a (n + 2) = hf (a (n + 1)) + hf (a n) := rfl

/-- `g n = hf (a n)`. -/
def g (n : ℕ) : ℕ := hf (a n)

lemma a_succ_succ' (n : ℕ) : a (n + 2) = g (n + 1) + g n := rfl

-- basic facts about hf
lemma hf_le (x : ℕ) : hf x ≤ x := by
  unfold hf; split <;> omega

lemma two_mul_hf_ge (x : ℕ) : x ≤ 2 * hf x := by
  unfold hf; split <;> omega

lemma hf_odd {x : ℕ} (h : x % 2 = 1) : hf x = x := by unfold hf; simp [h]

lemma hf_even {x : ℕ} (h : x % 2 = 0) : hf x = x / 2 := by unfold hf; simp [h]

lemma hf_pos {x : ℕ} (h : 1 ≤ x) : 1 ≤ hf x := by
  unfold hf; split <;> omega

@[simp] lemma g_zero : g 0 = 1 := rfl
@[simp] lemma g_one : g 1 = 3 := rfl

/-- `a n ≥ 1`. -/
lemma a_pos (n : ℕ) : 1 ≤ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
      rw [a_succ_succ]
      have : 1 ≤ hf (a m) := hf_pos (ih m (by omega))
      omega

lemma g_pos (n : ℕ) : 1 ≤ g n := hf_pos (a_pos n)

/-- The recurrence for `g`: `g (n+2) = hf (g (n+1) + g n)`. -/
lemma g_succ_succ (n : ℕ) : g (n + 2) = hf (g (n + 1) + g n) := by
  unfold g
  rw [a_succ_succ]

lemma hf_eq_one {x : ℕ} (h : hf x = 1) : x ≤ 2 := by
  unfold hf at h; split at h <;> omega

/-- `a n ≤ 2 * a (n+1)`. -/
lemma a_le_two_mul_succ (n : ℕ) : a n ≤ 2 * a (n + 1) := by
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [a_succ_succ]
    have h1 : a (m + 1) ≤ 2 * hf (a (m + 1)) := two_mul_hf_ge _
    omega

/-- `a (n+1) ≤ 3 * a n`. -/
lemma a_succ_le_three_mul (n : ℕ) : a (n + 1) ≤ 3 * a n := by
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [a_succ_succ]
    have h1 : hf (a (m + 1)) ≤ a (m + 1) := hf_le _
    have h2 : hf (a m) ≤ a m := hf_le _
    have h3 : a m ≤ 2 * a (m + 1) := a_le_two_mul_succ m
    omega

/-- The integer-valued first difference of `g`. -/
def e (k : ℕ) : ℤ := (g (k + 1) : ℤ) - (g k : ℤ)

/-- Parity of `e k` matches parity of `g(k+1)+g k`. -/
lemma e_even_iff (k : ℕ) : Even (e k) ↔ (g (k + 1) + g k) % 2 = 0 := by
  rw [e, Int.even_sub, Int.even_coe_nat, Int.even_coe_nat, ← Nat.even_add, Nat.even_iff]

/-- Forward step, even case: if `e k` is even then `2 * e (k+1) = - e k`. -/
lemma e_even_step {k : ℕ} (h : Even (e k)) : 2 * e (k + 1) = - e k := by
  have hpar : (g (k + 1) + g k) % 2 = 0 := (e_even_iff k).mp h
  have hsum : 2 * g (k + 2) = g (k + 1) + g k := by
    rw [g_succ_succ, hf_even hpar]; omega
  simp only [e]
  have hc : (2 * g (k + 2) : ℤ) = (g (k + 1) : ℤ) + g k := by exact_mod_cast hsum
  push_cast at hc ⊢; linarith

/-- Forward step, odd case: if `e k` is odd then `e (k+1) = g k`. -/
lemma e_odd_step {k : ℕ} (h : ¬ Even (e k)) : e (k + 1) = (g k : ℤ) := by
  have hpar : (g (k + 1) + g k) % 2 = 1 := by
    have := (e_even_iff k).not.mp h; omega
  have hsum : g (k + 2) = g (k + 1) + g k := by
    rw [g_succ_succ, hf_odd hpar]
  simp only [e]; rw [hsum]; push_cast; ring

/-- `a (k+2)` is even iff `e k` is even. -/
lemma a_even_iff_e_even (k : ℕ) : a (k + 2) % 2 = 0 ↔ Even (e k) := by
  rw [a_succ_succ', e_even_iff]

/-- Backward doubling step. -/
lemma e_back {k : ℕ} (h : a k > 2 * (e (k + 1)).natAbs) : e k = -2 * e (k + 1) := by
  by_cases he : Even (e k)
  · have := e_even_step he; linarith
  · exfalso
    have hodd := e_odd_step he
    have hg : (e (k + 1)).natAbs = g k := by rw [hodd]; simp
    rw [hg] at h
    have hle : a k ≤ 2 * g k := by
      have := two_mul_hf_ge (a k); simpa [g] using this
    omega

/-- The first difference of `a`, expressed via `e`. -/
lemma a_diff (m : ℕ) : (a (m + 3) : ℤ) - a (m + 2) = e (m + 1) + e m := by
  have h1 : a (m + 3) = g (m + 2) + g (m + 1) := a_succ_succ' (m + 1)
  have h2 : a (m + 2) = g (m + 1) + g m := a_succ_succ' m
  simp only [e]; rw [h1, h2]; push_cast; ring

/-- Base of the backward chain: a difference-1 event at `m+2` (with `a (m+1) > 2`)
forces `|e m| = 2`. -/
lemma base_case {m : ℕ} (hd : (e (m + 1) + e m).natAbs = 1) (hbig : a (m + 1) > 2) :
    (e m).natAbs = 2 := by
  by_cases he : Even (e m)
  · have hs := e_even_step he
    have hrw : e (m + 1) + e m = - e (m + 1) := by linarith
    have h1 : (e (m + 1)).natAbs = 1 := by rw [hrw] at hd; simpa using hd
    have h2 : e m = -2 * e (m + 1) := by linarith
    rw [h2, Int.natAbs_mul]; simp [h1]
  · exfalso
    have hodd := e_odd_step he
    have hsum : e (m + 1) + e m = (g (m + 1) : ℤ) := by
      rw [hodd]; simp only [e]; ring
    rw [hsum] at hd
    have hg1 : g (m + 1) = 1 := by simpa using hd
    have := hf_eq_one (x := a (m + 1)) (by simpa [g] using hg1)
    omega

/-- The backward doubling chain. Starting from a base `|e (b+i)| = 2` and provided the terms
`a (b + (i-j))` are large enough, every step down doubles `|e|`, giving `|e b| = 2^(i+1)`. -/
lemma chain : ∀ (i b : ℕ),
    (e (b + i)).natAbs = 2 →
    (∀ j, 1 ≤ j → j ≤ i → a (b + (i - j)) > 2 ^ (j + 1)) →
    (e b).natAbs = 2 ^ (i + 1) := by
  intro i
  induction i with
  | zero => intro b hbase _; simpa using hbase
  | succ i ih =>
    intro b hbase hcond
    have hb1 : (e (b + 1)).natAbs = 2 ^ (i + 1) := by
      apply ih (b + 1)
      · have h : b + 1 + i = b + (i + 1) := by omega
        rw [h]; exact hbase
      · intro j hj1 hji
        have heq : b + 1 + (i - j) = b + ((i + 1) - j) := by omega
        rw [heq]; exact hcond j hj1 (by omega)
    have hp : (2 : ℕ) ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [pow_succ]; ring
    have hak : a b > 2 * (e (b + 1)).natAbs := by
      have h0 := hcond (i + 1) (by omega) (by omega)
      simp only [Nat.sub_self, Nat.add_zero] at h0
      rw [hb1]; omega
    have hbk := e_back hak
    rw [hbk, Int.natAbs_mul, hb1]
    have h2 : (-2 : ℤ).natAbs = 2 := rfl
    rw [h2, pow_succ]; ring

/-! ### Growth monovariant -/

/-- The monovariant `P k = a k + 2 a (k+1)`. -/
def Pmon (k : ℕ) : ℕ := a k + 2 * a (k + 1)

/-- Count of "non-even-even" steps among `0,…,k-1`. -/
def Ncount : ℕ → ℕ
  | 0 => 0
  | (k + 1) => Ncount k + (if a k % 2 = 0 ∧ a (k + 1) % 2 = 0 then 0 else 1)

lemma Ncount_succ (k : ℕ) :
    Ncount (k + 1) = Ncount k + (if a k % 2 = 0 ∧ a (k + 1) % 2 = 0 then 0 else 1) := rfl

/-- `Pmon` is non-decreasing. -/
lemma Pmon_mono (k : ℕ) : Pmon k ≤ Pmon (k + 1) := by
  have hrec : a (k + 1 + 1) = hf (a (k + 1)) + hf (a k) := a_succ_succ k
  unfold Pmon
  rw [hrec]
  have h1 := two_mul_hf_ge (a (k + 1))
  have h2 := two_mul_hf_ge (a k)
  omega

/-- At a non-even-even step, `Pmon` grows by at least the factor `15/14`. -/
lemma Pmon_grow {k : ℕ} (h : ¬ (a k % 2 = 0 ∧ a (k + 1) % 2 = 0)) :
    15 * Pmon k ≤ 14 * Pmon (k + 1) := by
  have hrec : a (k + 1 + 1) = hf (a (k + 1)) + hf (a k) := a_succ_succ k
  have e1 := a_le_two_mul_succ k
  have e2 := a_succ_le_three_mul k
  have l1 := hf_le (a (k + 1))
  have l2 := hf_le (a k)
  have b1 := two_mul_hf_ge (a (k + 1))
  have b2 := two_mul_hf_ge (a k)
  unfold Pmon
  rw [hrec]
  rcases Nat.even_or_odd (a (k + 1)) with hp1 | hp1
  · rcases Nat.even_or_odd (a k) with hp2 | hp2
    · exact absurd ⟨Nat.even_iff.mp hp2, Nat.even_iff.mp hp1⟩ h
    · have hk : hf (a k) = a k := hf_odd (Nat.odd_iff.mp hp2)
      omega
  · have hk1 : hf (a (k + 1)) = a (k + 1) := hf_odd (Nat.odd_iff.mp hp1)
    omega

/-- The cleared-denominator growth invariant. -/
lemma growth_inv (k : ℕ) : 15 ^ (Ncount k) * 7 ≤ 14 ^ (Ncount k) * Pmon k := by
  induction k with
  | zero => norm_num [Ncount, Pmon]
  | succ k ih =>
    by_cases hEE : a k % 2 = 0 ∧ a (k + 1) % 2 = 0
    · have hNc : Ncount (k + 1) = Ncount k := by rw [Ncount_succ, if_pos hEE, add_zero]
      rw [hNc]
      calc 15 ^ (Ncount k) * 7 ≤ 14 ^ (Ncount k) * Pmon k := ih
        _ ≤ 14 ^ (Ncount k) * Pmon (k + 1) := by gcongr; exact Pmon_mono k
    · have hNc : Ncount (k + 1) = Ncount k + 1 := by rw [Ncount_succ, if_neg hEE]
      rw [hNc]
      have hgrow := Pmon_grow hEE
      calc 15 ^ (Ncount k + 1) * 7 = 15 * (15 ^ (Ncount k) * 7) := by rw [pow_succ]; ring
        _ ≤ 15 * (14 ^ (Ncount k) * Pmon k) := by gcongr
        _ = 14 ^ (Ncount k) * (15 * Pmon k) := by ring
        _ ≤ 14 ^ (Ncount k) * (14 * Pmon (k + 1)) := by gcongr
        _ = 14 ^ (Ncount k + 1) * Pmon (k + 1) := by rw [pow_succ]; ring

/-- A purely arithmetic inequality: `2^m · 14^N ≤ 15^N` whenever `14 m ≤ N`. -/
lemma pow_ineq {m N : ℕ} (h : 14 * m ≤ N) : 2 ^ m * 14 ^ N ≤ 15 ^ N := by
  obtain ⟨r, hr⟩ := Nat.le.dest h
  have h1 : (2 : ℕ) ^ m * 14 ^ (14 * m) ≤ 15 ^ (14 * m) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) m
  have h2 : (14 : ℕ) ^ r ≤ 15 ^ r := Nat.pow_le_pow_left (by norm_num) r
  calc 2 ^ m * 14 ^ N = (2 ^ m * 14 ^ (14 * m)) * 14 ^ r := by rw [← hr, pow_add]; ring
    _ ≤ 15 ^ (14 * m) * 15 ^ r := Nat.mul_le_mul h1 h2
    _ = 15 ^ N := by rw [← hr, pow_add]

/-- Growth lemma: if there are at least `14 m` non-even-even steps before `k`, then `a k ≥ 2^m`. -/
lemma a_ge_pow {k m : ℕ} (h : 14 * m ≤ Ncount k) : 2 ^ m ≤ a k := by
  have hinv := growth_inv k
  have hP : Pmon k ≤ 7 * a k := by
    unfold Pmon; have := a_succ_le_three_mul k; omega
  set N := Ncount k with hNdef
  have step1 : 15 ^ N * 7 ≤ 7 * (14 ^ N * a k) := by
    calc 15 ^ N * 7 ≤ 14 ^ N * Pmon k := hinv
      _ ≤ 14 ^ N * (7 * a k) := by gcongr
      _ = 7 * (14 ^ N * a k) := by ring
  have step2 : 15 ^ N ≤ 14 ^ N * a k := by omega
  have hpi := pow_ineq (m := m) (N := N) h
  have hcomb : 2 ^ m * 14 ^ N ≤ a k * 14 ^ N := by
    calc 2 ^ m * 14 ^ N ≤ 15 ^ N := hpi
      _ ≤ 14 ^ N * a k := step2
      _ = a k * 14 ^ N := by ring
  have h14 : 0 < 14 ^ N := by positivity
  exact Nat.le_of_mul_le_mul_right hcomb h14

/-! ### Even counting -/

/-- Number of even terms among `a 0, …, a (b-1)`. -/
def Ecount (b : ℕ) : ℕ := ((Finset.range b).filter (fun j => a j % 2 = 0)).card

lemma Ecount_succ (b : ℕ) :
    Ecount (b + 1) = Ecount b + (if a b % 2 = 0 then 1 else 0) := by
  unfold Ecount
  rw [Finset.range_succ, Finset.filter_insert]
  by_cases h : a b % 2 = 0
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, add_zero]

/-- Every index is either counted by `Ncount` or `Ecount`. -/
lemma Ncount_ge (k : ℕ) : k ≤ Ncount k + Ecount k := by
  induction k with
  | zero => simp [Ncount, Ecount]
  | succ k ih =>
    rw [Ncount_succ, Ecount_succ]
    by_cases hk : a k % 2 = 0
    · rw [if_pos hk]; split_ifs <;> omega
    · have hne : ¬ (a k % 2 = 0 ∧ a (k + 1) % 2 = 0) := by tauto
      rw [if_neg hk, if_neg hne]; omega

/- ### Density conversions -/

open Filter Topology

lemma ncard_Iio (b : ℕ) : (Set.Iio b).ncard = b := by
  rw [← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio]

lemma ncard_even_Iio (b : ℕ) :
    ({n : ℕ | a n % 2 = 0} ∩ Set.Iio b).ncard = Ecount b := by
  have hset : {n : ℕ | a n % 2 = 0} ∩ Set.Iio b
      = ↑((Finset.range b).filter (fun j => a j % 2 = 0)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio, Finset.coe_filter,
      Finset.mem_range]
    tauto
  rw [hset, Set.ncard_coe_finset]
  rfl

lemma density_eq (b : ℕ) :
    Set.partialDensity {n : ℕ | a n % 2 = 0} Set.univ b = (Ecount b : ℝ) / b := by
  unfold Set.partialDensity
  rw [Set.inter_univ, Set.univ_inter, ncard_even_Iio, ncard_Iio]

lemma hasDensity_tendsto (hP : ({n : ℕ | a n % 2 = 0}).HasDensity (1 / 2 : ℝ)) :
    Tendsto (fun b : ℕ => (Ecount b : ℝ) / b) atTop (𝓝 (1 / 2)) := by
  have h := hP
  unfold Set.HasDensity at h
  exact Filter.Tendsto.congr (fun b => density_eq b) h

/-- Upper density bound `Ecount b ≤ 101 b / 200` eventually. -/
lemma upper_bound (hP : ({n : ℕ | a n % 2 = 0}).HasDensity (1 / 2 : ℝ)) :
    ∃ K, ∀ b, K ≤ b → 200 * Ecount b ≤ 101 * b := by
  have hd := hasDensity_tendsto hP
  have hev : ∀ᶠ b : ℕ in atTop, (Ecount b : ℝ) / b < (101 : ℝ) / 200 :=
    hd.eventually_lt_const (by norm_num)
  rw [eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  refine ⟨max K 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbK : K ≤ b := le_trans (le_max_left _ _) hb
  have hlt := hK b hbK
  rw [div_lt_iff₀ (by exact_mod_cast (by omega : 0 < b))] at hlt
  have hr : (200 : ℝ) * Ecount b < 101 * b := by linarith
  have hnat : 200 * Ecount b < 101 * b := by exact_mod_cast hr
  omega

/-- Lower density bound `Ecount b ≥ 99 b / 200` eventually. -/
lemma lower_bound (hP : ({n : ℕ | a n % 2 = 0}).HasDensity (1 / 2 : ℝ)) :
    ∃ K, ∀ b, K ≤ b → 99 * b ≤ 200 * Ecount b := by
  have hd := hasDensity_tendsto hP
  have hev : ∀ᶠ b : ℕ in atTop, (99 : ℝ) / 200 < (Ecount b : ℝ) / b :=
    hd.eventually_const_lt (by norm_num)
  rw [eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  refine ⟨max K 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbK : K ≤ b := le_trans (le_max_left _ _) hb
  have hlt := hK b hbK
  rw [lt_div_iff₀ (by exact_mod_cast (by omega : 0 < b))] at hlt
  have hr : (99 : ℝ) * b < 200 * Ecount b := by linarith
  have hnat : 99 * b < 200 * Ecount b := by exact_mod_cast hr
  omega

/- ### Assembly -/

/-- Growth condition feeding the chain: large terms below the event index. -/
lemma cond_growth {K2 : ℕ} (hU : ∀ b, K2 ≤ b → 200 * Ecount b ≤ 101 * b)
    {n j : ℕ} (hj : 36 * j + 72 ≤ n) (hk : K2 ≤ n - 2 - j) :
    2 ^ (j + 1) < a (n - 2 - j) := by
  have hNc := Ncount_ge (n - 2 - j)
  have hEc := hU (n - 2 - j) hk
  have h14 : 14 * (j + 2) ≤ Ncount (n - 2 - j) := by omega
  have hpow : 2 ^ (j + 2) ≤ a (n - 2 - j) := a_ge_pow h14
  have hlt : 2 ^ (j + 1) < 2 ^ (j + 2) := by
    have he : (2 : ℕ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
    have hp : 0 < 2 ^ (j + 1) := by positivity
    omega
  omega

/-- From the chain, every term in the window `[n-L, n]` is even. -/
lemma a_even_run {n L t : ℕ} (hn2 : 2 ≤ n) (htL : t ≤ L) (hLn : L ≤ n - 2)
    (hbase : (e (n - 2)).natAbs = 2)
    (hcond : ∀ j, 1 ≤ j → j ≤ L → 2 ^ (j + 1) < a (n - 2 - j)) :
    a (n - t) % 2 = 0 := by
  have hchain : (e (n - 2 - t)).natAbs = 2 ^ (t + 1) := by
    apply chain t (n - 2 - t)
    · have h : n - 2 - t + t = n - 2 := by omega
      rw [h]; exact hbase
    · intro j hj1 hjt
      have hidx : n - 2 - t + (t - j) = n - 2 - j := by omega
      rw [hidx]
      exact hcond j hj1 (le_trans hjt htL)
  have heven : Even (e (n - 2 - t)) := by
    rw [← Int.natAbs_even, hchain]
    exact ⟨2 ^ t, by rw [pow_succ]; ring⟩
  have hk := (a_even_iff_e_even (n - 2 - t)).mpr heven
  have hidx2 : n - 2 - t + 2 = n - t := by omega
  rwa [hidx2] at hk

/-- Counting evens in a fully-even run. -/
lemma Ecount_run {c d : ℕ} (hcd : c ≤ d) (h : ∀ i, c ≤ i → i < d → a i % 2 = 0) :
    Ecount d = Ecount c + (d - c) := by
  induction d, hcd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    rw [Ecount_succ]
    have haeven : a d % 2 = 0 := h d hd (Nat.lt_succ_self d)
    rw [if_pos haeven, ih (fun i hi hid => h i hi (by omega))]
    omega

theorem disproof_dev :
    ¬ (({n : ℕ | a n % 2 = 0}).HasDensity (1 / 2 : ℝ) ∧
       Set.Infinite { n : ℕ | a (n + 1) = a n + 1 ∨ a n = a (n + 1) + 1 }) := by
  rintro ⟨hP, hQ⟩
  obtain ⟨K2, hU⟩ := upper_bound hP
  obtain ⟨K3, hL⟩ := lower_bound hP
  -- choose a large event index
  obtain ⟨n, hn_mem, hn_gt⟩ := hQ.exists_gt (40 * K2 + 40 * K3 + 100000)
  simp only [Set.mem_setOf_eq] at hn_mem
  have hnbig : 40 * K2 + 40 * K3 + 100000 < n := hn_gt
  have hn2 : 2 ≤ n := by omega
  set L := (n - 72) / 36 with hLdef
  -- the growth conditions for the chain
  have hcond : ∀ j, 1 ≤ j → j ≤ L → 2 ^ (j + 1) < a (n - 2 - j) := by
    intro j hj1 hjL
    apply cond_growth hU
    · omega
    · omega
  -- the difference relation at the event
  have hstep : (a (n + 1) : ℤ) - a n = e (n - 1) + e (n - 2) := by
    have hd := a_diff (n - 2)
    rw [show n - 2 + 3 = n + 1 from by omega, show n - 2 + 2 = n from by omega,
        show n - 2 + 1 = n - 1 from by omega] at hd
    exact hd
  have hdiff : (e (n - 1) + e (n - 2)).natAbs = 1 := by
    have key : ((a (n + 1) : ℤ) - a n) = 1 ∨ ((a (n + 1) : ℤ) - a n) = -1 := by
      rcases hn_mem with h | h
      · left; rw [h]; push_cast; ring
      · right; rw [h]; push_cast; ring
    rw [hstep] at key
    rcases key with h | h <;> rw [h] <;> decide
  -- a (n-1) > 2
  have hbig : 2 < a (n - 1) := by
    have hlb : 99 * (n - 1) ≤ 200 * Ncount (n - 1) := by
      have := Ncount_ge (n - 1); have := hU (n - 1) (by omega); omega
    have h28 : 14 * 2 ≤ Ncount (n - 1) := by omega
    have hp := a_ge_pow h28
    norm_num at hp; omega
  -- the base of the chain
  have hbase : (e (n - 2)).natAbs = 2 := by
    have hd' : (e (n - 2 + 1) + e (n - 2)).natAbs = 1 := by
      rw [show n - 2 + 1 = n - 1 from by omega]; exact hdiff
    have hbig' : 2 < a (n - 2 + 1) := by
      rw [show n - 2 + 1 = n - 1 from by omega]; exact hbig
    exact base_case hd' hbig'
  have hLn2 : L ≤ n - 2 := by omega
  -- the even run
  have hrun : ∀ i, n - L ≤ i → i < n + 1 → a i % 2 = 0 := by
    intro i hi1 hi2
    have hidx : i = n - (n - i) := by omega
    rw [hidx]
    exact a_even_run hn2 (by omega : n - i ≤ L) hLn2 hbase hcond
  -- counting
  have hcd : n - L ≤ n + 1 := by omega
  have hEcrun := Ecount_run hcd hrun
  have hUb : 200 * Ecount (n + 1) ≤ 101 * (n + 1) := hU (n + 1) (by omega)
  have hLb : 99 * (n - L) ≤ 200 * Ecount (n - L) := hL (n - L) (by omega)
  omega


/-- The local sequence `a` coincides with `A120424`. -/
lemma a_eq (n : ℕ) : a n = A120424 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      rw [a_succ_succ]
      show hf (a (m + 1)) + hf (a m) = A120424 (m + 2)
      rw [h1, h2]
      rfl

end HalfFib

theorem oeis_a120424_conjecture_0.disproof :
    ¬ (({n : ℕ | A120424 n % 2 = 0}).HasDensity (1/2 : ℝ) ∧
       Set.Infinite { n : ℕ | A120424 (n + 1) = A120424 n + 1 ∨ A120424 n = A120424 (n + 1) + 1 }) := by
  have hset1 : {n : ℕ | A120424 n % 2 = 0} = {n : ℕ | HalfFib.a n % 2 = 0} := by
    ext n; simp only [Set.mem_setOf_eq, HalfFib.a_eq]
  have hset2 : { n : ℕ | A120424 (n + 1) = A120424 n + 1 ∨ A120424 n = A120424 (n + 1) + 1 }
      = { n : ℕ | HalfFib.a (n + 1) = HalfFib.a n + 1 ∨ HalfFib.a n = HalfFib.a (n + 1) + 1 } := by
    ext n; simp only [Set.mem_setOf_eq, HalfFib.a_eq]
  rw [hset1, hset2]
  exact HalfFib.disproof_dev
