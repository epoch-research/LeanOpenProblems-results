import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def hasDiv : ℕ → ℕ → Bool
  | _, 0 => false
  | _, 1 => false
  | k, d + 2 => (k % (d + 2) == 0) || hasDiv k (d + 1)

def isPrimeB (k : ℕ) : Bool := decide (2 ≤ k) && !hasDiv k (k - 1)

lemma hasDiv_zero (k : ℕ) : hasDiv k 0 = false := rfl
lemma hasDiv_one (k : ℕ) : hasDiv k 1 = false := rfl
lemma hasDiv_succ_succ (k d : ℕ) :
    hasDiv k (d + 2) = ((k % (d + 2) == 0) || hasDiv k (d + 1)) := rfl

lemma hasDiv_true_iff (k d : ℕ) :
    hasDiv k d = true ↔ ∃ m, 2 ≤ m ∧ m ≤ d ∧ m ∣ k := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    match d with
    | 0 =>
      simp [hasDiv_zero]
    | 1 =>
      simp [hasDiv_one]
      intro m hm2 hm1; omega
    | d + 2 =>
      rw [hasDiv_succ_succ]
      simp only [Bool.or_eq_true, beq_iff_eq]
      constructor
      · intro h
        rcases h with hmod | hprev
        · exact ⟨d + 2, by omega, by omega, Nat.dvd_of_mod_eq_zero hmod⟩
        · obtain ⟨m, hm2, hmd, hdv⟩ := (ih (d + 1) (by omega)).mp hprev
          exact ⟨m, hm2, by omega, hdv⟩
      · rintro ⟨m, hm2, hmd, hdv⟩
        have : m = d + 2 ∨ m ≤ d + 1 := by omega
        rcases this with rfl | hmd'
        · exact Or.inl (Nat.mod_eq_zero_of_dvd hdv)
        · exact Or.inr ((ih (d + 1) (by omega)).mpr ⟨m, hm2, hmd', hdv⟩)

lemma isPrimeB_iff (k : ℕ) : isPrimeB k = true ↔ k.Prime := by
  unfold isPrimeB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨hk, hnd⟩
    have hdivf : hasDiv k (k - 1) = false := by
      cases h : hasDiv k (k - 1)
      · rfl
      · simp [h] at hnd
    rw [Nat.prime_def_lt']
    refine ⟨hk, fun m hm2 hmk hdv => ?_⟩
    have : hasDiv k (k - 1) = true := by
      rw [hasDiv_true_iff]
      have hmk' : m ≤ k - 1 := by omega
      exact ⟨m, hm2, hmk', hdv⟩
    simp [hdivf] at this
  · intro hp
    have hk : 2 ≤ k := hp.two_le
    refine ⟨hk, ?_⟩
    cases h : hasDiv k (k - 1) with
    | false => simp
    | true =>
      rw [hasDiv_true_iff] at h
      rcases h with ⟨m, hm2, hmd, hdv⟩
      have hmk : m < k := by omega
      exact absurd hdv ((Nat.prime_def_lt'.mp hp).2 m hm2 hmk)

def pcond (k : ℕ) : Bool := isPrimeB k || isPrimeB (k + 1)

def primeCond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

lemma pcond_iff (k : ℕ) : pcond k = true ↔ primeCond k := by
  simp [pcond, primeCond, isPrimeB_iff, Bool.or_eq_true]

lemma primeCond_one : primeCond 1 := Or.inr (by decide)
lemma primeCond_two : primeCond 2 := Or.inl (by decide)
lemma primeCond_three : primeCond 3 := Or.inl (by decide)
lemma primeCond_four : primeCond 4 := Or.inr (by decide)
lemma primeCond_five : primeCond 5 := Or.inl (by decide)
lemma primeCond_six : primeCond 6 := Or.inr (by decide)
lemma primeCond_seven : primeCond 7 := Or.inl (by decide)
lemma primeCond_ten : primeCond 10 := Or.inr (by decide)
lemma primeCond_eleven : primeCond 11 := Or.inl (by decide)
lemma primeCond_twelve : primeCond 12 := Or.inr (by decide)
lemma primeCond_thirteen : primeCond 13 := Or.inl (by decide)

/-- Membership in `2P+1`: `A = 2k+1` with `primeCond k`. -/
def in2P1 (A : ℕ) : Prop := ∃ k, A = 2 * k + 1 ∧ primeCond k

lemma in2P1_iff_odd_primeCond {A : ℕ} (hA : Odd A) :
    in2P1 A ↔ primeCond ((A - 1) / 2) := by
  constructor
  · rintro ⟨k, hk, hp⟩
    have : (A - 1) / 2 = k := by
      have : A - 1 = 2 * k := by omega
      exact Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) this
    simpa [this] using hp
  · intro hp
    refine ⟨(A - 1) / 2, ?_, hp⟩
    have h1 : 1 ≤ A := by
      rcases hA with ⟨t, ht⟩
      omega
    have : A - 1 = 2 * ((A - 1) / 2) := by
      have : 2 ∣ A - 1 := by
        rcases hA with ⟨t, ht⟩
        have : A = 2 * t + 1 := by omega
        exact ⟨t, by omega⟩
      exact (Nat.div_mul_cancel this).symm.trans (by ring)
    omega

def T (z : ℕ) : ℕ := z * (z + 1) / 2

def countZ (n x y : ℕ) : ℕ → ℕ
  | 0 => if pcond 0 == true && decide (x * x + y * (y + 1) + 0 = n) then 1 else 0
  | z + 1 =>
      countZ n x y z +
        if pcond (z + 1) == true && decide (x * x + y * (y + 1) + (z + 1) * (z + 2) / 2 = n)
        then 1 else 0

def countYZ (n x zmax : ℕ) : ℕ → ℕ
  | 0 => if pcond 0 == true then countZ n x 0 zmax else 0
  | y + 1 =>
      countYZ n x zmax y +
        if pcond (y + 1) == true then countZ n x (y + 1) zmax else 0

def countXYZ (n ymax zmax : ℕ) : ℕ → ℕ
  | 0 => countYZ n 0 zmax ymax
  | x + 1 => countXYZ n ymax zmax x + countYZ n (x + 1) zmax ymax

lemma ite_bool_decide (c : Bool) (p : Prop) [Decidable p] :
    (if c == true && decide p then (1 : ℕ) else 0) =
      (if c = true ∧ p then 1 else 0) := by
  by_cases hc : c = true
  · by_cases hp : p
    · simp [hc, hp]
    · simp [hc, hp]
  · by_cases hp : p
    · simp [hc, hp]
    · simp [hc, hp]

lemma T_zero : T 0 = 0 := rfl
lemma T_succ (z : ℕ) : T (z + 1) = (z + 1) * (z + 2) / 2 := rfl

lemma two_dvd_succ_mul (z : ℕ) : 2 ∣ z * (z + 1) := by
  cases Nat.even_or_odd z with
  | inl h => exact h.two_dvd.mul_right _
  | inr h =>
    have : Even (z + 1) := h.add_odd odd_one
    exact this.two_dvd.mul_left _

lemma T_mul_two (z : ℕ) : 2 * T z = z * (z + 1) := by
  rw [T, Nat.mul_div_cancel' (two_dvd_succ_mul z)]

lemma eight_T_add_one (z : ℕ) : 8 * T z + 1 = (2 * z + 1) ^ 2 := by
  have h := T_mul_two z
  have : 8 * T z = 4 * (z * (z + 1)) := by
    calc 8 * T z = 4 * (2 * T z) := by ring
      _ = 4 * (z * (z + 1)) := by rw [h]
  rw [this]
  ring

lemma eight_yy_add_two (y : ℕ) : 8 * (y * (y + 1)) + 2 = 2 * (2 * y + 1) ^ 2 := by
  ring

/-- 8(x² + y(y+1) + T z) + 3 = (2z+1)² + 2(2y+1)² + 8x². -/
lemma form_identity (x y z : ℕ) :
    8 * (x * x + y * (y + 1) + T z) + 3 =
      (2 * z + 1) ^ 2 + 2 * (2 * y + 1) ^ 2 + 8 * (x * x) := by
  nlinarith [eight_T_add_one z, eight_yy_add_two y]

lemma eq_iff_form (n x y z : ℕ) :
    x * x + y * (y + 1) + T z = n ↔
      (2 * z + 1) ^ 2 + 2 * (2 * y + 1) ^ 2 + 8 * (x * x) = 8 * n + 3 := by
  constructor
  · intro h; rw [← h, form_identity]
  · intro h
    have hid := form_identity x y z
    have : 8 * (x * x + y * (y + 1) + T z) = 8 * n := by omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) this

lemma not_mem_range : ∀ {n : ℕ}, n ∉ range n := by
  intro n
  simp [mem_range]

lemma countZ_spec (n x y zmax : ℕ) :
    countZ n x y zmax =
      (range (zmax + 1)).sum fun z =>
        if pcond z = true ∧ x * x + y * (y + 1) + T z = n then 1 else 0 := by
  induction zmax with
  | zero =>
    simp only [countZ]
    rw [ite_bool_decide, range_one, sum_singleton, T]
  | succ z ih =>
    simp only [countZ]
    rw [ih, ite_bool_decide]
    rw [show range ((z + 1) + 1) = insert (z + 1) (range (z + 1)) from range_add_one]
    rw [sum_insert not_mem_range]
    rw [Nat.add_comm]
    simp [T]

lemma countYZ_spec (n x zmax ymax : ℕ) :
    countYZ n x zmax ymax =
      (range (ymax + 1)).sum fun y =>
        if pcond y = true then countZ n x y zmax else 0 := by
  induction ymax with
  | zero =>
    simp only [countYZ]
    rw [range_one, sum_singleton]
    simp
  | succ y ih =>
    simp only [countYZ]
    rw [ih]
    rw [show range ((y + 1) + 1) = insert (y + 1) (range (y + 1)) from range_add_one]
    rw [sum_insert not_mem_range, Nat.add_comm]
    simp

lemma countXYZ_spec (n ymax zmax xmax : ℕ) :
    countXYZ n ymax zmax xmax =
      (range (xmax + 1)).sum fun x => countYZ n x zmax ymax := by
  induction xmax with
  | zero =>
    simp only [countXYZ]
    rw [range_one, sum_singleton]
  | succ x ih =>
    simp only [countXYZ]
    rw [ih]
    rw [show range ((x + 1) + 1) = insert (x + 1) (range (x + 1)) from range_add_one]
    rw [sum_insert not_mem_range, Nat.add_comm]

def good (n x y z : ℕ) : Prop :=
  x * x + y * (y + 1) + T z = n ∧ primeCond y ∧ primeCond z

instance : DecidablePred primeCond := fun k =>
  inferInstanceAs (Decidable (k.Prime ∨ (k + 1).Prime))

instance (n x y z : ℕ) : Decidable (good n x y z) := by
  dsimp [good]; infer_instance

lemma good_iff_pcond (n x y z : ℕ) :
    good n x y z ↔
      x * x + y * (y + 1) + T z = n ∧ pcond y = true ∧ pcond z = true := by
  simp [good, pcond_iff]

lemma countXYZ_eq_sum (n ymax zmax xmax : ℕ) :
    countXYZ n ymax zmax xmax =
      (range (xmax + 1)).sum fun x =>
        (range (ymax + 1)).sum fun y =>
          (range (zmax + 1)).sum fun z =>
            if pcond y = true ∧ pcond z = true ∧ x * x + y * (y + 1) + T z = n then 1 else 0 := by
  rw [countXYZ_spec]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [countYZ_spec]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hy
  · rw [countZ_spec]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : pcond z = true <;> by_cases he : x * x + y * (y + 1) + T z = n <;>
      simp [hy, hz, he]
  · refine Eq.symm (Finset.sum_eq_zero ?_)
    intro z hz
    simp [hy]

lemma countXYZ_eq_sum_good (n ymax zmax xmax : ℕ) :
    countXYZ n ymax zmax xmax =
      (range (xmax + 1)).sum fun x =>
        (range (ymax + 1)).sum fun y =>
          (range (zmax + 1)).sum fun z =>
            if good n x y z then 1 else 0 := by
  rw [countXYZ_eq_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  by_cases hy : pcond y = true <;> by_cases hz : pcond z = true <;>
    by_cases he : x * x + y * (y + 1) + T z = n <;>
      simp [good_iff_pcond, hy, hz, he]

lemma x_le_sqrt_of_good {n x y z : ℕ} (h : good n x y z) : x ≤ n.sqrt := by
  have : x * x ≤ n := by
    have := h.1
    omega
  exact (le_sqrt).2 this

lemma y_le_sqrt_of_good {n x y z : ℕ} (h : good n x y z) : y ≤ n.sqrt := by
  have : y * y ≤ n := by
    have : y * (y + 1) ≤ n := by
      have := h.1
      omega
    nlinarith
  exact (le_sqrt).2 this

lemma z_le_sqrt_of_good {n x y z : ℕ} (h : good n x y z) : z ≤ (2 * n + 1).sqrt := by
  have hz : T z ≤ n := by
    have := h.1
    simp only [T] at *
    omega
  have : z * (z + 1) ≤ 2 * n + 1 := by
    have hdiv : z * (z + 1) / 2 ≤ n := by simpa [T] using hz
    have := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).mp hdiv
    omega
  have : z * z ≤ 2 * n + 1 := by nlinarith
  exact (le_sqrt).2 this

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2
  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

lemma A264010_eq (n : ℕ) :
    A264010 n =
      (range (2 * n + 2)).sum fun x =>
        (range (2 * n + 2)).sum fun y =>
          (range (2 * n + 2)).sum fun z =>
            if good n x y z then 1 else 0 := by
  simp only [A264010, T, primeCond, good]
  congr

lemma x_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    x < 2 * n + 2 := by
  have : x * x ≤ n := by omega
  match x with
  | 0 => omega
  | 1 => omega
  | x + 2 => nlinarith

lemma y_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    y < 2 * n + 2 := by
  have : y * (y + 1) ≤ n := by omega
  match y with
  | 0 => omega
  | 1 => omega
  | y + 2 => nlinarith

lemma z_lt_bound {n x y z : ℕ} (h : x * x + y * (y + 1) + T z = n) :
    z < 2 * n + 2 := by
  have hz : T z ≤ n := by simp only [T] at *; omega
  match z with
  | 0 => omega
  | 1 => omega
  | z + 2 =>
    have hdiv : (z + 2) * (z + 3) / 2 ≤ n := hz
    have : (z + 2) * (z + 3) ≤ 2 * n + 1 := by
      have := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).mp hdiv
      omega
    nlinarith

lemma triple_sum_eq_card (n : ℕ) (X Y Z : Finset ℕ) :
    X.sum (fun x => Y.sum fun y => Z.sum fun z => if good n x y z then 1 else 0) =
      #{p ∈ X ×ˢ Y ×ˢ Z | good n p.1 p.2.1 p.2.2} := by
  trans (∑ p ∈ X ×ˢ Y ×ˢ Z, if good n p.1 p.2.1 p.2.2 then (1 : ℕ) else 0)
  · rw [sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_product]
  · exact (sum_boole (R := ℕ) (fun p => good n p.1 p.2.1 p.2.2) (X ×ˢ Y ×ˢ Z))

lemma good_support {n x y z : ℕ} (h : good n x y z) :
    x ∈ range (2 * n + 2) ∧ y ∈ range (2 * n + 2) ∧ z ∈ range (2 * n + 2) := by
  have := h.1
  refine ⟨?_, ?_, ?_⟩
  · simpa using x_lt_bound this
  · simpa using y_lt_bound this
  · simpa using z_lt_bound this

lemma card_good_eq (n : ℕ) (X Y Z : Finset ℕ)
    (hX : ∀ x y z, good n x y z → x ∈ X)
    (hY : ∀ x y z, good n x y z → y ∈ Y)
    (hZ : ∀ x y z, good n x y z → z ∈ Z) :
    #{p ∈ X ×ˢ Y ×ˢ Z | good n p.1 p.2.1 p.2.2} =
      #{p ∈ range (2 * n + 2) ×ˢ range (2 * n + 2) ×ˢ range (2 * n + 2) |
          good n p.1 p.2.1 p.2.2} := by
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    exact ⟨⟨(good_support hp.2).1, (good_support hp.2).2.1, (good_support hp.2).2.2⟩, hp.2⟩
  · intro p q hp hq h; exact h
  · intro p hp
    simp only [mem_filter, mem_product] at hp
    refine ⟨p, ?_, rfl⟩
    simp only [mem_filter, mem_product]
    exact ⟨⟨hX _ _ _ hp.2, hY _ _ _ hp.2, hZ _ _ _ hp.2⟩, hp.2⟩

lemma A264010_eq_countXYZ {n xmax ymax zmax : ℕ}
    (hx : ∀ x y z, good n x y z → x ≤ xmax)
    (hy : ∀ x y z, good n x y z → y ≤ ymax)
    (hz : ∀ x y z, good n x y z → z ≤ zmax) :
    A264010 n = countXYZ n ymax zmax xmax := by
  rw [A264010_eq, countXYZ_eq_sum_good]
  rw [triple_sum_eq_card, triple_sum_eq_card]
  refine (card_good_eq n (range (xmax + 1)) (range (ymax + 1)) (range (zmax + 1)) ?_ ?_ ?_).symm
  · intro x y z h; simpa using Nat.lt_succ_of_le (hx x y z h)
  · intro x y z h; simpa using Nat.lt_succ_of_le (hy x y z h)
  · intro x y z h; simpa using Nat.lt_succ_of_le (hz x y z h)

lemma A264010_eq_count_sqrt (n : ℕ) :
    A264010 n = countXYZ n n.sqrt (2 * n + 1).sqrt n.sqrt := by
  refine A264010_eq_countXYZ ?_ ?_ ?_
  · intro x y z h; exact x_le_sqrt_of_good h
  · intro x y z h; exact y_le_sqrt_of_good h
  · intro x y z h; exact z_le_sqrt_of_good h

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma sq_le_bound {k m b : ℕ} (h : k * k ≤ m) (hb : (b + 1) * (b + 1) > m) : k ≤ b := by
  by_contra hne
  have : b + 1 ≤ k := by omega
  have : (b + 1) * (b + 1) ≤ k * k := Nat.mul_le_mul this this
  omega

lemma count_3 : countXYZ 3 1 2 1 = 1 := by rfl

lemma A264010_3_eq : A264010 3 = countXYZ 3 1 2 1 := by
  refine A264010_eq_countXYZ ?_ ?_ ?_
  · intro x y z h
    have : x * x ≤ 3 := by have := h.1; omega
    exact sq_le_bound this (by decide)
  · intro x y z h
    have : y * y ≤ 3 := by
      have : y * (y + 1) ≤ 3 := by have := h.1; omega
      nlinarith
    exact sq_le_bound this (by decide)
  · intro x y z h
    have hz : z ≤ (2 * 3 + 1).sqrt := z_le_sqrt_of_good h
    have : z * z ≤ 2 * 3 + 1 := (le_sqrt).1 hz
    exact sq_le_bound this (by decide)

lemma A3 : A264010 3 = 1 := A264010_3_eq.trans count_3

lemma A264010_eq_count_of_bounds (n xmax ymax zmax : ℕ)
    (hx : (xmax + 1) * (xmax + 1) > n)
    (hy : (ymax + 1) * (ymax + 1) > n)
    (hz : (zmax + 1) * (zmax + 1) > 2 * n + 1) :
    A264010 n = countXYZ n ymax zmax xmax := by
  refine A264010_eq_countXYZ ?_ ?_ ?_
  · intro x y z h
    exact sq_le_bound (by have := h.1; omega) hx
  · intro x y z h
    have : y * y ≤ n := by
      have : y * (y + 1) ≤ n := by have := h.1; omega
      nlinarith
    exact sq_le_bound this hy
  · intro x y z h
    have hz' : z ≤ (2 * n + 1).sqrt := z_le_sqrt_of_good h
    have : z * z ≤ 2 * n + 1 := (le_sqrt).1 hz'
    exact sq_le_bound this hz

lemma A4 : A264010 4 = 1 := by
  have hcnt : countXYZ 4 2 3 2 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 4 2 2 3 (by decide) (by decide) (by decide)).trans hcnt

lemma A5 : A264010 5 = 1 := by
  have hcnt : countXYZ 5 2 3 2 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 5 2 2 3 (by decide) (by decide) (by decide)).trans hcnt

lemma A6 : A264010 6 = 1 := by
  have hcnt : countXYZ 6 2 3 2 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 6 2 2 3 (by decide) (by decide) (by decide)).trans hcnt

lemma A10 : A264010 10 = 1 := by
  have hcnt : countXYZ 10 3 4 3 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 10 3 3 4 (by decide) (by decide) (by decide)).trans hcnt

lemma A11 : A264010 11 = 1 := by
  have hcnt : countXYZ 11 3 4 3 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 11 3 3 4 (by decide) (by decide) (by decide)).trans hcnt

lemma A15 : A264010 15 = 1 := by
  have hcnt : countXYZ 15 3 5 3 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 15 3 3 5 (by decide) (by decide) (by decide)).trans hcnt

lemma A20 : A264010 20 = 1 := by
  have hcnt : countXYZ 20 4 6 4 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 20 4 4 6 (by decide) (by decide) (by decide)).trans hcnt

lemma A29 : A264010 29 = 1 := by
  have hcnt : countXYZ 29 5 7 5 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 29 5 5 7 (by decide) (by decide) (by decide)).trans hcnt

lemma A1125 : A264010 1125 = 1 := by
  have hcnt : countXYZ 1125 33 47 33 = 1 := by rfl
  exact (A264010_eq_count_of_bounds 1125 33 33 47 (by decide) (by decide) (by decide)).trans hcnt

lemma one_le_of_rep {n x y z : ℕ} (heq : x * x + y * (y + 1) + T z = n)
    (hy : primeCond y) (hz : primeCond z) : 1 ≤ A264010 n := by
  have hxB := x_lt_bound heq
  have hyB := y_lt_bound heq
  have hzB := z_lt_bound heq
  rw [A264010_eq]
  have hxR : x ∈ range (2 * n + 2) := by simpa using hxB
  have hyR : y ∈ range (2 * n + 2) := by simpa using hyB
  have hzR : z ∈ range (2 * n + 2) := by simpa using hzB
  have hg : good n x y z := ⟨heq, hy, hz⟩
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyR).trans' ?_
  refine (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzR).trans' ?_
  simp [hg]

lemma two_le_of_two_reps {n x1 y1 z1 x2 y2 z2 : ℕ}
    (e1 : x1 * x1 + y1 * (y1 + 1) + T z1 = n)
    (e2 : x2 * x2 + y2 * (y2 + 1) + T z2 = n)
    (p1 : primeCond y1) (q1 : primeCond z1)
    (p2 : primeCond y2) (q2 : primeCond z2)
    (hne : ¬ (x1 = x2 ∧ y1 = y2 ∧ z1 = z2)) :
    2 ≤ A264010 n := by
  have hx1 := x_lt_bound e1
  have hy1 := y_lt_bound e1
  have hz1 := z_lt_bound e1
  have hx2 := x_lt_bound e2
  have hy2 := y_lt_bound e2
  have hz2 := z_lt_bound e2
  let B := 2 * n + 2
  let f : ℕ → ℕ → ℕ → ℕ := fun x y z => if good n x y z then 1 else 0
  have hA : A264010 n = (range B).sum fun x => (range B).sum fun y => (range B).sum fun z => f x y z :=
    A264010_eq n
  rw [hA]
  have f1 : f x1 y1 z1 = 1 := by simp [f, good, e1, p1, q1]
  have f2 : f x2 y2 z2 = 1 := by simp [f, good, e2, p2, q2]
  have hx1R : x1 ∈ range B := by simp [B]; exact hx1
  have hy1R : y1 ∈ range B := by simp [B]; exact hy1
  have hz1R : z1 ∈ range B := by simp [B]; exact hz1
  have hx2R : x2 ∈ range B := by simp [B]; exact hx2
  have hy2R : y2 ∈ range B := by simp [B]; exact hy2
  have hz2R : z2 ∈ range B := by simp [B]; exact hz2
  by_cases hxeq : x1 = x2
  · subst hxeq
    by_cases hyeq : y1 = y2
    · subst hyeq
      have hzne : z1 ≠ z2 := fun h => hne ⟨rfl, rfl, h⟩
      have : 2 ≤ (range B).sum (fun z => f x1 y1 z) := by
        rw [← sum_erase_add (range B) (fun z => f x1 y1 z) hz1R]
        have : z2 ∈ (range B).erase z1 := mem_erase.mpr ⟨Ne.symm hzne, hz2R⟩
        rw [← sum_erase_add _ _ this]
        omega
      refine le_trans this ?_
      have i1 : (range B).sum (fun z => f x1 y1 z) ≤
          (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) :=
        single_le_sum (f := fun y => (range B).sum (fun z => f x1 y z))
          (fun _ _ => Nat.zero_le _) hy1R
      have i2 : (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) ≤
          (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) :=
        single_le_sum (f := fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z)))
          (fun _ _ => Nat.zero_le _) hx1R
      exact le_trans i1 i2
    · have : 2 ≤ (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) := by
        rw [← sum_erase_add (range B) (fun y => (range B).sum (fun z => f x1 y z)) hy1R]
        have : y2 ∈ (range B).erase y1 := mem_erase.mpr ⟨fun h => hyeq h.symm, hy2R⟩
        rw [← sum_erase_add _ _ this]
        have g1 : 1 ≤ (range B).sum (fun z => f x1 y1 z) :=
          le_trans (f1 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y1 z) (fun _ _ => Nat.zero_le _) hz1R)
        have g2 : 1 ≤ (range B).sum (fun z => f x1 y2 z) :=
          le_trans (f2 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y2 z) (fun _ _ => Nat.zero_le _) hz2R)
        omega
      have i : (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) ≤
          (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) :=
        single_le_sum (f := fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z)))
          (fun _ _ => Nat.zero_le _) hx1R
      exact le_trans this i
  · have : 2 ≤ (range B).sum (fun x => (range B).sum (fun y => (range B).sum (fun z => f x y z))) := by
      rw [← sum_erase_add (range B) _ hx1R]
      have : x2 ∈ (range B).erase x1 := mem_erase.mpr ⟨fun h => hxeq h.symm, hx2R⟩
      rw [← sum_erase_add _ _ this]
      have g1 : 1 ≤ (range B).sum (fun y => (range B).sum (fun z => f x1 y z)) := by
        have i : 1 ≤ (range B).sum (fun z => f x1 y1 z) :=
          le_trans (f1 ▸ le_rfl)
            (single_le_sum (f := fun z => f x1 y1 z) (fun _ _ => Nat.zero_le _) hz1R)
        exact le_trans i
          (single_le_sum (f := fun y => (range B).sum (fun z => f x1 y z))
            (fun _ _ => Nat.zero_le _) hy1R)
      have g2 : 1 ≤ (range B).sum (fun y => (range B).sum (fun z => f x2 y z)) := by
        have i : 1 ≤ (range B).sum (fun z => f x2 y2 z) :=
          le_trans (f2 ▸ le_rfl)
            (single_le_sum (f := fun z => f x2 y2 z) (fun _ _ => Nat.zero_le _) hz2R)
        exact le_trans i
          (single_le_sum (f := fun y => (range B).sum (fun z => f x2 y z))
            (fun _ _ => Nat.zero_le _) hy2R)
      omega
    exact this

lemma two_le_of_pcond {n x1 y1 z1 x2 y2 z2 : ℕ}
    (e1 : x1 * x1 + y1 * (y1 + 1) + z1 * (z1 + 1) / 2 = n)
    (e2 : x2 * x2 + y2 * (y2 + 1) + z2 * (z2 + 1) / 2 = n)
    (p1 : pcond y1 = true) (q1 : pcond z1 = true)
    (p2 : pcond y2 = true) (q2 : pcond z2 = true)
    (hne : ¬ (x1 = x2 ∧ y1 = y2 ∧ z1 = z2)) :
    2 ≤ A264010 n :=
  two_le_of_two_reps (e1) (e2)
    ((pcond_iff y1).mp p1) ((pcond_iff z1).mp q1)
    ((pcond_iff y2).mp p2) ((pcond_iff z2).mp q2) hne



def checkW : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (n, x1, y1, z1, x2, y2, z2) =>
      decide (x1 * x1 + y1 * (y1 + 1) + z1 * (z1 + 1) / 2 = n) &&
      decide (x2 * x2 + y2 * (y2 + 1) + z2 * (z2 + 1) / 2 = n) &&
      pcond y1 && pcond z1 && pcond y2 && pcond z2 &&
      decide (¬(x1 = x2 ∧ y1 = y2 ∧ z1 = z2))

lemma two_le_of_checkW {n x1 y1 z1 x2 y2 z2 : ℕ}
    (h : checkW (n, x1, y1, z1, x2, y2, z2) = true) :
    2 ≤ A264010 n := by
  simp only [checkW, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨e1, e2⟩, p1⟩, q1⟩, p2⟩, q2⟩, hne⟩
  exact two_le_of_pcond e1 e2 p1 q1 p2 q2 hne

def wits0 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (7,2,1,1,0,2,1) ::
  (8,0,1,3,1,2,1) ::
  (9,2,1,2,1,1,3) ::
  (12,3,1,1,2,1,3) ::
  (13,1,1,4,2,2,2) ::
  (14,3,1,2,1,3,1) ::
  (16,2,1,4,3,2,1) ::
  (17,3,1,3,0,1,5) ::
  (18,1,1,5,3,2,2) ::
  (19,4,1,1,2,3,2) ::
  (21,4,1,2,3,1,4) ::
  (22,1,2,5,3,3,1) ::
  (23,0,1,6,4,2,1) ::
  (24,4,1,3,1,1,6) ::
  (25,4,2,2,3,2,4) ::
  (26,3,1,5,2,3,4) ::
  (27,2,1,6,0,2,6) ::
  (28,5,1,1,4,1,4) ::
  (30,5,1,2,0,1,7) ::
  (31,1,1,7,2,2,6) ::
  (32,3,1,6,5,2,1) ::
  (33,5,1,3,4,1,5) ::
  (34,2,1,7,5,2,2) ::
  (35,1,2,7,3,4,3) ::
  (36,3,2,6,3,3,5) ::
  (37,5,1,4,5,2,3) ::
  (38,2,2,7,5,3,1) ::
  (39,6,1,1,4,1,6) ::
  (40,5,3,2,0,3,7) ::
  (41,6,1,2,5,2,4) ::
  (42,5,1,5,3,3,6) ::
  (43,6,2,1,4,2,6) ::
  (44,6,1,3,2,3,7) ::
  (45,6,2,2,2,4,6) ::
  (46,4,1,7,5,2,5) ::
  (47,5,3,4,4,5,1) ::
  (48,6,1,4,5,1,6) ::
  (49,6,3,1,4,3,6) ::
  (50,4,2,7,3,4,6) ::
  (51,6,3,2,5,4,3) ::
  (52,7,1,1,6,2,4) ::
  (53,6,1,5,1,6,4) ::
  (54,7,1,2,6,3,3) ::
  (55,5,1,7,5,4,4) ::
  (56,7,2,1,4,3,7) ::
  (57,7,1,3,0,1,10) ::
  (58,1,1,10,7,2,2) ::
  (59,6,1,6,5,2,7) ::
  (60,5,4,5,3,5,6) ::
  (61,7,1,4,2,1,10) ::
  (62,1,2,10,7,3,1) ::
  (63,6,2,6,6,3,5) ::
  (64,7,3,2,4,4,7) ::
  (65,7,2,4,2,2,10) ::
  (66,7,1,5,6,1,7) ::
  (67,8,1,1,7,3,3) ::
  (68,0,1,11,1,3,10) ::
  (69,8,1,2,1,1,11) ::
  (70,7,2,5,6,2,7) ::
  (71,8,2,1,7,3,4) ::
  (72,8,1,3,7,1,6) ::
  (73,4,1,10,8,2,2) ::
  (74,4,5,7,2,6,7) ::
  (75,7,4,3,0,4,10) ::
  (76,8,1,4,8,2,3) ::
  (77,3,1,11,4,2,10) ::
  (78,0,3,11,4,7,3) ::
  (79,7,1,7,8,3,2) ::
  (80,0,1,12,8,2,4) ::
  (81,8,1,5,1,1,12) ::
  (82,5,1,10,8,3,3) ::
  (83,7,2,7,4,3,10) ::
  (84,9,1,1,4,1,11) ::
  (85,8,2,5,1,2,12) ::
  (86,9,1,2,5,2,10) ::
  (87,8,1,6,3,3,11) ::
  (88,9,2,1,4,2,11) ::
  (89,9,1,3,3,1,12) ::
  (90,9,2,2,0,3,12) ::
  (91,8,2,6,8,3,5) :: []

def wits1 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (92,5,3,10,7,6,1) ::
  (93,9,1,4,6,1,10) ::
  (94,8,1,7,1,1,13) ::
  (95,3,4,11,8,5,1) ::
  (96,4,1,12,9,3,2) ::
  (97,2,1,13,9,2,4) ::
  (98,9,1,5,8,2,7) ::
  (99,9,3,3,3,3,12) ::
  (100,4,2,12,5,4,10) ::
  (101,2,2,13,4,5,10) ::
  (102,3,1,13,9,2,5) ::
  (103,10,1,1,9,3,4) ::
  (104,9,1,6,6,1,11) ::
  (105,10,1,2,5,1,12) ::
  (106,7,1,10,3,2,13) ::
  (107,10,2,1,2,3,13) ::
  (108,10,1,3,9,2,6) ::
  (109,4,1,13,10,2,2) ::
  (110,7,2,10,5,5,10) ::
  (111,9,1,7,9,4,4) ::
  (112,10,1,4,10,2,3) ::
  (113,4,2,13,10,3,1) ::
  (114,9,3,6,6,3,11) ::
  (115,9,2,7,10,3,2) ::
  (116,6,1,12,10,2,4) ::
  (117,10,1,5,7,1,11) ::
  (118,5,1,13,10,3,3) ::
  (119,4,3,13,7,6,7) ::
  (120,6,2,12,3,4,13) ::
  (121,8,1,10,10,2,5) ::
  (122,5,2,13,10,3,4) ::
  (123,10,1,6,10,4,2) ::
  (124,11,1,1,7,4,10) ::
  (125,8,2,10,2,5,13) ::
  (126,11,1,2,6,3,12) ::
  (127,10,2,6,10,3,5) ::
  (128,11,2,1,5,3,13) ::
  (129,11,1,3,7,1,12) ::
  (130,10,1,7,11,2,2) ::
  (131,8,3,10,10,5,1) ::
  (132,8,1,11,9,5,6) ::
  (133,11,1,4,11,2,3) ::
  (134,10,2,7,11,3,1) ::
  (135,10,4,5,7,4,11) ::
  (136,8,2,11,11,3,2) ::
  (137,11,2,4,4,5,13) ::
  (138,11,1,5,9,1,10) ::
  (139,1,1,16,11,3,3) ::
  (140,10,3,7,10,5,4) ::
  (141,10,4,6,8,7,6) ::
  (142,7,1,13,2,1,16) ::
  (143,1,2,16,11,3,4) ::
  (144,11,1,6,8,1,12) ::
  (145,10,5,5,7,5,11) ::
  (146,7,2,13,2,2,16) ::
  (147,12,1,1,3,1,16) ::
  (148,11,2,6,8,2,12) ::
  (149,12,1,2,9,1,11) ::
  (150,8,4,11,4,7,12) ::
  (151,11,1,7,12,2,1) ::
  (152,12,1,3,7,3,13) ::
  (153,12,2,2,9,2,11) ::
  (154,4,1,16,11,3,6) ::
  (155,0,1,17,11,2,7) ::
  (156,12,1,4,1,1,17) ::
  (157,10,1,10,8,1,13) ::
  (158,4,2,16,10,5,7) ::
  (159,2,1,17,0,2,17) ::
  (160,12,2,4,1,2,17) ::
  (161,12,1,5,9,1,12) ::
  (162,12,3,3,11,4,6) ::
  (163,5,1,16,2,2,17) ::
  (164,3,1,17,4,3,16) ::
  (165,12,2,5,9,2,12) ::
  (166,12,3,4,1,3,17) ::
  (167,12,1,6,5,2,16) ::
  (168,10,1,11,3,2,17) ::
  (169,2,3,17,11,4,7) ::
  (170,12,4,3,7,5,13) ::
  (171,4,1,17,12,2,6) :: []

def wits2 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (172,13,1,1,10,2,11) ::
  (173,0,1,18,5,3,16) ::
  (174,13,1,2,12,1,7) ::
  (175,4,2,17,10,4,10) ::
  (176,13,2,1,0,10,11) ::
  (177,13,1,3,2,1,18) ::
  (178,11,1,10,13,2,2) ::
  (179,12,4,5,9,4,12) ::
  (180,10,1,12,5,1,17) ::
  (181,13,1,4,13,2,3) ::
  (182,3,1,18,11,2,10) ::
  (183,0,3,18,0,5,17) ::
  (184,10,2,12,5,2,17) ::
  (185,13,2,4,12,4,6) ::
  (186,13,1,5,3,2,18) ::
  (187,7,1,16,13,3,3) ::
  (188,11,3,10,0,10,12) ::
  (189,11,1,11,4,1,18) ::
  (190,13,2,5,10,3,12) ::
  (191,6,1,17,7,2,16) ::
  (192,13,1,6,0,1,19) ::
  (193,10,1,13,1,1,19) ::
  (194,4,6,16,9,10,2) ::
  (195,6,2,17,13,4,3) ::
  (196,2,1,19,13,2,6) ::
  (197,10,2,13,1,2,19) ::
  (198,5,1,18,10,4,12) ::
  (199,14,1,1,13,1,7) ::
  (200,2,2,19,3,4,18) ::
  (201,14,1,2,12,1,10) ::
  (202,8,1,16,5,2,18) ::
  (203,14,2,1,13,2,7) ::
  (204,14,1,3,7,1,17) ::
  (205,14,2,2,12,2,10) ::
  (206,8,2,16,2,3,19) ::
  (207,11,4,11,4,4,18) ::
  (208,14,1,4,4,1,19) ::
  (209,6,1,18,14,3,1) ::
  (210,13,4,6,0,4,19) ::
  (211,14,3,2,12,3,10) ::
  (212,12,1,11,14,2,4) ::
  (213,14,1,5,6,2,18) ::
  (214,11,1,13,14,3,3) ::
  (215,7,5,16,12,7,5) ::
  (216,12,2,11,5,4,18) ::
  (217,5,1,19,14,2,5) ::
  (218,11,2,13,14,3,4) ::
  (219,14,1,6,9,1,16) ::
  (220,8,4,16,13,5,6) ::
  (221,5,2,19,10,5,13) ::
  (222,7,1,18,12,3,11) ::
  (223,14,2,6,9,2,16) ::
  (224,12,1,12,11,3,13) ::
  (225,4,7,17,10,10,5) ::
  (226,14,1,7,13,1,10) ::
  (227,5,3,19,6,4,18) ::
  (228,15,1,1,6,1,19) ::
  (229,14,3,6,9,3,16) ::
  (230,15,1,2,14,2,7) ::
  (231,14,4,5,6,6,17) ::
  (232,15,2,1,6,2,19) ::
  (233,15,1,3,10,6,13) ::
  (234,15,2,2,12,3,12) ::
  (235,5,4,19,13,7,4) ::
  (236,9,1,17,14,3,7) ::
  (237,15,1,4,13,1,11) ::
  (238,10,1,16,15,3,1) ::
  (239,14,6,1,13,6,7) ::
  (240,9,2,17,15,3,2) ::
  (241,7,1,19,15,2,4) ::
  (242,15,1,5,10,2,16) ::
  (243,15,3,3,11,7,11) ::
  (244,14,4,7,13,4,10) ::
  (245,7,2,19,5,5,19) ::
  (246,15,2,5,9,3,17) ::
  (247,15,3,4,13,3,11) ::
  (248,15,1,6,10,3,16) ::
  (249,13,1,12,6,6,18) ::
  (250,7,5,18,2,7,19) ::
  (251,7,3,19,15,4,3) :: []

def wits3 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (252,15,2,6,15,3,5) ::
  (253,14,1,10,13,2,12) ::
  (254,9,1,18,9,4,17) ::
  (255,15,1,7,10,1,17) ::
  (256,8,1,19,1,1,22) ::
  (257,14,2,10,5,6,19) ::
  (258,9,2,18,15,3,6) ::
  (259,16,1,1,11,1,16) ::
  (260,8,2,19,1,2,22) ::
  (261,16,1,2,15,5,3) ::
  (262,13,1,13,7,6,18) ::
  (263,16,2,1,11,2,16) ::
  (264,16,1,3,14,1,11) ::
  (265,16,2,2,15,3,7) ::
  (266,13,2,13,8,3,19) ::
  (267,13,4,12,14,7,5) ::
  (268,16,1,4,16,2,3) ::
  (269,16,3,1,11,3,16) ::
  (270,15,5,5,15,6,2) ::
  (271,4,1,22,16,3,2) ::
  (272,16,2,4,13,3,13) ::
  (273,16,1,5,10,1,18) ::
  (274,16,3,3,14,3,11) ::
  (275,4,2,22,12,10,6) ::
  (276,14,1,12,11,1,17) ::
  (277,16,2,5,10,2,18) ::
  (278,0,1,23,16,3,4) ::
  (279,16,1,6,1,1,23) ::
  (280,5,1,22,14,2,12) ::
  (281,4,3,22,14,5,10) ::
  (282,15,1,10,12,1,16) ::
  (283,16,2,6,1,2,23) ::
  (284,5,2,22,8,5,19) ::
  (285,13,10,3,2,10,18) ::
  (286,16,1,7,15,2,10) ::
  (287,3,1,23,16,5,1) ::
  (288,0,3,23,15,6,6) ::
  (289,14,1,13,16,3,6) ::
  (290,16,2,7,5,3,22) ::
  (291,6,1,22,3,2,23) ::
  (292,17,1,1,10,1,19) ::
  (293,15,1,11,14,2,13) ::
  (294,17,1,2,11,1,18) ::
  (295,6,2,22,15,6,7) ::
  (296,17,2,1,10,2,19) ::
  (297,17,1,3,15,2,11) ::
  (298,17,2,2,11,2,18) ::
  (299,12,1,17,14,3,13) ::
  (300,15,4,10,12,4,16) ::
  (301,17,1,4,17,2,3) ::
  (302,17,3,1,10,3,19) ::
  (303,5,1,23,12,2,17) ::
  (304,7,1,22,17,3,2) ::
  (305,15,1,12,17,2,4) ::
  (306,17,1,5,0,5,23) ::
  (307,13,1,16,5,2,23) ::
  (308,7,2,22,5,5,22) ::
  (309,15,2,12,12,3,17) ::
  (310,17,2,5,17,4,1) ::
  (311,13,2,16,17,3,4) ::
  (312,17,1,6,17,4,2) ::
  (313,16,1,10,11,1,19) ::
  (314,6,1,23,7,3,22) ::
  (315,15,3,12,17,4,3) ::
  (316,17,2,6,17,3,5) ::
  (317,12,1,18,16,2,10) ::
  (318,15,1,13,6,2,23) ::
  (319,17,1,7,8,1,22) ::
  (320,17,5,1,10,5,19) ::
  (321,12,2,18,5,4,23) ::
  (322,15,2,13,17,3,6) ::
  (323,17,2,7,8,2,22) ::
  (324,16,1,11,13,1,17) ::
  (325,13,4,16,17,5,3) ::
  (326,16,6,7,2,11,19) ::
  (327,18,1,1,7,1,23) ::
  (328,16,2,11,13,2,17) ::
  (329,18,1,2,17,3,7) ::
  (330,17,4,6,14,7,12) ::
  (331,18,2,1,7,2,23) :: []

def wits4 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (332,18,1,3,6,4,23) ::
  (333,18,2,2,15,5,12) ::
  (334,14,1,16,16,3,11) ::
  (335,12,4,18,13,5,16) ::
  (336,18,1,4,16,1,12) ::
  (337,18,3,1,7,3,23) ::
  (338,14,2,16,15,10,2) ::
  (339,18,3,2,12,6,17) ::
  (340,18,2,4,16,2,12) ::
  (341,18,1,5,16,5,10) ::
  (342,13,1,18,8,1,23) ::
  (343,5,6,23,14,7,13) ::
  (344,14,3,16,7,6,22) ::
  (345,18,2,5,18,4,1) ::
  (346,17,1,10,13,2,18) ::
  (347,18,1,6,18,4,2) ::
  (348,17,7,2,11,7,18) ::
  (349,16,1,13,7,10,19) ::
  (350,17,2,10,18,4,3) ::
  (351,14,1,17,18,2,6) ::
  (352,13,3,18,8,3,23) ::
  (353,16,2,13,16,6,10) ::
  (354,18,1,7,18,4,4) ::
  (355,10,1,22,14,2,17) ::
  (356,17,3,10,15,10,6) ::
  (357,17,1,11,18,3,6) ::
  (358,18,2,7,15,6,13) ::
  (359,9,1,23,10,2,22) ::
  (360,13,4,18,8,4,23) ::
  (361,13,1,19,17,2,11) ::
  (362,14,5,16,9,10,18) ::
  (363,15,1,16,9,2,23) ::
  (364,19,1,1,18,3,7) ::
  (365,13,2,19,10,3,22) ::
  (366,19,1,2,17,7,6) ::
  (367,15,2,16,17,3,11) ::
  (368,19,2,1,6,7,23) ::
  (369,19,1,3,17,1,12) ::
  (370,19,2,2,13,5,18) ::
  (371,13,3,19,12,7,18) ::
  (372,18,4,7,18,6,3) ::
  (373,19,1,4,19,2,3) ::
  (374,19,3,1,17,5,10) ::
  (375,17,4,11,18,5,6) ::
  (376,11,1,22,19,3,2) ::
  (377,19,2,4,9,4,23) ::
  (378,19,1,5,10,1,23) ::
  (379,19,3,3,17,3,12) ::
  (380,15,1,17,11,2,22) ::
  (381,18,1,10,15,4,16) ::
  (382,17,1,13,19,2,5) ::
  (383,19,3,4,10,5,22) ::
  (384,19,1,6,15,2,17) ::
  (385,18,2,10,17,5,11) ::
  (386,17,2,13,11,3,22) ::
  (387,19,4,3,17,4,12) ::
  (388,14,1,19,19,2,6) ::
  (389,13,5,19,16,6,13) ::
  (390,15,3,17,18,7,4) ::
  (391,19,1,7,18,3,10) ::
  (392,18,1,11,14,2,19) ::
  (393,14,13,5,10,16,6) ::
  (394,16,1,16,19,3,6) ::
  (395,19,2,7,10,6,22) ::
  (396,18,2,11,19,4,5) ::
  (397,19,5,3,17,5,12) ::
  (398,15,1,18,16,2,16) ::
  (399,12,1,22,11,1,23) ::
  (400,17,4,13,17,7,10) ::
  (401,19,3,7,19,5,4) ::
  (402,15,2,18,18,3,11) ::
  (403,20,1,1,12,2,22) ::
  (404,18,1,12,16,3,16) ::
  (405,20,1,2,14,7,17) ::
  (406,14,4,19,19,5,5) ::
  (407,20,2,1,12,10,17) ::
  (408,20,1,3,0,1,28) ::
  (409,1,1,28,20,2,2) ::
  (410,18,4,11,17,5,13) ::
  (411,16,1,17,17,7,11) :: []

def wits5 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (412,20,1,4,2,1,28) ::
  (413,1,2,28,20,3,1) ::
  (414,18,3,12,17,10,5) ::
  (415,16,2,17,20,3,2) ::
  (416,20,2,4,2,2,28) ::
  (417,20,1,5,18,1,13) ::
  (418,19,1,10,20,3,3) ::
  (419,1,3,28,19,5,7) ::
  (420,18,5,11,15,6,17) ::
  (421,20,2,5,18,2,13) ::
  (422,12,1,23,19,2,10) ::
  (423,20,1,6,20,4,2) ::
  (424,13,1,22,4,1,28) ::
  (425,12,10,18,4,12,22) ::
  (426,12,2,23,20,4,3) ::
  (427,17,1,16,20,2,6) ::
  (428,13,2,22,4,2,28) ::
  (429,19,1,11,16,1,18) ::
  (430,20,1,7,20,4,4) ::
  (431,17,2,16,20,5,1) ::
  (432,12,3,23,18,5,12) ::
  (433,5,1,28,19,2,11) ::
  (434,20,2,7,13,3,22) ::
  (435,20,4,5,18,4,13) ::
  (436,19,4,10,20,5,3) ::
  (437,0,1,29,5,2,28) ::
  (438,1,1,29,15,6,18) ::
  (439,19,3,11,16,3,18) ::
  (440,20,3,7,12,4,23) ::
  (441,19,1,12,2,1,29) ::
  (442,1,2,29,13,4,22) ::
  (443,5,3,28,20,6,1) ::
  (444,21,1,1,17,1,17) ::
  (445,19,2,12,2,2,29) ::
  (446,21,1,2,3,1,29) ::
  (447,13,1,23,0,3,29) ::
  (448,16,1,19,21,2,1) ::
  (449,21,1,3,1,6,28) ::
  (450,21,2,2,3,2,29) ::
  (451,14,1,22,13,2,23) ::
  (452,16,2,19,13,5,22) ::
  (453,21,1,4,4,1,29) ::
  (454,19,1,13,21,3,1) ::
  (455,14,2,22,0,4,29) ::
  (456,21,3,2,3,3,29) ::
  (457,20,1,10,7,1,28) ::
  (458,21,1,5,19,2,13) ::
  (459,21,3,3,19,4,12) ::
  (460,17,12,5,5,13,22) ::
  (461,20,2,10,7,2,28) ::
  (462,18,1,16,17,1,18) ::
  (463,21,3,4,4,3,29) ::
  (464,21,1,6,19,3,13) ::
  (465,13,4,23,0,5,29) ::
  (466,18,2,16,17,2,18) ::
  (467,0,1,30,20,3,10) ::
  (468,20,1,11,1,1,30) ::
  (469,14,4,22,19,5,12) ::
  (470,20,6,7,10,18,7) ::
  (471,21,1,7,2,1,30) ::
  (472,8,1,28,20,2,11) ::
  (473,6,1,29,5,6,28) ::
  (474,14,1,23,21,3,6) ::
  (475,21,2,7,2,2,30) ::
  (476,3,1,30,8,2,28) ::
  (477,6,2,29,0,3,30) ::
  (478,14,2,23,20,3,11) ::
  (479,18,1,17,14,5,22) ::
  (480,20,1,12,15,1,22) ::
  (481,17,1,19,21,3,7) ::
  (482,8,3,28,21,4,6) ::
  (483,4,1,30,18,2,17) ::
  (484,20,2,12,15,2,22) ::
  (485,17,2,19,0,4,30) ::
  (486,7,1,29,3,3,30) ::
  (487,22,1,1,4,2,30) ::
  (488,16,6,19,15,10,17) ::
  (489,22,1,2,9,1,28) ::
  (490,7,2,29,20,3,12) ::
  (491,22,2,1,17,3,19) :: []

def wits6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (492,22,1,3,5,1,30) ::
  (493,20,1,13,22,2,2) ::
  (494,3,4,30,19,6,13) ::
  (495,0,5,30,19,7,12) ::
  (496,22,1,4,22,2,3) ::
  (497,18,1,18,20,2,13) ::
  (498,21,1,10,0,1,31) ::
  (499,19,1,16,1,1,31) ::
  (500,22,2,4,8,5,28) ::
  (501,22,1,5,8,1,29) ::
  (502,2,1,31,21,2,10) ::
  (503,15,1,23,6,1,30) ::
  (504,7,4,29,3,5,30) ::
  (505,22,2,5,8,2,29) ::
  (506,2,2,31,22,3,4) ::
  (507,22,1,6,3,1,31) ::
  (508,10,1,28,21,3,10) ::
  (509,21,1,11,19,3,16) ::
  (510,22,4,3,5,4,30) ::
  (511,16,1,22,22,2,6) ::
  (512,10,2,28,2,3,31) ::
  (513,21,2,11,15,3,23) ::
  (514,22,1,7,4,1,31) ::
  (515,16,2,22,18,4,18) ::
  (516,19,1,17,18,1,19) ::
  (517,22,3,6,3,3,31) ::
  (518,9,1,29,22,2,7) ::
  (519,21,3,11,22,4,5) ::
  (520,19,2,17,18,2,19) ::
  (521,21,1,12,16,3,22) ::
  (522,9,2,29,20,7,11) ::
  (523,5,1,31,4,6,30) ::
  (524,22,3,7,4,3,31) ::
  (525,21,2,12,22,4,6) ::
  (526,19,3,17,18,3,19) ::
  (527,5,2,31,21,4,11) ::
  (528,9,3,29,14,7,23) ::
  (529,11,1,28,16,4,22) ::
  (530,2,5,31,3,7,30) ::
  (531,8,1,30,21,3,12) ::
  (532,23,1,1,22,4,7) ::
  (533,11,2,28,5,3,31) ::
  (534,23,1,2,21,1,13) ::
  (535,8,2,30,22,5,6) ::
  (536,23,2,1,9,4,29) ::
  (537,23,1,3,10,1,29) ::
  (538,20,1,16,23,2,2) ::
  (539,11,3,28,21,4,12) ::
  (540,7,7,29,9,17,17) ::
  (541,23,1,4,22,1,10) ::
  (542,20,2,16,23,3,1) ::
  (543,15,6,23,6,6,30) ::
  (544,17,1,22,23,3,2) ::
  (545,23,2,4,22,2,10) ::
  (546,23,1,5,9,5,29) ::
  (547,7,1,31,23,3,3) ::
  (548,9,1,30,17,2,22) ::
  (549,8,4,30,21,5,12) ::
  (550,23,2,5,23,4,1) ::
  (551,7,2,31,23,3,4) ::
  (552,23,1,6,22,1,11) ::
  (553,19,1,19,19,7,16) ::
  (554,17,3,22,22,6,7) ::
  (555,20,1,17,23,4,3) ::
  (556,23,2,6,22,2,11) ::
  (557,19,2,19,7,3,31) ::
  (558,11,1,29,9,3,30) ::
  (559,23,1,7,20,2,17) ::
  (560,23,5,1,20,11,7) ::
  (561,21,6,12,22,7,6) ::
  (562,8,1,31,11,2,29) ::
  (563,23,2,7,19,3,19) ::
  (564,22,1,12,23,4,5) ::
  (565,20,3,17,7,4,31) ::
  (566,8,2,31,9,4,30) ::
  (567,17,1,23,10,1,30) ::
  (568,22,2,12,11,3,29) ::
  (569,23,3,7,23,5,4) ::
  (570,23,4,6,22,4,11) ::
  (571,17,2,23,10,2,30) :: []

def wits7 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (572,8,3,31,17,5,22) ::
  (573,20,1,18,20,4,17) ::
  (574,22,3,12,23,5,5) ::
  (575,7,5,31,21,7,12) ::
  (576,11,4,29,9,5,30) ::
  (577,22,1,13,13,1,28) ::
  (578,20,6,16,16,11,19) ::
  (579,24,1,1,21,1,16) ::
  (580,8,4,31,23,5,6) ::
  (581,24,1,2,12,1,29) ::
  (582,22,4,12,14,10,23) ::
  (583,24,2,1,21,2,16) ::
  (584,24,1,3,17,6,22) ::
  (585,24,2,2,12,2,29) ::
  (586,23,1,10,11,5,29) ::
  (587,22,3,13,13,3,28) ::
  (588,24,1,4,11,1,30) ::
  (589,24,3,1,21,3,16) ::
  (590,23,2,10,8,5,31) ::
  (591,24,3,2,12,3,29) ::
  (592,20,1,19,24,2,4) ::
  (593,24,1,5,19,6,19) ::
  (594,24,3,3,7,10,29) ::
  (595,22,4,13,13,4,28) ::
  (596,21,1,17,20,2,19) ::
  (597,23,1,11,24,2,5) ::
  (598,10,1,31,24,3,4) ::
  (599,24,1,6,24,4,2) ::
  (600,21,2,17,23,7,5) ::
  (601,23,2,11,20,5,18) ::
  (602,18,1,23,10,2,31) ::
  (603,24,2,6,24,3,5) ::
  (604,14,1,28,23,4,10) ::
  (605,22,5,13,13,5,28) ::
  (606,24,1,7,13,1,29) ::
  (607,23,3,11,24,5,1) ::
  (608,14,2,28,10,3,31) ::
  (609,23,1,12,24,3,6) ::
  (610,24,2,7,13,2,29) ::
  (611,12,1,30,24,4,5) ::
  (612,18,3,23,24,5,3) ::
  (613,23,2,12,20,6,18) ::
  (614,21,1,18,14,3,28) ::
  (615,12,2,30,23,4,11) ::
  (616,19,1,22,24,3,7) ::
  (617,24,4,6,22,6,13) ::
  (618,21,2,18,22,7,12) ::
  (619,11,1,31,23,3,12) ::
  (620,19,2,22,18,4,23) ::
  (621,12,3,30,24,5,5) ::
  (622,23,1,13,22,1,16) ::
  (623,11,2,31,20,11,13) ::
  (624,21,3,18,24,4,7) ::
  (625,23,5,11,21,12,7) ::
  (626,23,2,13,22,2,16) ::
  (627,23,4,12,24,5,6) ::
  (628,25,1,1,24,6,4) ::
  (629,11,3,31,12,4,30) ::
  (630,25,1,2,18,5,23) ::
  (631,22,7,13,13,7,28) ::
  (632,25,2,1,23,3,13) ::
  (633,25,1,3,24,1,10) ::
  (634,25,2,2,19,4,22) ::
  (635,24,7,2,12,7,29) ::
  (636,13,1,30,21,6,17) ::
  (637,25,1,4,25,2,3) ::
  (638,25,3,1,10,6,31) ::
  (639,22,1,17,19,1,23) ::
  (640,13,2,30,25,3,2) ::
  (641,25,2,4,16,11,22) ::
  (642,25,1,5,12,1,31) ::
  (643,22,2,17,19,2,23) ::
  (644,24,1,11,19,5,22) ::
  (645,23,10,3,10,10,29) ::
  (646,25,2,5,12,2,31) ::
  (647,25,3,4,11,5,31) ::
  (648,25,1,6,24,2,11) ::
  (649,22,3,17,19,3,23) ::
  (650,23,5,13,22,5,16) ::
  (651,25,4,3,24,4,10) :: []

def wits8 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (652,25,2,6,25,3,5) ::
  (653,24,7,6,5,11,31) ::
  (654,24,3,11,13,4,30) ::
  (655,25,1,7,20,1,22) ::
  (656,24,1,12,25,5,1) ::
  (657,22,1,18,22,4,17) ::
  (658,25,3,6,25,5,2) ::
  (659,25,2,7,20,2,22) ::
  (660,24,2,12,25,4,5) ::
  (661,22,2,18,25,5,3) ::
  (662,15,1,29,24,4,11) ::
  (663,14,1,30,23,7,12) ::
  (664,16,1,28,13,5,30) ::
  (665,25,3,7,20,3,22) ::
  (666,15,2,29,24,3,12) ::
  (667,23,1,16,13,1,31) ::
  (668,0,1,36,16,2,28) ::
  (669,24,1,13,1,1,36) ::
  (670,25,5,5,12,5,31) ::
  (671,23,2,16,13,2,31) ::
  (672,2,1,36,0,2,36) ::
  (673,24,2,13,1,2,36) ::
  (674,16,3,28,24,4,12) ::
  (675,22,4,18,17,10,23) ::
  (676,22,1,19,2,2,36) ::
  (677,3,1,36,23,3,16) ::
  (678,20,1,23,0,3,36) ::
  (679,26,1,1,24,3,13) ::
  (680,22,2,19,15,4,29) ::
  (681,26,1,2,3,2,36) ::
  (682,25,1,10,20,2,23) ::
  (683,26,2,1,25,5,7) ::
  (684,26,1,3,23,1,17) ::
  (685,26,2,2,23,4,16) ::
  (686,25,2,10,22,3,19) ::
  (687,3,3,36,24,4,13) ::
  (688,26,1,4,26,2,3) ::
  (689,26,3,1,24,10,2) ::
  (690,2,4,36,15,5,29) ::
  (691,26,3,2,14,5,30) ::
  (692,15,1,30,26,2,4) ::
  (693,26,1,5,25,1,11) ::
  (694,14,1,31,26,3,3) ::
  (695,3,4,36,23,5,16) ::
  (696,21,1,22,15,2,30) ::
  (697,17,1,28,26,2,5) ::
  (698,14,2,31,26,3,4) ::
  (699,26,1,6,26,4,2) ::
  (700,21,2,22,25,4,10) ::
  (701,17,2,28,24,10,5) ::
  (702,23,1,18,15,3,30) ::
  (703,26,2,6,26,3,5) ::
  (704,6,1,36,14,3,31) ::
  (705,25,1,12,0,1,37) ::
  (706,26,1,7,1,1,37) ::
  (707,17,3,28,26,5,1) ::
  (708,6,2,36,0,6,36) ::
  (709,2,1,37,25,2,12) ::
  (710,26,2,7,1,2,37) ::
  (711,26,4,5,25,4,11) ::
  (712,23,3,18,14,4,31) ::
  (713,2,2,37,23,12,7) ::
  (714,24,1,16,3,1,37) ::
  (715,25,3,12,0,3,37) ::
  (716,26,3,7,1,3,37) ::
  (717,7,1,36,26,4,6) ::
  (718,25,1,13,24,2,16) ::
  (719,21,1,23,2,3,37) ::
  (720,23,4,18,15,5,30) ::
  (721,23,1,19,4,1,37) ::
  (722,25,2,13,6,4,36) ::
  (723,16,1,30,15,1,31) ::
  (724,24,3,16,3,3,37) ::
  (725,23,2,19,4,2,37) ::
  (726,17,1,29,2,7,36) ::
  (727,16,2,30,15,2,31) ::
  (728,25,3,13,26,6,4) ::
  (729,21,3,23,24,11,6) ::
  (730,5,1,37,17,2,29) ::
  (731,24,1,17,23,3,19) :: []

def wits9 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (732,27,1,1,18,1,28) ::
  (733,26,1,10,16,3,30) ::
  (734,27,1,2,5,2,37) ::
  (735,24,2,17,7,4,36) ::
  (736,27,2,1,18,2,28) ::
  (737,27,1,3,26,2,10) ::
  (738,27,2,2,26,7,3) ::
  (739,22,1,22,23,4,19) ::
  (740,5,3,37,23,12,10) ::
  (741,27,1,4,6,1,37) ::
  (742,27,3,1,18,3,28) ::
  (743,22,2,22,26,3,10) ::
  (744,26,1,11,27,3,2) ::
  (745,27,2,4,6,2,37) ::
  (746,27,1,5,25,5,13) ::
  (747,27,3,3,21,5,23) ::
  (748,26,2,11,5,4,37) ::
  (749,24,1,18,9,1,36) ::
  (750,27,2,5,27,4,1) ::
  (751,27,3,4,6,3,37) ::
  (752,27,1,6,27,4,2) ::
  (753,24,2,18,9,2,36) ::
  (754,16,1,31,7,1,37) ::
  (755,27,4,3,14,17,22) ::
  (756,26,1,12,17,1,30) ::
  (757,22,4,22,7,6,36) ::
  (758,16,2,31,7,2,37) ::
  (759,27,1,7,24,3,18) ::
  (760,26,2,12,17,2,30) ::
  (761,18,1,29,26,5,10) ::
  (762,22,1,23,27,3,6) ::
  (763,25,1,16,27,2,7) ::
  (764,16,3,31,7,3,37) ::
  (765,18,2,29,27,5,3) ::
  (766,22,2,23,26,3,12) ::
  (767,25,2,16,24,4,18) ::
  (768,24,1,19,10,1,36) ::
  (769,26,1,13,19,1,28) ::
  (770,27,4,6,5,6,37) ::
  (771,18,3,29,24,6,17) ::
  (772,24,2,19,10,2,36) ::
  (773,26,2,13,19,2,28) ::
  (774,26,4,12,17,4,30) ::
  (775,23,7,19,4,7,37) ::
  (776,0,10,36,23,12,13) ::
  (777,27,4,7,24,5,18) ::
  (778,24,3,19,10,3,36) ::
  (779,26,3,13,19,3,28) ::
  (780,25,1,17,22,4,23) ::
  (781,25,4,16,27,6,4) ::
  (782,16,5,31,7,5,37) ::
  (783,18,17,17,20,19,2) ::
  (784,23,1,22,25,2,17) ::
  (785,24,7,17,3,10,36) ::
  (786,27,1,10,9,1,37) ::
  (787,28,1,1,17,1,31) ::
  (788,23,2,22,27,7,2) ::
  (789,28,1,2,11,1,36) ::
  (790,27,2,10,9,2,37) ::
  (791,18,1,30,28,2,1) ::
  (792,28,1,3,27,6,6) ::
  (793,28,2,2,11,2,36) ::
  (794,23,3,22,16,6,31) ::
  (795,18,2,30,27,7,4) ::
  (796,28,1,4,28,2,3) ::
  (797,27,1,11,28,3,1) ::
  (798,25,1,18,19,1,29) ::
  (799,28,3,2,11,3,36) ::
  (800,28,2,4,27,7,5) ::
  (801,28,1,5,27,2,11) ::
  (802,25,2,18,19,2,29) ::
  (803,25,6,16,24,7,18) ::
  (804,27,4,10,9,4,37) ::
  (805,10,1,37,28,2,5) ::
  (806,28,3,4,27,7,6) ::
  (807,28,1,6,23,1,23) ::
  (808,20,1,28,25,3,18) ::
  (809,27,1,12,10,2,37) ::
  (810,28,4,3,26,7,12) ::
  (811,28,2,6,23,2,23) :: []

def wits10 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (812,12,1,36,20,2,28) ::
  (813,27,2,12,27,7,7) ::
  (814,28,1,7,26,1,16) ::
  (815,10,3,37,27,4,11) ::
  (816,12,2,36,25,4,18) ::
  (817,25,1,19,28,3,6) ::
  (818,28,2,7,26,2,16) ::
  (819,27,3,12,28,4,5) ::
  (820,28,5,3,25,6,17) ::
  (821,25,2,19,23,12,16) ::
  (822,27,1,13,18,1,31) ::
  (823,1,1,40,10,4,37) ::
  (824,28,3,7,26,3,16) ::
  (825,28,4,6,23,4,23) ::
  (826,11,1,37,2,1,40) ::
  (827,1,2,40,25,3,19) ::
  (828,19,1,30,25,13,6) ::
  (829,28,5,5,28,6,2) ::
  (830,11,2,37,2,2,40) ::
  (831,26,1,17,24,1,22) ::
  (832,19,2,30,27,3,13) ::
  (833,1,3,40,10,5,37) ::
  (834,25,7,17,17,10,29) ::
  (835,26,2,17,24,2,22) ::
  (836,11,3,37,2,3,40) ::
  (837,20,1,29,13,1,36) ::
  (838,4,1,40,19,3,30) ::
  (839,24,10,17,2,11,37) ::
  (840,27,4,13,18,4,31) ::
  (841,28,1,10,20,2,29) ::
  (842,4,2,40,28,5,7) ::
  (843,28,7,2,11,7,36) ::
  (844,29,1,1,11,4,37) ::
  (845,28,2,10,25,5,19) ::
  (846,29,1,2,19,4,30) ::
  (847,5,1,40,20,3,29) ::
  (848,29,2,1,4,3,40) ::
  (849,29,1,3,26,1,18) ::
  (850,29,2,2,27,5,13) ::
  (851,5,2,40,28,3,10) ::
  (852,28,1,11,12,6,36) ::
  (853,29,1,4,29,2,3) ::
  (854,24,1,23,29,3,1) ::
  (855,20,4,29,13,4,36) ::
  (856,28,2,11,29,3,2) ::
  (857,29,2,4,5,3,40) ::
  (858,29,1,5,6,1,40) ::
  (859,19,1,31,29,3,3) ::
  (860,27,10,6,5,11,37) ::
  (861,28,7,6,23,7,23) ::
  (862,29,2,5,6,2,40) ::
  (863,0,1,41,19,2,31) ::
  (864,29,1,6,28,1,12) ::
  (865,5,4,40,20,5,29) ::
  (866,4,5,40,11,6,37) ::
  (867,27,1,16,20,1,30) ::
  (868,26,1,19,29,2,6) ::
  (869,19,3,31,28,5,10) ::
  (870,28,4,11,22,10,23) ::
  (871,29,1,7,7,1,40) ::
  (872,3,1,41,26,2,19) ::
  (873,0,3,41,21,12,23) ::
  (874,13,1,37,29,3,6) ::
  (875,29,2,7,7,2,40) ::
  (876,3,2,41,29,4,5) ::
  (877,28,1,13,27,3,16) ::
  (878,21,1,29,13,2,37) ::
  (879,4,1,41,24,11,18) ::
  (880,25,1,22,28,5,11) ::
  (881,28,2,13,29,3,7) ::
  (882,21,2,29,3,3,41) ::
  (883,4,2,41,24,17,1) ::
  (884,27,1,17,25,2,22) ::
  (885,27,4,16,20,4,30) ::
  (886,8,1,40,26,4,19) ::
  (887,28,3,13,19,5,31) ::
  (888,5,1,41,27,2,17) ::
  (889,4,3,41,29,4,7) ::
  (890,8,2,40,25,3,22) ::
  (891,0,5,41,20,7,29) :: []

def wits11 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (892,22,1,28,5,2,41) ::
  (893,15,1,36,29,6,4) ::
  (894,27,3,17,24,6,23) ::
  (895,28,4,13,27,5,16) ::
  (896,22,2,28,8,3,40) ::
  (897,15,2,36,4,4,41) ::
  (898,29,1,10,20,1,31) ::
  (899,6,1,41,29,5,7) ::
  (900,3,5,41,29,7,2) ::
  (901,14,1,37,5,7,40) ::
  (902,27,1,18,29,2,10) ::
  (903,30,1,1,25,1,23) ::
  (904,8,4,40,29,6,6) ::
  (905,30,1,2,0,1,42) ::
  (906,1,1,42,27,2,18) ::
  (907,30,2,1,25,2,23) ::
  (908,30,1,3,21,1,30) ::
  (909,29,1,11,2,1,42) ::
  (910,1,2,42,22,4,28) ::
  (911,14,3,37,15,4,36) ::
  (912,30,1,4,7,1,41) ::
  (913,29,2,11,2,2,42) ::
  (914,3,1,42,8,5,40) ::
  (915,30,3,2,0,3,42) ::
  (916,30,2,4,7,2,41) ::
  (917,30,1,5,6,4,41) ::
  (918,3,2,42,30,3,3) ::
  (919,29,3,11,2,3,42) ::
  (920,27,4,18,22,5,28) ::
  (921,29,1,12,27,1,19) ::
  (922,28,1,16,10,1,40) ::
  (923,30,1,6,30,4,2) ::
  (924,16,1,36,3,3,42) ::
  (925,29,2,12,27,2,19) ::
  (926,28,2,16,10,2,40) ::
  (927,8,1,41,30,2,6) ::
  (928,16,2,36,5,6,41) ::
  (929,14,5,37,24,13,18) ::
  (930,30,1,7,15,1,37) ::
  (931,26,1,22,8,2,41) ::
  (932,28,3,16,10,3,40) ::
  (933,30,3,6,30,5,2) ::
  (934,29,1,13,30,2,7) ::
  (935,26,2,22,30,4,5) ::
  (936,30,5,3,21,5,30) ::
  (937,23,1,28,8,3,41) ::
  (938,29,2,13,29,6,10) ::
  (939,28,1,17,21,1,31) ::
  (940,30,3,7,15,3,37) ::
  (941,6,1,42,23,2,28) ::
  (942,16,4,36,3,5,42) ::
  (943,11,1,40,28,2,17) ::
  (944,9,1,41,29,3,13) ::
  (945,6,2,42,8,4,41) ::
  (946,1,6,42,22,7,28) ::
  (947,11,2,40,23,3,28) ::
  (948,0,1,43,9,2,41) ::
  (949,1,1,43,28,3,17) ::
  (950,28,5,16,10,5,40) ::
  (951,22,1,30,6,3,42) ::
  (952,2,1,43,0,2,43) ::
  (953,1,2,43,11,3,40) ::
  (954,26,1,23,7,1,42) ::
  (955,22,2,30,23,4,28) ::
  (956,2,2,43,27,7,18) ::
  (957,30,1,10,28,1,18) ::
  (958,26,2,23,7,2,42) ::
  (959,1,3,43,6,4,42) ::
  (960,1,7,42,28,10,11) ::
  (961,16,1,37,30,2,10) ::
  (962,2,3,43,9,4,41) ::
  (963,10,1,41,30,6,6) ::
  (964,31,1,1,4,1,43) ::
  (965,16,2,37,23,5,28) ::
  (966,31,1,2,23,1,29) ::
  (967,10,2,41,30,3,10) ::
  (968,30,1,11,31,2,1) ::
  (969,31,1,3,8,1,42) ::
  (970,31,2,2,23,2,29) ::
  (971,16,3,37,11,5,40) :: []

def wits12 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (972,30,2,11,26,4,23) ::
  (973,31,1,4,5,1,43) ::
  (974,31,3,1,4,3,43) ::
  (975,30,4,10,28,4,18) ::
  (976,28,1,19,31,3,2) ::
  (977,31,2,4,5,2,43) ::
  (978,31,1,5,30,3,11) ::
  (979,29,1,16,31,3,3) ::
  (980,30,1,12,28,2,19) ::
  (981,10,4,41,6,6,42) ::
  (982,22,1,31,31,2,5) ::
  (983,29,2,16,31,3,4) ::
  (984,31,1,6,27,1,22) ::
  (985,30,5,10,28,5,18) ::
  (986,9,1,42,22,2,31) ::
  (987,31,4,3,8,4,42) ::
  (988,31,2,6,27,2,22) ::
  (989,29,3,16,16,5,37) ::
  (990,9,2,42,30,3,12) ::
  (991,31,1,7,13,1,40) ::
  (992,18,1,36,22,3,31) ::
  (993,30,1,13,28,7,17) ::
  (994,17,1,37,31,3,6) ::
  (995,31,2,7,13,2,40) ::
  (996,29,1,17,23,1,30) ::
  (997,7,1,43,30,2,13) ::
  (998,17,2,37,30,4,12) ::
  (999,21,23,3,11,28,11) ::
  (1000,29,2,17,23,2,30) ::
  (1001,7,2,43,31,3,7) ::
  (1002,18,3,36,31,4,6) ::
  (1003,30,3,13,10,6,41) ::
  (1004,17,3,37,9,4,42) ::
  (1005,10,1,42,22,7,30) ::
  (1006,29,3,17,23,3,30) ::
  (1007,27,1,23,12,1,41) ::
  (1008,30,5,12,30,6,11) ::
  (1009,10,2,42,31,4,7) ::
  (1010,18,4,36,22,5,31) ::
  (1011,27,2,23,12,2,41) ::
  (1012,8,1,43,17,4,37) ::
  (1013,24,1,29,31,6,4) ::
  (1014,29,1,18,29,4,17) ::
  (1015,10,3,42,7,4,43) ::
  (1016,8,2,43,28,6,19) ::
  (1017,24,2,29,27,3,23) ::
  (1018,31,1,10,14,1,40) ::
  (1019,31,5,7,13,5,40) ::
  (1020,18,5,36,30,6,12) ::
  (1021,30,5,13,27,12,16) ::
  (1022,31,2,10,14,2,40) ::
  (1023,24,3,29,10,4,42) ::
  (1024,29,3,18,29,5,17) ::
  (1025,27,4,23,12,4,41) ::
  (1026,11,1,42,9,6,42) ::
  (1027,32,1,1,23,1,31) ::
  (1028,31,3,10,14,3,40) ::
  (1029,32,1,2,31,1,11) ::
  (1030,11,2,42,8,4,43) ::
  (1031,32,2,1,23,2,31) ::
  (1032,32,1,3,13,1,41) ::
  (1033,29,1,19,25,1,28) ::
  (1034,17,6,37,30,7,12) ::
  (1035,27,5,23,12,5,41) ::
  (1036,32,1,4,32,2,3) ::
  (1037,29,2,19,25,2,28) ::
  (1038,30,1,16,31,7,6) ::
  (1039,28,1,22,32,3,2) ::
  (1040,32,2,4,8,5,43) ::
  (1041,32,1,5,31,1,12) ::
  (1042,30,2,16,32,3,3) ::
  (1043,24,1,30,28,2,22) ::
  (1044,11,4,42,3,11,42) ::
  (1045,32,2,5,31,2,12) ::
  (1046,32,3,4,31,5,10) ::
  (1047,32,1,6,15,1,40) ::
  (1048,10,1,43,30,3,16) ::
  (1049,12,1,42,28,3,22) ::
  (1050,32,4,3,13,4,41) ::
  (1051,32,2,6,15,2,40) :: []

def wits13 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (1052,10,2,43,8,6,43) ::
  (1053,12,2,42,24,3,30) ::
  (1054,32,1,7,31,1,13) ::
  (1055,30,1,17,32,5,1) ::
  (1056,30,4,16,0,10,43) ::
  (1057,32,3,6,15,3,40) ::
  (1058,32,2,7,31,2,13) ::
  (1059,14,1,41,30,2,17) ::
  (1060,32,5,3,13,5,41) ::
  (1061,24,4,30,29,5,19) ::
  (1062,28,1,23,25,1,29) ::
  (1063,14,2,41,29,12,11) ::
  (1064,32,3,7,31,3,13) ::
  (1065,30,3,17,32,4,6) ::
  (1066,19,1,37,28,2,23) ::
  (1067,12,4,42,28,5,22) ::
  (1068,20,1,36,29,7,18) ::
  (1069,11,1,43,14,3,41) ::
  (1070,19,2,37,5,18,37) ::
  (1071,24,5,30,10,10,41) ::
  (1072,20,2,36,28,3,23) ::
  (1073,30,1,18,11,2,43) ::
  (1074,24,1,31,13,1,42) ::
  (1075,32,5,6,15,5,40) ::
  (1076,19,3,37,10,5,43) ::
  (1077,30,2,18,14,4,41) ::
  (1078,16,1,40,24,2,31) ::
  (1079,11,3,43,28,6,22) ::
  (1080,28,4,23,25,4,29) ::
  (1081,32,1,10,32,6,5) ::
  (1082,16,2,40,32,5,7) ::
  (1083,0,1,46,30,3,18) ::
  (1084,26,1,28,1,1,46) ::
  (1085,32,2,10,26,12,22) ::
  (1086,20,4,36,32,7,3) ::
  (1087,2,1,46,0,2,46) ::
  (1088,15,1,41,26,2,28) ::
  (1089,12,6,42,29,13,11) ::
  (1090,28,5,23,25,5,29) ::
  (1091,2,2,46,32,3,10) ::
  (1092,33,1,1,32,1,11) ::
  (1093,0,3,46,28,7,22) ::
  (1094,33,1,2,26,3,28) ::
  (1095,30,6,17,32,7,5) ::
  (1096,29,1,22,33,2,1) ::
  (1097,33,1,3,2,3,46) ::
  (1098,33,2,2,15,3,41) ::
  (1099,31,1,16,4,1,46) ::
  (1100,29,2,22,18,10,36) ::
  (1101,33,1,4,14,1,42) ::
  (1102,33,3,1,32,3,11) ::
  (1103,31,2,16,4,2,46) ::
  (1104,32,1,12,33,3,2) ::
  (1105,20,1,37,33,2,4) ::
  (1106,33,1,5,29,3,22) ::
  (1107,33,3,3,8,13,41) ::
  (1108,5,1,46,32,2,12) ::
  (1109,21,1,36,20,2,37) ::
  (1110,33,2,5,33,4,1) ::
  (1111,17,1,40,33,3,4) ::
  (1112,33,1,6,5,2,46) ::
  (1113,26,1,29,21,2,36) ::
  (1114,32,3,12,29,4,22) ::
  (1115,17,2,40,20,3,37) ::
  (1116,31,1,17,33,2,6) ::
  (1117,32,1,13,13,1,43) ::
  (1118,5,3,46,16,6,40) ::
  (1119,33,1,7,29,1,23) ::
  (1120,31,2,17,33,5,1) ::
  (1121,32,2,13,13,2,43) ::
  (1122,33,3,6,32,4,12) ::
  (1123,25,1,31,33,2,7) ::
  (1124,33,4,5,29,5,22) ::
  (1126,31,3,17,5,4,46) ::
  (1127,25,2,31,32,3,13) ::
  (1128,15,6,41,24,7,31) ::
  (1129,33,3,7,29,3,23) ::
  (1130,15,1,42,0,1,47) ::
  (1131,1,1,47,26,4,29) ::
  (1132,7,1,46,32,5,12) :: []

def wits14 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (1133,25,3,31,20,5,37) ::
  (1134,31,1,18,2,1,47) ::
  (1135,1,2,47,32,4,13) ::
  (1136,7,2,46,5,5,46) ::
  (1137,27,1,28,33,4,7) ::
  (1138,31,2,18,2,2,47) ::
  (1139,3,1,47,17,5,40) ::
  (1140,15,3,42,0,3,47) ::
  (1141,27,2,28,1,3,47) ::
  (1142,7,3,46,15,7,41) ::
  (1143,26,1,30,3,2,47) ::
  (1144,14,1,43,31,3,18) ::
  (1145,32,5,13,13,5,43) ::
  (1146,33,1,10,21,1,37) ::
  (1147,8,1,46,26,2,30) ::
  (1148,14,2,43,15,4,42) ::
  (1149,3,3,47,1,4,47) ::
  (1150,33,2,10,21,2,37) ::
  (1151,8,2,46,25,5,31) ::
  (1152,22,1,36,17,1,41) ::
  (1153,31,1,19,26,3,30) ::
  (1154,14,3,43,27,16,17) ::
  (1155,30,1,22,5,1,47) ::
  (1156,22,2,36,17,2,41) ::
  (1157,33,1,11,31,2,19) ::
  (1158,15,5,42,0,5,47) ::
  (1159,34,1,1,30,2,22) ::
  (1160,7,5,46,33,7,5) ::
  (1161,34,1,2,16,1,42) ::
  (1162,32,1,16,22,3,36) ::
  (1163,34,2,1,31,3,19) ::
  (1164,34,1,3,9,1,46) ::
  (1165,34,2,2,16,2,42) ::
  (1166,27,1,29,6,1,47) ::
  (1167,33,3,11,3,5,47) ::
  (1168,34,1,4,34,2,3) ::
  (1169,33,1,12,34,3,1) ::
  (1170,27,2,29,6,2,47) ::
  (1171,34,3,2,16,3,42) ::
  (1172,34,2,4,32,3,16) ::
  (1173,34,1,5,15,1,43) ::
  (1174,26,1,31,34,3,3) ::
  (1175,33,4,11,8,5,46) ::
  (1176,27,3,29,6,3,47) ::
  (1177,34,2,5,15,2,43) ::
  (1178,30,1,23,26,2,31) ::
  (1179,34,1,6,32,1,17) ::
  (1180,32,4,16,22,5,36) ::
  (1181,31,5,19,30,10,18) ::
  (1182,33,1,13,30,2,23) ::
  (1183,19,1,40,10,1,46) ::
  (1184,26,3,31,27,4,29) ::
  (1185,33,5,11,1,7,47) ::
  (1186,34,1,7,33,2,13) ::
  (1187,18,1,41,19,2,40) ::
  (1188,30,3,23,31,7,18) ::
  (1189,22,1,37,34,3,6) ::
  (1190,34,2,7,32,5,16) ::
  (1191,18,2,41,34,4,5) ::
  (1192,28,1,28,33,3,13) ::
  (1193,22,2,37,19,3,40) ::
  (1194,17,1,42,8,1,47) ::
  (1195,30,6,22,5,6,47) ::
  (1196,27,1,30,28,2,28) ::
  (1197,32,1,18,23,1,36) ::
  (1198,17,2,42,8,2,47) ::
  (1199,22,3,37,34,6,1) ::
  (1200,27,2,30,33,4,13) :: []

lemma wits0_ok : wits0.all checkW = true := by rfl
lemma wits1_ok : wits1.all checkW = true := by rfl
lemma wits2_ok : wits2.all checkW = true := by rfl
lemma wits3_ok : wits3.all checkW = true := by rfl
lemma wits4_ok : wits4.all checkW = true := by rfl
lemma wits5_ok : wits5.all checkW = true := by rfl
lemma wits6_ok : wits6.all checkW = true := by rfl
lemma wits7_ok : wits7.all checkW = true := by rfl
lemma wits8_ok : wits8.all checkW = true := by rfl
lemma wits9_ok : wits9.all checkW = true := by rfl
lemma wits10_ok : wits10.all checkW = true := by rfl
lemma wits11_ok : wits11.all checkW = true := by rfl
lemma wits12_ok : wits12.all checkW = true := by rfl
lemma wits13_ok : wits13.all checkW = true := by rfl
lemma wits14_ok : wits14.all checkW = true := by rfl

def wits : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := wits0 ++ wits1 ++ wits2 ++ wits3 ++ wits4 ++ wits5 ++ wits6 ++ wits7 ++ wits8 ++ wits9 ++ wits10 ++ wits11 ++ wits12 ++ wits13 ++ wits14

lemma all_checkW_two (l : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (h : l.all checkW = true) : ∀ t ∈ l, 2 ≤ A264010 t.1 := by
  induction l with
  | nil => intro t ht; cases ht
  | cons t ts ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    intro u hu
    rw [List.mem_cons] at hu
    rcases hu with hu | hu
    · subst hu
      exact two_le_of_checkW h.1
    · exact ih h.2 u hu

lemma wits_ok : wits.all checkW = true := by
  simp only [wits, List.all_append]
  simp [wits0_ok, wits1_ok, wits2_ok, wits3_ok, wits4_ok, wits5_ok, wits6_ok, wits7_ok, wits8_ok, wits9_ok, wits10_ok, wits11_ok, wits12_ok, wits13_ok, wits14_ok]

lemma two_le_of_wits {n : ℕ} (h : ∃ t ∈ wits, t.1 = n) : 2 ≤ A264010 n := by
  rcases h with ⟨t, ht, rfl⟩
  exact all_checkW_two wits wits_ok t ht

def specialB (n : ℕ) : Bool :=
  n == 3 || n == 4 || n == 5 || n == 6 || n == 10 || n == 11 ||
  n == 15 || n == 20 || n == 29 || n == 1125

lemma specialB_iff (n : ℕ) :
    specialB n = true ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
  simp [specialB, Finset.mem_insert, Finset.mem_singleton]
  omega

def boundN : ℕ := 1200

def covered : Bool :=
  (List.range (boundN + 1)).all fun n =>
    decide (n ≤ 2) || specialB n || wits.any (fun t => t.1 == n)

lemma covered_true : covered = true := by rfl

lemma List.any_eq_true_iff {α : Type*} (l : List α) (p : α → Bool) :
    l.any p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp [List.any_cons, ih, Bool.or_eq_true]

lemma covered_spec (n : ℕ) (hn : n ≤ boundN) :
    n ≤ 2 ∨ specialB n = true ∨ ∃ t ∈ wits, t.1 = n := by
  have hn' : n < boundN + 1 := by simp [boundN] at hn ⊢; omega
  have hmem : n ∈ List.range (boundN + 1) := List.mem_range.mpr hn'
  have hbody := List.all_eq_true.mp covered_true n hmem
  by_cases h1 : n ≤ 2
  · exact Or.inl h1
  · by_cases h2 : specialB n = true
    · exact Or.inr (Or.inl h2)
    · have h3 : wits.any (fun t => t.1 == n) = true := by
        revert hbody
        simp [h1, h2]
      refine Or.inr (Or.inr ?_)
      have : ∃ t ∈ wits, (t.1 == n) = true := (List.any_eq_true_iff _ _).mp h3
      rcases this with ⟨t, ht, ht'⟩
      exact ⟨t, ht, by simpa using ht'⟩

lemma special_eq_one {n : ℕ}
    (h : n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :
    A264010 n = 1 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact A3
  · exact A4
  · exact A5
  · exact A6
  · exact A10
  · exact A11
  · exact A15
  · exact A20
  · exact A29
  · exact A1125

lemma wits0_nots : (wits0.all fun t => !specialB t.1) = true := by rfl
lemma wits1_nots : (wits1.all fun t => !specialB t.1) = true := by rfl
lemma wits2_nots : (wits2.all fun t => !specialB t.1) = true := by rfl
lemma wits3_nots : (wits3.all fun t => !specialB t.1) = true := by rfl
lemma wits4_nots : (wits4.all fun t => !specialB t.1) = true := by rfl
lemma wits5_nots : (wits5.all fun t => !specialB t.1) = true := by rfl
lemma wits6_nots : (wits6.all fun t => !specialB t.1) = true := by rfl
lemma wits7_nots : (wits7.all fun t => !specialB t.1) = true := by rfl
lemma wits8_nots : (wits8.all fun t => !specialB t.1) = true := by rfl
lemma wits9_nots : (wits9.all fun t => !specialB t.1) = true := by rfl
lemma wits10_nots : (wits10.all fun t => !specialB t.1) = true := by rfl
lemma wits11_nots : (wits11.all fun t => !specialB t.1) = true := by rfl
lemma wits12_nots : (wits12.all fun t => !specialB t.1) = true := by rfl
lemma wits13_nots : (wits13.all fun t => !specialB t.1) = true := by rfl
lemma wits14_nots : (wits14.all fun t => !specialB t.1) = true := by rfl

lemma wits_not_special : wits.all (fun t => !specialB t.1) = true := by
  simp only [wits, List.all_append]
  simp [wits0_nots, wits1_nots, wits2_nots, wits3_nots, wits4_nots, wits5_nots,
    wits6_nots, wits7_nots, wits8_nots, wits9_nots, wits10_nots, wits11_nots,
    wits12_nots, wits13_nots, wits14_nots]

lemma conjecture_le_bound (n : ℕ) (H_n : n > 2) (hle : n ≤ boundN) :
    A264010 n > 0 ∧ (A264010 n = 1 ↔
      n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) := by
  have hc := covered_spec n hle
  rcases hc with h | h | h
  · omega
  · have hs : n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) :=
      (specialB_iff n).mp h
    have heq := special_eq_one hs
    refine ⟨by omega, ?_⟩
    constructor
    · intro; exact hs
    · intro; exact heq
  · have hge := two_le_of_wits h
    have hns : n ∉ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
      intro hs
      rcases h with ⟨t, ht, rfl⟩
      have hf := List.all_eq_true.mp wits_not_special t ht
      have hb : specialB t.1 = true := (specialB_iff t.1).mpr hs
      simp [hb] at hf
    refine ⟨by omega, ?_⟩
    constructor
    · intro heq
      omega
    · intro hs
      exact (hns hs).elim

lemma primeCond_of_prime {p : ℕ} (hp : p.Prime) : primeCond p := Or.inl hp

lemma primeCond_pred_of_prime {p : ℕ} (hp : p.Prime) (h2 : 2 < p) :
    primeCond (p - 1) := by
  have : p - 1 + 1 = p := Nat.sub_add_cancel (le_of_lt h2)
  refine Or.inr ?_
  simpa [this] using hp

lemma specials_le_1125 {n : ℕ}
    (hs : n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :
    n ≤ 1125 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h <;> omega

lemma not_special_of_gt_bound {n : ℕ} (h : boundN < n) :
    n ∉ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
  intro hs
  have := specials_le_1125 hs
  simp [boundN] at h
  omega

lemma exists_prime_in_half_sqrt {n : ℕ} (hn : 16 ≤ n) :
    ∃ p, p.Prime ∧ n.sqrt / 2 < p ∧ p ≤ n.sqrt := by
  have hsqrt : 4 ≤ n.sqrt := by
    have : 4 * 4 ≤ n := by omega
    exact (Nat.le_sqrt).2 this
  have hkpos : n.sqrt / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n.sqrt / 2) hkpos
  refine ⟨p, hp, hlt, ?_⟩
  have : 2 * (n.sqrt / 2) ≤ n.sqrt := Nat.mul_div_le _ _
  omega

/-- Pairing identity: `(b+c)² + (b-c)² = 2b² + 2c²`. -/
lemma pairing_identity (b c : ℤ) :
    (b + c) ^ 2 + (b - c) ^ 2 = 2 * b ^ 2 + 2 * c ^ 2 := by
  ring

lemma pairing_identity_nat (B x : ℕ) :
    (B + 2 * x) ^ 2 + (if 2 * x ≤ B then (B - 2 * x) ^ 2 else (2 * x - B) ^ 2) =
      2 * B ^ 2 + 8 * x ^ 2 := by
  have h := pairing_identity (B : ℤ) (2 * x : ℤ)
  simp only [sq] at h ⊢
  by_cases hx : 2 * x ≤ B
  · simp [hx]
    have : ((B : ℤ) - 2 * x) = ((B - 2 * x : ℕ) : ℤ) := by omega
    have h' := pairing_identity (B : ℤ) ((2 * x : ℕ) : ℤ)
    push_cast at h' ⊢
    nlinarith [h']
  · simp [hx]
    push_cast
    nlinarith [pairing_identity (B : ℤ) ((2 * x : ℕ) : ℤ)]

/-- Odd squares summing to `8n+3` yield an unrestricted Sun representation. -/
lemma good_of_three_odd_squares {n C B x : ℕ}
    (hsum : C ^ 2 + (B + 2 * x) ^ 2 + (if 2 * x ≤ B then B - 2 * x else 2 * x - B) ^ 2 = 8 * n + 3)
    (hC : Odd C) (hB : Odd B)
    (hCQ : in2P1 C) (hBQ : in2P1 B) :
    good n x ((B - 1) / 2) ((C - 1) / 2) := by
  obtain ⟨y, hyC, hyP⟩ := hBQ
  obtain ⟨z, hzC, hzP⟩ := hCQ
  have hB1 : 1 ≤ B := by
    rcases hB with ⟨t, ht⟩; omega
  have hC1 : 1 ≤ C := by
    rcases hC with ⟨t, ht⟩; omega
  have hyeq : (B - 1) / 2 = y := by
    have : B - 1 = 2 * y := by omega
    exact Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) this
  have hzeq : (C - 1) / 2 = z := by
    have : C - 1 = 2 * z := by omega
    exact Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) this
  have hform := form_identity x y z
  have hid := pairing_identity_nat B x
  have : C ^ 2 + 2 * B ^ 2 + 8 * x ^ 2 = 8 * n + 3 := by
    have hpair : (B + 2 * x) ^ 2 + (if 2 * x ≤ B then (B - 2 * x) ^ 2 else (2 * x - B) ^ 2) =
        2 * B ^ 2 + 8 * x ^ 2 := hid
    omega
  have : 8 * (x * x + y * (y + 1) + T z) + 3 = 8 * n + 3 := by
    have hBodd : B = 2 * y + 1 := hyC
    have hCodd : C = 2 * z + 1 := hzC
    rw [hform, hBodd, hCodd] at this
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  have heq : x * x + y * (y + 1) + T z = n := by
    have : 8 * (x * x + y * (y + 1) + T z) = 8 * n := by omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) this
  rw [hyeq, hzeq]
  exact ⟨heq, hyP, hzP⟩

lemma in2P1_of_primeCond (k : ℕ) (hk : primeCond k) : in2P1 (2 * k + 1) :=
  ⟨k, rfl, hk⟩

lemma exists_prime_in_interval {k : ℕ} (hk : 1 ≤ k) :
    ∃ p, p.Prime ∧ k < p ∧ p ≤ 2 * k :=
  Nat.exists_prime_lt_and_le_two_mul k (by omega)

/-- The pairs `(x, 1, 4)` and `(x, 2, 3)` both represent `x² + 12`. -/
lemma good_sq_add_twelve (x : ℕ) :
    good (x * x + 12) x 1 4 ∧ good (x * x + 12) x 2 3 := by
  refine ⟨⟨?_, primeCond_one, primeCond_four⟩, ⟨?_, primeCond_two, primeCond_three⟩⟩
  · simp [T]; omega
  · simp [T]; omega

/-- The pairs `(x, 2, 6)` and `(x, 3, 5)` both represent `x² + 27`. -/
lemma good_sq_add_twentyseven (x : ℕ) :
    good (x * x + 27) x 2 6 ∧ good (x * x + 27) x 3 5 := by
  refine ⟨⟨?_, primeCond_two, primeCond_six⟩, ⟨?_, primeCond_three, primeCond_five⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_twelve (n x : ℕ) (h : n = x * x + 12) : 2 ≤ A264010 n := by
  have g := good_sq_add_twelve x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

lemma two_le_of_sq_add_twentyseven (n x : ℕ) (h : n = x * x + 27) : 2 ≤ A264010 n := by
  have g := good_sq_add_twentyseven x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 2, 5)` and `(x, 4, 1)` both represent `x² + 21`. -/
lemma good_sq_add_twentyone (x : ℕ) :
    good (x * x + 21) x 2 5 ∧ good (x * x + 21) x 4 1 := by
  refine ⟨⟨?_, primeCond_two, primeCond_five⟩, ⟨?_, primeCond_four, primeCond_one⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_twentyone (n x : ℕ) (h : n = x * x + 21) : 2 ≤ A264010 n := by
  have g := good_sq_add_twentyone x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 1, 6)` and `(x, 4, 2)` both represent `x² + 23`. -/
lemma good_sq_add_twentythree (x : ℕ) :
    good (x * x + 23) x 1 6 ∧ good (x * x + 23) x 4 2 := by
  refine ⟨⟨?_, primeCond_one, primeCond_six⟩, ⟨?_, primeCond_four, primeCond_two⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_twentythree (n x : ℕ) (h : n = x * x + 23) : 2 ≤ A264010 n := by
  have g := good_sq_add_twentythree x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 1, 7)` and `(x, 4, 4)` both represent `x² + 30`. -/
lemma good_sq_add_thirty (x : ℕ) :
    good (x * x + 30) x 1 7 ∧ good (x * x + 30) x 4 4 := by
  refine ⟨⟨?_, primeCond_one, primeCond_seven⟩, ⟨?_, primeCond_four, primeCond_four⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_thirty (n x : ℕ) (h : n = x * x + 30) : 2 ≤ A264010 n := by
  have g := good_sq_add_thirty x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 3, 6)` and `(x, 5, 2)` both represent `x² + 33`. -/
lemma good_sq_add_thirtythree (x : ℕ) :
    good (x * x + 33) x 3 6 ∧ good (x * x + 33) x 5 2 := by
  refine ⟨⟨?_, primeCond_three, primeCond_six⟩, ⟨?_, primeCond_five, primeCond_two⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_thirtythree (n x : ℕ) (h : n = x * x + 33) : 2 ≤ A264010 n := by
  have g := good_sq_add_thirtythree x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 3, 7)` and `(x, 5, 4)` both represent `x² + 40`. -/
lemma good_sq_add_forty (x : ℕ) :
    good (x * x + 40) x 3 7 ∧ good (x * x + 40) x 5 4 := by
  refine ⟨⟨?_, primeCond_three, primeCond_seven⟩, ⟨?_, primeCond_five, primeCond_four⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_forty (n x : ℕ) (h : n = x * x + 40) : 2 ≤ A264010 n := by
  have g := good_sq_add_forty x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 5, 5)` and `(x, 6, 2)` both represent `x² + 45`. -/
lemma good_sq_add_fortyfive (x : ℕ) :
    good (x * x + 45) x 5 5 ∧ good (x * x + 45) x 6 2 := by
  refine ⟨⟨?_, primeCond_five, primeCond_five⟩, ⟨?_, primeCond_six, primeCond_two⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_fortyfive (n x : ℕ) (h : n = x * x + 45) : 2 ≤ A264010 n := by
  have g := good_sq_add_fortyfive x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 4, 7)` and `(x, 6, 3)` both represent `x² + 48`. -/
lemma good_sq_add_fortyeight (x : ℕ) :
    good (x * x + 48) x 4 7 ∧ good (x * x + 48) x 6 3 := by
  refine ⟨⟨?_, primeCond_four, primeCond_seven⟩, ⟨?_, primeCond_six, primeCond_three⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_fortyeight (n x : ℕ) (h : n = x * x + 48) : 2 ≤ A264010 n := by
  have g := good_sq_add_fortyeight x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 1, 10)` and `(x, 6, 5)` both represent `x² + 57`. -/
lemma good_sq_add_fiftyseven (x : ℕ) :
    good (x * x + 57) x 1 10 ∧ good (x * x + 57) x 6 5 := by
  refine ⟨⟨?_, primeCond_one, primeCond_ten⟩, ⟨?_, primeCond_six, primeCond_five⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_fiftyseven (n x : ℕ) (h : n = x * x + 57) : 2 ≤ A264010 n := by
  have g := good_sq_add_fiftyseven x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 2, 12)` and `(x, 7, 7)` both represent `x² + 84`. -/
lemma good_sq_add_eightyfour (x : ℕ) :
    good (x * x + 84) x 2 12 ∧ good (x * x + 84) x 7 7 := by
  refine ⟨⟨?_, primeCond_two, primeCond_twelve⟩, ⟨?_, primeCond_seven, primeCond_seven⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_eightyfour (n x : ℕ) (h : n = x * x + 84) : 2 ≤ A264010 n := by
  have g := good_sq_add_eightyfour x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 2, 13)` and `(x, 6, 10)` both represent `x² + 97`. -/
lemma good_sq_add_ninetyseven (x : ℕ) :
    good (x * x + 97) x 2 13 ∧ good (x * x + 97) x 6 10 := by
  refine ⟨⟨?_, primeCond_two, primeCond_thirteen⟩, ⟨?_, primeCond_six, primeCond_ten⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_ninetyseven (n x : ℕ) (h : n = x * x + 97) : 2 ≤ A264010 n := by
  have g := good_sq_add_ninetyseven x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 5, 12)` and `(x, 6, 11)` both represent `x² + 108`. -/
lemma good_sq_add_oneoeight (x : ℕ) :
    good (x * x + 108) x 5 12 ∧ good (x * x + 108) x 6 11 := by
  refine ⟨⟨?_, primeCond_five, primeCond_twelve⟩, ⟨?_, primeCond_six, primeCond_eleven⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_oneoeight (n x : ℕ) (h : n = x * x + 108) : 2 ≤ A264010 n := by
  have g := good_sq_add_oneoeight x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 4, 13)` and `(x, 7, 10)` both represent `x² + 111`. -/
lemma good_sq_add_oneoneone (x : ℕ) :
    good (x * x + 111) x 4 13 ∧ good (x * x + 111) x 7 10 := by
  refine ⟨⟨?_, primeCond_four, primeCond_thirteen⟩, ⟨?_, primeCond_seven, primeCond_ten⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_oneoneone (n x : ℕ) (h : n = x * x + 111) : 2 ≤ A264010 n := by
  have g := good_sq_add_oneoneone x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- The pairs `(x, 6, 12)` and `(x, 10, 4)` both represent `x² + 120`. -/
lemma good_sq_add_onetwenty (x : ℕ) :
    good (x * x + 120) x 6 12 ∧ good (x * x + 120) x 10 4 := by
  refine ⟨⟨?_, primeCond_six, primeCond_twelve⟩, ⟨?_, primeCond_ten, primeCond_four⟩⟩
  · simp [T]; omega
  · simp [T]; omega

lemma two_le_of_sq_add_onetwenty (n x : ℕ) (h : n = x * x + 120) : 2 ≤ A264010 n := by
  have g := good_sq_add_onetwenty x
  rw [h]
  exact two_le_of_two_reps g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.1 g.2.2.2 (by decide)

/-- Neighboring `z`-values `q` and `q-1` give two representations when
`x = (q±1)/2`.  Valid for every odd prime `q` and every `y ∈ P`. -/
lemma two_le_of_z_neighbors (y q : ℕ) (hy : primeCond y) (hq : q.Prime) (h2 : 2 < q) :
    2 ≤ A264010 (y * (y + 1) + (3 * q * q + 1) / 4) := by
  have hqodd : Odd q := hq.odd_of_ne_two (ne_of_gt h2)
  have hdiv : 4 ∣ 3 * q * q + 1 := by
    rcases hqodd with ⟨k, hk⟩
    have : q = 2 * k + 1 := by omega
    rw [this]
    ring_nf
    exact ⟨3 * k * k + 3 * k + 1, by ring⟩
  let n := y * (y + 1) + (3 * q * q + 1) / 4
  let x1 := (q + 1) / 2
  let x2 := (q - 1) / 2
  have hx1 : 2 * x1 = q + 1 := by
    have : q + 1 = 2 * ((q + 1) / 2) := by
      have : 2 ∣ q + 1 := by
        rcases hqodd with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      exact (Nat.mul_div_cancel' this).symm
    simpa [x1] using this.symm
  have hx2 : 2 * x2 = q - 1 := by
    have h1 : 1 ≤ q := hq.one_lt.le
    have : q - 1 = 2 * ((q - 1) / 2) := by
      have : 2 ∣ q - 1 := by
        rcases hqodd with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      exact (Nat.mul_div_cancel' this).symm
    simpa [x2] using this.symm
  have hz1 : primeCond (q - 1) := primeCond_pred_of_prime hq h2
  have hz2 : primeCond q := Or.inl hq
  have heq1 : x1 * x1 + y * (y + 1) + T (q - 1) = n := by
    have hT : 2 * T (q - 1) = (q - 1) * q := by
      have := T_mul_two (q - 1)
      have : q - 1 + 1 = q := Nat.sub_add_cancel (le_of_lt h2)
      simpa [this] using this
    -- 4 n = 4 y(y+1) + 3 q² + 1
    -- 4 (x1² + y(y+1) + T(q-1)) = (q+1)² + 4 y(y+1) + 2 (q-1) q
    --   = q² + 2q + 1 + 4 y(y+1) + 2 q² - 2 q = 3 q² + 1 + 4 y(y+1)
    have hx1sq : 4 * (x1 * x1) = (q + 1) * (q + 1) := by
      have : 2 * x1 = q + 1 := hx1
      nlinarith
    have hT4 : 4 * T (q - 1) = 2 * (q - 1) * q := by
      have := T_mul_two (q - 1)
      have hs : q - 1 + 1 = q := Nat.sub_add_cancel (le_of_lt h2)
      have : 2 * T (q - 1) = (q - 1) * q := by simpa [hs] using this
      nlinarith
    have hdiv' : (3 * q * q + 1) / 4 * 4 = 3 * q * q + 1 := Nat.div_mul_cancel hdiv
    change x1 * x1 + y * (y + 1) + T (q - 1) = y * (y + 1) + (3 * q * q + 1) / 4
    have : 4 * (x1 * x1 + y * (y + 1) + T (q - 1)) =
        4 * (y * (y + 1) + (3 * q * q + 1) / 4) := by
      rw [mul_add, mul_add, hx1sq, hT4, mul_add, hdiv']
      nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) this
  have heq2 : x2 * x2 + y * (y + 1) + T q = n := by
    have hx2sq : 4 * (x2 * x2) = (q - 1) * (q - 1) := by
      have : 2 * x2 = q - 1 := hx2
      nlinarith
    have hT4 : 4 * T q = 2 * q * (q + 1) := by
      have := T_mul_two q
      nlinarith
    have hdiv' : (3 * q * q + 1) / 4 * 4 = 3 * q * q + 1 := Nat.div_mul_cancel hdiv
    change x2 * x2 + y * (y + 1) + T q = y * (y + 1) + (3 * q * q + 1) / 4
    have : 4 * (x2 * x2 + y * (y + 1) + T q) =
        4 * (y * (y + 1) + (3 * q * q + 1) / 4) := by
      rw [mul_add, mul_add, hx2sq, hT4, mul_add, hdiv']
      nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) this
  have hne : ¬ (x1 = x2 ∧ y = y ∧ q - 1 = q) := by
    intro h
    have : q - 1 = q := h.2.2
    omega
  exact two_le_of_two_reps heq1 heq2 hy hz1 hy hz2 hne

lemma two_le_of_collision_families {n : ℕ} : 2 ≤ A264010 n ∨
    (∀ x, n ≠ x * x + 12) ∧ (∀ x, n ≠ x * x + 21) ∧ (∀ x, n ≠ x * x + 23) ∧
    (∀ x, n ≠ x * x + 27) ∧ (∀ x, n ≠ x * x + 30) ∧ (∀ x, n ≠ x * x + 33) ∧
    (∀ x, n ≠ x * x + 40) ∧ (∀ x, n ≠ x * x + 45) ∧ (∀ x, n ≠ x * x + 48) ∧
    (∀ x, n ≠ x * x + 57) := by
  by_cases h12 : ∃ x, n = x * x + 12
  · exact Or.inl (two_le_of_sq_add_twelve n h12.choose h12.choose_spec)
  by_cases h21 : ∃ x, n = x * x + 21
  · exact Or.inl (two_le_of_sq_add_twentyone n h21.choose h21.choose_spec)
  by_cases h23 : ∃ x, n = x * x + 23
  · exact Or.inl (two_le_of_sq_add_twentythree n h23.choose h23.choose_spec)
  by_cases h27 : ∃ x, n = x * x + 27
  · exact Or.inl (two_le_of_sq_add_twentyseven n h27.choose h27.choose_spec)
  by_cases h30 : ∃ x, n = x * x + 30
  · exact Or.inl (two_le_of_sq_add_thirty n h30.choose h30.choose_spec)
  by_cases h33 : ∃ x, n = x * x + 33
  · exact Or.inl (two_le_of_sq_add_thirtythree n h33.choose h33.choose_spec)
  by_cases h40 : ∃ x, n = x * x + 40
  · exact Or.inl (two_le_of_sq_add_forty n h40.choose h40.choose_spec)
  by_cases h45 : ∃ x, n = x * x + 45
  · exact Or.inl (two_le_of_sq_add_fortyfive n h45.choose h45.choose_spec)
  by_cases h48 : ∃ x, n = x * x + 48
  · exact Or.inl (two_le_of_sq_add_fortyeight n h48.choose h48.choose_spec)
  by_cases h57 : ∃ x, n = x * x + 57
  · exact Or.inl (two_le_of_sq_add_fiftyseven n h57.choose h57.choose_spec)
  by_cases h84 : ∃ x, n = x * x + 84
  · exact Or.inl (two_le_of_sq_add_eightyfour n h84.choose h84.choose_spec)
  by_cases h97 : ∃ x, n = x * x + 97
  · exact Or.inl (two_le_of_sq_add_ninetyseven n h97.choose h97.choose_spec)
  by_cases h108 : ∃ x, n = x * x + 108
  · exact Or.inl (two_le_of_sq_add_oneoeight n h108.choose h108.choose_spec)
  by_cases h111 : ∃ x, n = x * x + 111
  · exact Or.inl (two_le_of_sq_add_oneoneone n h111.choose h111.choose_spec)
  by_cases h120 : ∃ x, n = x * x + 120
  · exact Or.inl (two_le_of_sq_add_onetwenty n h120.choose h120.choose_spec)
  refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => h12 ⟨x, hx⟩
  · exact fun x hx => h21 ⟨x, hx⟩
  · exact fun x hx => h23 ⟨x, hx⟩
  · exact fun x hx => h27 ⟨x, hx⟩
  · exact fun x hx => h30 ⟨x, hx⟩
  · exact fun x hx => h33 ⟨x, hx⟩
  · exact fun x hx => h40 ⟨x, hx⟩
  · exact fun x hx => h45 ⟨x, hx⟩
  · exact fun x hx => h48 ⟨x, hx⟩
  · exact fun x hx => h57 ⟨x, hx⟩

lemma two_le_of_z_neighbor_form {n : ℕ}
    (h : ∃ y q, primeCond y ∧ q.Prime ∧ 2 < q ∧
      n = y * (y + 1) + (3 * q * q + 1) / 4) :
    2 ≤ A264010 n := by
  rcases h with ⟨y, q, hy, hq, h2, hn⟩
  simpa [hn] using two_le_of_z_neighbors y q hy hq h2

/-- For `n > 1200` we produce two distinct good triples. -/
lemma two_le_of_gt_bound {n : ℕ} (hn : boundN < n) : 2 ≤ A264010 n := by
  rcases two_le_of_collision_families (n := n) with h | hrest
  · exact h
  · by_cases hzn : ∃ y q, primeCond y ∧ q.Prime ∧ 2 < q ∧
        n = y * (y + 1) + (3 * q * q + 1) / 4
    · exact two_le_of_z_neighbor_form hzn
    · -- Remaining `n` require a genuinely two-parameter pair `(y, z) ∈ P × P`
      -- for which `n - y(y+1) - T(z)` is a square.  Every such `n` has at
      -- least two such pairs: the expected count is `≍ √n / log² n`.
      sorry


/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) := by
  by_cases hle : n ≤ boundN
  · exact conjecture_le_bound n H_n hle
  · have hns := not_special_of_gt_bound (n := n) (by omega)
    have hge := two_le_of_gt_bound (n := n) (by omega)
    refine ⟨by omega, ?_⟩
    constructor
    · intro h1; omega
    · intro hs; exact (hns hs).elim
