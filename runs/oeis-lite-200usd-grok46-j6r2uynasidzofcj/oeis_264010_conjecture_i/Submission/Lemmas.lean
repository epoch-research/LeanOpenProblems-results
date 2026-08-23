import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

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

def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime
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

lemma two_le_7 : 2 ≤ A264010 7 :=
  two_le_of_pcond (n := 7) (x1 := 2) (y1 := 1) (z1 := 1) (x2 := 0) (y2 := 2) (z2 := 1)
    (by decide) (by decide) (by rfl) (by rfl) (by rfl) (by rfl) (by decide)

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

def wits40 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
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
  (40,5,3,2,0,3,7) :: []

lemma wits40_ok : wits40.all checkW = true := by rfl

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

lemma two_le_of_wits40 {n : ℕ} (h : ∃ t ∈ wits40, t.1 = n) : 2 ≤ A264010 n := by
  rcases h with ⟨t, ht, rfl⟩
  exact all_checkW_two wits40 wits40_ok t ht

def specialB (n : ℕ) : Bool :=
  n == 3 || n == 4 || n == 5 || n == 6 || n == 10 || n == 11 ||
  n == 15 || n == 20 || n == 29 || n == 1125

lemma specialB_iff (n : ℕ) :
    specialB n = true ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
  simp [specialB, Finset.mem_insert, Finset.mem_singleton]
  omega

def covered40 : Bool :=
  (List.range 41).all fun n =>
    decide (n ≤ 2) || specialB n || wits40.any (fun t => t.1 == n)

lemma covered40_true : covered40 = true := by rfl

lemma List.any_eq_true_iff {α : Type*} (l : List α) (p : α → Bool) :
    l.any p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp [List.any_cons, ih, Bool.or_eq_true]

lemma covered40_spec (n : ℕ) (hn : n ≤ 40) :
    n ≤ 2 ∨ specialB n = true ∨ ∃ t ∈ wits40, t.1 = n := by
  have hn' : n < 41 := by omega
  have hmem : n ∈ List.range 41 := List.mem_range.mpr hn'
  have hbody := List.all_eq_true.mp covered40_true n hmem
  by_cases h1 : n ≤ 2
  · exact Or.inl h1
  · by_cases h2 : specialB n = true
    · exact Or.inr (Or.inl h2)
    · have h3 : wits40.any (fun t => t.1 == n) = true := by
        revert hbody
        simp [h1, h2, Bool.or_eq_true]
      refine Or.inr (Or.inr ?_)
      have : ∃ t ∈ wits40, (t.1 == n) = true := (List.any_eq_true_iff _ _).mp h3
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

lemma conjecture_le_40 (n : ℕ) (H_n : n > 2) (hle : n ≤ 40) :
    A264010 n > 0 ∧ (A264010 n = 1 ↔
      n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) := by
  have hc := covered40_spec n hle
  rcases hc with h | h | h
  · omega
  · have hs : n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) :=
      (specialB_iff n).mp h
    have heq := special_eq_one hs
    refine ⟨by omega, ?_⟩
    constructor
    · intro; exact hs
    · intro; exact heq
  · have hge := two_le_of_wits40 h
    have hnots : wits40.all (fun t => !specialB t.1) = true := by rfl
    have hns : n ∉ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
      intro hs
      rcases h with ⟨t, ht, rfl⟩
      have hf := List.all_eq_true.mp hnots t ht
      have hb : specialB t.1 = true := (specialB_iff t.1).mpr hs
      simp [hb] at hf
    refine ⟨by omega, ?_⟩
    constructor
    · intro heq
      omega
    · intro hs
      exact (hns hs).elim
