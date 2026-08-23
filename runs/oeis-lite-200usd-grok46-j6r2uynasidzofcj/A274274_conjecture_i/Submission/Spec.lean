import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
def A274274 (n : ℕ) : ℕ :=
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

/-- A natural number is a cube plus two squares. -/
def IsCubeTwoSquares (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), x ^ 3 + y ^ 2 + z ^ 2 = n

lemma le_self_pow_two (a : ℕ) : a ≤ a ^ 2 := by
  cases a with
  | zero => simp
  | succ a =>
    exact Nat.le_self_pow (by omega) _

lemma le_self_pow_three (a : ℕ) : a ≤ a ^ 3 := by
  cases a with
  | zero => simp
  | succ a =>
    exact Nat.le_self_pow (by omega) _

lemma mem_range_succ_of_le {a n : ℕ} (h : a ≤ n) : a ∈ range (succ n) := by
  rw [mem_range, succ_eq_add_one]
  omega

lemma A274274_ne_zero_of_rep {n x y z : ℕ}
    (hx : x ∈ range n.succ) (hy : y ∈ range n.succ) (hz : z ∈ range n.succ)
    (hrep : x ^ 3 + y ^ 2 + z ^ 2 = n) (hyz : y ≤ z) : A274274 n ≠ 0 := by
  let f : ℕ → ℕ := fun z => if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0
  have hf0 : ∀ i ∈ range n.succ, 0 ≤ f i := fun _ _ => Nat.zero_le _
  have hz1 : f z = 1 := by simp [f, hrep, hyz]
  have h1 : 1 ≤ ∑ z ∈ range n.succ, f z := by
    simpa [hz1] using single_le_sum hf0 hz
  let g : ℕ → ℕ := fun y => ∑ z ∈ range n.succ,
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0
  have hg0 : ∀ i ∈ range n.succ, 0 ≤ g i :=
    fun _ _ => sum_nonneg fun _ _ => Nat.zero_le _
  have hy1 : 1 ≤ g y := h1
  have h2 : 1 ≤ ∑ y ∈ range n.succ, g y :=
    le_trans hy1 (single_le_sum hg0 hy)
  let h : ℕ → ℕ := fun x => ∑ y ∈ range n.succ, ∑ z ∈ range n.succ,
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0
  have hh0 : ∀ i ∈ range n.succ, 0 ≤ h i :=
    fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => Nat.zero_le _
  have hx1 : 1 ≤ h x := h2
  have h3 : 1 ≤ ∑ x ∈ range n.succ, h x :=
    le_trans hx1 (single_le_sum hh0 hx)
  have heq : (∑ x ∈ range n.succ, h x) = A274274 n := rfl
  rw [heq] at h3
  exact Nat.ne_of_gt (Nat.lt_of_succ_le h3)

lemma A274274_eq_zero_of_not_rep {n : ℕ}
    (H : ∀ x ∈ range n.succ, ∀ y ∈ range n.succ, ∀ z ∈ range n.succ,
      ¬ (x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z)) : A274274 n = 0 := by
  refine sum_eq_zero fun x hx => sum_eq_zero fun y hy => sum_eq_zero fun z hz => ?_
  simp only [ite_eq_right_iff, one_ne_zero]
  exact H x hx y hy z hz

lemma A274274_pos_iff (n : ℕ) : A274274 n ≠ 0 ↔ IsCubeTwoSquares n := by
  constructor
  · intro h
    by_contra hnone
    apply h
    refine A274274_eq_zero_of_not_rep ?_
    intro x _hx y _hy z _hz ⟨hrep, _hyz⟩
    exact hnone ⟨x, y, z, hrep⟩
  · rintro ⟨x, y, z, hxyz⟩
    wlog hyz : y ≤ z generalizing y z
    · have h' : x ^ 3 + z ^ 2 + y ^ 2 = n := by linarith
      exact this z y h' (le_of_not_ge hyz)
    have hx3 : x ^ 3 ≤ n := by
      calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
        _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
        _ = n := hxyz
    have hy2 : y ^ 2 ≤ n := by
      calc y ^ 2 ≤ x ^ 3 + y ^ 2 := Nat.le_add_left _ _
        _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
        _ = n := hxyz
    have hz2 : z ^ 2 ≤ n := by
      calc z ^ 2 ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_left _ _
        _ = n := hxyz
    exact A274274_ne_zero_of_rep
      (mem_range_succ_of_le (le_trans (le_self_pow_three x) hx3))
      (mem_range_succ_of_le (le_trans (le_self_pow_two y) hy2))
      (mem_range_succ_of_le (le_trans (le_self_pow_two z) hz2))
      hxyz hyz

lemma IsCubeTwoSquares.of_two_sq {n y z : ℕ} (h : y ^ 2 + z ^ 2 = n) :
    IsCubeTwoSquares n :=
  ⟨0, y, z, by simp [h]⟩

lemma IsCubeTwoSquares.of_sq {n z : ℕ} (h : z ^ 2 = n) : IsCubeTwoSquares n :=
  ⟨0, 0, z, by simp [h]⟩

lemma IsCubeTwoSquares.of_cube {n x : ℕ} (h : x ^ 3 = n) : IsCubeTwoSquares n :=
  ⟨x, 0, 0, by simp [h]⟩

/-- Squares modulo 8 are 0, 1 or 4. -/
lemma sq_mod8 (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have : a ^ 2 % 8 = (a % 8) * (a % 8) % 8 := by
    rw [pow_two, Nat.mul_mod]
  have ha : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : a % 8 <;> simp [this, h]

/-- Numbers ≡ 3, 6 or 7 (mod 8) cannot be sums of two squares. -/
lemma not_two_sq_of_mod8 {n : ℕ} (h : n % 8 = 3 ∨ n % 8 = 6 ∨ n % 8 = 7) :
    ¬ ∃ y z : ℕ, y ^ 2 + z ^ 2 = n := by
  rintro ⟨y, z, rfl⟩
  have hy2 := sq_mod8 y
  have hz2 := sq_mod8 z
  have hsum : (y ^ 2 + z ^ 2) % 8 = (y ^ 2 % 8 + z ^ 2 % 8) % 8 := Nat.add_mod _ _ _
  rcases hy2 with hy2 | hy2 | hy2 <;> rcases hz2 with hz2 | hz2 | hz2 <;>
    simp [hsum, hy2, hz2] at h

/-- Two numbers both in {3,6,7} (mod 8) cannot differ by 2. -/
lemma not_both_hard_mod8_diff_two {a b : ℕ} (hab : a + 2 = b)
    (ha : a % 8 = 3 ∨ a % 8 = 6 ∨ a % 8 = 7)
    (hb : b % 8 = 3 ∨ b % 8 = 6 ∨ b % 8 = 7) : False := by
  have hb' : b % 8 = (a % 8 + 2) % 8 := by
    rw [← hab, Nat.add_mod]
  omega

/-- Two numbers both in {3,6,7} (mod 8) cannot differ by 6. -/
lemma not_both_hard_mod8_diff_six {a b : ℕ} (hab : a + 6 = b)
    (ha : a % 8 = 3 ∨ a % 8 = 6 ∨ a % 8 = 7)
    (hb : b % 8 = 3 ∨ b % 8 = 6 ∨ b % 8 = 7) : False := by
  have hb' : b % 8 = (a % 8 + 6) % 8 := by
    rw [← hab, Nat.add_mod]
  omega

lemma two_pow_add_two_mod8 (k : ℕ) : 2 ^ (k + 2) % 8 = 4 ∨ 2 ^ (k + 2) % 8 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
    rw [this, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

/-- Special-form numbers are never 3, 6 or 7 (mod 8). -/
lemma has_form_not_hard_mod8 {n : ℕ} (h : has_form_two_pow_k_times_four_m_plus_one n) :
    ¬ (n % 8 = 3 ∨ n % 8 = 6 ∨ n % 8 = 7) := by
  obtain ⟨k, m, rfl⟩ := h
  match k with
  | 0 =>
    have : (4 * m + 1) % 8 = 1 ∨ (4 * m + 1) % 8 = 5 := by omega
    omega
  | 1 =>
    have : (2 * (4 * m + 1)) % 8 = 2 := by omega
    omega
  | k + 2 =>
    have hpow := two_pow_add_two_mod8 k
    have hodd : (4 * m + 1) % 2 = 1 := by omega
    have hodd8 : (4 * m + 1) % 8 = 1 ∨ (4 * m + 1) % 8 = 5 := by omega
    have : (2 ^ (k + 2) * (4 * m + 1)) % 8 =
        ((2 ^ (k + 2) % 8) * ((4 * m + 1) % 8)) % 8 := Nat.mul_mod _ _ _
    rcases hpow with hpow | hpow <;> rcases hodd8 with hodd8 | hodd8 <;>
      simp [this, hpow, hodd8]

def IsHard (n : ℕ) : Prop := n % 8 = 3 ∨ n % 8 = 6 ∨ n % 8 = 7
def IsEasy (n : ℕ) : Prop := ¬ IsHard n

lemma IsEasy_iff (n : ℕ) : IsEasy n ↔ n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 5 := by
  unfold IsEasy IsHard
  omega

/-- A number with a prime p ≡ 3 (mod 4) to an odd valuation is not a sum of two squares. -/
lemma not_two_sq_of_odd_val {m p k : ℕ} [hp : Fact p.Prime]
    (h3 : p % 4 = 3) (hm : m ≠ 0)
    (hdvd : p ^ k ∣ m) (hnd : ¬ p ^ (k + 1) ∣ m) (hodd : Odd k) :
    ¬ ∃ y z : ℕ, m = y ^ 2 + z ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro H
  have hmem : p ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp.out, dvd_trans (dvd_pow_self p (by
      rintro rfl; exact Nat.not_odd_zero hodd)) hdvd, hm⟩
  have heven := H p hmem h3
  have hval : padicValNat p m = k := by
    have hle : k ≤ padicValNat p m :=
      (padicValNat_dvd_iff k m).mp hdvd |>.resolve_left hm
    have hgt : ¬ (k + 1 ≤ padicValNat p m) := by
      intro h
      have : p ^ (k + 1) ∣ m := (padicValNat_dvd_iff (k + 1) m).mpr (Or.inr h)
      exact hnd this
    omega
  rw [hval] at heven
  exact Nat.not_even_iff_odd.mpr hodd heven

-- Primality certificates
lemma prime_3 : Nat.Prime 3 := Nat.prime_three
lemma prime_7 : Nat.Prime 7 := Nat.prime_seven
lemma prime_11 : Nat.Prime 11 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 11 := Nat.le_sqrt.mp hms
  have : m ≤ 3 := by
    by_contra h
    have : 4 ≤ m := by omega
    have : 4 * 4 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_19 : Nat.Prime 19 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 19 := Nat.le_sqrt.mp hms
  have : m ≤ 4 := by
    by_contra h
    have : 5 ≤ m := by omega
    have : 5 * 5 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_23 : Nat.Prime 23 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 23 := Nat.le_sqrt.mp hms
  have : m ≤ 4 := by
    by_contra h
    have : 5 ≤ m := by omega
    have : 5 * 5 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_31 : Nat.Prime 31 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 31 := Nat.le_sqrt.mp hms
  have : m ≤ 5 := by
    by_contra h
    have : 6 ≤ m := by omega
    have : 6 * 6 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_43 : Nat.Prime 43 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 43 := Nat.le_sqrt.mp hms
  have : m ≤ 6 := by
    by_contra h
    have : 7 ≤ m := by omega
    have : 7 * 7 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_47 : Nat.Prime 47 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 47 := Nat.le_sqrt.mp hms
  have : m ≤ 6 := by
    by_contra h
    have : 7 ≤ m := by omega
    have : 7 * 7 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_59 : Nat.Prime 59 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 59 := Nat.le_sqrt.mp hms
  have : m ≤ 7 := by
    by_contra h
    have : 8 ≤ m := by omega
    have : 8 * 8 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_67 : Nat.Prime 67 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 67 := Nat.le_sqrt.mp hms
  have : m ≤ 8 := by
    by_contra h
    have : 9 ≤ m := by omega
    have : 9 * 9 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_71 : Nat.Prime 71 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 71 := Nat.le_sqrt.mp hms
  have : m ≤ 8 := by
    by_contra h
    have : 9 ≤ m := by omega
    have : 9 * 9 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_79 : Nat.Prime 79 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 79 := Nat.le_sqrt.mp hms
  have : m ≤ 8 := by
    by_contra h
    have : 9 ≤ m := by omega
    have : 9 * 9 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_83 : Nat.Prime 83 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 83 := Nat.le_sqrt.mp hms
  have : m ≤ 9 := by
    by_contra h
    have : 10 ≤ m := by omega
    have : 10 * 10 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_103 : Nat.Prime 103 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 103 := Nat.le_sqrt.mp hms
  have : m ≤ 10 := by
    by_contra h
    have : 11 ≤ m := by omega
    have : 11 * 11 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_107 : Nat.Prime 107 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 107 := Nat.le_sqrt.mp hms
  have : m ≤ 10 := by
    by_contra h
    have : 11 ≤ m := by omega
    have : 11 * 11 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_127 : Nat.Prime 127 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 127 := Nat.le_sqrt.mp hms
  have : m ≤ 11 := by
    by_contra h
    have : 12 ≤ m := by omega
    have : 12 * 12 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_131 : Nat.Prime 131 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 131 := Nat.le_sqrt.mp hms
  have : m ≤ 11 := by
    by_contra h
    have : 12 ≤ m := by omega
    have : 12 * 12 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_139 : Nat.Prime 139 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 139 := Nat.le_sqrt.mp hms
  have : m ≤ 11 := by
    by_contra h
    have : 12 ≤ m := by omega
    have : 12 * 12 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_167 : Nat.Prime 167 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 167 := Nat.le_sqrt.mp hms
  have : m ≤ 12 := by
    by_contra h
    have : 13 ≤ m := by omega
    have : 13 * 13 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_179 : Nat.Prime 179 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 179 := Nat.le_sqrt.mp hms
  have : m ≤ 13 := by
    by_contra h
    have : 14 ≤ m := by omega
    have : 14 * 14 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_211 : Nat.Prime 211 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 211 := Nat.le_sqrt.mp hms
  have : m ≤ 14 := by
    by_contra h
    have : 15 ≤ m := by omega
    have : 15 * 15 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_223 : Nat.Prime 223 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 223 := Nat.le_sqrt.mp hms
  have : m ≤ 14 := by
    by_contra h
    have : 15 ≤ m := by omega
    have : 15 * 15 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_227 : Nat.Prime 227 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 227 := Nat.le_sqrt.mp hms
  have : m ≤ 15 := by
    by_contra h
    have : 16 ≤ m := by omega
    have : 16 * 16 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_239 : Nat.Prime 239 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 239 := Nat.le_sqrt.mp hms
  have : m ≤ 15 := by
    by_contra h
    have : 16 ≤ m := by omega
    have : 16 * 16 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_251 : Nat.Prime 251 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 251 := Nat.le_sqrt.mp hms
  have : m ≤ 15 := by
    by_contra h
    have : 16 ≤ m := by omega
    have : 16 * 16 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_271 : Nat.Prime 271 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 271 := Nat.le_sqrt.mp hms
  have : m ≤ 16 := by
    by_contra h
    have : 17 ≤ m := by omega
    have : 17 * 17 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_283 : Nat.Prime 283 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 283 := Nat.le_sqrt.mp hms
  have : m ≤ 16 := by
    by_contra h
    have : 17 ≤ m := by omega
    have : 17 * 17 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_307 : Nat.Prime 307 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 307 := Nat.le_sqrt.mp hms
  have : m ≤ 17 := by
    by_contra h
    have : 18 ≤ m := by omega
    have : 18 * 18 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_311 : Nat.Prime 311 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 311 := Nat.le_sqrt.mp hms
  have : m ≤ 17 := by
    by_contra h
    have : 18 ≤ m := by omega
    have : 18 * 18 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_331 : Nat.Prime 331 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 331 := Nat.le_sqrt.mp hms
  have : m ≤ 18 := by
    by_contra h
    have : 19 ≤ m := by omega
    have : 19 * 19 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_347 : Nat.Prime 347 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 347 := Nat.le_sqrt.mp hms
  have : m ≤ 18 := by
    by_contra h
    have : 19 ≤ m := by omega
    have : 19 * 19 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_359 : Nat.Prime 359 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 359 := Nat.le_sqrt.mp hms
  have : m ≤ 18 := by
    by_contra h
    have : 19 ≤ m := by omega
    have : 19 * 19 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_383 : Nat.Prime 383 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 383 := Nat.le_sqrt.mp hms
  have : m ≤ 19 := by
    by_contra h
    have : 20 ≤ m := by omega
    have : 20 * 20 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_431 : Nat.Prime 431 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 431 := Nat.le_sqrt.mp hms
  have : m ≤ 20 := by
    by_contra h
    have : 21 ≤ m := by omega
    have : 21 * 21 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_491 : Nat.Prime 491 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 491 := Nat.le_sqrt.mp hms
  have : m ≤ 22 := by
    by_contra h
    have : 23 ≤ m := by omega
    have : 23 * 23 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_499 : Nat.Prime 499 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 499 := Nat.le_sqrt.mp hms
  have : m ≤ 22 := by
    by_contra h
    have : 23 ≤ m := by omega
    have : 23 * 23 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_503 : Nat.Prime 503 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 503 := Nat.le_sqrt.mp hms
  have : m ≤ 22 := by
    by_contra h
    have : 23 ≤ m := by omega
    have : 23 * 23 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_599 : Nat.Prime 599 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 599 := Nat.le_sqrt.mp hms
  have : m ≤ 24 := by
    by_contra h
    have : 25 ≤ m := by omega
    have : 25 * 25 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_631 : Nat.Prime 631 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 631 := Nat.le_sqrt.mp hms
  have : m ≤ 25 := by
    by_contra h
    have : 26 ≤ m := by omega
    have : 26 * 26 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_719 : Nat.Prime 719 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 719 := Nat.le_sqrt.mp hms
  have : m ≤ 26 := by
    by_contra h
    have : 27 ≤ m := by omega
    have : 27 * 27 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_727 : Nat.Prime 727 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 727 := Nat.le_sqrt.mp hms
  have : m ≤ 26 := by
    by_contra h
    have : 27 ≤ m := by omega
    have : 27 * 27 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_739 : Nat.Prime 739 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 739 := Nat.le_sqrt.mp hms
  have : m ≤ 27 := by
    by_contra h
    have : 28 ≤ m := by omega
    have : 28 * 28 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_751 : Nat.Prime 751 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 751 := Nat.le_sqrt.mp hms
  have : m ≤ 27 := by
    by_contra h
    have : 28 ≤ m := by omega
    have : 28 * 28 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_883 : Nat.Prime 883 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 883 := Nat.le_sqrt.mp hms
  have : m ≤ 29 := by
    by_contra h
    have : 30 ≤ m := by omega
    have : 30 * 30 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_911 : Nat.Prime 911 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 911 := Nat.le_sqrt.mp hms
  have : m ≤ 30 := by
    by_contra h
    have : 31 ≤ m := by omega
    have : 31 * 31 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_919 : Nat.Prime 919 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 919 := Nat.le_sqrt.mp hms
  have : m ≤ 30 := by
    by_contra h
    have : 31 ≤ m := by omega
    have : 31 * 31 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_991 : Nat.Prime 991 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 991 := Nat.le_sqrt.mp hms
  have : m ≤ 31 := by
    by_contra h
    have : 32 ≤ m := by omega
    have : 32 * 32 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1051 : Nat.Prime 1051 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1051 := Nat.le_sqrt.mp hms
  have : m ≤ 32 := by
    by_contra h
    have : 33 ≤ m := by omega
    have : 33 * 33 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1123 : Nat.Prime 1123 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1123 := Nat.le_sqrt.mp hms
  have : m ≤ 33 := by
    by_contra h
    have : 34 ≤ m := by omega
    have : 34 * 34 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1259 : Nat.Prime 1259 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1259 := Nat.le_sqrt.mp hms
  have : m ≤ 35 := by
    by_contra h
    have : 36 ≤ m := by omega
    have : 36 * 36 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1303 : Nat.Prime 1303 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1303 := Nat.le_sqrt.mp hms
  have : m ≤ 36 := by
    by_contra h
    have : 37 ≤ m := by omega
    have : 37 * 37 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1319 : Nat.Prime 1319 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1319 := Nat.le_sqrt.mp hms
  have : m ≤ 36 := by
    by_contra h
    have : 37 ≤ m := by omega
    have : 37 * 37 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1451 : Nat.Prime 1451 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1451 := Nat.le_sqrt.mp hms
  have : m ≤ 38 := by
    by_contra h
    have : 39 ≤ m := by omega
    have : 39 * 39 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1627 : Nat.Prime 1627 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1627 := Nat.le_sqrt.mp hms
  have : m ≤ 40 := by
    by_contra h
    have : 41 ≤ m := by omega
    have : 41 * 41 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1951 : Nat.Prime 1951 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1951 := Nat.le_sqrt.mp hms
  have : m ≤ 44 := by
    by_contra h
    have : 45 ≤ m := by omega
    have : 45 * 45 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_1987 : Nat.Prime 1987 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 1987 := Nat.le_sqrt.mp hms
  have : m ≤ 44 := by
    by_contra h
    have : 45 ≤ m := by omega
    have : 45 * 45 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2011 : Nat.Prime 2011 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2011 := Nat.le_sqrt.mp hms
  have : m ≤ 44 := by
    by_contra h
    have : 45 ≤ m := by omega
    have : 45 * 45 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2083 : Nat.Prime 2083 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2083 := Nat.le_sqrt.mp hms
  have : m ≤ 45 := by
    by_contra h
    have : 46 ≤ m := by omega
    have : 46 * 46 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2087 : Nat.Prime 2087 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2087 := Nat.le_sqrt.mp hms
  have : m ≤ 45 := by
    by_contra h
    have : 46 ≤ m := by omega
    have : 46 * 46 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2207 : Nat.Prime 2207 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2207 := Nat.le_sqrt.mp hms
  have : m ≤ 46 := by
    by_contra h
    have : 47 ≤ m := by omega
    have : 47 * 47 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2239 : Nat.Prime 2239 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2239 := Nat.le_sqrt.mp hms
  have : m ≤ 47 := by
    by_contra h
    have : 48 ≤ m := by omega
    have : 48 * 48 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_2999 : Nat.Prime 2999 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 2999 := Nat.le_sqrt.mp hms
  have : m ≤ 54 := by
    by_contra h
    have : 55 ≤ m := by omega
    have : 55 * 55 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_3299 : Nat.Prime 3299 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 3299 := Nat.le_sqrt.mp hms
  have : m ≤ 57 := by
    by_contra h
    have : 58 ≤ m := by omega
    have : 58 * 58 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_3691 : Nat.Prime 3691 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 3691 := Nat.le_sqrt.mp hms
  have : m ≤ 60 := by
    by_contra h
    have : 61 ≤ m := by omega
    have : 61 * 61 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_5147 : Nat.Prime 5147 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 5147 := Nat.le_sqrt.mp hms
  have : m ≤ 71 := by
    by_contra h
    have : 72 ≤ m := by omega
    have : 72 * 72 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_5743 : Nat.Prime 5743 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 5743 := Nat.le_sqrt.mp hms
  have : m ≤ 75 := by
    by_contra h
    have : 76 ≤ m := by omega
    have : 76 * 76 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_6911 : Nat.Prime 6911 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 6911 := Nat.le_sqrt.mp hms
  have : m ≤ 83 := by
    by_contra h
    have : 84 ≤ m := by omega
    have : 84 * 84 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_11699 : Nat.Prime 11699 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 11699 := Nat.le_sqrt.mp hms
  have : m ≤ 108 := by
    by_contra h
    have : 109 ≤ m := by omega
    have : 109 * 109 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_13883 : Nat.Prime 13883 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 13883 := Nat.le_sqrt.mp hms
  have : m ≤ 117 := by
    by_contra h
    have : 118 ≤ m := by omega
    have : 118 * 118 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_15731 : Nat.Prime 15731 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 15731 := Nat.le_sqrt.mp hms
  have : m ≤ 125 := by
    by_contra h
    have : 126 ≤ m := by omega
    have : 126 * 126 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_19543 : Nat.Prime 19543 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 19543 := Nat.le_sqrt.mp hms
  have : m ≤ 139 := by
    by_contra h
    have : 140 ≤ m := by omega
    have : 140 * 140 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_32359 : Nat.Prime 32359 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 32359 := Nat.le_sqrt.mp hms
  have : m ≤ 179 := by
    by_contra h
    have : 180 ≤ m := by omega
    have : 180 * 180 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_34267 : Nat.Prime 34267 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 34267 := Nat.le_sqrt.mp hms
  have : m ≤ 185 := by
    by_contra h
    have : 186 ≤ m := by omega
    have : 186 * 186 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num
lemma prime_38723 : Nat.Prime 38723 := by
  refine Nat.prime_def_le_sqrt.mpr ⟨by norm_num, ?_⟩
  intro m hm2 hms
  have hmm : m * m ≤ 38723 := Nat.le_sqrt.mp hms
  have : m ≤ 196 := by
    by_contra h
    have : 197 ≤ m := by omega
    have : 197 * 197 ≤ m * m := Nat.mul_le_mul this this
    omega
  interval_cases m <;> norm_num

-- Neighborhood representations
lemma rep_114 : IsCubeTwoSquares 114 := ⟨1, 7, 8, by norm_num⟩
lemma rep_118 : IsCubeTwoSquares 118 := ⟨1, 6, 9, by norm_num⟩
lemma rep_122 : IsCubeTwoSquares 122 := ⟨0, 1, 11, by norm_num⟩
lemma rep_126 : IsCubeTwoSquares 126 := ⟨1, 2, 11, by norm_num⟩
lemma rep_306 : IsCubeTwoSquares 306 := ⟨0, 9, 15, by norm_num⟩
lemma rep_310 : IsCubeTwoSquares 310 := ⟨5, 4, 13, by norm_num⟩
lemma rep_314 : IsCubeTwoSquares 314 := ⟨0, 5, 17, by norm_num⟩
lemma rep_318 : IsCubeTwoSquares 318 := ⟨1, 11, 14, by norm_num⟩
lemma rep_807 : IsCubeTwoSquares 807 := ⟨7, 8, 20, by norm_num⟩
lemma rep_811 : IsCubeTwoSquares 811 := ⟨1, 9, 27, by norm_num⟩
lemma rep_815 : IsCubeTwoSquares 815 := ⟨3, 2, 28, by norm_num⟩
lemma rep_819 : IsCubeTwoSquares 819 := ⟨1, 17, 23, by norm_num⟩
lemma rep_2130 : IsCubeTwoSquares 2130 := ⟨1, 23, 40, by norm_num⟩
lemma rep_2134 : IsCubeTwoSquares 2134 := ⟨5, 28, 35, by norm_num⟩
lemma rep_2138 : IsCubeTwoSquares 2138 := ⟨0, 17, 43, by norm_num⟩
lemma rep_2142 : IsCubeTwoSquares 2142 := ⟨1, 5, 46, by norm_num⟩
lemma rep_2674 : IsCubeTwoSquares 2674 := ⟨4, 3, 51, by norm_num⟩
lemma rep_2678 : IsCubeTwoSquares 2678 := ⟨1, 34, 39, by norm_num⟩
lemma rep_2682 : IsCubeTwoSquares 2682 := ⟨0, 9, 51, by norm_num⟩
lemma rep_2686 : IsCubeTwoSquares 2686 := ⟨5, 25, 44, by norm_num⟩
lemma rep_3218 : IsCubeTwoSquares 3218 := ⟨0, 37, 43, by norm_num⟩
lemma rep_3222 : IsCubeTwoSquares 3222 := ⟨1, 14, 55, by norm_num⟩
lemma rep_3226 : IsCubeTwoSquares 3226 := ⟨0, 25, 51, by norm_num⟩
lemma rep_3230 : IsCubeTwoSquares 3230 := ⟨1, 27, 50, by norm_num⟩
lemma rep_4398 : IsCubeTwoSquares 4398 := ⟨1, 26, 61, by norm_num⟩
lemma rep_4402 : IsCubeTwoSquares 4402 := ⟨2, 13, 65, by norm_num⟩
lemma rep_4406 : IsCubeTwoSquares 4406 := ⟨1, 7, 66, by norm_num⟩
lemma rep_4410 : IsCubeTwoSquares 4410 := ⟨0, 21, 63, by norm_num⟩
lemma rep_5334 : IsCubeTwoSquares 5334 := ⟨1, 2, 73, by norm_num⟩
lemma rep_5338 : IsCubeTwoSquares 5338 := ⟨0, 3, 73, by norm_num⟩
lemma rep_5342 : IsCubeTwoSquares 5342 := ⟨1, 21, 70, by norm_num⟩
lemma rep_5346 : IsCubeTwoSquares 5346 := ⟨1, 4, 73, by norm_num⟩
lemma rep_6414 : IsCubeTwoSquares 6414 := ⟨1, 22, 77, by norm_num⟩
lemma rep_6418 : IsCubeTwoSquares 6418 := ⟨0, 33, 73, by norm_num⟩
lemma rep_6422 : IsCubeTwoSquares 6422 := ⟨1, 39, 70, by norm_num⟩
lemma rep_6426 : IsCubeTwoSquares 6426 := ⟨1, 5, 80, by norm_num⟩
lemma rep_10054 : IsCubeTwoSquares 10054 := ⟨1, 63, 78, by norm_num⟩
lemma rep_10058 : IsCubeTwoSquares 10058 := ⟨1, 16, 99, by norm_num⟩
lemma rep_10062 : IsCubeTwoSquares 10062 := ⟨1, 35, 94, by norm_num⟩
lemma rep_10066 : IsCubeTwoSquares 10066 := ⟨5, 70, 71, by norm_num⟩
lemma rep_11314 : IsCubeTwoSquares 11314 := ⟨0, 17, 105, by norm_num⟩
lemma rep_11318 : IsCubeTwoSquares 11318 := ⟨1, 9, 106, by norm_num⟩
lemma rep_11322 : IsCubeTwoSquares 11322 := ⟨0, 39, 99, by norm_num⟩
lemma rep_11326 : IsCubeTwoSquares 11326 := ⟨9, 66, 79, by norm_num⟩
lemma rep_11818 : IsCubeTwoSquares 11818 := ⟨1, 51, 96, by norm_num⟩
lemma rep_11822 : IsCubeTwoSquares 11822 := ⟨1, 61, 90, by norm_num⟩
lemma rep_11826 : IsCubeTwoSquares 11826 := ⟨0, 45, 99, by norm_num⟩
lemma rep_11830 : IsCubeTwoSquares 11830 := ⟨5, 16, 107, by norm_num⟩
lemma rep_14002 : IsCubeTwoSquares 14002 := ⟨0, 41, 111, by norm_num⟩
lemma rep_14006 : IsCubeTwoSquares 14006 := ⟨1, 9, 118, by norm_num⟩
lemma rep_14010 : IsCubeTwoSquares 14010 := ⟨1, 28, 115, by norm_num⟩
lemma rep_14014 : IsCubeTwoSquares 14014 := ⟨1, 18, 117, by norm_num⟩
lemma rep_15850 : IsCubeTwoSquares 15850 := ⟨0, 15, 125, by norm_num⟩
lemma rep_15854 : IsCubeTwoSquares 15854 := ⟨9, 22, 121, by norm_num⟩
lemma rep_15858 : IsCubeTwoSquares 15858 := ⟨0, 27, 123, by norm_num⟩
lemma rep_15862 : IsCubeTwoSquares 15862 := ⟨5, 19, 124, by norm_num⟩
lemma rep_26538 : IsCubeTwoSquares 26538 := ⟨5, 13, 162, by norm_num⟩
lemma rep_26542 : IsCubeTwoSquares 26542 := ⟨5, 89, 136, by norm_num⟩
lemma rep_26546 : IsCubeTwoSquares 26546 := ⟨0, 25, 161, by norm_num⟩
lemma rep_26550 : IsCubeTwoSquares 26550 := ⟨21, 60, 117, by norm_num⟩
lemma rep_28798 : IsCubeTwoSquares 28798 := ⟨5, 28, 167, by norm_num⟩
lemma rep_28802 : IsCubeTwoSquares 28802 := ⟨0, 119, 121, by norm_num⟩
lemma rep_28806 : IsCubeTwoSquares 28806 := ⟨17, 22, 153, by norm_num⟩
lemma rep_28810 : IsCubeTwoSquares 28810 := ⟨2, 119, 121, by norm_num⟩
lemma rep_34386 : IsCubeTwoSquares 34386 := ⟨1, 23, 184, by norm_num⟩
lemma rep_34390 : IsCubeTwoSquares 34390 := ⟨1, 30, 183, by norm_num⟩
lemma rep_34394 : IsCubeTwoSquares 34394 := ⟨0, 13, 185, by norm_num⟩
lemma rep_34398 : IsCubeTwoSquares 34398 := ⟨5, 28, 183, by norm_num⟩
lemma rep_47978 : IsCubeTwoSquares 47978 := ⟨1, 4, 219, by norm_num⟩
lemma rep_47982 : IsCubeTwoSquares 47982 := ⟨1, 109, 190, by norm_num⟩
lemma rep_47986 : IsCubeTwoSquares 47986 := ⟨0, 5, 219, by norm_num⟩
lemma rep_47990 : IsCubeTwoSquares 47990 := ⟨1, 30, 217, by norm_num⟩
lemma rep_0 : IsCubeTwoSquares 0 := ⟨0, 0, 0, by norm_num⟩
lemma rep_1 : IsCubeTwoSquares 1 := ⟨0, 0, 1, by norm_num⟩
lemma rep_2 : IsCubeTwoSquares 2 := ⟨0, 1, 1, by norm_num⟩
lemma rep_4 : IsCubeTwoSquares 4 := ⟨0, 0, 2, by norm_num⟩
lemma rep_5 : IsCubeTwoSquares 5 := ⟨0, 1, 2, by norm_num⟩
lemma rep_8 : IsCubeTwoSquares 8 := ⟨0, 2, 2, by norm_num⟩
lemma rep_9 : IsCubeTwoSquares 9 := ⟨0, 0, 3, by norm_num⟩
lemma rep_10 : IsCubeTwoSquares 10 := ⟨0, 1, 3, by norm_num⟩
lemma rep_12 : IsCubeTwoSquares 12 := ⟨2, 0, 2, by norm_num⟩
lemma rep_13 : IsCubeTwoSquares 13 := ⟨0, 2, 3, by norm_num⟩
lemma rep_16 : IsCubeTwoSquares 16 := ⟨0, 0, 4, by norm_num⟩
lemma rep_17 : IsCubeTwoSquares 17 := ⟨0, 1, 4, by norm_num⟩
lemma rep_18 : IsCubeTwoSquares 18 := ⟨0, 3, 3, by norm_num⟩

-- The 18 easy zeros
lemma not_rep_120 : ¬ IsCubeTwoSquares 120 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 120 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 120 := h
  have hx : x ≤ 4 := by
    by_contra hx
    have : 5 ≤ x := by omega
    have : 5 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 5 ^ 3 ≤ 120 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 120, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 120 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 120 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 119, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 119 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 119 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 112, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 112 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 112 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 93, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 93 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 93 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 56, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 56 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 56 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_312 : ¬ IsCubeTwoSquares 312 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 312 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 312 := h
  have hx : x ≤ 6 := by
    by_contra hx
    have : 7 ≤ x := by omega
    have : 7 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 7 ^ 3 ≤ 312 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 312, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 312 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 312 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 311, blocked by 311^1
    have hr : y ^ 2 + z ^ 2 = 311 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 311) := ⟨prime_311⟩
    have : ¬ ∃ y z : ℕ, 311 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 311) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 304, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 304 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 304 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 285, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 285 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 285 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 248, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 248 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 248 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 187, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 187 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 187 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 96, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 96 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 96 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_813 : ¬ IsCubeTwoSquares 813 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 813 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 813 := h
  have hx : x ≤ 9 := by
    by_contra hx
    have : 10 ≤ x := by omega
    have : 10 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 10 ^ 3 ≤ 813 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 813, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 813 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 813 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 812, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 812 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 812 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 805, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 805 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 805 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 786, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 786 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 786 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 749, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 749 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 749 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 688, blocked by 43^1
    have hr : y ^ 2 + z ^ 2 = 688 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 43) := ⟨prime_43⟩
    have : ¬ ∃ y z : ℕ, 688 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 43) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 597, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 597 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 597 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 470, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 470 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 470 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 301, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 301 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 301 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 84, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 84 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 84 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_2136 : ¬ IsCubeTwoSquares 2136 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 2136 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 2136 := h
  have hx : x ≤ 12 := by
    by_contra hx
    have : 13 ≤ x := by omega
    have : 13 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 13 ^ 3 ≤ 2136 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 2136, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2136 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2136 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 2135, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2135 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2135 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 2128, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2128 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2128 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 2109, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2109 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2109 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 2072, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2072 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2072 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 2011, blocked by 2011^1
    have hr : y ^ 2 + z ^ 2 = 2011 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 2011) := ⟨prime_2011⟩
    have : ¬ ∃ y z : ℕ, 2011 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2011) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 1920, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1920 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1920 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 1793, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 1793 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 1793 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 1624, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 1624 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 1624 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 1407, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1407 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1407 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 1136, blocked by 71^1
    have hr : y ^ 2 + z ^ 2 = 1136 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 71) := ⟨prime_71⟩
    have : ¬ ∃ y z : ℕ, 1136 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 71) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 805, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 805 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 805 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 408, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 408 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 408 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_2680 : ¬ IsCubeTwoSquares 2680 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 2680 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 2680 := h
  have hx : x ≤ 13 := by
    by_contra hx
    have : 14 ≤ x := by omega
    have : 14 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 14 ^ 3 ≤ 2680 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 2680, blocked by 67^1
    have hr : y ^ 2 + z ^ 2 = 2680 := by
      simpa using h
    haveI : Fact (Nat.Prime 67) := ⟨prime_67⟩
    have : ¬ ∃ y z : ℕ, 2680 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 67) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 2679, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2679 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2679 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 2672, blocked by 167^1
    have hr : y ^ 2 + z ^ 2 = 2672 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 167) := ⟨prime_167⟩
    have : ¬ ∃ y z : ℕ, 2672 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 167) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 2653, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2653 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2653 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 2616, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2616 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2616 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 2555, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2555 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2555 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 2464, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2464 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2464 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 2337, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2337 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2337 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 2168, blocked by 271^1
    have hr : y ^ 2 + z ^ 2 = 2168 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 271) := ⟨prime_271⟩
    have : ¬ ∃ y z : ℕ, 2168 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 271) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 1951, blocked by 1951^1
    have hr : y ^ 2 + z ^ 2 = 1951 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1951) := ⟨prime_1951⟩
    have : ¬ ∃ y z : ℕ, 1951 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1951) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 1680, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1680 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1680 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 1349, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 1349 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 1349 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 952, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 952 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 952 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 483, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 483 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 483 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_3224 : ¬ IsCubeTwoSquares 3224 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 3224 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 3224 := h
  have hx : x ≤ 14 := by
    by_contra hx
    have : 15 ≤ x := by omega
    have : 15 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 15 ^ 3 ≤ 3224 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 3224, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 3224 := by
      simpa using h
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 3224 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 3223, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 3223 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 3223 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 3216, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3216 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3216 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 3197, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 3197 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 3197 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 3160, blocked by 79^1
    have hr : y ^ 2 + z ^ 2 = 3160 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 79) := ⟨prime_79⟩
    have : ¬ ∃ y z : ℕ, 3160 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 79) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 3099, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3099 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3099 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 3008, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 3008 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 3008 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 2881, blocked by 43^1
    have hr : y ^ 2 + z ^ 2 = 2881 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 43) := ⟨prime_43⟩
    have : ¬ ∃ y z : ℕ, 2881 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 43) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 2712, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2712 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2712 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 2495, blocked by 499^1
    have hr : y ^ 2 + z ^ 2 = 2495 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 499) := ⟨prime_499⟩
    have : ¬ ∃ y z : ℕ, 2495 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 499) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 2224, blocked by 139^1
    have hr : y ^ 2 + z ^ 2 = 2224 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 139) := ⟨prime_139⟩
    have : ¬ ∃ y z : ℕ, 2224 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 139) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 1893, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1893 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1893 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 1496, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 1496 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 1496 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 1027, blocked by 79^1
    have hr : y ^ 2 + z ^ 2 = 1027 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 79) := ⟨prime_79⟩
    have : ¬ ∃ y z : ℕ, 1027 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 79) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 480, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 480 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 480 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_4404 : ¬ IsCubeTwoSquares 4404 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 4404 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 4404 := h
  have hx : x ≤ 16 := by
    by_contra hx
    have : 17 ≤ x := by omega
    have : 17 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 17 ^ 3 ≤ 4404 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 4404, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4404 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4404 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 4403, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4403 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4403 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 4396, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4396 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4396 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 4377, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4377 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4377 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 4340, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4340 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4340 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 4279, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 4279 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 4279 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 4188, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4188 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4188 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 4061, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 4061 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 4061 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 3892, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 3892 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 3892 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 3675, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3675 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3675 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 3404, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 3404 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 3404 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 3073, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 3073 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 3073 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 2676, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 2676 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 2676 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 2207, blocked by 2207^1
    have hr : y ^ 2 + z ^ 2 = 2207 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 2207) := ⟨prime_2207⟩
    have : ¬ ∃ y z : ℕ, 2207 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2207) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 1660, blocked by 83^1
    have hr : y ^ 2 + z ^ 2 = 1660 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 83) := ⟨prime_83⟩
    have : ¬ ∃ y z : ℕ, 1660 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 83) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 1029, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1029 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1029 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 308, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 308 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 308 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_5340 : ¬ IsCubeTwoSquares 5340 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 5340 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 5340 := h
  have hx : x ≤ 17 := by
    by_contra hx
    have : 18 ≤ x := by omega
    have : 18 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 18 ^ 3 ≤ 5340 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 5340, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5340 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5340 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 5339, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 5339 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 5339 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 5332, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 5332 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 5332 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 5313, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5313 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5313 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 5276, blocked by 1319^1
    have hr : y ^ 2 + z ^ 2 = 5276 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1319) := ⟨prime_1319⟩
    have : ¬ ∃ y z : ℕ, 5276 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1319) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 5215, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 5215 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 5215 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 5124, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5124 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5124 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 4997, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 4997 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 4997 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 4828, blocked by 71^1
    have hr : y ^ 2 + z ^ 2 = 4828 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 71) := ⟨prime_71⟩
    have : ¬ ∃ y z : ℕ, 4828 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 71) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 4611, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4611 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4611 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 4340, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4340 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4340 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 4009, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 4009 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 4009 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 3612, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3612 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3612 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 3143, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 3143 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 3143 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 2596, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 2596 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 2596 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 1965, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1965 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1965 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 1244, blocked by 311^1
    have hr : y ^ 2 + z ^ 2 = 1244 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 311) := ⟨prime_311⟩
    have : ¬ ∃ y z : ℕ, 1244 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 311) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 427, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 427 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 427 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_6420 : ¬ IsCubeTwoSquares 6420 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 6420 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 6420 := h
  have hx : x ≤ 18 := by
    by_contra hx
    have : 19 ≤ x := by omega
    have : 19 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 19 ^ 3 ≤ 6420 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 6420, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 6420 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 6420 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 6419, blocked by 131^1
    have hr : y ^ 2 + z ^ 2 = 6419 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 131) := ⟨prime_131⟩
    have : ¬ ∃ y z : ℕ, 6419 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 131) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 6412, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 6412 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 6412 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 6393, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 6393 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 6393 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 6356, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 6356 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 6356 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 6295, blocked by 1259^1
    have hr : y ^ 2 + z ^ 2 = 6295 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1259) := ⟨prime_1259⟩
    have : ¬ ∃ y z : ℕ, 6295 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1259) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 6204, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 6204 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 6204 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 6077, blocked by 59^1
    have hr : y ^ 2 + z ^ 2 = 6077 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 59) := ⟨prime_59⟩
    have : ¬ ∃ y z : ℕ, 6077 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 59) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 5908, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 5908 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 5908 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 5691, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5691 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5691 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 5420, blocked by 271^1
    have hr : y ^ 2 + z ^ 2 = 5420 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 271) := ⟨prime_271⟩
    have : ¬ ∃ y z : ℕ, 5420 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 271) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 5089, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 5089 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 5089 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 4692, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4692 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4692 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 4223, blocked by 103^1
    have hr : y ^ 2 + z ^ 2 = 4223 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 103) := ⟨prime_103⟩
    have : ¬ ∃ y z : ℕ, 4223 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 103) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 3676, blocked by 919^1
    have hr : y ^ 2 + z ^ 2 = 3676 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 919) := ⟨prime_919⟩
    have : ¬ ∃ y z : ℕ, 3676 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 919) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 3045, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3045 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3045 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 2324, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 2324 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 2324 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 1507, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 1507 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 1507 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 588, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 588 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 588 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_10060 : ¬ IsCubeTwoSquares 10060 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 10060 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 10060 := h
  have hx : x ≤ 21 := by
    by_contra hx
    have : 22 ≤ x := by omega
    have : 22 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 22 ^ 3 ≤ 10060 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 10060, blocked by 503^1
    have hr : y ^ 2 + z ^ 2 = 10060 := by
      simpa using h
    haveI : Fact (Nat.Prime 503) := ⟨prime_503⟩
    have : ¬ ∃ y z : ℕ, 10060 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 503) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 10059, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 10059 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 10059 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 10052, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10052 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10052 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 10033, blocked by 79^1
    have hr : y ^ 2 + z ^ 2 = 10033 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 79) := ⟨prime_79⟩
    have : ¬ ∃ y z : ℕ, 10033 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 79) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 9996, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9996 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9996 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 9935, blocked by 1987^1
    have hr : y ^ 2 + z ^ 2 = 9935 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1987) := ⟨prime_1987⟩
    have : ¬ ∃ y z : ℕ, 9935 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1987) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 9844, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 9844 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 9844 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 9717, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9717 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9717 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 9548, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 9548 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 9548 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 9331, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 9331 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 9331 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 9060, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9060 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9060 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 8729, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 8729 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 8729 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 8332, blocked by 2083^1
    have hr : y ^ 2 + z ^ 2 = 8332 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 2083) := ⟨prime_2083⟩
    have : ¬ ∃ y z : ℕ, 8332 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2083) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 7863, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 7863 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 7863 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 7316, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 7316 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 7316 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 6685, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 6685 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 6685 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 5964, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5964 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5964 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 5147, blocked by 5147^1
    have hr : y ^ 2 + z ^ 2 = 5147 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 5147) := ⟨prime_5147⟩
    have : ¬ ∃ y z : ℕ, 5147 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 5147) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 4228, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4228 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4228 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 3201, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3201 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3201 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 2060, blocked by 103^1
    have hr : y ^ 2 + z ^ 2 = 2060 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 103) := ⟨prime_103⟩
    have : ¬ ∃ y z : ℕ, 2060 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 103) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 799, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 799 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 799 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_11320 : ¬ IsCubeTwoSquares 11320 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 11320 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 11320 := h
  have hx : x ≤ 22 := by
    by_contra hx
    have : 23 ≤ x := by omega
    have : 23 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 23 ^ 3 ≤ 11320 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 11320, blocked by 283^1
    have hr : y ^ 2 + z ^ 2 = 11320 := by
      simpa using h
    haveI : Fact (Nat.Prime 283) := ⟨prime_283⟩
    have : ¬ ∃ y z : ℕ, 11320 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 283) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 11319, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11319 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11319 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 11312, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 11312 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 11312 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 11293, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 11293 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 11293 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 11256, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11256 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11256 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 11195, blocked by 2239^1
    have hr : y ^ 2 + z ^ 2 = 11195 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 2239) := ⟨prime_2239⟩
    have : ¬ ∃ y z : ℕ, 11195 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2239) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 11104, blocked by 347^1
    have hr : y ^ 2 + z ^ 2 = 11104 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 347) := ⟨prime_347⟩
    have : ¬ ∃ y z : ℕ, 11104 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 347) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 10977, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 10977 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 10977 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 10808, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10808 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10808 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 10591, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10591 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10591 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 10320, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 10320 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 10320 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 9989, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 9989 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 9989 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 9592, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 9592 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 9592 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 9123, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9123 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9123 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 8576, blocked by 67^1
    have hr : y ^ 2 + z ^ 2 = 8576 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 67) := ⟨prime_67⟩
    have : ¬ ∃ y z : ℕ, 8576 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 67) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 7945, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 7945 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 7945 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 7224, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 7224 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 7224 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 6407, blocked by 43^1
    have hr : y ^ 2 + z ^ 2 = 6407 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 43) := ⟨prime_43⟩
    have : ¬ ∃ y z : ℕ, 6407 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 43) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 5488, blocked by 7^3
    have hr : y ^ 2 + z ^ 2 = 5488 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 5488 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 3) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 4461, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4461 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4461 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 3320, blocked by 83^1
    have hr : y ^ 2 + z ^ 2 = 3320 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 83) := ⟨prime_83⟩
    have : ¬ ∃ y z : ℕ, 3320 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 83) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 2059, blocked by 71^1
    have hr : y ^ 2 + z ^ 2 = 2059 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 71) := ⟨prime_71⟩
    have : ¬ ∃ y z : ℕ, 2059 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 71) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 672, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 672 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 672 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_11824 : ¬ IsCubeTwoSquares 11824 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 11824 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 11824 := h
  have hx : x ≤ 22 := by
    by_contra hx
    have : 23 ≤ x := by omega
    have : 23 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 23 ^ 3 ≤ 11824 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 11824, blocked by 739^1
    have hr : y ^ 2 + z ^ 2 = 11824 := by
      simpa using h
    haveI : Fact (Nat.Prime 739) := ⟨prime_739⟩
    have : ¬ ∃ y z : ℕ, 11824 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 739) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 11823, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11823 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11823 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 11816, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 11816 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 11816 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 11797, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 11797 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 11797 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 11760, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11760 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11760 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 11699, blocked by 11699^1
    have hr : y ^ 2 + z ^ 2 = 11699 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11699) := ⟨prime_11699⟩
    have : ¬ ∃ y z : ℕ, 11699 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11699) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 11608, blocked by 1451^1
    have hr : y ^ 2 + z ^ 2 = 11608 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1451) := ⟨prime_1451⟩
    have : ¬ ∃ y z : ℕ, 11608 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1451) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 11481, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11481 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11481 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 11312, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 11312 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 11312 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 11095, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 11095 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 11095 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 10824, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 10824 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 10824 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 10493, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10493 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10493 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 10096, blocked by 631^1
    have hr : y ^ 2 + z ^ 2 = 10096 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 631) := ⟨prime_631⟩
    have : ¬ ∃ y z : ℕ, 10096 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 631) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 9627, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9627 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9627 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 9080, blocked by 227^1
    have hr : y ^ 2 + z ^ 2 = 9080 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 227) := ⟨prime_227⟩
    have : ¬ ∃ y z : ℕ, 9080 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 227) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 8449, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 8449 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 8449 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 7728, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 7728 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 7728 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 6911, blocked by 6911^1
    have hr : y ^ 2 + z ^ 2 = 6911 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 6911) := ⟨prime_6911⟩
    have : ¬ ∃ y z : ℕ, 6911 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 6911) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 5992, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 5992 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 5992 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 4965, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 4965 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 4965 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 3824, blocked by 239^1
    have hr : y ^ 2 + z ^ 2 = 3824 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 239) := ⟨prime_239⟩
    have : ¬ ∃ y z : ℕ, 3824 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 239) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 2563, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 2563 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 2563 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 1176, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 1176 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 1176 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_14008 : ¬ IsCubeTwoSquares 14008 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 14008 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 14008 := h
  have hx : x ≤ 24 := by
    by_contra hx
    have : 25 ≤ x := by omega
    have : 25 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 25 ^ 3 ≤ 14008 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 14008, blocked by 103^1
    have hr : y ^ 2 + z ^ 2 = 14008 := by
      simpa using h
    haveI : Fact (Nat.Prime 103) := ⟨prime_103⟩
    have : ¬ ∃ y z : ℕ, 14008 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 103) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 14007, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 14007 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 14007 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 14000, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 14000 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 14000 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 13981, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 13981 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 13981 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 13944, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 13944 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 13944 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 13883, blocked by 13883^1
    have hr : y ^ 2 + z ^ 2 = 13883 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 13883) := ⟨prime_13883⟩
    have : ¬ ∃ y z : ℕ, 13883 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 13883) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 13792, blocked by 431^1
    have hr : y ^ 2 + z ^ 2 = 13792 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 431) := ⟨prime_431⟩
    have : ¬ ∃ y z : ℕ, 13792 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 431) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 13665, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 13665 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 13665 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 13496, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 13496 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 13496 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 13279, blocked by 271^1
    have hr : y ^ 2 + z ^ 2 = 13279 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 271) := ⟨prime_271⟩
    have : ¬ ∃ y z : ℕ, 13279 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 271) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 13008, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 13008 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 13008 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 12677, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 12677 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 12677 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 12280, blocked by 307^1
    have hr : y ^ 2 + z ^ 2 = 12280 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 307) := ⟨prime_307⟩
    have : ¬ ∃ y z : ℕ, 12280 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 307) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 11811, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11811 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11811 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 11264, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 11264 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 11264 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 10633, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 10633 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 10633 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 9912, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 9912 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 9912 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 9095, blocked by 107^1
    have hr : y ^ 2 + z ^ 2 = 9095 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 107) := ⟨prime_107⟩
    have : ¬ ∃ y z : ℕ, 9095 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 107) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 8176, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 8176 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 8176 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 7149, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 7149 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 7149 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 6008, blocked by 751^1
    have hr : y ^ 2 + z ^ 2 = 6008 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 751) := ⟨prime_751⟩
    have : ¬ ∃ y z : ℕ, 6008 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 751) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 4747, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 4747 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 4747 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 3360, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 3360 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 3360 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 1841, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 1841 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 1841 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 184, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 184 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 184 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_15856 : ¬ IsCubeTwoSquares 15856 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 15856 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 15856 := h
  have hx : x ≤ 25 := by
    by_contra hx
    have : 26 ≤ x := by omega
    have : 26 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 26 ^ 3 ≤ 15856 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 15856, blocked by 991^1
    have hr : y ^ 2 + z ^ 2 = 15856 := by
      simpa using h
    haveI : Fact (Nat.Prime 991) := ⟨prime_991⟩
    have : ¬ ∃ y z : ℕ, 15856 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 991) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 15855, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 15855 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 15855 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 15848, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 15848 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 15848 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 15829, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 15829 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 15829 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 15792, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 15792 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 15792 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 15731, blocked by 15731^1
    have hr : y ^ 2 + z ^ 2 = 15731 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 15731) := ⟨prime_15731⟩
    have : ¬ ∃ y z : ℕ, 15731 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 15731) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 15640, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 15640 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 15640 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 15513, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 15513 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 15513 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 15344, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 15344 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 15344 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 15127, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 15127 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 15127 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 14856, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 14856 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 14856 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 14525, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 14525 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 14525 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 14128, blocked by 883^1
    have hr : y ^ 2 + z ^ 2 = 14128 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 883) := ⟨prime_883⟩
    have : ¬ ∃ y z : ℕ, 14128 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 883) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 13659, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 13659 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 13659 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 13112, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 13112 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 13112 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 12481, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 12481 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 12481 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 11760, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 11760 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 11760 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 10943, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 10943 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 10943 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 10024, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10024 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10024 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 8997, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 8997 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 8997 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 7856, blocked by 491^1
    have hr : y ^ 2 + z ^ 2 = 7856 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 491) := ⟨prime_491⟩
    have : ¬ ∃ y z : ℕ, 7856 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 491) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 6595, blocked by 1319^1
    have hr : y ^ 2 + z ^ 2 = 6595 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1319) := ⟨prime_1319⟩
    have : ¬ ∃ y z : ℕ, 6595 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1319) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 5208, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5208 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5208 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 3689, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 3689 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 3689 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 2032, blocked by 127^1
    have hr : y ^ 2 + z ^ 2 = 2032 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 127) := ⟨prime_127⟩
    have : ¬ ∃ y z : ℕ, 2032 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 127) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 25, remainder 231, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 231 := by
      have : 25 ^ 3 = 15625 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 231 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_26544 : ¬ IsCubeTwoSquares 26544 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 26544 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 26544 := h
  have hx : x ≤ 29 := by
    by_contra hx
    have : 30 ≤ x := by omega
    have : 30 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 30 ^ 3 ≤ 26544 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 26544, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 26544 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 26544 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 26543, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 26543 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 26543 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 26536, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 26536 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 26536 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 26517, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 26517 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 26517 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 26480, blocked by 331^1
    have hr : y ^ 2 + z ^ 2 = 26480 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 331) := ⟨prime_331⟩
    have : ¬ ∃ y z : ℕ, 26480 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 331) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 26419, blocked by 911^1
    have hr : y ^ 2 + z ^ 2 = 26419 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 911) := ⟨prime_911⟩
    have : ¬ ∃ y z : ℕ, 26419 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 911) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 26328, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 26328 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 26328 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 26201, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 26201 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 26201 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 26032, blocked by 1627^1
    have hr : y ^ 2 + z ^ 2 = 26032 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1627) := ⟨prime_1627⟩
    have : ¬ ∃ y z : ℕ, 26032 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1627) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 25815, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 25815 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 25815 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 25544, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 25544 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 25544 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 25213, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 25213 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 25213 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 24816, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 24816 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 24816 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 24347, blocked by 251^1
    have hr : y ^ 2 + z ^ 2 = 24347 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 251) := ⟨prime_251⟩
    have : ¬ ∃ y z : ℕ, 24347 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 251) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 23800, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 23800 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 23800 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 23169, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 23169 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 23169 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 22448, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 22448 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 22448 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 21631, blocked by 223^1
    have hr : y ^ 2 + z ^ 2 = 21631 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 223) := ⟨prime_223⟩
    have : ¬ ∃ y z : ℕ, 21631 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 223) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 20712, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 20712 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 20712 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 19685, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 19685 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 19685 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 18544, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 18544 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 18544 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 17283, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 17283 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 17283 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 15896, blocked by 1987^1
    have hr : y ^ 2 + z ^ 2 = 15896 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1987) := ⟨prime_1987⟩
    have : ¬ ∃ y z : ℕ, 15896 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1987) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 14377, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 14377 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 14377 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 12720, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 12720 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 12720 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 25, remainder 10919, blocked by 179^1
    have hr : y ^ 2 + z ^ 2 = 10919 := by
      have : 25 ^ 3 = 15625 := by norm_num
      omega
    haveI : Fact (Nat.Prime 179) := ⟨prime_179⟩
    have : ¬ ∃ y z : ℕ, 10919 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 179) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 26, remainder 8968, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 8968 := by
      have : 26 ^ 3 = 17576 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 8968 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 27, remainder 6861, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 6861 := by
      have : 27 ^ 3 = 19683 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 6861 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 28, remainder 4592, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 4592 := by
      have : 28 ^ 3 = 21952 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 4592 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 29, remainder 2155, blocked by 431^1
    have hr : y ^ 2 + z ^ 2 = 2155 := by
      have : 29 ^ 3 = 24389 := by norm_num
      omega
    haveI : Fact (Nat.Prime 431) := ⟨prime_431⟩
    have : ¬ ∃ y z : ℕ, 2155 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 431) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_28804 : ¬ IsCubeTwoSquares 28804 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 28804 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 28804 := h
  have hx : x ≤ 30 := by
    by_contra hx
    have : 31 ≤ x := by omega
    have : 31 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 31 ^ 3 ≤ 28804 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 28804, blocked by 19^1
    have hr : y ^ 2 + z ^ 2 = 28804 := by
      simpa using h
    haveI : Fact (Nat.Prime 19) := ⟨prime_19⟩
    have : ¬ ∃ y z : ℕ, 28804 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 28803, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 28803 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 28803 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 28796, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 28796 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 28796 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 28777, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 28777 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 28777 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 28740, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 28740 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 28740 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 28679, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 28679 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 28679 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 28588, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 28588 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 28588 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 28461, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 28461 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 28461 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 28292, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 28292 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 28292 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 28075, blocked by 1123^1
    have hr : y ^ 2 + z ^ 2 = 28075 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1123) := ⟨prime_1123⟩
    have : ¬ ∃ y z : ℕ, 28075 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1123) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 27804, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 27804 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 27804 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 27473, blocked by 83^1
    have hr : y ^ 2 + z ^ 2 = 27473 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 83) := ⟨prime_83⟩
    have : ¬ ∃ y z : ℕ, 27473 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 83) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 27076, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 27076 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 27076 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 26607, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 26607 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 26607 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 26060, blocked by 1303^1
    have hr : y ^ 2 + z ^ 2 = 26060 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1303) := ⟨prime_1303⟩
    have : ¬ ∃ y z : ℕ, 26060 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1303) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 25429, blocked by 59^1
    have hr : y ^ 2 + z ^ 2 = 25429 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 59) := ⟨prime_59⟩
    have : ¬ ∃ y z : ℕ, 25429 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 59) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 24708, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 24708 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 24708 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 23891, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 23891 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 23891 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 22972, blocked by 5743^1
    have hr : y ^ 2 + z ^ 2 = 22972 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 5743) := ⟨prime_5743⟩
    have : ¬ ∃ y z : ℕ, 22972 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 5743) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 21945, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 21945 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 21945 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 20804, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 20804 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 20804 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 19543, blocked by 19543^1
    have hr : y ^ 2 + z ^ 2 = 19543 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 19543) := ⟨prime_19543⟩
    have : ¬ ∃ y z : ℕ, 19543 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 19543) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 18156, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 18156 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 18156 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 16637, blocked by 127^1
    have hr : y ^ 2 + z ^ 2 = 16637 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 127) := ⟨prime_127⟩
    have : ¬ ∃ y z : ℕ, 16637 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 127) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 14980, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 14980 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 14980 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 25, remainder 13179, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 13179 := by
      have : 25 ^ 3 = 15625 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 13179 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 26, remainder 11228, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 11228 := by
      have : 26 ^ 3 = 17576 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 11228 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 27, remainder 9121, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 9121 := by
      have : 27 ^ 3 = 19683 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 9121 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 28, remainder 6852, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 6852 := by
      have : 28 ^ 3 = 21952 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 6852 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 29, remainder 4415, blocked by 883^1
    have hr : y ^ 2 + z ^ 2 = 4415 := by
      have : 29 ^ 3 = 24389 := by norm_num
      omega
    haveI : Fact (Nat.Prime 883) := ⟨prime_883⟩
    have : ¬ ∃ y z : ℕ, 4415 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 883) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 30, remainder 1804, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 1804 := by
      have : 30 ^ 3 = 27000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 1804 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_34392 : ¬ IsCubeTwoSquares 34392 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 34392 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 34392 := h
  have hx : x ≤ 32 := by
    by_contra hx
    have : 33 ≤ x := by omega
    have : 33 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 33 ^ 3 ≤ 34392 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 34392, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 34392 := by
      simpa using h
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 34392 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 34391, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 34391 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 34391 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 34384, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 34384 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 34384 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 34365, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 34365 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 34365 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 34328, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 34328 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 34328 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 34267, blocked by 34267^1
    have hr : y ^ 2 + z ^ 2 = 34267 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 34267) := ⟨prime_34267⟩
    have : ¬ ∃ y z : ℕ, 34267 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 34267) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 34176, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 34176 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 34176 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 34049, blocked by 79^1
    have hr : y ^ 2 + z ^ 2 = 34049 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 79) := ⟨prime_79⟩
    have : ¬ ∃ y z : ℕ, 34049 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 79) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 33880, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 33880 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 33880 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 33663, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 33663 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 33663 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 33392, blocked by 2087^1
    have hr : y ^ 2 + z ^ 2 = 33392 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 2087) := ⟨prime_2087⟩
    have : ¬ ∃ y z : ℕ, 33392 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2087) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 33061, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 33061 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 33061 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 32664, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 32664 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 32664 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 32195, blocked by 47^1
    have hr : y ^ 2 + z ^ 2 = 32195 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 47) := ⟨prime_47⟩
    have : ¬ ∃ y z : ℕ, 32195 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 47) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 31648, blocked by 23^1
    have hr : y ^ 2 + z ^ 2 = 31648 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 23) := ⟨prime_23⟩
    have : ¬ ∃ y z : ℕ, 31648 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 23) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 31017, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 31017 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 31017 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 30296, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 30296 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 30296 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 29479, blocked by 719^1
    have hr : y ^ 2 + z ^ 2 = 29479 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 719) := ⟨prime_719⟩
    have : ¬ ∃ y z : ℕ, 29479 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 719) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 28560, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 28560 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 28560 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 27533, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 27533 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 27533 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 26392, blocked by 3299^1
    have hr : y ^ 2 + z ^ 2 = 26392 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3299) := ⟨prime_3299⟩
    have : ¬ ∃ y z : ℕ, 26392 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3299) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 25131, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 25131 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 25131 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 23744, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 23744 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 23744 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 22225, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 22225 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 22225 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 20568, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 20568 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 20568 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 25, remainder 18767, blocked by 383^1
    have hr : y ^ 2 + z ^ 2 = 18767 := by
      have : 25 ^ 3 = 15625 := by norm_num
      omega
    haveI : Fact (Nat.Prime 383) := ⟨prime_383⟩
    have : ¬ ∃ y z : ℕ, 18767 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 383) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 26, remainder 16816, blocked by 1051^1
    have hr : y ^ 2 + z ^ 2 = 16816 := by
      have : 26 ^ 3 = 17576 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1051) := ⟨prime_1051⟩
    have : ¬ ∃ y z : ℕ, 16816 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1051) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 27, remainder 14709, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 14709 := by
      have : 27 ^ 3 = 19683 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 14709 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 28, remainder 12440, blocked by 311^1
    have hr : y ^ 2 + z ^ 2 = 12440 := by
      have : 28 ^ 3 = 21952 := by norm_num
      omega
    haveI : Fact (Nat.Prime 311) := ⟨prime_311⟩
    have : ¬ ∃ y z : ℕ, 12440 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 311) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 29, remainder 10003, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 10003 := by
      have : 29 ^ 3 = 24389 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 10003 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 30, remainder 7392, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 7392 := by
      have : 30 ^ 3 = 27000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 7392 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 31, remainder 4601, blocked by 43^1
    have hr : y ^ 2 + z ^ 2 = 4601 := by
      have : 31 ^ 3 = 29791 := by norm_num
      omega
    haveI : Fact (Nat.Prime 43) := ⟨prime_43⟩
    have : ¬ ∃ y z : ℕ, 4601 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 43) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 32, remainder 1624, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 1624 := by
      have : 32 ^ 3 = 32768 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 1624 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
lemma not_rep_47984 : ¬ IsCubeTwoSquares 47984 := by
  rintro ⟨x, y, z, h⟩
  have hx3 : x ^ 3 ≤ 47984 := by
    calc x ^ 3 ≤ x ^ 3 + y ^ 2 := Nat.le_add_right _ _
      _ ≤ x ^ 3 + y ^ 2 + z ^ 2 := Nat.le_add_right _ _
      _ = 47984 := h
  have hx : x ≤ 36 := by
    by_contra hx
    have : 37 ≤ x := by omega
    have : 37 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left this 3
    have : 37 ^ 3 ≤ 47984 := le_trans this hx3
    norm_num at this
  interval_cases x
  · -- x = 0, remainder 47984, blocked by 2999^1
    have hr : y ^ 2 + z ^ 2 = 47984 := by
      simpa using h
    haveI : Fact (Nat.Prime 2999) := ⟨prime_2999⟩
    have : ¬ ∃ y z : ℕ, 47984 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 2999) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 1, remainder 47983, blocked by 3691^1
    have hr : y ^ 2 + z ^ 2 = 47983 := by
      have : 1 ^ 3 = 1 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3691) := ⟨prime_3691⟩
    have : ¬ ∃ y z : ℕ, 47983 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3691) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 2, remainder 47976, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 47976 := by
      have : 2 ^ 3 = 8 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 47976 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 3, remainder 47957, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 47957 := by
      have : 3 ^ 3 = 27 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 47957 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 4, remainder 47920, blocked by 599^1
    have hr : y ^ 2 + z ^ 2 = 47920 := by
      have : 4 ^ 3 = 64 := by norm_num
      omega
    haveI : Fact (Nat.Prime 599) := ⟨prime_599⟩
    have : ¬ ∃ y z : ℕ, 47920 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 599) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 5, remainder 47859, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 47859 := by
      have : 5 ^ 3 = 125 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 47859 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 6, remainder 47768, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 47768 := by
      have : 6 ^ 3 = 216 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 47768 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 7, remainder 47641, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 47641 := by
      have : 7 ^ 3 = 343 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 47641 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 8, remainder 47472, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 47472 := by
      have : 8 ^ 3 = 512 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 47472 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 9, remainder 47255, blocked by 727^1
    have hr : y ^ 2 + z ^ 2 = 47255 := by
      have : 9 ^ 3 = 729 := by norm_num
      omega
    haveI : Fact (Nat.Prime 727) := ⟨prime_727⟩
    have : ¬ ∃ y z : ℕ, 47255 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 727) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 10, remainder 46984, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 46984 := by
      have : 10 ^ 3 = 1000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 46984 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 11, remainder 46653, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 46653 := by
      have : 11 ^ 3 = 1331 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 46653 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 12, remainder 46256, blocked by 59^1
    have hr : y ^ 2 + z ^ 2 = 46256 := by
      have : 12 ^ 3 = 1728 := by norm_num
      omega
    haveI : Fact (Nat.Prime 59) := ⟨prime_59⟩
    have : ¬ ∃ y z : ℕ, 46256 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 59) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 13, remainder 45787, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 45787 := by
      have : 13 ^ 3 = 2197 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 45787 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 14, remainder 45240, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 45240 := by
      have : 14 ^ 3 = 2744 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 45240 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 15, remainder 44609, blocked by 31^1
    have hr : y ^ 2 + z ^ 2 = 44609 := by
      have : 15 ^ 3 = 3375 := by norm_num
      omega
    haveI : Fact (Nat.Prime 31) := ⟨prime_31⟩
    have : ¬ ∃ y z : ℕ, 44609 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 31) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 16, remainder 43888, blocked by 211^1
    have hr : y ^ 2 + z ^ 2 = 43888 := by
      have : 16 ^ 3 = 4096 := by norm_num
      omega
    haveI : Fact (Nat.Prime 211) := ⟨prime_211⟩
    have : ¬ ∃ y z : ℕ, 43888 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 211) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 17, remainder 43071, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 43071 := by
      have : 17 ^ 3 = 4913 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 43071 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 18, remainder 42152, blocked by 11^1
    have hr : y ^ 2 + z ^ 2 = 42152 := by
      have : 18 ^ 3 = 5832 := by norm_num
      omega
    haveI : Fact (Nat.Prime 11) := ⟨prime_11⟩
    have : ¬ ∃ y z : ℕ, 42152 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 11) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 19, remainder 41125, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 41125 := by
      have : 19 ^ 3 = 6859 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 41125 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 20, remainder 39984, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 39984 := by
      have : 20 ^ 3 = 8000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 39984 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 21, remainder 38723, blocked by 38723^1
    have hr : y ^ 2 + z ^ 2 = 38723 := by
      have : 21 ^ 3 = 9261 := by norm_num
      omega
    haveI : Fact (Nat.Prime 38723) := ⟨prime_38723⟩
    have : ¬ ∃ y z : ℕ, 38723 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 38723) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 22, remainder 37336, blocked by 359^1
    have hr : y ^ 2 + z ^ 2 = 37336 := by
      have : 22 ^ 3 = 10648 := by norm_num
      omega
    haveI : Fact (Nat.Prime 359) := ⟨prime_359⟩
    have : ¬ ∃ y z : ℕ, 37336 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 359) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 23, remainder 35817, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 35817 := by
      have : 23 ^ 3 = 12167 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 35817 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 24, remainder 34160, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 34160 := by
      have : 24 ^ 3 = 13824 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 34160 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 25, remainder 32359, blocked by 32359^1
    have hr : y ^ 2 + z ^ 2 = 32359 := by
      have : 25 ^ 3 = 15625 := by norm_num
      omega
    haveI : Fact (Nat.Prime 32359) := ⟨prime_32359⟩
    have : ¬ ∃ y z : ℕ, 32359 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 32359) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 26, remainder 30408, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 30408 := by
      have : 26 ^ 3 = 17576 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 30408 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 27, remainder 28301, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 28301 := by
      have : 27 ^ 3 = 19683 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 28301 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 28, remainder 26032, blocked by 1627^1
    have hr : y ^ 2 + z ^ 2 = 26032 := by
      have : 28 ^ 3 = 21952 := by norm_num
      omega
    haveI : Fact (Nat.Prime 1627) := ⟨prime_1627⟩
    have : ¬ ∃ y z : ℕ, 26032 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 1627) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 29, remainder 23595, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 23595 := by
      have : 29 ^ 3 = 24389 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 23595 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 30, remainder 20984, blocked by 43^1
    have hr : y ^ 2 + z ^ 2 = 20984 := by
      have : 30 ^ 3 = 27000 := by norm_num
      omega
    haveI : Fact (Nat.Prime 43) := ⟨prime_43⟩
    have : ¬ ∃ y z : ℕ, 20984 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 43) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 31, remainder 18193, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 18193 := by
      have : 31 ^ 3 = 29791 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 18193 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 32, remainder 15216, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 15216 := by
      have : 32 ^ 3 = 32768 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 15216 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 33, remainder 12047, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 12047 := by
      have : 33 ^ 3 = 35937 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 12047 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 34, remainder 8680, blocked by 7^1
    have hr : y ^ 2 + z ^ 2 = 8680 := by
      have : 34 ^ 3 = 39304 := by norm_num
      omega
    haveI : Fact (Nat.Prime 7) := ⟨prime_7⟩
    have : ¬ ∃ y z : ℕ, 8680 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 7) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 35, remainder 5109, blocked by 3^1
    have hr : y ^ 2 + z ^ 2 = 5109 := by
      have : 35 ^ 3 = 42875 := by norm_num
      omega
    haveI : Fact (Nat.Prime 3) := ⟨prime_3⟩
    have : ¬ ∃ y z : ℕ, 5109 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 3) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩
  · -- x = 36, remainder 1328, blocked by 83^1
    have hr : y ^ 2 + z ^ 2 = 1328 := by
      have : 36 ^ 3 = 46656 := by norm_num
      omega
    haveI : Fact (Nat.Prime 83) := ⟨prime_83⟩
    have : ¬ ∃ y z : ℕ, 1328 = y ^ 2 + z ^ 2 :=
      not_two_sq_of_odd_val (p := 83) (k := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by decide)
    exact this ⟨y, z, hr.symm⟩

def L18 : List ℕ := [120, 312, 813, 2136, 2680, 3224, 4404, 5340, 6420, 10060, 11320, 11824, 14008, 15856, 26544, 28804, 34392, 47984]

lemma mem_L18_iff (n : ℕ) : n ∈ L18 ↔
    n = 120 ∨ n = 312 ∨ n = 813 ∨ n = 2136 ∨ n = 2680 ∨ n = 3224 ∨
    n = 4404 ∨ n = 5340 ∨ n = 6420 ∨ n = 10060 ∨ n = 11320 ∨ n = 11824 ∨
    n = 14008 ∨ n = 15856 ∨ n = 26544 ∨ n = 28804 ∨ n = 34392 ∨ n = 47984 := by
  simp [L18]

lemma not_rep_of_mem_L18 {n : ℕ} (h : n ∈ L18) : ¬ IsCubeTwoSquares n := by
  rw [mem_L18_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact not_rep_120
  · exact not_rep_312
  · exact not_rep_813
  · exact not_rep_2136
  · exact not_rep_2680
  · exact not_rep_3224
  · exact not_rep_4404
  · exact not_rep_5340
  · exact not_rep_6420
  · exact not_rep_10060
  · exact not_rep_11320
  · exact not_rep_11824
  · exact not_rep_14008
  · exact not_rep_15856
  · exact not_rep_26544
  · exact not_rep_28804
  · exact not_rep_34392
  · exact not_rep_47984

lemma odd_of_four_mul_add_one (m : ℕ) : Odd (4 * m + 1) :=
  ⟨2 * m, by ring⟩

lemma pow_two_le_of_has_form {n k m : ℕ} (heq : n = 2 ^ k * (4 * m + 1)) :
    2 ^ k ≤ n := by
  rw [heq]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma not_has_form_of_val {N : ℕ} (hN : N ≠ 0)
    (H : ∀ k, 2 ^ k ≤ N → ∀ m, N ≠ 2 ^ k * (4 * m + 1)) :
    ¬ has_form_two_pow_k_times_four_m_plus_one N := by
  rintro ⟨k, m, heq⟩
  exact H k (pow_two_le_of_has_form heq) m heq

lemma k_le_of_two_pow_le {k N b : ℕ} (hb : 2 ^ (b + 1) > N)
    (hkN : 2 ^ k ≤ N) : k ≤ b := by
  by_contra h
  have : b + 1 ≤ k := by omega
  have : 2 ^ (b + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
  omega

lemma two_pow_mul_odd_unique {k₁ k₂ a b : ℕ} (ha : Odd a) (hb : Odd b)
    (h : 2 ^ k₁ * a = 2 ^ k₂ * b) : k₁ = k₂ ∧ a = b := by
  wlog hle : k₁ ≤ k₂ generalizing k₁ k₂ a b
  · have := this hb ha h.symm (le_of_not_ge hle)
    exact ⟨this.1.symm, this.2.symm⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hpow : 2 ^ (k₁ + t) = 2 ^ k₁ * 2 ^ t := Nat.pow_add _ _ _
  rw [hpow, mul_assoc] at h
  have hne : (2 : ℕ) ^ k₁ ≠ 0 := pow_ne_zero k₁ (by norm_num)
  have h' : a = 2 ^ t * b := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h
  have ht : t = 0 := by
    by_contra ht
    have : 2 ∣ a := by
      rw [h']
      exact dvd_mul_of_dvd_left (dvd_pow_self _ ht) _
    exact Nat.not_even_iff_odd.mpr ha (even_iff_two_dvd.mpr this)
  subst ht
  simp at h'
  exact ⟨rfl, h'⟩

lemma not_has_form_of_odd_part {n k odd : ℕ} (hodd : Odd odd) (hn : n = 2 ^ k * odd)
    (h3 : odd % 4 = 3) : ¬ has_form_two_pow_k_times_four_m_plus_one n := by
  rintro ⟨k', m, heq⟩
  have hodd' : Odd (4 * m + 1) := ⟨2 * m, by ring⟩
  have h1 : (4 * m + 1) % 4 = 1 := by omega
  obtain ⟨hk, hodd_eq⟩ := two_pow_mul_odd_unique hodd hodd' (hn.symm.trans heq)
  rw [hodd_eq] at h3
  omega

lemma L18_special_form {n : ℕ} (hn : n ∈ L18)
    (hf : has_form_two_pow_k_times_four_m_plus_one n) :
    n = 813 ∨ n = 4404 ∨ n = 6420 ∨ n = 28804 := by
  rw [mem_L18_iff] at hn
  rcases hn with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact (not_has_form_of_odd_part (n := 120) (k := 3) (odd := 15)
      ⟨7, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 312) (k := 3) (odd := 39)
      ⟨19, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · subst hn; exact Or.inl rfl
  · exact (not_has_form_of_odd_part (n := 2136) (k := 3) (odd := 267)
      ⟨133, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 2680) (k := 3) (odd := 335)
      ⟨167, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 3224) (k := 3) (odd := 403)
      ⟨201, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · subst hn; exact Or.inr (Or.inl rfl)
  · exact (not_has_form_of_odd_part (n := 5340) (k := 2) (odd := 1335)
      ⟨667, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · subst hn; exact Or.inr (Or.inr (Or.inl rfl))
  · exact (not_has_form_of_odd_part (n := 10060) (k := 2) (odd := 2515)
      ⟨1257, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 11320) (k := 3) (odd := 1415)
      ⟨707, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 11824) (k := 4) (odd := 739)
      ⟨369, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 14008) (k := 3) (odd := 1751)
      ⟨875, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 15856) (k := 4) (odd := 991)
      ⟨495, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 26544) (k := 4) (odd := 1659)
      ⟨829, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · subst hn; exact Or.inr (Or.inr (Or.inr rfl))
  · exact (not_has_form_of_odd_part (n := 34392) (k := 3) (odd := 4299)
      ⟨2149, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim
  · exact (not_has_form_of_odd_part (n := 47984) (k := 4) (odd := 2999)
      ⟨1499, by norm_num⟩ (by norm_num) (by norm_num) (by rwa [hn] at hf)).elim

/-- If `m` is a cube plus two squares, then so is `8 * m`. -/
lemma IsCubeTwoSquares.mul_eight {m : ℕ} (h : IsCubeTwoSquares m) :
    IsCubeTwoSquares (8 * m) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  wlog hyz : y ≤ z generalizing y z
  · exact this z y (by linarith) (le_of_not_ge hyz)
  refine ⟨2 * x, 2 * (y + z), 2 * (z - y), ?_⟩
  have hid' : (y + z) ^ 2 + (z - y) ^ 2 = 2 * (y ^ 2 + z ^ 2) := by
    zify [hyz]
    ring
  calc (2 * x) ^ 3 + (2 * (y + z)) ^ 2 + (2 * (z - y)) ^ 2
      = 8 * x ^ 3 + 4 * ((y + z) ^ 2 + (z - y) ^ 2) := by ring
    _ = 8 * x ^ 3 + 4 * (2 * (y ^ 2 + z ^ 2)) := by rw [hid']
    _ = 8 * (x ^ 3 + y ^ 2 + z ^ 2) := by ring
    _ = 8 * m := by rw [hxyz]

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

def isHardB (n : ℕ) : Bool :=
  decide (n % 8 = 3 ∨ n % 8 = 6 ∨ n % 8 = 7)

def isL18B (n : ℕ) : Bool :=
  n == 120 || n == 312 || n == 813 || n == 2136 || n == 2680 || n == 3224 ||
  n == 4404 || n == 5340 || n == 6420 || n == 10060 || n == 11320 || n == 11824 ||
  n == 14008 || n == 15856 || n == 26544 || n == 28804 || n == 34392 || n == 47984

lemma isHardB_iff (n : ℕ) : isHardB n = true ↔ IsHard n := by
  simp [isHardB, IsHard]

lemma isL18B_true_mem (n : ℕ) (h : isL18B n = true) : n ∈ L18 := by
  simp [isL18B, Bool.or_eq_true, beq_iff_eq] at h
  simp [L18]
  omega

def checkOne (n : ℕ) (w : ℕ × ℕ × ℕ) : Bool :=
  isHardB n || isL18B n || decide (w.1 ^ 3 + w.2.1 ^ 2 + w.2.2 ^ 2 = n)

def checkList : List (ℕ × ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | w :: rest, n => checkOne n w && checkList rest (n + 1)

lemma checkList_spec (l : List (ℕ × ℕ × ℕ)) (n0 : ℕ)
    (h : checkList l n0 = true) (n : ℕ) (hn1 : n0 ≤ n) (hn2 : n < n0 + l.length) :
    IsHard n ∨ n ∈ L18 ∨ IsCubeTwoSquares n := by
  induction l generalizing n0 n with
  | nil =>
    simp at hn2
    omega
  | cons w rest ih =>
    simp [checkList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases eq_or_lt_of_le hn1 with heq | hn1'
    · subst heq
      unfold checkOne at h1
      rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with (hHard | hL) | hW
      · exact Or.inl ((isHardB_iff n0).mp hHard)
      · exact Or.inr (Or.inl (isL18B_true_mem n0 hL))
      · exact Or.inr (Or.inr ⟨w.1, w.2.1, w.2.2, hW⟩)
    · refine ih (n0 + 1) h2 n hn1' ?_
      simp [List.length_cons] at hn2
      omega

def wits_0 : List (ℕ × ℕ × ℕ) := [(0,0,0),(0,0,1),(0,1,1),(0,0,0),(0,0,2),(0,1,2),(0,0,0),(0,0,0),(0,2,2),(0,0,3),(0,1,3),(0,0,0),(2,0,2),(0,2,3),(0,0,0),(0,0,0),(0,0,4),(0,1,4),(0,3,3),(0,0,0),(0,2,4),(1,2,4),(0,0,0),(0,0,0),(2,0,4),(0,0,5),(0,1,5),(0,0,0),(2,2,4),(0,2,5),(0,0,0),(0,0,0),(0,4,4),(1,4,4),(0,3,5),(0,0,0),(0,0,6),(0,1,6),(0,0,0),(0,0,0),(0,2,6),(0,4,5),(1,4,5),(0,0,0),(2,0,6),(0,3,6),(0,0,0),(0,0,0),(2,2,6),(0,0,7),(0,1,7),(0,0,0),(0,4,6),(0,2,7),(0,0,0),(0,0,0),(3,2,5),(2,0,7),(0,3,7),(0,0,0),(2,4,6),(0,5,6),(0,0,0),(0,0,0),(0,0,8),(0,1,8),(1,1,8),(0,0,0),(0,2,8),(1,2,8),(0,0,0),(0,0,0),(0,6,6),(0,3,8),(0,5,7),(0,0,0),(2,2,8),(3,1,7),(0,0,0),(0,0,0),(0,4,8),(0,0,9),(0,1,9),(0,0,0),(4,2,4),(0,2,9),(0,0,0),(0,0,0),(2,4,8),(0,5,8),(0,3,9),(0,0,0),(3,1,8),(2,2,9),(0,0,0),(0,0,0),(4,4,4),(0,4,9),(0,7,7),(0,0,0),(0,0,10),(0,1,10),(0,0,0),(0,0,0),(0,2,10),(1,2,10),(0,5,9),(0,0,0),(2,0,10),(0,3,10),(0,0,0),(0,0,0),(2,2,10),(0,7,8),(1,7,8),(0,0,0),(0,4,10),(0,6,9),(0,0,0),(0,0,0),(0,0,0),(0,0,11),(0,1,11),(0,0,0),(2,4,10),(0,2,11),(0,0,0),(0,0,0),(0,8,8),(1,8,8),(0,3,11),(0,0,0),(4,2,8),(2,2,11),(0,0,0),(0,0,0),(0,6,10),(0,4,11),(1,4,11),(0,0,0),(3,7,8),(5,0,4),(0,0,0),(0,0,0),(0,0,12),(0,1,12),(0,5,11),(0,0,0),(0,2,12),(0,7,10),(0,0,0),(0,0,0),(2,0,12),(0,3,12),(1,3,12),(0,0,0),(2,2,12),(0,6,11),(0,0,0),(0,0,0),(0,4,12),(1,4,12),(0,9,9),(0,0,0),(0,8,10),(1,8,10),(0,0,0),(0,0,0),(2,4,12),(0,0,13),(0,1,13),(0,0,0),(2,8,10),(0,2,13),(0,0,0),(0,0,0),(3,7,10),(2,0,13),(0,3,13),(0,0,0),(0,6,12),(0,9,10),(0,0,0),(0,0,0),(3,6,11),(0,4,13),(1,4,13),(0,0,0),(2,6,12),(2,9,10),(0,0,0),(0,0,0),(4,8,8),(0,7,12),(0,5,13),(0,0,0),(0,0,14),(0,1,14),(0,0,0),(0,0,0),(0,2,14),(1,2,14),(0,9,11),(0,0,0),(2,0,14),(0,3,14),(0,0,0),(0,0,0),(0,8,12),(1,8,12),(2,9,11),(0,0,0),(0,4,14),(1,4,14),(0,0,0),(0,0,0),(2,8,12),(4,3,12),(0,7,13),(0,0,0),(2,4,14),(0,5,14),(0,0,0),(0,0,0),(3,1,14),(0,0,15),(0,1,15),(0,0,0),(4,8,10),(0,2,15),(0,0,0),(0,0,0),(0,6,14),(0,8,13),(0,3,15),(0,0,0),(6,2,4),(2,2,15),(0,0,0),(0,0,0),(2,6,14),(0,4,15),(0,11,11),(0,0,0),(0,10,12),(0,7,14),(0,0,0),(0,0,0),(3,5,14),(2,4,15),(0,5,15),(0,0,0),(2,10,12),(2,7,14),(0,0,0),(0,0,0),(0,0,16),(0,1,16),(1,1,16),(0,0,0),(0,2,16),(0,6,15),(0,0,0),(0,0,0),(2,0,16),(0,3,16),(1,3,16),(0,0,0),(2,2,16),(0,10,13),(0,0,0),(0,0,0),(0,4,16),(1,4,16),(0,7,15),(0,0,0),(4,4,14),(0,9,14),(0,0,0),(0,0,0),(2,4,16),(0,5,16),(1,5,16),(0,0,0),(3,1,16),(2,9,14),(0,0,0),(0,0,0),(0,12,12),(0,0,17),(0,1,17),(0,0,0),(0,6,16),(0,2,17),(0,0,0),(0,0,0),(0,10,14),(1,10,14),(0,3,17),(0,0,0),(2,6,16),(2,2,17),(0,0,0),(0,0,0),(2,10,14),(0,4,17),(0,9,15),(0,0,0),(3,5,16),(4,7,14),(0,0,0),(0,0,0),(0,0,0),(0,12,13),(0,5,17),(0,0,0),(3,0,17),(0,11,14),(0,0,0),(0,0,0),(0,8,16),(1,8,16),(2,5,17),(0,0,0),(0,0,18),(0,1,18),(0,0,0),(0,0,0),(0,2,18),(1,2,18),(5,3,14),(0,0,0),(2,0,18),(0,3,18),(0,0,0),(0,0,0),(2,2,18),(0,9,16),(0,7,17),(0,0,0),(0,4,18),(1,4,18),(0,0,0),(0,0,0),(3,11,14),(2,9,16),(0,11,15),(0,0,0),(2,4,18),(0,5,18),(0,0,0),(0,0,0),(3,1,18),(0,8,17),(1,8,17),(0,0,0),(0,10,16),(1,10,16),(0,0,0),(0,0,0),(0,6,18),(0,0,19),(0,1,19),(0,0,0),(2,10,16),(0,2,19),(0,0,0),(0,0,0),(2,6,18),(0,12,15),(0,3,19),(0,0,0),(7,2,5),(0,7,18),(0,0,0),(0,0,0),(3,5,18),(0,4,19),(1,4,19),(0,0,0),(3,8,17),(2,7,18),(0,0,0),(0,0,0),(4,8,16),(2,4,19),(0,5,19),(0,0,0),(0,8,18),(0,10,17),(0,0,0),(0,0,0),(0,14,14),(1,14,14),(0,13,15),(0,0,0),(2,8,18),(0,6,19),(0,0,0),(0,0,0),(0,0,20),(0,1,20),(1,1,20),(0,0,0),(0,2,20),(0,9,18),(0,0,0),(0,0,0),(2,0,20),(0,3,20),(0,7,19),(0,0,0),(2,2,20),(2,9,18),(0,0,0),(0,0,0),(0,4,20),(1,4,20),(2,7,19),(0,0,0),(4,10,16),(0,14,15),(0,0,0),(0,0,0),(0,10,18),(0,5,20),(1,5,20),(0,0,0),(3,1,20),(2,14,15),(0,0,0),(0,0,0),(2,10,18),(0,12,17),(1,12,17),(0,0,0),(0,6,20),(1,6,20),(0,0,0),(0,0,0),(7,4,9),(0,0,21),(0,1,21),(0,0,0),(2,6,20),(0,2,21),(0,0,0),(0,0,0),(3,14,15),(0,7,20),(0,3,21),(0,0,0),(0,14,16),(1,14,16),(0,0,0),(0,0,0),(4,14,14),(0,4,21),(0,13,17),(0,0,0),(2,14,16),(0,10,19),(0,0,0),(0,0,0),(0,8,20),(1,8,20),(0,5,21),(0,0,0),(0,12,18),(1,12,18),(0,0,0),(0,0,0),(2,8,20),(4,3,20),(2,5,21),(0,0,0),(2,12,18),(0,6,21),(0,0,0),(0,0,0),(4,4,20),(0,9,20),(0,11,19),(0,0,0),(0,0,22),(0,1,22),(0,0,0),(0,0,0),(0,2,22),(1,2,22),(0,7,21),(0,0,0),(2,0,22),(0,3,22),(0,0,0),(0,0,0),(2,2,22),(4,12,17),(2,7,21),(0,0,0),(0,4,22),(1,4,22),(0,0,0),(0,0,0),(3,6,21),(0,8,21),(1,8,21),(0,0,0),(2,4,22),(0,5,22),(0,0,0),(0,0,0),(0,16,16),(1,16,16),(0,15,17),(0,0,0),(4,14,16),(2,5,22),(0,0,0),(0,0,0),(0,6,22),(0,11,20),(0,9,21),(0,0,0),(7,9,10),(4,10,19),(0,0,0),(0,0,0),(2,6,22),(0,0,23),(0,1,23),(0,0,0),(3,8,21),(0,2,23),(0,0,0),(0,0,0),(3,5,22),(2,0,23),(0,3,23),(0,0,0),(6,0,18),(0,10,21),(0,0,0),(0,0,0),(0,12,20),(0,4,23),(1,4,23),(0,0,0),(0,8,22),(0,15,18),(0,0,0),(0,0,0),(2,12,20),(2,4,23),(0,5,23),(0,0,0),(2,8,22),(0,14,19),(0,0,0),(0,0,0),(3,2,23),(5,6,20),(0,11,21),(0,0,0),(4,4,22),(0,6,23),(0,0,0),(0,0,0),(3,10,21),(0,13,20),(1,13,20),(0,0,0),(3,4,23),(2,6,23),(0,0,0),(0,0,0),(0,0,24),(0,1,24),(0,7,23),(0,0,0),(0,2,24),(1,2,24),(0,0,0),(0,0,0),(0,10,22),(0,3,24),(0,15,19),(0,0,0),(2,2,24),(3,11,21),(0,0,0),(0,0,0),(0,4,24),(0,8,23),(1,8,23),(0,0,0),(0,14,20),(1,14,20),(0,0,0),(0,0,0),(2,4,24),(0,5,24),(1,5,24),(0,0,0),(2,14,20),(0,11,22),(0,0,0),(0,0,0),(4,12,20),(2,5,24),(0,9,23),(0,0,0),(0,6,24),(0,17,18),(0,0,0),(0,0,0),(6,0,20),(0,16,19),(1,16,19),(0,0,0),(2,6,24),(2,17,18),(0,0,0),(0,0,0),(7,5,16),(0,0,25),(0,1,25),(0,0,0),(0,12,22),(0,2,25),(0,0,0),(0,0,0),(3,11,22),(2,0,25),(0,3,25),(0,0,0),(2,12,22),(0,14,21),(0,0,0),(0,0,0),(0,8,24),(0,4,25),(1,4,25),(0,0,0),(3,16,19),(2,14,21),(0,0,0),(0,0,0),(0,18,18),(1,18,18),(0,5,25),(0,0,0),(3,0,25),(0,13,22),(0,0,0),(0,0,0),(0,16,20),(0,9,24),(1,9,24),(0,0,0),(4,14,20),(0,6,25),(0,0,0),(0,0,0),(2,16,20),(2,9,24),(0,15,21),(0,0,0),(3,4,25),(2,6,25),(0,0,0),(0,0,0),(8,4,12),(0,12,23),(0,7,25),(0,0,0),(0,0,26),(0,1,26),(0,0,0),(0,0,0),(0,2,26),(1,2,26),(2,7,25),(0,0,0),(2,0,26),(0,3,26),(0,0,0),(0,0,0),(2,2,26),(0,8,25),(1,8,25),(0,0,0),(0,4,26),(1,4,26),(0,0,0),(0,0,0),(7,8,17),(0,11,24),(0,13,23),(0,0,0),(2,4,26),(0,5,26),(0,0,0),(0,0,0),(3,1,26),(2,11,24),(0,9,25),(0,0,0),(7,2,19),(0,15,22),(0,0,0),(0,0,0),(0,6,26),(1,6,26),(2,9,25),(0,0,0),(3,8,25),(2,15,22),(0,0,0),(0,0,0),(0,12,24),(1,12,24),(0,19,19),(0,0,0),(0,18,20),(0,7,26),(0,0,0),(0,0,0),(2,12,24),(0,0,27),(0,1,27),(0,0,0),(2,18,20),(0,2,27),(0,0,0),(0,0,0),(3,15,22),(2,0,27),(0,3,27),(0,0,0),(0,8,26),(1,8,26),(0,0,0),(0,0,0),(4,2,26),(0,4,27),(0,11,25),(0,0,0),(2,8,26),(3,19,19),(0,0,0),(0,0,0),(3,7,26),(2,4,27),(0,5,27),(0,0,0),(3,0,27),(0,9,26),(0,0,0),(0,0,0),(3,2,27),(0,19,20),(1,19,20),(0,0,0),(6,8,22),(0,6,27),(0,0,0),(0,0,0),(7,5,20),(0,12,25),(1,12,25),(0,0,0),(0,14,24),(0,17,22),(0,0,0),(0,0,0),(0,10,26),(1,10,26),(0,7,27),(0,0,0),(2,14,24),(2,17,22),(0,0,0),(0,0,0),(0,0,28),(0,1,28),(1,1,28),(0,0,0),(0,2,28),(1,2,28),(0,0,0),(0,0,0),(2,0,28),(0,3,28),(0,13,25),(0,0,0),(2,2,28),(0,11,26),(0,0,0),(0,0,0),(0,4,28),(0,15,24),(0,19,21),(0,0,0),(4,8,26),(2,11,26),(0,0,0),(0,0,0),(0,18,22),(0,5,28),(0,9,27),(0,0,0),(3,1,28),(0,0,0),(0,0,0),(0,0,0),(2,18,22),(2,5,28),(0,17,23),(0,0,0),(0,6,28),(0,14,25),(0,0,0),(0,0,0),(3,11,26),(4,19,20),(2,17,23),(0,0,0),(2,6,28),(0,10,27),(0,0,0),(0,0,0),(0,16,24),(0,7,28),(1,7,28),(0,0,0),(3,5,28),(2,10,27),(0,0,0),(0,0,0),(2,16,24),(0,0,29),(0,1,29),(0,0,0),(6,12,22),(0,2,29),(0,0,0),(0,0,0),(0,8,28),(1,8,28),(0,3,29),(0,0,0),(4,2,28),(0,18,23),(0,0,0),(0,0,0),(2,8,28),(0,4,29),(1,4,29),(0,0,0),(3,7,28),(2,18,23),(0,0,0),(0,0,0),(4,4,28),(0,9,28),(0,5,29),(0,0,0),(3,0,29),(3,1,29),(0,0,0),(0,0,0),(0,14,26),(0,12,27),(1,12,27),(0,0,0),(7,2,23),(0,6,29),(0,0,0),(0,0,0),(2,14,26),(0,16,25),(0,21,21),(0,0,0),(0,10,28),(1,10,28),(0,0,0),(0,0,0),(7,4,23),(2,16,25),(0,7,29),(0,0,0),(2,10,28),(3,5,29),(0,0,0),(0,0,0),(4,16,24),(4,7,28),(0,13,27),(0,0,0),(0,0,30),(0,1,30),(0,0,0),(0,0,0),(0,2,30),(0,8,29),(1,8,29),(0,0,0),(2,0,30),(0,3,30),(0,0,0),(0,0,0),(2,2,30),(2,8,29),(0,17,25),(0,0,0),(0,4,30),(1,4,30),(0,0,0),(0,0,0),(7,1,24),(4,4,29),(0,9,29),(0,0,0),(2,4,30),(0,5,30),(0,0,0),(0,0,0),(0,12,28),(0,20,23),(1,20,23),(0,0,0),(0,16,26),(1,16,26),(0,0,0),(0,0,0),(0,6,30),(0,19,24),(1,19,24),(0,0,0),(2,16,26),(0,10,29),(0,0,0),(0,0,0),(2,6,30),(2,19,24),(4,21,21),(0,0,0),(4,10,28),(0,7,30),(0,0,0),(0,0,0),(3,5,30),(0,13,28),(0,15,27),(0,0,0),(3,20,23),(2,7,30),(0,0,0),(0,0,0),(7,16,19),(0,0,31),(0,1,31),(0,0,0),(0,8,30),(0,2,31),(0,0,0),(0,0,0),(0,22,22),(1,22,22),(0,3,31),(0,0,0),(2,8,30),(2,2,31),(0,0,0),(0,0,0),(0,20,24),(0,4,31),(1,4,31),(0,0,0),(0,14,28),(0,9,30),(0,0,0),(0,0,0),(2,20,24),(0,12,29),(0,5,31),(0,0,0),(2,14,28),(2,9,30),(0,0,0),(0,0,0),(3,2,31),(2,12,29),(2,5,31),(0,0,0),(4,16,26),(0,6,31),(0,0,0),(0,0,0)]

def wits_1 : List (ℕ × ℕ × ℕ) := [(0,10,30),(1,10,30),(5,6,29),(0,0,0),(3,4,31),(2,6,31),(0,0,0),(0,0,0),(2,10,30),(0,15,28),(0,7,31),(0,0,0),(3,12,29),(0,22,23),(0,0,0),(0,0,0),(6,4,28),(0,21,24),(0,17,27),(0,0,0),(7,1,26),(0,11,30),(0,0,0),(0,0,0),(0,0,32),(0,1,32),(1,1,32),(0,0,0),(0,2,32),(1,2,32),(0,0,0),(0,0,0),(2,0,32),(0,3,32),(1,3,32),(0,0,0),(2,2,32),(0,14,29),(0,0,0),(0,0,0),(0,4,32),(1,4,32),(0,9,31),(0,0,0),(0,12,30),(1,12,30),(0,0,0),(0,0,0),(2,4,32),(0,5,32),(1,5,32),(0,0,0),(2,12,30),(0,18,27),(0,0,0),(0,0,0),(8,12,20),(2,5,32),(0,23,23),(0,0,0),(0,6,32),(0,10,31),(0,0,0),(0,0,0),(3,14,29),(7,19,19),(0,15,29),(0,0,0),(2,6,32),(0,13,30),(0,0,0),(0,0,0),(7,0,27),(0,7,32),(1,7,32),(0,0,0),(0,20,26),(1,20,26),(0,0,0),(0,0,0),(3,18,27),(2,7,32),(0,11,31),(0,0,0),(2,20,26),(3,23,23),(0,0,0),(0,0,0),(0,8,32),(0,0,33),(0,1,33),(0,0,0),(4,2,32),(0,2,33),(0,0,0),(0,0,0),(0,14,30),(0,16,29),(0,3,33),(0,0,0),(3,7,32),(2,2,33),(0,0,0),(0,0,0),(2,14,30),(0,4,33),(1,4,33),(0,0,0),(0,18,28),(0,22,25),(0,0,0),(0,0,0),(7,12,25),(2,4,33),(0,5,33),(0,0,0),(2,18,28),(0,21,26),(0,0,0),(0,0,0),(3,2,33),(6,8,29),(2,5,33),(0,0,0),(0,10,32),(0,6,33),(0,0,0),(0,0,0),(7,1,28),(0,20,27),(0,13,31),(0,0,0),(2,10,32),(2,6,33),(0,0,0),(0,0,0),(3,22,25),(2,20,27),(0,7,33),(0,0,0),(4,20,26),(3,5,33),(0,0,0),(0,0,0),(3,21,26),(0,11,32),(1,11,32),(0,0,0),(6,16,26),(5,0,32),(0,0,0),(0,0,0),(0,24,24),(0,8,33),(0,23,25),(0,0,0),(0,0,34),(0,1,34),(0,0,0),(0,0,0),(0,2,34),(1,2,34),(2,23,25),(0,0,0),(2,0,34),(0,3,34),(0,0,0),(0,0,0),(0,12,32),(1,12,32),(0,9,33),(0,0,0),(0,4,34),(1,4,34),(0,0,0),(0,0,0),(2,12,32),(6,0,31),(2,9,33),(0,0,0),(2,4,34),(0,5,34),(0,0,0),(0,0,0),(0,20,28),(1,20,28),(0,15,31),(0,0,0),(4,10,32),(0,10,33),(0,0,0),(0,0,0),(0,6,34),(0,13,32),(1,13,32),(0,0,0),(6,14,28),(2,10,33),(0,0,0),(0,0,0),(2,6,34),(0,24,25),(0,19,29),(0,0,0),(8,4,26),(0,7,34),(0,0,0),(0,0,0),(3,5,34),(2,24,25),(0,11,33),(0,0,0),(10,4,14),(0,22,27),(0,0,0),(0,0,0),(3,10,33),(0,16,31),(1,16,31),(0,0,0),(0,8,34),(1,8,34),(0,0,0),(0,0,0),(0,18,30),(0,0,35),(0,1,35),(0,0,0),(2,8,34),(0,2,35),(0,0,0),(0,0,0),(2,18,30),(0,12,33),(0,3,35),(0,0,0),(4,4,34),(0,9,34),(0,0,0),(0,0,0),(3,22,27),(0,4,35),(1,4,35),(0,0,0),(3,16,31),(2,9,34),(0,0,0),(0,0,0),(4,20,28),(0,15,32),(0,5,35),(0,0,0),(0,24,26),(1,24,26),(0,0,0),(0,0,0),(0,10,34),(1,10,34),(0,13,33),(0,0,0),(2,24,26),(0,6,35),(0,0,0),(0,0,0),(2,10,34),(4,24,25),(2,13,33),(0,0,0),(0,22,28),(1,22,28),(0,0,0),(0,0,0),(7,20,23),(8,19,20),(0,7,35),(0,0,0),(2,22,28),(0,11,34),(0,0,0),(0,0,0),(0,16,32),(1,16,32),(0,21,29),(0,0,0),(4,8,34),(0,14,33),(0,0,0),(0,0,0),(2,16,32),(0,8,35),(1,8,35),(0,0,0),(6,20,26),(2,14,33),(0,0,0),(0,0,0),(0,0,36),(0,1,36),(1,1,36),(0,0,0),(0,2,36),(0,25,26),(0,0,0),(0,0,0),(2,0,36),(0,3,36),(0,9,35),(0,0,0),(2,2,36),(2,25,26),(0,0,0),(0,0,0),(0,4,36),(0,17,32),(0,15,33),(0,0,0),(3,8,35),(5,6,34),(0,0,0),(0,0,0),(2,4,36),(0,5,36),(0,19,31),(0,0,0),(3,1,36),(0,10,35),(0,0,0),(0,0,0),(3,25,26),(2,5,36),(2,19,31),(0,0,0),(0,6,36),(1,6,36),(0,0,0),(0,0,0),(11,1,2),(10,9,16),(4,7,35),(0,0,0),(2,6,36),(0,21,30),(0,0,0),(0,0,0),(4,16,32),(0,7,36),(0,11,35),(0,0,0),(0,18,32),(1,18,32),(0,0,0),(0,0,0),(0,14,34),(1,14,34),(0,25,27),(0,0,0),(2,18,32),(8,2,29),(0,0,0),(0,0,0),(0,8,36),(0,20,31),(1,20,31),(0,0,0),(4,2,36),(4,25,26),(0,0,0),(0,0,0),(2,8,36),(0,0,37),(0,1,37),(0,0,0),(3,7,36),(0,2,37),(0,0,0),(0,0,0),(4,4,36),(0,9,36),(0,3,37),(0,0,0),(7,14,29),(0,15,34),(0,0,0),(0,0,0),(0,22,30),(0,4,37),(1,4,37),(0,0,0),(3,20,31),(2,15,34),(0,0,0),(0,0,0),(2,22,30),(2,4,37),(0,5,37),(0,0,0),(0,10,36),(1,10,36),(0,0,0),(0,0,0),(3,2,37),(7,23,23),(0,21,31),(0,0,0),(2,10,36),(0,6,37),(0,0,0),(0,0,0),(3,15,34),(0,25,28),(1,25,28),(0,0,0),(0,16,34),(0,18,33),(0,0,0),(0,0,0),(4,14,34),(0,11,36),(0,7,37),(0,0,0),(2,16,34),(0,14,35),(0,0,0),(0,0,0),(0,20,32),(1,20,32),(2,7,37),(0,0,0),(8,4,30),(0,23,30),(0,0,0),(0,0,0),(2,20,32),(0,8,37),(1,8,37),(0,0,0),(3,25,28),(2,23,30),(0,0,0),(0,0,0),(0,12,36),(1,12,36),(4,3,37),(0,0,0),(0,0,38),(0,1,38),(0,0,0),(0,0,0),(0,2,38),(1,2,38),(0,9,37),(0,0,0),(2,0,38),(0,3,38),(0,0,0),(0,0,0),(2,2,38),(5,6,36),(0,27,27),(0,0,0),(0,4,38),(1,4,38),(0,0,0),(0,0,0),(10,8,20),(0,13,36),(0,25,29),(0,0,0),(2,4,38),(0,5,38),(0,0,0),(0,0,0),(3,1,38),(2,13,36),(2,25,29),(0,0,0),(0,24,30),(1,24,30),(0,0,0),(0,0,0),(0,6,38),(0,16,35),(1,16,35),(0,0,0),(2,24,30),(3,27,27),(0,0,0),(0,0,0),(2,6,38),(0,20,33),(0,11,37),(0,0,0),(0,14,36),(0,7,38),(0,0,0),(0,0,0),(3,5,38),(2,20,33),(2,11,37),(0,0,0),(2,14,36),(2,7,38),(0,0,0),(0,0,0),(4,12,36),(6,8,35),(5,15,34),(0,0,0),(0,8,38),(1,8,38),(0,0,0),(0,0,0),(4,2,38),(0,12,37),(0,17,35),(0,0,0),(2,8,38),(0,19,34),(0,0,0),(0,0,0),(3,7,38),(0,0,39),(0,1,39),(0,0,0),(4,4,38),(0,2,39),(0,0,0),(0,0,0),(6,4,36),(2,0,39),(0,3,39),(0,0,0),(7,10,33),(2,2,39),(0,0,0),(0,0,0),(7,13,32),(0,4,39),(0,13,37),(0,0,0),(3,12,37),(3,17,35),(0,0,0),(0,0,0),(0,10,38),(1,10,38),(0,5,39),(0,0,0),(3,0,39),(0,18,35),(0,0,0),(0,0,0),(0,16,36),(0,23,32),(1,23,32),(0,0,0),(0,20,34),(0,6,39),(0,0,0),(0,0,0),(2,16,36),(2,23,32),(6,11,35),(0,0,0),(2,20,34),(0,11,38),(0,0,0),(0,0,0),(0,28,28),(1,28,28),(0,7,39),(0,0,0),(4,8,38),(0,22,33),(0,0,0),(0,0,0),(0,26,30),(1,26,30),(2,7,39),(0,0,0),(3,23,32),(2,22,33),(0,0,0),(0,0,0),(2,26,30),(0,8,39),(0,19,35),(0,0,0),(0,12,38),(1,12,38),(0,0,0),(0,0,0),(3,11,38),(2,8,39),(0,15,37),(0,0,0),(2,12,38),(0,21,34),(0,0,0),(0,0,0),(0,0,40),(0,1,40),(0,9,39),(0,0,0),(0,2,40),(1,2,40),(0,0,0),(0,0,0),(2,0,40),(0,3,40),(1,3,40),(0,0,0),(2,2,40),(0,13,38),(0,0,0),(0,0,0),(0,4,40),(1,4,40),(0,23,33),(0,0,0),(0,18,36),(0,10,39),(0,0,0),(0,0,0),(2,4,40),(0,5,40),(1,5,40),(0,0,0),(2,18,36),(0,27,30),(0,0,0),(0,0,0),(4,28,28),(2,5,40),(4,7,39),(0,0,0),(0,6,40),(0,26,31),(0,0,0),(0,0,0),(0,14,38),(1,14,38),(0,11,39),(0,0,0),(2,6,40),(2,26,31),(0,0,0),(0,0,0),(2,14,38),(0,7,40),(1,7,40),(0,0,0),(3,5,40),(10,13,22),(0,0,0),(0,0,0),(3,27,30),(0,19,36),(0,17,37),(0,0,0),(6,0,38),(4,21,34),(0,0,0),(0,0,0),(0,8,40),(0,12,39),(0,21,35),(0,0,0),(4,2,40),(0,15,38),(0,0,0),(0,0,0),(2,8,40),(2,12,39),(2,21,35),(0,0,0),(3,7,40),(2,15,38),(0,0,0),(0,0,0),(4,4,40),(0,0,41),(0,1,41),(0,0,0),(0,28,30),(0,2,41),(0,0,0),(0,0,0),(7,7,36),(2,0,41),(0,3,41),(0,0,0),(2,28,30),(0,18,37),(0,0,0),(0,0,0),(0,20,36),(0,4,41),(1,4,41),(0,0,0),(0,10,40),(1,10,40),(0,0,0),(0,0,0),(2,20,36),(2,4,41),(0,5,41),(0,0,0),(2,10,40),(0,22,35),(0,0,0),(0,0,0),(3,2,41),(4,7,40),(0,25,33),(0,0,0),(7,2,37),(0,6,41),(0,0,0),(0,0,0),(3,18,37),(0,11,40),(1,11,40),(0,0,0),(3,4,41),(2,6,41),(0,0,0),(0,0,0),(4,8,40),(2,11,40),(0,7,41),(0,0,0),(0,24,34),(0,17,38),(0,0,0),(0,0,0),(3,22,35),(0,21,36),(1,21,36),(0,0,0),(2,24,34),(0,29,30),(0,0,0),(0,0,0),(0,12,40),(0,8,41),(0,15,39),(0,0,0),(3,11,40),(2,29,30),(0,0,0),(0,0,0),(2,12,40),(0,27,32),(0,23,35),(0,0,0),(7,18,33),(3,7,41),(0,0,0),(0,0,0),(3,17,38),(2,27,32),(0,9,41),(0,0,0),(0,0,42),(0,1,42),(0,0,0),(0,0,0),(0,2,42),(0,13,40),(1,13,40),(0,0,0),(2,0,42),(0,3,42),(0,0,0),(0,0,0),(2,2,42),(0,16,39),(1,16,39),(0,0,0),(0,4,42),(0,10,41),(0,0,0),(0,0,0),(6,28,28),(2,16,39),(6,7,39),(0,0,0),(2,4,42),(0,5,42),(0,0,0),(0,0,0),(3,1,42),(7,9,37),(4,7,41),(0,0,0),(0,14,40),(1,14,40),(0,0,0),(0,0,0),(0,6,42),(0,24,35),(0,11,41),(0,0,0),(2,14,40),(0,19,38),(0,0,0),(0,0,0),(0,28,32),(1,28,32),(0,17,39),(0,0,0),(7,5,38),(0,7,42),(0,0,0),(0,0,0),(2,28,32),(4,27,32),(0,27,33),(0,0,0),(6,2,40),(2,7,42),(0,0,0),(0,0,0),(7,16,35),(0,12,41),(1,12,41),(0,0,0),(0,8,42),(1,8,42),(0,0,0),(0,0,0),(0,26,34),(1,26,34),(5,22,35),(0,0,0),(2,8,42),(3,17,39),(0,0,0),(0,0,0),(2,26,34),(4,16,39),(5,6,41),(0,0,0),(0,20,38),(0,9,42),(0,0,0),(0,0,0),(10,8,28),(0,0,43),(0,1,43),(0,0,0),(2,20,38),(0,2,43),(0,0,0),(0,0,0),(0,16,40),(1,16,40),(0,3,43),(0,0,0),(4,14,40),(0,30,31),(0,0,0),(0,0,0),(0,10,42),(0,4,43),(1,4,43),(0,0,0),(7,2,39),(2,30,31),(0,0,0),(0,0,0),(0,24,36),(0,28,33),(0,5,43),(0,0,0),(3,0,43),(0,14,41),(0,0,0),(0,0,0),(2,24,36),(2,28,33),(0,19,39),(0,0,0),(10,10,28),(0,6,43),(0,0,0),(0,0,0),(3,30,31),(0,17,40),(1,17,40),(0,0,0),(3,4,43),(2,6,43),(0,0,0),(0,0,0),(4,26,34),(2,17,40),(0,7,43),(0,0,0),(3,28,33),(0,26,35),(0,0,0),(0,0,0),(3,14,41),(5,4,42),(0,15,41),(0,0,0),(0,12,42),(1,12,42),(0,0,0),(0,0,0),(3,6,43),(0,8,43),(1,8,43),(0,0,0),(2,12,42),(4,2,43),(0,0,0),(0,0,0),(4,16,40),(0,20,39),(0,31,31),(0,0,0),(0,18,40),(1,18,40),(0,0,0),(0,0,0),(0,22,38),(1,22,38),(0,9,43),(0,0,0),(2,18,40),(0,13,42),(0,0,0),(0,0,0),(0,0,44),(0,1,44),(1,1,44),(0,0,0),(0,2,44),(1,2,44),(0,0,0),(0,0,0),(2,0,44),(0,3,44),(1,3,44),(0,0,0),(2,2,44),(0,10,43),(0,0,0),(0,0,0),(0,4,44),(1,4,44),(0,27,35),(0,0,0),(7,13,38),(2,10,43),(0,0,0),(0,0,0),(0,14,42),(0,5,44),(0,21,39),(0,0,0),(3,1,44),(4,26,35),(0,0,0),(0,0,0),(2,14,42),(2,5,44),(0,11,43),(0,0,0),(0,6,44),(0,23,38),(0,0,0),(0,0,0),(3,10,43),(4,8,43),(2,11,43),(0,0,0),(2,6,44),(2,23,38),(0,0,0),(0,0,0),(6,2,42),(0,7,44),(1,7,44),(0,0,0),(3,5,44),(0,15,42),(0,0,0),(0,0,0),(4,22,38),(0,12,43),(0,25,37),(0,0,0),(6,4,42),(0,29,34),(0,0,0),(0,0,0)]

def wits_2 : List (ℕ × ℕ × ℕ) := [(0,8,44),(1,8,44),(2,25,37),(0,0,0),(4,2,44),(0,18,41),(0,0,0),(0,0,0),(2,8,44),(0,28,35),(1,28,35),(0,0,0),(3,7,44),(2,18,41),(0,0,0),(0,0,0),(3,15,42),(0,9,44),(0,13,43),(0,0,0),(0,16,42),(1,16,42),(0,0,0),(0,0,0),(3,29,34),(0,0,45),(0,1,45),(0,0,0),(2,16,42),(0,2,45),(0,0,0),(0,0,0),(3,18,41),(2,0,45),(0,3,45),(0,0,0),(0,10,44),(1,10,44),(0,0,0),(0,0,0),(7,4,41),(0,4,45),(0,19,41),(0,0,0),(2,10,44),(0,14,43),(0,0,0),(0,0,0),(0,32,32),(1,32,32),(0,5,45),(0,0,0),(3,0,45),(0,17,42),(0,0,0),(0,0,0),(0,30,34),(0,11,44),(1,11,44),(0,0,0),(6,20,38),(0,6,45),(0,0,0),(0,0,0),(2,30,34),(2,11,44),(0,29,35),(0,0,0),(3,4,45),(0,25,38),(0,0,0),(0,0,0),(3,14,43),(4,28,35),(0,7,45),(0,0,0),(7,17,38),(2,25,38),(0,0,0),(0,0,0),(0,12,44),(0,20,41),(1,20,41),(0,0,0),(0,22,40),(1,22,40),(0,0,0),(0,0,0),(0,18,42),(0,8,45),(1,8,45),(0,0,0),(2,22,40),(3,29,35),(0,0,0),(0,0,0),(2,18,42),(0,24,39),(0,27,37),(0,0,0),(4,10,44),(3,7,45),(0,0,0),(0,0,0),(11,17,22),(0,13,44),(0,9,45),(0,0,0),(3,20,41),(4,14,43),(0,0,0),(0,0,0),(4,32,32),(0,32,33),(1,32,33),(0,0,0),(0,0,46),(0,1,46),(0,0,0),(0,0,0),(0,2,46),(1,2,46),(0,21,41),(0,0,0),(2,0,46),(0,3,46),(0,0,0),(0,0,0),(2,2,46),(0,23,40),(1,23,40),(0,0,0),(0,4,46),(1,4,46),(0,0,0),(0,0,0),(0,0,0),(0,29,36),(0,17,43),(0,0,0),(2,4,46),(0,5,46),(0,0,0),(0,0,0),(3,1,46),(2,29,36),(0,11,45),(0,0,0),(4,22,40),(2,5,46),(0,0,0),(0,0,0),(0,6,46),(0,28,37),(1,28,37),(0,0,0),(3,23,40),(10,1,34),(0,0,0),(0,0,0),(2,6,46),(0,15,44),(1,15,44),(0,0,0),(0,20,42),(0,7,46),(0,0,0),(0,0,0),(3,5,46),(0,12,45),(1,12,45),(0,0,0),(2,20,42),(0,18,43),(0,0,0),(0,0,0),(0,24,40),(1,24,40),(0,33,33),(0,0,0),(0,8,46),(1,8,46),(0,0,0),(0,0,0),(2,24,40),(12,4,21),(0,31,35),(0,0,0),(2,8,46),(4,3,46),(0,0,0),(0,0,0),(0,16,44),(1,16,44),(0,13,45),(0,0,0),(0,30,36),(0,9,46),(0,0,0),(0,0,0),(2,16,44),(4,29,36),(2,13,45),(0,0,0),(2,30,36),(0,21,42),(0,0,0),(0,0,0),(7,4,43),(0,0,47),(0,1,47),(0,0,0),(8,10,40),(0,2,47),(0,0,0),(0,0,0),(0,10,46),(1,10,46),(0,3,47),(0,0,0),(7,14,41),(0,14,45),(0,0,0),(0,0,0),(2,10,46),(0,4,47),(1,4,47),(0,0,0),(0,28,38),(1,28,38),(0,0,0),(0,0,0),(3,21,42),(2,4,47),(0,5,47),(0,0,0),(2,28,38),(0,11,46),(0,0,0),(0,0,0),(3,2,47),(5,0,46),(2,5,47),(0,0,0),(4,8,46),(0,6,47),(0,0,0),(0,0,0),(0,22,42),(0,20,43),(0,15,45),(0,0,0),(3,4,47),(2,6,47),(0,0,0),(0,0,0),(2,22,42),(0,24,41),(0,7,47),(0,0,0),(0,12,46),(1,12,46),(0,0,0),(0,0,0),(3,11,46),(2,24,41),(2,7,47),(0,0,0),(2,12,46),(0,30,37),(0,0,0),(0,0,0),(3,6,47),(0,8,47),(1,8,47),(0,0,0),(0,26,40),(1,26,40),(0,0,0),(0,0,0),(4,10,46),(0,16,45),(1,16,45),(0,0,0),(2,26,40),(0,13,46),(0,0,0),(0,0,0),(7,3,44),(2,16,45),(0,9,47),(0,0,0),(4,28,38),(0,23,42),(0,0,0),(0,0,0),(3,30,37),(0,19,44),(1,19,44),(0,0,0),(3,8,47),(2,23,42),(0,0,0),(0,0,0),(0,0,48),(0,1,48),(0,25,41),(0,0,0),(0,2,48),(0,10,47),(0,0,0),(0,0,0),(0,14,46),(0,3,48),(0,17,45),(0,0,0),(2,2,48),(2,10,47),(0,0,0),(0,0,0),(0,4,48),(1,4,48),(2,17,45),(0,0,0),(3,19,44),(8,7,42),(0,0,0),(0,0,0),(2,4,48),(0,5,48),(0,11,47),(0,0,0),(3,1,48),(0,22,43),(0,0,0),(0,0,0),(0,20,44),(1,20,44),(2,11,47),(0,0,0),(0,6,48),(0,15,46),(0,0,0),(0,0,0),(0,30,38),(1,30,38),(5,14,45),(0,0,0),(2,6,48),(0,18,45),(0,0,0),(0,0,0),(2,30,38),(0,7,48),(1,7,48),(0,0,0),(3,5,48),(0,26,41),(0,0,0),(0,0,0),(3,22,43),(2,7,48),(0,29,39),(0,0,0),(11,3,32),(2,26,41),(0,0,0),(0,0,0),(0,8,48),(1,8,48),(2,29,39),(0,0,0),(0,16,46),(1,16,46),(0,0,0),(0,0,0),(2,8,48),(0,21,44),(0,13,47),(0,0,0),(2,16,46),(0,34,35),(0,0,0),(0,0,0),(0,28,40),(0,9,48),(0,19,45),(0,0,0),(7,14,43),(0,25,42),(0,0,0),(0,0,0),(2,28,40),(0,32,37),(1,32,37),(0,0,0),(6,8,46),(2,25,42),(0,0,0),(0,0,0),(4,20,44),(0,0,49),(0,1,49),(0,0,0),(0,10,48),(0,2,49),(0,0,0),(0,0,0),(3,34,35),(2,0,49),(0,3,49),(0,0,0),(2,10,48),(2,2,49),(0,0,0),(0,0,0),(3,25,42),(0,4,49),(1,4,49),(0,0,0),(0,22,44),(0,30,39),(0,0,0),(0,0,0),(7,20,41),(0,11,48),(0,5,49),(0,0,0),(2,22,44),(2,30,39),(0,0,0),(0,0,0),(3,2,49),(2,11,48),(0,15,47),(0,0,0),(4,16,46),(0,6,49),(0,0,0),(0,0,0),(0,18,46),(0,29,40),(1,29,40),(0,0,0),(3,4,49),(2,6,49),(0,0,0),(0,0,0),(0,12,48),(1,12,48),(0,7,49),(0,0,0),(0,34,36),(1,34,36),(0,0,0),(0,0,0),(2,12,48),(4,32,37),(0,33,37),(0,0,0),(2,34,36),(3,15,47),(0,0,0),(0,0,0),(3,6,49),(0,8,49),(0,21,45),(0,0,0),(0,32,38),(1,32,38),(0,0,0),(0,0,0),(7,23,40),(0,13,48),(0,25,43),(0,0,0),(2,32,38),(0,19,46),(0,0,0),(0,0,0),(7,29,36),(2,13,48),(0,9,49),(0,0,0),(4,22,44),(2,19,46),(0,0,0),(0,0,0),(11,1,34),(4,11,48),(2,9,49),(0,0,0),(3,8,49),(0,27,42),(0,0,0),(0,0,0),(7,28,37),(5,16,46),(0,17,47),(0,0,0),(0,0,50),(0,1,50),(0,0,0),(0,0,0),(0,2,50),(1,2,50),(2,17,47),(0,0,0),(2,0,50),(0,3,50),(0,0,0),(0,0,0),(0,24,44),(1,24,44),(4,7,49),(0,0,0),(0,4,50),(1,4,50),(0,0,0),(0,0,0),(2,24,44),(0,35,36),(0,11,49),(0,0,0),(2,4,50),(0,5,50),(0,0,0),(0,0,0),(3,1,50),(0,15,48),(1,15,48),(0,0,0),(4,32,38),(0,18,47),(0,0,0),(0,0,0),(0,6,50),(1,6,50),(4,25,43),(0,0,0),(7,9,46),(2,18,47),(0,0,0),(0,0,0),(2,6,50),(0,12,49),(1,12,49),(0,0,0),(0,28,42),(0,7,50),(0,0,0),(0,0,0),(3,5,50),(2,12,49),(0,23,45),(0,0,0),(2,28,42),(0,21,46),(0,0,0),(0,0,0),(0,16,48),(0,25,44),(1,25,44),(0,0,0),(0,8,50),(1,8,50),(0,0,0),(0,0,0),(2,16,48),(2,25,44),(0,13,49),(0,0,0),(2,8,50),(4,3,50),(0,0,0),(0,0,0),(3,7,50),(5,34,36),(0,27,43),(0,0,0),(4,4,50),(0,9,50),(0,0,0),(0,0,0),(3,21,46),(4,35,36),(2,27,43),(0,0,0),(3,25,44),(2,9,50),(0,0,0),(0,0,0),(0,36,36),(0,17,48),(0,35,37),(0,0,0),(8,22,40),(0,14,49),(0,0,0),(0,0,0),(0,10,50),(0,0,51),(0,1,51),(0,0,0),(10,2,40),(0,2,51),(0,0,0),(0,0,0),(2,10,50),(0,20,47),(0,3,51),(0,0,0),(0,26,44),(1,26,44),(0,0,0),(0,0,0),(7,8,47),(0,4,51),(1,4,51),(0,0,0),(2,26,44),(0,11,50),(0,0,0),(0,0,0),(0,32,40),(1,32,40),(0,5,51),(0,0,0),(0,18,48),(1,18,48),(0,0,0),(0,0,0),(2,32,40),(0,28,43),(1,28,43),(0,0,0),(2,18,48),(0,6,51),(0,0,0),(0,0,0),(7,19,44),(2,28,43),(0,31,41),(0,0,0),(0,12,50),(0,23,46),(0,0,0),(0,0,0),(3,11,50),(7,25,41),(0,7,51),(0,0,0),(2,12,50),(2,23,46),(0,0,0),(0,0,0),(4,36,36),(0,16,49),(1,16,49),(0,0,0),(3,28,43),(4,14,49),(0,0,0),(0,0,0),(0,30,42),(0,8,51),(1,8,51),(0,0,0),(6,34,36),(0,13,50),(0,0,0),(0,0,0),(2,30,42),(2,8,51),(4,3,51),(0,0,0),(4,26,44),(0,34,39),(0,0,0),(0,0,0),(0,0,0),(4,4,51),(0,9,51),(0,0,0),(3,16,49),(2,34,39),(0,0,0),(0,0,0),(4,32,40),(0,33,40),(0,17,49),(0,0,0),(0,24,46),(0,22,47),(0,0,0),(0,0,0),(0,14,50),(1,14,50),(2,17,49),(0,0,0),(2,24,46),(0,10,51),(0,0,0),(0,0,0),(0,0,52),(0,1,52),(1,1,52),(0,0,0),(0,2,52),(1,2,52),(0,0,0),(0,0,0),(2,0,52),(0,3,52),(1,3,52),(0,0,0),(2,2,52),(3,17,49),(0,0,0),(0,0,0),(0,4,52),(1,4,52),(0,11,51),(0,0,0),(7,34,35),(0,15,50),(0,0,0),(0,0,0),(2,4,52),(0,5,52),(1,5,52),(0,0,0),(3,1,52),(2,15,50),(0,0,0),(0,0,0),(7,32,37),(2,5,52),(0,23,47),(0,0,0),(0,6,52),(0,25,46),(0,0,0),(0,0,0),(7,0,49),(0,12,51),(0,35,39),(0,0,0),(2,6,52),(0,30,43),(0,0,0),(0,0,0),(3,15,50),(0,7,52),(0,27,45),(0,0,0),(0,16,50),(1,16,50),(0,0,0),(0,0,0),(4,14,50),(2,7,52),(0,19,49),(0,0,0),(2,16,50),(3,23,47),(0,0,0),(0,0,0),(0,8,52),(1,8,52),(0,13,51),(0,0,0),(3,12,51),(3,35,39),(0,0,0),(0,0,0),(2,8,52),(0,29,44),(1,29,44),(0,0,0),(3,7,52),(3,27,45),(0,0,0),(0,0,0),(4,4,52),(0,9,52),(1,9,52),(0,0,0),(0,22,48),(0,17,50),(0,0,0),(0,0,0),(0,26,46),(1,26,46),(5,13,50),(0,0,0),(2,22,48),(0,14,51),(0,0,0),(0,0,0),(2,26,46),(0,20,49),(1,20,49),(0,0,0),(0,10,52),(1,10,52),(0,0,0),(0,0,0),(6,36,36),(0,0,53),(0,1,53),(0,0,0),(2,10,52),(0,2,53),(0,0,0),(0,0,0),(3,17,50),(0,36,39),(0,3,53),(0,0,0),(4,16,50),(2,2,53),(0,0,0),(0,0,0),(0,18,50),(0,4,53),(0,15,51),(0,0,0),(3,20,49),(5,0,52),(0,0,0),(0,0,0),(2,18,50),(0,23,48),(0,5,53),(0,0,0),(0,30,44),(0,34,41),(0,0,0),(0,0,0),(3,2,53),(2,23,48),(0,21,49),(0,0,0),(2,30,44),(0,6,53),(0,0,0),(0,0,0),(0,12,52),(1,12,52),(2,21,49),(0,0,0),(3,4,53),(0,33,42),(0,0,0),(0,0,0),(2,12,52),(0,16,51),(0,7,53),(0,0,0),(3,23,48),(0,19,50),(0,0,0),(0,0,0),(3,34,41),(2,16,51),(0,29,45),(0,0,0),(4,10,52),(2,19,50),(0,0,0),(0,0,0),(3,6,53),(0,8,53),(1,8,53),(0,0,0),(7,18,47),(4,2,53),(0,0,0),(0,0,0),(0,24,48),(1,24,48),(4,3,53),(0,0,0),(3,16,51),(0,22,49),(0,0,0),(0,0,0),(0,38,38),(1,38,38),(0,9,53),(0,0,0),(7,7,50),(2,22,49),(0,0,0),(0,0,0),(0,36,40),(0,31,44),(1,31,44),(0,0,0),(0,14,52),(1,14,52),(0,0,0),(0,0,0),(2,36,40),(2,31,44),(0,35,41),(0,0,0),(2,14,52),(0,10,53),(0,0,0),(0,0,0),(3,22,49),(5,22,48),(2,35,41),(0,0,0),(0,0,54),(0,1,54),(0,0,0),(0,0,0),(0,2,54),(1,2,54),(4,7,53),(0,0,0),(2,0,54),(0,3,54),(0,0,0),(0,0,0),(2,2,54),(0,15,52),(0,11,53),(0,0,0),(0,4,54),(1,4,54),(0,0,0),(0,0,0),(3,10,53),(2,15,52),(0,27,47),(0,0,0),(2,4,54),(0,5,54),(0,0,0),(0,0,0),(3,1,54),(6,5,52),(2,27,47),(0,0,0),(7,2,51),(2,5,54),(0,0,0),(0,0,0),(0,6,54),(0,12,53),(1,12,53),(0,0,0),(3,15,52),(0,29,46),(0,0,0),(0,0,0),(0,16,52),(1,16,52),(0,19,51),(0,0,0),(4,14,52),(0,7,54),(0,0,0),(0,0,0),(2,16,52),(0,37,40),(1,37,40),(0,0,0),(6,16,50),(2,7,54),(0,0,0),(0,0,0),(7,28,43),(0,24,49),(0,13,53),(0,0,0),(0,8,54),(1,8,54),(0,0,0),(0,0,0),(0,22,50),(1,22,50),(0,31,45),(0,0,0),(2,8,54),(0,35,42),(0,0,0),(0,0,0),(2,22,50),(0,17,52),(1,17,52),(0,0,0),(3,37,40),(0,9,54),(0,0,0),(0,0,0)]

def wits_3 : List (ℕ × ℕ × ℕ) := [(7,16,49),(0,20,51),(1,20,51),(0,0,0),(3,24,49),(0,14,53),(0,0,0),(0,0,0),(6,26,46),(2,20,51),(5,22,49),(0,0,0),(7,13,50),(2,14,53),(0,0,0),(0,0,0),(0,10,54),(1,10,54),(10,13,43),(0,0,0),(3,17,52),(4,29,46),(0,0,0),(0,0,0),(2,10,54),(0,0,55),(0,1,55),(0,0,0),(0,18,52),(0,2,55),(0,0,0),(0,0,0),(3,14,53),(0,27,48),(0,3,55),(0,0,0),(2,18,52),(0,11,54),(0,0,0),(0,0,0),(6,18,50),(0,4,55),(0,21,51),(0,0,0),(0,38,40),(1,38,40),(0,0,0),(0,0,0),(4,22,50),(0,32,45),(0,5,55),(0,0,0),(2,38,40),(3,1,55),(0,0,0),(0,0,0),(3,2,55),(2,32,45),(2,5,55),(0,0,0),(0,12,54),(0,6,55),(0,0,0),(0,0,0),(3,11,54),(0,16,53),(1,16,53),(0,0,0),(2,12,54),(2,6,55),(0,0,0),(0,0,0),(7,5,52),(2,16,53),(0,7,55),(0,0,0),(0,24,50),(0,26,49),(0,0,0),(0,0,0),(4,10,54),(7,23,47),(2,7,55),(0,0,0),(2,24,50),(0,13,54),(0,0,0),(0,0,0),(0,28,48),(0,8,55),(1,8,55),(0,0,0),(0,34,44),(1,34,44),(0,0,0),(0,0,0),(2,28,48),(2,8,55),(0,17,53),(0,0,0),(2,34,44),(3,7,55),(0,0,0),(0,0,0),(0,20,52),(1,20,52),(0,9,55),(0,0,0),(4,38,40),(0,30,47),(0,0,0),(0,0,0),(0,14,54),(1,14,54),(0,33,45),(0,0,0),(3,8,55),(2,30,47),(0,0,0),(0,0,0),(2,14,54),(0,39,40),(1,39,40),(0,0,0),(4,12,54),(0,10,55),(0,0,0),(0,0,0),(7,9,52),(2,39,40),(0,23,51),(0,0,0),(6,0,54),(0,18,53),(0,0,0),(0,0,0),(0,0,56),(0,1,56),(1,1,56),(0,0,0),(0,2,56),(0,15,54),(0,0,0),(0,0,0),(2,0,56),(0,3,56),(0,11,55),(0,0,0),(2,2,56),(2,15,54),(0,0,0),(0,0,0),(0,4,56),(1,4,56),(2,11,55),(0,0,0),(4,34,44),(3,23,51),(0,0,0),(0,0,0),(2,4,56),(0,5,56),(1,5,56),(0,0,0),(3,1,56),(10,7,46),(0,0,0),(0,0,0),(3,15,54),(0,12,55),(0,19,53),(0,0,0),(0,6,56),(1,6,56),(0,0,0),(0,0,0),(0,26,50),(0,24,51),(1,24,51),(0,0,0),(2,6,56),(0,34,45),(0,0,0),(0,0,0),(2,26,50),(0,7,56),(1,7,56),(0,0,0),(0,22,52),(1,22,52),(0,0,0),(0,0,0),(10,16,44),(2,7,56),(0,13,55),(0,0,0),(2,22,52),(3,19,53),(0,0,0),(0,0,0),(0,8,56),(1,8,56),(0,39,41),(0,0,0),(0,30,48),(0,17,54),(0,0,0),(0,0,0),(0,38,42),(0,20,53),(1,20,53),(0,0,0),(2,30,48),(2,17,54),(0,0,0),(0,0,0),(2,38,42),(0,9,56),(0,37,43),(0,0,0),(8,2,52),(0,14,55),(0,0,0),(0,0,0),(0,0,0),(2,9,56),(0,25,51),(0,0,0),(7,22,49),(0,27,50),(0,0,0),(0,0,0),(0,36,44),(0,23,52),(1,23,52),(0,0,0),(0,10,56),(1,10,56),(0,0,0),(0,0,0),(0,18,54),(1,18,54),(0,29,49),(0,0,0),(2,10,56),(3,37,43),(0,0,0),(0,0,0),(2,18,54),(0,0,57),(0,1,57),(0,0,0),(4,22,52),(0,2,57),(0,0,0),(0,0,0),(3,27,50),(0,11,56),(0,3,57),(0,0,0),(3,23,52),(2,2,57),(0,0,0),(0,0,0),(4,8,56),(0,4,57),(1,4,57),(0,0,0),(4,30,48),(3,29,49),(0,0,0),(0,0,0),(0,34,46),(1,34,46),(0,5,57),(0,0,0),(3,0,57),(0,19,54),(0,0,0),(0,0,0),(0,12,56),(0,16,55),(1,16,55),(0,0,0),(0,28,50),(0,6,57),(0,0,0),(0,0,0),(2,12,56),(2,16,55),(4,25,51),(0,0,0),(2,28,50),(0,22,53),(0,0,0),(0,0,0),(4,36,44),(4,23,52),(0,7,57),(0,0,0),(4,10,56),(0,30,49),(0,0,0),(0,0,0),(3,19,54),(0,13,56),(1,13,56),(0,0,0),(3,16,55),(2,30,49),(0,0,0),(0,0,0),(3,6,57),(0,8,57),(0,17,55),(0,0,0),(0,20,54),(1,20,54),(0,0,0),(0,0,0),(3,22,53),(0,36,45),(1,36,45),(0,0,0),(2,20,54),(3,7,57),(0,0,0),(0,0,0),(0,32,48),(0,25,52),(0,9,57),(0,0,0),(0,14,56),(1,14,56),(0,0,0),(0,0,0),(2,32,48),(2,25,52),(0,23,53),(0,0,0),(2,14,56),(0,29,50),(0,0,0),(0,0,0),(4,12,56),(4,16,55),(2,23,53),(0,0,0),(3,36,45),(0,10,57),(0,0,0),(0,0,0),(6,0,56),(6,1,56),(5,27,50),(0,0,0),(3,25,52),(0,21,54),(0,0,0),(0,0,0),(8,12,52),(0,15,56),(0,31,49),(0,0,0),(0,0,58),(0,1,58),(0,0,0),(0,0,0),(0,2,58),(1,2,58),(0,11,57),(0,0,0),(2,0,58),(0,3,58),(0,0,0),(0,0,0),(2,2,58),(4,8,57),(2,11,57),(0,0,0),(0,4,58),(1,4,58),(0,0,0),(0,0,0),(3,21,54),(0,24,53),(0,19,55),(0,0,0),(2,4,58),(0,5,58),(0,0,0),(0,0,0),(0,16,56),(0,12,57),(0,37,45),(0,0,0),(4,14,56),(2,5,58),(0,0,0),(0,0,0),(0,6,58),(1,6,58),(2,37,45),(0,0,0),(6,22,52),(4,29,50),(0,0,0),(0,0,0),(2,6,58),(5,28,50),(5,6,57),(0,0,0),(0,36,46),(0,7,58),(0,0,0),(0,0,0),(3,5,58),(7,7,55),(0,13,57),(0,0,0),(2,36,46),(2,7,58),(0,0,0),(0,0,0),(6,38,42),(0,17,56),(1,17,56),(0,0,0),(0,8,58),(1,8,58),(0,0,0),(0,0,0),(4,2,58),(0,27,52),(0,25,53),(0,0,0),(2,8,58),(4,3,58),(0,0,0),(0,0,0),(3,7,58),(2,27,52),(0,29,51),(0,0,0),(4,4,58),(0,9,58),(0,0,0),(0,0,0),(6,36,44),(0,40,43),(1,40,43),(0,0,0),(3,17,56),(2,9,58),(0,0,0),(0,0,0),(4,16,56),(0,39,44),(1,39,44),(0,0,0),(0,18,56),(0,31,50),(0,0,0),(0,0,0),(0,10,58),(1,10,58),(0,21,55),(0,0,0),(2,18,56),(0,38,45),(0,0,0),(0,0,0),(2,10,58),(6,11,56),(0,15,57),(0,0,0),(3,40,43),(2,38,45),(0,0,0),(0,0,0),(7,1,56),(0,0,59),(0,1,59),(0,0,0),(3,39,44),(0,2,59),(0,0,0),(0,0,0),(0,28,52),(1,28,52),(0,3,59),(0,0,0),(0,24,54),(1,24,54),(0,0,0),(0,0,0),(2,28,52),(0,4,59),(1,4,59),(0,0,0),(2,24,54),(0,30,51),(0,0,0),(0,0,0),(7,5,56),(0,16,57),(0,5,59),(0,0,0),(0,12,58),(0,22,55),(0,0,0),(0,0,0),(3,2,59),(2,16,57),(2,5,59),(0,0,0),(2,12,58),(0,6,59),(0,0,0),(0,0,0),(7,24,51),(4,39,44),(10,11,49),(0,0,0),(0,32,50),(1,32,50),(0,0,0),(0,0,0),(0,42,42),(0,35,48),(0,7,59),(0,0,0),(2,32,50),(0,13,58),(0,0,0),(0,0,0),(0,20,56),(1,20,56),(0,17,57),(0,0,0),(8,18,52),(0,25,54),(0,0,0),(0,0,0),(2,20,56),(0,8,59),(0,39,45),(0,0,0),(6,14,56),(2,25,54),(0,0,0),(0,0,0),(4,28,52),(2,8,59),(0,23,55),(0,0,0),(3,35,48),(0,34,49),(0,0,0),(0,0,0),(0,14,58),(1,14,58),(0,9,59),(0,0,0),(7,14,55),(2,34,49),(0,0,0),(0,0,0),(2,14,58),(4,16,57),(2,9,59),(0,0,0),(3,8,59),(0,18,57),(0,0,0),(0,0,0),(7,23,52),(0,21,56),(0,37,47),(0,0,0),(6,0,58),(0,10,59),(0,0,0),(0,0,0),(3,34,49),(2,21,56),(2,37,47),(0,0,0),(4,32,50),(0,15,58),(0,0,0),(0,0,0),(0,26,54),(0,28,53),(1,28,53),(0,0,0),(6,4,58),(2,15,58),(0,0,0),(0,0,0),(0,0,60),(0,1,60),(0,11,59),(0,0,0),(0,2,60),(1,2,60),(0,0,0),(0,0,0),(2,0,60),(0,3,60),(0,19,57),(0,0,0),(2,2,60),(0,42,43),(0,0,0),(0,0,0),(0,4,60),(0,41,44),(1,41,44),(0,0,0),(0,16,58),(1,16,58),(0,0,0),(0,0,0),(2,4,60),(0,5,60),(0,35,49),(0,0,0),(2,16,58),(3,11,59),(0,0,0),(0,0,0),(15,1,16),(2,5,60),(2,35,49),(0,0,0),(0,6,60),(0,39,46),(0,0,0),(0,0,0),(3,42,43),(4,21,56),(4,37,47),(0,0,0),(2,6,60),(0,27,54),(0,0,0),(0,0,0),(7,13,56),(0,7,60),(0,13,59),(0,0,0),(3,5,60),(0,17,58),(0,0,0),(0,0,0),(0,34,50),(1,34,50),(2,13,59),(0,0,0),(11,5,48),(2,17,58),(0,0,0),(0,0,0),(0,8,60),(0,23,56),(1,23,56),(0,0,0),(4,2,60),(10,13,50),(0,0,0),(0,0,0),(2,8,60),(0,37,48),(1,37,48),(0,0,0),(3,7,60),(0,14,59),(0,0,0),(0,0,0),(3,17,58),(0,9,60),(1,9,60),(0,0,0),(4,16,58),(2,14,59),(0,0,0),(0,0,0),(0,18,58),(1,18,58),(0,21,57),(0,0,0),(3,23,56),(8,34,45),(0,0,0),(0,0,0),(2,18,58),(0,36,49),(0,43,43),(0,0,0),(0,10,60),(0,26,55),(0,0,0),(0,0,0),(3,14,59),(2,36,49),(0,15,59),(0,0,0),(2,10,60),(0,30,53),(0,0,0),(0,0,0),(0,24,56),(1,24,56),(2,15,59),(0,0,0),(0,40,46),(1,40,46),(0,0,0),(0,0,0),(2,24,56),(0,0,61),(0,1,61),(0,0,0),(2,40,46),(0,2,61),(0,0,0),(0,0,0),(0,32,52),(1,32,52),(0,3,61),(0,0,0),(7,5,58),(0,22,57),(0,0,0),(0,0,0),(2,32,52),(0,4,61),(1,4,61),(0,0,0),(6,32,50),(2,22,57),(0,0,0),(0,0,0),(0,12,60),(1,12,60),(0,5,61),(0,0,0),(0,38,48),(1,38,48),(0,0,0),(0,0,0),(2,12,60),(10,7,52),(0,27,55),(0,0,0),(2,38,48),(0,6,61),(0,0,0),(0,0,0),(3,22,57),(0,25,56),(1,25,56),(0,0,0),(0,20,58),(1,20,58),(0,0,0),(0,0,0),(7,17,56),(0,13,60),(0,7,61),(0,0,0),(2,20,58),(3,5,61),(0,0,0),(0,0,0),(4,24,56),(2,13,60),(0,23,57),(0,0,0),(4,40,46),(3,27,55),(0,0,0),(0,0,0),(3,6,61),(0,8,61),(1,8,61),(0,0,0),(3,25,56),(0,42,45),(0,0,0),(0,0,0),(4,32,52),(0,33,52),(1,33,52),(0,0,0),(0,14,60),(0,41,46),(0,0,0),(0,0,0),(7,39,44),(2,33,52),(0,9,61),(0,0,0),(2,14,60),(0,18,59),(0,0,0),(0,0,0),(4,12,60),(0,28,55),(1,28,55),(0,0,0),(0,26,56),(1,26,56),(0,0,0),(0,0,0),(0,30,54),(1,30,54),(4,27,55),(0,0,0),(2,26,56),(0,10,61),(0,0,0),(0,0,0),(2,30,54),(0,15,60),(0,35,51),(0,0,0),(4,20,58),(2,10,61),(0,0,0),(0,0,0),(3,18,59),(0,32,53),(1,32,53),(0,0,0),(3,28,55),(5,24,56),(0,0,0),(0,0,0),(7,4,59),(2,32,53),(0,11,61),(0,0,0),(0,0,62),(0,1,62),(0,0,0),(0,0,0),(0,2,62),(1,2,62),(2,11,61),(0,0,0),(2,0,62),(0,3,62),(0,0,0),(0,0,0),(0,16,60),(1,16,60),(5,22,57),(0,0,0),(0,4,62),(1,4,62),(0,0,0),(0,0,0),(2,16,60),(0,12,61),(0,29,55),(0,0,0),(2,4,62),(0,5,62),(0,0,0),(0,0,0),(0,44,44),(1,44,44),(0,25,57),(0,0,0),(4,26,56),(0,31,54),(0,0,0),(0,0,0),(0,6,62),(0,20,59),(1,20,59),(0,0,0),(7,25,54),(2,31,54),(0,0,0),(0,0,0),(2,6,62),(0,17,60),(0,13,61),(0,0,0),(3,12,61),(0,7,62),(0,0,0),(0,0,0),(3,5,62),(0,36,51),(0,33,53),(0,0,0),(7,34,49),(2,7,62),(0,0,0),(0,0,0),(0,40,48),(1,40,48),(2,33,53),(0,0,0),(0,8,62),(1,8,62),(0,0,0),(0,0,0),(2,40,48),(6,36,49),(5,42,45),(0,0,0),(2,8,62),(0,14,61),(0,0,0),(0,0,0),(0,28,56),(1,28,56),(0,21,59),(0,0,0),(0,18,60),(0,9,62),(0,0,0),(0,0,0),(2,28,56),(0,35,52),(1,35,52),(0,0,0),(2,18,60),(2,9,62),(0,0,0),(0,0,0),(4,44,44),(2,35,52),(4,25,57),(0,0,0),(0,24,58),(1,24,58),(0,0,0),(0,0,0),(0,10,62),(1,10,62),(0,15,61),(0,0,0),(2,24,58),(3,21,59),(0,0,0),(0,0,0),(2,10,62),(4,17,60),(2,15,61),(0,0,0),(3,35,52),(4,7,62),(0,0,0),(0,0,0),(6,12,60),(0,19,60),(1,19,60),(0,0,0),(6,38,48),(0,11,62),(0,0,0),(0,0,0),(4,40,48),(0,0,63),(0,1,63),(0,0,0),(4,8,62),(0,2,63),(0,0,0),(0,0,0),(8,10,58),(0,16,61),(0,3,63),(0,0,0),(6,20,58),(2,2,63),(0,0,0),(0,0,0),(4,28,56),(0,4,63),(0,31,55),(0,0,0),(0,12,62),(0,25,58),(0,0,0),(0,0,0),(3,11,62),(2,4,63),(0,5,63),(0,0,0),(2,12,62),(2,25,58),(0,0,0),(0,0,0)]

def wits_4 : List (ℕ × ℕ × ℕ) := [(0,20,60),(0,40,49),(1,40,49),(0,0,0),(3,16,61),(0,6,63),(0,0,0),(0,0,0),(2,20,60),(2,40,49),(0,17,61),(0,0,0),(3,4,63),(0,13,62),(0,0,0),(0,0,0),(3,25,58),(8,16,57),(0,7,63),(0,0,0),(7,14,59),(0,39,50),(0,0,0),(0,0,0),(7,9,60),(4,19,60),(2,7,63),(0,0,0),(3,40,49),(2,39,50),(0,0,0),(0,0,0),(3,6,63),(0,8,63),(0,35,53),(0,0,0),(0,30,56),(1,30,56),(0,0,0),(0,0,0),(0,14,62),(0,21,60),(1,21,60),(0,0,0),(2,30,56),(0,18,61),(0,0,0),(0,0,0),(2,14,62),(0,32,55),(0,9,63),(0,0,0),(0,44,46),(1,44,46),(0,0,0),(0,0,0),(11,15,50),(0,24,59),(0,43,47),(0,0,0),(2,44,46),(3,35,53),(0,0,0),(0,0,0),(4,20,60),(2,24,59),(2,43,47),(0,0,0),(0,42,48),(0,10,63),(0,0,0),(0,0,0),(0,34,54),(0,37,52),(1,37,52),(0,0,0),(2,42,48),(2,10,63),(0,0,0),(0,0,0),(2,34,54),(2,37,52),(0,19,61),(0,0,0),(0,22,60),(1,22,60),(0,0,0),(0,0,0),(6,44,44),(7,5,61),(0,11,63),(0,0,0),(2,22,60),(0,27,58),(0,0,0),(0,0,0),(0,0,64),(0,1,64),(1,1,64),(0,0,0),(0,2,64),(1,2,64),(0,0,0),(0,0,0),(2,0,64),(0,3,64),(0,25,59),(0,0,0),(2,2,64),(3,19,61),(0,0,0),(0,0,0),(0,4,64),(0,12,63),(0,33,55),(0,0,0),(4,44,46),(3,11,63),(0,0,0),(0,0,0),(2,4,64),(0,5,64),(0,39,51),(0,0,0),(3,1,64),(5,20,60),(0,0,0),(0,0,0),(7,8,61),(0,23,60),(1,23,60),(0,0,0),(0,6,64),(0,17,62),(0,0,0),(0,0,0),(4,34,54),(2,23,60),(0,13,63),(0,0,0),(2,6,64),(0,35,54),(0,0,0),(0,0,0),(11,2,53),(0,7,64),(1,7,64),(0,0,0),(0,28,58),(0,30,57),(0,0,0),(0,0,0),(7,28,55),(0,43,48),(1,43,48),(0,0,0),(2,28,58),(0,26,59),(0,0,0),(0,0,0),(0,8,64),(1,8,64),(0,21,61),(0,0,0),(4,2,64),(0,14,63),(0,0,0),(0,0,0),(0,18,62),(1,18,62),(2,21,61),(0,0,0),(3,7,64),(2,14,63),(0,0,0),(0,0,0),(0,24,60),(0,9,64),(0,37,53),(0,0,0),(3,43,48),(0,34,55),(0,0,0),(0,0,0),(2,24,60),(2,9,64),(2,37,53),(0,0,0),(7,1,62),(2,34,55),(0,0,0),(0,0,0),(3,14,63),(4,23,60),(0,15,63),(0,0,0),(0,10,64),(1,10,64),(0,0,0),(0,0,0),(8,18,58),(0,40,51),(1,40,51),(0,0,0),(2,10,64),(0,19,62),(0,0,0),(0,0,0),(3,34,55),(2,40,51),(0,27,59),(0,0,0),(0,36,54),(1,36,54),(0,0,0),(0,0,0),(6,20,60),(0,11,64),(1,11,64),(0,0,0),(2,36,54),(3,15,63),(0,0,0),(0,0,0),(4,8,64),(0,0,65),(0,1,65),(0,0,0),(3,40,51),(0,2,65),(0,0,0),(0,0,0),(0,46,46),(1,46,46),(0,3,65),(0,0,0),(7,7,62),(2,2,65),(0,0,0),(0,0,0),(0,12,64),(0,4,65),(1,4,65),(0,0,0),(0,20,62),(1,20,62),(0,0,0),(0,0,0),(2,12,64),(2,4,65),(0,5,65),(0,0,0),(2,20,62),(0,38,53),(0,0,0),(0,0,0),(3,2,65),(5,6,64),(0,17,63),(0,0,0),(4,10,64),(0,6,65),(0,0,0),(0,0,0),(0,30,58),(0,13,64),(1,13,64),(0,0,0),(3,4,65),(2,6,65),(0,0,0),(0,0,0),(2,30,58),(0,32,57),(0,7,65),(0,0,0),(0,26,60),(1,26,60),(0,0,0),(0,0,0),(3,38,53),(2,32,57),(0,41,51),(0,0,0),(2,26,60),(0,21,62),(0,0,0),(0,0,0),(3,6,65),(0,8,65),(1,8,65),(0,0,0),(0,14,64),(0,18,63),(0,0,0),(0,0,0),(4,46,46),(0,24,61),(1,24,61),(0,0,0),(2,14,64),(2,18,63),(0,0,0),(0,0,0),(0,40,52),(1,40,52),(0,9,65),(0,0,0),(4,20,62),(3,41,51),(0,0,0),(0,0,0),(2,40,52),(6,1,64),(2,9,65),(0,0,0),(3,8,65),(4,38,53),(0,0,0),(0,0,0),(3,18,63),(0,15,64),(0,29,59),(0,0,0),(3,24,61),(0,10,65),(0,0,0),(0,0,0),(0,22,62),(0,27,60),(0,19,63),(0,0,0),(7,25,58),(2,10,65),(0,0,0),(0,0,0),(2,22,62),(0,44,49),(0,33,57),(0,0,0),(4,26,60),(10,29,50),(0,0,0),(0,0,0),(7,40,49),(2,44,49),(0,11,65),(0,0,0),(3,15,64),(0,43,50),(0,0,0),(0,0,0),(0,16,64),(1,16,64),(2,11,65),(0,0,0),(0,0,66),(0,1,66),(0,0,0),(0,0,0),(0,2,66),(0,35,56),(1,35,56),(0,0,0),(2,0,66),(0,3,66),(0,0,0),(0,0,0),(2,2,66),(0,12,65),(1,12,65),(0,0,0),(0,4,66),(0,23,62),(0,0,0),(0,0,0),(3,43,50),(2,12,65),(5,38,53),(0,0,0),(2,4,66),(0,5,66),(0,0,0),(0,0,0),(0,28,60),(0,17,64),(1,17,64),(0,0,0),(0,32,58),(1,32,58),(0,0,0),(0,0,0),(0,6,66),(1,6,66),(0,13,65),(0,0,0),(2,32,58),(0,26,61),(0,0,0),(0,0,0),(2,6,66),(4,44,49),(2,13,65),(0,0,0),(0,0,0),(0,7,66),(0,0,0),(0,0,0),(3,5,66),(0,40,53),(0,21,63),(0,0,0),(3,17,64),(2,7,66),(0,0,0),(0,0,0),(4,16,64),(2,40,53),(0,47,47),(0,0,0),(0,8,66),(0,14,65),(0,0,0),(0,0,0),(3,26,61),(4,35,56),(0,45,49),(0,0,0),(2,8,66),(2,14,65),(0,0,0),(0,0,0),(0,36,56),(1,36,56),(2,45,49),(0,0,0),(0,44,50),(0,9,66),(0,0,0),(0,0,0),(2,36,56),(0,29,60),(0,31,59),(0,0,0),(2,44,50),(2,9,66),(0,0,0),(0,0,0),(3,14,65),(2,29,60),(0,15,65),(0,0,0),(4,32,58),(0,22,63),(0,0,0),(0,0,0),(0,10,66),(0,19,64),(1,19,64),(0,0,0),(6,20,62),(2,22,63),(0,0,0),(0,0,0),(2,10,66),(2,19,64),(6,5,65),(0,0,0),(0,42,52),(0,25,62),(0,0,0),(0,0,0),(7,23,60),(4,40,53),(0,35,57),(0,0,0),(2,42,52),(0,11,66),(0,0,0),(0,0,0),(3,22,63),(0,16,65),(1,16,65),(0,0,0),(3,19,64),(2,11,66),(0,0,0),(0,0,0),(7,7,64),(0,0,67),(0,1,67),(0,0,0),(6,26,60),(0,2,67),(0,0,0),(0,0,0),(0,20,64),(1,20,64),(0,3,67),(0,0,0),(0,12,66),(1,12,66),(0,0,0),(0,0,0),(2,20,64),(0,4,67),(1,4,67),(0,0,0),(2,12,66),(5,28,60),(0,0,0),(0,0,0),(8,20,60),(0,47,48),(0,5,67),(0,0,0),(0,40,54),(0,46,49),(0,0,0),(0,0,0),(0,26,62),(1,26,62),(2,5,67),(0,0,0),(2,40,54),(0,6,67),(0,0,0),(0,0,0),(2,26,62),(10,35,48),(5,7,66),(0,0,0),(3,4,67),(2,6,67),(0,0,0),(0,0,0),(10,20,56),(0,21,64),(0,7,67),(0,0,0),(3,47,48),(3,5,67),(0,0,0),(0,0,0),(3,46,49),(0,24,63),(0,39,55),(0,0,0),(7,19,62),(0,18,65),(0,0,0),(0,0,0),(0,14,66),(0,8,67),(1,8,67),(0,0,0),(15,5,34),(2,18,65),(0,0,0),(0,0,0),(2,14,66),(0,31,60),(0,29,61),(0,0,0),(3,21,64),(3,7,67),(0,0,0),(0,0,0),(6,16,64),(2,31,60),(0,9,67),(0,0,0),(3,24,63),(0,27,62),(0,0,0),(0,0,0),(3,18,65),(4,47,48),(2,9,67),(0,0,0),(0,22,64),(0,15,66),(0,0,0),(0,0,0),(4,26,62),(6,12,65),(0,19,65),(0,0,0),(2,22,64),(0,10,67),(0,0,0),(0,0,0),(10,26,54),(5,42,52),(0,25,63),(0,0,0),(7,38,53),(0,41,54),(0,0,0),(0,0,0),(3,27,62),(4,21,64),(2,25,63),(0,0,0),(6,32,58),(2,41,54),(0,0,0),(0,0,0),(0,48,48),(1,48,48),(0,11,67),(0,0,0),(0,16,66),(1,16,66),(0,0,0),(0,0,0),(0,46,50),(1,46,50),(0,37,57),(0,0,0),(2,16,66),(0,30,61),(0,0,0),(0,0,0),(0,0,68),(0,1,68),(0,45,51),(0,0,0),(0,2,68),(1,2,68),(0,0,0),(0,0,0),(2,0,68),(0,3,68),(1,3,68),(0,0,0),(2,2,68),(0,34,59),(0,0,0),(0,0,0),(0,4,68),(1,4,68),(5,46,49),(0,0,0),(4,22,64),(0,17,66),(0,0,0),(0,0,0),(2,4,68),(0,5,68),(1,5,68),(0,0,0),(3,1,68),(2,17,66),(0,0,0),(0,0,0),(10,34,50),(0,39,56),(0,13,67),(0,0,0),(0,6,68),(1,6,68),(0,0,0),(0,0,0),(3,34,59),(2,39,56),(0,21,65),(0,0,0),(2,6,68),(6,22,63),(0,0,0),(0,0,0),(0,24,64),(0,7,68),(1,7,68),(0,0,0),(3,5,68),(5,14,66),(0,0,0),(0,0,0),(0,18,66),(1,18,66),(0,31,61),(0,0,0),(3,39,56),(0,14,67),(0,0,0),(0,0,0),(0,8,68),(0,33,60),(1,33,60),(0,0,0),(4,2,68),(0,38,57),(0,0,0),(0,0,0),(2,8,68),(2,33,60),(0,27,63),(0,0,0),(3,7,68),(2,38,57),(0,0,0),(0,0,0),(4,4,68),(0,9,68),(0,35,59),(0,0,0),(7,3,66),(0,22,65),(0,0,0),(0,0,0),(3,14,67),(2,9,68),(0,15,67),(0,0,0),(3,33,60),(0,19,66),(0,0,0),(0,0,0),(3,38,57),(0,25,64),(1,25,64),(0,0,0),(0,10,68),(1,10,68),(0,0,0),(0,0,0),(7,17,64),(0,45,52),(1,45,52),(0,0,0),(2,10,68),(0,37,58),(0,0,0),(0,0,0),(0,40,56),(1,40,56),(8,1,65),(0,0,0),(7,26,61),(2,37,58),(0,0,0),(0,0,0),(0,30,62),(0,11,68),(1,11,68),(0,0,0),(3,25,64),(4,14,67),(0,0,0),(0,0,0),(2,30,62),(0,28,63),(0,23,65),(0,0,0),(0,20,66),(1,20,66),(0,0,0),(0,0,0),(3,37,58),(0,0,69),(0,1,69),(0,0,0),(2,20,66),(0,2,69),(0,0,0),(0,0,0),(0,12,68),(1,12,68),(0,3,69),(0,0,0),(0,26,64),(1,26,64),(0,0,0),(0,0,0),(2,12,68),(0,4,69),(0,17,67),(0,0,0),(2,26,64),(3,23,65),(0,0,0),(0,0,0),(7,29,60),(2,4,69),(0,5,69),(0,0,0),(3,0,69),(0,42,55),(0,0,0),(0,0,0),(3,2,69),(0,13,68),(1,13,68),(0,0,0),(6,22,64),(0,6,69),(0,0,0),(0,0,0),(4,40,56),(0,24,65),(0,49,49),(0,0,0),(0,48,50),(0,31,62),(0,0,0),(0,0,0),(0,38,58),(1,38,58),(0,7,69),(0,0,0),(2,48,50),(0,18,67),(0,0,0),(0,0,0),(2,38,58),(0,41,56),(1,41,56),(0,0,0),(0,14,68),(1,14,68),(0,0,0),(0,0,0),(3,6,69),(0,8,69),(1,8,69),(0,0,0),(2,14,68),(3,49,49),(0,0,0),(0,0,0),(3,31,62),(2,8,69),(0,45,53),(0,0,0),(4,26,64),(3,7,69),(0,0,0),(0,0,0),(0,22,66),(1,22,66),(0,9,69),(0,0,0),(3,41,56),(10,1,62),(0,0,0),(0,0,0),(2,22,66),(0,15,68),(0,19,67),(0,0,0),(0,44,54),(1,44,54),(0,0,0),(0,0,0),(6,4,68),(2,15,68),(2,19,67),(0,0,0),(2,44,54),(0,10,69),(0,0,0),(0,0,0),(8,16,64),(4,24,65),(4,49,49),(0,0,0),(0,32,62),(0,30,63),(0,0,0),(0,0,0),(4,38,58),(6,39,56),(0,43,55),(0,0,0),(2,32,62),(0,34,61),(0,0,0),(0,0,0),(0,16,68),(1,16,68),(0,11,69),(0,0,0),(4,14,68),(0,23,66),(0,0,0),(0,0,0),(2,16,68),(0,20,67),(1,20,67),(0,0,0),(7,18,65),(2,23,66),(0,0,0),(0,0,0),(0,36,60),(1,36,60),(4,45,53),(0,0,0),(0,0,70),(0,1,70),(0,0,0),(0,0,0),(0,2,70),(0,12,69),(1,12,69),(0,0,0),(2,0,70),(0,3,70),(0,0,0),(0,0,0),(2,2,70),(0,17,68),(1,17,68),(0,0,0),(0,4,70),(1,4,70),(0,0,0),(0,0,0),(10,28,56),(2,17,68),(5,6,69),(0,0,0),(2,4,70),(0,5,70),(0,0,0),(0,0,0),(3,1,70),(5,48,50),(0,13,69),(0,0,0),(0,24,66),(0,33,62),(0,0,0),(0,0,0),(0,6,70),(0,29,64),(1,29,64),(0,0,0),(2,24,66),(0,45,54),(0,0,0),(0,0,0),(2,6,70),(2,29,64),(0,35,61),(0,0,0),(0,18,68),(0,7,70),(0,0,0),(0,0,0),(3,5,70),(4,20,67),(0,27,65),(0,0,0),(2,18,68),(0,14,69),(0,0,0),(0,0,0),(3,33,62),(0,44,55),(1,44,55),(0,0,0),(0,8,70),(1,8,70),(0,0,0),(0,0,0),(3,45,54),(0,37,60),(1,37,60),(0,0,0),(2,8,70),(0,22,67),(0,0,0),(0,0,0),(3,7,70),(2,37,60),(6,1,69),(0,0,0),(4,4,70),(0,9,70),(0,0,0),(0,0,0),(3,14,69),(0,19,68),(0,15,69),(0,0,0),(3,44,55),(2,9,70),(0,0,0),(0,0,0),(7,5,68),(0,32,63),(1,32,63),(0,0,0),(0,30,64),(1,30,64),(0,0,0),(0,0,0)]

def wits_5 : List (ℕ × ℕ × ℕ) := [(0,10,70),(1,10,70),(0,39,59),(0,0,0),(2,30,64),(4,45,54),(0,0,0),(0,0,0),(0,48,52),(0,28,65),(1,28,65),(0,0,0),(3,19,68),(0,42,57),(0,0,0),(0,0,0),(2,48,52),(0,16,69),(0,23,67),(0,0,0),(3,32,63),(0,11,70),(0,0,0),(0,0,0),(0,20,68),(1,20,68),(2,23,67),(0,0,0),(4,8,70),(2,11,70),(0,0,0),(0,0,0),(0,26,66),(1,26,66),(5,3,70),(0,0,0),(3,28,65),(4,22,67),(0,0,0),(0,0,0),(2,26,66),(0,0,71),(0,1,71),(0,0,0),(0,12,70),(0,2,71),(0,0,0),(0,0,0),(3,11,70),(2,0,71),(0,3,71),(0,0,0),(2,12,70),(2,2,71),(0,0,0),(0,0,0),(6,22,66),(0,4,71),(0,33,63),(0,0,0),(4,30,64),(5,6,70),(0,0,0),(0,0,0),(4,10,70),(0,21,68),(0,5,71),(0,0,0),(3,0,71),(0,13,70),(0,0,0),(0,0,0),(0,44,56),(1,44,56),(2,5,71),(0,0,0),(7,37,58),(0,6,71),(0,0,0),(0,0,0),(2,44,56),(0,40,59),(1,40,59),(0,0,0),(3,4,71),(0,18,69),(0,0,0),(0,0,0),(4,20,68),(2,40,59),(0,7,71),(0,0,0),(3,21,68),(2,18,69),(0,0,0),(0,0,0),(0,14,70),(1,14,70),(0,43,57),(0,0,0),(10,2,64),(0,50,51),(0,0,0),(0,0,0),(2,14,70),(0,8,71),(1,8,71),(0,0,0),(0,22,68),(1,22,68),(0,0,0),(0,0,0),(3,18,69),(0,48,53),(0,25,67),(0,0,0),(2,22,68),(3,7,71),(0,0,0),(0,0,0),(0,32,64),(0,39,60),(0,9,71),(0,0,0),(8,16,66),(0,15,70),(0,0,0),(0,0,0),(0,42,58),(1,42,58),(2,9,71),(0,0,0),(3,8,71),(2,15,70),(0,0,0),(0,0,0),(2,42,58),(8,1,68),(5,42,57),(0,0,0),(0,28,66),(0,10,71),(0,0,0),(0,0,0),(7,24,65),(4,40,59),(5,11,70),(0,0,0),(2,28,66),(2,10,71),(0,0,0),(0,0,0),(3,15,70),(0,23,68),(1,23,68),(0,0,0),(0,16,70),(1,16,70),(0,0,0),(0,0,0),(4,14,70),(0,20,69),(0,11,71),(0,0,0),(2,16,70),(0,26,67),(0,0,0),(0,0,0),(3,10,71),(2,20,69),(2,11,71),(0,0,0),(4,22,68),(2,26,67),(0,0,0),(0,0,0),(10,24,60),(4,48,53),(4,25,67),(0,0,0),(3,23,68),(10,34,55),(0,0,0),(0,0,0),(0,0,72),(0,1,72),(0,31,65),(0,0,0),(0,2,72),(0,17,70),(0,0,0),(0,0,0),(2,0,72),(0,3,72),(0,35,63),(0,0,0),(2,2,72),(0,29,66),(0,0,0),(0,0,0),(0,4,72),(1,4,72),(0,21,69),(0,0,0),(0,50,52),(1,50,52),(0,0,0),(0,0,0),(2,4,72),(0,5,72),(0,13,71),(0,0,0),(2,50,52),(0,37,62),(0,0,0),(0,0,0),(3,17,70),(2,5,72),(0,27,67),(0,0,0),(0,6,72),(1,6,72),(0,0,0),(0,0,0),(0,18,70),(1,18,70),(2,27,67),(0,0,0),(2,6,72),(3,21,69),(0,0,0),(0,0,0),(2,18,70),(0,7,72),(0,47,55),(0,0,0),(3,5,72),(0,14,71),(0,0,0),(0,0,0),(3,37,62),(2,7,72),(0,39,61),(0,0,0),(7,1,70),(0,22,69),(0,0,0),(0,0,0),(0,8,72),(0,25,68),(1,25,68),(0,0,0),(0,34,64),(1,34,64),(0,0,0),(0,0,0),(0,30,66),(1,30,66),(4,35,63),(0,0,0),(2,34,64),(0,19,70),(0,0,0),(0,0,0),(2,30,66),(0,9,72),(0,15,71),(0,0,0),(4,50,52),(2,19,70),(0,0,0),(0,0,0),(3,22,69),(0,28,67),(0,45,57),(0,0,0),(3,25,68),(4,37,62),(0,0,0),(0,0,0),(7,29,64),(0,41,60),(1,41,60),(0,0,0),(0,10,72),(1,10,72),(0,0,0),(0,0,0),(0,38,62),(1,38,62),(0,23,69),(0,0,0),(2,10,72),(3,15,71),(0,0,0),(0,0,0),(2,38,62),(0,16,71),(1,16,71),(0,0,0),(0,20,70),(1,20,70),(0,0,0),(0,0,0),(7,44,55),(0,11,72),(1,11,72),(0,0,0),(2,20,70),(0,50,53),(0,0,0),(0,0,0),(4,8,72),(2,11,72),(0,33,65),(0,0,0),(4,34,64),(0,31,66),(0,0,0),(0,0,0),(4,30,66),(0,35,64),(1,35,64),(0,0,0),(3,16,71),(2,31,66),(0,0,0),(0,0,0),(0,12,72),(0,0,73),(0,1,73),(0,0,0),(3,11,72),(0,2,73),(0,0,0),(0,0,0),(2,12,72),(0,24,69),(0,3,73),(0,0,0),(0,0,0),(0,21,70),(0,0,0),(0,0,0),(3,31,66),(0,4,73),(1,4,73),(0,0,0),(3,35,64),(2,21,70),(0,0,0),(0,0,0),(4,38,62),(0,13,72),(0,5,73),(0,0,0),(3,0,73),(3,1,73),(0,0,0),(0,0,0),(3,2,73),(2,13,72),(2,5,73),(0,0,0),(0,42,60),(0,6,73),(0,0,0),(0,0,0),(3,21,70),(4,11,72),(5,22,69),(0,0,0),(2,42,60),(2,6,73),(0,0,0),(0,0,0),(11,18,61),(5,34,64),(0,7,73),(0,0,0),(0,14,72),(0,34,65),(0,0,0),(0,0,0),(0,22,70),(1,22,70),(0,25,69),(0,0,0),(2,14,72),(0,30,67),(0,0,0),(0,0,0),(0,36,64),(0,8,73),(1,8,73),(0,0,0),(16,2,36),(2,30,67),(0,0,0),(0,0,0),(2,36,64),(2,8,73),(0,19,71),(0,0,0),(6,2,72),(3,7,73),(0,0,0),(0,0,0),(0,28,68),(0,15,72),(0,9,73),(0,0,0),(7,13,70),(0,38,63),(0,0,0),(0,0,0),(0,50,54),(0,44,59),(1,44,59),(0,0,0),(3,8,73),(2,38,63),(0,0,0),(0,0,0),(2,50,54),(2,44,59),(0,49,55),(0,0,0),(4,42,60),(0,10,73),(0,0,0),(0,0,0),(10,36,56),(7,7,71),(2,49,55),(0,0,0),(3,15,72),(0,26,69),(0,0,0),(0,0,0),(0,16,72),(0,20,71),(1,20,71),(0,0,0),(0,40,62),(0,33,66),(0,0,0),(0,0,0),(2,16,72),(0,43,60),(0,11,73),(0,0,0),(2,40,62),(2,33,66),(0,0,0),(0,0,0),(3,10,73),(2,43,60),(0,47,57),(0,0,0),(8,18,68),(6,22,69),(0,0,0),(0,0,0),(3,26,69),(0,29,68),(1,29,68),(0,0,0),(3,20,71),(8,14,69),(0,0,0),(0,0,0),(3,33,66),(0,12,73),(1,12,73),(0,0,0),(0,0,74),(0,1,74),(0,0,0),(0,0,0),(0,2,74),(1,2,74),(0,21,71),(0,0,0),(2,0,74),(0,3,74),(0,0,0),(0,0,0),(2,2,74),(5,42,60),(0,27,69),(0,0,0),(0,4,74),(1,4,74),(0,0,0),(0,0,0),(7,23,68),(6,41,60),(0,13,73),(0,0,0),(2,4,74),(0,5,74),(0,0,0),(0,0,0),(3,1,74),(4,20,71),(0,45,59),(0,0,0),(0,18,72),(1,18,72),(0,0,0),(0,0,0),(0,6,74),(0,32,67),(1,32,67),(0,0,0),(2,18,72),(0,51,54),(0,0,0),(0,0,0),(2,6,74),(0,36,65),(1,36,65),(0,0,0),(0,30,68),(0,7,74),(0,0,0),(0,0,0),(3,5,74),(2,36,65),(6,33,65),(0,0,0),(2,30,68),(2,7,74),(0,0,0),(0,0,0),(0,44,60),(0,49,56),(1,49,56),(0,0,0),(0,8,74),(1,8,74),(0,0,0),(0,0,0),(2,44,60),(0,19,72),(1,19,72),(0,0,0),(2,8,74),(4,3,74),(0,0,0),(0,0,0),(3,7,74),(0,48,57),(0,15,73),(0,0,0),(4,4,74),(0,9,74),(0,0,0),(0,0,0),(11,2,65),(2,48,57),(2,15,73),(0,0,0),(3,49,56),(2,9,74),(0,0,0),(0,0,0),(14,18,50),(0,40,63),(0,23,71),(0,0,0),(3,19,72),(0,47,58),(0,0,0),(0,0,0),(0,10,74),(1,10,74),(0,33,67),(0,0,0),(3,48,57),(0,35,66),(0,0,0),(0,0,0),(0,20,72),(0,16,73),(1,16,73),(0,0,0),(4,30,68),(2,35,66),(0,0,0),(0,0,0),(2,20,72),(2,16,73),(0,37,65),(0,0,0),(3,40,63),(0,11,74),(0,0,0),(0,0,0),(3,47,58),(4,49,56),(0,29,69),(0,0,0),(4,8,74),(2,11,74),(0,0,0),(0,0,0),(0,42,62),(1,42,62),(2,29,69),(0,0,0),(3,16,73),(8,50,51),(0,0,0),(0,0,0),(2,42,62),(0,24,71),(0,17,73),(0,0,0),(0,12,74),(1,12,74),(0,0,0),(0,0,0),(3,11,74),(0,0,75),(0,1,75),(0,0,0),(2,12,74),(0,2,75),(0,0,0),(0,0,0),(6,50,54),(2,0,75),(0,3,75),(0,0,0),(0,50,56),(1,50,56),(0,0,0),(0,0,0),(4,10,74),(0,4,75),(1,4,75),(0,0,0),(2,50,56),(0,13,74),(0,0,0),(0,0,0),(0,32,68),(1,32,68),(0,5,75),(0,0,0),(0,36,66),(0,18,73),(0,0,0),(0,0,0),(2,32,68),(0,44,61),(1,44,61),(0,0,0),(2,36,66),(0,6,75),(0,0,0),(0,0,0),(7,35,64),(2,44,61),(0,25,71),(0,0,0),(0,22,72),(0,38,65),(0,0,0),(0,0,0),(0,14,74),(1,14,74),(0,7,75),(0,0,0),(2,22,72),(2,38,65),(0,0,0),(0,0,0),(2,14,74),(4,24,71),(2,7,75),(0,0,0),(0,28,70),(1,28,70),(0,0,0),(0,0,0),(3,6,75),(0,8,75),(0,19,73),(0,0,0),(2,28,70),(0,43,62),(0,0,0),(0,0,0),(0,40,64),(1,40,64),(2,19,73),(0,0,0),(4,50,56),(0,15,74),(0,0,0),(0,0,0),(2,40,64),(4,4,75),(0,9,75),(0,0,0),(6,4,74),(2,15,74),(0,0,0),(0,0,0),(4,32,68),(0,23,72),(0,35,67),(0,0,0),(0,46,60),(0,26,71),(0,0,0),(0,0,0),(3,43,62),(2,23,72),(0,31,69),(0,0,0),(2,46,60),(0,10,75),(0,0,0),(0,0,0),(3,15,74),(0,20,73),(1,20,73),(0,0,0),(0,16,74),(0,42,63),(0,0,0),(0,0,0),(4,14,74),(0,51,56),(1,51,56),(0,0,0),(2,16,74),(0,29,70),(0,0,0),(0,0,0),(3,26,71),(2,51,56),(0,11,75),(0,0,0),(4,28,70),(0,50,57),(0,0,0),(0,0,0),(3,10,75),(4,8,75),(2,11,75),(0,0,0),(3,20,73),(2,50,57),(0,0,0),(0,0,0),(0,24,72),(1,24,72),(10,1,69),(0,0,0),(3,51,56),(0,17,74),(0,0,0),(0,0,0),(2,24,72),(0,12,75),(0,21,73),(0,0,0),(7,10,73),(2,17,74),(0,0,0),(0,0,0),(0,0,76),(0,1,76),(1,1,76),(0,0,0),(0,2,76),(1,2,76),(0,0,0),(0,0,0),(2,0,76),(0,3,76),(1,3,76),(0,0,0),(2,2,76),(4,10,75),(0,0,0),(0,0,0),(0,4,76),(1,4,76),(0,13,75),(0,0,0),(3,12,75),(3,21,73),(0,0,0),(0,0,0),(0,18,74),(0,5,76),(1,5,76),(0,0,0),(3,1,76),(4,29,70),(0,0,0),(0,0,0),(2,18,74),(0,25,72),(1,25,72),(0,0,0),(0,6,76),(0,22,73),(0,0,0),(0,0,0),(7,12,73),(2,25,72),(0,43,63),(0,0,0),(2,6,76),(0,14,75),(0,0,0),(0,0,0),(4,24,72),(0,7,76),(1,7,76),(0,0,0),(3,5,76),(2,14,75),(0,0,0),(0,0,0),(0,54,54),(1,54,54),(0,53,55),(0,0,0),(3,25,72),(0,19,74),(0,0,0),(0,0,0),(0,8,76),(1,8,76),(2,53,55),(0,0,0),(4,2,76),(2,19,74),(0,0,0),(0,0,0),(2,8,76),(0,35,68),(0,15,75),(0,0,0),(3,7,76),(8,21,70),(0,0,0),(0,0,0),(4,4,76),(0,9,76),(0,23,73),(0,0,0),(0,26,72),(0,31,70),(0,0,0),(0,0,0),(0,50,58),(1,50,58),(2,23,73),(0,0,0),(2,26,72),(0,45,62),(0,0,0),(0,0,0),(2,50,58),(4,25,72),(5,50,57),(0,0,0),(0,10,76),(0,39,66),(0,0,0),(0,0,0),(7,49,56),(0,16,75),(0,29,71),(0,0,0),(2,10,76),(2,39,66),(0,0,0),(0,0,0),(3,31,70),(2,16,75),(2,29,71),(0,0,0),(8,14,72),(8,34,65),(0,0,0),(0,0,0),(3,45,62),(0,11,76),(1,11,76),(0,0,0),(6,28,70),(4,19,74),(0,0,0),(0,0,0),(0,48,60),(0,24,73),(0,41,65),(0,0,0),(3,16,75),(3,29,71),(0,0,0),(0,0,0),(2,48,60),(0,27,72),(0,17,75),(0,0,0),(7,47,58),(0,21,74),(0,0,0),(0,0,0),(0,12,76),(1,12,76),(2,17,75),(0,0,0),(0,32,70),(1,32,70),(0,0,0),(0,0,0),(2,12,76),(0,0,77),(0,1,77),(0,0,0),(2,32,70),(0,2,77),(0,0,0),(0,0,0),(10,6,70),(2,0,77),(0,3,77),(0,0,0),(3,27,72),(0,30,71),(0,0,0),(0,0,0),(3,21,74),(0,4,77),(1,4,77),(0,0,0),(6,16,74),(0,18,75),(0,0,0),(0,0,0),(8,16,72),(0,52,57),(0,5,77),(0,0,0),(0,40,66),(1,40,66),(0,0,0),(0,0,0),(0,22,74),(1,22,74),(2,5,77),(0,0,0),(2,40,66),(0,6,77),(0,0,0),(0,0,0),(0,28,72),(1,28,72),(4,41,65),(0,0,0),(0,14,76),(1,14,76),(0,0,0),(0,0,0),(2,28,72),(4,27,72),(0,7,77),(0,0,0),(2,14,76),(0,50,59),(0,0,0),(0,0,0),(4,12,76),(5,26,72),(0,19,75),(0,0,0),(4,32,70),(0,33,70),(0,0,0),(0,0,0),(3,6,77),(0,8,77),(0,45,63),(0,0,0),(6,2,76),(2,33,70),(0,0,0),(0,0,0)]

def wits_6 : List (ℕ × ℕ × ℕ) := [(7,44,61),(0,15,76),(0,31,71),(0,0,0),(7,6,75),(0,23,74),(0,0,0),(0,0,0),(3,50,59),(2,15,76),(0,9,77),(0,0,0),(7,38,65),(2,23,74),(0,0,0),(0,0,0),(3,33,70),(4,52,57),(2,9,77),(0,0,0),(3,8,77),(3,45,63),(0,0,0),(0,0,0),(4,22,74),(0,20,75),(1,20,75),(0,0,0),(3,15,76),(0,10,77),(0,0,0),(0,0,0),(0,16,76),(1,16,76),(6,43,63),(0,0,0),(4,14,76),(0,41,66),(0,0,0),(0,0,0),(2,16,76),(6,7,76),(4,7,77),(0,0,0),(7,15,74),(2,41,66),(0,0,0),(0,0,0),(6,54,54),(5,32,70),(0,11,77),(0,0,0),(0,24,74),(0,47,62),(0,0,0),(0,0,0),(0,34,70),(0,36,69),(0,27,73),(0,0,0),(2,24,74),(2,47,62),(0,0,0),(0,0,0),(2,34,70),(0,17,76),(0,21,75),(0,0,0),(0,38,68),(1,38,68),(0,0,0),(0,0,0),(7,20,73),(0,12,77),(0,43,65),(0,0,0),(2,38,68),(3,11,77),(0,0,0),(0,0,0),(3,47,62),(2,12,77),(0,51,59),(0,0,0),(0,0,78),(0,1,78),(0,0,0),(0,0,0),(0,2,78),(0,40,67),(1,40,67),(0,0,0),(2,0,78),(0,3,78),(0,0,0),(0,0,0),(2,2,78),(2,40,67),(0,13,77),(0,0,0),(0,4,78),(0,25,74),(0,0,0),(0,0,0),(15,5,52),(10,8,71),(2,13,77),(0,0,0),(2,4,78),(0,5,78),(0,0,0),(0,0,0),(3,1,78),(0,28,73),(1,28,73),(0,0,0),(3,40,67),(2,5,78),(0,0,0),(0,0,0),(0,6,78),(0,45,64),(0,49,61),(0,0,0),(11,13,68),(0,14,77),(0,0,0),(0,0,0),(2,6,78),(2,45,64),(0,33,71),(0,0,0),(4,38,68),(0,7,78),(0,0,0),(0,0,0),(3,5,78),(0,19,76),(1,19,76),(0,0,0),(3,28,73),(2,7,78),(0,0,0),(0,0,0),(7,5,76),(0,31,72),(1,31,72),(0,0,0),(0,8,78),(1,8,78),(0,0,0),(0,0,0),(0,26,74),(1,26,74),(0,15,77),(0,0,0),(2,8,78),(3,33,71),(0,0,0),(0,0,0),(2,26,74),(0,44,65),(1,44,65),(0,0,0),(3,19,76),(0,9,78),(0,0,0),(0,0,0),(7,7,76),(2,44,65),(0,29,73),(0,0,0),(3,31,72),(0,53,58),(0,0,0),(0,0,0),(0,20,76),(1,20,76),(0,47,63),(0,0,0),(7,19,74),(2,53,58),(0,0,0),(0,0,0),(0,10,78),(0,16,77),(1,16,77),(0,0,0),(3,44,65),(4,14,77),(0,0,0),(0,0,0),(2,10,78),(2,16,77),(4,33,71),(0,0,0),(0,36,70),(0,34,71),(0,0,0),(0,0,0),(3,53,58),(0,24,75),(1,24,75),(0,0,0),(2,36,70),(0,11,78),(0,0,0),(0,0,0),(0,32,72),(1,32,72),(5,1,78),(0,0,0),(0,46,64),(1,46,64),(0,0,0),(0,0,0),(2,32,72),(0,21,76),(0,17,77),(0,0,0),(2,46,64),(0,50,61),(0,0,0),(0,0,0),(0,40,68),(1,40,68),(2,17,77),(0,0,0),(0,12,78),(0,30,73),(0,0,0),(0,0,0),(2,40,68),(10,7,72),(4,29,73),(0,0,0),(2,12,78),(2,30,73),(0,0,0),(0,0,0),(4,20,76),(0,0,79),(0,1,79),(0,0,0),(3,21,76),(0,2,79),(0,0,0),(0,0,0),(3,50,61),(2,0,79),(0,3,79),(0,0,0),(10,34,64),(0,13,78),(0,0,0),(0,0,0),(3,30,73),(0,4,79),(1,4,79),(0,0,0),(0,22,76),(1,22,76),(0,0,0),(0,0,0),(11,33,62),(2,4,79),(0,5,79),(0,0,0),(2,22,76),(0,37,70),(0,0,0),(0,0,0),(0,56,56),(0,33,72),(0,55,57),(0,0,0),(4,46,64),(0,6,79),(0,0,0),(0,0,0),(0,14,78),(1,14,78),(0,39,69),(0,0,0),(3,4,79),(2,6,79),(0,0,0),(0,0,0),(2,14,78),(6,12,77),(0,7,79),(0,0,0),(0,44,66),(1,44,66),(0,0,0),(0,0,0),(3,37,70),(7,5,77),(2,7,79),(0,0,0),(2,44,66),(0,26,75),(0,0,0),(0,0,0),(0,52,60),(0,8,79),(1,8,79),(0,0,0),(7,6,77),(0,15,78),(0,0,0),(0,0,0),(2,52,60),(2,8,79),(4,3,79),(0,0,0),(6,4,78),(0,29,74),(0,0,0),(0,0,0),(18,2,22),(4,4,79),(0,9,79),(0,0,0),(4,22,76),(2,29,74),(0,0,0),(0,0,0),(3,26,75),(0,20,77),(1,20,77),(0,0,0),(3,8,79),(4,37,70),(0,0,0),(0,0,0),(3,15,78),(0,36,71),(0,43,67),(0,0,0),(0,16,78),(0,10,79),(0,0,0),(0,0,0),(0,38,70),(1,38,70),(2,43,67),(0,0,0),(2,16,78),(2,10,79),(0,0,0),(0,0,0),(0,24,76),(0,32,73),(0,27,75),(0,0,0),(3,20,77),(13,8,64),(0,0,0),(0,0,0),(2,24,76),(0,40,69),(0,11,79),(0,0,0),(3,36,71),(3,43,67),(0,0,0),(0,0,0),(3,10,79),(2,40,69),(0,21,77),(0,0,0),(7,10,77),(0,17,78),(0,0,0),(0,0,0),(0,30,74),(1,30,74),(2,21,77),(0,0,0),(3,32,73),(0,45,66),(0,0,0),(0,0,0),(2,30,74),(0,12,79),(1,12,79),(0,0,0),(0,42,68),(0,55,58),(0,0,0),(0,0,0),(6,20,76),(2,12,79),(5,37,70),(0,0,0),(2,42,68),(0,54,59),(0,0,0),(0,0,0),(0,0,80),(0,1,80),(1,1,80),(0,0,0),(0,2,80),(1,2,80),(0,0,0),(0,0,0),(0,18,78),(0,3,80),(0,13,79),(0,0,0),(2,2,80),(0,22,77),(0,0,0),(0,0,0),(0,4,80),(1,4,80),(0,33,73),(0,0,0),(0,0,0),(0,39,70),(0,0,0),(0,0,0),(2,4,80),(0,5,80),(1,5,80),(0,0,0),(3,1,80),(2,39,70),(0,0,0),(0,0,0),(7,40,67),(2,5,80),(0,47,65),(0,0,0),(0,6,80),(0,14,79),(0,0,0),(0,0,0),(3,22,77),(7,13,77),(0,41,69),(0,0,0),(2,6,80),(0,19,78),(0,0,0),(0,0,0),(3,39,70),(0,7,80),(1,7,80),(0,0,0),(0,26,76),(1,26,76),(0,0,0),(0,0,0),(7,28,73),(2,7,80),(0,23,77),(0,0,0),(2,26,76),(3,47,65),(0,0,0),(0,0,0),(0,8,80),(1,8,80),(0,15,79),(0,0,0),(4,2,80),(0,50,63),(0,0,0),(0,0,0),(0,46,66),(0,43,68),(1,43,68),(0,0,0),(3,7,80),(2,50,63),(0,0,0),(0,0,0),(0,36,72),(0,9,80),(1,9,80),(0,0,0),(0,20,78),(0,34,73),(0,0,0),(0,0,0),(2,36,72),(2,9,80),(6,55,57),(0,0,0),(2,20,78),(2,34,73),(0,0,0),(0,0,0),(3,50,63),(0,16,79),(0,57,57),(0,0,0),(0,10,80),(1,10,80),(0,0,0),(0,0,0),(7,44,65),(0,24,77),(0,55,59),(0,0,0),(2,10,80),(4,19,78),(0,0,0),(0,0,0),(3,34,73),(2,24,77),(0,45,67),(0,0,0),(0,54,60),(1,54,60),(0,0,0),(0,0,0),(6,52,60),(0,11,80),(1,11,80),(0,0,0),(2,54,60),(0,21,78),(0,0,0),(0,0,0),(4,8,80),(0,48,65),(0,17,79),(0,0,0),(3,24,77),(2,21,78),(0,0,0),(0,0,0),(4,46,66),(2,48,65),(2,17,79),(0,0,0),(7,34,71),(3,45,67),(0,0,0),(0,0,0),(0,12,80),(1,12,80),(5,39,70),(0,0,0),(0,52,62),(1,52,62),(0,0,0),(0,0,0),(2,12,80),(0,37,72),(0,25,77),(0,0,0),(2,52,62),(3,17,79),(0,0,0),(0,0,0),(0,28,76),(0,0,81),(0,1,81),(0,0,0),(4,10,80),(0,2,81),(0,0,0),(0,0,0),(0,22,78),(0,13,80),(0,3,81),(0,0,0),(7,30,73),(2,2,81),(0,0,0),(0,0,0),(2,22,78),(0,4,81),(1,4,81),(0,0,0),(3,37,72),(0,41,70),(0,0,0),(0,0,0),(7,0,79),(2,4,81),(0,5,81),(0,0,0),(3,0,81),(2,41,70),(0,0,0),(0,0,0),(3,2,81),(4,48,65),(2,5,81),(0,0,0),(0,14,80),(0,6,81),(0,0,0),(0,0,0),(7,4,79),(6,12,79),(0,19,79),(0,0,0),(2,14,80),(0,26,77),(0,0,0),(0,0,0),(3,41,70),(5,20,78),(0,7,81),(0,0,0),(4,52,62),(0,23,78),(0,0,0),(0,0,0),(6,0,80),(0,29,76),(1,29,76),(0,0,0),(6,2,80),(2,23,78),(0,0,0),(0,0,0),(3,6,81),(0,8,81),(0,49,65),(0,0,0),(0,38,72),(1,38,72),(0,0,0),(0,0,0),(0,34,74),(1,34,74),(2,49,65),(0,0,0),(2,38,72),(0,54,61),(0,0,0),(0,0,0),(2,34,74),(0,20,79),(0,9,81),(0,0,0),(3,29,76),(2,54,61),(0,0,0),(0,0,0),(7,8,79),(0,32,75),(1,32,75),(0,0,0),(3,8,81),(0,53,62),(0,0,0),(0,0,0),(0,16,80),(1,16,80),(0,27,77),(0,0,0),(0,24,78),(0,10,81),(0,0,0),(0,0,0),(0,42,70),(1,42,70),(2,27,77),(0,0,0),(2,24,78),(2,10,81),(0,0,0),(0,0,0),(2,42,70),(0,52,63),(1,52,63),(0,0,0),(0,30,76),(1,30,76),(0,0,0),(0,0,0),(3,53,62),(2,52,63),(0,11,81),(0,0,0),(2,30,76),(3,27,77),(0,0,0),(0,0,0),(3,10,81),(0,17,80),(1,17,80),(0,0,0),(4,38,72),(5,22,78),(0,0,0),(0,0,0),(4,34,74),(0,44,69),(0,37,73),(0,0,0),(3,52,63),(0,35,74),(0,0,0),(0,0,0),(7,40,69),(0,12,81),(1,12,81),(0,0,0),(8,36,70),(0,25,78),(0,0,0),(0,0,0),(11,34,65),(0,28,77),(0,33,75),(0,0,0),(3,17,80),(2,25,78),(0,0,0),(0,0,0),(4,16,80),(2,28,77),(0,41,71),(0,0,0),(0,0,82),(0,1,82),(0,0,0),(0,0,0),(0,2,82),(1,2,82),(0,13,81),(0,0,0),(2,0,82),(0,3,82),(0,0,0),(0,0,0),(0,56,60),(0,31,76),(1,31,76),(0,0,0),(0,4,82),(1,4,82),(0,0,0),(0,0,0),(2,56,60),(2,31,76),(0,55,61),(0,0,0),(2,4,82),(0,5,82),(0,0,0),(0,0,0),(3,1,82),(4,17,80),(2,55,61),(0,0,0),(7,22,77),(0,14,81),(0,0,0),(0,0,0),(0,6,82),(0,19,80),(1,19,80),(0,0,0),(3,31,76),(2,14,81),(0,0,0),(0,0,0),(2,6,82),(2,19,80),(0,23,79),(0,0,0),(0,36,74),(0,7,82),(0,0,0),(0,0,0),(3,5,82),(4,28,77),(0,53,63),(0,0,0),(2,36,74),(0,34,75),(0,0,0),(0,0,0),(0,40,72),(1,40,72),(0,15,81),(0,0,0),(0,8,82),(1,8,82),(0,0,0),(0,0,0),(2,40,72),(0,48,67),(1,48,67),(0,0,0),(2,8,82),(3,23,79),(0,0,0),(0,0,0),(0,20,80),(1,20,80),(6,5,81),(0,0,0),(4,4,82),(0,9,82),(0,0,0),(0,0,0),(2,20,80),(7,15,79),(4,55,61),(0,0,0),(6,14,80),(0,27,78),(0,0,0),(0,0,0),(7,43,68),(0,16,81),(1,16,81),(0,0,0),(3,48,67),(2,27,78),(0,0,0),(0,0,0),(0,10,82),(1,10,82),(0,51,65),(0,0,0),(7,34,73),(0,30,77),(0,0,0),(0,0,0),(2,10,82),(0,47,68),(1,47,68),(0,0,0),(0,44,70),(1,44,70),(0,0,0),(0,0,0),(3,27,78),(0,21,80),(1,21,80),(0,0,0),(2,44,70),(0,11,82),(0,0,0),(0,0,0),(4,40,72),(0,57,60),(0,17,81),(0,0,0),(4,8,82),(2,11,82),(0,0,0),(0,0,0),(0,50,66),(0,56,61),(1,56,61),(0,0,0),(3,47,68),(5,56,60),(0,0,0),(0,0,0),(2,50,66),(0,33,76),(0,25,79),(0,0,0),(0,12,82),(0,55,62),(0,0,0),(0,0,0),(3,11,82),(2,33,76),(2,25,79),(0,0,0),(2,12,82),(0,46,69),(0,0,0),(0,0,0),(6,42,70),(4,16,81),(5,14,81),(0,0,0),(0,22,80),(0,18,81),(0,0,0),(0,0,0),(4,10,82),(0,0,83),(0,1,83),(0,0,0),(2,22,80),(0,2,83),(0,0,0),(0,0,0),(3,55,62),(2,0,83),(0,3,83),(0,0,0),(4,44,70),(2,2,83),(0,0,0),(0,0,0),(3,46,69),(0,4,83),(1,4,83),(0,0,0),(7,2,81),(4,11,82),(0,0,0),(0,0,0),(3,18,81),(2,4,83),(0,5,83),(0,0,0),(3,0,83),(0,26,79),(0,0,0),(0,0,0),(0,14,82),(0,36,75),(0,19,81),(0,0,0),(7,41,70),(0,6,83),(0,0,0),(0,0,0),(0,48,68),(0,23,80),(1,23,80),(0,0,0),(0,34,76),(1,34,76),(0,0,0),(0,0,0),(2,48,68),(2,23,80),(0,7,83),(0,0,0),(2,34,76),(3,5,83),(0,0,0),(0,0,0),(3,26,79),(7,19,79),(2,7,83),(0,0,0),(0,42,72),(0,15,82),(0,0,0),(0,0,0),(3,6,83),(0,8,83),(1,8,83),(0,0,0),(2,42,72),(0,51,66),(0,0,0),(0,0,0),(7,29,76),(0,20,81),(0,59,59),(0,0,0),(0,58,60),(1,58,60),(0,0,0),(0,0,0),(7,8,81),(2,20,81),(0,9,83),(0,0,0),(2,58,60),(6,14,81),(0,0,0),(0,0,0),(0,24,80),(0,44,71),(1,44,71),(0,0,0),(0,16,82),(1,16,82),(0,0,0),(0,0,0),(0,30,78),(1,30,78),(4,19,81),(0,0,0),(2,16,82),(0,10,83),(0,0,0),(0,0,0),(2,30,78),(4,23,80),(0,37,75),(0,0,0),(4,34,76),(0,39,74),(0,0,0),(0,0,0)]

def wits_7 : List (ℕ × ℕ × ℕ) := [(6,40,72),(0,35,76),(0,21,81),(0,0,0),(3,44,71),(2,39,74),(0,0,0),(0,0,0),(14,30,58),(2,35,76),(0,11,83),(0,0,0),(0,54,64),(0,17,82),(0,0,0),(0,0,0),(0,46,70),(1,46,70),(0,33,77),(0,0,0),(2,54,64),(2,17,82),(0,0,0),(0,0,0),(2,46,70),(0,25,80),(1,25,80),(0,0,0),(3,35,76),(3,21,81),(0,0,0),(0,0,0),(7,17,80),(0,12,83),(0,53,65),(0,0,0),(14,14,64),(3,11,83),(0,0,0),(0,0,0),(3,17,82),(2,12,83),(2,53,65),(0,0,0),(4,16,82),(0,22,81),(0,0,0),(0,0,0),(0,18,82),(1,18,82),(5,6,83),(0,0,0),(3,25,80),(2,22,81),(0,0,0),(0,0,0),(0,0,84),(0,1,84),(0,13,83),(0,0,0),(0,2,84),(1,2,84),(0,0,0),(0,0,0),(2,0,84),(0,3,84),(0,45,71),(0,0,0),(2,2,84),(0,38,75),(0,0,0),(0,0,0),(0,4,84),(1,4,84),(2,45,71),(0,0,0),(0,26,80),(1,26,80),(0,0,0),(0,0,0),(2,4,84),(0,5,84),(0,29,79),(0,0,0),(2,26,80),(0,14,83),(0,0,0),(0,0,0),(10,2,78),(2,5,84),(0,23,81),(0,0,0),(0,6,84),(0,42,73),(0,0,0),(0,0,0),(3,38,75),(4,12,83),(2,23,81),(0,0,0),(2,6,84),(2,42,73),(0,0,0),(0,0,0),(7,19,80),(0,7,84),(1,7,84),(0,0,0),(0,32,78),(0,47,70),(0,0,0),(0,0,0),(3,14,83),(2,7,84),(0,15,83),(0,0,0),(2,32,78),(2,47,70),(0,0,0),(0,0,0),(0,8,84),(0,55,64),(1,55,64),(0,0,0),(0,20,82),(1,20,82),(0,0,0),(0,0,0),(2,8,84),(0,27,80),(1,27,80),(0,0,0),(2,20,82),(4,38,75),(0,0,0),(0,0,0),(3,47,70),(0,9,84),(1,9,84),(0,0,0),(4,26,80),(0,30,79),(0,0,0),(0,0,0),(6,48,68),(0,16,83),(0,39,75),(0,0,0),(3,55,64),(2,30,79),(0,0,0),(0,0,0),(10,26,74),(2,16,83),(0,35,77),(0,0,0),(0,10,84),(0,41,74),(0,0,0),(0,0,0),(7,16,81),(8,32,75),(0,49,69),(0,0,0),(2,10,84),(0,21,82),(0,0,0),(0,0,0),(3,30,79),(4,7,84),(2,49,69),(0,0,0),(3,16,83),(0,33,78),(0,0,0),(0,0,0),(7,47,68),(0,11,84),(0,17,83),(0,0,0),(6,58,60),(2,33,78),(0,0,0),(0,0,0),(0,28,80),(1,28,80),(0,25,81),(0,0,0),(4,20,82),(3,49,69),(0,0,0),(0,0,0),(2,28,80),(0,52,67),(1,52,67),(0,0,0),(6,16,82),(5,4,84),(0,0,0),(0,0,0),(0,12,84),(1,12,84),(0,31,79),(0,0,0),(0,48,70),(1,48,70),(0,0,0),(0,0,0),(0,22,82),(0,45,72),(1,45,72),(0,0,0),(2,48,70),(0,18,83),(0,0,0),(0,0,0),(2,22,82),(2,45,72),(0,57,63),(0,0,0),(0,38,76),(1,38,76),(0,0,0),(0,0,0),(10,40,68),(0,0,85),(0,1,85),(0,0,0),(2,38,76),(0,2,85),(0,0,0),(0,0,0),(0,56,64),(1,56,64),(0,3,85),(0,0,0),(3,45,72),(0,26,81),(0,0,0),(0,0,0),(0,34,78),(0,4,85),(1,4,85),(0,0,0),(11,27,72),(2,26,81),(0,0,0),(0,0,0),(2,34,78),(2,4,85),(0,5,85),(0,0,0),(0,14,84),(0,23,82),(0,0,0),(0,0,0),(3,2,85),(4,52,67),(2,5,85),(0,0,0),(2,14,84),(0,6,85),(0,0,0),(0,0,0),(3,26,81),(0,32,79),(1,32,79),(0,0,0),(3,4,85),(2,6,85),(0,0,0),(0,0,0),(0,54,66),(1,54,66),(0,7,85),(0,0,0),(6,2,84),(3,5,85),(0,0,0),(0,0,0),(2,54,66),(0,15,84),(1,15,84),(0,0,0),(4,38,76),(6,38,75),(0,0,0),(0,0,0),(3,6,85),(0,8,85),(0,27,81),(0,0,0),(3,32,79),(4,2,85),(0,0,0),(0,0,0),(4,56,64),(0,39,76),(0,37,77),(0,0,0),(0,24,82),(0,49,70),(0,0,0),(0,0,0),(4,34,78),(2,39,76),(0,9,85),(0,0,0),(2,24,82),(0,35,78),(0,0,0),(0,0,0),(0,16,84),(1,16,84),(2,9,85),(0,0,0),(3,8,85),(2,35,78),(0,0,0),(0,0,0),(2,16,84),(0,60,61),(1,60,61),(0,0,0),(3,39,76),(0,10,85),(0,0,0),(0,0,0),(0,52,68),(1,52,68),(0,21,83),(0,0,0),(7,10,83),(0,58,63),(0,0,0),(0,0,0),(2,52,68),(6,55,64),(2,21,83),(0,0,0),(6,20,82),(2,58,63),(0,0,0),(0,0,0),(7,35,76),(0,17,84),(0,11,85),(0,0,0),(3,60,61),(0,25,82),(0,0,0),(0,0,0),(3,10,85),(2,17,84),(0,45,73),(0,0,0),(7,17,82),(2,25,82),(0,0,0),(0,0,0),(3,58,63),(0,31,80),(0,51,69),(0,0,0),(4,24,82),(4,49,70),(0,0,0),(0,0,0),(7,25,80),(0,12,85),(1,12,85),(0,0,0),(3,17,84),(0,22,83),(0,0,0),(0,0,0),(0,40,76),(1,40,76),(5,23,82),(0,0,0),(0,18,84),(0,55,66),(0,0,0),(0,0,0),(2,40,76),(4,60,61),(5,6,85),(0,0,0),(2,18,84),(0,42,75),(0,0,0),(0,0,0),(4,52,68),(0,47,72),(0,13,85),(0,0,0),(0,0,86),(0,1,86),(0,0,0),(0,0,0),(0,2,86),(1,2,86),(0,29,81),(0,0,0),(2,0,86),(0,3,86),(0,0,0),(0,0,0),(2,2,86),(4,17,84),(2,29,81),(0,0,0),(0,4,86),(1,4,86),(0,0,0),(0,0,0),(3,42,75),(0,19,84),(0,23,83),(0,0,0),(2,4,86),(0,5,86),(0,0,0),(0,0,0),(0,32,80),(1,32,80),(2,23,83),(0,0,0),(7,14,83),(2,5,86),(0,0,0),(0,0,0),(0,6,86),(0,53,68),(1,53,68),(0,0,0),(6,38,76),(4,22,83),(0,0,0),(0,0,0),(2,6,86),(2,53,68),(0,49,71),(0,0,0),(0,60,62),(0,7,86),(0,0,0),(0,0,0),(3,5,86),(10,7,80),(0,15,85),(0,0,0),(2,60,62),(0,27,82),(0,0,0),(0,0,0),(0,20,84),(0,41,76),(1,41,76),(0,0,0),(0,8,86),(0,30,81),(0,0,0),(0,0,0),(2,20,84),(0,24,83),(0,35,79),(0,0,0),(2,8,86),(2,30,81),(0,0,0),(0,0,0),(3,7,86),(2,24,83),(0,43,75),(0,0,0),(4,4,86),(0,9,86),(0,0,0),(0,0,0),(3,27,82),(0,16,85),(1,16,85),(0,0,0),(3,41,76),(2,9,86),(0,0,0),(0,0,0),(0,48,72),(0,33,80),(1,33,80),(0,0,0),(0,56,66),(1,56,66),(0,0,0),(0,0,0),(0,10,86),(0,21,84),(1,21,84),(0,0,0),(2,56,66),(0,45,74),(0,0,0),(0,0,0),(2,10,86),(2,21,84),(4,49,71),(0,0,0),(0,28,82),(1,28,82),(0,0,0),(0,0,0),(14,12,68),(6,39,76),(0,17,85),(0,0,0),(2,28,82),(0,11,86),(0,0,0),(0,0,0),(4,20,84),(4,41,76),(0,31,81),(0,0,0),(3,21,84),(2,11,86),(0,0,0),(0,0,0),(0,38,78),(0,40,77),(1,40,77),(0,0,0),(11,24,75),(14,42,55),(0,0,0),(0,0,0),(2,38,78),(0,36,79),(0,47,73),(0,0,0),(0,12,86),(0,50,71),(0,0,0),(0,0,0),(3,11,86),(2,36,79),(2,47,73),(0,0,0),(2,12,86),(0,18,85),(0,0,0),(0,0,0),(4,48,72),(4,33,80),(10,25,77),(0,0,0),(0,34,80),(1,34,80),(0,0,0),(0,0,0),(4,10,86),(0,44,75),(1,44,75),(0,0,0),(2,34,80),(0,13,86),(0,0,0),(0,0,0),(3,50,71),(0,0,87),(0,1,87),(0,0,0),(4,28,82),(0,2,87),(0,0,0),(0,0,0),(3,18,85),(0,59,64),(0,3,87),(0,0,0),(7,26,81),(2,2,87),(0,0,0),(0,0,0),(7,4,85),(0,4,87),(0,19,85),(0,0,0),(3,44,75),(0,58,65),(0,0,0),(0,0,0),(0,14,86),(1,14,86),(0,5,87),(0,0,0),(3,0,87),(2,58,65),(0,0,0),(0,0,0),(2,14,86),(4,36,79),(2,5,87),(0,0,0),(0,52,70),(0,6,87),(0,0,0),(0,0,0),(7,32,79),(6,47,72),(0,37,79),(0,0,0),(2,52,70),(2,6,87),(0,0,0),(0,0,0),(3,58,65),(5,56,66),(0,7,87),(0,0,0),(4,34,80),(0,15,86),(0,0,0),(0,0,0),(0,30,82),(0,20,85),(1,20,85),(0,0,0),(6,4,86),(2,15,86),(0,0,0),(0,0,0),(0,24,84),(0,8,87),(1,8,87),(0,0,0),(8,20,82),(3,37,79),(0,0,0),(0,0,0),(2,24,84),(2,8,87),(0,51,71),(0,0,0),(7,49,70),(3,7,87),(0,0,0),(0,0,0),(3,15,86),(0,55,68),(0,9,87),(0,0,0),(0,16,86),(1,16,86),(0,0,0),(0,0,0),(4,14,86),(2,55,68),(2,9,87),(0,0,0),(2,16,86),(6,7,86),(0,0,0),(0,0,0),(7,60,61),(5,12,86),(0,21,85),(0,0,0),(4,52,70),(0,10,87),(0,0,0),(0,0,0),(6,20,84),(0,28,83),(1,28,83),(0,0,0),(3,55,68),(0,54,69),(0,0,0),(0,0,0),(14,6,70),(0,25,84),(1,25,84),(0,0,0),(0,40,78),(0,17,86),(0,0,0),(0,0,0),(0,62,62),(1,62,62),(0,11,87),(0,0,0),(2,40,78),(0,42,77),(0,0,0),(0,0,0),(0,36,80),(1,36,80),(2,11,87),(0,0,0),(3,28,83),(2,42,77),(0,0,0),(0,0,0),(2,36,80),(6,33,80),(0,59,65),(0,0,0),(3,25,84),(0,22,85),(0,0,0),(0,0,0),(0,44,76),(0,12,87),(1,12,87),(0,0,0),(4,16,86),(0,34,81),(0,0,0),(0,0,0),(0,18,86),(1,18,86),(10,41,71),(0,0,0),(6,28,82),(2,34,81),(0,0,0),(0,0,0),(2,18,86),(5,52,70),(0,29,83),(0,0,0),(0,26,84),(1,26,84),(0,0,0),(0,0,0),(3,22,85),(4,28,83),(0,13,87),(0,0,0),(2,26,84),(0,46,75),(0,0,0),(0,0,0),(0,0,88),(0,1,88),(1,1,88),(0,0,0),(0,2,88),(1,2,88),(0,0,0),(0,0,0),(2,0,88),(0,3,88),(0,23,85),(0,0,0),(2,2,88),(0,19,86),(0,0,0),(0,0,0),(0,4,88),(1,4,88),(0,39,79),(0,0,0),(7,5,86),(0,14,87),(0,0,0),(0,0,0),(2,4,88),(0,5,88),(1,5,88),(0,0,0),(3,1,88),(2,14,87),(0,0,0),(0,0,0),(4,44,76),(2,5,88),(0,43,77),(0,0,0),(0,6,88),(1,6,88),(0,0,0),(0,0,0),(3,19,86),(0,27,84),(0,35,81),(0,0,0),(2,6,88),(0,30,83),(0,0,0),(0,0,0),(3,14,87),(0,7,88),(0,15,87),(0,0,0),(0,20,86),(1,20,86),(0,0,0),(0,0,0),(7,41,76),(0,24,85),(1,24,85),(0,0,0),(2,20,86),(3,43,77),(0,0,0),(0,0,0),(0,8,88),(1,8,88),(5,17,86),(0,0,0),(3,27,84),(0,33,82),(0,0,0),(0,0,0),(0,54,70),(0,61,64),(1,61,64),(0,0,0),(3,7,88),(2,33,82),(0,0,0),(0,0,0),(2,54,70),(0,9,88),(1,9,88),(0,0,0),(3,24,85),(0,50,73),(0,0,0),(0,0,0),(7,33,80),(2,9,88),(0,47,75),(0,0,0),(10,44,70),(0,21,86),(0,0,0),(0,0,0),(0,28,84),(0,40,79),(1,40,79),(0,0,0),(0,10,88),(1,10,88),(0,0,0),(0,0,0),(0,42,78),(1,42,78),(0,25,85),(0,0,0),(2,10,88),(0,58,67),(0,0,0),(0,0,0),(2,42,78),(0,36,81),(0,17,87),(0,0,0),(4,20,86),(2,58,67),(0,0,0),(0,0,0),(3,21,86),(0,11,88),(1,11,88),(0,0,0),(3,40,79),(5,0,88),(0,0,0),(0,0,0),(4,8,88),(0,57,68),(1,57,68),(0,0,0),(12,8,78),(0,49,74),(0,0,0),(0,0,0),(0,22,86),(1,22,86),(5,19,86),(0,0,0),(3,36,81),(2,49,74),(0,0,0),(0,0,0),(0,12,88),(1,12,88),(5,14,87),(0,0,0),(0,46,76),(0,18,87),(0,0,0),(0,0,0),(2,12,88),(0,29,84),(1,29,84),(0,0,0),(2,46,76),(0,26,85),(0,0,0),(0,0,0),(3,49,74),(2,29,84),(6,11,87),(0,0,0),(4,10,88),(2,26,85),(0,0,0),(0,0,0),(4,42,78),(0,13,88),(1,13,88),(0,0,0),(7,2,87),(4,58,67),(0,0,0),(0,0,0),(3,18,87),(0,0,89),(0,1,89),(0,0,0),(3,29,84),(0,2,89),(0,0,0),(0,0,0),(3,26,85),(0,48,75),(0,3,89),(0,0,0),(7,58,65),(0,43,78),(0,0,0),(0,0,0),(6,18,86),(0,4,89),(0,63,63),(0,0,0),(0,14,88),(1,14,88),(0,0,0),(0,0,0),(4,22,86),(2,4,89),(0,5,89),(0,0,0),(2,14,88),(0,35,82),(0,0,0),(0,0,0),(3,2,89),(7,37,79),(0,27,85),(0,0,0),(0,30,84),(0,6,89),(0,0,0),(0,0,0),(3,43,78),(4,29,84),(2,27,85),(0,0,0),(2,30,84),(2,6,89),(0,0,0),(0,0,0),(7,20,85),(0,15,88),(0,7,89),(0,0,0),(0,24,86),(1,24,86),(0,0,0),(0,0,0),(0,50,74),(1,50,74),(0,33,83),(0,0,0),(2,24,86),(3,27,85),(0,0,0),(0,0,0),(2,50,74),(0,8,89),(1,8,89),(0,0,0),(0,58,68),(1,58,68),(0,0,0),(0,0,0),(7,55,68),(0,53,72),(1,53,72),(0,0,0),(2,58,68),(3,7,89),(0,0,0),(0,0,0)]

def wits_8 : List (ℕ × ℕ × ℕ) := [(0,16,88),(1,16,88),(0,9,89),(0,0,0),(4,14,88),(0,38,81),(0,0,0),(0,0,0),(2,16,88),(0,28,85),(0,21,87),(0,0,0),(3,8,89),(2,38,81),(0,0,0),(0,0,0),(7,28,83),(0,31,84),(1,31,84),(0,0,0),(0,36,82),(0,10,89),(0,0,0),(0,0,0),(6,8,88),(2,31,84),(0,49,75),(0,0,0),(2,36,82),(2,10,89),(0,0,0),(0,0,0),(3,38,81),(0,17,88),(1,17,88),(0,0,0),(0,56,70),(1,56,70),(0,0,0),(0,0,0),(4,50,74),(2,17,88),(0,11,89),(0,0,0),(2,56,70),(0,34,83),(0,0,0),(0,0,0),(3,10,89),(4,8,89),(2,11,89),(0,0,0),(4,58,68),(0,22,87),(0,0,0),(0,0,0),(6,28,84),(4,53,72),(5,43,78),(0,0,0),(3,17,88),(2,22,87),(0,0,0),(0,0,0),(4,16,88),(0,12,89),(0,29,85),(0,0,0),(0,18,88),(0,62,65),(0,0,0),(0,0,0),(0,26,86),(1,26,86),(2,29,85),(0,0,0),(2,18,88),(0,51,74),(0,0,0),(0,0,0),(0,32,84),(0,41,80),(0,39,81),(0,0,0),(4,36,82),(2,51,74),(0,0,0),(0,0,0),(2,32,84),(0,60,67),(0,13,89),(0,0,0),(3,12,89),(0,37,82),(0,0,0),(0,0,0),(3,62,65),(2,60,67),(0,23,87),(0,0,0),(0,0,90),(0,1,90),(0,0,0),(0,0,0),(0,2,90),(0,19,88),(1,19,88),(0,0,0),(2,0,90),(0,3,90),(0,0,0),(0,0,0),(2,2,90),(2,19,88),(0,35,83),(0,0,0),(0,4,90),(0,14,89),(0,0,0),(0,0,0),(3,37,82),(7,43,77),(2,35,83),(0,0,0),(2,4,90),(0,5,90),(0,0,0),(0,0,0),(3,1,90),(4,12,89),(4,29,85),(0,0,0),(3,19,88),(2,5,90),(0,0,0),(0,0,0),(0,6,90),(1,6,90),(0,47,77),(0,0,0),(15,2,69),(3,35,83),(0,0,0),(0,0,0),(0,20,88),(0,24,87),(0,15,89),(0,0,0),(11,16,81),(0,7,90),(0,0,0),(0,0,0),(2,20,88),(2,24,87),(2,15,89),(0,0,0),(6,14,88),(2,7,90),(0,0,0),(0,0,0),(7,61,64),(0,40,81),(1,40,81),(0,0,0),(0,8,90),(1,8,90),(0,0,0),(0,0,0),(0,38,82),(1,38,82),(5,34,83),(0,0,0),(2,8,90),(3,15,89),(0,0,0),(0,0,0),(2,38,82),(0,16,89),(1,16,89),(0,0,0),(0,28,86),(0,9,90),(0,0,0),(0,0,0),(7,40,79),(0,21,88),(0,31,85),(0,0,0),(2,28,86),(2,9,90),(0,0,0),(0,0,0),(0,64,64),(1,64,64),(0,25,87),(0,0,0),(7,58,67),(5,26,86),(0,0,0),(0,0,0),(0,10,90),(1,10,90),(2,25,87),(0,0,0),(3,16,89),(5,32,84),(0,0,0),(0,0,0),(2,10,90),(0,55,72),(0,17,89),(0,0,0),(0,34,84),(1,34,84),(0,0,0),(0,0,0),(6,16,88),(2,55,72),(2,17,89),(0,0,0),(2,34,84),(0,11,90),(0,0,0),(0,0,0),(0,60,68),(1,60,68),(0,51,75),(0,0,0),(0,22,88),(1,22,88),(0,0,0),(0,0,0),(2,60,68),(0,48,77),(1,48,77),(0,0,0),(2,22,88),(0,29,86),(0,0,0),(0,0,0),(7,29,84),(2,48,77),(0,41,81),(0,0,0),(0,12,90),(0,18,89),(0,0,0),(0,0,0),(3,11,90),(0,32,85),(1,32,85),(0,0,0),(2,12,90),(2,18,89),(0,0,0),(0,0,0),(4,64,64),(2,32,85),(0,37,83),(0,0,0),(3,48,77),(5,6,90),(0,0,0),(0,0,0),(0,58,70),(1,58,70),(0,45,79),(0,0,0),(7,2,89),(0,13,90),(0,0,0),(0,0,0),(2,58,70),(0,23,88),(1,23,88),(0,0,0),(0,50,76),(1,50,76),(0,0,0),(0,0,0),(7,4,89),(0,0,91),(0,1,91),(0,0,0),(2,50,76),(0,2,91),(0,0,0),(0,0,0),(4,60,68),(2,0,91),(0,3,91),(0,0,0),(4,22,88),(0,47,78),(0,0,0),(0,0,0),(0,14,90),(0,4,91),(0,27,87),(0,0,0),(3,23,88),(2,47,78),(0,0,0),(0,0,0),(2,14,90),(2,4,91),(0,5,91),(0,0,0),(3,0,91),(3,1,91),(0,0,0),(0,0,0),(3,2,91),(4,32,85),(0,33,85),(0,0,0),(6,0,90),(0,6,91),(0,0,0),(0,0,0),(0,24,88),(0,20,89),(1,20,89),(0,0,0),(0,40,82),(0,15,90),(0,0,0),(0,0,0),(2,24,88),(0,52,75),(0,7,91),(0,0,0),(2,40,82),(0,38,83),(0,0,0),(0,0,0),(0,44,80),(1,44,80),(2,7,91),(0,0,0),(4,50,76),(2,38,83),(0,0,0),(0,0,0),(2,44,80),(0,8,91),(1,8,91),(0,0,0),(3,20,89),(4,2,91),(0,0,0),(0,0,0),(0,36,84),(0,28,87),(0,55,73),(0,0,0),(0,16,90),(0,31,86),(0,0,0),(0,0,0),(2,36,84),(0,60,69),(0,9,91),(0,0,0),(2,16,90),(2,31,86),(0,0,0),(0,0,0),(15,32,63),(0,25,88),(1,25,88),(0,0,0),(3,8,91),(10,22,83),(0,0,0),(0,0,0),(7,17,88),(0,51,76),(1,51,76),(0,0,0),(3,28,87),(0,10,91),(0,0,0),(0,0,0),(3,31,86),(2,51,76),(12,27,77),(0,0,0),(0,48,78),(0,17,90),(0,0,0),(0,0,0),(0,54,74),(1,54,74),(4,7,91),(0,0,0),(2,48,78),(2,17,90),(0,0,0),(0,0,0),(2,54,74),(5,50,76),(0,11,91),(0,0,0),(3,51,76),(0,22,89),(0,0,0),(0,0,0),(3,10,91),(4,8,91),(0,29,87),(0,0,0),(7,62,65),(2,22,89),(0,0,0),(0,0,0),(3,17,90),(4,28,87),(2,29,87),(0,0,0),(0,26,88),(1,26,88),(0,0,0),(0,0,0),(0,18,90),(0,12,91),(1,12,91),(0,0,0),(2,26,88),(0,50,77),(0,0,0),(0,0,0),(2,18,90),(0,57,72),(0,53,75),(0,0,0),(7,37,82),(2,50,77),(0,0,0),(0,0,0),(6,60,68),(2,57,72),(2,53,75),(0,0,0),(6,22,88),(4,10,91),(0,0,0),(0,0,0),(7,19,88),(5,40,82),(0,13,91),(0,0,0),(0,64,66),(1,64,66),(0,0,0),(0,0,0),(3,50,77),(7,35,83),(0,63,67),(0,0,0),(2,64,66),(0,19,90),(0,0,0),(0,0,0),(0,0,92),(0,1,92),(1,1,92),(0,0,0),(0,2,92),(0,30,87),(0,0,0),(0,0,0),(2,0,92),(0,3,92),(1,3,92),(0,0,0),(2,2,92),(0,14,91),(0,0,0),(0,0,0),(0,4,92),(1,4,92),(0,61,69),(0,0,0),(4,26,88),(0,33,86),(0,0,0),(0,0,0),(0,42,82),(0,5,92),(1,5,92),(0,0,0),(3,1,92),(2,33,86),(0,0,0),(0,0,0),(2,42,82),(0,24,89),(1,24,89),(0,0,0),(0,6,92),(0,55,74),(0,0,0),(0,0,0),(3,14,91),(2,24,89),(0,15,91),(0,0,0),(2,6,92),(2,55,74),(0,0,0),(0,0,0),(3,33,86),(0,7,92),(1,7,92),(0,0,0),(0,46,80),(1,46,80),(0,0,0),(0,0,0),(7,16,89),(0,36,85),(0,59,71),(0,0,0),(2,46,80),(4,19,90),(0,0,0),(0,0,0),(0,8,92),(1,8,92),(0,31,87),(0,0,0),(4,2,92),(3,15,91),(0,0,0),(0,0,0),(2,8,92),(0,16,91),(1,16,91),(0,0,0),(3,7,92),(0,21,90),(0,0,0),(0,0,0),(4,4,92),(0,9,92),(0,25,89),(0,0,0),(0,58,72),(1,58,72),(0,0,0),(0,0,0),(0,34,86),(1,34,86),(2,25,89),(0,0,0),(2,58,72),(3,31,87),(0,0,0),(0,0,0),(2,34,86),(4,24,89),(14,43,63),(0,0,0),(0,10,92),(1,10,92),(0,0,0),(0,0,0),(3,21,90),(6,28,87),(0,17,91),(0,0,0),(2,10,92),(0,43,82),(0,0,0),(0,0,0),(7,48,77),(0,39,84),(0,57,73),(0,0,0),(4,46,80),(0,65,66),(0,0,0),(0,0,0),(0,22,90),(0,11,92),(0,45,81),(0,0,0),(7,18,89),(2,65,66),(0,0,0),(0,0,0),(2,22,90),(0,32,87),(0,37,85),(0,0,0),(11,32,79),(0,26,89),(0,0,0),(0,0,0),(3,43,82),(2,32,87),(2,37,85),(0,0,0),(3,39,84),(0,18,91),(0,0,0),(0,0,0),(0,12,92),(0,47,80),(1,47,80),(0,0,0),(0,56,74),(1,56,74),(0,0,0),(0,0,0),(2,12,92),(2,47,80),(6,11,91),(0,0,0),(2,56,74),(0,35,86),(0,0,0),(0,0,0),(3,26,89),(5,6,92),(5,55,74),(0,0,0),(4,10,92),(0,23,90),(0,0,0),(0,0,0),(3,18,91),(0,13,92),(1,13,92),(0,0,0),(3,47,80),(2,23,90),(0,0,0),(0,0,0),(6,18,90),(0,60,71),(0,19,91),(0,0,0),(0,30,88),(1,30,88),(0,0,0),(0,0,0),(3,35,86),(0,0,93),(0,1,93),(0,0,0),(2,30,88),(0,2,93),(0,0,0),(0,0,0),(0,40,84),(1,40,84),(0,3,93),(0,0,0),(0,14,92),(1,14,92),(0,0,0),(0,0,0),(2,40,84),(0,4,93),(1,4,93),(0,0,0),(2,14,92),(0,38,85),(0,0,0),(0,0,0),(4,12,92),(2,4,93),(0,5,93),(0,0,0),(0,24,90),(0,46,81),(0,0,0),(0,0,0),(3,2,93),(0,20,91),(1,20,91),(0,0,0),(2,24,90),(0,6,93),(0,0,0),(0,0,0),(7,8,91),(0,15,92),(1,15,92),(0,0,0),(0,36,86),(0,58,73),(0,0,0),(0,0,0),(3,38,85),(2,15,92),(0,7,93),(0,0,0),(2,36,86),(2,58,73),(0,0,0),(0,0,0),(0,48,80),(0,28,89),(1,28,89),(0,0,0),(3,20,91),(5,22,90),(0,0,0),(0,0,0),(0,66,66),(0,8,93),(0,65,67),(0,0,0),(3,15,92),(4,2,93),(0,0,0),(0,0,0),(0,16,92),(1,16,92),(0,21,91),(0,0,0),(4,14,92),(0,25,90),(0,0,0),(0,0,0),(2,16,92),(4,4,93),(0,9,93),(0,0,0),(3,28,89),(2,25,90),(0,0,0),(0,0,0),(8,60,68),(0,41,84),(0,43,83),(0,0,0),(3,8,93),(0,50,79),(0,0,0),(0,0,0),(0,62,70),(1,62,70),(0,39,85),(0,0,0),(7,22,89),(0,10,93),(0,0,0),(0,0,0),(2,62,70),(0,17,92),(1,17,92),(0,0,0),(4,36,86),(2,10,93),(0,0,0),(0,0,0),(10,4,88),(0,56,75),(0,29,89),(0,0,0),(3,41,84),(0,22,91),(0,0,0),(0,0,0),(0,32,88),(1,32,88),(0,11,93),(0,0,0),(7,50,77),(2,22,91),(0,0,0),(0,0,0),(0,26,90),(1,26,90),(2,11,93),(0,0,0),(3,17,92),(5,40,84),(0,0,0),(0,0,0),(0,60,72),(1,60,72),(4,21,91),(0,0,0),(0,18,92),(1,18,92),(0,0,0),(0,0,0),(2,60,72),(0,12,93),(0,35,87),(0,0,0),(2,18,92),(3,11,93),(0,0,0),(0,0,0),(6,22,90),(0,49,80),(1,49,80),(0,0,0),(7,19,90),(4,50,79),(0,0,0),(0,0,0),(4,62,70),(2,49,80),(0,23,91),(0,0,0),(7,30,87),(4,10,93),(0,0,0),(0,0,0),(7,3,92),(4,17,92),(0,13,93),(0,0,0),(0,42,84),(0,30,89),(0,0,0),(0,0,0),(6,12,92),(0,19,92),(1,19,92),(0,0,0),(2,42,84),(0,27,90),(0,0,0),(0,0,0),(4,32,88),(0,33,88),(1,33,88),(0,0,0),(0,0,94),(0,1,94),(0,0,0),(0,0,0),(0,2,94),(1,2,94),(0,51,79),(0,0,0),(2,0,94),(0,3,94),(0,0,0),(0,0,0),(2,2,94),(0,65,68),(1,65,68),(0,0,0),(0,4,94),(1,4,94),(0,0,0),(0,0,0),(3,27,90),(0,24,91),(1,24,91),(0,0,0),(2,4,94),(0,5,94),(0,0,0),(0,0,0),(0,20,92),(0,36,87),(1,36,87),(0,0,0),(8,16,90),(0,63,70),(0,0,0),(0,0,0),(0,6,94),(1,6,94),(0,15,93),(0,0,0),(3,65,68),(2,63,70),(0,0,0),(0,0,0),(2,6,94),(6,4,93),(0,31,89),(0,0,0),(0,28,90),(0,7,94),(0,0,0),(0,0,0),(3,5,94),(4,19,92),(2,31,89),(0,0,0),(2,28,90),(0,53,78),(0,0,0),(0,0,0),(3,63,70),(4,33,88),(13,35,74),(0,0,0),(0,8,94),(1,8,94),(0,0,0),(0,0,0),(4,2,94),(0,16,93),(0,25,91),(0,0,0),(2,8,94),(3,31,89),(0,0,0),(0,0,0),(0,56,76),(1,56,76),(0,45,83),(0,0,0),(4,4,94),(0,9,94),(0,0,0),(0,0,0),(2,56,76),(4,24,91),(2,45,83),(0,0,0),(7,65,66),(2,9,94),(0,0,0),(0,0,0),(4,20,92),(0,60,73),(1,60,73),(0,0,0),(3,16,93),(0,47,82),(0,0,0),(0,0,0),(0,10,94),(1,10,94),(0,17,93),(0,0,0),(7,26,89),(0,29,90),(0,0,0),(0,0,0),(2,10,94),(0,32,89),(1,32,89),(0,0,0),(0,22,92),(1,22,92),(0,0,0),(0,0,0),(7,47,80),(2,32,89),(0,55,77),(0,0,0),(2,22,92),(0,11,94),(0,0,0),(0,0,0),(3,47,82),(5,0,94),(0,49,81),(0,0,0),(4,8,94),(2,11,94),(0,0,0),(0,0,0),(3,29,90),(0,35,88),(1,35,88),(0,0,0),(3,32,89),(0,18,93),(0,0,0),(0,0,0),(4,56,76),(2,35,88),(0,67,67),(0,0,0),(0,12,94),(1,12,94),(0,0,0),(0,0,0),(3,11,94),(7,19,91),(0,65,69),(0,0,0),(2,12,94),(0,42,85),(0,0,0),(0,0,0),(0,44,84),(0,23,92),(1,23,92),(0,0,0),(0,40,86),(1,40,86),(0,0,0),(0,0,0)]

def wits_9 : List (ℕ × ℕ × ℕ) := [(0,30,90),(0,51,80),(1,51,80),(0,0,0),(2,40,86),(0,13,94),(0,0,0),(0,0,0),(2,30,90),(2,51,80),(0,19,93),(0,0,0),(4,22,92),(0,38,87),(0,0,0),(0,0,0),(3,42,85),(6,49,80),(2,19,93),(0,0,0),(3,23,92),(2,38,87),(0,0,0),(0,0,0),(7,20,91),(0,0,95),(0,1,95),(0,0,0),(0,48,82),(0,2,95),(0,0,0),(0,0,0),(0,14,94),(1,14,94),(0,3,95),(0,0,0),(2,48,82),(2,2,95),(0,0,0),(0,0,0),(0,24,92),(0,4,95),(1,4,95),(0,0,0),(4,12,94),(6,27,90),(0,0,0),(0,0,0),(2,24,92),(0,20,93),(0,5,95),(0,0,0),(3,0,95),(3,1,95),(0,0,0),(0,0,0),(3,2,95),(2,20,93),(2,5,95),(0,0,0),(4,40,86),(0,6,95),(0,0,0),(0,0,0),(4,30,90),(0,28,91),(1,28,91),(0,0,0),(3,4,95),(2,6,95),(0,0,0),(0,0,0),(10,26,86),(2,28,91),(0,7,95),(0,0,0),(0,60,74),(0,34,89),(0,0,0),(0,0,0),(6,20,92),(0,45,84),(1,45,84),(0,0,0),(2,60,74),(2,34,89),(0,0,0),(0,0,0),(3,6,95),(0,8,95),(0,21,93),(0,0,0),(0,16,94),(1,16,94),(0,0,0),(0,0,0),(4,14,94),(2,8,95),(0,47,83),(0,0,0),(2,16,94),(3,7,95),(0,0,0),(0,0,0),(0,52,80),(1,52,80),(0,9,95),(0,0,0),(3,45,84),(0,55,78),(0,0,0),(0,0,0),(2,52,80),(0,37,88),(1,37,88),(0,0,0),(3,8,95),(0,66,69),(0,0,0),(0,0,0),(8,12,92),(2,37,88),(0,29,91),(0,0,0),(0,32,90),(0,10,95),(0,0,0),(0,0,0),(6,56,76),(4,28,91),(2,29,91),(0,0,0),(2,32,90),(0,22,93),(0,0,0),(0,0,0),(3,55,78),(0,64,71),(1,64,71),(0,0,0),(0,26,92),(1,26,92),(0,0,0),(0,0,0),(3,66,69),(2,64,71),(0,11,95),(0,0,0),(2,26,92),(3,29,91),(0,0,0),(0,0,0),(3,10,95),(0,63,72),(1,63,72),(0,0,0),(4,16,94),(0,54,79),(0,0,0),(0,0,0),(0,18,94),(0,44,85),(0,51,81),(0,0,0),(3,64,71),(2,54,79),(0,0,0),(0,0,0),(2,18,94),(0,12,95),(1,12,95),(0,0,0),(0,46,84),(0,62,73),(0,0,0),(0,0,0),(7,33,88),(2,12,95),(0,23,93),(0,0,0),(2,46,84),(0,30,91),(0,0,0),(0,0,0),(3,54,79),(6,35,88),(2,23,93),(0,0,0),(0,38,88),(0,33,90),(0,0,0),(0,0,0),(7,65,68),(0,27,92),(0,13,95),(0,0,0),(2,38,88),(0,19,94),(0,0,0),(0,0,0),(3,62,73),(2,27,92),(2,13,95),(0,0,0),(4,26,92),(2,19,94),(0,0,0),(0,0,0),(3,30,91),(0,53,80),(1,53,80),(0,0,0),(6,40,86),(13,46,70),(0,0,0),(0,0,0),(0,0,96),(0,1,96),(1,1,96),(0,0,0),(0,2,96),(0,14,95),(0,0,0),(0,0,0),(0,50,82),(0,3,96),(1,3,96),(0,0,0),(2,2,96),(2,14,95),(0,0,0),(0,0,0),(0,4,96),(1,4,96),(5,55,78),(0,0,0),(0,20,94),(1,20,94),(0,0,0),(0,0,0),(2,4,96),(0,5,96),(0,31,91),(0,0,0),(2,20,94),(0,43,86),(0,0,0),(0,0,0),(0,28,92),(1,28,92),(0,15,95),(0,0,0),(0,6,96),(1,6,96),(0,0,0),(0,0,0),(0,34,90),(0,59,76),(1,59,76),(0,0,0),(2,6,96),(4,19,94),(0,0,0),(0,0,0),(2,34,90),(0,7,96),(0,55,79),(0,0,0),(3,5,96),(3,31,91),(0,0,0),(0,0,0),(3,43,86),(2,7,96),(0,25,93),(0,0,0),(7,47,82),(0,21,94),(0,0,0),(0,0,0),(0,8,96),(0,16,95),(1,16,95),(0,0,0),(3,59,76),(2,21,94),(0,0,0),(0,0,0),(2,8,96),(2,16,95),(0,37,89),(0,0,0),(3,7,96),(0,58,77),(0,0,0),(0,0,0),(4,4,96),(0,9,96),(0,63,73),(0,0,0),(4,20,94),(2,58,77),(0,0,0),(0,0,0),(3,21,94),(0,29,92),(1,29,92),(0,0,0),(3,16,95),(4,43,86),(0,0,0),(0,0,0),(4,28,92),(2,29,92),(0,17,95),(0,0,0),(0,10,96),(1,10,96),(0,0,0),(0,0,0),(0,22,94),(1,22,94),(2,17,95),(0,0,0),(2,10,96),(0,26,93),(0,0,0),(0,0,0),(2,22,94),(4,7,96),(4,55,79),(0,0,0),(0,44,86),(0,42,87),(0,0,0),(0,0,0),(7,23,92),(0,11,96),(1,11,96),(0,0,0),(2,44,86),(0,46,85),(0,0,0),(0,0,0),(0,40,88),(1,40,88),(0,61,75),(0,0,0),(7,13,94),(0,18,95),(0,0,0),(0,0,0),(2,40,88),(6,64,71),(2,61,75),(0,0,0),(6,26,92),(2,18,95),(0,0,0),(0,0,0),(0,12,96),(1,12,96),(4,63,73),(0,0,0),(0,30,92),(0,23,94),(0,0,0),(0,0,0),(2,12,96),(4,29,92),(0,33,91),(0,0,0),(2,30,92),(2,23,94),(0,0,0),(0,0,0),(0,60,76),(0,56,79),(0,27,93),(0,0,0),(4,10,96),(5,34,90),(0,0,0),(0,0,0),(2,60,76),(0,13,96),(0,19,95),(0,0,0),(6,46,84),(0,50,83),(0,0,0),(0,0,0),(3,23,94),(2,13,96),(2,19,95),(0,0,0),(0,36,90),(0,66,71),(0,0,0),(0,0,0),(11,62,65),(4,11,96),(5,21,94),(0,0,0),(2,36,90),(2,66,71),(0,0,0),(0,0,0),(4,40,88),(0,0,97),(0,1,97),(0,0,0),(0,14,96),(0,2,97),(0,0,0),(0,0,0),(3,50,83),(2,0,97),(0,3,97),(0,0,0),(2,14,96),(0,45,86),(0,0,0),(0,0,0),(3,66,71),(0,4,97),(1,4,97),(0,0,0),(0,52,82),(1,52,82),(0,0,0),(0,0,0),(6,0,96),(0,28,93),(0,5,97),(0,0,0),(2,52,82),(0,34,91),(0,0,0),(0,0,0),(3,2,97),(0,15,96),(0,39,89),(0,0,0),(20,0,38),(0,6,97),(0,0,0),(0,0,0),(0,58,78),(1,58,78),(2,39,89),(0,0,0),(3,4,97),(2,6,97),(0,0,0),(0,0,0),(2,58,78),(0,49,84),(0,7,97),(0,0,0),(3,28,93),(0,25,94),(0,0,0),(0,0,0),(3,34,91),(2,49,84),(0,21,95),(0,0,0),(3,15,96),(0,37,90),(0,0,0),(0,0,0),(0,16,96),(0,8,97),(1,8,97),(0,0,0),(4,14,96),(0,54,81),(0,0,0),(0,0,0),(2,16,96),(2,8,97),(4,3,97),(0,0,0),(3,49,84),(2,54,81),(0,0,0),(0,0,0),(0,32,92),(1,32,92),(0,9,97),(0,0,0),(4,52,82),(3,21,95),(0,0,0),(0,0,0),(2,32,92),(0,61,76),(1,61,76),(0,0,0),(3,8,97),(4,34,91),(0,0,0),(0,0,0),(3,54,81),(0,17,96),(0,35,91),(0,0,0),(0,42,88),(0,10,97),(0,0,0),(0,0,0),(0,26,94),(1,26,94),(2,35,91),(0,0,0),(2,42,88),(2,10,97),(0,0,0),(0,0,0),(2,26,94),(0,40,89),(0,69,69),(0,0,0),(0,68,70),(1,68,70),(0,0,0),(0,0,0),(10,8,92),(0,48,85),(0,11,97),(0,0,0),(2,68,70),(0,53,82),(0,0,0),(0,0,0),(0,56,80),(1,56,80),(2,11,97),(0,0,0),(0,18,96),(1,18,96),(0,0,0),(0,0,0),(0,38,90),(1,38,90),(5,45,86),(0,0,0),(2,18,96),(0,30,93),(0,0,0),(0,0,0),(2,38,90),(0,12,97),(0,23,95),(0,0,0),(0,50,84),(1,50,84),(0,0,0),(0,0,0),(3,53,82),(2,12,97),(2,23,95),(0,0,0),(2,50,84),(0,27,94),(0,0,0),(0,0,0),(7,3,96),(4,17,96),(4,35,91),(0,0,0),(0,64,74),(1,64,74),(0,0,0),(0,0,0),(3,30,93),(0,19,96),(0,13,97),(0,0,0),(2,64,74),(3,23,95),(0,0,0),(0,0,0),(7,5,96),(2,19,96),(0,55,81),(0,0,0),(4,68,70),(8,34,89),(0,0,0),(0,0,0),(3,27,94),(0,43,88),(0,45,87),(0,0,0),(15,50,61),(4,53,82),(0,0,0),(0,0,0),(4,56,80),(0,24,95),(0,41,89),(0,0,0),(0,0,98),(0,1,98),(0,0,0),(0,0,0),(0,2,98),(1,2,98),(0,31,93),(0,0,0),(2,0,98),(0,3,98),(0,0,0),(0,0,0),(0,20,96),(1,20,96),(2,31,93),(0,0,0),(0,4,98),(0,39,90),(0,0,0),(0,0,0),(2,20,96),(6,0,97),(0,49,85),(0,0,0),(2,4,98),(0,5,98),(0,0,0),(0,0,0),(3,1,98),(5,42,88),(0,15,97),(0,0,0),(4,64,74),(2,5,98),(0,0,0),(0,0,0),(0,6,98),(1,6,98),(2,15,97),(0,0,0),(6,52,82),(8,22,93),(0,0,0),(0,0,0),(2,6,98),(0,57,80),(0,25,95),(0,0,0),(8,26,92),(0,7,98),(0,0,0),(0,0,0),(3,5,98),(0,21,96),(1,21,96),(0,0,0),(10,14,92),(0,69,70),(0,0,0),(0,0,0),(6,58,78),(0,16,97),(1,16,97),(0,0,0),(0,8,98),(1,8,98),(0,0,0),(0,0,0),(4,2,98),(0,32,93),(1,32,93),(0,0,0),(2,8,98),(0,29,94),(0,0,0),(0,0,0),(0,44,88),(1,44,88),(6,21,95),(0,0,0),(0,60,78),(0,9,98),(0,0,0),(0,0,0),(2,44,88),(0,35,92),(1,35,92),(0,0,0),(2,60,78),(2,9,98),(0,0,0),(0,0,0),(19,34,41),(0,56,81),(0,17,97),(0,0,0),(0,22,96),(0,26,95),(0,0,0),(0,0,0),(0,10,98),(1,10,98),(2,17,97),(0,0,0),(2,22,96),(2,26,95),(0,0,0),(0,0,0),(2,10,98),(4,57,80),(4,25,95),(0,0,0),(3,35,92),(4,7,98),(0,0,0),(0,0,0),(7,56,79),(0,64,75),(0,59,79),(0,0,0),(3,56,81),(0,11,98),(0,0,0),(0,0,0),(3,26,95),(2,64,75),(2,59,79),(0,0,0),(4,8,98),(0,18,97),(0,0,0),(0,0,0),(0,30,94),(1,30,94),(0,33,93),(0,0,0),(6,68,70),(2,18,97),(0,0,0),(0,0,0),(2,30,94),(0,23,96),(1,23,96),(0,0,0),(0,12,98),(0,55,82),(0,0,0),(0,0,0),(3,11,98),(2,23,96),(0,27,95),(0,0,0),(2,12,98),(2,55,82),(0,0,0),(0,0,0),(0,36,92),(1,36,92),(2,27,95),(0,0,0),(0,58,80),(1,58,80),(0,0,0),(0,0,0),(2,36,92),(0,45,88),(0,19,97),(0,0,0),(2,58,80),(0,13,98),(0,0,0),(0,0,0),(3,55,82),(2,45,88),(0,47,87),(0,0,0),(7,34,91),(0,41,90),(0,0,0),(0,0,0),(7,15,96),(4,64,75),(2,47,87),(0,0,0),(6,64,74),(2,41,90),(0,0,0),(0,0,0),(0,24,96),(1,24,96),(6,13,97),(0,0,0),(3,45,88),(0,31,94),(0,0,0),(0,0,0),(0,14,98),(0,0,99),(0,1,99),(0,0,0),(7,25,94),(0,2,99),(0,0,0),(0,0,0),(0,68,72),(0,20,97),(0,3,99),(0,0,0),(4,12,98),(2,2,99),(0,0,0),(0,0,0),(2,68,72),(0,4,99),(0,67,73),(0,0,0),(6,0,98),(6,1,98),(0,0,0),(0,0,0),(3,31,94),(2,4,99),(0,5,99),(0,0,0),(3,0,99),(0,15,98),(0,0,0),(0,0,0),(0,66,74),(0,37,92),(1,37,92),(0,0,0),(3,20,97),(0,6,99),(0,0,0),(0,0,0),(2,66,74),(0,25,96),(1,25,96),(0,0,0),(3,4,99),(2,6,99),(0,0,0),(0,0,0),(7,17,96),(2,25,96),(0,7,99),(0,0,0),(7,10,97),(3,5,99),(0,0,0),(0,0,0),(3,15,98),(0,44,89),(1,44,89),(0,0,0),(0,16,98),(1,16,98),(0,0,0),(0,0,0),(0,42,90),(0,8,99),(0,29,95),(0,0,0),(2,16,98),(4,2,99),(0,0,0),(0,0,0),(0,64,76),(0,48,87),(0,35,93),(0,0,0),(7,53,82),(3,7,99),(0,0,0),(0,0,0),(2,64,76),(0,40,91),(0,9,99),(0,0,0),(3,44,89),(5,36,92),(0,0,0),(0,0,0),(8,60,76),(2,40,91),(2,9,99),(0,0,0),(0,26,96),(0,17,98),(0,0,0),(0,0,0),(0,50,86),(1,50,86),(0,63,77),(0,0,0),(2,26,96),(0,10,99),(0,0,0),(0,0,0),(2,50,86),(4,25,96),(2,63,77),(0,0,0),(0,38,92),(1,38,92),(0,0,0),(0,0,0),(10,56,76),(6,56,81),(0,55,83),(0,0,0),(2,38,92),(5,24,96),(0,0,0),(0,0,0),(3,17,98),(4,44,89),(0,11,99),(0,0,0),(4,16,98),(0,30,95),(0,0,0),(0,0,0),(0,18,98),(0,52,85),(1,52,85),(0,0,0),(18,2,64),(2,30,95),(0,0,0),(0,0,0),(2,18,98),(2,52,85),(0,23,97),(0,0,0),(8,52,82),(0,70,71),(0,0,0),(0,0,0),(7,24,95),(0,12,99),(0,45,89),(0,0,0),(7,1,98),(0,43,90),(0,0,0),(0,0,0),(3,30,95),(0,47,88),(1,47,88),(0,0,0),(3,52,85),(2,43,90),(0,0,0),(0,0,0),(4,50,86),(2,47,88),(0,41,91),(0,0,0),(6,12,98),(0,19,98),(0,0,0),(0,0,0),(3,70,71),(7,49,85),(0,13,99),(0,0,0),(0,54,84),(0,57,82),(0,0,0),(0,0,0),(3,43,90),(7,15,97),(2,13,99),(0,0,0),(2,54,84),(0,66,75),(0,0,0),(0,0,0),(8,16,96),(0,24,97),(0,31,95),(0,0,0),(15,23,78),(2,66,75),(0,0,0),(0,0,0),(0,34,94),(1,34,94),(2,31,95),(0,0,0),(7,7,98),(0,14,99),(0,0,0),(0,0,0)]

def wits_10 : List (ℕ × ℕ × ℕ) := [(0,0,100),(0,1,100),(1,1,100),(0,0,0),(0,2,100),(1,2,100),(0,0,0),(0,0,0),(2,0,100),(0,3,100),(1,3,100),(0,0,0),(2,2,100),(3,31,95),(0,0,0),(0,0,0),(0,4,100),(1,4,100),(0,37,93),(0,0,0),(7,29,94),(5,50,86),(0,0,0),(0,0,0),(2,4,100),(0,5,100),(0,15,99),(0,0,0),(3,1,100),(4,19,98),(0,0,0),(0,0,0),(7,35,92),(2,5,100),(0,25,97),(0,0,0),(0,6,100),(0,46,89),(0,0,0),(0,0,0),(7,56,81),(7,17,97),(0,59,81),(0,0,0),(2,6,100),(0,21,98),(0,0,0),(0,0,0),(0,48,88),(0,7,100),(1,7,100),(0,0,0),(3,5,100),(0,63,78),(0,0,0),(0,0,0),(2,48,88),(0,16,99),(1,16,99),(0,0,0),(0,0,0),(0,35,94),(0,0,0),(0,0,0),(0,8,100),(1,8,100),(5,70,71),(0,0,0),(4,2,100),(0,50,87),(0,0,0),(0,0,0),(2,8,100),(4,3,100),(5,43,90),(0,0,0),(3,7,100),(2,50,87),(0,0,0),(0,0,0),(3,63,78),(0,9,100),(0,71,71),(0,0,0),(0,70,72),(0,26,97),(0,0,0),(0,0,0),(0,22,98),(1,22,98),(0,17,99),(0,0,0),(2,70,72),(0,38,93),(0,0,0),(0,0,0),(2,22,98),(5,54,84),(2,17,99),(0,0,0),(0,10,100),(1,10,100),(0,0,0),(0,0,0),(10,52,80),(8,43,88),(4,59,81),(0,0,0),(2,10,100),(3,71,71),(0,0,0),(0,0,0),(3,26,97),(4,7,100),(0,33,95),(0,0,0),(0,30,96),(1,30,96),(0,0,0),(0,0,0),(3,38,93),(0,11,100),(1,11,100),(0,0,0),(2,30,96),(0,18,99),(0,0,0),(0,0,0),(4,8,100),(2,11,100),(0,43,91),(0,0,0),(0,36,94),(0,23,98),(0,0,0),(0,0,0),(15,19,80),(10,64,71),(0,27,97),(0,0,0),(2,36,94),(0,54,85),(0,0,0),(0,0,0),(0,12,100),(0,41,92),(1,41,92),(0,0,0),(3,11,100),(2,54,85),(0,0,0),(0,0,0),(2,12,100),(2,41,92),(0,65,77),(0,0,0),(11,19,92),(3,43,91),(0,0,0),(0,0,0),(3,23,98),(0,60,81),(0,19,99),(0,0,0),(4,10,100),(3,27,97),(0,0,0),(0,0,0),(3,54,85),(0,13,100),(0,39,93),(0,0,0),(3,41,92),(5,48,88),(0,0,0),(0,0,0),(7,37,92),(0,31,96),(1,31,96),(0,0,0),(0,24,98),(0,34,95),(0,0,0),(0,0,0),(7,25,96),(2,31,96),(5,35,94),(0,0,0),(2,24,98),(2,34,95),(0,0,0),(0,0,0),(0,56,84),(0,28,97),(1,28,97),(0,0,0),(0,14,100),(1,14,100),(0,0,0),(0,0,0),(2,56,84),(0,0,101),(0,1,101),(0,0,0),(2,14,100),(0,2,101),(0,0,0),(0,0,0),(3,34,95),(2,0,101),(0,3,101),(0,0,0),(8,22,96),(2,2,101),(0,0,0),(0,0,0),(0,46,90),(0,4,101),(1,4,101),(0,0,0),(3,28,97),(10,14,95),(0,0,0),(0,0,0),(2,46,90),(0,15,100),(0,5,101),(0,0,0),(0,42,92),(0,25,98),(0,0,0),(0,0,0),(3,2,101),(2,15,100),(2,5,101),(0,0,0),(2,42,92),(0,6,101),(0,0,0),(0,0,0),(0,32,96),(1,32,96),(0,21,99),(0,0,0),(0,50,88),(1,50,88),(0,0,0),(0,0,0),(2,32,96),(0,40,93),(0,7,101),(0,0,0),(2,50,88),(0,58,83),(0,0,0),(0,0,0),(0,16,100),(1,16,100),(2,7,101),(0,0,0),(4,14,100),(2,58,83),(0,0,0),(0,0,0),(2,16,100),(0,8,101),(1,8,101),(0,0,0),(7,30,95),(3,21,99),(0,0,0),(0,0,0),(7,52,85),(0,52,87),(1,52,87),(0,0,0),(3,40,93),(3,7,101),(0,0,0),(0,0,0),(0,26,98),(1,26,98),(0,9,101),(0,0,0),(7,70,71),(0,22,99),(0,0,0),(0,0,0),(2,26,98),(0,17,100),(1,17,100),(0,0,0),(3,8,101),(2,22,99),(0,0,0),(0,0,0),(7,47,88),(2,17,100),(6,71,71),(0,0,0),(3,52,87),(0,10,101),(0,0,0),(0,0,0),(4,32,96),(0,33,96),(0,45,91),(0,0,0),(4,50,88),(0,30,97),(0,0,0),(0,0,0),(0,54,86),(0,43,92),(1,43,92),(0,0,0),(3,17,100),(2,30,97),(0,0,0),(0,0,0),(2,54,86),(0,36,95),(0,11,101),(0,0,0),(0,18,100),(1,18,100),(0,0,0),(0,0,0),(3,10,101),(2,36,95),(0,23,99),(0,0,0),(2,18,100),(0,27,98),(0,0,0),(0,0,0),(3,30,97),(0,64,79),(1,64,79),(0,0,0),(3,43,92),(2,27,98),(0,0,0),(0,0,0),(4,26,98),(0,12,101),(1,12,101),(0,0,0),(3,36,95),(3,11,101),(0,0,0),(0,0,0),(7,3,100),(2,12,101),(5,25,98),(0,0,0),(11,0,95),(0,39,94),(0,0,0),(0,0,0),(3,27,98),(0,19,100),(1,19,100),(0,0,0),(3,64,79),(2,39,94),(0,0,0),(0,0,0),(0,72,72),(0,63,80),(0,13,101),(0,0,0),(0,34,96),(1,34,96),(0,0,0),(0,0,0),(0,70,74),(0,24,99),(0,53,87),(0,0,0),(2,34,96),(5,16,100),(0,0,0),(0,0,0),(2,70,74),(2,24,99),(0,69,75),(0,0,0),(0,28,98),(1,28,98),(0,0,0),(0,0,0),(7,7,100),(6,31,96),(0,37,95),(0,0,0),(2,28,98),(0,14,101),(0,0,0),(0,0,0),(0,20,100),(1,20,100),(2,37,95),(0,0,0),(0,0,102),(0,1,102),(0,0,0),(0,0,0),(0,2,102),(1,2,102),(5,22,99),(0,0,0),(2,0,102),(0,3,102),(0,0,0),(0,0,0),(2,2,102),(6,0,101),(0,67,77),(0,0,0),(0,4,102),(0,50,89),(0,0,0),(0,0,0),(3,14,101),(4,19,100),(0,15,101),(0,0,0),(2,4,102),(0,5,102),(0,0,0),(0,0,0),(3,1,102),(0,32,97),(1,32,97),(0,0,0),(0,40,94),(1,40,94),(0,0,0),(0,0,0),(0,6,102),(0,21,100),(1,21,100),(0,0,0),(2,40,94),(0,29,98),(0,0,0),(0,0,0),(0,52,88),(1,52,88),(4,69,75),(0,0,0),(4,28,98),(0,7,102),(0,0,0),(0,0,0),(2,52,88),(0,16,101),(1,16,101),(0,0,0),(3,32,97),(2,7,102),(0,0,0),(0,0,0),(4,20,100),(2,16,101),(0,65,79),(0,0,0),(0,8,102),(0,38,95),(0,0,0),(0,0,0),(3,29,98),(7,43,91),(0,57,85),(0,0,0),(2,8,102),(0,26,99),(0,0,0),(0,0,0),(3,7,102),(6,8,101),(2,57,85),(0,0,0),(0,22,100),(0,9,102),(0,0,0),(0,0,0),(7,41,92),(0,45,92),(0,17,101),(0,0,0),(2,22,100),(2,9,102),(0,0,0),(0,0,0),(0,64,80),(1,64,80),(0,33,97),(0,0,0),(4,40,94),(0,49,90),(0,0,0),(0,0,0),(0,10,102),(1,10,102),(2,33,97),(0,0,0),(10,42,88),(2,49,90),(0,0,0),(0,0,0),(0,36,96),(0,72,73),(1,72,73),(0,0,0),(3,45,92),(0,41,94),(0,0,0),(0,0,0),(2,36,96),(2,72,73),(0,51,89),(0,0,0),(7,34,95),(0,11,102),(0,0,0),(0,0,0),(3,49,90),(0,23,100),(0,27,99),(0,0,0),(0,56,86),(1,56,86),(0,0,0),(0,0,0),(7,28,97),(0,59,84),(1,59,84),(0,0,0),(2,56,86),(4,26,99),(0,0,0),(0,0,0),(3,41,94),(2,59,84),(0,39,95),(0,0,0),(0,12,102),(1,12,102),(0,0,0),(0,0,0),(3,11,102),(0,53,88),(1,53,88),(0,0,0),(2,12,102),(3,27,99),(0,0,0),(0,0,0),(4,64,80),(2,53,88),(0,19,101),(0,0,0),(3,59,84),(0,31,98),(0,0,0),(0,0,0),(0,62,82),(1,62,82),(2,19,101),(0,0,0),(7,25,98),(0,13,102),(0,0,0),(0,0,0),(0,24,100),(1,24,100),(5,7,102),(0,0,0),(0,46,92),(1,46,92),(0,0,0),(0,0,0),(2,24,100),(0,28,99),(1,28,99),(0,0,0),(2,46,92),(0,58,85),(0,0,0),(0,0,0),(3,31,98),(2,28,99),(0,55,87),(0,0,0),(4,56,86),(0,66,79),(0,0,0),(0,0,0),(0,14,102),(0,20,101),(1,20,101),(0,0,0),(6,28,98),(2,66,79),(0,0,0),(0,0,0),(2,14,102),(0,0,103),(0,1,103),(0,0,0),(3,28,99),(0,2,103),(0,0,0),(0,0,0),(3,58,85),(2,0,103),(0,3,103),(0,0,0),(6,0,102),(2,2,103),(0,0,0),(0,0,0),(3,66,79),(0,4,103),(1,4,103),(0,0,0),(0,32,98),(0,15,102),(0,0,0),(0,0,0),(4,62,82),(2,4,103),(0,5,103),(0,0,0),(2,32,98),(2,15,102),(0,0,0),(0,0,0),(3,2,103),(14,29,84),(0,21,101),(0,0,0),(4,46,92),(0,6,103),(0,0,0),(0,0,0),(7,33,96),(4,28,99),(2,21,101),(0,0,0),(3,4,103),(2,6,103),(0,0,0),(0,0,0),(0,60,84),(0,64,81),(0,7,103),(0,0,0),(0,16,102),(1,16,102),(0,0,0),(0,0,0),(2,60,84),(2,64,81),(0,71,75),(0,0,0),(2,16,102),(3,21,101),(0,0,0),(0,0,0),(3,6,103),(0,8,103),(0,45,93),(0,0,0),(0,26,100),(1,26,100),(0,0,0),(0,0,0),(7,64,79),(2,8,103),(0,49,91),(0,0,0),(2,26,100),(0,22,101),(0,0,0),(0,0,0),(7,12,101),(4,4,103),(0,9,103),(0,0,0),(4,32,98),(0,17,102),(0,0,0),(0,0,0),(11,23,94),(10,56,81),(2,9,103),(0,0,0),(3,8,103),(0,30,99),(0,0,0),(0,0,0),(7,19,100),(0,36,97),(0,41,95),(0,0,0),(0,68,78),(0,10,103),(0,0,0),(0,0,0),(3,22,101),(2,36,97),(2,41,95),(0,0,0),(2,68,78),(2,10,103),(0,0,0),(0,0,0),(3,17,102),(4,64,81),(4,7,103),(0,0,0),(4,16,102),(5,14,102),(0,0,0),(0,0,0),(0,18,102),(0,27,100),(0,11,103),(0,0,0),(3,36,97),(0,62,83),(0,0,0),(0,0,0),(2,18,102),(0,39,96),(1,39,96),(0,0,0),(4,26,100),(2,62,83),(0,0,0),(0,0,0),(11,2,97),(2,39,96),(4,49,91),(0,0,0),(6,56,86),(4,22,101),(0,0,0),(0,0,0),(8,32,96),(0,12,103),(1,12,103),(0,0,0),(0,66,80),(1,66,80),(0,0,0),(0,0,0),(0,34,98),(1,34,98),(0,31,99),(0,0,0),(2,66,80),(0,19,102),(0,0,0),(0,0,0),(0,48,92),(0,55,88),(1,55,88),(0,0,0),(0,44,94),(1,44,94),(0,0,0),(0,0,0),(2,48,92),(0,24,101),(0,13,103),(0,0,0),(2,44,94),(0,50,91),(0,0,0),(0,0,0),(0,28,100),(1,28,100),(0,65,81),(0,0,0),(7,29,98),(0,42,95),(0,0,0),(0,0,0),(2,28,100),(4,27,100),(2,65,81),(0,0,0),(3,55,88),(2,42,95),(0,0,0),(0,0,0),(7,16,101),(4,39,96),(10,1,99),(0,0,0),(0,20,102),(0,14,103),(0,0,0),(0,0,0),(3,50,91),(0,72,75),(1,72,75),(0,0,0),(2,20,102),(2,14,103),(0,0,0),(0,0,0),(0,0,104),(0,1,104),(0,57,87),(0,0,0),(0,2,104),(1,2,104),(0,0,0),(0,0,0),(2,0,104),(0,3,104),(0,25,101),(0,0,0),(2,2,104),(0,35,98),(0,0,0),(0,0,0),(0,4,104),(1,4,104),(0,15,103),(0,0,0),(3,72,75),(0,54,89),(0,0,0),(0,0,0),(2,4,104),(0,5,104),(1,5,104),(0,0,0),(3,1,104),(0,21,102),(0,0,0),(0,0,0),(4,28,100),(2,5,104),(4,65,81),(0,0,0),(0,6,104),(0,38,97),(0,0,0),(0,0,0),(3,35,98),(8,12,101),(0,47,93),(0,0,0),(2,6,104),(0,45,94),(0,0,0),(0,0,0),(3,54,89),(0,7,104),(1,7,104),(0,0,0),(3,5,104),(2,45,94),(0,0,0),(0,0,0),(3,21,102),(2,7,104),(0,43,95),(0,0,0),(6,16,102),(0,26,101),(0,0,0),(0,0,0),(0,8,104),(1,8,104),(0,51,91),(0,0,0),(4,2,104),(2,26,101),(0,0,0),(0,0,0),(0,22,102),(0,67,80),(0,33,99),(0,0,0),(3,7,104),(4,35,98),(0,0,0),(0,0,0),(2,22,102),(0,9,104),(0,17,103),(0,0,0),(0,30,100),(1,30,100),(0,0,0),(0,0,0),(3,26,101),(2,9,104),(2,17,103),(0,0,0),(2,30,100),(0,53,90),(0,0,0),(0,0,0),(8,20,100),(15,47,73),(5,42,95),(0,0,0),(0,10,104),(0,66,81),(0,0,0),(0,0,0),(8,2,102),(6,36,97),(4,47,93),(0,0,0),(2,10,104),(2,66,81),(0,0,0),(0,0,0),(7,28,99),(4,7,104),(0,27,101),(0,0,0),(7,58,85),(0,18,103),(0,0,0),(0,0,0),(3,53,90),(0,11,104),(1,11,104),(0,0,0),(7,66,79),(2,18,103),(0,0,0),(0,0,0),(3,66,81),(2,11,104),(0,55,89),(0,0,0),(8,40,94),(0,65,82),(0,0,0),(0,0,0),(0,46,94),(0,48,93),(0,73,75),(0,0,0),(7,2,103),(0,34,99),(0,0,0),(0,0,0),(0,12,104),(0,31,100),(1,31,100),(0,0,0),(0,50,92),(1,50,92),(0,0,0),(0,0,0),(2,12,104),(2,31,100),(0,19,103),(0,0,0),(2,50,92),(0,37,98),(0,0,0),(0,0,0),(3,65,82),(5,6,104),(2,19,103),(0,0,0),(0,24,102),(1,24,102),(0,0,0),(0,0,0),(0,70,78),(0,13,104),(1,13,104),(0,0,0),(2,24,102),(8,26,99),(0,0,0),(0,0,0),(2,70,78),(0,57,88),(1,57,88),(0,0,0),(0,60,86),(1,60,86),(0,0,0),(0,0,0)]

def wits_11 : List (ℕ × ℕ × ℕ) := [(3,37,98),(2,57,88),(0,69,79),(0,0,0),(2,60,86),(5,8,104),(0,0,0),(0,0,0),(8,64,80),(0,20,103),(1,20,103),(0,0,0),(0,14,104),(1,14,104),(0,0,0),(0,0,0),(0,54,90),(1,54,90),(4,73,75),(0,0,0),(2,14,104),(4,34,99),(0,0,0),(0,0,0),(0,32,100),(0,0,105),(0,1,105),(0,0,0),(4,50,92),(0,2,105),(0,0,0),(0,0,0),(2,32,100),(2,0,105),(0,3,105),(0,0,0),(3,20,103),(2,2,105),(0,0,0),(0,0,0),(14,14,90),(0,4,105),(0,29,101),(0,0,0),(4,24,102),(0,47,94),(0,0,0),(0,0,0),(0,38,98),(1,38,98),(0,5,105),(0,0,0),(3,0,105),(2,47,94),(0,0,0),(0,0,0),(2,38,98),(0,56,89),(1,56,89),(0,0,0),(4,60,86),(0,6,105),(0,0,0),(0,0,0),(10,8,100),(0,43,96),(1,43,96),(0,0,0),(3,4,105),(0,62,85),(0,0,0),(0,0,0),(0,16,104),(1,16,104),(0,7,105),(0,0,0),(4,14,104),(2,62,85),(0,0,0),(0,0,0),(0,26,102),(1,26,102),(2,7,105),(0,0,0),(3,56,89),(5,12,104),(0,0,0),(0,0,0),(2,26,102),(0,8,105),(0,41,97),(0,0,0),(3,43,96),(0,22,103),(0,0,0),(0,0,0),(3,62,85),(0,36,99),(1,36,99),(0,0,0),(10,10,100),(0,30,101),(0,0,0),(0,0,0),(6,22,102),(0,17,104),(0,9,105),(0,0,0),(0,58,88),(1,58,88),(0,0,0),(0,0,0),(4,38,98),(0,72,77),(0,65,83),(0,0,0),(2,58,88),(0,61,86),(0,0,0),(0,0,0),(3,22,103),(2,72,77),(2,65,83),(0,0,0),(3,36,99),(0,10,105),(0,0,0),(0,0,0),(3,30,101),(4,43,96),(8,3,103),(0,0,0),(3,17,104),(0,27,102),(0,0,0),(0,0,0),(4,16,104),(5,14,104),(0,23,103),(0,0,0),(0,18,104),(0,46,95),(0,0,0),(0,0,0),(3,61,86),(10,41,92),(0,11,105),(0,0,0),(2,18,104),(0,50,93),(0,0,0),(0,0,0),(0,44,96),(1,44,96),(2,11,105),(0,0,0),(0,34,100),(1,34,100),(0,0,0),(0,0,0),(2,44,96),(0,69,80),(0,31,101),(0,0,0),(2,34,100),(3,23,103),(0,0,0),(0,0,0),(0,52,92),(0,12,105),(0,37,99),(0,0,0),(4,58,88),(0,42,97),(0,0,0),(0,0,0),(2,52,92),(0,19,104),(1,19,104),(0,0,0),(6,50,92),(2,42,97),(0,0,0),(0,0,0),(7,5,104),(0,24,103),(1,24,103),(0,0,0),(0,28,102),(1,28,102),(0,0,0),(0,0,0),(10,56,84),(2,24,103),(0,13,105),(0,0,0),(2,28,102),(0,54,91),(0,0,0),(0,0,0),(3,42,97),(6,13,104),(2,13,105),(0,0,0),(0,40,98),(1,40,98),(0,0,0),(0,0,0),(7,7,104),(6,57,88),(4,11,105),(0,0,0),(2,40,98),(0,67,82),(0,0,0),(0,0,0),(0,20,104),(1,20,104),(5,22,103),(0,0,0),(4,34,100),(0,14,105),(0,0,0),(0,0,0),(2,20,104),(0,32,101),(1,32,101),(0,0,0),(6,14,104),(2,14,105),(0,0,0),(0,0,0),(4,52,92),(2,32,101),(0,25,103),(0,0,0),(0,0,106),(0,1,106),(0,0,0),(0,0,0),(0,2,106),(0,45,96),(1,45,96),(0,0,0),(2,0,106),(0,3,106),(0,0,0),(0,0,0),(2,2,106),(2,45,96),(0,15,105),(0,0,0),(0,4,106),(1,4,106),(0,0,0),(0,0,0),(10,16,100),(0,21,104),(0,43,97),(0,0,0),(2,4,106),(0,5,106),(0,0,0),(0,0,0),(3,1,106),(2,21,104),(2,43,97),(0,0,0),(0,72,78),(1,72,78),(0,0,0),(0,0,0),(0,6,106),(0,53,92),(1,53,92),(0,0,0),(2,72,78),(3,15,105),(0,0,0),(0,0,0),(2,6,106),(0,16,105),(0,71,79),(0,0,0),(3,21,104),(0,7,106),(0,0,0),(0,0,0),(3,5,106),(2,16,105),(0,33,101),(0,0,0),(7,65,82),(2,7,106),(0,0,0),(0,0,0),(0,36,100),(1,36,100),(2,33,101),(0,0,0),(0,8,106),(1,8,106),(0,0,0),(0,0,0),(0,30,102),(1,30,102),(0,55,91),(0,0,0),(2,8,106),(3,71,79),(0,0,0),(0,0,0),(2,30,102),(5,28,102),(0,17,105),(0,0,0),(4,4,106),(0,9,106),(0,0,0),(0,0,0),(0,0,0),(0,64,85),(0,39,99),(0,0,0),(6,58,88),(2,9,106),(0,0,0),(0,0,0),(7,13,104),(0,48,95),(1,48,95),(0,0,0),(0,46,96),(1,46,96),(0,0,0),(0,0,0),(0,10,106),(1,10,106),(0,27,103),(0,0,0),(2,46,96),(3,17,105),(0,0,0),(0,0,0),(0,60,88),(0,23,104),(1,23,104),(0,0,0),(0,68,82),(0,18,105),(0,0,0),(0,0,0),(2,60,88),(0,52,93),(1,52,93),(0,0,0),(2,68,82),(0,11,106),(0,0,0),(0,0,0),(4,36,100),(2,52,93),(5,1,106),(0,0,0),(4,8,106),(0,31,102),(0,0,0),(0,0,0),(0,42,98),(0,37,100),(1,37,100),(0,0,0),(3,23,104),(2,31,102),(0,0,0),(0,0,0),(2,42,98),(2,37,100),(0,67,83),(0,0,0),(0,12,106),(1,12,106),(0,0,0),(0,0,0),(3,11,106),(4,64,85),(0,19,105),(0,0,0),(2,12,106),(6,42,97),(0,0,0),(0,0,0),(0,24,104),(0,28,103),(1,28,103),(0,0,0),(3,37,100),(5,6,106),(0,0,0),(0,0,0),(2,24,104),(0,40,99),(0,59,89),(0,0,0),(6,28,102),(0,13,106),(0,0,0),(0,0,0),(4,60,88),(2,40,99),(2,59,89),(0,0,0),(0,66,84),(0,62,87),(0,0,0),(0,0,0),(11,26,97),(0,56,91),(1,56,91),(0,0,0),(2,66,84),(2,62,87),(0,0,0),(0,0,0),(11,38,93),(0,20,105),(0,35,101),(0,0,0),(0,32,102),(1,32,102),(0,0,0),(0,0,0),(0,14,106),(1,14,106),(0,45,97),(0,0,0),(2,32,102),(0,51,94),(0,0,0),(0,0,0),(2,14,106),(0,25,104),(1,25,104),(0,0,0),(0,38,100),(1,38,100),(0,0,0),(0,0,0),(7,17,104),(0,0,107),(0,1,107),(0,0,0),(2,38,100),(0,2,107),(0,0,0),(0,0,0),(4,24,104),(2,0,107),(0,3,107),(0,0,0),(7,61,86),(0,15,106),(0,0,0),(0,0,0),(0,58,90),(0,4,107),(0,21,105),(0,0,0),(3,25,104),(2,15,106),(0,0,0),(0,0,0),(2,58,90),(2,4,107),(0,5,107),(0,0,0),(3,0,107),(3,1,107),(0,0,0),(0,0,0),(3,2,107),(4,56,91),(0,41,99),(0,0,0),(6,72,78),(0,6,107),(0,0,0),(0,0,0),(3,15,106),(0,55,92),(1,55,92),(0,0,0),(0,16,106),(0,33,102),(0,0,0),(0,0,0),(4,14,106),(0,36,101),(0,7,107),(0,0,0),(2,16,106),(2,33,102),(0,0,0),(0,0,0),(7,69,80),(2,36,101),(2,7,107),(0,0,0),(4,38,100),(0,22,105),(0,0,0),(0,0,0),(3,6,107),(0,8,107),(1,8,107),(0,0,0),(3,55,92),(2,22,105),(0,0,0),(0,0,0),(0,48,96),(0,39,100),(1,39,100),(0,0,0),(3,36,101),(0,17,106),(0,0,0),(0,0,0),(2,48,96),(2,39,100),(0,9,107),(0,0,0),(10,56,86),(2,17,106),(0,0,0),(0,0,0),(3,22,105),(5,66,84),(0,63,87),(0,0,0),(0,44,98),(1,44,98),(0,0,0),(0,0,0),(19,14,67),(0,27,104),(1,27,104),(0,0,0),(2,44,98),(0,10,107),(0,0,0),(0,0,0),(0,76,76),(1,76,76),(0,23,105),(0,0,0),(4,16,106),(2,10,107),(0,0,0),(0,0,0),(0,18,106),(1,18,106),(2,23,105),(0,0,0),(6,68,82),(0,42,99),(0,0,0),(0,0,0),(2,18,106),(5,38,100),(0,11,107),(0,0,0),(3,27,104),(2,42,99),(0,0,0),(0,0,0),(3,10,107),(4,8,107),(2,11,107),(0,0,0),(7,1,106),(0,59,90),(0,0,0),(0,0,0),(0,72,80),(1,72,80),(5,15,106),(0,0,0),(0,62,88),(1,62,88),(0,0,0),(0,0,0),(2,72,80),(0,12,107),(1,12,107),(0,0,0),(2,62,88),(0,19,106),(0,0,0),(0,0,0),(0,28,104),(0,24,105),(0,71,81),(0,0,0),(4,44,98),(2,19,106),(0,0,0),(0,0,0),(2,28,104),(2,24,105),(2,71,81),(0,0,0),(15,29,86),(4,10,107),(0,0,0),(0,0,0),(4,76,76),(0,49,96),(0,13,107),(0,0,0),(3,12,107),(0,65,86),(0,0,0),(0,0,0),(0,70,82),(1,70,82),(0,51,95),(0,0,0),(3,24,105),(0,35,102),(0,0,0),(0,0,0),(2,70,82),(0,32,103),(1,32,103),(0,0,0),(0,20,106),(1,20,106),(0,0,0),(0,0,0),(11,30,97),(2,32,103),(0,61,89),(0,0,0),(2,20,106),(0,14,107),(0,0,0),(0,0,0),(3,65,86),(7,55,91),(0,25,105),(0,0,0),(4,62,88),(2,14,107),(0,0,0),(0,0,0),(3,35,102),(0,29,104),(1,29,104),(0,0,0),(3,32,103),(4,19,106),(0,0,0),(0,0,0),(0,0,108),(0,1,108),(1,1,108),(0,0,0),(0,2,108),(1,2,108),(0,0,0),(0,0,0),(2,0,108),(0,3,108),(0,15,107),(0,0,0),(2,2,108),(0,21,106),(0,0,0),(0,0,0),(0,4,108),(0,41,100),(1,41,100),(0,0,0),(3,29,104),(2,21,106),(0,0,0),(0,0,0),(2,4,108),(0,5,108),(1,5,108),(0,0,0),(3,1,108),(4,35,102),(0,0,0),(0,0,0),(7,52,93),(2,5,108),(0,33,103),(0,0,0),(0,6,108),(0,26,105),(0,0,0),(0,0,0),(3,21,106),(0,16,107),(1,16,107),(0,0,0),(2,6,108),(0,75,78),(0,0,0),(0,0,0),(7,37,100),(0,7,108),(0,67,85),(0,0,0),(0,30,104),(0,74,79),(0,0,0),(0,0,0),(0,22,106),(1,22,106),(0,39,101),(0,0,0),(2,30,104),(2,74,79),(0,0,0),(0,0,0),(0,8,108),(0,52,95),(1,52,95),(0,0,0),(3,16,107),(8,14,105),(0,0,0),(0,0,0),(2,8,108),(0,44,99),(0,17,107),(0,0,0),(3,7,108),(3,67,85),(0,0,0),(0,0,0),(3,74,79),(0,9,108),(1,9,108),(0,0,0),(7,13,106),(3,39,101),(0,0,0),(0,0,0),(0,54,94),(1,54,94),(0,27,105),(0,0,0),(3,52,95),(8,3,106),(0,0,0),(0,0,0),(2,54,94),(5,20,106),(0,59,91),(0,0,0),(0,10,108),(0,23,106),(0,0,0),(0,0,0),(6,76,76),(4,16,107),(2,59,91),(0,0,0),(2,10,108),(0,18,107),(0,0,0),(0,0,0),(6,18,106),(0,31,104),(1,31,104),(0,0,0),(4,30,104),(2,18,107),(0,0,0),(0,0,0),(4,22,106),(0,11,108),(1,11,108),(0,0,0),(11,16,101),(0,70,83),(0,0,0),(0,0,0),(3,23,106),(2,11,108),(0,65,87),(0,0,0),(7,2,107),(2,70,83),(0,0,0),(0,0,0),(3,18,107),(0,40,101),(1,40,101),(0,0,0),(3,31,104),(5,4,108),(0,0,0),(0,0,0),(0,12,108),(0,28,105),(0,19,107),(0,0,0),(0,24,106),(0,47,98),(0,0,0),(0,0,0),(2,12,108),(0,51,96),(1,51,96),(0,0,0),(2,24,106),(0,61,90),(0,0,0),(0,0,0),(0,0,0),(2,51,96),(0,45,99),(0,0,0),(0,58,92),(1,58,92),(0,0,0),(0,0,0),(7,55,92),(0,13,108),(0,35,103),(0,0,0),(2,58,92),(3,19,107),(0,0,0),(0,0,0),(0,32,104),(1,32,104),(2,35,103),(0,0,0),(3,51,96),(5,22,106),(0,0,0),(0,0,0),(0,38,102),(0,20,107),(1,20,107),(0,0,0),(6,20,106),(3,45,99),(0,0,0),(0,0,0),(2,38,102),(2,20,107),(0,77,77),(0,0,0),(0,14,108),(0,25,106),(0,0,0),(0,0,0),(7,39,100),(4,40,101),(0,29,105),(0,0,0),(2,14,108),(2,25,106),(0,0,0),(0,0,0),(4,12,108),(4,28,105),(2,29,105),(0,0,0),(0,74,80),(1,74,80),(0,0,0),(0,0,0),(6,0,108),(0,0,109),(0,1,109),(0,0,0),(2,74,80),(0,2,109),(0,0,0),(0,0,0),(3,25,106),(0,15,108),(0,3,109),(0,0,0),(4,58,92),(2,2,109),(0,0,0),(0,0,0),(6,4,108),(0,4,109),(0,57,93),(0,0,0),(10,30,100),(13,10,98),(0,0,0),(0,0,0),(4,32,104),(0,33,104),(0,5,109),(0,0,0),(0,48,98),(0,50,97),(0,0,0),(0,0,0),(0,26,106),(1,26,106),(2,5,109),(0,0,0),(2,48,98),(0,6,109),(0,0,0),(0,0,0),(0,16,108),(1,16,108),(4,77,77),(0,0,0),(3,4,109),(0,30,105),(0,0,0),(0,0,0),(2,16,108),(6,7,108),(0,7,109),(0,0,0),(3,33,104),(0,22,107),(0,0,0),(0,0,0),(0,44,100),(1,44,100),(2,7,109),(0,0,0),(4,74,80),(0,54,95),(0,0,0),(0,0,0),(0,62,90),(0,8,109),(1,8,109),(0,0,0),(15,43,82),(2,54,95),(0,0,0),(0,0,0),(2,62,90),(0,17,108),(1,17,108),(0,0,0),(0,70,84),(1,70,84),(0,0,0),(0,0,0),(3,22,107),(2,17,108),(0,9,109),(0,0,0),(2,70,84),(0,27,106),(0,0,0),(0,0,0),(3,54,95),(0,65,88),(1,65,88),(0,0,0),(0,34,104),(1,34,104),(0,0,0),(0,0,0),(4,26,106),(2,65,88),(0,23,107),(0,0,0),(2,34,104),(0,10,109),(0,0,0),(0,0,0),(4,16,108),(5,14,108),(0,31,105),(0,0,0),(0,18,108),(1,18,108),(0,0,0),(0,0,0),(3,27,106),(6,31,104),(2,31,105),(0,0,0),(2,18,108),(4,22,107),(0,0,0),(0,0,0)]

def wits_12 : List (ℕ × ℕ × ℕ) := [(4,44,100),(5,74,80),(0,11,109),(0,0,0),(0,40,102),(0,49,98),(0,0,0),(0,0,0),(3,10,109),(4,8,109),(0,47,99),(0,0,0),(2,40,102),(0,58,93),(0,0,0),(0,0,0),(7,3,108),(0,64,89),(1,64,89),(0,0,0),(0,28,106),(1,28,106),(0,0,0),(0,0,0),(6,12,108),(0,12,109),(1,12,109),(0,0,0),(2,28,106),(3,11,109),(0,0,0),(0,0,0),(3,49,98),(2,12,109),(5,50,97),(0,0,0),(4,34,104),(0,74,81),(0,0,0),(0,0,0),(3,58,93),(0,35,104),(1,35,104),(0,0,0),(3,64,89),(2,74,81),(0,0,0),(0,0,0),(7,16,107),(0,32,105),(0,13,109),(0,0,0),(3,12,109),(0,38,103),(0,0,0),(0,0,0),(6,32,104),(2,32,105),(0,67,87),(0,0,0),(7,74,79),(2,38,103),(0,0,0),(0,0,0),(0,20,108),(1,20,108),(2,67,87),(0,0,0),(3,35,104),(0,63,90),(0,0,0),(0,0,0),(2,20,108),(0,72,83),(0,25,107),(0,0,0),(3,32,105),(0,14,109),(0,0,0),(0,0,0),(3,38,103),(2,72,83),(2,25,107),(0,0,0),(4,28,106),(0,41,102),(0,0,0),(0,0,0),(7,9,108),(4,12,109),(5,27,106),(0,0,0),(6,74,80),(2,41,102),(0,0,0),(0,0,0),(3,63,90),(0,71,84),(1,71,84),(0,0,0),(0,0,110),(0,1,110),(0,0,0),(0,0,0),(0,2,110),(0,21,108),(0,15,109),(0,0,0),(2,0,110),(0,3,110),(0,0,0),(0,0,0),(0,36,104),(0,52,97),(0,33,105),(0,0,0),(0,4,110),(1,4,110),(0,0,0),(0,0,0),(2,36,104),(2,52,97),(2,33,105),(0,0,0),(2,4,110),(0,5,110),(0,0,0),(0,0,0),(3,1,110),(5,40,102),(0,39,103),(0,0,0),(0,54,96),(1,54,96),(0,0,0),(0,0,0),(0,6,110),(0,16,109),(1,16,109),(0,0,0),(2,54,96),(3,33,105),(0,0,0),(0,0,0),(2,6,110),(2,16,109),(0,65,89),(0,0,0),(0,22,108),(0,7,110),(0,0,0),(0,0,0),(3,5,110),(7,19,107),(2,65,89),(0,0,0),(2,22,108),(0,69,86),(0,0,0),(0,0,0),(6,62,90),(0,56,95),(1,56,95),(0,0,0),(0,8,110),(1,8,110),(0,0,0),(0,0,0),(0,42,102),(1,42,102),(0,17,109),(0,0,0),(2,8,110),(3,65,89),(0,0,0),(0,0,0),(0,76,80),(1,76,80),(0,27,107),(0,0,0),(4,4,110),(0,9,110),(0,0,0),(0,0,0),(2,76,80),(0,37,104),(0,75,81),(0,0,0),(3,56,95),(2,9,110),(0,0,0),(0,0,0),(7,20,107),(0,23,108),(1,23,108),(0,0,0),(0,64,90),(0,31,106),(0,0,0),(0,0,0),(0,10,110),(1,10,110),(0,49,99),(0,0,0),(2,64,90),(0,18,109),(0,0,0),(0,0,0),(2,10,110),(0,40,103),(1,40,103),(0,0,0),(3,37,104),(2,18,109),(0,0,0),(0,0,0),(10,20,104),(2,40,103),(0,53,97),(0,0,0),(3,23,108),(0,11,110),(0,0,0),(0,0,0),(3,31,106),(4,56,95),(0,45,101),(0,0,0),(4,8,110),(2,11,110),(0,0,0),(0,0,0),(3,18,109),(0,28,107),(1,28,107),(0,0,0),(3,40,103),(5,36,104),(0,0,0),(0,0,0),(0,24,108),(0,55,96),(0,19,109),(0,0,0),(0,12,110),(1,12,110),(0,0,0),(0,0,0),(2,24,108),(0,60,93),(0,35,105),(0,0,0),(2,12,110),(0,43,102),(0,0,0),(0,0,0),(14,26,94),(2,60,93),(2,35,105),(0,0,0),(0,32,106),(1,32,106),(0,0,0),(0,0,0),(4,10,110),(6,32,105),(0,71,85),(0,0,0),(2,32,106),(0,13,110),(0,0,0),(0,0,0),(10,6,106),(4,40,103),(0,57,95),(0,0,0),(3,60,93),(0,66,89),(0,0,0),(0,0,0),(3,43,102),(0,20,109),(1,20,109),(0,0,0),(7,54,95),(2,66,89),(0,0,0),(0,0,0),(7,8,109),(0,25,108),(0,29,107),(0,0,0),(11,31,100),(3,71,85),(0,0,0),(0,0,0),(0,14,110),(1,14,110),(2,29,107),(0,0,0),(10,8,106),(0,50,99),(0,0,0),(0,0,0),(0,48,100),(1,48,100),(4,19,109),(0,0,0),(0,52,98),(1,52,98),(0,0,0),(0,0,0),(2,48,100),(4,60,93),(4,35,105),(0,0,0),(2,52,98),(0,46,101),(0,0,0),(0,0,0),(6,2,110),(0,0,111),(0,1,111),(0,0,0),(4,32,106),(0,2,111),(0,0,0),(0,0,0),(3,50,99),(0,77,80),(0,3,111),(0,0,0),(6,4,110),(2,2,111),(0,0,0),(0,0,0),(10,10,106),(0,4,111),(1,4,111),(0,0,0),(0,26,108),(1,26,108),(0,0,0),(0,0,0),(3,46,101),(2,4,111),(0,5,111),(0,0,0),(2,26,108),(0,30,107),(0,0,0),(0,0,0),(0,56,96),(1,56,96),(2,5,111),(0,0,0),(0,16,110),(0,6,111),(0,0,0),(0,0,0),(2,56,96),(8,20,107),(6,65,89),(0,0,0),(2,16,110),(0,22,109),(0,0,0),(0,0,0),(0,68,88),(1,68,88),(0,7,111),(0,0,0),(4,52,98),(0,42,103),(0,0,0),(0,0,0),(2,68,88),(0,64,91),(1,64,91),(0,0,0),(6,8,110),(2,42,103),(0,0,0),(0,0,0),(3,6,111),(0,8,111),(1,8,111),(0,0,0),(8,74,80),(0,17,110),(0,0,0),(0,0,0),(0,34,106),(0,27,108),(0,37,105),(0,0,0),(7,38,103),(2,17,110),(0,0,0),(0,0,0),(2,34,106),(0,49,100),(0,9,111),(0,0,0),(3,64,91),(10,13,106),(0,0,0),(0,0,0),(23,4,15),(0,72,85),(0,23,109),(0,0,0),(3,8,111),(0,53,98),(0,0,0),(0,0,0),(0,40,104),(1,40,104),(2,23,109),(0,0,0),(3,27,108),(0,10,111),(0,0,0),(0,0,0),(0,18,110),(1,18,110),(5,50,99),(0,0,0),(3,49,100),(0,45,102),(0,0,0),(0,0,0),(2,18,110),(0,63,92),(0,55,97),(0,0,0),(0,60,94),(0,71,86),(0,0,0),(0,0,0),(3,53,98),(2,63,92),(0,11,111),(0,0,0),(2,60,94),(2,71,86),(0,0,0),(0,0,0),(0,28,108),(1,28,108),(2,11,111),(0,0,0),(7,3,110),(4,17,110),(0,0,0),(0,0,0),(0,66,90),(0,24,109),(0,43,103),(0,0,0),(3,63,92),(0,19,110),(0,0,0),(0,0,0),(2,66,90),(0,12,111),(1,12,111),(0,0,0),(7,5,110),(0,38,105),(0,0,0),(0,0,0),(11,46,95),(0,32,107),(1,32,107),(0,0,0),(6,32,106),(2,38,105),(0,0,0),(0,0,0),(4,40,104),(2,32,107),(0,79,79),(0,0,0),(0,78,80),(1,78,80),(0,0,0),(0,0,0),(3,19,110),(7,65,89),(0,13,111),(0,0,0),(2,78,80),(0,62,93),(0,0,0),(0,0,0),(3,38,105),(0,41,104),(1,41,104),(0,0,0),(0,20,110),(1,20,110),(0,0,0),(0,0,0),(7,56,95),(0,29,108),(0,25,109),(0,0,0),(2,20,110),(3,79,79),(0,0,0),(0,0,0),(4,28,108),(2,29,108),(0,75,83),(0,0,0),(8,40,102),(0,14,111),(0,0,0),(0,0,0),(0,46,102),(1,46,102),(2,75,83),(0,0,0),(3,41,104),(2,14,111),(0,0,0),(0,0,0),(2,46,102),(4,12,111),(9,40,101),(0,0,0),(0,36,106),(1,36,106),(0,0,0),(0,0,0),(7,23,108),(4,32,107),(0,33,107),(0,0,0),(2,36,106),(0,21,110),(0,0,0),(0,0,0),(0,0,112),(0,1,112),(0,15,111),(0,0,0),(0,2,112),(1,2,112),(0,0,0),(0,0,0),(2,0,112),(0,3,112),(0,73,85),(0,0,0),(2,2,112),(0,26,109),(0,0,0),(0,0,0),(0,4,112),(1,4,112),(2,73,85),(0,0,0),(0,30,108),(1,30,108),(0,0,0),(0,0,0),(2,4,112),(0,5,112),(1,5,112),(0,0,0),(2,30,108),(3,15,111),(0,0,0),(0,0,0),(7,28,107),(0,16,111),(1,16,111),(0,0,0),(0,6,112),(1,6,112),(0,0,0),(0,0,0),(0,22,110),(1,22,110),(5,19,110),(0,0,0),(2,6,112),(0,67,90),(0,0,0),(0,0,0),(2,22,110),(0,7,112),(1,7,112),(0,0,0),(3,5,112),(2,67,90),(0,0,0),(0,0,0),(10,28,104),(0,51,100),(0,49,101),(0,0,0),(3,16,111),(0,34,107),(0,0,0),(0,0,0),(0,8,112),(1,8,112),(0,17,111),(0,0,0),(4,2,112),(0,47,102),(0,0,0),(0,0,0),(2,8,112),(4,3,112),(0,63,93),(0,0,0),(3,7,112),(2,47,102),(0,0,0),(0,0,0),(4,4,112),(0,9,112),(1,9,112),(0,0,0),(3,51,100),(0,23,110),(0,0,0),(0,0,0),(3,34,107),(2,9,112),(0,45,103),(0,0,0),(10,20,106),(0,66,91),(0,0,0),(0,0,0),(3,47,102),(0,79,80),(1,79,80),(0,0,0),(0,10,112),(0,18,111),(0,0,0),(0,0,0),(4,22,110),(2,79,80),(6,55,97),(0,0,0),(2,10,112),(0,77,82),(0,0,0),(0,0,0),(3,23,110),(4,7,112),(0,57,97),(0,0,0),(7,46,101),(2,77,82),(0,0,0),(0,0,0),(3,66,91),(0,11,112),(1,11,112),(0,0,0),(3,79,80),(4,34,107),(0,0,0),(0,0,0),(3,18,111),(2,11,112),(0,35,107),(0,0,0),(0,24,110),(1,24,110),(0,0,0),(0,0,0),(0,38,106),(0,75,84),(0,19,111),(0,0,0),(2,24,110),(3,57,97),(0,0,0),(0,0,0),(0,12,112),(0,65,92),(1,65,92),(0,0,0),(3,11,112),(4,23,110),(0,0,0),(0,0,0),(2,12,112),(0,59,96),(1,59,96),(0,0,0),(6,78,80),(0,50,101),(0,0,0),(0,0,0),(0,52,100),(1,52,100),(0,41,105),(0,0,0),(0,48,102),(1,48,102),(0,0,0),(0,0,0),(2,52,100),(0,13,112),(1,13,112),(0,0,0),(2,48,102),(0,54,99),(0,0,0),(0,0,0),(7,64,91),(0,20,111),(0,29,109),(0,0,0),(0,68,90),(0,25,110),(0,0,0),(0,0,0),(3,50,101),(2,20,111),(2,29,109),(0,0,0),(2,68,90),(2,25,110),(0,0,0),(0,0,0),(6,46,102),(7,37,105),(4,35,107),(0,0,0),(0,14,112),(1,14,112),(0,0,0),(0,0,0),(3,54,99),(0,36,107),(0,61,95),(0,0,0),(2,14,112),(3,29,109),(0,0,0),(0,0,0),(0,44,104),(0,33,108),(1,33,108),(0,0,0),(7,53,98),(0,39,106),(0,0,0),(0,0,0),(2,44,104),(2,33,108),(0,21,111),(0,0,0),(6,2,112),(2,39,106),(0,0,0),(0,0,0),(4,52,100),(0,0,113),(0,1,113),(0,0,0),(3,36,107),(0,2,113),(0,0,0),(0,0,0),(0,26,110),(1,26,110),(0,3,113),(0,0,0),(3,33,108),(0,30,109),(0,0,0),(0,0,0),(2,26,110),(0,4,113),(1,4,113),(0,0,0),(4,68,90),(0,42,105),(0,0,0),(0,0,0),(11,15,106),(2,4,113),(0,5,113),(0,0,0),(3,0,113),(2,42,105),(0,0,0),(0,0,0),(0,16,112),(1,16,112),(0,51,101),(0,0,0),(4,14,112),(0,6,113),(0,0,0),(0,0,0),(0,78,82),(0,53,100),(1,53,100),(0,0,0),(3,4,113),(2,6,113),(0,0,0),(0,0,0),(0,60,96),(1,60,96),(0,7,113),(0,0,0),(0,34,108),(0,70,89),(0,0,0),(0,0,0),(2,60,96),(7,79,79),(0,55,99),(0,0,0),(2,34,108),(0,27,110),(0,0,0),(0,0,0),(0,76,84),(0,8,113),(1,8,113),(0,0,0),(0,40,106),(1,40,106),(0,0,0),(0,0,0),(2,76,84),(0,45,104),(0,31,109),(0,0,0),(2,40,106),(3,7,113),(0,0,0),(0,0,0),(3,70,89),(2,45,104),(0,9,113),(0,0,0),(8,26,108),(0,57,98),(0,0,0),(0,0,0),(3,27,110),(6,79,80),(2,9,113),(0,0,0),(3,8,113),(0,69,90),(0,0,0),(0,0,0),(4,16,112),(5,14,112),(4,51,101),(0,0,0),(0,18,112),(0,10,113),(0,0,0),(0,0,0),(0,74,86),(1,74,86),(0,43,105),(0,0,0),(2,18,112),(2,10,113),(0,0,0),(0,0,0),(2,74,86),(6,11,112),(2,43,105),(0,0,0),(0,28,110),(1,28,110),(0,0,0),(0,0,0),(3,69,90),(0,35,108),(0,11,113),(0,0,0),(2,28,110),(0,38,107),(0,0,0),(0,0,0),(3,10,113),(0,24,111),(0,73,87),(0,0,0),(4,40,106),(2,38,107),(0,0,0),(0,0,0),(0,50,102),(0,19,112),(1,19,112),(0,0,0),(10,48,98),(10,50,97),(0,0,0),(0,0,0),(2,50,102),(0,12,113),(1,12,113),(0,0,0),(0,54,100),(0,41,106),(0,0,0),(0,0,0),(3,38,107),(2,12,113),(6,41,105),(0,0,0),(2,54,100),(2,41,106),(0,0,0),(0,0,0),(0,72,88),(1,72,88),(5,6,113),(0,0,0),(0,46,104),(1,46,104),(0,0,0),(0,0,0),(2,72,88),(0,56,99),(0,13,113),(0,0,0),(2,46,104),(0,29,110),(0,0,0),(0,0,0),(0,20,112),(1,20,112),(0,25,111),(0,0,0),(4,28,110),(2,29,110),(0,0,0),(0,0,0),(2,20,112),(0,67,92),(1,67,92),(0,0,0),(6,14,112),(4,38,107),(0,0,0),(0,0,0),(0,36,108),(0,44,105),(0,71,89),(0,0,0),(3,56,99),(0,14,113),(0,0,0),(0,0,0),(0,58,98),(1,58,98),(0,33,109),(0,0,0),(7,23,110),(0,78,83),(0,0,0),(0,0,0),(2,58,98),(4,12,113),(2,33,109),(0,0,0),(3,67,92),(2,78,83),(0,0,0),(0,0,0),(7,79,80),(0,21,112),(1,21,112),(0,0,0),(3,44,105),(3,71,89),(0,0,0),(0,0,0),(3,14,113),(2,21,112),(0,15,113),(0,0,0),(0,0,114),(0,1,114),(0,0,0),(0,0,0)]

def wits_13 : List (ℕ × ℕ × ℕ) := [(0,2,114),(0,76,85),(1,76,85),(0,0,0),(2,0,114),(0,3,114),(0,0,0),(0,0,0),(2,2,114),(0,60,97),(0,49,103),(0,0,0),(0,4,114),(1,4,114),(0,0,0),(0,0,0),(6,16,112),(2,60,97),(2,49,103),(0,0,0),(2,4,114),(0,5,114),(0,0,0),(0,0,0),(3,1,114),(0,16,113),(1,16,113),(0,0,0),(0,22,112),(1,22,112),(0,0,0),(0,0,0),(0,6,114),(0,37,108),(1,37,108),(0,0,0),(2,22,112),(0,34,109),(0,0,0),(0,0,0),(2,6,114),(2,37,108),(0,69,91),(0,0,0),(7,50,101),(0,7,114),(0,0,0),(0,0,0),(3,5,114),(0,40,107),(0,27,111),(0,0,0),(3,16,113),(2,7,114),(0,0,0),(0,0,0),(7,13,112),(2,40,107),(0,17,113),(0,0,0),(0,8,114),(0,31,110),(0,0,0),(0,0,0),(3,34,109),(4,76,85),(2,17,113),(0,0,0),(2,8,114),(2,31,110),(0,0,0),(0,0,0),(3,7,114),(0,23,112),(1,23,112),(0,0,0),(3,40,107),(0,9,114),(0,0,0),(0,0,0),(19,50,61),(2,23,112),(16,65,69),(0,0,0),(6,18,112),(0,43,106),(0,0,0),(0,0,0),(0,68,92),(1,68,92),(5,14,113),(0,0,0),(4,22,112),(0,18,113),(0,0,0),(0,0,0),(0,10,114),(1,10,114),(5,78,83),(0,0,0),(3,23,112),(2,18,113),(0,0,0),(0,0,0),(2,10,114),(0,28,111),(0,35,109),(0,0,0),(0,38,108),(0,50,103),(0,0,0),(0,0,0),(3,43,106),(2,28,111),(2,35,109),(0,0,0),(2,38,108),(0,11,114),(0,0,0),(0,0,0),(0,24,112),(0,64,95),(0,81,81),(0,0,0),(0,32,110),(1,32,110),(0,0,0),(0,0,0),(2,24,112),(2,64,95),(0,19,113),(0,0,0),(2,32,110),(3,35,109),(0,0,0),(0,0,0),(0,56,100),(1,56,100),(0,67,93),(0,0,0),(0,12,114),(0,46,105),(0,0,0),(0,0,0),(2,56,100),(7,51,101),(2,67,93),(0,0,0),(2,12,114),(2,46,105),(0,0,0),(0,0,0),(4,68,92),(5,22,112),(0,77,85),(0,0,0),(8,10,112),(3,19,113),(0,0,0),(0,0,0),(4,10,114),(7,7,113),(0,29,111),(0,0,0),(7,70,89),(0,13,114),(0,0,0),(0,0,0),(3,46,105),(0,20,113),(1,20,113),(0,0,0),(0,44,106),(1,44,106),(0,0,0),(0,0,0),(6,36,108),(0,36,109),(1,36,109),(0,0,0),(2,44,106),(0,70,91),(0,0,0),(0,0,0),(4,24,112),(0,39,108),(1,39,108),(0,0,0),(4,32,110),(0,33,110),(0,0,0),(0,0,0),(0,14,114),(1,14,114),(0,75,87),(0,0,0),(3,20,113),(2,33,110),(0,0,0),(0,0,0),(2,14,114),(6,21,112),(2,75,87),(0,0,0),(0,60,98),(1,60,98),(0,0,0),(0,0,0),(3,70,91),(8,59,96),(0,21,113),(0,0,0),(2,60,98),(0,42,107),(0,0,0),(0,0,0),(3,33,110),(0,49,104),(1,49,104),(0,0,0),(0,26,112),(0,15,114),(0,0,0),(0,0,0),(20,18,70),(0,0,115),(0,1,115),(0,0,0),(2,26,112),(0,2,115),(0,0,0),(0,0,0),(7,35,108),(2,0,115),(0,3,115),(0,0,0),(4,44,106),(2,2,115),(0,0,0),(0,0,0),(3,42,107),(0,4,115),(1,4,115),(0,0,0),(3,49,104),(4,70,91),(0,0,0),(0,0,0),(3,15,114),(0,57,100),(0,5,115),(0,0,0),(0,16,114),(0,22,113),(0,0,0),(0,0,0),(0,34,110),(1,34,110),(2,5,115),(0,0,0),(2,16,114),(0,6,115),(0,0,0),(0,0,0),(0,40,108),(1,40,108),(5,46,105),(0,0,0),(3,4,115),(2,6,115),(0,0,0),(0,0,0),(2,40,108),(0,27,112),(0,7,115),(0,0,0),(3,57,100),(3,5,115),(0,0,0),(0,0,0),(3,22,113),(2,27,112),(0,31,111),(0,0,0),(0,72,90),(0,17,114),(0,0,0),(0,0,0),(3,6,115),(0,8,115),(1,8,115),(0,0,0),(2,72,90),(2,17,114),(0,0,0),(0,0,0),(7,67,92),(0,79,84),(0,23,113),(0,0,0),(3,27,112),(3,7,115),(0,0,0),(0,0,0),(6,68,92),(2,79,84),(0,9,115),(0,0,0),(7,14,113),(0,78,85),(0,0,0),(0,0,0),(0,64,96),(0,52,103),(1,52,103),(0,0,0),(0,50,104),(1,50,104),(0,0,0),(0,0,0),(0,18,114),(1,18,114),(0,71,91),(0,0,0),(2,50,104),(0,10,115),(0,0,0),(0,0,0),(0,28,112),(0,48,105),(1,48,105),(0,0,0),(8,34,108),(2,10,115),(0,0,0),(0,0,0),(2,28,112),(0,56,101),(1,56,101),(0,0,0),(3,52,103),(8,27,110),(0,0,0),(0,0,0),(7,76,85),(0,24,113),(0,11,115),(0,0,0),(4,72,90),(3,71,91),(0,0,0),(0,0,0),(0,46,106),(1,46,106),(2,11,115),(0,0,0),(3,48,105),(0,19,114),(0,0,0),(0,0,0),(2,46,106),(4,79,84),(4,23,113),(0,0,0),(0,58,100),(1,58,100),(0,0,0),(0,0,0),(7,16,113),(0,12,115),(1,12,115),(0,0,0),(2,58,100),(3,11,115),(0,0,0),(0,0,0),(4,64,96),(2,12,115),(0,63,97),(0,0,0),(4,50,104),(0,66,95),(0,0,0),(0,0,0),(3,19,114),(0,29,112),(1,29,112),(0,0,0),(6,44,106),(2,66,95),(0,0,0),(0,0,0),(4,28,112),(2,29,112),(0,13,115),(0,0,0),(0,20,114),(0,74,89),(0,0,0),(0,0,0),(11,63,90),(0,60,99),(0,39,109),(0,0,0),(2,20,114),(2,74,89),(0,0,0),(0,0,0),(3,66,95),(2,60,99),(0,33,111),(0,0,0),(3,29,112),(10,53,98),(0,0,0),(0,0,0),(4,46,106),(0,51,104),(0,53,103),(0,0,0),(6,60,98),(0,14,115),(0,0,0),(0,0,0),(3,74,89),(2,51,104),(0,49,105),(0,0,0),(0,42,108),(0,55,102),(0,0,0),(0,0,0),(11,1,110),(4,12,115),(2,49,105),(0,0,0),(2,42,108),(0,21,114),(0,0,0),(0,0,0),(8,72,88),(0,65,96),(1,65,96),(0,0,0),(0,30,112),(0,26,113),(0,0,0),(0,0,0),(0,62,98),(1,62,98),(0,15,115),(0,0,0),(2,30,112),(2,26,113),(0,0,0),(0,0,0),(0,0,116),(0,1,116),(1,1,116),(0,0,0),(0,2,116),(1,2,116),(0,0,0),(0,0,0),(2,0,116),(0,3,116),(0,79,85),(0,0,0),(2,2,116),(0,37,110),(0,0,0),(0,0,0),(0,4,116),(1,4,116),(0,45,107),(0,0,0),(19,29,76),(0,34,111),(0,0,0),(0,0,0),(0,22,114),(0,5,116),(1,5,116),(0,0,0),(3,1,116),(2,34,111),(0,0,0),(0,0,0),(2,22,114),(2,5,116),(4,49,105),(0,0,0),(0,6,116),(1,6,116),(0,0,0),(0,0,0),(3,37,110),(7,77,85),(0,27,113),(0,0,0),(2,6,116),(3,45,107),(0,0,0),(0,0,0),(3,34,111),(0,7,116),(1,7,116),(0,0,0),(3,5,116),(4,26,113),(0,0,0),(0,0,0),(4,62,98),(0,43,108),(0,17,115),(0,0,0),(11,37,104),(8,3,114),(0,0,0),(0,0,0),(0,8,116),(1,8,116),(0,61,99),(0,0,0),(4,2,116),(0,23,114),(0,0,0),(0,0,0),(2,8,116),(4,3,116),(2,61,99),(0,0,0),(3,7,116),(2,23,114),(0,0,0),(0,0,0),(4,4,116),(0,9,116),(1,9,116),(0,0,0),(0,48,106),(1,48,106),(0,0,0),(0,0,0),(0,38,110),(1,38,110),(0,35,111),(0,0,0),(2,48,106),(0,18,115),(0,0,0),(0,0,0),(2,38,110),(0,28,113),(1,28,113),(0,0,0),(0,10,116),(1,10,116),(0,0,0),(0,0,0),(7,49,104),(2,28,113),(0,41,109),(0,0,0),(2,10,116),(0,46,107),(0,0,0),(0,0,0),(0,32,112),(1,32,112),(2,41,109),(0,0,0),(0,24,114),(0,63,98),(0,0,0),(0,0,0),(0,74,90),(0,11,116),(1,11,116),(0,0,0),(2,24,114),(2,63,98),(0,0,0),(0,0,0),(2,74,90),(2,11,116),(0,19,115),(0,0,0),(12,14,108),(3,41,109),(0,0,0),(0,0,0),(3,46,107),(7,5,115),(2,19,115),(0,0,0),(7,22,113),(0,69,94),(0,0,0),(0,0,0),(0,12,116),(1,12,116),(5,34,111),(0,0,0),(3,11,116),(2,69,94),(0,0,0),(0,0,0),(2,12,116),(12,0,109),(0,29,113),(0,0,0),(6,20,114),(0,82,83),(0,0,0),(0,0,0),(7,27,112),(0,36,111),(1,36,111),(0,0,0),(4,10,116),(0,25,114),(0,0,0),(0,0,0),(3,69,94),(0,13,116),(0,51,105),(0,0,0),(7,17,114),(2,25,114),(0,0,0),(0,0,0),(4,32,112),(0,33,112),(0,55,103),(0,0,0),(4,24,114),(0,49,106),(0,0,0),(0,0,0),(3,82,83),(2,33,112),(2,55,103),(0,0,0),(3,36,111),(0,42,109),(0,0,0),(0,0,0),(0,72,92),(0,68,95),(1,68,95),(0,0,0),(0,14,116),(0,57,102),(0,0,0),(0,0,0),(2,72,92),(2,68,95),(0,47,107),(0,0,0),(2,14,116),(2,57,102),(0,0,0),(0,0,0),(3,49,106),(5,48,106),(0,21,115),(0,0,0),(7,10,115),(0,30,113),(0,0,0),(0,0,0),(0,26,114),(0,77,88),(1,77,88),(0,0,0),(3,68,95),(2,30,113),(0,0,0),(0,0,0),(2,26,114),(0,15,116),(0,59,101),(0,0,0),(8,44,106),(3,47,107),(0,0,0),(0,0,0),(6,4,116),(0,0,117),(0,1,117),(0,0,0),(19,47,68),(0,2,117),(0,0,0),(0,0,0),(3,30,113),(0,76,89),(0,3,117),(0,0,0),(0,34,112),(1,34,112),(0,0,0),(0,0,0),(8,14,114),(0,4,117),(1,4,117),(0,0,0),(2,34,112),(0,22,115),(0,0,0),(0,0,0),(0,16,116),(1,16,116),(0,5,117),(0,0,0),(3,0,117),(2,22,115),(0,0,0),(0,0,0),(2,16,116),(0,61,100),(1,61,100),(0,0,0),(3,76,89),(0,6,117),(0,0,0),(0,0,0),(7,29,112),(0,52,105),(0,31,113),(0,0,0),(0,54,104),(1,54,104),(0,0,0),(0,0,0),(0,50,106),(1,50,106),(0,7,117),(0,0,0),(2,54,104),(3,5,117),(0,0,0),(0,0,0),(2,50,106),(0,17,116),(1,17,116),(0,0,0),(3,61,100),(13,76,76),(0,0,0),(0,0,0),(3,6,117),(0,8,117),(0,23,115),(0,0,0),(3,52,105),(0,74,91),(0,0,0),(0,0,0),(6,38,110),(2,8,117),(2,23,115),(0,0,0),(4,34,112),(0,38,111),(0,0,0),(0,0,0),(0,58,102),(0,35,112),(0,9,117),(0,0,0),(3,17,116),(2,38,111),(0,0,0),(0,0,0),(2,58,102),(2,35,112),(0,83,83),(0,0,0),(0,18,116),(0,41,110),(0,0,0),(0,0,0),(3,74,91),(4,61,100),(0,69,95),(0,0,0),(2,18,116),(0,10,117),(0,0,0),(0,0,0),(3,38,111),(0,32,113),(1,32,113),(0,0,0),(0,80,86),(1,80,86),(0,0,0),(0,0,0),(4,50,106),(0,24,115),(1,24,115),(0,0,0),(2,80,86),(3,83,83),(0,0,0),(0,0,0),(3,41,110),(2,24,115),(0,11,117),(0,0,0),(7,37,110),(3,69,95),(0,0,0),(0,0,0),(3,10,117),(0,19,116),(1,19,116),(0,0,0),(3,32,113),(4,74,91),(0,0,0),(0,0,0),(7,5,116),(2,19,116),(6,29,113),(0,0,0),(0,78,88),(0,65,98),(0,0,0),(0,0,0),(4,58,102),(0,12,117),(0,53,105),(0,0,0),(2,78,88),(0,29,114),(0,0,0),(0,0,0),(0,36,112),(0,55,104),(0,39,111),(0,0,0),(0,62,100),(1,62,100),(0,0,0),(0,0,0),(2,36,112),(2,55,104),(0,25,115),(0,0,0),(2,62,100),(4,10,117),(0,0,0),(0,0,0),(0,20,116),(1,20,116),(0,13,117),(0,0,0),(3,12,117),(3,53,105),(0,0,0),(0,0,0),(0,42,110),(1,42,110),(2,13,117),(0,0,0),(3,55,104),(3,39,111),(0,0,0),(0,0,0),(2,42,110),(0,47,108),(1,47,108),(0,0,0),(0,76,90),(0,71,94),(0,0,0),(0,0,0),(7,9,116),(2,47,108),(5,74,91),(0,0,0),(2,76,90),(0,14,117),(0,0,0),(0,0,0),(6,26,114),(6,77,88),(5,38,111),(0,0,0),(4,78,88),(2,14,117),(0,0,0),(0,0,0),(0,30,114),(0,21,116),(0,67,97),(0,0,0),(3,47,108),(0,26,115),(0,0,0),(0,0,0),(2,30,114),(2,21,116),(0,45,109),(0,0,0),(4,62,100),(2,26,115),(0,0,0),(0,0,0),(3,14,117),(0,37,112),(0,15,117),(0,0,0),(6,34,112),(10,41,106),(0,0,0),(0,0,0),(4,20,116),(0,40,111),(0,61,101),(0,0,0),(0,0,118),(0,1,118),(0,0,0),(0,0,0),(0,2,118),(1,2,118),(2,61,101),(0,0,0),(2,0,118),(0,3,118),(0,0,0),(0,0,0),(2,2,118),(4,47,108),(8,49,105),(0,0,0),(0,4,118),(0,54,105),(0,0,0),(0,0,0),(10,20,112),(0,16,117),(1,16,117),(0,0,0),(2,4,118),(0,5,118),(0,0,0),(0,0,0),(0,56,104),(1,56,104),(0,27,115),(0,0,0),(7,82,83),(0,31,114),(0,0,0),(0,0,0),(0,6,118),(1,6,118),(2,27,115),(0,0,0),(7,25,114),(2,31,114),(0,0,0),(0,0,0),(0,48,108),(0,63,100),(1,63,100),(0,0,0),(3,16,117),(0,7,118),(0,0,0),(0,0,0),(2,48,108),(0,69,96),(0,17,117),(0,0,0),(7,49,106),(2,7,118),(0,0,0),(0,0,0),(3,31,114),(0,23,116),(1,23,116),(0,0,0),(0,8,118),(1,8,118),(0,0,0),(0,0,0),(4,2,118),(2,23,116),(0,35,113),(0,0,0),(2,8,118),(0,46,109),(0,0,0),(0,0,0)]

def wits_14 : List (ℕ × ℕ × ℕ) := [(3,7,118),(5,76,90),(0,41,111),(0,0,0),(0,60,102),(0,9,118),(0,0,0),(0,0,0),(0,0,0),(0,28,115),(1,28,115),(0,0,0),(2,60,102),(0,18,117),(0,0,0),(0,0,0),(4,56,104),(2,28,115),(4,27,115),(0,0,0),(0,32,114),(1,32,114),(0,0,0),(0,0,0),(0,10,118),(1,10,118),(0,65,99),(0,0,0),(2,32,114),(0,77,90),(0,0,0),(0,0,0),(0,24,116),(0,68,97),(1,68,97),(0,0,0),(0,44,110),(1,44,110),(0,0,0),(0,0,0),(2,24,116),(2,68,97),(4,17,117),(0,0,0),(2,44,110),(0,11,118),(0,0,0),(0,0,0),(7,4,117),(4,23,116),(0,19,117),(0,0,0),(4,8,118),(2,11,118),(0,0,0),(0,0,0),(3,77,90),(0,76,91),(1,76,91),(0,0,0),(3,68,97),(4,46,109),(0,0,0),(0,0,0),(7,61,100),(0,36,113),(0,29,115),(0,0,0),(0,12,118),(1,12,118),(0,0,0),(0,0,0),(3,11,118),(2,36,113),(2,29,115),(0,0,0),(2,12,118),(3,19,117),(0,0,0),(0,0,0),(6,42,110),(0,25,116),(1,25,116),(0,0,0),(3,76,91),(0,33,114),(0,0,0),(0,0,0),(4,10,118),(0,20,117),(0,47,109),(0,0,0),(3,36,113),(0,13,118),(0,0,0),(0,0,0),(0,64,100),(1,64,100),(2,47,109),(0,0,0),(4,44,110),(2,13,118),(0,0,0),(0,0,0),(2,64,100),(10,28,111),(10,35,109),(0,0,0),(3,25,116),(4,11,118),(0,0,0),(0,0,0),(0,84,84),(1,84,84),(0,83,85),(0,0,0),(0,70,96),(1,70,96),(0,0,0),(0,0,0),(0,14,118),(1,14,118),(2,83,85),(0,0,0),(2,70,96),(0,30,115),(0,0,0),(0,0,0),(2,14,118),(4,36,113),(0,21,117),(0,0,0),(0,26,116),(1,26,116),(0,0,0),(0,0,0),(7,32,113),(6,40,111),(0,37,113),(0,0,0),(2,26,116),(3,83,85),(0,0,0),(0,0,0),(0,40,112),(1,40,112),(2,37,113),(0,0,0),(19,8,85),(0,15,118),(0,0,0),(0,0,0),(0,34,114),(0,52,107),(1,52,107),(0,0,0),(6,4,118),(0,66,99),(0,0,0),(0,0,0),(2,34,114),(0,0,119),(0,1,119),(0,0,0),(0,50,108),(0,2,119),(0,0,0),(0,0,0),(6,56,104),(2,0,119),(0,3,119),(0,0,0),(2,50,108),(0,22,117),(0,0,0),(0,0,0),(3,15,118),(0,4,119),(1,4,119),(0,0,0),(0,16,118),(1,16,118),(0,0,0),(0,0,0),(0,78,90),(0,27,116),(0,5,119),(0,0,0),(2,16,118),(3,1,119),(0,0,0),(0,0,0),(2,78,90),(2,27,116),(2,5,119),(0,0,0),(4,26,116),(0,6,119),(0,0,0),(0,0,0),(3,22,117),(6,23,116),(4,37,113),(0,0,0),(3,4,119),(2,6,119),(0,0,0),(0,0,0),(4,40,112),(0,60,103),(0,7,119),(0,0,0),(3,27,116),(0,17,118),(0,0,0),(0,0,0),(0,46,110),(1,46,110),(0,23,117),(0,0,0),(6,60,102),(0,35,114),(0,0,0),(0,0,0),(2,46,110),(0,8,119),(1,8,119),(0,0,0),(0,68,98),(1,68,98),(0,0,0),(0,0,0),(19,22,83),(2,8,119),(4,3,119),(0,0,0),(2,68,98),(3,7,119),(0,0,0),(0,0,0),(0,28,116),(1,28,116),(0,9,119),(0,0,0),(4,16,118),(3,23,117),(0,0,0),(0,0,0),(0,18,118),(0,32,115),(1,32,115),(0,0,0),(3,8,119),(10,22,113),(0,0,0),(0,0,0),(2,18,118),(0,44,111),(0,53,107),(0,0,0),(12,36,106),(0,10,119),(0,0,0),(0,0,0),(7,40,111),(0,24,117),(1,24,117),(0,0,0),(7,1,118),(2,10,119),(0,0,0),(0,0,0),(11,29,110),(2,24,117),(0,57,105),(0,0,0),(3,32,115),(4,17,118),(0,0,0),(0,0,0),(4,46,110),(0,84,85),(0,11,119),(0,0,0),(3,44,111),(0,19,118),(0,0,0),(0,0,0),(3,10,119),(2,84,85),(0,39,113),(0,0,0),(0,36,114),(0,82,87),(0,0,0),(0,0,0),(11,14,113),(0,29,116),(1,29,116),(0,0,0),(2,36,114),(2,82,87),(0,0,0),(0,0,0),(4,28,116),(0,12,119),(1,12,119),(0,0,0),(0,42,112),(0,47,110),(0,0,0),(0,0,0),(0,74,94),(1,74,94),(0,25,117),(0,0,0),(2,42,112),(2,47,110),(0,0,0),(0,0,0),(2,74,94),(0,80,89),(1,80,89),(0,0,0),(0,20,118),(1,20,118),(0,0,0),(0,0,0),(6,84,84),(2,80,89),(0,13,119),(0,0,0),(2,20,118),(12,34,107),(0,0,0),(0,0,0),(3,47,110),(7,35,113),(2,13,119),(0,0,0),(7,46,109),(0,79,90),(0,0,0),(0,0,0),(14,28,104),(4,84,85),(0,45,111),(0,0,0),(3,80,89),(2,79,90),(0,0,0),(0,0,0),(7,28,115),(5,68,98),(0,73,95),(0,0,0),(0,30,116),(0,14,119),(0,0,0),(0,0,0),(6,40,112),(4,29,116),(2,73,95),(0,0,0),(2,30,116),(0,21,118),(0,0,0),(0,0,0),(0,52,108),(0,40,113),(1,40,113),(0,0,0),(0,56,106),(0,63,102),(0,0,0),(0,0,0),(2,52,108),(2,40,113),(4,25,117),(0,0,0),(2,56,106),(0,34,115),(0,0,0),(0,0,0),(3,14,119),(4,80,89),(0,15,119),(0,0,0),(4,20,118),(0,58,105),(0,0,0),(0,0,0),(3,21,118),(0,43,112),(1,43,112),(0,0,0),(3,40,113),(2,58,105),(0,0,0),(0,0,0),(0,0,120),(0,1,120),(1,1,120),(0,0,0),(0,2,120),(1,2,120),(0,0,0),(0,0,0),(0,22,118),(0,3,120),(1,3,120),(0,0,0),(2,2,120),(3,15,119),(0,0,0),(0,0,0),(0,4,120),(0,16,119),(0,27,117),(0,0,0),(3,43,112),(4,14,119),(0,0,0),(0,0,0),(2,4,120),(0,5,120),(0,65,101),(0,0,0),(3,1,120),(4,21,118),(0,0,0),(0,0,0),(4,52,108),(2,5,120),(2,65,101),(0,0,0),(0,6,120),(0,46,111),(0,0,0),(0,0,0),(0,38,114),(1,38,114),(14,33,103),(0,0,0),(2,6,120),(2,46,111),(0,0,0),(0,0,0),(2,38,114),(0,7,120),(0,17,119),(0,0,0),(0,84,86),(0,23,118),(0,0,0),(0,0,0),(6,28,116),(2,7,120),(0,83,87),(0,0,0),(2,84,86),(0,75,94),(0,0,0),(0,0,0),(0,8,120),(1,8,120),(2,83,87),(0,0,0),(0,82,88),(1,82,88),(0,0,0),(0,0,0),(2,8,120),(0,28,117),(0,55,107),(0,0,0),(2,82,88),(3,17,119),(0,0,0),(0,0,0),(0,32,116),(0,9,120),(0,51,109),(0,0,0),(16,28,98),(0,18,119),(0,0,0),(0,0,0),(2,32,116),(0,67,100),(1,67,100),(0,0,0),(7,15,118),(2,18,119),(0,0,0),(0,0,0),(7,52,107),(2,67,100),(5,63,102),(0,0,0),(0,10,120),(0,49,110),(0,0,0),(0,0,0),(0,70,98),(1,70,98),(0,59,105),(0,0,0),(2,10,120),(2,49,110),(0,0,0),(0,0,0),(2,70,98),(4,7,120),(2,59,105),(0,0,0),(3,67,100),(0,39,114),(0,0,0),(0,0,0),(7,4,119),(0,11,120),(0,19,119),(0,0,0),(6,42,112),(2,39,114),(0,0,0),(0,0,0),(3,49,110),(2,11,120),(0,29,117),(0,0,0),(4,82,88),(0,42,113),(0,0,0),(0,0,0),(8,10,118),(0,61,104),(1,61,104),(0,0,0),(6,20,118),(2,42,113),(0,0,0),(0,0,0),(0,12,120),(0,33,116),(1,33,116),(0,0,0),(0,78,92),(0,25,118),(0,0,0),(0,0,0),(2,12,120),(2,33,116),(12,55,99),(0,0,0),(2,78,92),(0,66,101),(0,0,0),(0,0,0),(3,42,113),(0,20,119),(0,69,99),(0,0,0),(3,61,104),(2,66,101),(0,0,0),(0,0,0),(4,70,98),(0,13,120),(1,13,120),(0,0,0),(3,33,116),(6,14,119),(0,0,0),(0,0,0),(3,25,118),(2,13,120),(0,63,103),(0,0,0),(0,54,108),(1,54,108),(0,0,0),(0,0,0),(3,66,101),(0,52,109),(1,52,109),(0,0,0),(2,54,108),(0,30,117),(0,0,0),(0,0,0),(7,32,115),(0,72,97),(0,37,115),(0,0,0),(0,14,120),(1,14,120),(0,0,0),(0,0,0),(0,26,118),(1,26,118),(0,21,119),(0,0,0),(2,14,120),(3,63,103),(0,0,0),(0,0,0),(2,26,118),(4,33,116),(2,21,119),(0,0,0),(0,34,116),(1,34,116),(0,0,0),(0,0,0),(3,30,117),(6,1,120),(0,43,113),(0,0,0),(2,34,116),(0,85,86),(0,0,0),(0,0,0),(0,68,100),(0,15,120),(1,15,120),(0,0,0),(7,19,118),(0,65,102),(0,0,0),(0,0,0),(2,68,100),(0,83,88),(1,83,88),(0,0,0),(7,82,87),(2,65,102),(0,0,0),(0,0,0),(7,29,116),(0,0,121),(0,1,121),(0,0,0),(4,54,108),(0,2,121),(0,0,0),(0,0,0),(3,85,86),(2,0,121),(0,3,121),(0,0,0),(3,15,120),(0,27,118),(0,0,0),(0,0,0),(0,16,120),(0,4,121),(1,4,121),(0,0,0),(0,46,112),(0,81,90),(0,0,0),(0,0,0),(2,16,120),(2,4,121),(0,5,121),(0,0,0),(2,46,112),(0,38,115),(0,0,0),(0,0,0),(3,2,121),(5,78,92),(2,5,121),(0,0,0),(4,34,116),(0,6,121),(0,0,0),(0,0,0),(3,27,118),(0,35,116),(1,35,116),(0,0,0),(3,4,121),(2,6,121),(0,0,0),(0,0,0),(3,81,90),(0,17,120),(0,7,121),(0,0,0),(0,74,96),(1,74,96),(0,0,0),(0,0,0),(3,38,115),(2,17,120),(0,57,107),(0,0,0),(2,74,96),(0,51,110),(0,0,0),(0,0,0),(3,6,121),(0,8,121),(1,8,121),(0,0,0),(0,28,118),(1,28,118),(0,0,0),(0,0,0),(7,40,113),(0,32,117),(1,32,117),(0,0,0),(2,28,118),(0,59,106),(0,0,0),(0,0,0),(4,16,120),(2,32,117),(0,9,121),(0,0,0),(0,18,120),(1,18,120),(0,0,0),(0,0,0),(3,51,110),(7,15,119),(2,9,121),(0,0,0),(2,18,120),(0,78,93),(0,0,0),(0,0,0),(7,43,112),(0,24,119),(0,73,97),(0,0,0),(3,32,117),(0,10,121),(0,0,0),(0,0,0),(3,59,106),(2,24,119),(0,39,115),(0,0,0),(11,51,104),(2,10,121),(0,0,0),(0,0,0),(0,36,116),(0,47,112),(1,47,112),(0,0,0),(4,74,96),(10,74,91),(0,0,0),(0,0,0),(0,42,114),(0,19,120),(0,11,121),(0,0,0),(3,24,119),(0,29,118),(0,0,0),(0,0,0),(2,42,114),(2,19,120),(2,11,121),(0,0,0),(4,28,118),(2,29,118),(0,0,0),(0,0,0),(11,26,113),(4,32,117),(0,33,117),(0,0,0),(3,47,112),(4,59,106),(0,0,0),(0,0,0),(19,2,89),(0,12,121),(0,25,119),(0,0,0),(0,72,98),(1,72,98),(0,0,0),(0,0,0),(0,86,86),(1,86,86),(0,45,113),(0,0,0),(2,72,98),(0,54,109),(0,0,0),(0,0,0),(0,20,120),(0,76,95),(1,76,95),(0,0,0),(0,52,110),(1,52,110),(0,0,0),(0,0,0),(2,20,120),(2,76,95),(0,13,121),(0,0,0),(2,52,110),(0,58,107),(0,0,0),(0,0,0),(4,36,116),(4,47,112),(2,13,121),(0,0,0),(8,42,112),(0,50,111),(0,0,0),(0,0,0),(0,30,118),(0,37,116),(1,37,116),(0,0,0),(3,76,95),(2,50,111),(0,0,0),(0,0,0),(2,30,118),(2,37,116),(0,65,103),(0,0,0),(0,60,106),(0,14,121),(0,0,0),(0,0,0),(3,58,107),(0,21,120),(0,71,99),(0,0,0),(2,60,106),(0,34,117),(0,0,0),(0,0,0),(0,48,112),(1,48,112),(2,71,99),(0,0,0),(3,37,116),(2,34,117),(0,0,0),(0,0,0),(2,48,112),(6,0,121),(4,45,113),(0,0,0),(7,39,114),(3,65,103),(0,0,0),(0,0,0),(0,80,92),(1,80,92),(0,15,121),(0,0,0),(3,21,120),(0,62,105),(0,0,0),(0,0,0),(2,80,92),(6,4,121),(2,15,121),(0,0,0),(6,46,112),(2,62,105),(0,0,0),(0,0,0),(7,61,104),(8,40,113),(6,5,121),(0,0,0),(0,0,122),(0,1,122),(0,0,0),(0,0,0),(0,2,122),(1,2,122),(0,27,119),(0,0,0),(2,0,122),(0,3,122),(0,0,0),(0,0,0),(2,2,122),(0,16,121),(1,16,121),(0,0,0),(0,4,122),(1,4,122),(0,0,0),(0,0,0),(7,20,119),(2,16,121),(0,41,115),(0,0,0),(2,4,122),(0,5,122),(0,0,0),(0,0,0),(0,64,104),(0,57,108),(0,35,117),(0,0,0),(8,2,120),(2,5,122),(0,0,0),(0,0,0),(0,6,122),(1,6,122),(0,51,111),(0,0,0),(3,16,121),(5,20,120),(0,0,0),(0,0,0),(2,6,122),(0,23,120),(0,17,121),(0,0,0),(0,44,114),(0,7,122),(0,0,0),(0,0,0),(3,5,122),(2,23,120),(2,17,121),(0,0,0),(2,44,114),(2,7,122),(0,0,0),(0,0,0),(11,82,83),(0,28,119),(1,28,119),(0,0,0),(0,8,122),(1,8,122),(0,0,0),(0,0,0),(4,2,122),(2,28,119),(0,77,95),(0,0,0),(2,8,122),(0,61,106),(0,0,0),(0,0,0),(3,7,122),(4,16,121),(0,69,101),(0,0,0),(4,4,122),(0,9,122),(0,0,0),(0,0,0),(6,36,116),(0,85,88),(1,85,88),(0,0,0),(3,28,119),(2,9,122),(0,0,0),(0,0,0),(0,24,120),(0,39,116),(0,47,113),(0,0,0),(8,82,88),(3,77,95),(0,0,0),(0,0,0),(0,10,122),(0,36,117),(1,36,117),(0,0,0),(7,2,121),(0,42,115),(0,0,0),(0,0,0),(0,76,96),(1,76,96),(0,63,105),(0,0,0),(3,85,88),(2,42,115),(0,0,0),(0,0,0)]

def wits_15 : List (ℕ × ℕ × ℕ) := [(2,76,96),(6,12,121),(0,19,121),(0,0,0),(3,39,116),(0,11,122),(0,0,0),(0,0,0),(6,86,86),(4,28,119),(2,19,121),(0,0,0),(3,36,117),(0,33,118),(0,0,0),(0,0,0),(0,54,110),(0,56,109),(1,56,109),(0,0,0),(6,52,110),(0,45,114),(0,0,0),(0,0,0),(2,54,110),(0,25,120),(1,25,120),(0,0,0),(0,12,122),(1,12,122),(0,0,0),(0,0,0),(3,11,122),(2,25,120),(0,75,97),(0,0,0),(2,12,122),(5,64,104),(0,0,0),(0,0,0),(3,33,118),(0,20,121),(1,20,121),(0,0,0),(0,50,112),(1,50,112),(0,0,0),(0,0,0),(3,45,114),(0,60,107),(1,60,107),(0,0,0),(2,50,112),(0,13,122),(0,0,0),(0,0,0),(0,40,116),(1,40,116),(0,37,117),(0,0,0),(7,59,106),(0,30,119),(0,0,0),(0,0,0),(2,40,116),(7,9,121),(2,37,117),(0,0,0),(3,20,121),(2,30,119),(0,0,0),(0,0,0),(20,4,84),(0,48,113),(0,43,115),(0,0,0),(0,26,120),(0,79,94),(0,0,0),(0,0,0),(0,14,122),(1,14,122),(0,21,121),(0,0,0),(2,26,120),(2,79,94),(0,0,0),(0,0,0),(2,14,122),(4,25,120),(2,21,121),(0,0,0),(4,12,122),(10,13,118),(0,0,0),(0,0,0),(7,47,112),(8,52,109),(0,67,103),(0,0,0),(3,48,113),(0,70,101),(0,0,0),(0,0,0),(3,79,94),(4,20,121),(2,67,103),(0,0,0),(4,50,112),(0,15,122),(0,0,0),(0,0,0),(0,46,114),(1,46,114),(5,42,115),(0,0,0),(6,4,122),(2,15,122),(0,0,0),(0,0,0),(2,46,114),(0,64,105),(0,31,119),(0,0,0),(8,34,116),(0,22,121),(0,0,0),(0,0,0),(3,70,101),(0,0,123),(0,1,123),(0,0,0),(10,26,116),(0,2,123),(0,0,0),(0,0,0),(3,15,122),(0,41,116),(0,3,123),(0,0,0),(0,16,122),(1,16,122),(0,0,0),(0,0,0),(4,14,122),(0,4,123),(0,85,89),(0,0,0),(2,16,122),(0,35,118),(0,0,0),(0,0,0),(3,22,121),(2,4,123),(0,5,123),(0,0,0),(0,84,90),(1,84,90),(0,0,0),(0,0,0),(3,2,123),(0,44,115),(1,44,115),(0,0,0),(2,84,90),(0,6,123),(0,0,0),(0,0,0),(7,37,116),(2,44,115),(0,23,121),(0,0,0),(0,66,104),(0,17,122),(0,0,0),(0,0,0),(3,35,118),(7,65,103),(0,7,123),(0,0,0),(2,66,104),(2,17,122),(0,0,0),(0,0,0),(0,28,120),(0,32,119),(1,32,119),(0,0,0),(0,82,92),(1,82,92),(0,0,0),(0,0,0),(2,28,120),(0,8,123),(1,8,123),(0,0,0),(2,82,92),(3,23,121),(0,0,0),(0,0,0),(3,17,122),(2,8,123),(4,3,123),(0,0,0),(4,16,122),(0,47,114),(0,0,0),(0,0,0),(0,18,122),(1,18,122),(0,9,123),(0,0,0),(3,32,119),(2,47,114),(0,0,0),(0,0,0),(2,18,122),(0,24,121),(1,24,121),(0,0,0),(0,36,118),(1,36,118),(0,0,0),(0,0,0),(15,20,107),(2,24,121),(5,70,101),(0,0,0),(2,36,118),(0,10,123),(0,0,0),(0,0,0),(3,47,114),(0,68,103),(1,68,103),(0,0,0),(0,56,110),(0,54,111),(0,0,0),(0,0,0),(7,16,121),(0,29,120),(0,71,101),(0,0,0),(2,56,110),(0,19,122),(0,0,0),(0,0,0),(0,52,112),(1,52,112),(0,11,123),(0,0,0),(4,82,92),(2,19,122),(0,0,0),(0,0,0),(2,52,112),(4,8,123),(2,11,123),(0,0,0),(3,68,103),(10,10,119),(0,0,0),(0,0,0),(0,60,108),(1,60,108),(0,25,121),(0,0,0),(3,29,120),(0,50,113),(0,0,0),(0,0,0),(2,60,108),(0,12,123),(1,12,123),(0,0,0),(7,7,122),(0,74,99),(0,0,0),(0,0,0),(11,5,118),(2,12,123),(10,11,119),(0,0,0),(0,20,122),(1,20,122),(0,0,0),(0,0,0),(7,28,119),(0,40,117),(1,40,117),(0,0,0),(2,20,122),(0,37,118),(0,0,0),(0,0,0),(3,50,113),(2,40,117),(0,13,123),(0,0,0),(0,30,120),(1,30,120),(0,0,0),(0,0,0),(0,70,102),(0,43,116),(1,43,116),(0,0,0),(2,30,120),(4,19,122),(0,0,0),(0,0,0),(2,70,102),(0,87,88),(1,87,88),(0,0,0),(3,40,117),(0,26,121),(0,0,0),(0,0,0),(3,37,118),(2,87,88),(8,13,121),(0,0,0),(10,20,118),(0,14,123),(0,0,0),(0,0,0),(4,60,108),(0,73,100),(1,73,100),(0,0,0),(0,64,106),(1,64,106),(0,0,0),(0,0,0),(8,30,118),(0,84,91),(0,77,97),(0,0,0),(2,64,106),(0,46,115),(0,0,0),(0,0,0),(3,26,121),(2,84,91),(0,55,111),(0,0,0),(4,20,122),(0,57,110),(0,0,0),(0,0,0),(3,14,123),(0,53,112),(0,15,123),(0,0,0),(3,73,100),(2,57,110),(0,0,0),(0,0,0),(7,56,109),(0,31,120),(0,59,109),(0,0,0),(3,84,91),(3,77,97),(0,0,0),(0,0,0),(0,22,122),(1,22,122),(0,27,121),(0,0,0),(6,84,90),(0,82,93),(0,0,0),(0,0,0),(0,0,124),(0,1,124),(1,1,124),(0,0,0),(0,2,124),(0,66,105),(0,0,0),(0,0,0),(2,0,124),(0,3,124),(0,35,119),(0,0,0),(2,2,124),(2,66,105),(0,0,0),(0,0,0),(0,4,124),(1,4,124),(2,35,119),(0,0,0),(4,64,106),(0,49,114),(0,0,0),(0,0,0),(2,4,124),(0,5,124),(1,5,124),(0,0,0),(3,1,124),(2,49,114),(0,0,0),(0,0,0),(3,66,105),(2,5,124),(4,55,111),(0,0,0),(0,6,124),(0,23,122),(0,0,0),(0,0,0),(7,48,113),(4,53,112),(0,17,123),(0,0,0),(2,6,124),(2,23,122),(0,0,0),(0,0,0),(0,32,120),(0,7,124),(0,75,99),(0,0,0),(3,5,124),(5,70,102),(0,0,0),(0,0,0),(2,32,120),(2,7,124),(0,47,115),(0,0,0),(6,36,118),(4,82,93),(0,0,0),(0,0,0),(0,8,124),(1,8,124),(2,47,115),(0,0,0),(4,2,124),(0,39,118),(0,0,0),(0,0,0),(2,8,124),(4,3,124),(4,35,119),(0,0,0),(3,7,124),(0,18,123),(0,0,0),(0,0,0),(4,4,124),(0,9,124),(1,9,124),(0,0,0),(0,24,122),(0,65,106),(0,0,0),(0,0,0),(0,58,110),(1,58,110),(5,46,115),(0,0,0),(2,24,122),(2,65,106),(0,0,0),(0,0,0),(2,58,110),(0,52,113),(1,52,113),(0,0,0),(0,10,124),(1,10,124),(0,0,0),(0,0,0),(3,18,123),(0,45,116),(0,29,121),(0,0,0),(2,10,124),(6,50,113),(0,0,0),(0,0,0),(0,88,88),(0,33,120),(0,19,123),(0,0,0),(7,35,118),(0,78,97),(0,0,0),(0,0,0),(0,50,114),(0,11,124),(1,11,124),(0,0,0),(3,52,113),(2,78,97),(0,0,0),(0,0,0),(2,50,114),(2,11,124),(0,85,91),(0,0,0),(0,62,108),(0,25,122),(0,0,0),(0,0,0),(15,16,109),(7,23,121),(0,67,105),(0,0,0),(2,62,108),(2,25,122),(0,0,0),(0,0,0),(0,12,124),(1,12,124),(2,67,105),(0,0,0),(0,40,118),(1,40,118),(0,0,0),(0,0,0),(2,12,124),(0,20,123),(0,37,119),(0,0,0),(2,40,118),(0,77,98),(0,0,0),(0,0,0),(3,25,122),(2,20,123),(0,43,117),(0,0,0),(4,10,124),(0,30,121),(0,0,0),(0,0,0),(10,12,120),(0,13,124),(1,13,124),(0,0,0),(6,64,106),(2,30,121),(0,0,0),(0,0,0),(4,88,88),(2,13,124),(4,19,123),(0,0,0),(0,34,120),(1,34,120),(0,0,0),(0,0,0),(0,26,122),(1,26,122),(6,55,111),(0,0,0),(2,34,120),(3,43,117),(0,0,0),(0,0,0),(2,26,122),(0,55,112),(0,21,123),(0,0,0),(0,14,124),(1,14,124),(0,0,0),(0,0,0),(7,68,103),(0,69,104),(0,53,113),(0,0,0),(2,14,124),(0,59,110),(0,0,0),(0,0,0),(4,12,124),(2,69,104),(0,81,95),(0,0,0),(0,72,102),(1,72,102),(0,0,0),(0,0,0),(0,66,106),(1,66,106),(2,81,95),(0,0,0),(2,72,102),(0,51,114),(0,0,0),(0,0,0),(2,66,106),(0,15,124),(0,31,121),(0,0,0),(3,69,104),(0,38,119),(0,0,0),(0,0,0),(3,59,110),(2,15,124),(2,31,121),(0,0,0),(7,50,113),(0,22,123),(0,0,0),(0,0,0),(0,80,96),(1,80,96),(5,78,97),(0,0,0),(4,34,120),(2,22,123),(0,0,0),(0,0,0),(2,80,96),(0,0,125),(0,1,125),(0,0,0),(3,15,124),(0,2,125),(0,0,0),(0,0,0),(0,16,124),(0,63,108),(0,3,125),(0,0,0),(4,14,124),(2,2,125),(0,0,0),(0,0,0),(2,16,124),(0,4,125),(1,4,125),(0,0,0),(15,13,110),(4,59,110),(0,0,0),(0,0,0),(7,43,116),(0,68,105),(0,5,125),(0,0,0),(3,0,125),(3,1,125),(0,0,0),(0,0,0),(3,2,125),(2,68,105),(0,23,123),(0,0,0),(3,63,108),(0,6,125),(0,0,0),(0,0,0),(15,25,108),(0,17,124),(1,17,124),(0,0,0),(0,28,122),(0,87,90),(0,0,0),(0,0,0),(7,73,100),(2,17,124),(0,7,125),(0,0,0),(2,28,122),(0,74,101),(0,0,0),(0,0,0),(0,56,112),(1,56,112),(0,39,119),(0,0,0),(7,46,115),(0,54,113),(0,0,0),(0,0,0),(0,42,118),(0,8,125),(1,8,125),(0,0,0),(3,17,124),(2,54,113),(0,0,0),(0,0,0),(0,36,120),(1,36,120),(4,3,125),(0,0,0),(0,18,124),(1,18,124),(0,0,0),(0,0,0),(2,36,120),(0,24,123),(0,9,125),(0,0,0),(2,18,124),(3,39,119),(0,0,0),(0,0,0),(3,54,113),(2,24,123),(0,45,117),(0,0,0),(0,70,104),(1,70,104),(0,0,0),(0,0,0),(7,1,124),(9,76,96),(2,45,117),(0,0,0),(2,70,104),(0,10,125),(0,0,0),(0,0,0),(7,3,124),(4,17,124),(0,33,121),(0,0,0),(3,24,123),(0,73,102),(0,0,0),(0,0,0),(6,12,124),(0,19,124),(1,19,124),(0,0,0),(6,40,118),(2,73,102),(0,0,0),(0,0,0),(4,56,112),(2,19,124),(0,11,125),(0,0,0),(8,56,110),(0,82,95),(0,0,0),(0,0,0),(3,10,125),(4,8,125),(0,25,123),(0,0,0),(7,23,122),(2,82,95),(0,0,0),(0,0,0),(0,48,116),(0,40,119),(1,40,119),(0,0,0),(3,19,124),(10,29,118),(0,0,0),(0,0,0),(2,48,116),(0,12,125),(1,12,125),(0,0,0),(6,34,120),(0,43,118),(0,0,0),(0,0,0),(0,20,124),(0,81,96),(1,81,96),(0,0,0),(4,70,104),(2,43,118),(0,0,0),(0,0,0),(0,30,122),(1,30,122),(0,69,105),(0,0,0),(3,40,119),(4,10,125),(0,0,0),(0,0,0),(2,30,122),(0,57,112),(0,13,125),(0,0,0),(3,12,125),(0,34,121),(0,0,0),(0,0,0),(3,43,118),(2,57,112),(0,59,111),(0,0,0),(3,81,96),(0,26,123),(0,0,0),(0,0,0),(6,66,106),(0,80,97),(1,80,97),(0,0,0),(8,30,120),(2,26,123),(0,0,0),(0,0,0),(7,52,113),(0,21,124),(1,21,124),(0,0,0),(3,57,112),(0,14,125),(0,0,0),(0,0,0),(3,34,121),(2,21,124),(0,51,115),(0,0,0),(19,35,88),(2,14,125),(0,0,0),(0,0,0),(3,26,123),(4,12,125),(2,51,115),(0,0,0),(3,80,97),(4,43,118),(0,0,0),(0,0,0),(4,20,124),(4,81,96),(0,41,119),(0,0,0),(0,38,120),(0,31,122),(0,0,0),(0,0,0),(3,14,125),(6,63,108),(0,15,125),(0,0,0),(2,38,120),(2,31,122),(0,0,0),(0,0,0),(0,0,0),(0,49,116),(0,27,123),(0,0,0),(0,22,124),(1,22,124),(0,0,0),(0,0,0),(10,80,92),(2,49,116),(0,35,121),(0,0,0),(2,22,124),(3,41,119),(0,0,0),(0,0,0),(3,31,122),(4,80,97),(0,85,93),(0,0,0),(0,0,126),(0,1,126),(0,0,0),(0,0,0),(0,2,126),(0,16,125),(1,16,125),(0,0,0),(2,0,126),(0,3,126),(0,0,0),(0,0,0),(2,2,126),(0,65,108),(1,65,108),(0,0,0),(0,4,126),(1,4,126),(0,0,0),(0,0,0),(6,56,112),(2,65,108),(0,47,117),(0,0,0),(2,4,126),(0,5,126),(0,0,0),(0,0,0),(3,1,126),(0,23,124),(1,23,124),(0,0,0),(0,32,122),(1,32,122),(0,0,0),(0,0,0),(0,6,126),(0,28,123),(0,17,125),(0,0,0),(2,32,122),(9,82,92),(0,0,0),(0,0,0),(2,6,126),(0,39,120),(1,39,120),(0,0,0),(4,22,124),(0,7,126),(0,0,0),(0,0,0),(3,5,126),(0,52,115),(1,52,115),(0,0,0),(3,23,124),(2,7,126),(0,0,0),(0,0,0),(8,32,120),(0,36,121),(0,67,107),(0,0,0),(0,8,126),(1,8,126),(0,0,0),(0,0,0),(0,62,110),(1,62,110),(2,67,107),(0,0,0),(2,8,126),(0,18,125),(0,0,0),(0,0,0),(0,24,124),(1,24,124),(10,77,95),(0,0,0),(0,50,116),(0,9,126),(0,0,0),(0,0,0),(2,24,124),(14,49,104),(4,47,117),(0,0,0),(2,50,116),(2,9,126),(0,0,0),(0,0,0),(7,0,125),(4,23,124),(0,29,123),(0,0,0),(4,32,122),(0,33,122),(0,0,0),(0,0,0),(0,10,126),(0,64,109),(1,64,109),(0,0,0),(15,34,107),(2,33,122),(0,0,0),(0,0,0),(2,10,126),(2,64,109),(0,19,125),(0,0,0),(8,10,124),(4,7,126),(0,0,0),(0,0,0),(6,20,124),(0,48,117),(1,48,117),(0,0,0),(14,16,114),(0,11,126),(0,0,0),(0,0,0)]

def wits_16 : List (ℕ × ℕ × ℕ) := [(0,40,120),(0,25,124),(1,25,124),(0,0,0),(0,80,98),(1,80,98),(0,0,0),(0,0,0),(2,40,120),(2,25,124),(0,37,121),(0,0,0),(2,80,98),(3,19,125),(0,0,0),(0,0,0),(4,24,124),(5,4,126),(0,57,113),(0,0,0),(0,12,126),(0,55,114),(0,0,0),(0,0,0),(3,11,126),(0,20,125),(1,20,125),(0,0,0),(2,12,126),(0,30,123),(0,0,0),(0,0,0),(7,8,125),(0,87,92),(0,53,115),(0,0,0),(8,40,118),(2,30,123),(0,0,0),(0,0,0),(0,34,122),(1,34,122),(0,61,111),(0,0,0),(10,50,112),(0,13,126),(0,0,0),(0,0,0),(2,34,122),(7,9,125),(2,61,111),(0,0,0),(0,26,124),(1,26,124),(0,0,0),(0,0,0),(3,30,123),(0,51,116),(1,51,116),(0,0,0),(2,26,124),(0,85,94),(0,0,0),(0,0,0),(4,40,120),(2,51,116),(0,21,125),(0,0,0),(4,80,98),(0,63,110),(0,0,0),(0,0,0),(0,14,126),(0,68,107),(1,68,107),(0,0,0),(6,22,124),(2,63,110),(0,0,0),(0,0,0),(2,14,126),(0,41,120),(1,41,120),(0,0,0),(0,78,100),(0,38,121),(0,0,0),(0,0,0),(3,85,94),(2,41,120),(0,31,123),(0,0,0),(2,78,100),(2,38,121),(0,0,0),(0,0,0),(3,63,110),(0,44,119),(1,44,119),(0,0,0),(3,68,107),(0,15,126),(0,0,0),(0,0,0),(4,34,122),(0,27,124),(0,65,109),(0,0,0),(3,41,120),(0,22,125),(0,0,0),(0,0,0),(3,38,121),(2,27,124),(2,65,109),(0,0,0),(4,26,124),(2,22,125),(0,0,0),(0,0,0),(7,81,96),(4,51,116),(5,11,126),(0,0,0),(3,44,119),(4,85,94),(0,0,0),(0,0,0),(3,15,126),(0,0,127),(0,1,127),(0,0,0),(0,16,126),(0,2,127),(0,0,0),(0,0,0),(0,70,106),(1,70,106),(0,3,127),(0,0,0),(2,16,126),(0,54,115),(0,0,0),(0,0,0),(0,60,112),(0,4,127),(1,4,127),(0,0,0),(4,78,100),(2,54,115),(0,0,0),(0,0,0),(2,60,112),(0,32,123),(0,5,127),(0,0,0),(3,0,127),(3,1,127),(0,0,0),(0,0,0),(0,28,124),(1,28,124),(0,39,121),(0,0,0),(0,42,120),(0,6,127),(0,0,0),(0,0,0),(2,28,124),(4,27,124),(2,39,121),(0,0,0),(2,42,120),(2,6,127),(0,0,0),(0,0,0),(11,34,117),(5,26,124),(0,7,127),(0,0,0),(0,36,122),(1,36,122),(0,0,0),(0,0,0),(10,28,120),(7,41,119),(0,45,119),(0,0,0),(2,36,122),(0,50,117),(0,0,0),(0,0,0),(3,6,127),(0,8,127),(1,8,127),(0,0,0),(0,64,110),(1,64,110),(0,0,0),(0,0,0),(0,18,126),(0,24,125),(0,89,91),(0,0,0),(2,64,110),(3,7,127),(0,0,0),(0,0,0),(0,88,92),(0,72,105),(0,9,127),(0,0,0),(8,18,124),(3,45,119),(0,0,0),(0,0,0),(2,88,92),(0,29,124),(0,33,123),(0,0,0),(3,8,127),(11,27,119),(0,0,0),(0,0,0),(4,28,124),(2,29,124),(2,33,123),(0,0,0),(0,48,118),(0,10,127),(0,0,0),(0,0,0),(0,86,94),(1,86,94),(0,75,103),(0,0,0),(2,48,118),(0,19,126),(0,0,0),(0,0,0),(2,86,94),(0,40,121),(1,40,121),(0,0,0),(3,29,124),(0,57,114),(0,0,0),(0,0,0),(7,23,124),(0,43,120),(0,11,127),(0,0,0),(18,4,102),(0,37,122),(0,0,0),(0,0,0),(3,10,127),(2,43,120),(2,11,127),(0,0,0),(4,64,110),(2,37,122),(0,0,0),(0,0,0),(3,19,126),(0,53,116),(1,53,116),(0,0,0),(3,40,121),(5,60,112),(0,0,0),(0,0,0),(0,84,96),(0,12,127),(1,12,127),(0,0,0),(0,20,126),(0,46,119),(0,0,0),(0,0,0),(2,84,96),(2,12,127),(4,33,123),(0,0,0),(2,20,126),(0,34,123),(0,0,0),(0,0,0),(0,68,108),(1,68,108),(0,51,117),(0,0,0),(0,74,104),(1,74,104),(0,0,0),(0,0,0),(2,68,108),(6,41,120),(0,13,127),(0,0,0),(2,74,104),(0,26,125),(0,0,0),(0,0,0),(3,46,119),(4,40,121),(2,13,127),(0,0,0),(11,39,116),(2,26,125),(0,0,0),(0,0,0),(3,34,123),(4,43,120),(4,11,127),(0,0,0),(7,33,122),(0,21,126),(0,0,0),(0,0,0),(7,64,109),(5,64,110),(0,41,121),(0,0,0),(12,14,120),(0,14,127),(0,0,0),(0,0,0),(0,38,122),(1,38,122),(2,41,121),(0,0,0),(10,64,106),(0,77,102),(0,0,0),(0,0,0),(0,44,120),(0,31,124),(1,31,124),(0,0,0),(4,20,126),(2,77,102),(0,0,0),(0,0,0),(2,44,120),(2,31,124),(6,1,127),(0,0,0),(6,16,126),(0,70,107),(0,0,0),(0,0,0),(3,14,127),(5,48,118),(0,15,127),(0,0,0),(4,74,104),(2,70,107),(0,0,0),(0,0,0),(0,22,126),(0,56,115),(0,81,99),(0,0,0),(3,31,124),(4,26,125),(0,0,0),(0,0,0),(2,22,126),(0,60,113),(0,47,119),(0,0,0),(0,54,116),(1,54,116),(0,0,0),(0,0,0),(3,70,107),(2,60,113),(2,47,119),(0,0,0),(2,54,116),(0,90,91),(0,0,0),(0,0,0),(0,0,128),(0,1,128),(1,1,128),(0,0,0),(0,2,128),(1,2,128),(0,0,0),(0,0,0),(2,0,128),(0,3,128),(1,3,128),(0,0,0),(2,2,128),(3,47,119),(0,0,0),(0,0,0),(0,4,128),(1,4,128),(5,46,119),(0,0,0),(7,85,94),(0,23,126),(0,0,0),(0,0,0),(2,4,128),(0,5,128),(1,5,128),(0,0,0),(3,1,128),(2,23,126),(0,0,0),(0,0,0),(6,18,126),(0,64,111),(0,17,127),(0,0,0),(0,6,128),(0,86,95),(0,0,0),(0,0,0),(0,50,118),(0,36,123),(1,36,123),(0,0,0),(2,6,128),(2,86,95),(0,0,0),(0,0,0),(2,50,118),(0,7,128),(1,7,128),(0,0,0),(3,5,128),(8,7,126),(0,0,0),(0,0,0),(7,44,119),(0,75,104),(0,79,101),(0,0,0),(3,64,111),(3,17,127),(0,0,0),(0,0,0),(0,8,128),(1,8,128),(2,79,101),(0,0,0),(0,24,126),(0,18,127),(0,0,0),(0,0,0),(0,66,110),(1,66,110),(5,77,102),(0,0,0),(2,24,126),(2,18,127),(0,0,0),(0,0,0),(2,66,110),(0,9,128),(0,29,125),(0,0,0),(3,75,104),(3,79,101),(0,0,0),(0,0,0),(7,0,127),(2,9,128),(0,57,115),(0,0,0),(7,2,127),(0,59,114),(0,0,0),(0,0,0),(3,18,127),(0,55,116),(1,55,116),(0,0,0),(0,10,128),(1,10,128),(0,0,0),(0,0,0),(0,78,102),(1,78,102),(0,19,127),(0,0,0),(2,10,128),(0,83,98),(0,0,0),(0,0,0),(2,78,102),(4,7,128),(0,37,123),(0,0,0),(20,6,92),(0,25,126),(0,0,0),(0,0,0),(3,59,114),(0,11,128),(1,11,128),(0,0,0),(3,55,116),(2,25,126),(0,0,0),(0,0,0),(4,8,128),(0,63,112),(1,63,112),(0,0,0),(0,46,120),(1,46,120),(0,0,0),(0,0,0),(3,83,98),(2,63,112),(8,37,121),(0,0,0),(2,46,120),(0,30,125),(0,0,0),(0,0,0),(0,12,128),(0,20,127),(1,20,127),(0,0,0),(0,34,124),(1,34,124),(0,0,0),(0,0,0),(2,12,128),(2,20,127),(0,77,103),(0,0,0),(2,34,124),(4,59,114),(0,0,0),(0,0,0),(6,38,122),(4,55,116),(0,65,111),(0,0,0),(4,10,128),(5,50,118),(0,0,0),(0,0,0),(0,26,126),(0,13,128),(1,13,128),(0,0,0),(3,20,127),(4,83,98),(0,0,0),(0,0,0),(2,26,126),(0,81,100),(0,49,119),(0,0,0),(0,70,108),(0,41,122),(0,0,0),(0,0,0),(11,54,111),(2,81,100),(0,21,127),(0,0,0),(2,70,108),(0,38,123),(0,0,0),(0,0,0),(6,22,126),(0,44,121),(1,44,121),(0,0,0),(0,14,128),(1,14,128),(0,0,0),(0,0,0),(7,40,121),(2,44,121),(0,31,125),(0,0,0),(2,14,128),(0,58,115),(0,0,0),(0,0,0),(0,56,116),(1,56,116),(0,87,95),(0,0,0),(0,60,114),(1,60,114),(0,0,0),(0,0,0),(2,56,116),(0,35,124),(1,35,124),(0,0,0),(2,60,114),(0,27,126),(0,0,0),(0,0,0),(7,53,116),(0,15,128),(1,15,128),(0,0,0),(0,86,96),(0,22,127),(0,0,0),(0,0,0),(3,58,115),(2,15,128),(5,83,98),(0,0,0),(2,86,96),(2,22,127),(0,0,0),(0,0,0),(11,37,118),(4,81,100),(4,49,119),(0,0,0),(0,52,118),(1,52,118),(0,0,0),(0,0,0),(3,27,126),(0,72,107),(0,85,97),(0,0,0),(2,52,118),(4,38,123),(0,0,0),(0,0,0),(0,16,128),(0,0,129),(0,1,129),(0,0,0),(4,14,128),(0,2,129),(0,0,0),(0,0,0),(0,42,122),(0,32,125),(0,3,129),(0,0,0),(18,2,104),(2,2,129),(0,0,0),(0,0,0),(2,42,122),(0,4,129),(0,23,127),(0,0,0),(0,28,126),(0,50,119),(0,0,0),(0,0,0),(6,8,128),(2,4,129),(0,5,129),(0,0,0),(2,28,126),(2,50,119),(0,0,0),(0,0,0),(0,36,124),(0,17,128),(1,17,128),(0,0,0),(3,32,125),(0,6,129),(0,0,0),(0,0,0),(2,36,124),(2,17,128),(6,29,125),(0,0,0),(3,4,129),(2,6,129),(0,0,0),(0,0,0),(3,50,119),(5,70,108),(0,7,129),(0,0,0),(4,52,118),(0,78,103),(0,0,0),(0,0,0),(10,36,120),(4,72,107),(2,7,129),(0,0,0),(3,17,128),(2,78,103),(0,0,0),(0,0,0),(0,48,120),(0,8,129),(0,59,115),(0,0,0),(0,18,128),(1,18,128),(0,0,0),(0,0,0),(0,74,106),(1,74,106),(0,33,125),(0,0,0),(2,18,128),(0,29,126),(0,0,0),(0,0,0),(2,74,106),(4,4,129),(0,9,129),(0,0,0),(0,68,110),(1,68,110),(0,0,0),(0,0,0),(7,1,128),(0,40,123),(1,40,123),(0,0,0),(2,68,110),(0,43,122),(0,0,0),(0,0,0),(4,36,124),(2,40,123),(0,63,113),(0,0,0),(8,48,118),(0,10,129),(0,0,0),(0,0,0),(3,29,126),(0,19,128),(1,19,128),(0,0,0),(6,34,124),(0,90,93),(0,0,0),(0,0,0),(7,5,128),(2,19,128),(0,25,127),(0,0,0),(3,40,123),(0,46,121),(0,0,0),(0,0,0),(3,43,122),(7,17,127),(0,11,129),(0,0,0),(7,86,95),(2,46,121),(0,0,0),(0,0,0),(3,10,129),(0,65,112),(1,65,112),(0,0,0),(3,19,128),(5,42,122),(0,0,0),(0,0,0),(0,30,126),(1,30,126),(0,73,107),(0,0,0),(6,70,108),(0,34,125),(0,0,0),(0,0,0),(0,20,128),(0,12,129),(1,12,129),(0,0,0),(4,68,110),(2,34,125),(0,0,0),(0,0,0),(2,20,128),(2,12,129),(10,13,125),(0,0,0),(3,65,112),(4,43,122),(0,0,0),(0,0,0),(8,68,108),(0,49,120),(1,49,120),(0,0,0),(0,80,102),(0,26,127),(0,0,0),(0,0,0),(3,34,125),(2,49,120),(0,13,129),(0,0,0),(2,80,102),(2,26,127),(0,0,0),(0,0,0),(15,65,96),(6,35,124),(2,13,129),(0,0,0),(0,38,124),(1,38,124),(0,0,0),(0,0,0),(7,55,116),(0,21,128),(1,21,128),(0,0,0),(2,38,124),(0,85,98),(0,0,0),(0,0,0),(3,26,127),(2,21,128),(8,41,121),(0,0,0),(7,83,98),(0,14,129),(0,0,0),(0,0,0),(0,54,118),(1,54,118),(4,73,107),(0,0,0),(6,52,118),(2,14,129),(0,0,0),(0,0,0),(0,72,108),(1,72,108),(0,35,125),(0,0,0),(3,21,128),(12,22,121),(0,0,0),(0,0,0),(2,72,108),(0,84,99),(0,27,127),(0,0,0),(10,22,124),(0,69,110),(0,0,0),(0,0,0),(3,14,129),(0,52,119),(0,15,129),(0,0,0),(0,22,128),(1,22,128),(0,0,0),(0,0,0),(7,20,127),(2,52,119),(2,15,129),(0,0,0),(2,22,128),(3,35,125),(0,0,0),(0,0,0),(10,2,126),(7,77,103),(5,46,121),(0,0,0),(3,84,99),(3,27,127),(0,0,0),(0,0,0),(3,69,110),(0,83,100),(1,83,100),(0,0,0),(3,52,119),(0,42,123),(0,0,0),(0,0,0),(7,13,128),(0,16,129),(1,16,129),(0,0,0),(0,0,130),(0,1,130),(0,0,0),(0,0,0),(0,2,130),(1,2,130),(5,34,125),(0,0,0),(2,0,130),(0,3,130),(0,0,0),(0,0,0),(2,2,130),(0,23,128),(1,23,128),(0,0,0),(0,4,130),(1,4,130),(0,0,0),(0,0,0),(3,42,123),(0,36,125),(0,71,109),(0,0,0),(2,4,130),(0,5,130),(0,0,0),(0,0,0),(0,92,92),(1,92,92),(0,17,129),(0,0,0),(4,22,128),(2,5,130),(0,0,0),(0,0,0),(0,6,130),(0,59,116),(0,57,117),(0,0,0),(3,23,128),(14,6,119),(0,0,0),(0,0,0),(2,6,130),(0,48,121),(0,61,115),(0,0,0),(3,36,125),(0,7,130),(0,0,0),(0,0,0),(3,5,130),(2,48,121),(0,77,105),(0,0,0),(7,22,127),(2,7,130),(0,0,0),(0,0,0),(0,24,128),(1,24,128),(2,77,105),(0,0,0),(0,8,130),(0,18,129),(0,0,0),(0,0,0),(2,24,128),(12,29,120),(0,29,127),(0,0,0),(2,8,130),(2,18,129),(0,0,0),(0,0,0),(0,40,124),(1,40,124),(0,43,123),(0,0,0),(4,4,130),(0,9,130),(0,0,0),(0,0,0),(2,40,124),(4,36,125),(2,43,123),(0,0,0),(7,2,129),(2,9,130),(0,0,0),(0,0,0),(3,18,129),(0,73,108),(0,37,125),(0,0,0),(8,10,128),(3,29,127),(0,0,0),(0,0,0)]

def wits_17 : List (ℕ × ℕ × ℕ) := [(0,10,130),(0,51,120),(0,19,129),(0,0,0),(7,50,119),(3,43,123),(0,0,0),(0,0,0),(2,10,130),(0,25,128),(1,25,128),(0,0,0),(0,76,106),(1,76,106),(0,0,0),(0,0,0),(7,17,128),(2,25,128),(4,77,105),(0,0,0),(2,76,106),(0,11,130),(0,0,0),(0,0,0),(4,24,128),(5,0,130),(0,85,99),(0,0,0),(3,51,120),(0,30,127),(0,0,0),(0,0,0),(0,34,126),(0,67,112),(1,67,112),(0,0,0),(3,25,128),(2,30,127),(0,0,0),(0,0,0),(2,34,126),(0,20,129),(0,49,121),(0,0,0),(0,12,130),(1,12,130),(0,0,0),(0,0,0),(3,11,130),(2,20,129),(2,49,121),(0,0,0),(2,12,130),(0,58,117),(0,0,0),(0,0,0),(0,60,116),(0,41,124),(1,41,124),(0,0,0),(0,26,128),(1,26,128),(0,0,0),(0,0,0),(2,60,116),(0,44,123),(1,44,123),(0,0,0),(2,26,128),(0,13,130),(0,0,0),(0,0,0),(7,40,123),(2,44,123),(0,75,107),(0,0,0),(4,76,106),(0,54,119),(0,0,0),(0,0,0),(3,58,117),(6,52,119),(0,21,129),(0,0,0),(3,41,124),(2,54,119),(0,0,0),(0,0,0),(7,19,128),(5,8,130),(0,31,127),(0,0,0),(0,64,114),(0,47,122),(0,0,0),(0,0,0),(0,14,130),(1,14,130),(2,31,127),(0,0,0),(2,64,114),(0,35,126),(0,0,0),(0,0,0),(0,52,120),(1,52,120),(4,49,121),(0,0,0),(4,12,130),(0,78,105),(0,0,0),(0,0,0),(2,52,120),(0,27,128),(1,27,128),(0,0,0),(6,0,130),(0,91,94),(0,0,0),(0,0,0),(3,47,122),(2,27,128),(9,3,128),(0,0,0),(4,26,128),(0,15,130),(0,0,0),(0,0,0),(0,82,102),(1,82,102),(10,1,127),(0,0,0),(6,4,130),(2,15,130),(0,0,0),(0,0,0),(2,82,102),(0,89,96),(1,89,96),(0,0,0),(0,42,124),(0,50,121),(0,0,0),(0,0,0),(3,91,94),(2,89,96),(0,39,125),(0,0,0),(2,42,124),(2,50,121),(0,0,0),(0,0,0),(3,15,130),(0,32,127),(0,45,123),(0,0,0),(0,16,130),(1,16,130),(0,0,0),(0,0,0),(4,14,130),(0,0,131),(0,1,131),(0,0,0),(2,16,130),(0,2,131),(0,0,0),(0,0,0),(0,28,128),(1,28,128),(0,3,131),(0,0,0),(0,36,126),(0,57,118),(0,0,0),(0,0,0),(2,28,128),(0,4,131),(1,4,131),(0,0,0),(2,36,126),(2,57,118),(0,0,0),(0,0,0),(8,36,124),(2,4,131),(0,5,131),(0,0,0),(0,48,122),(0,17,130),(0,0,0),(0,0,0),(3,2,131),(7,35,125),(0,63,115),(0,0,0),(2,48,122),(0,6,131),(0,0,0),(0,0,0),(3,57,118),(4,89,96),(2,63,115),(0,0,0),(3,4,131),(2,6,131),(0,0,0),(0,0,0),(7,52,119),(0,53,120),(0,7,131),(0,0,0),(11,16,125),(3,5,131),(0,0,0),(0,0,0),(0,80,104),(0,24,129),(0,33,127),(0,0,0),(4,16,130),(0,65,114),(0,0,0),(0,0,0),(0,18,130),(0,8,131),(1,8,131),(0,0,0),(6,76,106),(2,65,114),(0,0,0),(0,0,0),(2,18,130),(2,8,131),(4,3,131),(0,0,0),(3,53,120),(3,7,131),(0,0,0),(0,0,0),(7,16,129),(4,4,131),(0,9,131),(0,0,0),(3,24,129),(0,37,126),(0,0,0),(0,0,0),(3,65,114),(6,67,112),(2,9,131),(0,0,0),(3,8,131),(2,37,126),(0,0,0),(0,0,0),(7,23,128),(0,84,101),(0,67,113),(0,0,0),(6,12,130),(0,10,131),(0,0,0),(0,0,0),(7,36,125),(2,84,101),(0,25,129),(0,0,0),(7,5,130),(2,10,131),(0,0,0),(0,0,0),(3,37,126),(4,53,120),(2,25,129),(0,0,0),(6,26,128),(10,46,119),(0,0,0),(0,0,0),(4,80,104),(4,24,129),(0,11,131),(0,0,0),(0,30,128),(0,34,127),(0,0,0),(0,0,0),(0,58,118),(0,60,117),(1,60,117),(0,0,0),(2,30,128),(0,83,102),(0,0,0),(0,0,0),(2,58,118),(0,56,119),(0,93,93),(0,0,0),(0,20,130),(1,20,130),(0,0,0),(0,0,0),(11,33,122),(0,12,131),(0,41,125),(0,0,0),(2,20,130),(3,11,131),(0,0,0),(0,0,0),(0,44,124),(1,44,124),(2,41,125),(0,0,0),(0,54,120),(0,26,129),(0,0,0),(0,0,0),(0,38,126),(0,64,115),(1,64,115),(0,0,0),(2,54,120),(2,26,129),(0,0,0),(0,0,0),(2,38,126),(2,64,115),(0,13,131),(0,0,0),(3,12,131),(0,82,103),(0,0,0),(0,0,0),(7,73,108),(7,37,125),(0,47,123),(0,0,0),(14,14,120),(0,21,130),(0,0,0),(0,0,0),(3,26,129),(0,31,128),(1,31,128),(0,0,0),(0,88,98),(1,88,98),(0,0,0),(0,0,0),(0,66,114),(1,66,114),(0,35,127),(0,0,0),(2,88,98),(0,14,131),(0,0,0),(0,0,0),(2,66,114),(4,56,119),(0,71,111),(0,0,0),(4,20,130),(2,14,131),(0,0,0),(0,0,0),(3,21,130),(4,12,131),(0,27,129),(0,0,0),(3,31,128),(8,69,110),(0,0,0),(0,0,0),(4,44,124),(0,81,104),(0,77,107),(0,0,0),(4,54,120),(3,35,127),(0,0,0),(0,0,0),(0,22,130),(1,22,130),(0,15,131),(0,0,0),(6,36,126),(0,42,125),(0,0,0),(0,0,0),(2,22,130),(0,68,113),(1,68,113),(0,0,0),(0,86,100),(0,39,126),(0,0,0),(0,0,0),(7,41,124),(0,45,124),(1,45,124),(0,0,0),(2,86,100),(0,59,118),(0,0,0),(0,0,0),(0,32,128),(1,32,128),(0,57,119),(0,0,0),(4,88,98),(2,59,118),(0,0,0),(0,0,0),(2,32,128),(0,16,131),(1,16,131),(0,0,0),(3,68,113),(4,14,131),(0,0,0),(0,0,0),(0,0,132),(0,1,132),(0,85,101),(0,0,0),(0,2,132),(0,23,130),(0,0,0),(0,0,0),(2,0,132),(0,3,132),(1,3,132),(0,0,0),(2,2,132),(2,23,130),(0,0,0),(0,0,0),(0,4,132),(1,4,132),(4,77,107),(0,0,0),(0,70,112),(1,70,112),(0,0,0),(0,0,0),(2,4,132),(0,5,132),(0,17,131),(0,0,0),(2,70,112),(3,85,101),(0,0,0),(0,0,0),(3,23,130),(2,5,132),(2,17,131),(0,0,0),(0,6,132),(1,6,132),(0,0,0),(0,0,0),(11,2,127),(4,45,124),(5,21,130),(0,0,0),(2,6,132),(4,59,118),(0,0,0),(0,0,0),(4,32,128),(0,7,132),(0,43,125),(0,0,0),(0,24,130),(0,79,106),(0,0,0),(0,0,0),(7,89,96),(2,7,132),(0,29,129),(0,0,0),(2,24,130),(0,18,131),(0,0,0),(0,0,0),(0,8,132),(0,92,95),(1,92,95),(0,0,0),(0,46,124),(1,46,124),(0,0,0),(0,0,0),(2,8,132),(0,91,96),(0,37,127),(0,0,0),(2,46,124),(3,43,125),(0,0,0),(0,0,0),(3,79,106),(0,9,132),(0,75,109),(0,0,0),(4,70,112),(0,90,97),(0,0,0),(0,0,0),(3,18,131),(2,9,132),(2,75,109),(0,0,0),(3,92,95),(2,90,97),(0,0,0),(0,0,0),(7,4,131),(5,86,100),(0,19,131),(0,0,0),(0,10,132),(0,25,130),(0,0,0),(0,0,0),(6,44,124),(7,5,131),(0,49,123),(0,0,0),(2,10,132),(0,62,117),(0,0,0),(0,0,0),(0,56,120),(1,56,120),(2,49,123),(0,0,0),(0,34,128),(0,30,129),(0,0,0),(0,0,0),(2,56,120),(0,11,132),(1,11,132),(0,0,0),(2,34,128),(2,30,129),(0,0,0),(0,0,0),(0,64,116),(1,64,116),(5,23,130),(0,0,0),(4,46,124),(0,41,126),(0,0,0),(0,0,0),(2,64,116),(0,20,131),(1,20,131),(0,0,0),(6,88,98),(2,41,126),(0,0,0),(0,0,0),(0,12,132),(0,87,100),(1,87,100),(0,0,0),(3,11,132),(0,38,127),(0,0,0),(0,0,0),(0,26,130),(1,26,130),(6,71,111),(0,0,0),(10,14,128),(0,66,115),(0,0,0),(0,0,0),(2,26,130),(0,47,124),(0,81,105),(0,0,0),(0,52,122),(1,52,122),(0,0,0),(0,0,0),(10,56,116),(0,13,132),(1,13,132),(0,0,0),(2,52,122),(0,86,101),(0,0,0),(0,0,0),(3,38,127),(2,13,132),(0,21,131),(0,0,0),(4,34,128),(2,86,101),(0,0,0),(0,0,0),(3,66,115),(0,35,128),(1,35,128),(0,0,0),(3,47,124),(3,81,105),(0,0,0),(0,0,0),(4,64,116),(2,35,128),(9,83,100),(0,0,0),(0,14,132),(1,14,132),(0,0,0),(0,0,0),(3,86,101),(4,20,131),(6,57,119),(0,0,0),(2,14,132),(0,27,130),(0,0,0),(0,0,0),(4,12,132),(4,87,100),(5,90,97),(0,0,0),(0,80,106),(1,80,106),(0,0,0),(0,0,0),(0,42,126),(1,42,126),(0,59,119),(0,0,0),(2,80,106),(0,22,131),(0,0,0),(0,0,0),(2,42,126),(0,15,132),(0,39,127),(0,0,0),(4,52,122),(2,22,131),(0,0,0),(0,0,0),(3,27,130),(0,76,109),(0,63,117),(0,0,0),(6,70,112),(4,86,101),(0,0,0),(0,0,0),(7,64,115),(0,32,129),(0,55,121),(0,0,0),(8,16,130),(0,70,113),(0,0,0),(0,0,0),(0,94,94),(1,94,94),(0,93,95),(0,0,0),(3,15,132),(2,70,113),(0,0,0),(0,0,0),(0,16,132),(0,65,116),(1,65,116),(0,0,0),(0,28,130),(1,28,130),(0,0,0),(0,0,0),(2,16,132),(0,0,133),(0,1,133),(0,0,0),(2,28,130),(0,2,133),(0,0,0),(0,0,0),(3,70,113),(2,0,133),(0,3,133),(0,0,0),(4,80,106),(2,2,133),(0,0,0),(0,0,0),(0,90,98),(0,4,133),(1,4,133),(0,0,0),(3,65,116),(4,22,131),(0,0,0),(0,0,0),(2,90,98),(0,17,132),(0,5,133),(0,0,0),(3,0,133),(3,1,133),(0,0,0),(0,0,0),(3,2,133),(2,17,132),(0,89,99),(0,0,0),(10,68,110),(0,6,133),(0,0,0),(0,0,0),(0,72,112),(0,40,127),(0,33,129),(0,0,0),(3,4,133),(2,6,133),(0,0,0),(0,0,0),(2,72,112),(0,24,131),(0,7,133),(0,0,0),(3,17,132),(0,29,130),(0,0,0),(0,0,0),(0,88,100),(1,88,100),(2,7,133),(0,0,0),(0,18,132),(0,82,105),(0,0,0),(0,0,0),(2,88,100),(0,8,133),(1,8,133),(0,0,0),(2,18,132),(0,69,114),(0,0,0),(0,0,0),(7,16,131),(0,60,119),(1,60,119),(0,0,0),(0,58,120),(1,58,120),(0,0,0),(0,0,0),(0,62,118),(1,62,118),(0,9,133),(0,0,0),(2,58,120),(6,41,126),(0,0,0),(0,0,0),(2,62,118),(0,49,124),(1,49,124),(0,0,0),(3,8,133),(10,34,125),(0,0,0),(0,0,0),(3,69,114),(0,19,132),(0,25,131),(0,0,0),(3,60,119),(0,10,133),(0,0,0),(0,0,0),(4,72,112),(2,19,132),(2,25,131),(0,0,0),(8,30,128),(0,34,129),(0,0,0),(0,0,0),(0,30,130),(1,30,130),(4,7,133),(0,0,0),(3,49,124),(2,34,129),(0,0,0),(0,0,0),(2,30,130),(5,28,130),(0,11,133),(0,0,0),(0,44,126),(1,44,126),(0,0,0),(0,0,0),(3,10,133),(4,8,133),(2,11,133),(0,0,0),(2,44,126),(4,69,114),(0,0,0),(0,0,0),(0,20,132),(1,20,132),(13,2,125),(0,0,0),(0,38,128),(1,38,128),(0,0,0),(0,0,0),(2,20,132),(0,12,133),(0,47,125),(0,0,0),(2,38,128),(0,26,131),(0,0,0),(0,0,0),(7,91,96),(2,12,133),(2,47,125),(0,0,0),(11,63,112),(2,26,131),(0,0,0),(0,0,0),(7,9,132),(0,68,115),(1,68,115),(0,0,0),(6,80,106),(4,10,133),(0,0,0),(0,0,0),(6,42,126),(2,68,115),(0,13,133),(0,0,0),(3,12,133),(0,31,130),(0,0,0),(0,0,0),(3,26,131),(0,21,132),(0,35,129),(0,0,0),(7,25,130),(2,31,130),(0,0,0),(0,0,0),(0,84,104),(0,73,112),(1,73,112),(0,0,0),(0,50,124),(1,50,124),(0,0,0),(0,0,0),(2,84,104),(0,59,120),(0,61,119),(0,0,0),(2,50,124),(0,14,133),(0,0,0),(0,0,0),(3,31,130),(2,59,120),(0,27,131),(0,0,0),(3,21,132),(0,42,127),(0,0,0),(0,0,0),(0,70,114),(1,70,114),(2,27,131),(0,0,0),(3,73,112),(0,45,126),(0,0,0),(0,0,0),(2,70,114),(0,39,128),(1,39,128),(0,0,0),(0,22,132),(0,55,122),(0,0,0),(0,0,0),(3,14,133),(2,39,128),(0,15,133),(0,0,0),(2,22,132),(2,55,122),(0,0,0),(0,0,0),(3,42,127),(0,89,100),(1,89,100),(0,0,0),(0,32,130),(1,32,130),(0,0,0),(0,0,0),(3,45,126),(0,48,125),(1,48,125),(0,0,0),(2,32,130),(16,29,114),(0,0,0),(0,0,0),(3,55,122),(0,36,129),(0,53,123),(0,0,0),(4,50,124),(3,15,133),(0,0,0),(0,0,0),(6,72,112),(0,16,133),(0,75,111),(0,0,0),(3,89,100),(4,14,133),(0,0,0),(0,0,0),(7,35,128),(0,23,132),(1,23,132),(0,0,0),(0,0,134),(0,1,134),(0,0,0),(0,0,0),(0,2,134),(1,2,134),(5,26,131),(0,0,0),(2,0,134),(0,3,134),(0,0,0),(0,0,0),(2,2,134),(4,39,128),(10,29,127),(0,0,0),(0,4,134),(0,87,102),(0,0,0),(0,0,0),(10,40,124),(0,51,124),(0,17,133),(0,0,0),(2,4,134),(0,5,134),(0,0,0),(0,0,0),(0,40,128),(1,40,128),(0,69,115),(0,0,0),(4,32,130),(0,33,130),(0,0,0),(0,0,0),(0,6,134),(1,6,134),(2,69,115),(0,0,0),(15,85,86),(2,33,130),(0,0,0),(0,0,0)]

def wits_18 : List (ℕ × ℕ × ℕ) := [(0,24,132),(1,24,132),(0,29,131),(0,0,0),(3,51,124),(0,7,134),(0,0,0),(0,0,0),(2,24,132),(4,16,133),(0,37,129),(0,0,0),(7,70,113),(0,18,133),(0,0,0),(0,0,0),(3,33,130),(4,23,132),(2,37,129),(0,0,0),(0,8,134),(1,8,134),(0,0,0),(0,0,0),(4,2,134),(15,3,121),(0,49,125),(0,0,0),(2,8,134),(0,77,110),(0,0,0),(0,0,0),(3,7,134),(5,22,132),(2,49,125),(0,0,0),(4,4,134),(0,9,134),(0,0,0),(0,0,0),(3,18,133),(0,85,104),(1,85,104),(0,0,0),(6,38,128),(0,54,123),(0,0,0),(0,0,0),(4,40,128),(0,25,132),(0,19,133),(0,0,0),(0,94,96),(1,94,96),(0,0,0),(0,0,0),(0,10,134),(1,10,134),(0,93,97),(0,0,0),(2,94,96),(0,30,131),(0,0,0),(0,0,0),(0,80,108),(0,41,128),(1,41,128),(0,0,0),(0,92,98),(1,92,98),(0,0,0),(0,0,0),(2,80,108),(2,41,128),(4,37,129),(0,0,0),(2,92,98),(0,11,134),(0,0,0),(0,0,0),(0,52,124),(0,84,105),(0,91,99),(0,0,0),(4,8,134),(0,38,129),(0,0,0),(0,0,0),(2,52,124),(0,20,133),(1,20,133),(0,0,0),(3,41,128),(2,38,129),(0,0,0),(0,0,0),(7,8,133),(0,76,111),(0,73,113),(0,0,0),(0,12,134),(1,12,134),(0,0,0),(0,0,0),(3,11,134),(2,76,111),(2,73,113),(0,0,0),(2,12,134),(3,91,99),(0,0,0),(0,0,0),(3,38,129),(4,25,132),(4,19,133),(0,0,0),(3,20,133),(5,6,134),(0,0,0),(0,0,0),(4,10,134),(0,61,120),(0,31,131),(0,0,0),(3,76,111),(0,13,134),(0,0,0),(0,0,0),(4,80,108),(2,61,120),(0,21,133),(0,0,0),(4,92,98),(0,57,122),(0,0,0),(0,0,0),(11,26,127),(6,89,100),(2,21,133),(0,0,0),(6,32,130),(2,57,122),(0,0,0),(0,0,0),(4,52,124),(4,84,105),(4,91,99),(0,0,0),(0,42,128),(0,65,118),(0,0,0),(0,0,0),(0,14,134),(0,27,132),(0,45,127),(0,0,0),(2,42,128),(2,65,118),(0,0,0),(0,0,0),(2,14,134),(2,27,132),(0,39,129),(0,0,0),(4,12,134),(10,2,131),(0,0,0),(0,0,0),(10,28,128),(0,75,112),(1,75,112),(0,0,0),(6,0,134),(0,22,133),(0,0,0),(0,0,0),(3,65,118),(2,75,112),(0,67,117),(0,0,0),(0,48,126),(0,15,134),(0,0,0),(0,0,0),(0,78,110),(0,32,131),(1,32,131),(0,0,0),(2,48,126),(2,15,134),(0,0,0),(0,0,0),(2,78,110),(2,32,131),(4,21,133),(0,0,0),(0,36,130),(1,36,130),(0,0,0),(0,0,0),(3,22,133),(7,13,133),(5,11,134),(0,0,0),(2,36,130),(3,67,117),(0,0,0),(0,0,0),(0,28,132),(1,28,132),(5,38,129),(0,0,0),(0,16,134),(1,16,134),(0,0,0),(0,0,0),(2,28,132),(0,69,116),(0,23,133),(0,0,0),(2,16,134),(6,7,134),(0,0,0),(0,0,0),(7,59,120),(0,0,135),(0,1,135),(0,0,0),(7,14,133),(0,2,135),(0,0,0),(0,0,0),(11,1,130),(0,43,128),(0,3,135),(0,0,0),(6,8,134),(2,2,135),(0,0,0),(0,0,0),(8,72,112),(0,4,135),(1,4,135),(0,0,0),(0,62,120),(0,17,134),(0,0,0),(0,0,0),(0,58,122),(1,58,122),(0,5,135),(0,0,0),(2,62,120),(0,93,98),(0,0,0),(0,0,0),(2,58,122),(0,64,119),(1,64,119),(0,0,0),(3,43,128),(0,6,135),(0,0,0),(0,0,0),(7,89,100),(0,24,133),(0,71,115),(0,0,0),(3,4,135),(0,37,130),(0,0,0),(0,0,0),(3,17,134),(2,24,133),(0,7,135),(0,0,0),(4,16,134),(0,49,126),(0,0,0),(0,0,0),(0,18,134),(0,80,109),(1,80,109),(0,0,0),(3,64,119),(2,49,126),(0,0,0),(0,0,0),(2,18,134),(0,8,135),(1,8,135),(0,0,0),(0,54,124),(1,54,124),(0,0,0),(0,0,0),(3,37,130),(2,8,135),(4,3,135),(0,0,0),(2,54,124),(0,90,101),(0,0,0),(0,0,0),(3,49,126),(4,4,135),(0,9,135),(0,0,0),(3,80,109),(2,90,101),(0,0,0),(0,0,0),(4,58,122),(0,68,117),(0,25,133),(0,0,0),(3,8,135),(0,19,134),(0,0,0),(0,0,0),(0,44,128),(1,44,128),(0,41,129),(0,0,0),(0,30,132),(0,10,135),(0,0,0),(0,0,0),(2,44,128),(0,52,125),(1,52,125),(0,0,0),(2,30,132),(2,10,135),(0,0,0),(0,0,0),(8,20,132),(2,52,125),(0,47,127),(0,0,0),(3,68,117),(0,79,110),(0,0,0),(0,0,0),(0,38,130),(1,38,130),(0,11,135),(0,0,0),(7,7,134),(2,79,110),(0,0,0),(0,0,0),(2,38,130),(0,88,103),(1,88,103),(0,0,0),(0,20,134),(1,20,134),(0,0,0),(0,0,0),(11,30,127),(2,88,103),(0,61,121),(0,0,0),(2,20,134),(0,26,133),(0,0,0),(0,0,0),(3,79,110),(0,12,135),(1,12,135),(0,0,0),(7,77,110),(2,26,133),(0,0,0),(0,0,0),(0,50,126),(1,50,126),(0,57,123),(0,0,0),(3,88,103),(4,19,134),(0,0,0),(0,0,0),(2,50,126),(0,31,132),(0,35,131),(0,0,0),(0,82,108),(1,82,108),(0,0,0),(0,0,0),(3,26,133),(2,31,132),(0,13,135),(0,0,0),(2,82,108),(0,21,134),(0,0,0),(0,0,0),(6,78,110),(0,55,124),(1,55,124),(0,0,0),(7,30,131),(0,42,129),(0,0,0),(0,0,0),(4,38,130),(0,45,128),(1,45,128),(0,0,0),(3,31,132),(0,67,118),(0,0,0),(0,0,0),(15,20,121),(2,45,128),(0,27,133),(0,0,0),(4,20,134),(0,14,135),(0,0,0),(0,0,0),(3,21,134),(7,91,99),(2,27,133),(0,0,0),(3,55,124),(2,14,135),(0,0,0),(0,0,0),(0,96,96),(0,48,127),(0,53,125),(0,0,0),(3,45,128),(16,79,90),(0,0,0),(0,0,0),(0,22,134),(1,22,134),(0,81,109),(0,0,0),(10,70,112),(3,27,133),(0,0,0),(0,0,0),(0,32,132),(1,32,132),(0,15,135),(0,0,0),(4,82,108),(16,14,119),(0,0,0),(0,0,0),(2,32,132),(0,36,131),(1,36,131),(0,0,0),(3,48,127),(0,85,106),(0,0,0),(0,0,0),(0,92,100),(1,92,100),(5,79,110),(0,0,0),(7,13,134),(2,85,106),(0,0,0),(0,0,0),(0,74,114),(0,28,133),(1,28,133),(0,0,0),(7,57,122),(0,51,126),(0,0,0),(0,0,0),(2,74,114),(0,16,135),(0,91,101),(0,0,0),(0,60,122),(0,23,134),(0,0,0),(0,0,0),(3,85,106),(2,16,135),(0,43,129),(0,0,0),(2,60,122),(0,58,123),(0,0,0),(0,0,0),(0,0,136),(0,1,136),(1,1,136),(0,0,0),(0,2,136),(1,2,136),(0,0,0),(0,0,0),(0,90,102),(0,3,136),(1,3,136),(0,0,0),(2,2,136),(3,91,101),(0,0,0),(0,0,0),(0,4,136),(0,33,132),(0,17,135),(0,0,0),(7,22,133),(0,66,119),(0,0,0),(0,0,0),(2,4,136),(0,5,136),(1,5,136),(0,0,0),(3,1,136),(2,66,119),(0,0,0),(0,0,0),(4,92,100),(2,5,136),(0,29,133),(0,0,0),(0,6,136),(1,6,136),(0,0,0),(0,0,0),(4,74,114),(4,28,133),(2,29,133),(0,0,0),(2,6,136),(0,54,125),(0,0,0),(0,0,0),(3,66,119),(0,7,136),(1,7,136),(0,0,0),(0,68,118),(0,18,135),(0,0,0),(0,0,0),(10,64,116),(0,83,108),(0,73,115),(0,0,0),(2,68,118),(2,18,135),(0,0,0),(0,0,0),(0,8,136),(1,8,136),(0,79,111),(0,0,0),(4,2,136),(5,22,134),(0,0,0),(0,0,0),(2,8,136),(4,3,136),(2,79,111),(0,0,0),(3,7,136),(5,32,132),(0,0,0),(0,0,0),(3,18,135),(0,9,136),(1,9,136),(0,0,0),(0,34,132),(0,25,134),(0,0,0),(0,0,0),(7,4,135),(2,9,136),(0,19,135),(0,0,0),(2,34,132),(0,30,133),(0,0,0),(0,0,0),(6,50,126),(0,47,128),(0,87,105),(0,0,0),(0,10,136),(1,10,136),(0,0,0),(0,0,0),(7,64,119),(2,47,128),(2,87,105),(0,0,0),(2,10,136),(0,38,131),(0,0,0),(0,0,0),(3,25,134),(4,7,136),(0,59,123),(0,0,0),(4,68,118),(2,38,131),(0,0,0),(0,0,0),(3,30,133),(0,11,136),(1,11,136),(0,0,0),(3,47,128),(0,75,114),(0,0,0),(0,0,0),(4,8,136),(0,20,135),(1,20,135),(0,0,0),(0,78,112),(0,50,127),(0,0,0),(0,0,0),(0,26,134),(1,26,134),(6,27,133),(0,0,0),(2,78,112),(0,94,99),(0,0,0),(0,0,0),(0,12,136),(1,12,136),(5,66,119),(0,0,0),(3,11,136),(2,94,99),(0,0,0),(0,0,0),(2,12,136),(0,35,132),(0,31,133),(0,0,0),(3,20,135),(4,30,133),(0,0,0),(0,0,0),(3,50,127),(2,35,132),(2,31,133),(0,0,0),(4,10,136),(0,81,110),(0,0,0),(0,0,0),(0,42,130),(0,13,136),(0,21,135),(0,0,0),(7,10,135),(2,81,110),(0,0,0),(0,0,0),(2,42,130),(2,13,136),(0,85,107),(0,0,0),(3,35,132),(3,31,133),(0,0,0),(0,0,0),(6,92,100),(4,11,136),(0,39,131),(0,0,0),(7,79,110),(0,27,134),(0,0,0),(0,0,0),(0,48,128),(1,48,128),(2,39,131),(0,0,0),(0,14,136),(1,14,136),(0,0,0),(0,0,0),(2,48,128),(6,16,135),(0,77,113),(0,0,0),(2,14,136),(0,74,115),(0,0,0),(0,0,0),(4,12,136),(5,34,132),(2,77,113),(0,0,0),(7,26,133),(0,22,135),(0,0,0),(0,0,0),(3,27,134),(0,32,133),(1,32,133),(0,0,0),(6,2,136),(2,22,135),(0,0,0),(0,0,0),(0,36,132),(0,15,136),(1,15,136),(0,0,0),(8,16,134),(3,77,113),(0,0,0),(0,0,0),(0,62,122),(0,60,123),(0,51,127),(0,0,0),(11,45,124),(6,66,119),(0,0,0),(0,0,0),(2,62,122),(0,64,121),(1,64,121),(0,0,0),(0,28,134),(1,28,134),(0,0,0),(0,0,0),(7,55,124),(2,64,121),(4,39,131),(0,0,0),(2,28,134),(0,43,130),(0,0,0),(0,0,0),(0,16,136),(1,16,136),(0,23,135),(0,0,0),(0,66,120),(0,46,129),(0,0,0),(0,0,0),(2,16,136),(0,40,131),(1,40,131),(0,0,0),(2,66,120),(2,46,129),(0,0,0),(0,0,0),(10,62,118),(0,0,137),(0,1,137),(0,0,0),(0,76,114),(0,2,137),(0,0,0),(0,0,0),(3,43,130),(2,0,137),(0,3,137),(0,0,0),(2,76,114),(2,2,137),(0,0,0),(0,0,0),(3,46,129),(0,4,137),(1,4,137),(0,0,0),(3,40,131),(5,42,130),(0,0,0),(0,0,0),(0,54,126),(0,37,132),(0,5,137),(0,0,0),(3,0,137),(0,29,134),(0,0,0),(0,0,0),(2,54,126),(0,24,135),(1,24,135),(0,0,0),(4,28,134),(0,6,137),(0,0,0),(0,0,0),(11,79,106),(2,24,135),(5,27,134),(0,0,0),(3,4,137),(2,6,137),(0,0,0),(0,0,0),(4,16,136),(5,14,136),(0,7,137),(0,0,0),(0,18,136),(1,18,136),(0,0,0),(0,0,0),(0,70,118),(1,70,118),(0,95,99),(0,0,0),(2,18,136),(8,19,134),(0,0,0),(0,0,0),(2,70,118),(0,8,137),(1,8,137),(0,0,0),(0,44,130),(1,44,130),(0,0,0),(0,0,0),(7,1,136),(2,8,137),(0,41,131),(0,0,0),(2,44,130),(0,34,133),(0,0,0),(0,0,0),(6,26,134),(4,4,137),(0,9,137),(0,0,0),(20,6,104),(0,63,122),(0,0,0),(0,0,0),(0,30,134),(0,19,136),(1,19,136),(0,0,0),(3,8,137),(2,63,122),(0,0,0),(0,0,0),(2,30,134),(2,19,136),(0,65,121),(0,0,0),(0,38,132),(0,10,137),(0,0,0),(0,0,0),(3,34,133),(0,72,117),(0,57,125),(0,0,0),(2,38,132),(2,10,137),(0,0,0),(0,0,0),(3,63,122),(2,72,117),(0,81,111),(0,0,0),(0,50,128),(1,50,128),(0,0,0),(0,0,0),(4,70,118),(0,67,120),(0,11,137),(0,0,0),(2,50,128),(3,65,121),(0,0,0),(0,0,0),(0,20,136),(1,20,136),(2,11,137),(0,0,0),(3,72,117),(0,26,135),(0,0,0),(0,0,0),(2,20,136),(7,79,111),(4,41,131),(0,0,0),(6,14,136),(2,26,135),(0,0,0),(0,0,0),(11,66,115),(0,12,137),(0,35,133),(0,0,0),(0,90,104),(0,31,134),(0,0,0),(0,0,0),(4,30,134),(2,12,137),(0,69,119),(0,0,0),(2,90,104),(0,42,131),(0,0,0),(0,0,0),(3,26,135),(6,32,133),(2,69,119),(0,0,0),(0,74,116),(1,74,116),(0,0,0),(0,0,0),(6,36,132),(0,21,136),(0,13,137),(0,0,0),(2,74,116),(3,35,133),(0,0,0),(0,0,0),(0,80,112),(0,39,132),(0,89,105),(0,0,0),(4,50,128),(3,69,119),(0,0,0),(0,0,0),(2,80,112),(2,39,132),(0,27,135),(0,0,0),(6,28,134),(10,1,134),(0,0,0),(0,0,0),(4,20,136),(5,44,130),(2,27,135),(0,0,0),(3,21,136),(0,14,137),(0,0,0),(0,0,0),(6,16,136),(8,36,131),(5,34,133),(0,0,0),(3,39,132),(0,62,123),(0,0,0),(0,0,0),(0,60,124),(1,60,124),(4,35,133),(0,0,0),(0,22,136),(1,22,136),(0,0,0),(0,0,0),(2,60,124),(0,36,133),(1,36,133),(0,0,0),(2,22,136),(0,58,125),(0,0,0),(0,0,0),(3,14,137),(2,36,133),(0,15,137),(0,0,0),(4,74,116),(0,66,121),(0,0,0),(0,0,0)]

def wits_19 : List (ℕ × ℕ × ℕ) := [(3,62,123),(0,76,115),(1,76,115),(0,0,0),(7,81,110),(2,66,121),(0,0,0),(0,0,0),(4,80,112),(0,28,135),(0,43,131),(0,0,0),(0,56,126),(0,97,98),(0,0,0),(0,0,0),(0,46,130),(0,96,99),(0,73,117),(0,0,0),(2,56,126),(2,97,98),(0,0,0),(0,0,0),(0,40,132),(0,16,137),(1,16,137),(0,0,0),(3,76,115),(4,14,137),(0,0,0),(0,0,0),(2,40,132),(2,16,137),(6,7,137),(0,0,0),(3,28,135),(0,94,101),(0,0,0),(0,0,0),(3,97,98),(5,90,104),(0,49,129),(0,0,0),(0,0,138),(0,1,138),(0,0,0),(0,0,0),(0,2,138),(1,2,138),(2,49,129),(0,0,0),(2,0,138),(0,3,138),(0,0,0),(0,0,0),(2,2,138),(5,74,116),(0,17,137),(0,0,0),(0,4,138),(0,70,119),(0,0,0),(0,0,0),(3,94,101),(4,76,115),(0,29,135),(0,0,0),(2,4,138),(0,5,138),(0,0,0),(0,0,0),(0,24,136),(0,92,103),(1,92,103),(0,0,0),(4,56,126),(2,5,138),(0,0,0),(0,0,0),(0,6,138),(0,75,116),(1,75,116),(0,0,0),(6,38,132),(3,17,137),(0,0,0),(0,0,0),(0,52,128),(1,52,128),(5,14,137),(0,0,0),(7,43,130),(0,7,138),(0,0,0),(0,0,0),(2,52,128),(0,44,131),(0,63,123),(0,0,0),(3,92,103),(2,7,138),(0,0,0),(0,0,0),(7,40,131),(0,41,132),(0,59,125),(0,0,0),(0,8,138),(0,47,130),(0,0,0),(0,0,0),(0,34,134),(1,34,134),(2,59,125),(0,0,0),(2,8,138),(2,47,130),(0,0,0),(0,0,0),(2,34,134),(0,25,136),(1,25,136),(0,0,0),(3,44,131),(0,9,138),(0,0,0),(0,0,0),(7,4,137),(2,25,136),(0,19,137),(0,0,0),(3,41,132),(0,38,133),(0,0,0),(0,0,0),(3,47,130),(4,92,103),(2,19,137),(0,0,0),(7,29,134),(0,50,129),(0,0,0),(0,0,0),(0,10,138),(1,10,138),(13,7,130),(0,0,0),(3,25,136),(2,50,129),(0,0,0),(0,0,0),(2,10,138),(6,21,136),(0,55,127),(0,0,0),(0,84,110),(0,89,106),(0,0,0),(0,0,0),(3,38,133),(0,69,120),(1,69,120),(0,0,0),(2,84,110),(0,11,138),(0,0,0),(0,0,0),(3,50,129),(0,20,137),(1,20,137),(0,0,0),(0,26,136),(1,26,136),(0,0,0),(0,0,0),(4,34,134),(2,20,137),(5,3,138),(0,0,0),(2,26,136),(0,35,134),(0,0,0),(0,0,0),(3,89,106),(4,25,136),(0,31,135),(0,0,0),(0,12,138),(1,12,138),(0,0,0),(0,0,0),(3,11,138),(0,53,128),(1,53,128),(0,0,0),(2,12,138),(4,38,133),(0,0,0),(0,0,0),(7,19,136),(2,53,128),(0,71,119),(0,0,0),(0,48,130),(1,48,130),(0,0,0),(0,0,0),(0,98,98),(1,98,98),(0,21,137),(0,0,0),(2,48,130),(0,13,138),(0,0,0),(0,0,0),(0,96,100),(1,96,100),(2,21,137),(0,0,0),(0,62,124),(1,62,124),(0,0,0),(0,0,0),(2,96,100),(0,27,136),(0,95,101),(0,0,0),(2,62,124),(3,71,119),(0,0,0),(0,0,0),(0,76,116),(0,87,108),(1,87,108),(0,0,0),(4,26,136),(0,79,114),(0,0,0),(0,0,0),(0,14,138),(1,14,138),(0,51,129),(0,0,0),(7,26,135),(2,79,114),(0,0,0),(0,0,0),(2,14,138),(0,32,135),(1,32,135),(0,0,0),(0,36,134),(0,22,137),(0,0,0),(0,0,0),(7,12,137),(2,32,135),(0,93,103),(0,0,0),(2,36,134),(2,22,137),(0,0,0),(0,0,0),(3,79,114),(0,56,127),(1,56,127),(0,0,0),(0,82,112),(0,15,138),(0,0,0),(0,0,0),(4,98,98),(0,43,132),(1,43,132),(0,0,0),(2,82,112),(0,46,131),(0,0,0),(0,0,0),(0,28,136),(1,28,136),(5,89,106),(0,0,0),(4,62,124),(2,46,131),(0,0,0),(0,0,0),(2,28,136),(0,40,133),(1,40,133),(0,0,0),(3,56,127),(13,14,130),(0,0,0),(0,0,0),(3,15,138),(2,40,133),(0,23,137),(0,0,0),(0,16,138),(0,49,130),(0,0,0),(0,0,0),(3,46,131),(8,37,132),(0,91,105),(0,0,0),(2,16,138),(0,78,115),(0,0,0),(0,0,0),(11,5,134),(4,32,135),(0,33,135),(0,0,0),(3,40,133),(2,78,115),(0,0,0),(0,0,0),(10,44,128),(0,0,139),(0,1,139),(0,0,0),(6,8,138),(0,2,139),(0,0,0),(0,0,0),(3,49,130),(2,0,139),(0,3,139),(0,0,0),(4,82,112),(0,17,138),(0,0,0),(0,0,0),(0,90,106),(0,4,139),(1,4,139),(0,0,0),(7,66,121),(2,17,138),(0,0,0),(0,0,0),(2,90,106),(0,24,137),(0,5,139),(0,0,0),(3,0,139),(3,1,139),(0,0,0),(0,0,0),(3,2,139),(2,24,137),(0,65,123),(0,0,0),(7,97,98),(0,6,139),(0,0,0),(0,0,0),(0,44,132),(1,44,132),(2,65,123),(0,0,0),(3,4,139),(2,6,139),(0,0,0),(0,0,0),(0,18,138),(1,18,138),(0,7,139),(0,0,0),(3,24,137),(0,67,122),(0,0,0),(0,0,0),(2,18,138),(0,84,111),(0,57,127),(0,0,0),(7,94,101),(0,34,135),(0,0,0),(0,0,0),(3,6,139),(0,8,139),(1,8,139),(0,0,0),(6,26,136),(2,34,135),(0,0,0),(0,0,0),(11,30,131),(2,8,139),(0,25,137),(0,0,0),(0,30,136),(1,30,136),(0,0,0),(0,0,0),(0,38,134),(1,38,134),(0,9,139),(0,0,0),(2,30,136),(0,19,138),(0,0,0),(0,0,0),(0,88,108),(0,55,128),(1,55,128),(0,0,0),(3,8,139),(2,19,138),(0,0,0),(0,0,0),(2,88,108),(0,96,101),(1,96,101),(0,0,0),(6,48,130),(0,10,139),(0,0,0),(0,0,0),(4,44,132),(2,96,101),(5,49,130),(0,0,0),(8,90,104),(0,95,102),(0,0,0),(0,0,0),(3,19,138),(0,83,112),(1,83,112),(0,0,0),(3,55,128),(2,95,102),(0,0,0),(0,0,0),(7,44,131),(0,71,120),(0,11,139),(0,0,0),(0,20,138),(0,26,137),(0,0,0),(0,0,0),(3,10,139),(0,45,132),(0,35,135),(0,0,0),(2,20,138),(0,42,133),(0,0,0),(0,0,0),(3,95,102),(0,31,136),(1,31,136),(0,0,0),(3,83,112),(2,42,133),(0,0,0),(0,0,0),(4,38,134),(0,12,139),(0,79,115),(0,0,0),(3,71,120),(0,62,125),(0,0,0),(0,0,0),(0,64,124),(1,64,124),(2,79,115),(0,0,0),(0,60,126),(0,39,134),(0,0,0),(0,0,0),(2,64,124),(4,96,101),(5,6,139),(0,0,0),(2,60,126),(0,21,138),(0,0,0),(0,0,0),(8,60,124),(0,92,105),(0,13,139),(0,0,0),(3,12,139),(0,58,127),(0,0,0),(0,0,0),(0,86,110),(1,86,110),(0,27,137),(0,0,0),(7,89,106),(0,51,130),(0,0,0),(0,0,0),(2,86,110),(4,71,120),(2,27,137),(0,0,0),(0,68,122),(1,68,122),(0,0,0),(0,0,0),(3,21,138),(4,45,132),(4,35,135),(0,0,0),(2,68,122),(0,14,139),(0,0,0),(0,0,0),(0,32,136),(0,36,135),(1,36,135),(0,0,0),(7,35,134),(2,14,139),(0,0,0),(0,0,0),(0,22,138),(1,22,138),(4,79,115),(0,0,0),(10,6,136),(4,62,125),(0,0,0),(0,0,0),(2,22,138),(6,0,139),(0,43,133),(0,0,0),(0,46,132),(0,70,121),(0,0,0),(0,0,0),(3,14,139),(7,71,119),(0,15,139),(0,0,0),(2,46,132),(0,75,118),(0,0,0),(0,0,0),(6,90,106),(0,28,137),(1,28,137),(0,0,0),(0,40,134),(0,54,129),(0,0,0),(0,0,0),(4,86,110),(2,28,137),(0,49,131),(0,0,0),(2,40,134),(2,54,129),(0,0,0),(0,0,0),(3,70,121),(5,20,138),(2,49,131),(0,0,0),(4,68,122),(0,23,138),(0,0,0),(0,0,0),(3,75,118),(0,16,139),(1,16,139),(0,0,0),(3,28,137),(2,23,138),(0,0,0),(0,0,0),(0,72,120),(0,33,136),(1,33,136),(0,0,0),(11,64,119),(3,49,131),(0,0,0),(0,0,0),(2,72,120),(2,33,136),(0,37,135),(0,0,0),(7,22,137),(0,61,126),(0,0,0),(0,0,0),(0,0,140),(0,1,140),(0,99,99),(0,0,0),(0,2,140),(1,2,140),(0,0,0),(0,0,0),(2,0,140),(0,3,140),(0,17,139),(0,0,0),(2,2,140),(4,75,118),(0,0,0),(0,0,0),(0,4,140),(1,4,140),(0,67,123),(0,0,0),(0,24,138),(1,24,138),(0,0,0),(0,0,0),(2,4,140),(0,5,140),(1,5,140),(0,0,0),(2,24,138),(3,99,99),(0,0,0),(0,0,0),(7,40,133),(0,47,132),(0,95,103),(0,0,0),(0,6,140),(0,41,134),(0,0,0),(0,0,0),(10,12,136),(2,47,132),(2,95,103),(0,0,0),(2,6,140),(0,18,139),(0,0,0),(0,0,0),(4,72,120),(0,7,140),(1,7,140),(0,0,0),(0,34,136),(1,34,136),(0,0,0),(0,0,0),(8,10,138),(2,7,140),(0,83,113),(0,0,0),(2,34,136),(0,50,131),(0,0,0),(0,0,0),(0,8,140),(1,8,140),(0,55,129),(0,0,0),(4,2,140),(0,25,138),(0,0,0),(0,0,0),(2,8,140),(4,3,140),(0,93,105),(0,0,0),(3,7,140),(2,25,138),(0,0,0),(0,0,0),(4,4,140),(0,9,140),(0,19,139),(0,0,0),(4,24,138),(3,83,113),(0,0,0),(0,0,0),(3,50,131),(2,9,140),(2,19,139),(0,0,0),(6,60,126),(3,55,129),(0,0,0),(0,0,0),(3,25,138),(0,79,116),(1,79,116),(0,0,0),(0,10,140),(1,10,140),(0,0,0),(0,0,0),(14,24,128),(2,79,116),(6,13,139),(0,0,0),(2,10,140),(0,53,130),(0,0,0),(0,0,0),(6,86,110),(4,7,140),(0,45,133),(0,0,0),(4,34,136),(0,86,111),(0,0,0),(0,0,0),(0,26,138),(0,11,140),(1,11,140),(0,0,0),(3,79,116),(2,86,111),(0,0,0),(0,0,0),(0,48,132),(0,60,127),(0,31,137),(0,0,0),(0,66,124),(1,66,124),(0,0,0),(0,0,0),(2,48,132),(2,60,127),(2,31,137),(0,0,0),(2,66,124),(3,45,133),(0,0,0),(0,0,0),(0,12,140),(1,12,140),(0,39,135),(0,0,0),(0,58,128),(1,58,128),(0,0,0),(0,0,0),(2,12,140),(0,68,123),(1,68,123),(0,0,0),(2,58,128),(3,31,137),(0,0,0),(0,0,0),(7,96,101),(2,68,123),(0,21,139),(0,0,0),(0,90,108),(1,90,108),(0,0,0),(0,0,0),(15,3,128),(0,13,140),(1,13,140),(0,0,0),(2,90,108),(0,27,138),(0,0,0),(0,0,0),(7,83,112),(0,56,129),(1,56,129),(0,0,0),(3,68,123),(2,27,138),(0,0,0),(0,0,0),(0,70,122),(1,70,122),(0,75,119),(0,0,0),(7,26,137),(3,21,139),(0,0,0),(0,0,0),(0,36,136),(0,32,137),(1,32,137),(0,0,0),(0,14,140),(1,14,140),(0,0,0),(0,0,0),(2,36,136),(0,99,100),(0,89,109),(0,0,0),(2,14,140),(0,22,139),(0,0,0),(0,0,0),(4,12,140),(2,99,100),(2,89,109),(0,0,0),(4,58,128),(0,97,102),(0,0,0),(0,0,0),(0,54,130),(1,54,130),(6,99,99),(0,0,0),(3,32,137),(2,97,102),(0,0,0),(0,0,0),(2,54,130),(0,15,140),(1,15,140),(0,0,0),(0,28,138),(1,28,138),(0,0,0),(0,0,0),(3,22,139),(2,15,140),(5,53,130),(0,0,0),(2,28,138),(4,27,138),(0,0,0),(0,0,0),(3,97,102),(0,95,104),(1,95,104),(0,0,0),(0,88,110),(0,63,126),(0,0,0),(0,0,0),(4,70,122),(2,95,104),(0,23,139),(0,0,0),(2,88,110),(0,77,118),(0,0,0),(0,0,0),(0,16,140),(1,16,140),(0,33,137),(0,0,0),(4,14,140),(0,94,105),(0,0,0),(0,0,0),(2,16,140),(0,37,136),(1,37,136),(0,0,0),(3,95,104),(2,94,105),(0,0,0),(0,0,0),(3,63,126),(2,37,136),(6,83,113),(0,0,0),(0,74,120),(1,74,120),(0,0,0),(0,0,0),(3,77,118),(0,0,141),(0,1,141),(0,0,0),(2,74,120),(0,2,141),(0,0,0),(0,0,0),(3,94,105),(0,17,140),(0,3,141),(0,0,0),(0,44,134),(1,44,134),(0,0,0),(0,0,0),(7,28,137),(0,4,141),(0,47,133),(0,0,0),(2,44,134),(9,26,136),(0,0,0),(0,0,0),(15,20,127),(2,4,141),(0,5,141),(0,0,0),(3,0,141),(3,1,141),(0,0,0),(0,0,0),(3,2,141),(0,92,107),(1,92,107),(0,0,0),(3,17,140),(0,6,141),(0,0,0),(0,0,0),(4,16,140),(2,92,107),(4,33,137),(0,0,0),(0,18,140),(0,34,137),(0,0,0),(0,0,0),(7,33,136),(4,37,136),(0,7,141),(0,0,0),(2,18,140),(2,34,137),(0,0,0),(0,0,0),(6,26,138),(0,76,119),(1,76,119),(0,0,0),(0,38,136),(1,38,136),(0,0,0),(0,0,0),(0,30,138),(0,8,141),(0,25,139),(0,0,0),(2,38,136),(0,82,115),(0,0,0),(0,0,0),(2,30,138),(2,8,141),(2,25,139),(0,0,0),(4,44,134),(2,82,115),(0,0,0),(0,0,0),(6,12,140),(0,19,140),(0,9,141),(0,0,0),(3,76,119),(8,42,133),(0,0,0),(0,0,0),(7,5,140),(2,19,140),(0,53,131),(0,0,0),(0,64,126),(0,62,127),(0,0,0),(0,0,0),(3,82,115),(4,92,107),(2,53,131),(0,0,0),(2,64,126),(0,10,141),(0,0,0),(0,0,0),(0,60,128),(1,60,128),(5,94,105),(0,0,0),(3,19,140),(0,42,135),(0,0,0),(0,0,0),(2,60,128),(0,48,133),(0,35,137),(0,0,0),(11,13,136),(0,26,139),(0,0,0),(0,0,0)]

def wits_20 : List (ℕ × ℕ × ℕ) := [(0,20,140),(1,20,140),(0,11,141),(0,0,0),(4,38,136),(0,31,138),(0,0,0),(0,0,0),(0,78,118),(1,78,118),(2,11,141),(0,0,0),(6,14,140),(2,31,138),(0,0,0),(0,0,0),(2,78,118),(0,39,136),(0,97,103),(0,0,0),(3,48,133),(0,89,110),(0,0,0),(0,0,0),(3,26,139),(0,12,141),(1,12,141),(0,0,0),(14,30,128),(0,70,123),(0,0,0),(0,0,0),(0,96,104),(1,96,104),(4,53,131),(0,0,0),(0,56,130),(1,56,130),(0,0,0),(0,0,0),(2,96,104),(0,21,140),(1,21,140),(0,0,0),(2,56,130),(3,97,103),(0,0,0),(0,0,0),(3,89,110),(2,21,140),(0,13,141),(0,0,0),(0,84,114),(1,84,114),(0,0,0),(0,0,0),(3,70,123),(4,48,133),(2,13,141),(0,0,0),(2,84,114),(4,26,139),(0,0,0),(0,0,0),(4,20,140),(0,36,137),(1,36,137),(0,0,0),(0,32,138),(1,32,138),(0,0,0),(0,0,0),(0,46,134),(1,46,134),(0,43,135),(0,0,0),(2,32,138),(0,14,141),(0,0,0),(0,0,0),(2,46,134),(4,39,136),(2,43,135),(0,0,0),(0,22,140),(1,22,140),(0,0,0),(0,0,0),(10,52,128),(0,80,117),(0,49,133),(0,0,0),(2,22,140),(4,70,123),(0,0,0),(0,0,0),(0,40,136),(1,40,136),(0,63,127),(0,0,0),(4,56,130),(0,65,126),(0,0,0),(0,0,0),(2,40,136),(0,28,139),(0,15,141),(0,0,0),(6,44,134),(2,65,126),(0,0,0),(0,0,0),(7,13,140),(0,87,112),(0,67,125),(0,0,0),(3,80,117),(0,74,121),(0,0,0),(0,0,0),(7,56,129),(2,87,112),(0,59,129),(0,0,0),(11,37,132),(2,74,121),(0,0,0),(0,0,0),(0,52,132),(0,23,140),(1,23,140),(0,0,0),(3,28,139),(0,33,138),(0,0,0),(0,0,0),(2,52,132),(0,16,141),(0,37,137),(0,0,0),(3,87,112),(2,33,138),(0,0,0),(0,0,0),(3,74,121),(2,16,141),(2,37,137),(0,0,0),(4,22,140),(0,57,130),(0,0,0),(0,0,0),(14,32,128),(4,80,117),(4,49,133),(0,0,0),(3,23,140),(2,57,130),(0,0,0),(0,0,0),(3,33,138),(0,44,135),(0,29,139),(0,0,0),(0,0,142),(0,1,142),(0,0,0),(0,0,0),(0,2,142),(1,2,142),(0,17,141),(0,0,0),(2,0,142),(0,3,142),(0,0,0),(0,0,0),(0,24,140),(0,41,136),(1,41,136),(0,0,0),(0,4,142),(1,4,142),(0,0,0),(0,0,0),(2,24,140),(2,41,136),(0,55,131),(0,0,0),(2,4,142),(0,5,142),(0,0,0),(0,0,0),(3,1,142),(4,23,140),(2,55,131),(0,0,0),(7,77,118),(2,5,142),(0,0,0),(0,0,0),(0,6,142),(0,100,101),(1,100,101),(0,0,0),(3,41,136),(0,18,141),(0,0,0),(0,0,0),(2,6,142),(2,100,101),(6,35,137),(0,0,0),(8,10,140),(0,7,142),(0,0,0),(0,0,0),(3,5,142),(13,8,134),(6,11,141),(0,0,0),(10,62,124),(0,30,139),(0,0,0),(0,0,0),(6,78,118),(0,25,140),(1,25,140),(0,0,0),(0,8,142),(1,8,142),(0,0,0),(0,0,0),(0,66,126),(0,53,132),(1,53,132),(0,0,0),(2,8,142),(4,3,142),(0,0,0),(0,0,0),(2,66,126),(0,60,129),(0,19,141),(0,0,0),(4,4,142),(0,9,142),(0,0,0),(0,0,0),(3,30,139),(0,68,125),(0,45,135),(0,0,0),(3,25,140),(2,9,142),(0,0,0),(0,0,0),(7,92,107),(2,68,125),(2,45,135),(0,0,0),(0,42,136),(0,95,106),(0,0,0),(0,0,0),(0,10,142),(1,10,142),(0,75,121),(0,0,0),(2,42,136),(0,35,138),(0,0,0),(0,0,0),(2,10,142),(7,7,141),(2,75,121),(0,0,0),(0,26,140),(1,26,140),(0,0,0),(0,0,0),(7,76,119),(0,20,141),(0,31,139),(0,0,0),(2,26,140),(0,11,142),(0,0,0),(0,0,0),(0,88,112),(1,88,112),(0,39,137),(0,0,0),(4,8,142),(2,11,142),(0,0,0),(0,0,0),(2,88,112),(0,56,131),(1,56,131),(0,0,0),(6,22,140),(5,24,140),(0,0,0),(0,0,0),(7,19,140),(2,56,131),(4,19,141),(0,0,0),(0,12,142),(1,12,142),(0,0,0),(0,0,0),(3,11,142),(0,72,123),(1,72,123),(0,0,0),(2,12,142),(3,39,137),(0,0,0),(0,0,0),(11,58,125),(2,72,123),(0,21,141),(0,0,0),(0,80,118),(1,80,118),(0,0,0),(0,0,0),(4,10,142),(0,27,140),(1,27,140),(0,0,0),(2,80,118),(0,13,142),(0,0,0),(0,0,0),(7,48,133),(2,27,140),(0,87,113),(0,0,0),(0,36,138),(0,46,135),(0,0,0),(0,0,0),(6,52,132),(0,32,139),(1,32,139),(0,0,0),(2,36,138),(2,46,135),(0,0,0),(0,0,0),(4,88,112),(0,63,128),(0,65,127),(0,0,0),(3,27,140),(0,49,134),(0,0,0),(0,0,0),(0,14,142),(1,14,142),(0,61,129),(0,0,0),(7,89,110),(0,22,141),(0,0,0),(0,0,0),(2,14,142),(0,40,137),(1,40,137),(0,0,0),(3,32,139),(2,22,141),(0,0,0),(0,0,0),(11,1,138),(2,40,137),(6,29,139),(0,0,0),(3,63,128),(0,59,130),(0,0,0),(0,0,0),(0,28,140),(1,28,140),(0,69,125),(0,0,0),(4,80,118),(0,15,142),(0,0,0),(0,0,0),(0,86,114),(0,52,133),(1,52,133),(0,0,0),(3,40,137),(2,15,142),(0,0,0),(0,0,0),(2,86,114),(2,52,133),(0,79,119),(0,0,0),(0,100,102),(1,100,102),(0,0,0),(0,0,0),(3,59,130),(4,32,139),(0,23,141),(0,0,0),(2,100,102),(0,37,138),(0,0,0),(0,0,0),(3,15,142),(0,71,124),(1,71,124),(0,0,0),(0,16,142),(0,90,111),(0,0,0),(0,0,0),(4,14,142),(2,71,124),(4,61,129),(0,0,0),(2,16,142),(2,90,111),(0,0,0),(0,0,0),(0,44,136),(1,44,136),(0,47,135),(0,0,0),(8,18,140),(3,23,141),(0,0,0),(0,0,0),(2,44,136),(0,29,140),(1,29,140),(0,0,0),(3,71,124),(4,59,130),(0,0,0),(0,0,0),(3,90,111),(0,0,143),(0,1,143),(0,0,0),(0,96,106),(0,2,143),(0,0,0),(0,0,0),(0,50,134),(0,24,141),(0,3,143),(0,0,0),(2,96,106),(2,2,143),(0,0,0),(0,0,0),(2,50,134),(0,4,143),(1,4,143),(0,0,0),(3,29,140),(10,62,125),(0,0,0),(0,0,0),(7,23,140),(2,4,143),(0,5,143),(0,0,0),(3,0,143),(0,34,139),(0,0,0),(0,0,0),(0,64,128),(1,64,128),(2,5,143),(0,0,0),(0,78,120),(0,6,143),(0,0,0),(0,0,0),(0,18,142),(1,18,142),(5,22,141),(0,0,0),(2,78,120),(2,6,143),(0,0,0),(0,0,0),(2,18,142),(6,20,141),(0,7,143),(0,0,0),(0,30,140),(1,30,140),(0,0,0),(0,0,0),(3,34,139),(4,29,140),(0,25,141),(0,0,0),(2,30,140),(0,75,122),(0,0,0),(0,0,0),(0,84,116),(0,8,143),(1,8,143),(0,0,0),(4,96,106),(2,75,122),(0,0,0),(0,0,0),(2,84,116),(0,45,136),(1,45,136),(0,0,0),(6,12,142),(0,19,142),(0,0,0),(0,0,0),(10,22,138),(0,48,135),(0,9,143),(0,0,0),(7,5,142),(0,42,137),(0,0,0),(0,0,0),(3,75,122),(2,48,135),(2,9,143),(0,0,0),(3,8,143),(2,42,137),(0,0,0),(0,0,0),(4,64,128),(5,16,142),(0,35,139),(0,0,0),(3,45,136),(0,10,143),(0,0,0),(0,0,0),(3,19,142),(8,21,140),(2,35,139),(0,0,0),(3,48,135),(0,26,141),(0,0,0),(0,0,0),(0,56,132),(0,31,140),(1,31,140),(0,0,0),(0,20,142),(0,39,138),(0,0,0),(0,0,0),(2,56,132),(2,31,140),(0,11,143),(0,0,0),(2,20,142),(2,39,138),(0,0,0),(0,0,0),(3,10,143),(4,8,143),(0,83,117),(0,0,0),(8,32,138),(5,50,134),(0,0,0),(0,0,0),(3,26,141),(4,45,136),(2,83,117),(0,0,0),(3,31,140),(4,19,142),(0,0,0),(0,0,0),(3,39,138),(0,12,143),(1,12,143),(0,0,0),(8,22,140),(3,11,143),(0,0,0),(0,0,0),(6,28,140),(2,12,143),(0,91,111),(0,0,0),(7,95,106),(0,21,142),(0,0,0),(0,0,0),(6,86,114),(0,65,128),(0,27,141),(0,0,0),(0,46,136),(1,46,136),(0,0,0),(0,0,0),(10,4,140),(0,36,139),(0,13,143),(0,0,0),(2,46,136),(0,61,130),(0,0,0),(0,0,0),(0,32,140),(1,32,140),(0,49,135),(0,0,0),(4,20,142),(0,98,105),(0,0,0),(0,0,0),(2,32,140),(6,71,124),(2,49,135),(0,0,0),(3,65,128),(0,69,126),(0,0,0),(0,0,0),(7,56,131),(0,79,120),(0,59,131),(0,0,0),(0,40,138),(0,14,143),(0,0,0),(0,0,0),(0,22,142),(1,22,142),(2,59,131),(0,0,0),(2,40,138),(2,14,143),(0,0,0),(0,0,0),(2,22,142),(4,12,143),(5,42,137),(0,0,0),(0,52,134),(1,52,134),(0,0,0),(0,0,0),(3,69,126),(0,28,141),(0,71,125),(0,0,0),(2,52,134),(3,59,131),(0,0,0),(0,0,0),(3,14,143),(0,57,132),(0,15,143),(0,0,0),(4,46,136),(8,1,142),(0,0,0),(0,0,0),(8,2,142),(0,85,116),(1,85,116),(0,0,0),(7,46,135),(4,61,130),(0,0,0),(0,0,0),(4,32,140),(0,33,140),(0,37,139),(0,0,0),(3,28,141),(0,23,142),(0,0,0),(0,0,0),(6,64,128),(2,33,140),(2,37,139),(0,0,0),(3,57,132),(2,23,142),(0,0,0),(0,0,0),(6,18,142),(0,16,143),(1,16,143),(0,0,0),(3,85,116),(4,14,143),(0,0,0),(0,0,0),(4,22,142),(2,16,143),(0,55,133),(0,0,0),(3,33,140),(0,94,109),(0,0,0),(0,0,0),(3,23,142),(10,11,140),(0,29,141),(0,0,0),(4,52,134),(0,41,138),(0,0,0),(0,0,0),(6,84,116),(4,28,141),(2,29,141),(0,0,0),(3,16,143),(2,41,138),(0,0,0),(0,0,0),(0,0,144),(0,1,144),(0,17,143),(0,0,0),(0,2,144),(1,2,144),(0,0,0),(0,0,0),(0,62,130),(0,3,144),(1,3,144),(0,0,0),(2,2,144),(0,93,110),(0,0,0),(0,0,0),(0,4,144),(0,68,127),(0,75,123),(0,0,0),(0,34,140),(1,34,140),(0,0,0),(0,0,0),(2,4,144),(0,5,144),(1,5,144),(0,0,0),(2,34,140),(0,38,139),(0,0,0),(0,0,0),(15,68,113),(2,5,144),(5,14,143),(0,0,0),(0,6,144),(0,18,143),(0,0,0),(0,0,0),(0,70,126),(1,70,126),(4,55,133),(0,0,0),(2,6,144),(0,30,141),(0,0,0),(0,0,0),(2,70,126),(0,7,144),(1,7,144),(0,0,0),(0,58,132),(0,25,142),(0,0,0),(0,0,0),(3,38,139),(2,7,144),(0,45,137),(0,0,0),(2,58,132),(2,25,142),(0,0,0),(0,0,0),(0,8,144),(1,8,144),(2,45,137),(0,0,0),(4,2,144),(10,22,139),(0,0,0),(0,0,0),(0,42,138),(0,72,125),(0,19,143),(0,0,0),(3,7,144),(0,77,122),(0,0,0),(0,0,0),(0,100,104),(0,9,144),(1,9,144),(0,0,0),(4,34,140),(2,77,122),(0,0,0),(0,0,0),(2,100,104),(0,35,140),(0,51,135),(0,0,0),(6,46,136),(4,38,139),(0,0,0),(0,0,0),(11,51,130),(2,35,140),(2,51,135),(0,0,0),(0,10,144),(1,10,144),(0,0,0),(0,0,0),(0,26,142),(1,26,142),(0,31,141),(0,0,0),(2,10,144),(4,30,141),(0,0,0),(0,0,0),(2,26,142),(0,20,143),(1,20,143),(0,0,0),(0,74,124),(1,74,124),(0,0,0),(0,0,0),(7,8,143),(0,11,144),(0,97,107),(0,0,0),(2,74,124),(5,0,144),(0,0,0),(0,0,0),(4,8,144),(2,11,144),(0,65,129),(0,0,0),(7,19,142),(0,63,130),(0,0,0),(0,0,0),(0,54,134),(0,67,128),(1,67,128),(0,0,0),(3,20,143),(2,63,130),(0,0,0),(0,0,0),(0,12,144),(1,12,144),(0,61,131),(0,0,0),(3,11,144),(0,46,137),(0,0,0),(0,0,0),(2,12,144),(4,35,140),(0,21,143),(0,0,0),(7,10,143),(0,27,142),(0,0,0),(0,0,0),(0,36,140),(0,49,136),(1,49,136),(0,0,0),(3,67,128),(2,27,142),(0,0,0),(0,0,0),(2,36,140),(0,13,144),(0,95,109),(0,0,0),(7,39,138),(3,61,131),(0,0,0),(0,0,0),(3,46,137),(2,13,144),(0,85,117),(0,0,0),(4,74,124),(0,71,126),(0,0,0),(0,0,0),(3,27,142),(0,40,139),(1,40,139),(0,0,0),(3,49,136),(2,71,126),(0,0,0),(0,0,0),(11,61,126),(0,52,135),(1,52,135),(0,0,0),(0,14,144),(0,22,143),(0,0,0),(0,0,0),(0,94,110),(1,94,110),(0,57,133),(0,0,0),(2,14,144),(2,22,143),(0,0,0),(0,0,0),(2,94,110),(7,91,111),(2,57,133),(0,0,0),(0,28,142),(1,28,142),(0,0,0),(0,0,0),(6,0,144),(6,1,144),(0,73,125),(0,0,0),(2,28,142),(4,27,142),(0,0,0),(0,0,0),(3,22,143),(0,15,144),(1,15,144),(0,0,0),(7,61,130),(3,57,133),(0,0,0),(0,0,0),(0,78,122),(0,37,140),(0,33,141),(0,0,0),(6,34,140),(10,62,127),(0,0,0),(0,0,0),(2,78,122),(2,37,140),(0,23,143),(0,0,0),(0,44,138),(0,55,134),(0,0,0),(0,0,0),(7,79,120),(4,40,139),(2,23,143),(0,0,0),(2,44,138),(2,55,134),(0,0,0),(0,0,0),(0,16,144),(1,16,144),(5,63,130),(0,0,0),(0,50,136),(0,66,129),(0,0,0),(0,0,0)]

def wits_21 : List (ℕ × ℕ × ℕ) := [(2,16,144),(0,75,124),(0,41,139),(0,0,0),(2,50,136),(0,29,142),(0,0,0),(0,0,0),(0,68,128),(1,68,128),(2,41,139),(0,0,0),(4,28,142),(0,102,103),(0,0,0),(0,0,0),(2,68,128),(0,101,104),(1,101,104),(0,0,0),(15,22,131),(2,102,103),(0,0,0),(0,0,0),(0,60,132),(0,0,145),(0,1,145),(0,0,0),(3,75,124),(0,2,145),(0,0,0),(0,0,0),(2,60,132),(2,0,145),(0,3,145),(0,0,0),(7,23,142),(0,34,141),(0,0,0),(0,0,0),(3,102,103),(0,4,145),(1,4,145),(0,0,0),(0,38,140),(1,38,140),(0,0,0),(0,0,0),(7,16,143),(2,4,145),(0,5,145),(0,0,0),(2,38,140),(0,58,133),(0,0,0),(0,0,0),(3,2,145),(5,14,144),(0,77,123),(0,0,0),(0,18,144),(0,6,145),(0,0,0),(0,0,0),(0,30,142),(1,30,142),(2,77,123),(0,0,0),(2,18,144),(0,45,138),(0,0,0),(0,0,0),(2,30,142),(0,48,137),(0,7,145),(0,0,0),(8,20,142),(2,45,138),(0,0,0),(0,0,0),(3,58,133),(2,48,137),(2,7,145),(0,0,0),(10,22,140),(0,42,139),(0,0,0),(0,0,0),(3,6,145),(0,8,145),(1,8,145),(0,0,0),(0,56,134),(1,56,134),(0,0,0),(0,0,0),(0,90,114),(0,19,144),(1,19,144),(0,0,0),(2,56,134),(0,74,125),(0,0,0),(0,0,0),(2,90,114),(2,19,144),(0,9,145),(0,0,0),(4,38,140),(2,74,125),(0,0,0),(0,0,0),(3,42,139),(6,49,136),(2,9,145),(0,0,0),(3,8,145),(4,58,133),(0,0,0),(0,0,0),(14,50,126),(0,39,140),(1,39,140),(0,0,0),(0,82,120),(0,10,145),(0,0,0),(0,0,0),(3,74,125),(2,39,140),(0,63,131),(0,0,0),(2,82,120),(2,10,145),(0,0,0),(0,0,0),(0,20,144),(1,20,144),(2,63,131),(0,0,0),(16,12,130),(0,54,135),(0,0,0),(0,0,0),(2,20,144),(0,61,132),(0,11,145),(0,0,0),(3,39,140),(0,85,118),(0,0,0),(0,0,0),(0,76,124),(1,76,124),(2,11,145),(0,0,0),(4,56,134),(0,94,111),(0,0,0),(0,0,0),(0,46,138),(1,46,138),(5,34,141),(0,0,0),(6,28,142),(2,94,111),(0,0,0),(0,0,0),(2,46,138),(0,12,145),(0,43,139),(0,0,0),(3,61,132),(3,11,145),(0,0,0),(0,0,0),(3,85,118),(0,21,144),(0,27,143),(0,0,0),(10,4,142),(9,96,106),(0,0,0),(0,0,0),(3,94,111),(2,21,144),(2,27,143),(0,0,0),(0,32,142),(1,32,142),(0,0,0),(0,0,0),(7,20,143),(0,93,112),(0,13,145),(0,0,0),(2,32,142),(3,43,139),(0,0,0),(0,0,0),(0,40,140),(1,40,140),(0,81,121),(0,0,0),(3,21,144),(0,57,134),(0,0,0),(0,0,0),(2,40,140),(4,61,132),(2,81,121),(0,0,0),(6,50,136),(0,78,123),(0,0,0),(0,0,0),(4,76,124),(0,84,119),(0,103,103),(0,0,0),(0,22,144),(0,14,145),(0,0,0),(0,0,0),(4,46,138),(2,84,119),(0,101,105),(0,0,0),(2,22,144),(2,14,145),(0,0,0),(0,0,0),(3,57,134),(0,28,143),(1,28,143),(0,0,0),(0,100,106),(1,100,106),(0,0,0),(0,0,0),(3,78,123),(2,28,143),(4,27,143),(0,0,0),(2,100,106),(3,103,103),(0,0,0),(0,0,0),(3,14,145),(5,82,120),(0,15,145),(0,0,0),(4,32,142),(0,33,142),(0,0,0),(0,0,0),(0,66,130),(0,44,139),(0,87,117),(0,0,0),(3,28,143),(2,33,142),(0,0,0),(0,0,0),(2,66,130),(0,23,144),(1,23,144),(0,0,0),(0,62,132),(0,50,137),(0,0,0),(0,0,0),(7,52,135),(2,23,144),(5,85,118),(0,0,0),(2,62,132),(0,91,114),(0,0,0),(0,0,0),(3,33,142),(0,16,145),(1,16,145),(0,0,0),(0,70,128),(1,70,128),(0,0,0),(0,0,0),(8,70,126),(0,60,133),(0,29,143),(0,0,0),(2,70,128),(8,30,141),(0,0,0),(0,0,0),(3,50,137),(2,60,133),(2,29,143),(0,0,0),(4,100,106),(6,42,139),(0,0,0),(0,0,0),(3,91,114),(0,53,136),(1,53,136),(0,0,0),(3,16,145),(13,34,134),(0,0,0),(0,0,0),(0,24,144),(0,72,127),(0,17,145),(0,0,0),(0,0,146),(0,1,146),(0,0,0),(0,0,0),(0,2,146),(1,2,146),(2,17,145),(0,0,0),(2,0,146),(0,3,146),(0,0,0),(0,0,0),(2,2,146),(4,23,144),(5,57,134),(0,0,0),(0,4,146),(1,4,146),(0,0,0),(0,0,0),(11,31,138),(6,39,140),(5,78,123),(0,0,0),(2,4,146),(0,5,146),(0,0,0),(0,0,0),(3,1,146),(4,16,145),(0,45,139),(0,0,0),(0,48,138),(0,18,145),(0,0,0),(0,0,0),(0,6,146),(1,6,146),(2,45,139),(0,0,0),(2,48,138),(2,18,145),(0,0,0),(0,0,0),(2,6,146),(0,25,144),(1,25,144),(0,0,0),(0,42,140),(0,7,146),(0,0,0),(0,0,0),(3,5,146),(2,25,144),(0,51,137),(0,0,0),(2,42,140),(2,7,146),(0,0,0),(0,0,0),(3,18,145),(0,89,116),(1,89,116),(0,0,0),(0,8,146),(1,8,146),(0,0,0),(0,0,0),(4,2,146),(2,89,116),(0,19,145),(0,0,0),(2,8,146),(0,35,142),(0,0,0),(0,0,0),(3,7,146),(0,63,132),(1,63,132),(0,0,0),(4,4,146),(0,9,146),(0,0,0),(0,0,0),(27,6,41),(0,76,125),(0,39,141),(0,0,0),(3,89,116),(2,9,146),(0,0,0),(0,0,0),(8,36,140),(2,76,125),(0,31,143),(0,0,0),(0,26,144),(1,26,144),(0,0,0),(0,0,0),(0,10,146),(1,10,146),(0,93,113),(0,0,0),(2,26,144),(6,57,134),(0,0,0),(0,0,0),(2,10,146),(0,20,145),(1,20,145),(0,0,0),(3,76,125),(0,102,105),(0,0,0),(0,0,0),(7,8,145),(0,88,117),(1,88,117),(0,0,0),(6,22,144),(0,11,146),(0,0,0),(0,0,0),(7,19,144),(2,88,117),(5,1,146),(0,0,0),(4,8,146),(0,49,138),(0,0,0),(0,0,0),(8,94,110),(0,43,140),(1,43,140),(0,0,0),(3,20,145),(2,49,138),(0,0,0),(0,0,0),(0,84,120),(1,84,120),(0,73,127),(0,0,0),(0,12,146),(1,12,146),(0,0,0),(0,0,0),(2,84,120),(0,27,144),(0,21,145),(0,0,0),(2,12,146),(6,33,142),(0,0,0),(0,0,0),(3,49,138),(0,32,143),(0,57,135),(0,0,0),(3,43,140),(5,6,146),(0,0,0),(0,0,0),(4,10,146),(0,40,141),(1,40,141),(0,0,0),(6,62,132),(0,13,146),(0,0,0),(0,0,0),(7,61,132),(2,40,141),(5,7,146),(0,0,0),(3,27,144),(0,87,118),(0,0,0),(0,0,0),(11,1,142),(4,88,117),(10,7,143),(0,0,0),(3,32,143),(0,75,126),(0,0,0),(0,0,0),(8,16,144),(5,8,146),(0,91,115),(0,0,0),(3,40,141),(0,22,145),(0,0,0),(0,0,0),(0,14,146),(1,14,146),(2,91,115),(0,0,0),(14,76,114),(0,66,131),(0,0,0),(0,0,0),(0,28,144),(0,55,136),(1,55,136),(0,0,0),(0,68,130),(1,68,130),(0,0,0),(0,0,0),(2,28,144),(0,80,123),(0,47,139),(0,0,0),(2,68,130),(0,37,142),(0,0,0),(0,0,0),(0,44,140),(0,96,111),(0,33,143),(0,0,0),(16,70,112),(0,15,146),(0,0,0),(0,0,0),(0,50,138),(1,50,138),(2,33,143),(0,0,0),(3,55,136),(2,15,146),(0,0,0),(0,0,0),(2,50,138),(8,4,145),(0,23,145),(0,0,0),(0,60,134),(0,86,119),(0,0,0),(0,0,0),(3,37,142),(7,103,103),(0,41,141),(0,0,0),(2,60,134),(2,86,119),(0,0,0),(0,0,0),(0,72,128),(0,95,112),(1,95,112),(0,0,0),(0,16,146),(1,16,146),(0,0,0),(0,0,0),(2,72,128),(0,29,144),(0,53,137),(0,0,0),(2,16,146),(3,23,145),(0,0,0),(0,0,0),(3,86,119),(2,29,144),(2,53,137),(0,0,0),(4,68,130),(0,58,135),(0,0,0),(0,0,0),(11,95,106),(4,80,123),(4,47,139),(0,0,0),(3,95,112),(2,58,135),(0,0,0),(0,0,0),(4,44,140),(0,24,145),(1,24,145),(0,0,0),(3,29,144),(0,17,146),(0,0,0),(0,0,0),(0,38,142),(0,0,147),(0,1,147),(0,0,0),(7,50,137),(0,2,147),(0,0,0),(0,0,0),(2,38,142),(0,79,124),(0,3,147),(0,0,0),(4,60,134),(2,2,147),(0,0,0),(0,0,0),(7,16,145),(0,4,147),(1,4,147),(0,0,0),(3,24,145),(10,98,105),(0,0,0),(0,0,0),(0,56,136),(1,56,136),(0,5,147),(0,0,0),(0,30,144),(1,30,144),(0,0,0),(0,0,0),(0,18,146),(1,18,146),(2,5,147),(0,0,0),(2,30,144),(0,6,147),(0,0,0),(0,0,0),(2,18,146),(0,65,132),(0,25,145),(0,0,0),(0,76,126),(1,76,126),(0,0,0),(0,0,0),(7,72,127),(2,65,132),(0,7,147),(0,0,0),(2,76,126),(0,69,130),(0,0,0),(0,0,0),(0,100,108),(1,100,108),(2,7,147),(0,0,0),(0,88,118),(1,88,118),(0,0,0),(0,0,0),(2,100,108),(0,8,147),(0,35,143),(0,0,0),(2,88,118),(0,19,146),(0,0,0),(0,0,0),(19,50,111),(2,8,147),(0,71,129),(0,0,0),(7,5,146),(0,39,142),(0,0,0),(0,0,0),(3,69,130),(0,92,115),(0,9,147),(0,0,0),(7,18,145),(2,39,142),(0,0,0),(0,0,0),(4,56,136),(0,31,144),(1,31,144),(0,0,0),(3,8,147),(0,26,145),(0,0,0),(0,0,0),(0,98,110),(1,98,110),(0,59,135),(0,0,0),(7,7,146),(0,10,147),(0,0,0),(0,0,0),(2,98,110),(0,73,128),(1,73,128),(0,0,0),(0,20,146),(1,20,146),(0,0,0),(0,0,0),(7,89,116),(2,73,128),(0,49,139),(0,0,0),(2,20,146),(4,69,130),(0,0,0),(0,0,0),(3,26,145),(7,19,145),(0,11,147),(0,0,0),(4,88,118),(3,59,135),(0,0,0),(0,0,0),(3,10,147),(0,91,116),(1,91,116),(0,0,0),(3,73,128),(4,19,146),(0,0,0),(0,0,0),(7,76,125),(0,36,143),(1,36,143),(0,0,0),(0,52,138),(1,52,138),(0,0,0),(0,0,0),(6,44,140),(0,12,147),(0,27,145),(0,0,0),(2,52,138),(0,21,146),(0,0,0),(0,0,0),(0,32,144),(1,32,144),(2,27,145),(0,0,0),(0,40,142),(1,40,142),(0,0,0),(0,0,0),(2,32,144),(8,44,139),(4,59,135),(0,0,0),(2,40,142),(0,83,122),(0,0,0),(0,0,0),(0,80,124),(1,80,124),(0,13,147),(0,0,0),(0,66,132),(1,66,132),(0,0,0),(0,0,0),(2,80,124),(0,64,133),(1,64,133),(0,0,0),(2,66,132),(0,90,117),(0,0,0),(0,0,0),(7,43,140),(2,64,133),(0,55,137),(0,0,0),(0,86,120),(1,86,120),(0,0,0),(0,0,0),(0,22,146),(1,22,146),(2,55,137),(0,0,0),(2,86,120),(0,14,147),(0,0,0),(0,0,0),(2,22,146),(0,28,145),(1,28,145),(0,0,0),(3,64,133),(2,14,147),(0,0,0),(0,0,0),(3,90,117),(0,44,141),(0,37,143),(0,0,0),(23,7,98),(0,50,139),(0,0,0),(0,0,0),(4,32,144),(0,33,144),(1,33,144),(0,0,0),(4,40,142),(2,50,139),(0,0,0),(0,0,0),(0,94,114),(1,94,114),(0,15,147),(0,0,0),(3,28,145),(4,83,122),(0,0,0),(0,0,0),(2,94,114),(0,104,105),(1,104,105),(0,0,0),(3,44,141),(0,23,146),(0,0,0),(0,0,0),(3,50,139),(2,104,105),(6,5,147),(0,0,0),(3,33,144),(0,53,138),(0,0,0),(0,0,0),(6,18,146),(10,11,144),(4,55,137),(0,0,0),(0,58,136),(1,58,136),(0,0,0),(0,0,0),(4,22,146),(0,16,147),(0,29,145),(0,0,0),(2,58,136),(4,14,147),(0,0,0),(0,0,0),(3,23,146),(2,16,147),(0,93,115),(0,0,0),(7,37,142),(6,69,130),(0,0,0),(0,0,0),(3,53,138),(0,100,109),(1,100,109),(0,0,0),(6,88,118),(4,50,139),(0,0,0),(0,0,0),(11,26,141),(2,100,109),(6,35,143),(0,0,0),(0,24,146),(0,38,143),(0,0,0),(0,0,0),(4,94,114),(7,23,145),(0,17,147),(0,0,0),(2,24,146),(0,99,110),(0,0,0),(0,0,0),(0,0,148),(0,1,148),(0,45,141),(0,0,0),(0,2,148),(1,2,148),(0,0,0),(0,0,0),(2,0,148),(0,3,148),(0,65,133),(0,0,0),(2,2,148),(4,53,138),(0,0,0),(0,0,0),(0,4,148),(1,4,148),(0,51,139),(0,0,0),(4,58,136),(0,30,145),(0,0,0),(0,0,0),(0,42,142),(0,5,148),(1,5,148),(0,0,0),(3,1,148),(0,18,147),(0,0,0),(0,0,0),(2,42,142),(0,81,124),(1,81,124),(0,0,0),(0,6,148),(0,25,146),(0,0,0),(0,0,0),(7,24,145),(2,81,124),(0,61,135),(0,0,0),(2,6,148),(2,25,146),(0,0,0),(0,0,0),(3,30,145),(0,7,148),(1,7,148),(0,0,0),(3,5,148),(4,38,143),(0,0,0),(0,0,0),(0,54,138),(0,35,144),(1,35,144),(0,0,0),(3,81,124),(4,99,110),(0,0,0),(0,0,0),(0,8,148),(0,87,120),(0,19,147),(0,0,0),(4,2,148),(3,61,135),(0,0,0),(0,0,0),(2,8,148),(0,59,136),(1,59,136),(0,0,0),(3,7,148),(10,55,134),(0,0,0),(0,0,0),(4,4,148),(0,9,148),(0,31,145),(0,0,0),(3,35,144),(4,30,145),(0,0,0),(0,0,0),(0,26,146),(1,26,146),(2,31,145),(0,0,0),(3,87,120),(0,46,141),(0,0,0),(0,0,0)]

def wits_22 : List (ℕ × ℕ × ℕ) := [(2,26,146),(0,49,140),(1,49,140),(0,0,0),(0,10,148),(1,10,148),(0,0,0),(0,0,0),(10,68,128),(0,20,147),(1,20,147),(0,0,0),(2,10,148),(0,43,142),(0,0,0),(0,0,0),(6,22,146),(2,20,147),(0,57,137),(0,0,0),(7,19,146),(0,95,114),(0,0,0),(0,0,0),(0,90,118),(0,11,148),(1,11,148),(0,0,0),(3,49,140),(2,95,114),(0,0,0),(0,0,0),(0,36,144),(1,36,144),(4,19,147),(0,0,0),(3,20,147),(0,86,121),(0,0,0),(0,0,0),(2,36,144),(4,59,136),(8,47,139),(0,0,0),(7,26,145),(0,27,146),(0,0,0),(0,0,0),(0,12,148),(0,32,145),(0,21,147),(0,0,0),(0,64,134),(1,64,134),(0,0,0),(0,0,0),(2,12,148),(2,32,145),(0,77,127),(0,0,0),(2,64,134),(0,70,131),(0,0,0),(0,0,0),(3,86,121),(4,49,140),(2,77,127),(0,0,0),(0,102,108),(0,55,138),(0,0,0),(0,0,0),(3,27,146),(0,13,148),(1,13,148),(0,0,0),(2,102,108),(2,55,138),(0,0,0),(0,0,0),(7,91,116),(2,13,148),(0,89,119),(0,0,0),(0,72,130),(1,72,130),(0,0,0),(0,0,0),(3,70,131),(4,11,148),(0,47,141),(0,0,0),(2,72,130),(0,22,147),(0,0,0),(0,0,0),(0,60,136),(1,60,136),(2,47,141),(0,0,0),(0,14,148),(1,14,148),(0,0,0),(0,0,0),(2,60,136),(0,37,144),(1,37,144),(0,0,0),(2,14,148),(0,85,122),(0,0,0),(0,0,0),(4,12,148),(2,37,144),(0,33,145),(0,0,0),(4,64,134),(0,74,129),(0,0,0),(0,0,0),(3,22,147),(6,1,148),(0,99,111),(0,0,0),(6,2,148),(2,74,129),(0,0,0),(0,0,0),(7,64,133),(0,15,148),(0,41,143),(0,0,0),(3,37,144),(0,58,137),(0,0,0),(0,0,0),(3,85,122),(2,15,148),(0,23,147),(0,0,0),(11,72,125),(2,58,137),(0,0,0),(0,0,0),(0,88,120),(1,88,120),(2,23,147),(0,0,0),(0,98,112),(1,98,112),(0,0,0),(0,0,0),(2,88,120),(0,92,117),(1,92,117),(0,0,0),(2,98,112),(0,29,146),(0,0,0),(0,0,0),(0,16,148),(1,16,148),(5,86,121),(0,0,0),(4,14,148),(2,29,146),(0,0,0),(0,0,0),(2,16,148),(4,37,144),(5,27,146),(0,0,0),(15,29,134),(4,85,122),(0,0,0),(0,0,0),(6,54,138),(5,64,134),(0,67,133),(0,0,0),(0,38,144),(0,34,145),(0,0,0),(0,0,0),(3,29,146),(0,24,147),(0,81,125),(0,0,0),(2,38,144),(0,45,142),(0,0,0),(0,0,0),(18,22,126),(0,17,148),(0,63,135),(0,0,0),(7,53,138),(2,45,142),(0,0,0),(0,0,0),(10,40,140),(0,0,149),(0,1,149),(0,0,0),(11,67,128),(0,2,149),(0,0,0),(0,0,0),(3,34,145),(2,0,149),(0,3,149),(0,0,0),(0,96,114),(0,42,143),(0,0,0),(0,0,0),(0,30,146),(0,4,149),(1,4,149),(0,0,0),(2,96,114),(2,42,143),(0,0,0),(0,0,0),(2,30,146),(2,4,149),(0,5,149),(0,0,0),(0,18,148),(0,73,130),(0,0,0),(0,0,0),(3,2,149),(10,28,143),(0,25,147),(0,0,0),(2,18,148),(0,6,149),(0,0,0),(0,0,0),(3,42,143),(6,11,148),(2,25,147),(0,0,0),(3,4,149),(2,6,149),(0,0,0),(0,0,0),(6,36,144),(4,24,147),(0,7,149),(0,0,0),(11,40,139),(3,5,149),(0,0,0),(0,0,0),(3,73,130),(0,39,144),(1,39,144),(0,0,0),(8,52,138),(0,90,119),(0,0,0),(0,0,0),(3,6,149),(0,8,149),(0,75,129),(0,0,0),(6,64,134),(2,90,119),(0,0,0),(0,0,0),(7,5,148),(0,103,108),(1,103,108),(0,0,0),(0,80,126),(0,31,146),(0,0,0),(0,0,0),(0,46,142),(1,46,142),(0,9,149),(0,0,0),(2,80,126),(0,26,147),(0,0,0),(0,0,0),(2,46,142),(6,13,148),(2,9,149),(0,0,0),(0,94,116),(0,57,138),(0,0,0),(0,0,0),(7,7,148),(8,64,133),(0,43,143),(0,0,0),(2,94,116),(0,10,149),(0,0,0),(0,0,0),(0,20,148),(1,20,148),(2,43,143),(0,0,0),(8,86,120),(2,10,149),(0,0,0),(0,0,0),(0,66,134),(0,68,133),(1,68,133),(0,0,0),(6,14,148),(8,14,147),(0,0,0),(0,0,0),(2,66,134),(0,36,145),(0,11,149),(0,0,0),(0,70,132),(1,70,132),(0,0,0),(0,0,0),(3,10,149),(2,36,145),(2,11,149),(0,0,0),(2,70,132),(6,74,129),(0,0,0),(0,0,0),(0,40,144),(1,40,144),(0,27,147),(0,0,0),(0,32,146),(1,32,146),(0,0,0),(0,0,0),(2,40,144),(0,12,149),(0,55,139),(0,0,0),(2,32,146),(0,82,125),(0,0,0),(0,0,0),(7,20,147),(2,12,149),(0,85,123),(0,0,0),(4,94,116),(2,82,125),(0,0,0),(0,0,0),(6,88,120),(7,57,137),(2,85,123),(0,0,0),(6,98,112),(3,27,147),(0,0,0),(0,0,0),(4,20,148),(0,60,137),(0,13,149),(0,0,0),(3,12,149),(0,47,142),(0,0,0),(0,0,0),(0,74,130),(1,74,130),(2,13,149),(0,0,0),(7,86,121),(0,50,141),(0,0,0),(0,0,0),(2,74,130),(0,44,143),(1,44,143),(0,0,0),(0,22,148),(1,22,148),(0,0,0),(0,0,0),(7,32,145),(0,28,147),(0,37,145),(0,0,0),(2,22,148),(0,14,149),(0,0,0),(0,0,0),(3,47,142),(2,28,147),(2,37,145),(0,0,0),(4,32,146),(0,33,146),(0,0,0),(0,0,0),(0,58,138),(0,53,140),(1,53,140),(0,0,0),(3,44,143),(2,33,146),(0,0,0),(0,0,0),(2,58,138),(0,41,144),(1,41,144),(0,0,0),(3,28,147),(3,37,145),(0,0,0),(0,0,0),(3,14,149),(2,41,144),(0,15,149),(0,0,0),(6,96,114),(5,20,148),(0,0,0),(0,0,0),(0,84,124),(0,23,148),(1,23,148),(0,0,0),(3,53,140),(0,81,126),(0,0,0),(0,0,0),(2,84,124),(0,96,115),(0,91,119),(0,0,0),(3,41,144),(0,67,134),(0,0,0),(0,0,0),(7,37,144),(2,96,115),(0,29,147),(0,0,0),(4,22,148),(0,87,122),(0,0,0),(0,0,0),(10,84,120),(0,16,149),(1,16,149),(0,0,0),(3,23,148),(2,87,122),(0,0,0),(0,0,0),(3,81,126),(0,63,136),(1,63,136),(0,0,0),(0,48,142),(0,38,145),(0,0,0),(0,0,0),(0,34,146),(1,34,146),(0,45,143),(0,0,0),(2,48,142),(2,38,145),(0,0,0),(0,0,0),(0,24,148),(0,95,116),(0,51,141),(0,0,0),(3,16,149),(10,13,146),(0,0,0),(0,0,0),(2,24,148),(2,95,116),(0,17,149),(0,0,0),(3,63,136),(6,31,146),(0,0,0),(0,0,0),(3,38,145),(4,23,148),(2,17,149),(0,0,0),(0,0,150),(0,1,150),(0,0,0),(0,0,0),(0,2,150),(1,2,150),(4,91,119),(0,0,0),(2,0,150),(0,3,150),(0,0,0),(0,0,0),(2,2,150),(5,22,148),(0,83,125),(0,0,0),(0,4,150),(1,4,150),(0,0,0),(0,0,0),(6,20,148),(4,16,149),(0,101,111),(0,0,0),(2,4,150),(0,5,150),(0,0,0),(0,0,0),(3,1,150),(0,25,148),(1,25,148),(0,0,0),(4,48,142),(2,5,150),(0,0,0),(0,0,0),(0,6,150),(1,6,150),(4,45,143),(0,0,0),(6,70,132),(0,35,146),(0,0,0),(0,0,0),(0,100,112),(1,100,112),(0,39,145),(0,0,0),(7,2,149),(0,7,150),(0,0,0),(0,0,0),(2,100,112),(7,3,149),(2,39,145),(0,0,0),(3,25,148),(2,7,150),(0,0,0),(0,0,0),(7,4,149),(6,12,149),(0,19,149),(0,0,0),(0,8,150),(0,46,143),(0,0,0),(0,0,0),(3,35,146),(7,5,149),(0,31,147),(0,0,0),(2,8,150),(0,93,118),(0,0,0),(0,0,0),(3,7,150),(7,25,147),(2,31,147),(0,0,0),(0,26,148),(0,9,150),(0,0,0),(0,0,0),(11,33,142),(0,43,144),(1,43,144),(0,0,0),(2,26,148),(0,70,133),(0,0,0),(0,0,0),(0,64,136),(1,64,136),(5,38,145),(0,0,0),(8,72,130),(2,70,133),(0,0,0),(0,0,0),(0,10,150),(0,20,149),(1,20,149),(0,0,0),(6,22,148),(4,35,146),(0,0,0),(0,0,0),(0,72,132),(1,72,132),(4,39,145),(0,0,0),(0,36,146),(0,62,137),(0,0,0),(0,0,0),(2,72,132),(8,37,144),(10,3,147),(0,0,0),(2,36,146),(0,11,150),(0,0,0),(0,0,0),(6,58,138),(0,40,145),(1,40,145),(0,0,0),(0,88,122),(1,88,122),(0,0,0),(0,0,0),(10,56,136),(0,27,148),(0,97,115),(0,0,0),(2,88,122),(0,74,131),(0,0,0),(0,0,0),(3,62,137),(2,27,148),(0,21,149),(0,0,0),(0,12,150),(1,12,150),(0,0,0),(0,0,0),(3,11,150),(4,43,144),(2,21,149),(0,0,0),(2,12,150),(4,70,133),(0,0,0),(0,0,0),(4,64,136),(6,96,115),(0,47,143),(0,0,0),(3,27,148),(3,97,115),(0,0,0),(0,0,0),(0,50,142),(1,50,142),(2,47,143),(0,0,0),(10,88,118),(0,13,150),(0,0,0),(0,0,0),(0,44,144),(1,44,144),(5,7,150),(0,0,0),(0,76,130),(1,76,130),(0,0,0),(0,0,0),(2,44,144),(0,84,125),(1,84,125),(0,0,0),(2,76,130),(0,22,149),(0,0,0),(0,0,0),(0,28,148),(0,105,108),(0,53,141),(0,0,0),(4,88,122),(2,22,149),(0,0,0),(0,0,0),(0,14,150),(0,104,109),(0,33,147),(0,0,0),(15,2,139),(4,74,131),(0,0,0),(0,0,0),(2,14,150),(2,104,109),(0,41,145),(0,0,0),(3,84,125),(0,103,110),(0,0,0),(0,0,0),(3,22,149),(7,13,149),(0,67,135),(0,0,0),(3,105,108),(0,69,134),(0,0,0),(0,0,0),(6,2,150),(0,65,136),(1,65,136),(0,0,0),(3,104,109),(0,15,150),(0,0,0),(0,0,0),(4,50,142),(2,65,136),(0,23,149),(0,0,0),(6,4,150),(2,15,150),(0,0,0),(0,0,0),(0,56,140),(1,56,140),(0,63,137),(0,0,0),(4,76,130),(0,90,121),(0,0,0),(0,0,0),(2,56,140),(0,29,148),(1,29,148),(0,0,0),(3,65,136),(2,90,121),(0,0,0),(0,0,0),(3,15,150),(0,48,143),(1,48,143),(0,0,0),(0,16,150),(1,16,150),(0,0,0),(0,0,0),(0,38,146),(0,45,144),(1,45,144),(0,0,0),(2,16,150),(0,34,147),(0,0,0),(0,0,0),(2,38,146),(0,100,113),(1,100,113),(0,0,0),(0,86,124),(1,86,124),(0,0,0),(0,0,0),(7,23,148),(0,24,149),(1,24,149),(0,0,0),(2,86,124),(4,69,134),(0,0,0),(0,0,0),(0,80,128),(1,80,128),(0,75,131),(0,0,0),(3,45,144),(0,17,150),(0,0,0),(0,0,0),(2,80,128),(7,29,147),(2,75,131),(0,0,0),(3,100,113),(0,54,141),(0,0,0),(0,0,0),(4,56,140),(0,0,151),(0,1,151),(0,0,0),(0,30,148),(0,2,151),(0,0,0),(0,0,0),(6,64,136),(2,0,151),(0,3,151),(0,0,0),(2,30,148),(2,2,151),(0,0,0),(0,0,0),(3,17,150),(0,4,151),(1,4,151),(0,0,0),(4,16,150),(5,14,150),(0,0,0),(0,0,0),(0,18,150),(1,18,150),(0,5,151),(0,0,0),(3,0,151),(0,77,130),(0,0,0),(0,0,0),(2,18,150),(4,100,113),(0,35,147),(0,0,0),(4,86,124),(0,6,151),(0,0,0),(0,0,0),(11,22,145),(4,24,149),(2,35,147),(0,0,0),(3,4,151),(2,6,151),(0,0,0),(0,0,0),(4,80,128),(0,57,140),(0,7,151),(0,0,0),(0,46,144),(0,82,127),(0,0,0),(0,0,0),(0,70,134),(1,70,134),(2,7,151),(0,0,0),(2,46,144),(0,19,150),(0,0,0),(0,0,0),(0,92,120),(0,8,151),(1,8,151),(0,0,0),(0,52,142),(1,52,142),(0,0,0),(0,0,0),(2,92,120),(0,72,133),(0,43,145),(0,0,0),(2,52,142),(0,26,149),(0,0,0),(0,0,0),(3,82,127),(2,72,133),(0,9,151),(0,0,0),(7,35,146),(2,26,149),(0,0,0),(0,0,0),(0,62,138),(1,62,138),(2,9,151),(0,0,0),(3,8,151),(4,77,130),(0,0,0),(0,0,0),(2,62,138),(5,86,124),(0,107,107),(0,0,0),(0,20,150),(0,10,151),(0,0,0),(0,0,0),(3,26,149),(0,36,147),(0,55,141),(0,0,0),(2,20,150),(2,10,151),(0,0,0),(0,0,0),(6,14,150),(2,36,147),(2,55,141),(0,0,0),(0,40,146),(1,40,146),(0,0,0),(0,0,0),(4,70,134),(0,60,139),(0,11,151),(0,0,0),(2,40,146),(3,107,107),(0,0,0),(0,0,0),(0,32,148),(1,32,148),(0,27,149),(0,0,0),(0,84,126),(1,84,126),(0,0,0),(0,0,0),(2,32,148),(0,76,131),(1,76,131),(0,0,0),(2,84,126),(0,21,150),(0,0,0),(0,0,0),(7,20,149),(0,12,151),(1,12,151),(0,0,0),(0,102,112),(0,50,143),(0,0,0),(0,0,0),(4,62,138),(2,12,151),(5,77,130),(0,0,0),(2,102,112),(2,50,143),(0,0,0),(0,0,0),(10,54,138),(0,44,145),(1,44,145),(0,0,0),(0,58,140),(1,58,140),(0,0,0),(0,0,0),(3,21,150),(2,44,145),(0,13,151),(0,0,0),(2,58,140),(0,53,142),(0,0,0),(0,0,0),(3,50,143),(5,46,144),(0,37,147),(0,0,0),(4,40,146),(2,53,142),(0,0,0),(0,0,0),(0,22,150),(0,28,149),(0,69,135),(0,0,0),(3,44,145),(5,92,120),(0,0,0),(0,0,0),(2,22,150),(0,33,148),(0,65,137),(0,0,0),(0,100,114),(0,14,151),(0,0,0),(0,0,0)]

def wits_23 : List (ℕ × ℕ × ℕ) := [(3,53,142),(2,33,148),(2,65,137),(0,0,0),(2,100,114),(2,14,151),(0,0,0),(0,0,0),(11,19,146),(4,12,151),(13,77,122),(0,0,0),(3,28,149),(0,63,138),(0,0,0),(0,0,0),(8,2,150),(0,56,141),(0,73,133),(0,0,0),(3,33,148),(0,86,125),(0,0,0),(0,0,0),(3,14,151),(2,56,141),(0,15,151),(0,0,0),(4,58,140),(0,23,150),(0,0,0),(0,0,0),(7,105,108),(6,4,151),(2,15,151),(0,0,0),(15,50,131),(2,23,150),(0,0,0),(0,0,0),(0,48,144),(0,80,129),(0,29,149),(0,0,0),(3,56,141),(3,73,133),(0,0,0),(0,0,0),(2,48,144),(0,75,132),(0,45,145),(0,0,0),(7,103,110),(0,38,147),(0,0,0),(0,0,0),(3,23,150),(0,16,151),(1,16,151),(0,0,0),(0,34,148),(1,34,148),(0,0,0),(0,0,0),(7,65,136),(2,16,151),(5,21,150),(0,0,0),(2,34,148),(3,29,149),(0,0,0),(0,0,0),(6,70,134),(5,102,112),(5,50,143),(0,0,0),(0,24,150),(1,24,150),(0,0,0),(0,0,0),(0,42,146),(0,59,140),(1,59,140),(0,0,0),(2,24,150),(4,86,125),(0,0,0),(0,0,0),(2,42,146),(2,59,140),(0,17,151),(0,0,0),(8,26,148),(4,23,150),(0,0,0),(0,0,0),(7,48,143),(8,43,144),(0,97,117),(0,0,0),(10,14,148),(0,30,149),(0,0,0),(0,0,0),(0,0,152),(0,1,152),(1,1,152),(0,0,0),(0,2,152),(1,2,152),(0,0,0),(0,0,0),(2,0,152),(0,3,152),(1,3,152),(0,0,0),(2,2,152),(0,106,109),(0,0,0),(0,0,0),(0,4,152),(1,4,152),(5,14,151),(0,0,0),(4,34,148),(0,18,151),(0,0,0),(0,0,0),(2,4,152),(0,5,152),(0,39,147),(0,0,0),(3,1,152),(2,18,151),(0,0,0),(0,0,0),(11,14,147),(0,49,144),(1,49,144),(0,0,0),(0,6,152),(0,46,145),(0,0,0),(0,0,0),(3,106,109),(2,49,144),(5,86,125),(0,0,0),(2,6,152),(2,46,145),(0,0,0),(0,0,0),(3,18,151),(0,7,152),(1,7,152),(0,0,0),(3,5,152),(3,39,147),(0,0,0),(0,0,0),(7,4,151),(2,7,152),(0,19,151),(0,0,0),(3,49,144),(0,43,146),(0,0,0),(0,0,0),(0,8,152),(1,8,152),(2,19,151),(0,0,0),(4,2,152),(0,102,113),(0,0,0),(0,0,0),(0,26,150),(1,26,150),(5,38,147),(0,0,0),(3,7,152),(2,102,113),(0,0,0),(0,0,0),(2,26,150),(0,9,152),(0,95,119),(0,0,0),(8,76,130),(0,55,142),(0,0,0),(0,0,0),(3,43,146),(2,9,152),(0,87,125),(0,0,0),(7,82,127),(0,101,114),(0,0,0),(0,0,0),(0,36,148),(0,20,151),(0,81,129),(0,0,0),(0,10,152),(1,10,152),(0,0,0),(0,0,0),(2,36,148),(0,40,147),(1,40,147),(0,0,0),(2,10,152),(3,95,119),(0,0,0),(0,0,0),(3,55,142),(2,40,147),(8,41,145),(0,0,0),(7,26,149),(3,87,125),(0,0,0),(0,0,0),(3,101,114),(0,11,152),(1,11,152),(0,0,0),(3,20,151),(0,27,150),(0,0,0),(0,0,0),(4,8,152),(2,11,152),(0,47,145),(0,0,0),(0,50,144),(1,50,144),(0,0,0),(0,0,0),(4,26,150),(7,107,107),(0,21,151),(0,0,0),(2,50,144),(0,58,141),(0,0,0),(0,0,0),(0,12,152),(1,12,152),(2,21,151),(0,0,0),(0,44,146),(1,44,146),(0,0,0),(0,0,0),(2,12,152),(0,69,136),(0,53,143),(0,0,0),(2,44,146),(3,47,145),(0,0,0),(0,0,0),(4,36,148),(2,69,136),(0,71,135),(0,0,0),(4,10,152),(0,65,138),(0,0,0),(0,0,0),(0,86,126),(0,13,152),(1,13,152),(0,0,0),(6,34,148),(2,65,138),(0,0,0),(0,0,0),(2,86,126),(2,13,152),(10,9,149),(0,0,0),(0,28,150),(0,22,151),(0,0,0),(0,0,0),(7,12,151),(4,11,152),(0,33,149),(0,0,0),(2,28,150),(0,98,117),(0,0,0),(0,0,0),(3,65,138),(0,89,124),(1,89,124),(0,0,0),(0,14,152),(1,14,152),(0,0,0),(0,0,0),(7,44,145),(2,89,124),(4,21,151),(0,0,0),(2,14,152),(4,58,141),(0,0,0),(0,0,0),(3,22,151),(7,13,151),(0,75,133),(0,0,0),(4,44,146),(3,33,149),(0,0,0),(0,0,0),(3,98,117),(0,61,140),(1,61,140),(0,0,0),(3,89,124),(5,36,148),(0,0,0),(0,0,0),(0,108,108),(0,15,152),(0,23,151),(0,0,0),(11,49,140),(0,97,118),(0,0,0),(0,0,0),(0,106,110),(0,51,144),(1,51,144),(0,0,0),(7,14,151),(0,29,150),(0,0,0),(0,0,0),(2,106,110),(2,51,144),(0,105,111),(0,0,0),(0,38,148),(1,38,148),(0,0,0),(0,0,0),(11,95,114),(0,77,132),(0,85,127),(0,0,0),(2,38,148),(0,34,149),(0,0,0),(0,0,0),(0,16,152),(1,16,152),(0,59,141),(0,0,0),(3,51,144),(0,54,143),(0,0,0),(0,0,0),(2,16,152),(0,88,125),(1,88,125),(0,0,0),(7,23,150),(0,42,147),(0,0,0),(0,0,0),(8,92,120),(0,24,151),(0,103,113),(0,0,0),(3,77,132),(2,42,147),(0,0,0),(0,0,0),(3,34,149),(2,24,151),(2,103,113),(0,0,0),(10,22,148),(3,59,141),(0,0,0),(0,0,0),(3,54,143),(0,17,152),(1,17,152),(0,0,0),(0,70,136),(1,70,136),(0,0,0),(0,0,0),(0,30,150),(1,30,150),(0,79,131),(0,0,0),(2,70,136),(3,103,113),(0,0,0),(0,0,0),(2,30,150),(0,0,153),(0,1,153),(0,0,0),(4,38,148),(0,2,153),(0,0,0),(0,0,0),(6,36,148),(0,64,139),(0,3,153),(0,0,0),(3,17,152),(2,2,153),(0,0,0),(0,0,0),(4,16,152),(0,4,153),(0,25,151),(0,0,0),(0,18,152),(1,18,152),(0,0,0),(0,0,0),(0,46,146),(1,46,146),(0,5,153),(0,0,0),(2,18,152),(3,1,153),(0,0,0),(0,0,0),(0,52,144),(1,52,144),(2,5,153),(0,0,0),(0,62,140),(0,6,153),(0,0,0),(0,0,0),(2,52,144),(8,76,131),(6,47,145),(0,0,0),(2,62,140),(2,6,153),(0,0,0),(0,0,0),(0,100,116),(1,100,116),(0,7,153),(0,0,0),(4,70,136),(0,31,150),(0,0,0),(0,0,0),(2,100,116),(0,19,152),(1,19,152),(0,0,0),(6,44,146),(2,31,150),(0,0,0),(0,0,0),(3,6,153),(0,8,153),(0,55,143),(0,0,0),(0,90,124),(0,26,151),(0,0,0),(0,0,0),(7,49,144),(0,60,141),(1,60,141),(0,0,0),(2,90,124),(2,26,151),(0,0,0),(0,0,0),(3,31,150),(2,60,141),(0,9,153),(0,0,0),(3,19,152),(14,93,110),(0,0,0),(0,0,0),(4,46,146),(0,36,149),(1,36,149),(0,0,0),(3,8,153),(3,55,143),(0,0,0),(0,0,0),(0,20,152),(1,20,152),(6,33,149),(0,0,0),(0,78,132),(0,10,153),(0,0,0),(0,0,0),(2,20,152),(6,89,124),(10,83,125),(0,0,0),(2,78,132),(2,10,153),(0,0,0),(0,0,0),(4,100,116),(5,70,136),(4,7,153),(0,0,0),(0,32,150),(0,47,146),(0,0,0),(0,0,0),(0,58,142),(1,58,142),(0,11,153),(0,0,0),(2,32,150),(0,67,138),(0,0,0),(0,0,0),(2,58,142),(0,71,136),(1,71,136),(0,0,0),(4,90,124),(2,67,138),(0,0,0),(0,0,0),(6,108,108),(0,21,152),(0,65,139),(0,0,0),(11,4,149),(0,107,110),(0,0,0),(0,0,0),(3,47,146),(0,12,153),(0,73,135),(0,0,0),(20,34,120),(0,106,111),(0,0,0),(0,0,0),(3,67,138),(0,80,131),(1,80,131),(0,0,0),(3,71,136),(2,106,111),(0,0,0),(0,0,0),(4,20,152),(0,63,140),(0,37,149),(0,0,0),(3,21,152),(3,65,139),(0,0,0),(0,0,0),(3,107,110),(2,63,140),(0,13,153),(0,0,0),(3,12,153),(0,75,134),(0,0,0),(0,0,0),(3,106,111),(0,28,151),(1,28,151),(0,0,0),(0,22,152),(0,33,150),(0,0,0),(0,0,0),(4,58,142),(0,92,123),(1,92,123),(0,0,0),(2,22,152),(2,33,150),(0,0,0),(0,0,0),(7,69,136),(2,92,123),(0,61,141),(0,0,0),(11,103,108),(0,14,153),(0,0,0),(0,0,0),(3,75,134),(0,85,128),(1,85,128),(0,0,0),(3,28,151),(2,14,153),(0,0,0),(0,0,0),(0,96,120),(1,96,120),(0,77,133),(0,0,0),(0,48,146),(1,48,146),(0,0,0),(0,0,0),(0,82,130),(1,82,130),(0,51,145),(0,0,0),(2,48,146),(0,102,115),(0,0,0),(0,0,0),(2,82,130),(0,23,152),(0,15,153),(0,0,0),(3,85,128),(2,102,115),(0,0,0),(0,0,0),(7,89,124),(2,23,152),(0,29,151),(0,0,0),(6,18,152),(0,38,149),(0,0,0),(0,0,0),(6,46,146),(4,28,151),(2,29,151),(0,0,0),(0,54,144),(1,54,144),(0,0,0),(0,0,0),(0,34,150),(0,91,124),(1,91,124),(0,0,0),(2,54,144),(3,15,153),(0,0,0),(0,0,0),(2,34,150),(0,16,153),(0,95,121),(0,0,0),(0,42,148),(0,70,137),(0,0,0),(0,0,0),(3,38,149),(2,16,153),(2,95,121),(0,0,0),(2,42,148),(0,66,139),(0,0,0),(0,0,0),(0,24,152),(1,24,152),(4,77,133),(0,0,0),(3,91,124),(2,66,139),(0,0,0),(0,0,0),(2,24,152),(0,100,117),(1,100,117),(0,0,0),(3,16,153),(3,95,121),(0,0,0),(0,0,0),(0,64,140),(0,84,129),(0,17,153),(0,0,0),(7,34,149),(0,30,151),(0,0,0),(0,0,0),(2,64,140),(2,84,129),(2,17,153),(0,0,0),(7,54,143),(2,30,151),(0,0,0),(0,0,0),(7,88,125),(5,22,152),(5,33,150),(0,0,0),(0,0,154),(0,1,154),(0,0,0),(0,0,0),(0,2,154),(1,2,154),(0,39,149),(0,0,0),(2,0,154),(0,3,154),(0,0,0),(0,0,0),(2,2,154),(0,25,152),(1,25,152),(0,0,0),(0,4,154),(0,18,153),(0,0,0),(0,0,0),(7,17,152),(2,25,152),(10,63,137),(0,0,0),(2,4,154),(0,5,154),(0,0,0),(0,0,0),(3,1,154),(5,48,146),(6,11,153),(0,0,0),(8,50,144),(2,5,154),(0,0,0),(0,0,0),(0,6,154),(0,43,148),(1,43,148),(0,0,0),(3,25,152),(8,58,141),(0,0,0),(0,0,0),(2,6,154),(0,55,144),(0,31,151),(0,0,0),(0,60,142),(0,7,154),(0,0,0),(0,0,0),(3,5,154),(2,55,144),(0,19,153),(0,0,0),(2,60,142),(0,78,133),(0,0,0),(0,0,0),(11,67,134),(5,54,144),(0,93,123),(0,0,0),(0,8,154),(1,8,154),(0,0,0),(0,0,0),(4,2,154),(6,63,140),(2,93,123),(0,0,0),(2,8,154),(0,83,130),(0,0,0),(0,0,0),(3,7,154),(4,25,152),(0,105,113),(0,0,0),(0,36,150),(0,9,154),(0,0,0),(0,0,0),(3,78,133),(0,40,149),(1,40,149),(0,0,0),(2,36,150),(0,69,138),(0,0,0),(0,0,0),(7,19,152),(0,20,153),(0,67,139),(0,0,0),(0,104,114),(0,58,143),(0,0,0),(0,0,0),(0,10,154),(1,10,154),(0,47,147),(0,0,0),(2,104,114),(2,58,143),(0,0,0),(0,0,0),(0,80,132),(0,32,151),(1,32,151),(0,0,0),(3,40,149),(4,7,154),(0,0,0),(0,0,0),(2,80,132),(0,27,152),(0,53,145),(0,0,0),(3,20,153),(0,11,154),(0,0,0),(0,0,0),(0,44,148),(1,44,148),(2,53,145),(0,0,0),(4,8,154),(2,11,154),(0,0,0),(0,0,0),(2,44,148),(6,23,152),(0,21,153),(0,0,0),(3,32,151),(4,83,130),(0,0,0),(0,0,0),(10,70,134),(0,96,121),(1,96,121),(0,0,0),(0,12,154),(1,12,154),(0,0,0),(0,0,0),(3,11,154),(2,96,121),(0,85,129),(0,0,0),(2,12,154),(0,37,150),(0,0,0),(0,0,0),(0,56,144),(0,88,127),(1,88,127),(0,0,0),(4,104,114),(2,37,150),(0,0,0),(0,0,0),(2,56,144),(2,88,127),(0,41,149),(0,0,0),(3,96,121),(0,13,154),(0,0,0),(0,0,0),(0,28,152),(1,28,152),(0,33,151),(0,0,0),(7,107,110),(0,22,153),(0,0,0),(0,0,0),(2,28,152),(4,27,152),(2,33,151),(0,0,0),(3,88,127),(2,22,153),(0,0,0),(0,0,0),(4,44,148),(5,8,154),(0,91,125),(0,0,0),(8,70,136),(0,95,122),(0,0,0),(0,0,0),(0,14,154),(0,48,147),(1,48,147),(0,0,0),(10,40,146),(0,51,146),(0,0,0),(0,0,0),(2,14,154),(2,48,147),(5,9,154),(0,0,0),(0,100,118),(1,100,118),(0,0,0),(0,0,0),(7,28,151),(0,45,148),(0,59,143),(0,0,0),(2,100,118),(3,91,125),(0,0,0),(0,0,0),(3,95,122),(2,45,148),(0,23,153),(0,0,0),(3,48,147),(0,15,154),(0,0,0),(0,0,0),(0,38,150),(0,29,152),(1,29,152),(0,0,0),(6,4,154),(2,15,154),(0,0,0),(0,0,0),(2,38,150),(0,72,137),(1,72,137),(0,0,0),(0,66,140),(0,34,151),(0,0,0),(0,0,0),(19,35,126),(2,72,137),(0,99,119),(0,0,0),(2,66,140),(0,42,149),(0,0,0),(0,0,0),(3,15,154),(6,43,148),(2,99,119),(0,0,0),(0,16,154),(1,16,154),(0,0,0),(0,0,0),(0,90,126),(0,64,141),(1,64,141),(0,0,0),(2,16,154),(0,109,110),(0,0,0),(0,0,0),(2,90,126),(0,24,153),(1,24,153),(0,0,0),(4,100,118),(2,109,110),(0,0,0),(0,0,0),(3,42,149),(0,107,112),(1,107,112),(0,0,0),(6,8,154),(5,56,144),(0,0,0),(0,0,0)]

def wits_24 : List (ℕ × ℕ × ℕ) := [(7,91,124),(0,76,135),(1,76,135),(0,0,0),(0,30,152),(0,17,154),(0,0,0),(0,0,0),(0,62,142),(1,62,142),(0,49,147),(0,0,0),(2,30,152),(2,17,154),(0,0,0),(0,0,0),(2,62,142),(4,72,137),(2,49,147),(0,0,0),(0,46,148),(0,39,150),(0,0,0),(0,0,0),(19,2,131),(0,0,155),(0,1,155),(0,0,0),(2,46,148),(0,2,155),(0,0,0),(0,0,0),(3,17,154),(2,0,155),(0,3,155),(0,0,0),(4,16,154),(0,86,129),(0,0,0),(0,0,0),(0,18,154),(0,4,155),(1,4,155),(0,0,0),(7,30,151),(2,86,129),(0,0,0),(0,0,0),(2,18,154),(0,60,143),(0,5,155),(0,0,0),(3,0,155),(3,1,155),(0,0,0),(0,0,0),(3,2,155),(2,60,143),(2,5,155),(0,0,0),(7,1,154),(0,6,155),(0,0,0),(0,0,0),(3,86,129),(0,31,152),(1,31,152),(0,0,0),(3,4,155),(2,6,155),(0,0,0),(0,0,0),(4,62,142),(2,31,152),(0,7,155),(0,0,0),(3,60,143),(0,19,154),(0,0,0),(0,0,0),(10,42,146),(5,66,140),(0,69,139),(0,0,0),(4,46,148),(0,26,153),(0,0,0),(0,0,0),(3,6,155),(0,8,155),(1,8,155),(0,0,0),(3,31,152),(0,102,117),(0,0,0),(0,0,0),(7,43,148),(0,36,151),(0,73,137),(0,0,0),(0,40,150),(1,40,150),(0,0,0),(0,0,0),(3,19,154),(2,36,151),(0,9,155),(0,0,0),(2,40,150),(0,50,147),(0,0,0),(0,0,0),(3,26,153),(0,47,148),(1,47,148),(0,0,0),(0,20,154),(1,20,154),(0,0,0),(0,0,0),(3,102,117),(0,75,136),(1,75,136),(0,0,0),(2,20,154),(0,10,155),(0,0,0),(0,0,0),(0,32,152),(1,32,152),(5,17,154),(0,0,0),(7,83,130),(0,63,142),(0,0,0),(0,0,0),(2,32,152),(0,44,149),(0,27,153),(0,0,0),(3,47,148),(2,63,142),(0,0,0),(0,0,0),(7,40,149),(2,44,149),(0,11,155),(0,0,0),(0,82,132),(1,82,132),(0,0,0),(0,0,0),(3,10,155),(4,8,155),(0,77,135),(0,0,0),(2,82,132),(0,21,154),(0,0,0),(0,0,0),(3,63,142),(0,56,145),(1,56,145),(0,0,0),(3,44,149),(2,21,154),(0,0,0),(0,0,0),(7,32,151),(0,12,155),(0,37,151),(0,0,0),(6,66,140),(3,11,155),(0,0,0),(0,0,0),(7,27,152),(2,12,155),(2,37,151),(0,0,0),(4,20,154),(0,41,150),(0,0,0),(0,0,0),(3,21,154),(4,75,136),(5,6,155),(0,0,0),(3,56,145),(2,41,150),(0,0,0),(0,0,0),(4,32,152),(0,28,153),(0,13,155),(0,0,0),(3,12,155),(0,79,134),(0,0,0),(0,0,0),(0,22,154),(0,99,120),(0,109,111),(0,0,0),(10,10,152),(2,79,134),(0,0,0),(0,0,0),(0,48,148),(1,48,148),(0,51,147),(0,0,0),(0,94,124),(1,94,124),(0,0,0),(0,0,0),(2,48,148),(0,59,144),(0,107,113),(0,0,0),(2,94,124),(0,14,155),(0,0,0),(0,0,0),(0,68,140),(1,68,140),(0,45,149),(0,0,0),(0,72,138),(0,90,127),(0,0,0),(0,0,0),(0,54,146),(1,54,146),(2,45,149),(0,0,0),(2,72,138),(0,66,141),(0,0,0),(0,0,0),(2,54,146),(5,20,154),(6,1,155),(0,0,0),(3,59,144),(0,23,154),(0,0,0),(0,0,0),(3,14,155),(7,91,125),(0,15,155),(0,0,0),(7,95,122),(2,23,154),(0,0,0),(0,0,0),(3,90,127),(4,28,153),(2,15,155),(0,0,0),(0,34,152),(1,34,152),(0,0,0),(0,0,0),(0,42,150),(1,42,150),(4,109,111),(0,0,0),(2,34,152),(10,65,138),(0,0,0),(0,0,0),(0,76,136),(1,76,136),(0,57,145),(0,0,0),(4,94,124),(3,15,155),(0,0,0),(0,0,0),(2,76,136),(0,16,155),(1,16,155),(0,0,0),(7,15,154),(4,14,155),(0,0,0),(0,0,0),(4,68,140),(2,16,155),(4,45,149),(0,0,0),(0,24,154),(0,62,143),(0,0,0),(0,0,0),(0,86,130),(1,86,130),(0,103,117),(0,0,0),(2,24,154),(2,62,143),(0,0,0),(0,0,0),(2,86,130),(0,49,148),(1,49,148),(0,0,0),(3,16,155),(0,30,153),(0,0,0),(0,0,0),(14,72,128),(0,52,147),(0,17,155),(0,0,0),(6,40,150),(0,46,149),(0,0,0),(0,0,0),(3,62,143),(2,52,147),(0,39,151),(0,0,0),(4,34,152),(2,46,149),(0,0,0),(0,0,0),(0,102,118),(0,35,152),(1,35,152),(0,0,0),(3,49,148),(5,48,148),(0,0,0),(0,0,0),(0,0,156),(0,1,156),(1,1,156),(0,0,0),(0,2,156),(0,25,154),(0,0,0),(0,0,0),(2,0,156),(0,3,156),(1,3,156),(0,0,0),(2,2,156),(0,18,155),(0,0,0),(0,0,0),(0,4,156),(1,4,156),(5,90,127),(0,0,0),(0,80,134),(1,80,134),(0,0,0),(0,0,0),(2,4,156),(0,5,156),(0,71,139),(0,0,0),(2,80,134),(10,54,143),(0,0,0),(0,0,0),(3,25,154),(2,5,156),(0,31,153),(0,0,0),(0,6,156),(0,73,138),(0,0,0),(0,0,0),(3,18,155),(4,52,147),(2,31,153),(0,0,0),(2,6,156),(2,73,138),(0,0,0),(0,0,0),(7,4,155),(0,7,156),(0,19,155),(0,0,0),(3,5,156),(0,58,145),(0,0,0),(0,0,0),(0,26,154),(1,26,154),(0,75,137),(0,0,0),(10,70,136),(2,58,145),(0,0,0),(0,0,0),(0,8,156),(0,40,151),(1,40,151),(0,0,0),(0,50,148),(1,50,148),(0,0,0),(0,0,0),(2,8,156),(2,40,151),(0,47,149),(0,0,0),(2,50,148),(0,82,133),(0,0,0),(0,0,0),(3,58,145),(0,9,156),(0,53,147),(0,0,0),(4,80,134),(0,110,111),(0,0,0),(0,0,0),(6,48,148),(0,20,155),(1,20,155),(0,0,0),(3,40,151),(2,110,111),(0,0,0),(0,0,0),(7,8,155),(0,32,153),(1,32,153),(0,0,0),(0,10,156),(1,10,156),(0,0,0),(0,0,0),(3,82,133),(2,32,153),(0,99,121),(0,0,0),(2,10,156),(0,27,154),(0,0,0),(0,0,0),(3,110,111),(4,7,156),(2,99,121),(0,0,0),(0,56,146),(1,56,146),(0,0,0),(0,0,0),(4,26,154),(0,11,156),(1,11,156),(0,0,0),(2,56,146),(0,94,125),(0,0,0),(0,0,0),(4,8,156),(2,11,156),(0,21,155),(0,0,0),(4,50,148),(0,87,130),(0,0,0),(0,0,0),(3,27,154),(0,37,152),(1,37,152),(0,0,0),(6,34,152),(2,87,130),(0,0,0),(0,0,0),(0,12,156),(0,105,116),(0,41,151),(0,0,0),(0,90,128),(1,90,128),(0,0,0),(0,0,0),(0,98,122),(1,98,122),(2,41,151),(0,0,0),(2,90,128),(3,21,155),(0,0,0),(0,0,0),(2,98,122),(4,32,153),(0,33,153),(0,0,0),(0,28,154),(1,28,154),(0,0,0),(0,0,0),(7,56,145),(0,13,156),(0,59,145),(0,0,0),(2,28,154),(0,22,155),(0,0,0),(0,0,0),(6,86,130),(2,13,156),(2,59,145),(0,0,0),(4,56,146),(0,81,134),(0,0,0),(0,0,0),(0,66,142),(1,66,142),(8,49,147),(0,0,0),(7,41,150),(0,45,150),(0,0,0),(0,0,0),(2,66,142),(5,50,148),(4,21,155),(0,0,0),(0,14,156),(0,103,118),(0,0,0),(0,0,0),(3,22,155),(4,37,152),(0,97,123),(0,0,0),(2,14,156),(2,103,118),(0,0,0),(0,0,0),(3,81,134),(0,64,143),(1,64,143),(0,0,0),(0,38,152),(1,38,152),(0,0,0),(0,0,0),(3,45,150),(2,64,143),(0,23,155),(0,0,0),(2,38,152),(0,29,154),(0,0,0),(0,0,0),(3,103,118),(0,15,156),(0,89,129),(0,0,0),(4,28,154),(0,34,153),(0,0,0),(0,0,0),(6,4,156),(2,15,156),(2,89,129),(0,0,0),(3,64,143),(2,34,153),(0,0,0),(0,0,0),(11,58,141),(5,56,146),(0,83,133),(0,0,0),(0,62,144),(1,62,144),(0,0,0),(0,0,0),(3,29,154),(10,28,151),(2,83,133),(0,0,0),(2,62,144),(3,89,129),(0,0,0),(0,0,0),(0,16,156),(0,92,127),(1,92,127),(0,0,0),(4,14,156),(4,103,118),(0,0,0),(0,0,0),(2,16,156),(0,24,155),(0,49,149),(0,0,0),(11,13,152),(3,83,133),(0,0,0),(0,0,0),(0,52,148),(1,52,148),(2,49,149),(0,0,0),(4,38,152),(5,98,122),(0,0,0),(0,0,0),(0,30,154),(1,30,154),(4,23,155),(0,0,0),(3,92,127),(4,29,154),(0,0,0),(0,0,0),(2,30,154),(0,17,156),(1,17,156),(0,0,0),(3,24,155),(3,49,149),(0,0,0),(0,0,0),(15,44,139),(2,17,156),(0,35,153),(0,0,0),(7,62,143),(6,110,111),(0,0,0),(0,0,0),(8,32,152),(0,71,140),(0,69,141),(0,0,0),(0,88,130),(1,88,130),(0,0,0),(0,0,0),(7,49,148),(0,0,157),(0,1,157),(0,0,0),(2,88,130),(0,2,157),(0,0,0),(0,0,0),(4,16,156),(2,0,157),(0,3,157),(0,0,0),(0,18,156),(1,18,156),(0,0,0),(0,0,0),(11,97,118),(0,4,157),(1,4,157),(0,0,0),(2,18,156),(0,75,138),(0,0,0),(0,0,0),(4,52,148),(2,4,157),(0,5,157),(0,0,0),(3,0,157),(0,31,154),(0,0,0),(0,0,0),(0,58,146),(1,58,146),(2,5,157),(0,0,0),(7,25,154),(0,6,157),(0,0,0),(0,0,0),(2,58,146),(4,17,156),(5,34,153),(0,0,0),(0,106,116),(1,106,116),(0,0,0),(0,0,0),(3,75,138),(0,19,156),(0,7,157),(0,0,0),(2,106,116),(0,26,155),(0,0,0),(0,0,0),(0,40,152),(0,36,153),(1,36,153),(0,0,0),(4,88,130),(0,47,150),(0,0,0),(0,0,0),(0,94,126),(0,8,157),(0,105,117),(0,0,0),(6,28,154),(2,47,150),(0,0,0),(0,0,0),(2,94,126),(2,8,157),(2,105,117),(0,0,0),(3,19,156),(3,7,157),(0,0,0),(0,0,0),(3,26,155),(4,4,157),(0,9,157),(0,0,0),(3,36,153),(0,98,123),(0,0,0),(0,0,0),(0,20,156),(0,44,151),(1,44,151),(0,0,0),(0,32,154),(0,90,129),(0,0,0),(0,0,0),(2,20,156),(0,56,147),(0,61,145),(0,0,0),(2,32,154),(0,10,157),(0,0,0),(0,0,0),(10,6,154),(2,56,147),(0,27,155),(0,0,0),(4,106,116),(2,10,157),(0,0,0),(0,0,0),(3,98,123),(4,19,156),(2,27,155),(0,0,0),(3,44,151),(4,26,155),(0,0,0),(0,0,0),(3,90,129),(4,36,153),(0,11,157),(0,0,0),(3,56,147),(3,61,145),(0,0,0),(0,0,0),(3,10,157),(0,21,156),(0,37,153),(0,0,0),(10,8,154),(0,70,141),(0,0,0),(0,0,0),(0,72,140),(0,41,152),(0,81,135),(0,0,0),(0,68,142),(1,68,142),(0,0,0),(0,0,0),(2,72,140),(0,12,157),(1,12,157),(0,0,0),(2,68,142),(0,59,146),(0,0,0),(0,0,0),(4,20,156),(2,12,157),(0,51,149),(0,0,0),(0,48,150),(0,33,154),(0,0,0),(0,0,0),(3,70,141),(0,28,155),(1,28,155),(0,0,0),(2,48,150),(2,33,154),(0,0,0),(0,0,0),(7,37,152),(2,28,155),(0,13,157),(0,0,0),(0,22,156),(0,89,130),(0,0,0),(0,0,0),(3,59,146),(7,41,151),(0,45,151),(0,0,0),(2,22,156),(2,89,130),(0,0,0),(0,0,0),(0,64,144),(1,64,144),(2,45,151),(0,0,0),(3,28,155),(5,94,126),(0,0,0),(0,0,0),(2,64,144),(0,96,125),(0,101,121),(0,0,0),(14,14,148),(0,14,157),(0,0,0),(0,0,0),(0,92,128),(1,92,128),(2,101,121),(0,0,0),(4,68,142),(0,38,153),(0,0,0),(0,0,0),(2,92,128),(4,12,157),(0,57,147),(0,0,0),(6,88,130),(2,38,153),(0,0,0),(0,0,0),(8,4,156),(0,23,156),(0,29,155),(0,0,0),(0,42,152),(0,62,145),(0,0,0),(0,0,0),(0,34,154),(1,34,154),(0,15,157),(0,0,0),(2,42,152),(0,109,114),(0,0,0),(0,0,0),(2,34,154),(6,4,157),(2,15,157),(0,0,0),(0,100,122),(1,100,122),(0,0,0),(0,0,0),(7,64,143),(0,108,115),(1,108,115),(0,0,0),(2,100,122),(3,29,155),(0,0,0),(0,0,0),(0,80,136),(1,80,136),(8,19,155),(0,0,0),(7,29,154),(0,49,150),(0,0,0),(0,0,0),(2,80,136),(0,16,157),(1,16,157),(0,0,0),(6,106,116),(2,49,150),(0,0,0),(0,0,0),(0,24,156),(1,24,156),(0,85,133),(0,0,0),(0,60,146),(0,46,151),(0,0,0),(0,0,0),(2,24,156),(6,36,153),(0,71,141),(0,0,0),(2,60,146),(0,30,155),(0,0,0),(0,0,0),(3,49,150),(0,55,148),(0,39,153),(0,0,0),(3,16,157),(2,30,155),(0,0,0),(0,0,0),(4,34,154),(2,55,148),(0,17,157),(0,0,0),(11,85,128),(0,35,154),(0,0,0),(0,0,0),(3,46,151),(5,22,156),(0,75,139),(0,0,0),(4,100,122),(0,82,135),(0,0,0),(0,0,0),(3,30,155),(0,43,152),(1,43,152),(0,0,0),(3,55,148),(2,82,135),(0,0,0),(0,0,0),(4,80,136),(0,25,156),(1,25,156),(0,0,0),(0,0,158),(0,1,158),(0,0,0),(0,0,0),(0,2,158),(1,2,158),(5,14,157),(0,0,0),(2,0,158),(0,3,158),(0,0,0),(0,0,0),(2,2,158),(0,104,119),(1,104,119),(0,0,0),(0,4,158),(1,4,158),(0,0,0),(0,0,0),(7,71,140),(2,104,119),(0,31,155),(0,0,0),(2,4,158),(0,5,158),(0,0,0),(0,0,0),(3,1,158),(0,87,132),(0,63,145),(0,0,0),(7,2,157),(2,5,158),(0,0,0),(0,0,0)]

def wits_25 : List (ℕ × ℕ × ℕ) := [(0,6,158),(1,6,158),(2,63,145),(0,0,0),(3,104,119),(4,35,154),(0,0,0),(0,0,0),(2,6,158),(0,40,153),(0,19,157),(0,0,0),(0,26,156),(0,7,158),(0,0,0),(0,0,0),(3,5,158),(2,40,153),(2,19,157),(0,0,0),(2,26,156),(2,7,158),(0,0,0),(0,0,0),(14,46,142),(4,25,156),(5,49,150),(0,0,0),(0,8,158),(1,8,158),(0,0,0),(0,0,0),(4,2,158),(0,93,128),(0,97,125),(0,0,0),(2,8,158),(0,61,146),(0,0,0),(0,0,0),(0,44,152),(1,44,152),(2,97,125),(0,0,0),(4,4,158),(0,9,158),(0,0,0),(0,0,0),(2,44,152),(0,20,157),(1,20,157),(0,0,0),(7,47,150),(2,9,158),(0,0,0),(0,0,0),(7,8,157),(0,81,136),(1,81,136),(0,0,0),(3,93,128),(3,97,125),(0,0,0),(0,0,0),(0,10,158),(0,27,156),(1,27,156),(0,0,0),(14,70,132),(6,38,153),(0,0,0),(0,0,0),(2,10,158),(0,68,143),(1,68,143),(0,0,0),(0,74,140),(1,74,140),(0,0,0),(0,0,0),(7,44,151),(2,68,143),(0,89,131),(0,0,0),(2,74,140),(0,11,158),(0,0,0),(0,0,0),(0,112,112),(1,112,112),(0,21,157),(0,0,0),(0,66,144),(1,66,144),(0,0,0),(0,0,0),(0,110,114),(0,76,139),(1,76,139),(0,0,0),(2,66,144),(0,51,150),(0,0,0),(0,0,0),(2,110,114),(0,48,151),(0,109,115),(0,0,0),(0,12,158),(1,12,158),(0,0,0),(0,0,0),(3,11,158),(2,48,151),(0,33,155),(0,0,0),(2,12,158),(0,54,149),(0,0,0),(0,0,0),(0,28,156),(0,64,145),(1,64,145),(0,0,0),(3,76,139),(2,54,149),(0,0,0),(0,0,0),(0,78,138),(0,45,152),(1,45,152),(0,0,0),(3,48,151),(0,13,158),(0,0,0),(0,0,0),(2,78,138),(2,45,152),(0,107,117),(0,0,0),(4,74,140),(2,13,158),(0,0,0),(0,0,0),(3,54,149),(6,55,148),(2,107,117),(0,0,0),(3,64,145),(4,11,158),(0,0,0),(0,0,0),(4,112,112),(0,57,148),(0,95,127),(0,0,0),(3,45,152),(6,35,154),(0,0,0),(0,0,0),(0,14,158),(1,14,158),(2,95,127),(0,0,0),(7,89,130),(3,107,117),(0,0,0),(0,0,0),(0,88,132),(0,80,137),(1,80,137),(0,0,0),(4,12,158),(0,42,153),(0,0,0),(0,0,0),(2,88,132),(0,29,156),(0,23,157),(0,0,0),(3,57,148),(0,34,155),(0,0,0),(0,0,0),(4,28,156),(2,29,156),(0,105,119),(0,0,0),(7,14,157),(0,15,158),(0,0,0),(0,0,0),(4,78,138),(4,45,152),(2,105,119),(0,0,0),(3,80,137),(2,15,158),(0,0,0),(0,0,0),(3,42,153),(5,74,140),(0,49,151),(0,0,0),(0,52,150),(0,71,142),(0,0,0),(0,0,0),(3,34,155),(0,60,147),(0,69,143),(0,0,0),(2,52,150),(2,71,142),(0,0,0),(0,0,0),(0,104,120),(1,104,120),(2,69,143),(0,0,0),(0,16,158),(1,16,158),(0,0,0),(0,0,0),(2,104,120),(0,24,157),(0,55,149),(0,0,0),(2,16,158),(0,98,125),(0,0,0),(0,0,0),(3,71,142),(2,24,157),(2,55,149),(0,0,0),(0,30,156),(0,39,154),(0,0,0),(0,0,0),(11,95,122),(4,29,156),(4,23,157),(0,0,0),(2,30,156),(2,39,154),(0,0,0),(0,0,0),(7,16,157),(6,93,128),(0,35,155),(0,0,0),(3,24,157),(0,17,158),(0,0,0),(0,0,0),(3,98,125),(7,85,133),(0,43,153),(0,0,0),(7,46,151),(0,90,131),(0,0,0),(0,0,0),(3,39,154),(6,20,157),(2,43,153),(0,0,0),(0,58,148),(1,58,148),(0,0,0),(0,0,0),(7,55,148),(4,60,147),(0,25,157),(0,0,0),(2,58,148),(3,35,155),(0,0,0),(0,0,0),(3,17,158),(0,0,159),(0,1,159),(0,0,0),(4,16,158),(0,2,159),(0,0,0),(0,0,0),(0,18,158),(1,18,158),(0,3,159),(0,0,0),(6,74,140),(2,2,159),(0,0,0),(0,0,0),(2,18,158),(0,4,159),(1,4,159),(0,0,0),(4,30,156),(0,50,151),(0,0,0),(0,0,0),(6,112,112),(2,4,159),(0,5,159),(0,0,0),(3,0,159),(0,53,150),(0,0,0),(0,0,0),(3,2,159),(0,47,152),(1,47,152),(0,0,0),(0,40,154),(0,6,159),(0,0,0),(0,0,0),(7,104,119),(0,36,155),(1,36,155),(0,0,0),(2,40,154),(0,19,158),(0,0,0),(0,0,0),(3,50,151),(2,36,155),(0,7,159),(0,0,0),(4,58,148),(2,19,158),(0,0,0),(0,0,0),(3,53,150),(0,56,149),(1,56,149),(0,0,0),(3,47,152),(5,104,120),(0,0,0),(0,0,0),(3,6,159),(0,8,159),(1,8,159),(0,0,0),(0,72,142),(0,70,143),(0,0,0),(0,0,0),(0,86,134),(0,108,117),(1,108,117),(0,0,0),(2,72,142),(0,74,141),(0,0,0),(0,0,0),(0,32,156),(1,32,156),(0,9,159),(0,0,0),(0,20,158),(1,20,158),(0,0,0),(0,0,0),(2,32,156),(6,57,148),(2,9,159),(0,0,0),(2,20,158),(0,107,118),(0,0,0),(0,0,0),(0,76,140),(1,76,140),(0,27,157),(0,0,0),(3,108,117),(0,10,159),(0,0,0),(0,0,0),(2,76,140),(0,59,148),(1,59,148),(0,0,0),(7,9,158),(2,10,159),(0,0,0),(0,0,0),(7,20,157),(2,59,148),(0,37,155),(0,0,0),(8,100,122),(0,41,154),(0,0,0),(0,0,0),(3,107,118),(4,56,149),(0,11,159),(0,0,0),(10,50,148),(0,21,158),(0,0,0),(0,0,0),(0,48,152),(0,95,128),(1,95,128),(0,0,0),(0,64,146),(1,64,146),(0,0,0),(0,0,0),(0,54,150),(1,54,150),(6,49,151),(0,0,0),(2,64,146),(3,37,155),(0,0,0),(0,0,0),(2,54,150),(0,12,159),(0,99,125),(0,0,0),(4,20,158),(3,11,159),(0,0,0),(0,0,0),(3,21,158),(0,28,157),(0,45,153),(0,0,0),(3,95,128),(4,107,118),(0,0,0),(0,0,0),(4,76,140),(2,28,157),(0,91,131),(0,0,0),(0,80,138),(1,80,138),(0,0,0),(0,0,0),(0,22,158),(1,22,158),(0,13,159),(0,0,0),(2,80,138),(0,62,147),(0,0,0),(0,0,0),(2,22,158),(0,104,121),(1,104,121),(0,0,0),(3,28,157),(2,62,147),(0,0,0),(0,0,0),(7,64,145),(2,104,121),(4,11,159),(0,0,0),(11,44,149),(0,38,155),(0,0,0),(0,0,0),(4,48,152),(4,95,128),(5,70,143),(0,0,0),(4,64,146),(0,14,159),(0,0,0),(0,0,0),(0,42,154),(1,42,154),(5,74,141),(0,0,0),(3,104,121),(2,14,159),(0,0,0),(0,0,0),(2,42,154),(4,12,159),(0,29,157),(0,0,0),(0,34,156),(0,23,158),(0,0,0),(0,0,0),(3,38,155),(0,69,144),(1,69,144),(0,0,0),(2,34,156),(2,23,158),(0,0,0),(0,0,0),(0,60,148),(0,49,152),(0,15,159),(0,0,0),(4,80,138),(10,22,155),(0,0,0),(0,0,0),(2,60,148),(2,49,152),(0,67,145),(0,0,0),(7,42,153),(3,29,157),(0,0,0),(0,0,0),(3,23,158),(4,104,121),(2,67,145),(0,0,0),(0,90,132),(0,46,153),(0,0,0),(0,0,0),(11,79,134),(0,77,140),(1,77,140),(0,0,0),(2,90,132),(0,102,123),(0,0,0),(0,0,0),(20,56,120),(0,16,159),(0,97,127),(0,0,0),(0,24,158),(0,65,146),(0,0,0),(0,0,0),(4,42,154),(2,16,159),(0,39,155),(0,0,0),(2,24,158),(0,30,157),(0,0,0),(0,0,0),(0,84,136),(1,84,136),(2,39,155),(0,0,0),(0,110,116),(1,110,116),(0,0,0),(0,0,0),(2,84,136),(0,35,156),(0,79,139),(0,0,0),(2,110,116),(0,43,154),(0,0,0),(0,0,0),(3,65,146),(2,35,156),(0,17,159),(0,0,0),(7,98,125),(2,43,154),(0,0,0),(0,0,0),(3,30,157),(0,101,124),(0,63,147),(0,0,0),(6,20,158),(11,15,155),(0,0,0),(0,0,0),(23,51,104),(2,101,124),(2,63,147),(0,0,0),(0,108,118),(0,25,158),(0,0,0),(0,0,0),(3,43,154),(4,77,140),(5,38,155),(0,0,0),(2,108,118),(2,25,158),(0,0,0),(0,0,0),(0,0,160),(0,1,160),(1,1,160),(0,0,0),(0,2,160),(0,18,159),(0,0,0),(0,0,0),(2,0,160),(0,3,160),(0,31,157),(0,0,0),(2,2,160),(2,18,159),(0,0,0),(0,0,0),(0,4,160),(1,4,160),(0,47,153),(0,0,0),(4,110,116),(0,86,135),(0,0,0),(0,0,0),(2,4,160),(0,5,160),(1,5,160),(0,0,0),(3,1,160),(2,86,135),(0,0,0),(0,0,0),(0,36,156),(0,72,143),(1,72,143),(0,0,0),(0,6,160),(1,6,160),(0,0,0),(0,0,0),(0,26,158),(1,26,158),(0,19,159),(0,0,0),(2,6,160),(3,47,153),(0,0,0),(0,0,0),(2,26,158),(0,7,160),(1,7,160),(0,0,0),(0,44,154),(1,44,154),(0,0,0),(0,0,0),(7,47,152),(0,76,141),(0,83,137),(0,0,0),(2,44,154),(21,4,128),(0,0,0),(0,0,0),(0,8,160),(1,8,160),(0,95,129),(0,0,0),(4,2,160),(3,19,159),(0,0,0),(0,0,0),(0,66,146),(0,32,157),(1,32,157),(0,0,0),(3,7,160),(0,99,126),(0,0,0),(0,0,0),(2,66,146),(0,9,160),(0,59,149),(0,0,0),(0,78,140),(1,78,140),(0,0,0),(0,0,0),(7,8,159),(2,9,160),(2,59,149),(0,0,0),(2,78,140),(0,27,158),(0,0,0),(0,0,0),(4,36,156),(4,72,143),(8,105,119),(0,0,0),(0,10,160),(1,10,160),(0,0,0),(0,0,0),(3,99,126),(0,37,156),(0,41,155),(0,0,0),(2,10,160),(3,59,149),(0,0,0),(0,0,0),(10,94,126),(0,48,153),(1,48,153),(0,0,0),(4,44,154),(0,54,151),(0,0,0),(0,0,0),(3,27,158),(0,11,160),(0,21,159),(0,0,0),(7,10,159),(2,54,151),(0,0,0),(0,0,0),(4,8,160),(2,11,160),(2,21,159),(0,0,0),(3,37,156),(0,98,127),(0,0,0),(0,0,0),(0,94,130),(1,94,130),(0,33,157),(0,0,0),(3,48,153),(0,45,154),(0,0,0),(0,0,0),(0,12,160),(1,12,160),(2,33,157),(0,0,0),(0,28,158),(0,57,150),(0,0,0),(0,0,0),(2,12,160),(6,16,159),(6,97,127),(0,0,0),(2,28,158),(2,57,150),(0,0,0),(0,0,0),(3,98,127),(5,6,160),(6,39,155),(0,0,0),(4,10,160),(0,22,159),(0,0,0),(0,0,0),(0,82,138),(0,13,160),(1,13,160),(0,0,0),(6,110,116),(2,22,159),(0,0,0),(0,0,0),(2,82,138),(0,71,144),(0,73,143),(0,0,0),(0,38,156),(1,38,156),(0,0,0),(0,0,0),(10,72,140),(2,71,144),(0,69,145),(0,0,0),(2,38,156),(0,42,155),(0,0,0),(0,0,0),(3,22,159),(0,97,128),(0,87,135),(0,0,0),(0,14,160),(1,14,160),(0,0,0),(0,0,0),(4,94,130),(0,60,149),(1,60,149),(0,0,0),(2,14,160),(0,29,158),(0,0,0),(0,0,0),(0,52,152),(1,52,152),(0,23,159),(0,0,0),(4,28,158),(2,29,158),(0,0,0),(0,0,0),(2,52,152),(6,1,160),(2,23,159),(0,0,0),(3,97,128),(3,87,135),(0,0,0),(0,0,0),(14,42,146),(0,15,160),(0,55,151),(0,0,0),(3,60,149),(4,22,159),(0,0,0),(0,0,0),(0,46,154),(1,46,154),(0,65,147),(0,0,0),(7,23,158),(3,23,159),(0,0,0),(0,0,0),(2,46,154),(0,79,140),(1,79,140),(0,0,0),(4,38,156),(10,14,157),(0,0,0),(0,0,0),(6,36,156),(0,107,120),(1,107,120),(0,0,0),(3,15,160),(3,55,151),(0,0,0),(0,0,0),(0,16,160),(0,24,159),(1,24,159),(0,0,0),(4,14,160),(3,65,147),(0,0,0),(0,0,0),(0,30,158),(1,30,158),(5,45,154),(0,0,0),(3,79,140),(4,29,158),(0,0,0),(0,0,0),(2,30,158),(0,63,148),(0,35,157),(0,0,0),(0,100,126),(0,89,134),(0,0,0),(0,0,0),(6,8,160),(2,63,148),(0,81,139),(0,0,0),(2,100,126),(2,89,134),(0,0,0),(0,0,0),(0,92,132),(0,17,160),(1,17,160),(0,0,0),(0,86,136),(1,86,136),(0,0,0),(0,0,0),(2,92,132),(2,17,160),(4,65,147),(0,0,0),(2,86,136),(3,35,157),(0,0,0),(0,0,0),(3,89,134),(4,79,140),(0,25,159),(0,0,0),(7,43,154),(0,50,153),(0,0,0),(0,0,0),(10,24,156),(0,53,152),(1,53,152),(0,0,0),(3,17,160),(2,50,153),(0,0,0),(0,0,0),(0,72,144),(0,0,161),(0,1,161),(0,0,0),(0,18,160),(0,2,161),(0,0,0),(0,0,0),(2,72,144),(2,0,161),(0,3,161),(0,0,0),(2,18,160),(0,83,138),(0,0,0),(0,0,0),(0,40,156),(0,4,161),(1,4,161),(0,0,0),(0,68,146),(1,68,146),(0,0,0),(0,0,0),(2,40,156),(0,36,157),(0,5,161),(0,0,0),(2,68,146),(3,1,161),(0,0,0),(0,0,0),(3,2,161),(2,36,157),(2,5,161),(0,0,0),(4,86,136),(0,6,161),(0,0,0),(0,0,0),(3,83,138),(0,19,160),(1,19,160),(0,0,0),(3,4,161),(0,66,147),(0,0,0),(0,0,0),(7,5,160),(0,88,135),(0,7,161),(0,0,0),(3,36,157),(2,66,147),(0,0,0),(0,0,0),(7,72,143),(2,88,135),(2,7,161),(0,0,0),(10,4,158),(0,59,150),(0,0,0),(0,0,0),(3,6,161),(0,8,161),(1,8,161),(0,0,0),(0,32,158),(1,32,158),(0,0,0),(0,0,0),(0,114,114),(1,114,114),(0,85,137),(0,0,0),(2,32,158),(0,94,131),(0,0,0),(0,0,0)]

def wits_26 : List (ℕ × ℕ × ℕ) := [(0,20,160),(1,20,160),(0,9,161),(0,0,0),(4,68,146),(2,94,131),(0,0,0),(0,0,0),(2,20,160),(4,36,157),(0,27,159),(0,0,0),(3,8,161),(5,92,132),(0,0,0),(0,0,0),(7,32,157),(0,41,156),(0,37,157),(0,0,0),(0,48,154),(0,10,161),(0,0,0),(0,0,0),(0,110,118),(1,110,118),(2,37,157),(0,0,0),(2,48,154),(0,102,125),(0,0,0),(0,0,0),(2,110,118),(4,88,135),(4,7,161),(0,0,0),(7,27,158),(2,102,125),(0,0,0),(0,0,0),(10,44,152),(0,21,160),(0,11,161),(0,0,0),(3,41,156),(0,62,149),(0,0,0),(0,0,0),(3,10,161),(2,21,160),(0,45,155),(0,0,0),(4,32,158),(0,33,158),(0,0,0),(0,0,0),(0,90,134),(1,90,134),(2,45,155),(0,0,0),(7,54,151),(2,33,158),(0,0,0),(0,0,0),(0,108,120),(0,12,161),(0,71,145),(0,0,0),(3,21,160),(3,11,161),(0,0,0),(0,0,0),(2,108,120),(0,93,132),(0,75,143),(0,0,0),(7,98,127),(0,69,146),(0,0,0),(0,0,0),(3,33,158),(2,93,132),(2,75,143),(0,0,0),(0,22,160),(1,22,160),(0,0,0),(0,0,0),(4,110,118),(6,63,148),(0,13,161),(0,0,0),(2,22,160),(0,38,157),(0,0,0),(0,0,0),(10,110,114),(10,76,139),(0,67,147),(0,0,0),(0,42,156),(1,42,156),(0,0,0),(0,0,0),(3,69,146),(4,21,160),(2,67,147),(0,0,0),(2,42,156),(4,62,149),(0,0,0),(0,0,0),(7,13,160),(0,52,153),(1,52,153),(0,0,0),(0,96,130),(0,14,161),(0,0,0),(0,0,0),(0,34,158),(1,34,158),(0,29,159),(0,0,0),(2,96,130),(2,14,161),(0,0,0),(0,0,0),(2,34,158),(0,23,160),(1,23,160),(0,0,0),(7,42,155),(8,86,135),(0,0,0),(0,0,0),(6,72,144),(2,23,160),(4,75,143),(0,0,0),(3,52,153),(0,46,155),(0,0,0),(0,0,0),(3,14,161),(5,48,154),(0,15,161),(0,0,0),(4,22,160),(2,46,155),(0,0,0),(0,0,0),(6,40,156),(0,92,133),(0,105,123),(0,0,0),(3,23,160),(4,38,157),(0,0,0),(0,0,0),(10,14,158),(0,81,140),(1,81,140),(0,0,0),(4,42,156),(0,58,151),(0,0,0),(0,0,0),(3,46,155),(2,81,140),(0,39,157),(0,0,0),(11,96,125),(2,58,151),(0,0,0),(0,0,0),(0,24,160),(0,16,161),(1,16,161),(0,0,0),(3,92,133),(0,30,159),(0,0,0),(0,0,0),(2,24,160),(0,43,156),(0,95,131),(0,0,0),(3,81,140),(0,35,158),(0,0,0),(0,0,0),(0,104,124),(1,104,124),(2,95,131),(0,0,0),(8,78,140),(2,35,158),(0,0,0),(0,0,0),(2,104,124),(6,8,161),(5,69,146),(0,0,0),(3,16,161),(4,46,155),(0,0,0),(0,0,0),(3,30,159),(0,72,145),(0,17,161),(0,0,0),(0,74,144),(1,74,144),(0,0,0),(0,0,0),(0,50,154),(1,50,154),(0,53,153),(0,0,0),(2,74,144),(0,61,150),(0,0,0),(0,0,0),(2,50,154),(0,25,160),(1,25,160),(0,0,0),(12,28,154),(2,61,150),(0,0,0),(0,0,0),(7,17,160),(0,68,147),(0,47,155),(0,0,0),(3,72,145),(0,91,134),(0,0,0),(0,0,0),(0,56,152),(1,56,152),(0,31,159),(0,0,0),(0,0,162),(0,1,162),(0,0,0),(0,0,0),(0,2,162),(0,40,157),(1,40,157),(0,0,0),(2,0,162),(0,3,162),(0,0,0),(0,0,0),(2,2,162),(2,40,157),(6,11,161),(0,0,0),(0,4,162),(0,110,119),(0,0,0),(0,0,0),(3,91,134),(7,1,161),(5,46,155),(0,0,0),(2,4,162),(0,5,162),(0,0,0),(0,0,0),(0,44,156),(1,44,156),(4,17,161),(0,0,0),(0,26,160),(1,26,160),(0,0,0),(0,0,0),(0,6,162),(0,80,141),(0,19,161),(0,0,0),(2,26,160),(4,61,150),(0,0,0),(0,0,0),(2,6,162),(2,80,141),(2,19,161),(0,0,0),(8,38,156),(0,7,162),(0,0,0),(0,0,0),(3,5,162),(0,64,149),(1,64,149),(0,0,0),(6,22,160),(2,7,162),(0,0,0),(0,0,0),(4,56,152),(0,32,159),(1,32,159),(0,0,0),(0,8,162),(0,97,130),(0,0,0),(0,0,0),(4,2,162),(2,32,159),(5,35,158),(0,0,0),(2,8,162),(0,51,154),(0,0,0),(0,0,0),(3,7,162),(0,20,161),(1,20,161),(0,0,0),(0,82,140),(0,9,162),(0,0,0),(0,0,0),(7,8,161),(0,27,160),(0,41,157),(0,0,0),(2,82,140),(0,37,158),(0,0,0),(0,0,0),(3,97,130),(2,27,160),(0,87,137),(0,0,0),(4,26,160),(2,37,158),(0,0,0),(0,0,0),(0,10,162),(1,10,162),(2,87,137),(0,0,0),(3,20,161),(10,70,143),(0,0,0),(0,0,0),(2,10,162),(0,57,152),(0,73,145),(0,0,0),(3,27,160),(0,71,146),(0,0,0),(0,0,0),(3,37,158),(0,45,156),(0,21,161),(0,0,0),(7,10,161),(0,11,162),(0,0,0),(0,0,0),(8,16,160),(2,45,156),(0,33,159),(0,0,0),(4,8,162),(2,11,162),(0,0,0),(0,0,0),(8,30,158),(0,84,139),(0,77,143),(0,0,0),(3,57,152),(3,73,145),(0,0,0),(0,0,0),(0,28,160),(1,28,160),(2,77,143),(0,0,0),(0,12,162),(1,12,162),(0,0,0),(0,0,0),(2,28,160),(0,67,148),(1,67,148),(0,0,0),(2,12,162),(3,33,159),(0,0,0),(0,0,0),(8,92,132),(0,60,151),(1,60,151),(0,0,0),(3,84,139),(0,22,161),(0,0,0),(0,0,0),(0,38,158),(1,38,158),(9,9,160),(0,0,0),(10,64,146),(0,13,162),(0,0,0),(0,0,0),(2,38,158),(0,89,136),(1,89,136),(0,0,0),(0,52,154),(1,52,154),(0,0,0),(0,0,0),(14,24,152),(2,89,136),(0,49,155),(0,0,0),(2,52,154),(4,11,162),(0,0,0),(0,0,0),(3,22,161),(5,8,162),(0,55,153),(0,0,0),(7,38,157),(0,34,159),(0,0,0),(0,0,0),(0,14,162),(0,29,160),(0,81,141),(0,0,0),(3,89,136),(2,34,159),(0,0,0),(0,0,0),(2,14,162),(0,95,132),(0,23,161),(0,0,0),(0,46,156),(1,46,156),(0,0,0),(0,0,0),(6,56,152),(2,95,132),(0,113,117),(0,0,0),(2,46,156),(3,55,153),(0,0,0),(0,0,0),(3,34,159),(4,60,151),(2,113,117),(0,0,0),(0,58,152),(0,15,162),(0,0,0),(0,0,0),(4,38,158),(8,19,160),(12,61,145),(0,0,0),(2,58,152),(2,15,162),(0,0,0),(0,0,0),(10,42,154),(4,89,136),(0,111,119),(0,0,0),(4,52,154),(0,39,158),(0,0,0),(0,0,0),(6,44,156),(0,83,140),(1,83,140),(0,0,0),(6,26,160),(2,39,158),(0,0,0),(0,0,0),(3,15,162),(0,24,161),(0,43,157),(0,0,0),(0,16,162),(0,74,145),(0,0,0),(0,0,0),(0,98,130),(1,98,130),(0,35,159),(0,0,0),(2,16,162),(0,70,147),(0,0,0),(0,0,0),(0,76,144),(0,88,137),(1,88,137),(0,0,0),(3,83,140),(2,70,147),(0,0,0),(0,0,0),(2,76,144),(2,88,137),(0,61,151),(0,0,0),(3,24,161),(0,50,155),(0,0,0),(0,0,0),(0,68,148),(1,68,148),(2,61,151),(0,0,0),(4,58,152),(0,17,162),(0,0,0),(0,0,0),(2,68,148),(6,20,161),(5,13,162),(0,0,0),(3,88,137),(2,17,162),(0,0,0),(0,0,0),(0,0,0),(0,47,156),(0,25,161),(0,0,0),(0,108,122),(1,108,122),(0,0,0),(0,0,0),(3,50,155),(2,47,156),(2,25,161),(0,0,0),(2,108,122),(0,66,149),(0,0,0),(0,0,0),(3,17,162),(0,31,160),(1,31,160),(0,0,0),(0,40,158),(1,40,158),(0,0,0),(0,0,0),(0,18,162),(0,0,163),(0,1,163),(0,0,0),(2,40,158),(0,2,163),(0,0,0),(0,0,0),(2,18,162),(0,36,159),(0,3,163),(0,0,0),(7,91,134),(2,2,163),(0,0,0),(0,0,0),(3,66,149),(0,4,163),(1,4,163),(0,0,0),(3,31,160),(4,50,155),(0,0,0),(0,0,0),(4,68,148),(2,4,163),(0,5,163),(0,0,0),(0,64,150),(0,26,161),(0,0,0),(0,0,0),(3,2,163),(10,1,160),(2,5,163),(0,0,0),(2,64,150),(0,6,163),(0,0,0),(0,0,0),(18,70,126),(4,47,156),(4,25,161),(0,0,0),(0,106,124),(0,87,138),(0,0,0),(0,0,0),(10,4,160),(6,60,151),(0,7,163),(0,0,0),(2,106,124),(2,87,138),(0,0,0),(0,0,0),(0,32,160),(1,32,160),(0,51,155),(0,0,0),(4,40,158),(5,98,130),(0,0,0),(0,0,0),(0,54,154),(0,8,163),(1,8,163),(0,0,0),(6,52,154),(4,2,163),(0,0,0),(0,0,0),(0,48,156),(0,100,129),(1,100,129),(0,0,0),(0,20,162),(0,41,158),(0,0,0),(0,0,0),(2,48,156),(2,100,129),(0,9,163),(0,0,0),(2,20,162),(2,41,158),(0,0,0),(0,0,0),(0,84,140),(1,84,140),(0,57,153),(0,0,0),(3,8,163),(4,26,161),(0,0,0),(0,0,0),(2,84,140),(0,69,148),(1,69,148),(0,0,0),(3,100,129),(0,10,163),(0,0,0),(0,0,0),(3,41,158),(2,69,148),(0,45,157),(0,0,0),(4,106,124),(2,10,163),(0,0,0),(0,0,0),(11,70,143),(0,115,116),(1,115,116),(0,0,0),(6,58,152),(0,21,162),(0,0,0),(0,0,0),(4,32,160),(0,33,160),(0,11,163),(0,0,0),(0,104,126),(0,113,118),(0,0,0),(0,0,0),(3,10,163),(2,33,160),(2,11,163),(0,0,0),(2,104,126),(0,99,130),(0,0,0),(0,0,0),(0,60,152),(0,28,161),(1,28,161),(0,0,0),(3,115,116),(2,99,130),(0,0,0),(0,0,0),(2,60,152),(0,12,163),(0,95,133),(0,0,0),(3,33,160),(0,86,139),(0,0,0),(0,0,0),(3,113,118),(0,111,120),(1,111,120),(0,0,0),(8,74,144),(0,38,159),(0,0,0),(0,0,0),(0,22,162),(0,52,155),(1,52,155),(0,0,0),(3,28,161),(2,38,159),(0,0,0),(0,0,0),(2,22,162),(0,49,156),(0,13,163),(0,0,0),(3,12,163),(0,55,154),(0,0,0),(0,0,0),(3,86,139),(2,49,156),(2,13,163),(0,0,0),(3,111,120),(2,55,154),(0,0,0),(0,0,0),(3,38,159),(4,33,160),(4,11,163),(0,0,0),(0,34,160),(1,34,160),(0,0,0),(0,0,0),(7,89,136),(6,47,156),(0,29,161),(0,0,0),(2,34,160),(0,14,163),(0,0,0),(0,0,0),(3,55,154),(4,28,161),(0,63,151),(0,0,0),(8,4,162),(0,23,162),(0,0,0),(0,0,0),(19,6,141),(0,91,136),(1,91,136),(0,0,0),(6,40,158),(2,23,162),(0,0,0),(0,0,0),(6,18,162),(2,91,136),(6,1,163),(0,0,0),(0,88,138),(1,88,138),(0,0,0),(0,0,0),(0,74,146),(0,72,147),(0,15,163),(0,0,0),(2,88,138),(3,63,151),(0,0,0),(0,0,0),(2,74,146),(0,76,145),(0,39,159),(0,0,0),(0,70,148),(1,70,148),(0,0,0),(0,0,0),(10,52,152),(2,76,145),(2,39,159),(0,0,0),(2,70,148),(0,43,158),(0,0,0),(0,0,0),(12,112,112),(5,104,126),(5,113,118),(0,0,0),(0,24,162),(0,30,161),(0,0,0),(0,0,0),(11,23,158),(0,16,163),(1,16,163),(0,0,0),(2,24,162),(2,30,161),(0,0,0),(0,0,0),(7,83,140),(0,97,132),(0,53,155),(0,0,0),(0,50,156),(1,50,156),(0,0,0),(0,0,0),(3,43,158),(2,97,132),(0,101,129),(0,0,0),(2,50,156),(8,37,158),(0,0,0),(0,0,0),(3,30,161),(0,80,143),(1,80,143),(0,0,0),(0,56,154),(1,56,154),(0,0,0),(0,0,0),(0,66,150),(1,66,150),(0,17,163),(0,0,0),(2,56,154),(0,106,125),(0,0,0),(0,0,0),(2,66,150),(4,76,145),(2,17,163),(0,0,0),(4,70,148),(0,25,162),(0,0,0),(0,0,0),(6,84,140),(8,45,156),(0,93,135),(0,0,0),(3,80,143),(2,25,162),(0,0,0),(0,0,0),(11,30,157),(0,40,159),(0,31,161),(0,0,0),(4,24,162),(3,17,163),(0,0,0),(0,0,0),(0,82,142),(1,82,142),(0,59,153),(0,0,0),(10,86,136),(0,18,163),(0,0,0),(0,0,0),(0,0,164),(0,1,164),(1,1,164),(0,0,0),(0,2,164),(0,105,126),(0,0,0),(0,0,0),(2,0,164),(0,3,164),(1,3,164),(0,0,0),(2,2,164),(2,105,126),(0,0,0),(0,0,0),(0,4,164),(1,4,164),(0,115,117),(0,0,0),(4,56,154),(3,59,153),(0,0,0),(0,0,0),(0,26,162),(0,5,164),(1,5,164),(0,0,0),(3,1,164),(4,106,125),(0,0,0),(0,0,0),(2,26,162),(2,5,164),(0,19,163),(0,0,0),(0,6,164),(1,6,164),(0,0,0),(0,0,0),(10,40,156),(0,51,156),(0,73,147),(0,0,0),(2,6,164),(0,54,155),(0,0,0),(0,0,0),(0,112,120),(0,7,164),(1,7,164),(0,0,0),(0,62,152),(1,62,152),(0,0,0),(0,0,0),(2,112,120),(0,48,157),(0,77,145),(0,0,0),(2,62,152),(3,19,163),(0,0,0),(0,0,0),(0,8,164),(1,8,164),(0,41,159),(0,0,0),(3,51,156),(0,57,154),(0,0,0),(0,0,0),(2,8,164),(0,20,163),(1,20,163),(0,0,0),(3,7,164),(0,27,162),(0,0,0),(0,0,0),(4,4,164),(0,9,164),(1,9,164),(0,0,0),(3,48,157),(0,95,134),(0,0,0),(0,0,0),(0,110,122),(1,110,122),(5,106,125),(0,0,0),(7,41,158),(0,45,158),(0,0,0),(0,0,0),(2,110,122),(0,103,128),(1,103,128),(0,0,0),(0,10,164),(1,10,164),(0,0,0),(0,0,0)]

def wits_27 : List (ℕ × ℕ × ℕ) := [(3,27,162),(2,103,128),(4,73,147),(0,0,0),(2,10,164),(4,54,155),(0,0,0),(0,0,0),(3,95,134),(0,60,153),(0,21,163),(0,0,0),(4,62,152),(5,82,142),(0,0,0),(0,0,0),(3,45,158),(0,11,164),(1,11,164),(0,0,0),(3,103,128),(5,0,164),(0,0,0),(0,0,0),(4,8,164),(2,11,164),(0,65,151),(0,0,0),(0,28,162),(1,28,162),(0,0,0),(0,0,0),(7,33,160),(4,20,163),(2,65,151),(0,0,0),(2,28,162),(3,21,163),(0,0,0),(0,0,0),(0,12,164),(1,12,164),(10,11,161),(0,0,0),(0,38,160),(0,42,159),(0,0,0),(0,0,0),(2,12,164),(6,97,132),(0,49,157),(0,0,0),(2,38,160),(0,22,163),(0,0,0),(0,0,0),(7,12,163),(4,103,128),(2,49,157),(0,0,0),(4,10,164),(0,94,135),(0,0,0),(0,0,0),(7,111,120),(0,13,164),(1,13,164),(0,0,0),(6,56,154),(2,94,135),(0,0,0),(0,0,0),(3,42,159),(0,63,152),(0,107,125),(0,0,0),(8,40,158),(0,34,161),(0,0,0),(0,0,0),(0,46,158),(1,46,158),(2,107,125),(0,0,0),(7,55,154),(0,29,162),(0,0,0),(0,0,0),(0,72,148),(1,72,148),(4,65,151),(0,0,0),(0,14,164),(1,14,164),(0,0,0),(0,0,0),(2,72,148),(6,40,159),(0,23,163),(0,0,0),(2,14,164),(0,70,149),(0,0,0),(0,0,0),(3,34,161),(7,29,161),(0,85,141),(0,0,0),(4,38,160),(0,78,145),(0,0,0),(0,0,0),(0,106,126),(1,106,126),(2,85,141),(0,0,0),(6,2,164),(2,78,145),(0,0,0),(0,0,0),(2,106,126),(0,15,164),(1,15,164),(0,0,0),(0,68,150),(1,68,150),(0,0,0),(0,0,0),(3,70,149),(2,15,164),(0,43,159),(0,0,0),(2,68,150),(3,85,141),(0,0,0),(0,0,0),(0,80,144),(1,80,144),(2,43,159),(0,0,0),(12,64,146),(4,34,161),(0,0,0),(0,0,0),(0,30,162),(0,24,163),(0,35,161),(0,0,0),(3,15,164),(0,50,157),(0,0,0),(0,0,0),(0,16,164),(1,16,164),(0,105,127),(0,0,0),(4,14,164),(0,66,151),(0,0,0),(0,0,0),(2,16,164),(0,56,155),(1,56,155),(0,0,0),(6,62,152),(2,66,151),(0,0,0),(0,0,0),(7,16,163),(0,87,140),(1,87,140),(0,0,0),(0,96,134),(0,47,158),(0,0,0),(0,0,0),(3,50,157),(2,87,140),(5,22,163),(0,0,0),(2,96,134),(2,47,158),(0,0,0),(0,0,0),(3,66,151),(0,17,164),(1,17,164),(0,0,0),(3,56,155),(6,27,162),(0,0,0),(0,0,0),(7,80,143),(2,17,164),(0,25,163),(0,0,0),(3,87,140),(0,59,154),(0,0,0),(0,0,0),(0,40,160),(1,40,160),(2,25,163),(0,0,0),(7,106,125),(0,31,162),(0,0,0),(0,0,0),(2,40,160),(4,24,163),(4,35,161),(0,0,0),(3,17,164),(2,31,162),(0,0,0),(0,0,0),(4,16,164),(0,36,161),(1,36,161),(0,0,0),(0,18,164),(1,18,164),(0,0,0),(0,0,0),(3,59,154),(0,0,165),(0,1,165),(0,0,0),(2,18,164),(0,2,165),(0,0,0),(0,0,0),(3,31,162),(0,73,148),(0,3,165),(0,0,0),(4,96,134),(2,2,165),(0,0,0),(0,0,0),(7,1,164),(0,4,165),(0,71,149),(0,0,0),(3,36,161),(0,26,163),(0,0,0),(0,0,0),(7,3,164),(2,4,165),(0,5,165),(0,0,0),(0,54,156),(0,62,153),(0,0,0),(0,0,0),(3,2,165),(0,19,164),(1,19,164),(0,0,0),(2,54,156),(0,6,165),(0,0,0),(0,0,0),(4,40,160),(2,19,164),(0,79,145),(0,0,0),(0,32,162),(1,32,162),(0,0,0),(0,0,0),(3,26,163),(7,19,163),(0,7,165),(0,0,0),(2,32,162),(0,86,141),(0,0,0),(0,0,0),(3,62,153),(0,41,160),(1,41,160),(0,0,0),(3,19,164),(2,86,141),(0,0,0),(0,0,0),(3,6,165),(0,8,165),(0,37,161),(0,0,0),(11,19,160),(0,98,133),(0,0,0),(0,0,0),(0,20,164),(0,81,144),(0,27,163),(0,0,0),(8,88,138),(2,98,133),(0,0,0),(0,0,0),(0,102,130),(1,102,130),(0,9,165),(0,0,0),(3,41,160),(4,26,163),(0,0,0),(0,0,0),(2,102,130),(8,76,145),(2,9,165),(0,0,0),(0,60,154),(1,60,154),(0,0,0),(0,0,0),(3,98,133),(4,19,164),(5,59,154),(0,0,0),(2,60,154),(0,10,165),(0,0,0),(0,0,0),(6,106,126),(0,65,152),(1,65,152),(0,0,0),(0,94,136),(0,33,162),(0,0,0),(0,0,0),(7,103,128),(0,21,164),(0,83,143),(0,0,0),(2,94,136),(2,33,162),(0,0,0),(0,0,0),(0,88,140),(1,88,140),(0,11,165),(0,0,0),(8,50,156),(11,37,157),(0,0,0),(0,0,0),(2,88,140),(0,28,163),(1,28,163),(0,0,0),(3,65,152),(4,98,133),(0,0,0),(0,0,0),(3,33,162),(0,55,156),(0,101,131),(0,0,0),(0,42,160),(0,38,161),(0,0,0),(0,0,0),(4,102,130),(0,12,165),(1,12,165),(0,0,0),(2,42,160),(2,38,161),(0,0,0),(0,0,0),(11,62,149),(2,12,165),(0,63,153),(0,0,0),(0,22,164),(1,22,164),(0,0,0),(0,0,0),(10,28,160),(0,72,149),(0,115,119),(0,0,0),(2,22,164),(0,58,155),(0,0,0),(0,0,0),(3,38,161),(2,72,149),(0,13,165),(0,0,0),(0,114,120),(0,46,159),(0,0,0),(0,0,0),(0,34,162),(1,34,162),(2,13,165),(0,0,0),(2,114,120),(2,46,159),(0,0,0),(0,0,0),(2,34,162),(0,105,128),(0,29,163),(0,0,0),(3,72,149),(3,115,119),(0,0,0),(0,0,0),(3,58,155),(2,105,128),(0,93,137),(0,0,0),(7,34,161),(0,14,165),(0,0,0),(0,0,0),(0,100,132),(0,23,164),(1,23,164),(0,0,0),(0,112,122),(1,112,122),(0,0,0),(0,0,0),(2,100,132),(2,23,164),(9,28,161),(0,0,0),(2,112,122),(0,61,154),(0,0,0),(0,0,0),(10,14,162),(0,96,135),(0,39,161),(0,0,0),(4,22,164),(2,61,154),(0,0,0),(0,0,0),(3,14,165),(0,43,160),(0,15,165),(0,0,0),(3,23,164),(4,58,155),(0,0,0),(0,0,0),(8,112,120),(0,104,129),(0,53,157),(0,0,0),(0,66,152),(1,66,152),(0,0,0),(0,0,0),(0,50,158),(1,50,158),(2,53,157),(0,0,0),(2,66,152),(0,30,163),(0,0,0),(0,0,0),(0,24,164),(1,24,164),(4,29,163),(0,0,0),(0,110,124),(1,110,124),(0,0,0),(0,0,0),(2,24,164),(0,16,165),(1,16,165),(0,0,0),(2,110,124),(3,53,157),(0,0,0),(0,0,0),(4,100,132),(2,16,165),(0,47,159),(0,0,0),(4,112,122),(6,86,141),(0,0,0),(0,0,0),(3,30,163),(6,41,160),(2,47,159),(0,0,0),(7,66,151),(4,61,154),(0,0,0),(0,0,0),(7,56,155),(0,64,153),(0,59,155),(0,0,0),(0,92,138),(0,103,130),(0,0,0),(0,0,0),(6,20,164),(2,64,153),(0,17,165),(0,0,0),(2,92,138),(2,103,130),(0,0,0),(0,0,0),(6,102,130),(0,25,164),(1,25,164),(0,0,0),(4,66,152),(5,34,162),(0,0,0),(0,0,0),(4,50,158),(0,75,148),(0,31,163),(0,0,0),(3,64,153),(3,59,155),(0,0,0),(0,0,0),(0,44,160),(1,44,160),(0,77,147),(0,0,0),(0,36,162),(0,71,150),(0,0,0),(0,0,0),(2,44,160),(4,16,165),(2,77,147),(0,0,0),(2,36,162),(0,18,165),(0,0,0),(0,0,0),(8,12,164),(5,112,122),(4,47,159),(0,0,0),(0,0,166),(0,1,166),(0,0,0),(0,0,0),(0,2,166),(1,2,166),(0,69,151),(0,0,0),(2,0,166),(0,3,166),(0,0,0),(0,0,0),(2,2,166),(4,64,153),(2,69,151),(0,0,0),(0,4,166),(1,4,166),(0,0,0),(0,0,0),(3,18,165),(6,55,156),(0,107,127),(0,0,0),(2,4,166),(0,5,166),(0,0,0),(0,0,0),(3,1,166),(0,48,159),(0,19,165),(0,0,0),(7,26,163),(2,5,166),(0,0,0),(0,0,0),(0,6,166),(0,32,163),(1,32,163),(0,0,0),(6,22,164),(5,24,164),(0,0,0),(0,0,0),(2,6,166),(2,32,163),(0,41,161),(0,0,0),(4,36,162),(0,7,166),(0,0,0),(0,0,0),(3,5,166),(7,79,145),(2,41,161),(0,0,0),(3,48,159),(0,37,162),(0,0,0),(0,0,0),(6,34,162),(0,116,119),(1,116,119),(0,0,0),(0,8,166),(1,8,166),(0,0,0),(0,0,0),(4,2,166),(0,20,165),(1,20,165),(0,0,0),(2,8,166),(3,41,161),(0,0,0),(0,0,0),(3,7,166),(2,20,165),(0,65,153),(0,0,0),(4,4,166),(0,9,166),(0,0,0),(0,0,0),(3,37,162),(6,23,164),(2,65,153),(0,0,0),(3,116,119),(2,9,166),(0,0,0),(0,0,0),(8,80,144),(4,48,159),(4,19,165),(0,0,0),(3,20,165),(0,113,122),(0,0,0),(0,0,0),(0,10,166),(1,10,166),(0,33,163),(0,0,0),(11,27,160),(2,113,122),(0,0,0),(0,0,0),(2,10,166),(5,36,162),(0,21,165),(0,0,0),(0,52,158),(1,52,158),(0,0,0),(0,0,0),(7,65,152),(0,112,123),(0,55,157),(0,0,0),(2,52,158),(0,11,166),(0,0,0),(0,0,0),(0,28,164),(1,28,164),(0,49,159),(0,0,0),(0,72,150),(0,42,161),(0,0,0),(0,0,0),(0,38,162),(0,100,133),(1,100,133),(0,0,0),(2,72,150),(0,78,147),(0,0,0),(0,0,0),(2,38,162),(0,111,124),(1,111,124),(0,0,0),(0,12,166),(0,70,151),(0,0,0),(0,0,0),(3,11,166),(2,111,124),(5,5,166),(0,0,0),(2,12,166),(0,22,165),(0,0,0),(0,0,0),(0,96,136),(1,96,136),(10,95,133),(0,0,0),(0,46,160),(1,46,160),(0,0,0),(0,0,0),(2,96,136),(6,64,153),(4,33,163),(0,0,0),(2,46,160),(0,13,166),(0,0,0),(0,0,0),(0,68,152),(1,68,152),(4,21,165),(0,0,0),(4,52,158),(0,87,142),(0,0,0),(0,0,0),(2,68,152),(0,29,164),(1,29,164),(0,0,0),(7,46,159),(2,87,142),(0,0,0),(0,0,0),(4,28,164),(2,29,164),(0,61,155),(0,0,0),(4,72,150),(0,82,145),(0,0,0),(0,0,0),(0,14,166),(1,14,166),(0,23,165),(0,0,0),(6,36,162),(0,99,134),(0,0,0),(0,0,0),(2,14,166),(4,111,124),(2,23,165),(0,0,0),(3,29,164),(0,39,162),(0,0,0),(0,0,0),(7,23,164),(8,19,164),(0,43,161),(0,0,0),(6,0,166),(0,53,158),(0,0,0),(0,0,0),(3,82,145),(10,91,136),(2,43,161),(0,0,0),(4,46,160),(0,15,166),(0,0,0),(0,0,0),(3,99,134),(0,56,157),(1,56,157),(0,0,0),(6,4,166),(2,15,166),(0,0,0),(0,0,0),(0,84,144),(0,108,127),(0,35,163),(0,0,0),(0,30,164),(1,30,164),(0,0,0),(0,0,0),(2,84,144),(0,24,165),(0,89,141),(0,0,0),(2,30,164),(5,28,164),(0,0,0),(0,0,0),(3,15,166),(0,47,160),(1,47,160),(0,0,0),(0,16,166),(1,16,166),(0,0,0),(0,0,0),(4,14,166),(0,59,156),(1,59,156),(0,0,0),(2,16,166),(3,35,163),(0,0,0),(0,0,0),(7,16,165),(2,59,156),(0,75,149),(0,0,0),(0,102,132),(0,73,150),(0,0,0),(0,0,0),(11,74,145),(0,77,148),(1,77,148),(0,0,0),(2,102,132),(2,73,150),(0,0,0),(0,0,0),(11,70,147),(2,77,148),(0,71,151),(0,0,0),(0,40,162),(0,17,166),(0,0,0),(0,0,0),(0,118,118),(1,118,118),(0,25,165),(0,0,0),(2,40,162),(2,17,166),(0,0,0),(0,0,0),(0,116,120),(0,31,164),(1,31,164),(0,0,0),(3,77,148),(10,106,125),(0,0,0),(0,0,0),(2,116,120),(0,36,163),(0,115,121),(0,0,0),(27,21,88),(0,62,155),(0,0,0),(0,0,0),(3,17,166),(2,36,163),(2,115,121),(0,0,0),(4,16,166),(0,81,146),(0,0,0),(0,0,0),(0,18,166),(0,91,140),(0,51,159),(0,0,0),(3,31,164),(2,81,146),(0,0,0),(0,0,0),(2,18,166),(0,0,167),(0,1,167),(0,0,0),(3,36,163),(0,2,167),(0,0,0),(0,0,0),(3,62,155),(2,0,167),(0,3,167),(0,0,0),(6,72,150),(0,26,165),(0,0,0),(0,0,0),(0,48,160),(0,4,167),(1,4,167),(0,0,0),(0,88,142),(1,88,142),(0,0,0),(0,0,0),(2,48,160),(2,4,167),(0,5,167),(0,0,0),(2,88,142),(0,19,166),(0,0,0),(0,0,0),(0,32,164),(1,32,164),(2,5,167),(0,0,0),(7,5,166),(0,6,167),(0,0,0),(0,0,0),(2,32,164),(4,36,163),(4,115,121),(0,0,0),(3,4,167),(2,6,167),(0,0,0),(0,0,0),(0,60,156),(1,60,156),(0,7,167),(0,0,0),(8,112,122),(0,65,154),(0,0,0),(0,0,0),(2,60,156),(4,91,140),(0,45,161),(0,0,0),(7,7,166),(2,65,154),(0,0,0),(0,0,0),(3,6,167),(0,8,167),(0,27,165),(0,0,0),(0,20,166),(1,20,166),(0,0,0),(0,0,0),(7,116,119),(0,85,144),(1,85,144),(0,0,0),(2,20,166),(3,7,167),(0,0,0),(0,0,0),(3,65,154),(2,85,144),(0,9,167),(0,0,0),(4,88,142),(3,45,161),(0,0,0),(0,0,0),(0,74,150),(0,76,149),(1,76,149),(0,0,0),(3,8,167),(0,90,141),(0,0,0),(0,0,0),(2,74,150),(0,33,164),(1,33,164),(0,0,0),(0,78,148),(0,10,167),(0,0,0),(0,0,0),(18,16,148),(2,33,164),(0,63,155),(0,0,0),(2,78,148),(0,21,166),(0,0,0),(0,0,0)]

def wits_28 : List (ℕ × ℕ × ℕ) := [(4,60,156),(0,49,160),(1,49,160),(0,0,0),(0,70,152),(1,70,152),(0,0,0),(0,0,0),(0,42,162),(0,28,165),(0,11,167),(0,0,0),(2,70,152),(0,38,163),(0,0,0),(0,0,0),(2,42,162),(2,28,165),(0,87,143),(0,0,0),(4,20,166),(2,38,163),(0,0,0),(0,0,0),(3,21,166),(4,85,144),(0,99,135),(0,0,0),(3,49,160),(5,48,160),(0,0,0),(0,0,0),(7,100,133),(0,12,167),(1,12,167),(0,0,0),(3,28,165),(0,46,161),(0,0,0),(0,0,0),(0,22,166),(1,22,166),(5,19,166),(0,0,0),(6,102,132),(2,46,161),(0,0,0),(0,0,0),(0,108,128),(1,108,128),(5,6,167),(0,0,0),(0,34,164),(1,34,164),(0,0,0),(0,0,0),(2,108,128),(0,61,156),(0,13,167),(0,0,0),(2,34,164),(4,21,166),(0,0,0),(0,0,0),(0,92,140),(1,92,140),(0,29,165),(0,0,0),(4,70,152),(0,95,138),(0,0,0),(0,0,0),(0,66,154),(1,66,154),(2,29,165),(0,0,0),(7,87,142),(2,95,138),(0,0,0),(0,0,0),(2,66,154),(0,84,145),(1,84,145),(0,0,0),(3,61,156),(0,14,167),(0,0,0),(0,0,0),(10,72,148),(0,117,120),(0,39,163),(0,0,0),(7,82,145),(0,43,162),(0,0,0),(0,0,0),(3,95,138),(0,116,121),(1,116,121),(0,0,0),(0,50,160),(1,50,160),(0,0,0),(0,0,0),(4,22,166),(2,116,121),(5,90,141),(0,0,0),(2,50,160),(0,115,122),(0,0,0),(0,0,0),(3,14,167),(5,78,148),(0,15,167),(0,0,0),(3,117,120),(2,115,122),(0,0,0),(0,0,0),(3,43,162),(0,35,164),(1,35,164),(0,0,0),(3,116,121),(0,30,165),(0,0,0),(0,0,0),(4,92,140),(2,35,164),(0,47,161),(0,0,0),(0,24,166),(1,24,166),(0,0,0),(0,0,0),(0,106,130),(1,106,130),(2,47,161),(0,0,0),(2,24,166),(3,15,167),(0,0,0),(0,0,0),(2,106,130),(0,16,167),(1,16,167),(0,0,0),(3,35,164),(4,14,167),(0,0,0),(0,0,0),(3,30,165),(2,16,167),(4,39,163),(0,0,0),(11,16,163),(0,94,139),(0,0,0),(0,0,0),(7,59,156),(4,116,121),(0,91,141),(0,0,0),(4,50,160),(2,94,139),(0,0,0),(0,0,0),(8,10,166),(0,40,163),(0,69,153),(0,0,0),(3,16,167),(4,115,122),(0,0,0),(0,0,0),(7,77,148),(2,40,163),(0,17,167),(0,0,0),(0,44,162),(0,25,166),(0,0,0),(0,0,0),(3,94,139),(4,35,164),(0,31,165),(0,0,0),(2,44,162),(2,25,166),(0,0,0),(0,0,0),(0,36,164),(0,88,143),(1,88,143),(0,0,0),(3,40,163),(0,54,159),(0,0,0),(0,0,0),(2,36,164),(0,51,160),(1,51,160),(0,0,0),(6,78,148),(0,67,154),(0,0,0),(0,0,0),(3,25,166),(2,51,160),(5,14,167),(0,0,0),(7,62,155),(0,18,167),(0,0,0),(0,0,0),(15,96,125),(6,49,160),(5,43,162),(0,0,0),(3,88,143),(2,18,167),(0,0,0),(0,0,0),(0,0,168),(0,1,168),(1,1,168),(0,0,0),(0,2,168),(0,110,127),(0,0,0),(0,0,0),(0,26,166),(0,3,168),(1,3,168),(0,0,0),(2,2,168),(2,110,127),(0,0,0),(0,0,0),(0,4,168),(1,4,168),(4,17,167),(0,0,0),(4,44,162),(4,25,166),(0,0,0),(0,0,0),(2,4,168),(0,5,168),(0,19,167),(0,0,0),(3,1,168),(6,46,161),(0,0,0),(0,0,0),(3,110,127),(2,5,168),(2,19,167),(0,0,0),(0,6,168),(1,6,168),(0,0,0),(0,0,0),(0,90,142),(0,37,164),(1,37,164),(0,0,0),(2,6,168),(0,45,162),(0,0,0),(0,0,0),(2,90,142),(0,7,168),(1,7,168),(0,0,0),(0,76,150),(0,74,151),(0,0,0),(0,0,0),(6,92,140),(2,7,168),(5,94,139),(0,0,0),(2,76,150),(0,27,166),(0,0,0),(0,0,0),(0,8,168),(0,20,167),(1,20,167),(0,0,0),(3,37,164),(2,27,166),(0,0,0),(0,0,0),(2,8,168),(0,99,136),(0,103,133),(0,0,0),(3,7,168),(6,14,167),(0,0,0),(0,0,0),(0,52,160),(0,9,168),(0,55,159),(0,0,0),(8,30,164),(0,70,153),(0,0,0),(0,0,0),(2,52,160),(2,9,168),(0,33,165),(0,0,0),(3,20,167),(2,70,153),(0,0,0),(0,0,0),(7,76,149),(8,47,160),(0,49,161),(0,0,0),(0,10,168),(1,10,168),(0,0,0),(0,0,0),(0,58,158),(1,58,158),(0,21,167),(0,0,0),(2,10,168),(0,42,163),(0,0,0),(0,0,0),(2,58,158),(4,7,168),(2,21,167),(0,0,0),(0,28,166),(1,28,166),(0,0,0),(0,0,0),(7,49,160),(0,11,168),(0,95,139),(0,0,0),(2,28,166),(0,107,130),(0,0,0),(0,0,0),(4,8,168),(2,11,168),(0,115,123),(0,0,0),(7,38,163),(2,107,130),(0,0,0),(0,0,0),(0,46,162),(1,46,162),(2,115,123),(0,0,0),(10,42,160),(5,4,168),(0,0,0),(0,0,0),(0,12,168),(1,12,168),(0,61,157),(0,0,0),(0,84,146),(0,22,167),(0,0,0),(0,0,0),(2,12,168),(8,36,163),(2,61,157),(0,0,0),(2,84,146),(0,34,165),(0,0,0),(0,0,0),(11,22,163),(5,6,168),(4,49,161),(0,0,0),(4,10,168),(2,34,165),(0,0,0),(0,0,0),(4,58,158),(0,13,168),(0,113,125),(0,0,0),(6,44,162),(0,29,166),(0,0,0),(0,0,0),(3,22,167),(2,13,168),(2,113,125),(0,0,0),(4,28,166),(2,29,166),(0,0,0),(0,0,0),(3,34,165),(0,53,160),(1,53,160),(0,0,0),(7,95,138),(4,107,130),(0,0,0),(0,0,0),(8,48,160),(0,39,164),(0,23,167),(0,0,0),(0,14,168),(0,50,161),(0,0,0),(0,0,0),(3,29,166),(2,39,164),(0,75,151),(0,0,0),(2,14,168),(0,77,150),(0,0,0),(0,0,0),(0,64,156),(0,73,152),(1,73,152),(0,0,0),(0,94,140),(1,94,140),(0,0,0),(0,0,0),(2,64,156),(2,73,152),(0,79,149),(0,0,0),(2,94,140),(0,59,158),(0,0,0),(0,0,0),(3,50,161),(0,15,168),(0,35,165),(0,0,0),(7,115,122),(0,47,162),(0,0,0),(0,0,0),(0,30,166),(1,30,166),(2,35,165),(0,0,0),(3,73,152),(2,47,162),(0,0,0),(0,0,0),(2,30,166),(0,24,167),(1,24,167),(0,0,0),(7,30,165),(3,79,149),(0,0,0),(0,0,0),(3,59,158),(2,24,167),(5,107,130),(0,0,0),(3,15,168),(0,69,154),(0,0,0),(0,0,0),(0,16,168),(1,16,168),(4,23,167),(0,0,0),(0,110,128),(1,110,128),(0,0,0),(0,0,0),(2,16,168),(6,7,168),(4,75,151),(0,0,0),(2,110,128),(0,62,157),(0,0,0),(0,0,0),(0,40,164),(1,40,164),(0,83,147),(0,0,0),(4,94,140),(2,62,157),(0,0,0),(0,0,0),(2,40,164),(0,44,163),(1,44,163),(0,0,0),(10,92,138),(4,59,158),(0,0,0),(0,0,0),(7,40,163),(0,17,168),(0,25,167),(0,0,0),(0,54,160),(0,31,166),(0,0,0),(0,0,0),(3,62,157),(0,36,165),(0,51,161),(0,0,0),(2,54,160),(2,31,166),(0,0,0),(0,0,0),(11,59,154),(2,36,165),(0,57,159),(0,0,0),(3,44,163),(14,42,155),(0,0,0),(0,0,0),(7,88,143),(0,96,139),(1,96,139),(0,0,0),(3,17,168),(0,85,146),(0,0,0),(0,0,0),(3,31,166),(2,96,139),(5,50,161),(0,0,0),(0,18,168),(0,90,143),(0,0,0),(0,0,0),(8,22,166),(12,16,163),(5,77,150),(0,0,0),(2,18,168),(2,90,143),(0,0,0),(0,0,0),(4,40,164),(0,0,169),(0,1,169),(0,0,0),(0,60,158),(0,2,169),(0,0,0),(0,0,0),(3,85,146),(2,0,169),(0,3,169),(0,0,0),(2,60,158),(0,117,122),(0,0,0),(0,0,0),(3,90,143),(0,4,169),(1,4,169),(0,0,0),(0,32,166),(1,32,166),(0,0,0),(0,0,0),(0,78,150),(0,19,168),(0,5,169),(0,0,0),(2,32,166),(3,1,169),(0,0,0),(0,0,0),(2,78,150),(0,72,153),(0,37,165),(0,0,0),(16,28,154),(0,6,169),(0,0,0),(0,0,0),(3,117,122),(0,80,149),(1,80,149),(0,0,0),(3,4,169),(2,6,169),(0,0,0),(0,0,0),(7,37,164),(2,80,149),(0,7,169),(0,0,0),(3,19,168),(3,5,169),(0,0,0),(0,0,0),(0,70,154),(1,70,154),(0,27,167),(0,0,0),(3,72,153),(0,114,125),(0,0,0),(0,0,0),(0,20,168),(0,8,169),(1,8,169),(0,0,0),(0,82,148),(0,102,135),(0,0,0),(0,0,0),(2,20,168),(2,8,169),(4,3,169),(0,0,0),(2,82,148),(2,102,135),(0,0,0),(0,0,0),(7,99,136),(4,4,169),(0,9,169),(0,0,0),(4,32,166),(0,33,166),(0,0,0),(0,0,0),(0,98,138),(0,68,155),(1,68,155),(0,0,0),(3,8,169),(2,33,166),(0,0,0),(0,0,0),(2,98,138),(0,89,144),(1,89,144),(0,0,0),(0,42,164),(0,10,169),(0,0,0),(0,0,0),(11,33,162),(0,21,168),(1,21,168),(0,0,0),(2,42,164),(0,38,165),(0,0,0),(0,0,0),(3,33,166),(0,28,167),(1,28,167),(0,0,0),(3,68,155),(2,38,165),(0,0,0),(0,0,0),(4,70,154),(2,28,167),(0,11,169),(0,0,0),(3,89,144),(0,46,163),(0,0,0),(0,0,0),(3,10,169),(4,8,169),(2,11,169),(0,0,0),(0,66,156),(1,66,156),(0,0,0),(0,0,0),(3,38,165),(0,101,136),(1,101,136),(0,0,0),(2,66,156),(10,70,151),(0,0,0),(0,0,0),(8,36,164),(0,12,169),(1,12,169),(0,0,0),(0,22,168),(1,22,168),(0,0,0),(0,0,0),(0,34,166),(1,34,166),(0,105,133),(0,0,0),(2,22,168),(0,94,141),(0,0,0),(0,0,0),(2,34,166),(4,89,144),(2,105,133),(0,0,0),(3,101,136),(2,94,141),(0,0,0),(0,0,0),(10,68,152),(0,75,152),(0,13,169),(0,0,0),(3,12,169),(4,38,165),(0,0,0),(0,0,0),(0,56,160),(1,56,160),(0,73,153),(0,0,0),(7,29,166),(0,79,150),(0,0,0),(0,0,0),(0,50,162),(0,43,164),(0,39,165),(0,0,0),(15,107,118),(2,79,150),(0,0,0),(0,0,0),(2,50,162),(0,23,168),(1,23,168),(0,0,0),(3,75,152),(0,14,169),(0,0,0),(0,0,0),(7,39,164),(2,23,168),(0,59,159),(0,0,0),(6,18,168),(2,14,169),(0,0,0),(0,0,0),(3,79,150),(0,88,145),(1,88,145),(0,0,0),(0,104,134),(1,104,134),(0,0,0),(0,0,0),(4,34,166),(2,88,145),(0,47,163),(0,0,0),(2,104,134),(0,35,166),(0,0,0),(0,0,0),(3,14,169),(5,42,164),(0,15,169),(0,0,0),(7,59,158),(0,30,167),(0,0,0),(0,0,0),(7,15,168),(0,83,148),(1,83,148),(0,0,0),(3,88,145),(2,30,167),(0,0,0),(0,0,0),(0,24,168),(1,24,168),(0,119,121),(0,0,0),(0,0,0),(3,47,163),(0,0,0),(0,0,0),(0,62,158),(1,62,158),(2,119,121),(0,0,0),(10,16,166),(0,93,142),(0,0,0),(0,0,0),(0,96,140),(0,16,169),(0,117,123),(0,0,0),(3,83,148),(2,93,142),(0,0,0),(0,0,0),(2,96,140),(0,40,165),(1,40,165),(0,0,0),(10,102,132),(3,119,121),(0,0,0),(0,0,0),(0,44,164),(1,44,164),(0,85,147),(0,0,0),(0,90,144),(0,54,161),(0,0,0),(0,0,0),(2,44,164),(6,8,169),(2,85,147),(0,0,0),(2,90,144),(0,51,162),(0,0,0),(0,0,0),(7,44,163),(0,25,168),(0,17,169),(0,0,0),(0,36,166),(1,36,166),(0,0,0),(0,0,0),(7,17,168),(2,25,168),(2,17,169),(0,0,0),(2,36,166),(3,85,147),(0,0,0),(0,0,0),(3,54,161),(6,68,155),(4,119,121),(0,0,0),(15,23,158),(5,50,162),(0,0,0),(0,0,0),(0,114,126),(0,48,163),(0,65,157),(0,0,0),(3,25,168),(3,17,169),(0,0,0),(0,0,0),(0,76,152),(0,60,159),(1,60,159),(0,0,0),(7,85,146),(0,18,169),(0,0,0),(0,0,0),(2,76,152),(2,60,159),(10,1,167),(0,0,0),(7,90,143),(2,18,169),(0,0,0),(0,0,0),(4,44,164),(5,104,134),(0,113,127),(0,0,0),(0,0,170),(0,1,170),(0,0,0),(0,0,0),(0,2,170),(1,2,170),(0,41,165),(0,0,0),(2,0,170),(0,3,170),(0,0,0),(0,0,0),(2,2,170),(0,32,167),(1,32,167),(0,0,0),(0,4,170),(1,4,170),(0,0,0),(0,0,0),(7,4,169),(0,45,164),(0,19,169),(0,0,0),(2,4,170),(0,5,170),(0,0,0),(0,0,0),(0,112,128),(1,112,128),(2,19,169),(0,0,0),(8,14,168),(0,63,158),(0,0,0),(0,0,0),(0,6,170),(1,6,170),(4,65,157),(0,0,0),(3,32,167),(2,63,158),(0,0,0),(0,0,0),(2,6,170),(4,60,159),(0,55,161),(0,0,0),(0,52,162),(0,7,170),(0,0,0),(0,0,0),(3,5,170),(0,27,168),(1,27,168),(0,0,0),(2,52,162),(2,7,170),(0,0,0),(0,0,0),(0,68,156),(0,20,169),(0,111,129),(0,0,0),(0,8,170),(1,8,170),(0,0,0),(0,0,0),(2,68,156),(2,20,169),(0,49,163),(0,0,0),(2,8,170),(3,55,161),(0,0,0),(0,0,0),(3,7,170),(4,32,167),(0,33,167),(0,0,0),(3,27,168),(0,9,170),(0,0,0),(0,0,0),(11,113,122),(4,45,164),(2,33,167),(0,0,0),(3,20,169),(0,42,165),(0,0,0),(0,0,0),(4,112,128),(9,90,142),(6,47,163),(0,0,0),(8,110,128),(2,42,165),(0,0,0),(0,0,0)]

def wits_29 : List (ℕ × ℕ × ℕ) := [(0,10,170),(1,10,170),(0,21,169),(0,0,0),(7,10,169),(0,66,157),(0,0,0),(0,0,0),(0,28,168),(0,97,140),(1,97,140),(0,0,0),(0,46,164),(1,46,164),(0,0,0),(0,0,0),(2,28,168),(0,91,144),(1,91,144),(0,0,0),(2,46,164),(0,11,170),(0,0,0),(0,0,0),(4,68,156),(2,91,144),(4,111,129),(0,0,0),(4,8,170),(2,11,170),(0,0,0),(0,0,0),(3,66,157),(0,77,152),(0,75,153),(0,0,0),(3,97,140),(10,46,161),(0,0,0),(0,0,0),(7,101,136),(0,104,135),(0,79,151),(0,0,0),(0,12,170),(0,22,169),(0,0,0),(0,0,0),(3,11,170),(2,104,135),(2,79,151),(0,0,0),(2,12,170),(0,53,162),(0,0,0),(0,0,0),(11,13,166),(0,56,161),(1,56,161),(0,0,0),(0,64,158),(0,81,150),(0,0,0),(0,0,0),(4,10,170),(0,29,168),(0,71,155),(0,0,0),(2,64,158),(0,13,170),(0,0,0),(0,0,0),(3,22,169),(2,29,168),(0,43,165),(0,0,0),(4,46,164),(0,39,166),(0,0,0),(0,0,0),(3,53,162),(0,59,160),(1,59,160),(0,0,0),(3,56,161),(2,39,166),(0,0,0),(0,0,0),(0,108,132),(1,108,132),(0,23,169),(0,0,0),(3,29,168),(3,71,155),(0,0,0),(0,0,0),(0,14,170),(0,69,156),(0,93,143),(0,0,0),(7,14,169),(0,115,126),(0,0,0),(0,0,0),(2,14,170),(0,47,164),(1,47,164),(0,0,0),(3,59,160),(2,115,126),(0,0,0),(0,0,0),(7,88,145),(2,47,164),(0,35,167),(0,0,0),(6,0,170),(3,23,169),(0,0,0),(0,0,0),(6,2,170),(4,56,161),(0,99,139),(0,0,0),(0,30,168),(0,15,170),(0,0,0),(0,0,0),(3,115,126),(0,85,148),(1,85,148),(0,0,0),(2,30,168),(2,15,170),(0,0,0),(0,0,0),(7,83,148),(0,24,169),(0,67,157),(0,0,0),(8,82,148),(3,35,167),(0,0,0),(0,0,0),(6,112,128),(2,24,169),(2,67,157),(0,0,0),(11,59,156),(3,99,139),(0,0,0),(0,0,0),(3,15,170),(0,113,128),(1,113,128),(0,0,0),(0,16,170),(1,16,170),(0,0,0),(0,0,0),(0,54,162),(0,44,165),(1,44,165),(0,0,0),(2,16,170),(3,67,157),(0,0,0),(0,0,0),(2,54,162),(2,44,165),(0,51,163),(0,0,0),(8,42,164),(0,102,137),(0,0,0),(0,0,0),(6,68,156),(6,20,169),(0,87,147),(0,0,0),(3,113,128),(2,102,137),(0,0,0),(0,0,0),(14,14,162),(0,31,168),(0,25,169),(0,0,0),(0,78,152),(0,17,170),(0,0,0),(0,0,0),(0,74,154),(1,74,154),(2,25,169),(0,0,0),(2,78,152),(2,17,170),(0,0,0),(0,0,0),(0,48,164),(0,80,151),(1,80,151),(0,0,0),(0,98,140),(1,98,140),(0,0,0),(0,0,0),(2,48,164),(0,72,155),(1,72,155),(0,0,0),(2,98,140),(3,25,169),(0,0,0),(0,0,0),(3,17,170),(2,72,155),(6,21,169),(0,0,0),(4,16,170),(0,111,130),(0,0,0),(0,0,0),(0,18,170),(1,18,170),(5,115,126),(0,0,0),(3,80,151),(2,111,130),(0,0,0),(0,0,0),(2,18,170),(6,91,144),(4,51,163),(0,0,0),(0,70,156),(0,26,169),(0,0,0),(0,0,0),(10,4,168),(0,0,171),(0,1,171),(0,0,0),(2,70,156),(0,2,171),(0,0,0),(0,0,0),(0,32,168),(1,32,168),(0,3,171),(0,0,0),(4,78,152),(2,2,171),(0,0,0),(0,0,0),(2,32,168),(0,4,171),(0,37,167),(0,0,0),(6,12,170),(0,19,170),(0,0,0),(0,0,0),(3,26,169),(2,4,171),(0,5,171),(0,0,0),(3,0,171),(0,55,162),(0,0,0),(0,0,0),(3,2,171),(0,52,163),(1,52,163),(0,0,0),(6,64,158),(0,6,171),(0,0,0),(0,0,0),(22,26,134),(2,52,163),(0,121,121),(0,0,0),(0,120,122),(0,58,161),(0,0,0),(0,0,0),(3,19,170),(7,55,161),(0,7,171),(0,0,0),(2,120,122),(2,58,161),(0,0,0),(0,0,0),(3,55,162),(0,49,164),(1,49,164),(0,0,0),(0,20,170),(1,20,170),(0,0,0),(0,0,0),(3,6,171),(0,8,171),(0,91,145),(0,0,0),(2,20,170),(3,121,121),(0,0,0),(0,0,0),(0,104,136),(0,33,168),(0,117,125),(0,0,0),(11,33,164),(3,7,171),(0,0,0),(0,0,0),(0,42,166),(0,61,160),(0,9,171),(0,0,0),(3,49,164),(4,19,170),(0,0,0),(0,0,0),(2,42,166),(2,61,160),(2,9,171),(0,0,0),(0,116,126),(0,38,167),(0,0,0),(0,0,0),(15,19,160),(4,52,163),(0,77,153),(0,0,0),(2,116,126),(0,10,171),(0,0,0),(0,0,0),(8,44,164),(0,28,169),(1,28,169),(0,0,0),(3,61,160),(2,10,171),(0,0,0),(0,0,0),(7,97,140),(0,88,147),(0,73,155),(0,0,0),(14,106,124),(8,51,162),(0,0,0),(0,0,0),(3,38,167),(2,88,147),(0,11,171),(0,0,0),(4,20,170),(3,77,153),(0,0,0),(0,0,0),(3,10,171),(4,8,171),(2,11,171),(0,0,0),(3,28,169),(5,32,168),(0,0,0),(0,0,0),(4,104,136),(0,64,159),(0,53,163),(0,0,0),(0,34,168),(1,34,168),(0,0,0),(0,0,0),(0,22,170),(0,12,171),(1,12,171),(0,0,0),(2,34,168),(0,83,150),(0,0,0),(0,0,0),(2,22,170),(2,12,171),(5,55,162),(0,0,0),(0,50,164),(1,50,164),(0,0,0),(0,0,0),(7,56,161),(0,99,140),(0,29,169),(0,0,0),(2,50,164),(0,43,166),(0,0,0),(0,0,0),(6,74,154),(2,99,140),(0,13,171),(0,0,0),(3,12,171),(2,43,166),(0,0,0),(0,0,0),(0,90,146),(1,90,146),(2,13,171),(0,0,0),(6,98,140),(8,3,170),(0,0,0),(0,0,0),(2,90,146),(5,20,170),(0,85,149),(0,0,0),(3,99,140),(0,23,170),(0,0,0),(0,0,0),(3,43,166),(7,23,169),(0,47,165),(0,0,0),(10,94,140),(0,14,171),(0,0,0),(0,0,0),(6,18,170),(4,64,159),(2,47,165),(0,0,0),(0,62,160),(1,62,160),(0,0,0),(0,0,0),(0,102,138),(0,35,168),(1,35,168),(0,0,0),(2,62,160),(0,67,158),(0,0,0),(0,0,0),(2,102,138),(2,35,168),(5,38,167),(0,0,0),(4,50,164),(0,30,169),(0,0,0),(0,0,0),(3,14,171),(4,99,140),(0,15,171),(0,0,0),(7,15,170),(2,30,169),(0,0,0),(0,0,0),(7,85,148),(0,87,148),(0,95,143),(0,0,0),(0,24,170),(1,24,170),(0,0,0),(0,0,0),(3,67,158),(2,87,148),(0,111,131),(0,0,0),(2,24,170),(0,54,163),(0,0,0),(0,0,0),(3,30,169),(0,40,167),(1,40,167),(0,0,0),(0,44,166),(0,57,162),(0,0,0),(0,0,0),(7,113,128),(0,16,171),(1,16,171),(0,0,0),(2,44,166),(0,74,155),(0,0,0),(0,0,0),(0,80,152),(1,80,152),(0,65,159),(0,0,0),(4,62,160),(2,74,155),(0,0,0),(0,0,0),(2,80,152),(4,35,168),(2,65,159),(0,0,0),(3,40,167),(4,67,158),(0,0,0),(0,0,0),(0,36,168),(0,60,161),(0,31,169),(0,0,0),(0,110,132),(0,25,170),(0,0,0),(0,0,0),(2,36,168),(0,48,165),(0,17,171),(0,0,0),(2,110,132),(2,25,170),(0,0,0),(0,0,0),(6,42,166),(0,119,124),(1,119,124),(0,0,0),(4,24,170),(5,90,146),(0,0,0),(0,0,0),(7,80,151),(2,119,124),(4,111,131),(0,0,0),(3,60,161),(0,70,157),(0,0,0),(0,0,0),(3,25,170),(4,40,167),(5,23,170),(0,0,0),(0,84,150),(1,84,150),(0,0,0),(0,0,0),(11,110,127),(4,16,171),(5,14,171),(0,0,0),(2,84,150),(0,18,171),(0,0,0),(0,0,0),(4,80,152),(0,63,160),(0,41,167),(0,0,0),(0,94,144),(0,97,142),(0,0,0),(0,0,0),(0,26,170),(1,26,170),(2,41,167),(0,0,0),(2,94,144),(0,45,166),(0,0,0),(0,0,0),(0,0,172),(0,1,172),(1,1,172),(0,0,0),(0,2,172),(1,2,172),(0,0,0),(0,0,0),(2,0,172),(0,3,172),(0,55,163),(0,0,0),(2,2,172),(0,86,149),(0,0,0),(0,0,0),(0,4,172),(1,4,172),(0,19,171),(0,0,0),(7,19,170),(2,86,149),(0,0,0),(0,0,0),(0,58,162),(0,5,172),(1,5,172),(0,0,0),(3,1,172),(4,70,157),(0,0,0),(0,0,0),(2,58,162),(2,5,172),(5,57,162),(0,0,0),(0,6,172),(1,6,172),(0,0,0),(0,0,0),(3,86,149),(7,121,121),(0,49,165),(0,0,0),(2,6,172),(0,27,170),(0,0,0),(0,0,0),(6,90,146),(0,7,172),(1,7,172),(0,0,0),(3,5,172),(0,66,159),(0,0,0),(0,0,0),(4,26,170),(0,20,171),(0,61,161),(0,0,0),(14,2,164),(0,77,154),(0,0,0),(0,0,0),(0,8,172),(1,8,172),(0,33,169),(0,0,0),(4,2,172),(0,42,167),(0,0,0),(0,0,0),(2,8,172),(4,3,172),(2,33,169),(0,0,0),(3,7,172),(2,42,167),(0,0,0),(0,0,0),(3,66,159),(0,9,172),(1,9,172),(0,0,0),(0,38,168),(0,113,130),(0,0,0),(0,0,0),(0,46,166),(1,46,166),(0,93,145),(0,0,0),(2,38,168),(2,113,130),(0,0,0),(0,0,0),(2,46,166),(5,84,150),(0,21,171),(0,0,0),(0,10,172),(1,10,172),(0,0,0),(0,0,0),(7,28,169),(6,87,148),(0,71,157),(0,0,0),(2,10,172),(4,27,170),(0,0,0),(0,0,0),(0,64,160),(1,64,160),(2,71,157),(0,0,0),(8,78,152),(3,93,145),(0,0,0),(0,0,0),(2,64,160),(0,11,172),(1,11,172),(0,0,0),(6,44,166),(0,90,147),(0,0,0),(0,0,0),(4,8,172),(2,11,172),(4,33,169),(0,0,0),(8,98,140),(0,34,169),(0,0,0),(0,0,0),(6,80,152),(7,53,163),(5,86,149),(0,0,0),(11,13,168),(0,22,171),(0,0,0),(0,0,0),(0,12,172),(1,12,172),(10,13,169),(0,0,0),(0,106,136),(1,106,136),(0,0,0),(0,0,0),(2,12,172),(6,60,161),(0,43,167),(0,0,0),(2,106,136),(0,29,170),(0,0,0),(0,0,0),(3,34,169),(0,39,168),(1,39,168),(0,0,0),(4,10,172),(2,29,170),(0,0,0),(0,0,0),(3,22,171),(0,13,172),(1,13,172),(0,0,0),(18,100,118),(8,2,171),(0,0,0),(0,0,0),(4,64,160),(0,95,144),(1,95,144),(0,0,0),(11,73,152),(0,47,166),(0,0,0),(0,0,0),(0,98,142),(1,98,142),(0,23,171),(0,0,0),(3,39,168),(2,47,166),(0,0,0),(0,0,0),(0,120,124),(1,120,124),(2,23,171),(0,0,0),(0,14,172),(1,14,172),(0,0,0),(0,0,0),(2,120,124),(6,63,160),(0,35,169),(0,0,0),(2,14,172),(0,110,133),(0,0,0),(0,0,0),(3,47,166),(5,38,168),(0,105,137),(0,0,0),(4,106,136),(2,110,133),(0,0,0),(0,0,0),(0,30,170),(0,76,155),(1,76,155),(0,0,0),(6,2,172),(4,29,170),(0,0,0),(0,0,0),(2,30,170),(0,15,172),(1,15,172),(0,0,0),(0,54,164),(1,54,164),(0,0,0),(0,0,0),(3,110,133),(0,24,171),(0,57,163),(0,0,0),(2,54,164),(3,105,137),(0,0,0),(0,0,0),(0,40,168),(0,44,167),(0,51,165),(0,0,0),(0,82,152),(1,82,152),(0,0,0),(0,0,0),(2,40,168),(0,72,157),(1,72,157),(0,0,0),(2,82,152),(0,109,134),(0,0,0),(0,0,0),(0,16,172),(1,16,172),(5,34,169),(0,0,0),(0,60,162),(1,60,162),(0,0,0),(0,0,0),(2,16,172),(6,7,172),(4,35,169),(0,0,0),(2,60,162),(3,51,165),(0,0,0),(0,0,0),(14,106,126),(0,36,169),(0,97,143),(0,0,0),(0,48,166),(0,31,170),(0,0,0),(0,0,0),(0,70,158),(1,70,158),(0,25,171),(0,0,0),(2,48,166),(2,31,170),(0,0,0),(0,0,0),(2,70,158),(0,17,172),(1,17,172),(0,0,0),(4,54,164),(13,28,164),(0,0,0),(0,0,0),(7,119,124),(0,100,141),(1,100,141),(0,0,0),(3,36,169),(3,97,143),(0,0,0),(0,0,0),(3,31,170),(0,108,135),(0,63,161),(0,0,0),(4,82,152),(3,25,171),(0,0,0),(0,0,0),(0,86,150),(1,86,150),(2,63,161),(0,0,0),(3,17,172),(4,109,134),(0,0,0),(0,0,0),(2,86,150),(0,41,168),(1,41,168),(0,0,0),(0,18,172),(1,18,172),(0,0,0),(0,0,0),(6,64,160),(2,41,168),(0,45,167),(0,0,0),(2,18,172),(0,26,171),(0,0,0),(0,0,0),(12,36,164),(0,55,164),(1,55,164),(0,0,0),(0,32,170),(1,32,170),(0,0,0),(0,0,0),(4,70,158),(0,0,173),(0,1,173),(0,0,0),(2,32,170),(0,2,173),(0,0,0),(0,0,0),(7,3,172),(2,0,173),(0,3,173),(0,0,0),(7,86,149),(2,2,173),(0,0,0),(0,0,0),(3,26,171),(0,4,173),(1,4,173),(0,0,0),(3,55,164),(5,40,168),(0,0,0),(0,0,0),(0,96,144),(1,96,144),(0,5,173),(0,0,0),(0,66,160),(0,49,166),(0,0,0),(0,0,0),(2,96,144),(0,75,156),(1,75,156),(0,0,0),(2,66,160),(0,6,173),(0,0,0),(0,0,0),(0,112,132),(1,112,132),(0,27,171),(0,0,0),(3,4,173),(2,6,173),(0,0,0),(0,0,0),(2,112,132),(6,95,144),(0,7,173),(0,0,0),(7,66,159),(3,5,173),(0,0,0),(0,0,0),(0,20,172),(1,20,172),(2,7,173),(0,0,0),(0,42,168),(0,33,170),(0,0,0),(0,0,0),(2,20,172),(0,8,173),(1,8,173),(0,0,0),(2,42,168),(2,33,170),(0,0,0),(0,0,0)]

def wits_30 : List (ℕ × ℕ × ℕ) := [(10,10,170),(2,8,173),(4,3,173),(0,0,0),(0,90,148),(0,38,169),(0,0,0),(0,0,0),(7,9,172),(4,4,173),(0,9,173),(0,0,0),(2,90,148),(0,122,123),(0,0,0),(0,0,0),(3,33,170),(0,64,161),(1,64,161),(0,0,0),(3,8,173),(2,122,123),(0,0,0),(0,0,0),(19,43,146),(0,21,172),(0,85,151),(0,0,0),(6,54,164),(0,10,173),(0,0,0),(0,0,0),(0,56,164),(1,56,164),(0,53,165),(0,0,0),(8,110,132),(0,119,126),(0,0,0),(0,0,0),(2,56,164),(6,44,167),(0,69,159),(0,0,0),(3,64,161),(2,119,126),(0,0,0),(0,0,0),(4,20,172),(5,32,170),(0,11,173),(0,0,0),(3,21,172),(0,98,143),(0,0,0),(0,0,0),(0,34,170),(1,34,170),(2,11,173),(0,0,0),(6,60,162),(2,98,143),(0,0,0),(0,0,0),(2,34,170),(10,29,168),(10,71,155),(0,0,0),(0,22,172),(0,87,150),(0,0,0),(0,0,0),(11,79,150),(0,12,173),(1,12,173),(0,0,0),(2,22,172),(2,87,150),(0,0,0),(0,0,0),(3,98,143),(2,12,173),(0,29,171),(0,0,0),(7,29,170),(8,97,142),(0,0,0),(0,0,0),(0,62,162),(0,67,160),(1,67,160),(0,0,0),(15,86,139),(4,10,173),(0,0,0),(0,0,0),(2,62,162),(0,116,129),(0,13,173),(0,0,0),(3,12,173),(4,119,126),(0,0,0),(0,0,0),(7,95,144),(2,116,129),(0,109,135),(0,0,0),(7,47,166),(0,78,155),(0,0,0),(0,0,0),(0,76,156),(0,23,172),(1,23,172),(0,0,0),(0,80,154),(1,80,154),(0,0,0),(0,0,0),(2,76,156),(2,23,172),(0,89,149),(0,0,0),(2,80,154),(0,14,173),(0,0,0),(0,0,0),(18,86,130),(5,90,148),(2,89,149),(0,0,0),(4,22,172),(0,82,153),(0,0,0),(0,0,0),(3,78,155),(0,104,139),(1,104,139),(0,0,0),(3,23,172),(0,30,171),(0,0,0),(0,0,0),(7,76,155),(0,57,164),(0,65,161),(0,0,0),(0,72,158),(1,72,158),(0,0,0),(0,0,0),(0,94,146),(1,94,146),(0,15,173),(0,0,0),(2,72,158),(0,51,166),(0,0,0),(0,0,0),(0,24,172),(0,40,169),(1,40,169),(0,0,0),(0,100,142),(1,100,142),(0,0,0),(0,0,0),(2,24,172),(0,60,163),(1,60,163),(0,0,0),(2,100,142),(3,65,161),(0,0,0),(0,0,0),(4,76,156),(2,60,163),(5,98,143),(0,0,0),(4,80,154),(0,70,159),(0,0,0),(0,0,0),(3,51,166),(0,16,173),(1,16,173),(0,0,0),(3,40,169),(2,70,159),(0,0,0),(0,0,0),(10,74,154),(0,48,167),(1,48,167),(0,0,0),(0,36,170),(0,86,151),(0,0,0),(0,0,0),(6,20,172),(2,48,167),(0,31,171),(0,0,0),(2,36,170),(2,86,151),(0,0,0),(0,0,0),(3,70,159),(0,25,172),(1,25,172),(0,0,0),(3,16,173),(0,63,162),(0,0,0),(0,0,0),(4,94,146),(2,25,172),(0,17,173),(0,0,0),(3,48,167),(2,63,162),(0,0,0),(0,0,0),(0,68,160),(1,68,160),(2,17,173),(0,0,0),(4,100,142),(3,31,171),(0,0,0),(0,0,0),(2,68,160),(0,112,133),(1,112,133),(0,0,0),(3,25,172),(5,76,156),(0,0,0),(0,0,0),(3,63,162),(0,96,145),(0,41,169),(0,0,0),(0,88,150),(1,88,150),(0,0,0),(0,0,0),(6,56,164),(0,45,168),(0,55,165),(0,0,0),(2,88,150),(0,18,173),(0,0,0),(0,0,0),(11,5,170),(2,45,168),(0,93,147),(0,0,0),(0,26,172),(1,26,172),(0,0,0),(0,0,0),(7,55,164),(0,32,171),(0,79,155),(0,0,0),(2,26,172),(0,37,170),(0,0,0),(0,0,0),(6,34,170),(2,32,171),(0,75,157),(0,0,0),(0,0,174),(0,1,174),(0,0,0),(0,0,0),(0,2,174),(1,2,174),(2,75,157),(0,0,0),(2,0,174),(0,3,174),(0,0,0),(0,0,0),(2,2,174),(5,100,142),(0,19,173),(0,0,0),(0,4,174),(0,73,158),(0,0,0),(0,0,0),(3,37,170),(4,112,133),(0,83,153),(0,0,0),(2,4,174),(0,5,174),(0,0,0),(0,0,0),(3,1,174),(4,96,145),(2,83,153),(0,0,0),(0,118,128),(1,118,128),(0,0,0),(0,0,0),(0,6,174),(0,27,172),(1,27,172),(0,0,0),(2,118,128),(3,19,173),(0,0,0),(0,0,0),(2,6,174),(2,27,172),(0,71,159),(0,0,0),(4,26,172),(0,7,174),(0,0,0),(0,0,0),(3,5,174),(0,20,173),(0,33,171),(0,0,0),(6,80,154),(2,7,174),(0,0,0),(0,0,0),(7,8,173),(2,20,173),(2,33,171),(0,0,0),(0,8,174),(0,95,146),(0,0,0),(0,0,0),(0,38,170),(1,38,170),(0,105,139),(0,0,0),(2,8,174),(2,95,146),(0,0,0),(0,0,0),(2,38,170),(6,104,139),(2,105,139),(0,0,0),(0,116,130),(0,9,174),(0,0,0),(0,0,0),(7,64,161),(0,56,165),(1,56,165),(0,0,0),(2,116,130),(0,53,166),(0,0,0),(0,0,0),(0,28,172),(1,28,172),(0,21,173),(0,0,0),(4,118,128),(2,53,166),(0,0,0),(0,0,0),(0,10,174),(0,59,164),(1,59,164),(0,0,0),(6,100,142),(14,9,166),(0,0,0),(0,0,0),(2,10,174),(2,59,164),(0,115,131),(0,0,0),(3,56,165),(0,50,167),(0,0,0),(0,0,0),(3,53,166),(4,20,173),(2,115,131),(0,0,0),(7,98,143),(0,11,174),(0,0,0),(0,0,0),(11,13,170),(5,0,174),(5,1,174),(0,0,0),(3,59,164),(2,11,174),(0,0,0),(0,0,0),(4,38,170),(6,48,167),(0,43,169),(0,0,0),(6,36,170),(0,22,173),(0,0,0),(0,0,0),(0,104,140),(1,104,140),(2,43,169),(0,0,0),(0,12,174),(0,39,170),(0,0,0),(0,0,0),(2,104,140),(0,29,172),(1,29,172),(0,0,0),(2,12,174),(2,39,170),(0,0,0),(0,0,0),(4,28,172),(0,47,168),(0,97,145),(0,0,0),(8,32,170),(3,43,169),(0,0,0),(0,0,0),(0,74,158),(1,74,158),(2,97,145),(0,0,0),(10,62,160),(0,13,174),(0,0,0),(0,0,0),(2,74,158),(0,100,143),(1,100,143),(0,0,0),(3,29,172),(2,13,174),(0,0,0),(0,0,0),(7,23,172),(2,100,143),(0,23,173),(0,0,0),(3,47,168),(3,97,145),(0,0,0),(0,0,0),(8,96,144),(0,72,159),(0,35,171),(0,0,0),(7,14,173),(0,65,162),(0,0,0),(0,0,0),(0,14,174),(1,14,174),(0,57,165),(0,0,0),(3,100,143),(2,65,162),(0,0,0),(0,0,0),(2,14,174),(5,116,130),(0,91,149),(0,0,0),(0,30,172),(1,30,172),(0,0,0),(0,0,0),(7,57,164),(4,29,172),(0,51,167),(0,0,0),(2,30,172),(0,107,138),(0,0,0),(0,0,0),(0,60,164),(0,44,169),(1,44,169),(0,0,0),(0,40,170),(0,15,174),(0,0,0),(0,0,0),(2,60,164),(0,24,173),(1,24,173),(0,0,0),(2,40,170),(0,122,125),(0,0,0),(0,0,0),(7,60,163),(2,24,173),(5,50,167),(0,0,0),(8,90,148),(0,121,126),(0,0,0),(0,0,0),(3,107,138),(10,60,161),(4,23,173),(0,0,0),(3,44,169),(2,121,126),(0,0,0),(0,0,0),(0,48,168),(0,120,127),(1,120,127),(0,0,0),(0,16,174),(1,16,174),(0,0,0),(0,0,0),(2,48,168),(0,36,171),(0,63,163),(0,0,0),(2,16,174),(5,104,140),(0,0,0),(0,0,0),(3,121,126),(0,31,172),(0,111,135),(0,0,0),(4,30,172),(8,119,126),(0,0,0),(0,0,0),(7,25,172),(0,93,148),(0,25,173),(0,0,0),(3,120,127),(0,106,139),(0,0,0),(0,0,0),(4,60,164),(2,93,148),(2,25,173),(0,0,0),(3,36,171),(0,17,174),(0,0,0),(0,0,0),(0,102,142),(1,102,142),(5,13,174),(0,0,0),(3,31,172),(2,17,174),(0,0,0),(0,0,0),(2,102,142),(0,79,156),(0,77,157),(0,0,0),(3,93,148),(0,41,170),(0,0,0),(0,0,0),(3,106,139),(2,79,156),(0,45,169),(0,0,0),(10,2,172),(0,58,165),(0,0,0),(0,0,0),(3,17,174),(0,52,167),(1,52,167),(0,0,0),(0,110,136),(1,110,136),(0,0,0),(0,0,0),(0,18,174),(1,18,174),(4,63,163),(0,0,0),(2,110,136),(0,26,173),(0,0,0),(0,0,0),(0,32,172),(1,32,172),(0,37,171),(0,0,0),(7,37,170),(2,26,173),(0,0,0),(0,0,0),(2,32,172),(0,61,164),(1,61,164),(0,0,0),(3,52,167),(4,106,139),(0,0,0),(0,0,0),(8,76,156),(0,0,175),(0,1,175),(0,0,0),(7,3,174),(0,2,175),(0,0,0),(0,0,0),(3,26,173),(2,0,175),(0,3,175),(0,0,0),(6,12,174),(0,19,174),(0,0,0),(0,0,0),(23,28,133),(0,4,175),(1,4,175),(0,0,0),(3,61,164),(2,19,174),(0,0,0),(0,0,0),(10,8,172),(0,115,132),(0,5,175),(0,0,0),(3,0,175),(3,1,175),(0,0,0),(0,0,0),(3,2,175),(2,115,132),(0,27,173),(0,0,0),(4,110,136),(0,6,175),(0,0,0),(0,0,0),(0,42,170),(0,64,163),(1,64,163),(0,0,0),(3,4,175),(2,6,175),(0,0,0),(0,0,0),(2,42,170),(0,33,172),(0,7,175),(0,0,0),(0,20,174),(0,46,169),(0,0,0),(0,0,0),(14,60,156),(2,33,172),(0,69,161),(0,0,0),(2,20,174),(0,38,171),(0,0,0),(0,0,0),(3,6,175),(0,8,175),(1,8,175),(0,0,0),(0,56,166),(1,56,166),(0,0,0),(0,0,0),(10,64,160),(0,104,141),(0,53,167),(0,0,0),(2,56,166),(3,7,175),(0,0,0),(0,0,0),(3,46,169),(2,104,141),(0,9,175),(0,0,0),(0,108,138),(1,108,138),(0,0,0),(0,0,0),(3,38,171),(0,28,173),(1,28,173),(0,0,0),(2,108,138),(0,21,174),(0,0,0),(0,0,0),(7,59,164),(2,28,173),(0,89,151),(0,0,0),(0,50,168),(0,10,175),(0,0,0),(0,0,0),(4,42,170),(4,64,163),(2,89,151),(0,0,0),(2,50,168),(0,67,162),(0,0,0),(0,0,0),(0,80,156),(1,80,156),(4,7,175),(0,0,0),(0,34,172),(1,34,172),(0,0,0),(0,0,0),(2,80,156),(6,120,127),(0,11,175),(0,0,0),(2,34,172),(0,43,170),(0,0,0),(0,0,0),(0,124,124),(1,124,124),(0,123,125),(0,0,0),(4,56,166),(0,74,159),(0,0,0),(0,0,0),(0,22,174),(1,22,174),(0,39,171),(0,0,0),(7,39,170),(2,74,159),(0,0,0),(0,0,0),(2,22,174),(0,12,175),(0,29,173),(0,0,0),(0,84,154),(0,103,142),(0,0,0),(0,0,0),(3,43,170),(2,12,175),(2,29,173),(0,0,0),(2,84,154),(0,91,150),(0,0,0),(0,0,0),(0,72,160),(1,72,160),(4,89,151),(0,0,0),(4,50,168),(2,91,150),(0,0,0),(0,0,0),(2,72,160),(6,79,156),(0,13,175),(0,0,0),(3,12,175),(3,29,173),(0,0,0),(0,0,0),(3,103,142),(5,20,174),(0,119,129),(0,0,0),(4,34,172),(0,23,174),(0,0,0),(0,0,0),(3,91,150),(0,35,172),(1,35,172),(0,0,0),(6,110,136),(2,23,174),(0,0,0),(0,0,0),(4,124,124),(0,111,136),(1,111,136),(0,0,0),(8,118,128),(0,14,175),(0,0,0),(0,0,0),(0,118,130),(0,51,168),(0,99,145),(0,0,0),(10,82,152),(0,30,173),(0,0,0),(0,0,0),(2,118,130),(2,51,168),(2,99,145),(0,0,0),(0,44,170),(1,44,170),(0,0,0),(0,0,0),(7,44,169),(0,40,171),(1,40,171),(0,0,0),(2,44,170),(4,91,150),(0,0,0),(0,0,0),(0,88,152),(1,88,152),(0,15,175),(0,0,0),(0,24,174),(0,102,143),(0,0,0),(0,0,0),(2,88,152),(6,4,175),(2,15,175),(0,0,0),(2,24,174),(2,102,143),(0,0,0),(0,0,0),(10,70,158),(0,48,169),(1,48,169),(0,0,0),(0,68,162),(0,110,137),(0,0,0),(0,0,0),(7,120,127),(2,48,169),(5,43,170),(0,0,0),(2,68,162),(2,110,137),(0,0,0),(0,0,0),(0,36,172),(0,16,175),(1,16,175),(0,0,0),(12,16,170),(4,14,175),(0,0,0),(0,0,0),(2,36,172),(2,16,175),(0,31,173),(0,0,0),(3,48,169),(0,77,158),(0,0,0),(0,0,0),(3,110,137),(0,81,156),(1,81,156),(0,0,0),(4,44,170),(0,25,174),(0,0,0),(0,0,0),(11,97,142),(2,81,156),(0,75,159),(0,0,0),(3,16,175),(2,25,174),(0,0,0),(0,0,0),(4,88,152),(6,104,141),(0,17,175),(0,0,0),(4,24,174),(3,31,173),(0,0,0),(0,0,0),(0,58,166),(1,58,166),(0,41,171),(0,0,0),(3,81,156),(0,45,170),(0,0,0),(0,0,0),(0,52,168),(0,73,160),(1,73,160),(0,0,0),(4,68,162),(2,45,170),(0,0,0),(0,0,0),(2,52,168),(0,101,144),(1,101,144),(0,0,0),(6,50,168),(0,85,154),(0,0,0),(0,0,0),(4,36,172),(2,101,144),(0,61,165),(0,0,0),(7,26,173),(0,18,175),(0,0,0),(0,0,0),(0,26,174),(0,32,173),(1,32,173),(0,0,0),(3,73,160),(2,18,175),(0,0,0),(0,0,0),(2,26,174),(2,32,173),(0,49,169),(0,0,0),(0,92,150),(1,92,150),(0,0,0),(0,0,0),(3,85,154),(7,1,175),(2,49,169),(0,0,0),(2,92,150),(3,61,165),(0,0,0),(0,0,0),(0,0,176),(0,1,176),(0,87,153),(0,0,0),(0,2,176),(1,2,176),(0,0,0),(0,0,0),(2,0,176),(0,3,176),(0,19,175),(0,0,0),(2,2,176),(3,49,169),(0,0,0),(0,0,0),(0,4,176),(1,4,176),(0,113,135),(0,0,0),(8,30,172),(6,91,150),(0,0,0),(0,0,0)]

def wits_31 : List (ℕ × ℕ × ℕ) := [(2,4,176),(0,5,176),(1,5,176),(0,0,0),(3,1,176),(0,27,174),(0,0,0),(0,0,0),(7,64,163),(2,5,176),(4,61,165),(0,0,0),(0,6,176),(0,122,127),(0,0,0),(0,0,0),(0,46,170),(1,46,170),(0,33,173),(0,0,0),(2,6,176),(2,122,127),(0,0,0),(0,0,0),(2,46,170),(0,7,176),(1,7,176),(0,0,0),(0,38,172),(1,38,172),(0,0,0),(0,0,0),(3,27,174),(0,53,168),(1,53,168),(0,0,0),(2,38,172),(0,59,166),(0,0,0),(0,0,0),(0,8,176),(0,120,129),(1,120,129),(0,0,0),(4,2,176),(2,59,166),(0,0,0),(0,0,0),(0,78,158),(0,80,157),(1,80,157),(0,0,0),(3,7,176),(5,52,168),(0,0,0),(0,0,0),(2,78,158),(0,9,176),(0,67,163),(0,0,0),(0,28,174),(0,50,169),(0,0,0),(0,0,0),(3,59,166),(2,9,176),(0,21,175),(0,0,0),(2,28,174),(0,62,165),(0,0,0),(0,0,0),(11,29,170),(9,38,170),(2,21,175),(0,0,0),(0,10,176),(1,10,176),(0,0,0),(0,0,0),(4,46,170),(0,84,155),(0,91,151),(0,0,0),(2,10,176),(0,34,173),(0,0,0),(0,0,0),(3,50,169),(2,84,155),(0,43,171),(0,0,0),(4,38,172),(2,34,173),(0,0,0),(0,0,0),(3,62,165),(0,11,176),(1,11,176),(0,0,0),(7,74,159),(4,59,166),(0,0,0),(0,0,0),(4,8,176),(0,39,172),(1,39,172),(0,0,0),(3,84,155),(0,22,175),(0,0,0),(0,0,0),(0,86,154),(0,117,132),(1,117,132),(0,0,0),(7,103,142),(0,29,174),(0,0,0),(0,0,0),(0,12,176),(0,65,164),(1,65,164),(0,0,0),(3,11,176),(2,29,174),(0,0,0),(0,0,0),(2,12,176),(2,65,164),(4,21,175),(0,0,0),(3,39,172),(4,62,165),(0,0,0),(0,0,0),(3,22,175),(5,6,176),(0,57,167),(0,0,0),(0,54,168),(1,54,168),(0,0,0),(0,0,0),(0,70,162),(0,13,176),(1,13,176),(0,0,0),(2,54,168),(0,93,150),(0,0,0),(0,0,0),(2,70,162),(0,88,153),(0,23,175),(0,0,0),(0,60,166),(1,60,166),(0,0,0),(0,0,0),(7,111,136),(2,88,153),(0,51,169),(0,0,0),(2,60,166),(3,57,167),(0,0,0),(0,0,0),(6,26,174),(4,39,172),(2,51,169),(0,0,0),(0,14,176),(1,14,176),(0,0,0),(0,0,0),(0,30,174),(0,44,171),(1,44,171),(0,0,0),(2,14,176),(0,115,134),(0,0,0),(0,0,0),(0,40,172),(1,40,172),(5,50,169),(0,0,0),(8,20,174),(0,105,142),(0,0,0),(0,0,0),(2,40,172),(0,68,163),(0,63,165),(0,0,0),(6,2,176),(2,105,142),(0,0,0),(0,0,0),(14,30,166),(0,15,176),(0,109,139),(0,0,0),(0,48,170),(0,79,158),(0,0,0),(0,0,0),(3,115,134),(2,15,176),(0,77,159),(0,0,0),(2,48,170),(0,98,147),(0,0,0),(0,0,0),(3,105,142),(4,88,153),(2,77,159),(0,0,0),(3,68,163),(0,114,135),(0,0,0),(0,0,0),(7,16,175),(0,36,173),(0,95,149),(0,0,0),(3,15,176),(2,114,135),(0,0,0),(0,0,0),(0,16,176),(1,16,176),(2,95,149),(0,0,0),(4,14,176),(0,31,174),(0,0,0),(0,0,0),(2,16,176),(4,44,171),(5,29,174),(0,0,0),(6,38,172),(2,31,174),(0,0,0),(0,0,0),(3,114,135),(0,55,168),(0,25,175),(0,0,0),(0,66,164),(0,58,167),(0,0,0),(0,0,0),(6,8,176),(2,55,168),(0,123,127),(0,0,0),(2,66,164),(2,58,167),(0,0,0),(0,0,0),(0,108,140),(0,17,176),(0,45,171),(0,0,0),(0,122,128),(1,122,128),(0,0,0),(0,0,0),(2,108,140),(2,17,176),(2,45,171),(0,0,0),(2,122,128),(0,61,166),(0,0,0),(0,0,0),(3,58,167),(5,60,166),(0,121,129),(0,0,0),(7,85,154),(0,71,162),(0,0,0),(0,0,0),(11,49,166),(4,36,173),(2,121,129),(0,0,0),(3,17,176),(2,71,162),(0,0,0),(0,0,0),(4,16,176),(5,14,176),(0,37,173),(0,0,0),(0,18,176),(0,26,175),(0,0,0),(0,0,0),(3,61,166),(7,49,169),(2,37,173),(0,0,0),(2,18,176),(2,26,175),(0,0,0),(0,0,0),(3,71,162),(0,97,148),(1,97,148),(0,0,0),(0,100,146),(1,100,146),(0,0,0),(0,0,0),(7,1,176),(0,64,165),(0,119,131),(0,0,0),(2,100,146),(3,37,173),(0,0,0),(0,0,0),(3,26,175),(0,0,177),(0,1,177),(0,0,0),(4,122,128),(0,2,177),(0,0,0),(0,0,0),(0,94,150),(0,19,176),(0,3,177),(0,0,0),(3,97,148),(2,2,177),(0,0,0),(0,0,0),(2,94,150),(0,4,177),(1,4,177),(0,0,0),(0,42,172),(1,42,172),(0,0,0),(0,0,0),(15,76,149),(2,4,177),(0,5,177),(0,0,0),(2,42,172),(0,46,171),(0,0,0),(0,0,0),(0,56,168),(1,56,168),(2,5,177),(0,0,0),(0,80,158),(0,6,177),(0,0,0),(0,0,0),(2,56,168),(6,88,153),(0,53,169),(0,0,0),(2,80,158),(0,38,173),(0,0,0),(0,0,0),(0,20,176),(1,20,176),(0,7,177),(0,0,0),(4,100,146),(2,38,173),(0,0,0),(0,0,0),(2,20,176),(0,67,164),(1,67,164),(0,0,0),(6,14,176),(5,108,140),(0,0,0),(0,0,0),(0,84,156),(0,8,177),(1,8,177),(0,0,0),(12,38,168),(0,74,161),(0,0,0),(0,0,0),(0,50,170),(1,50,170),(4,3,177),(0,0,0),(7,50,169),(2,74,161),(0,0,0),(0,0,0),(2,50,170),(0,28,175),(0,9,177),(0,0,0),(0,116,134),(1,116,134),(0,0,0),(0,0,0),(10,104,140),(0,21,176),(1,21,176),(0,0,0),(2,116,134),(0,86,155),(0,0,0),(0,0,0),(3,74,161),(2,21,176),(5,26,175),(0,0,0),(0,72,162),(0,10,177),(0,0,0),(0,0,0),(0,34,174),(0,43,172),(1,43,172),(0,0,0),(2,72,162),(2,10,177),(0,0,0),(0,0,0),(2,34,174),(2,43,172),(4,7,177),(0,0,0),(3,21,176),(10,13,174),(0,0,0),(0,0,0),(3,86,155),(4,67,164),(0,11,177),(0,0,0),(7,22,175),(6,31,174),(0,0,0),(0,0,0),(3,10,177),(4,8,177),(2,11,177),(0,0,0),(0,22,176),(1,22,176),(0,0,0),(0,0,0),(4,50,170),(6,55,168),(0,29,175),(0,0,0),(2,22,176),(0,70,163),(0,0,0),(0,0,0),(10,14,174),(0,12,177),(0,105,143),(0,0,0),(4,116,134),(0,54,169),(0,0,0),(0,0,0),(6,108,140),(0,109,140),(1,109,140),(0,0,0),(6,122,128),(2,54,169),(0,0,0),(0,0,0),(7,13,176),(0,60,167),(1,60,167),(0,0,0),(0,114,136),(1,114,136),(0,0,0),(0,0,0),(3,70,163),(2,60,167),(0,13,177),(0,0,0),(2,114,136),(0,35,174),(0,0,0),(0,0,0),(3,54,169),(0,23,176),(1,23,176),(0,0,0),(0,98,148),(0,90,153),(0,0,0),(0,0,0),(11,70,159),(0,123,128),(1,123,128),(0,0,0),(2,98,148),(0,101,146),(0,0,0),(0,0,0),(0,44,172),(1,44,172),(0,79,159),(0,0,0),(4,22,176),(0,14,177),(0,0,0),(0,0,0),(2,44,172),(0,40,173),(1,40,173),(0,0,0),(3,23,176),(2,14,177),(0,0,0),(0,0,0),(3,90,153),(2,40,173),(0,83,157),(0,0,0),(3,123,128),(0,121,130),(0,0,0),(0,0,0),(3,101,146),(0,48,171),(0,75,161),(0,0,0),(7,79,158),(2,121,130),(0,0,0),(0,0,0),(0,24,176),(1,24,176),(0,15,177),(0,0,0),(3,40,173),(5,34,174),(0,0,0),(0,0,0),(2,24,176),(0,85,156),(1,85,156),(0,0,0),(6,42,172),(3,83,157),(0,0,0),(0,0,0),(0,92,152),(1,92,152),(6,5,177),(0,0,0),(0,36,174),(0,73,162),(0,0,0),(0,0,0),(2,92,152),(4,123,128),(8,21,175),(0,0,0),(2,36,174),(0,66,165),(0,0,0),(0,0,0),(4,44,172),(0,16,177),(0,31,175),(0,0,0),(0,58,168),(1,58,168),(0,0,0),(0,0,0),(6,20,176),(2,16,177),(0,87,155),(0,0,0),(2,58,168),(8,34,173),(0,0,0),(0,0,0),(3,73,162),(0,25,176),(1,25,176),(0,0,0),(0,52,170),(1,52,170),(0,0,0),(0,0,0),(3,66,165),(0,45,172),(0,41,173),(0,0,0),(2,52,170),(0,107,142),(0,0,0),(0,0,0),(4,24,176),(2,45,172),(0,17,177),(0,0,0),(7,61,166),(2,107,142),(0,0,0),(0,0,0),(8,86,154),(4,85,156),(2,17,177),(0,0,0),(3,25,176),(8,29,174),(0,0,0),(0,0,0),(4,92,152),(5,98,148),(0,103,145),(0,0,0),(3,45,172),(0,89,154),(0,0,0),(0,0,0),(3,107,142),(7,37,173),(0,49,171),(0,0,0),(6,72,162),(0,37,174),(0,0,0),(0,0,0),(6,34,174),(0,32,175),(1,32,175),(0,0,0),(0,26,176),(0,18,177),(0,0,0),(0,0,0),(7,97,148),(0,69,164),(1,69,164),(0,0,0),(2,26,176),(2,18,177),(0,0,0),(0,0,0),(3,89,154),(2,69,164),(5,121,130),(0,0,0),(4,52,170),(3,49,171),(0,0,0),(0,0,0),(3,37,174),(4,45,172),(4,41,173),(0,0,0),(3,32,175),(4,107,142),(0,0,0),(0,0,0),(3,18,177),(0,80,159),(1,80,159),(0,0,0),(0,0,178),(0,1,178),(0,0,0),(0,0,0),(0,2,178),(1,2,178),(0,19,177),(0,0,0),(2,0,178),(0,3,178),(0,0,0),(0,0,0),(2,2,178),(0,56,169),(1,56,169),(0,0,0),(0,4,178),(1,4,178),(0,0,0),(0,0,0),(14,68,156),(0,27,176),(1,27,176),(0,0,0),(2,4,178),(0,5,178),(0,0,0),(0,0,0),(3,1,178),(2,27,176),(0,33,175),(0,0,0),(0,96,150),(1,96,150),(0,0,0),(0,0,0),(0,6,178),(0,115,136),(1,115,136),(0,0,0),(2,96,150),(6,90,153),(0,0,0),(0,0,0),(2,6,178),(0,20,177),(1,20,177),(0,0,0),(0,86,156),(0,7,178),(0,0,0),(0,0,0),(3,5,178),(2,20,177),(5,107,142),(0,0,0),(2,86,156),(0,50,171),(0,0,0),(0,0,0),(8,16,176),(4,80,159),(10,11,175),(0,0,0),(0,8,178),(1,8,178),(0,0,0),(0,0,0),(0,126,126),(0,72,163),(0,125,127),(0,0,0),(2,8,178),(4,3,178),(0,0,0),(0,0,0),(0,28,176),(0,105,144),(0,109,141),(0,0,0),(4,4,178),(0,9,178),(0,0,0),(0,0,0),(2,28,176),(0,88,155),(0,21,177),(0,0,0),(7,10,177),(2,9,178),(0,0,0),(0,0,0),(7,43,172),(2,88,155),(0,43,173),(0,0,0),(3,72,163),(0,34,175),(0,0,0),(0,0,0),(0,10,178),(1,10,178),(2,43,173),(0,0,0),(3,105,144),(2,34,175),(0,0,0),(0,0,0),(2,10,178),(0,47,172),(1,47,172),(0,0,0),(0,70,164),(0,39,174),(0,0,0),(0,0,0),(11,65,162),(2,47,172),(0,121,131),(0,0,0),(2,70,164),(0,11,178),(0,0,0),(0,0,0),(3,34,175),(5,0,178),(0,57,169),(0,0,0),(4,8,178),(0,22,177),(0,0,0),(0,0,0),(0,54,170),(0,29,176),(1,29,176),(0,0,0),(3,47,172),(2,22,177),(0,0,0),(0,0,0),(0,60,168),(1,60,168),(0,95,151),(0,0,0),(0,12,178),(1,12,178),(0,0,0),(0,0,0),(2,60,168),(4,88,155),(2,95,151),(0,0,0),(2,12,178),(3,57,169),(0,0,0),(0,0,0),(3,22,177),(0,79,160),(0,51,171),(0,0,0),(3,29,176),(4,34,175),(0,0,0),(0,0,0),(4,10,178),(0,68,165),(0,35,175),(0,0,0),(7,90,153),(0,13,178),(0,0,0),(0,0,0),(7,123,128),(2,68,165),(0,23,177),(0,0,0),(4,70,164),(2,13,178),(0,0,0),(0,0,0),(23,79,116),(0,44,173),(1,44,173),(0,0,0),(3,79,160),(0,75,162),(0,0,0),(0,0,0),(7,40,173),(0,92,153),(0,85,157),(0,0,0),(0,30,176),(1,30,176),(0,0,0),(0,0,0),(0,14,178),(1,14,178),(2,85,157),(0,0,0),(2,30,176),(3,23,177),(0,0,0),(0,0,0),(0,48,172),(1,48,172),(4,95,151),(0,0,0),(3,44,173),(10,77,158),(0,0,0),(0,0,0),(2,48,172),(6,80,159),(0,73,163),(0,0,0),(3,92,153),(3,85,157),(0,0,0),(0,0,0),(0,100,148),(0,24,177),(1,24,177),(0,0,0),(11,79,156),(0,15,178),(0,0,0),(0,0,0),(0,66,166),(1,66,166),(0,117,135),(0,0,0),(6,4,178),(2,15,178),(0,0,0),(0,0,0),(2,66,166),(0,36,175),(1,36,175),(0,0,0),(7,66,165),(0,55,170),(0,0,0),(0,0,0),(7,16,177),(2,36,175),(5,11,178),(0,0,0),(3,24,177),(2,55,170),(0,0,0),(0,0,0),(3,15,178),(0,31,176),(1,31,176),(0,0,0),(0,16,178),(1,16,178),(0,0,0),(0,0,0),(4,14,178),(0,52,171),(0,89,155),(0,0,0),(2,16,178),(5,60,168),(0,0,0),(0,0,0),(0,116,136),(1,116,136),(0,25,177),(0,0,0),(7,107,142),(0,41,174),(0,0,0),(0,0,0),(2,116,136),(7,17,177),(2,25,177),(0,0,0),(3,31,176),(2,41,174),(0,0,0),(0,0,0),(4,100,148),(4,24,177),(6,125,127),(0,0,0),(0,106,144),(0,17,178),(0,0,0),(0,0,0),(4,66,166),(6,105,144),(4,117,135),(0,0,0),(2,106,144),(0,110,141),(0,0,0),(0,0,0),(3,41,174),(0,49,172),(0,69,165),(0,0,0),(7,37,174),(2,110,141),(0,0,0),(0,0,0),(7,32,175),(2,49,172),(0,37,175),(0,0,0),(7,18,177),(0,91,154),(0,0,0),(0,0,0)]

def wits_32 : List (ℕ × ℕ × ℕ) := [(0,32,176),(1,32,176),(0,99,149),(0,0,0),(4,16,178),(0,26,177),(0,0,0),(0,0,0),(0,18,178),(0,125,128),(1,125,128),(0,0,0),(3,49,172),(0,102,147),(0,0,0),(0,0,0),(2,18,178),(0,96,151),(1,96,151),(0,0,0),(0,76,162),(1,76,162),(0,0,0),(0,0,0),(3,91,154),(2,96,151),(6,57,169),(0,0,0),(2,76,162),(0,123,130),(0,0,0),(0,0,0),(3,26,177),(6,29,176),(5,15,178),(0,0,0),(0,56,170),(1,56,170),(0,0,0),(0,0,0),(0,42,174),(0,0,179),(0,1,179),(0,0,0),(2,56,170),(0,2,179),(0,0,0),(0,0,0),(2,42,174),(2,0,179),(0,3,179),(0,0,0),(7,5,178),(2,2,179),(0,0,0),(0,0,0),(3,123,130),(0,4,179),(0,27,177),(0,0,0),(10,28,174),(4,91,154),(0,0,0),(0,0,0),(4,32,176),(0,33,176),(0,5,179),(0,0,0),(0,62,168),(0,38,175),(0,0,0),(0,0,0),(3,2,179),(2,33,176),(2,5,179),(0,0,0),(2,62,168),(0,6,179),(0,0,0),(0,0,0),(0,72,164),(1,72,164),(5,41,174),(0,0,0),(0,20,178),(1,20,178),(0,0,0),(0,0,0),(2,72,164),(0,120,133),(0,7,179),(0,0,0),(2,20,178),(3,5,179),(0,0,0),(0,0,0),(3,38,175),(2,120,133),(2,7,179),(0,0,0),(4,56,170),(11,29,173),(0,0,0),(0,0,0),(0,98,150),(0,8,179),(1,8,179),(0,0,0),(7,9,178),(4,2,179),(0,0,0),(0,0,0),(2,98,150),(0,28,177),(0,65,167),(0,0,0),(3,120,133),(0,119,134),(0,0,0),(0,0,0),(6,100,148),(2,28,177),(0,9,179),(0,0,0),(7,34,175),(0,21,178),(0,0,0),(0,0,0),(6,66,166),(0,95,152),(1,95,152),(0,0,0),(0,34,176),(1,34,176),(0,0,0),(0,0,0),(7,47,172),(2,95,152),(0,47,173),(0,0,0),(2,34,176),(0,10,179),(0,0,0),(0,0,0),(0,112,140),(1,112,140),(0,39,175),(0,0,0),(4,20,178),(0,57,170),(0,0,0),(0,0,0),(2,112,140),(4,120,133),(2,39,175),(0,0,0),(3,95,152),(0,54,171),(0,0,0),(0,0,0),(7,29,176),(0,60,169),(0,11,179),(0,0,0),(8,26,176),(2,54,171),(0,0,0),(0,0,0),(0,22,178),(1,22,178),(0,29,177),(0,0,0),(10,14,176),(0,77,162),(0,0,0),(0,0,0),(2,22,178),(4,28,177),(2,29,177),(0,0,0),(0,68,166),(1,68,166),(0,0,0),(0,0,0),(3,54,171),(0,12,179),(1,12,179),(0,0,0),(2,68,166),(0,85,158),(0,0,0),(0,0,0),(7,68,165),(0,63,168),(0,75,163),(0,0,0),(4,34,176),(2,85,158),(0,0,0),(0,0,0),(3,77,162),(0,35,176),(0,111,141),(0,0,0),(10,48,170),(4,10,179),(0,0,0),(0,0,0),(4,112,140),(2,35,176),(0,13,179),(0,0,0),(0,44,174),(0,23,178),(0,0,0),(0,0,0),(3,85,158),(7,85,157),(0,87,157),(0,0,0),(2,44,174),(2,23,178),(0,0,0),(0,0,0),(6,18,178),(0,40,175),(1,40,175),(0,0,0),(3,35,176),(0,30,177),(0,0,0),(0,0,0),(4,22,178),(0,48,173),(1,48,173),(0,0,0),(6,76,162),(0,14,179),(0,0,0),(0,0,0),(3,23,178),(2,48,173),(5,119,134),(0,0,0),(4,68,166),(0,66,167),(0,0,0),(0,0,0),(7,24,177),(4,12,179),(5,21,178),(0,0,0),(3,40,175),(2,66,167),(0,0,0),(0,0,0),(3,30,177),(0,89,156),(0,127,127),(0,0,0),(0,24,178),(0,106,145),(0,0,0),(0,0,0),(0,58,170),(1,58,170),(0,15,179),(0,0,0),(2,24,178),(0,115,138),(0,0,0),(0,0,0),(0,36,176),(1,36,176),(2,15,179),(0,0,0),(0,124,130),(1,124,130),(0,0,0),(0,0,0),(2,36,176),(6,33,176),(0,61,169),(0,0,0),(2,124,130),(3,127,127),(0,0,0),(0,0,0),(0,52,172),(1,52,172),(0,31,177),(0,0,0),(19,28,157),(3,15,179),(0,0,0),(0,0,0),(2,52,172),(0,16,179),(1,16,179),(0,0,0),(6,20,178),(0,45,174),(0,0,0),(0,0,0),(23,16,141),(2,16,179),(0,41,175),(0,0,0),(0,102,148),(0,25,178),(0,0,0),(0,0,0),(19,62,147),(10,97,148),(2,41,175),(0,0,0),(2,102,148),(0,69,166),(0,0,0),(0,0,0),(0,64,168),(0,80,161),(1,80,161),(0,0,0),(0,82,160),(1,82,160),(0,0,0),(0,0,0),(0,78,162),(1,78,162),(0,17,179),(0,0,0),(2,82,160),(3,41,175),(0,0,0),(0,0,0),(2,78,162),(0,84,159),(1,84,159),(0,0,0),(4,124,130),(0,105,146),(0,0,0),(0,0,0),(3,69,166),(0,37,176),(1,37,176),(0,0,0),(3,80,161),(2,105,146),(0,0,0),(0,0,0),(4,52,172),(0,32,177),(1,32,177),(0,0,0),(0,120,134),(1,120,134),(0,0,0),(0,0,0),(0,26,178),(1,26,178),(5,14,179),(0,0,0),(2,120,134),(0,18,179),(0,0,0),(0,0,0),(2,26,178),(0,113,140),(1,113,140),(0,0,0),(0,74,164),(1,74,164),(0,0,0),(0,0,0),(10,20,176),(0,56,171),(0,67,167),(0,0,0),(2,74,164),(0,59,170),(0,0,0),(0,0,0),(4,64,168),(2,56,171),(0,119,135),(0,0,0),(4,82,160),(0,42,175),(0,0,0),(0,0,0),(0,46,174),(0,53,172),(1,53,172),(0,0,0),(3,113,140),(2,42,175),(0,0,0),(0,0,0),(0,0,180),(0,1,180),(0,19,179),(0,0,0),(0,2,180),(0,62,169),(0,0,0),(0,0,0),(2,0,180),(0,3,180),(1,3,180),(0,0,0),(2,2,180),(0,27,178),(0,0,0),(0,0,0),(0,4,180),(1,4,180),(0,33,177),(0,0,0),(0,38,176),(1,38,176),(0,0,0),(0,0,0),(2,4,180),(0,5,180),(1,5,180),(0,0,0),(2,38,176),(0,50,173),(0,0,0),(0,0,0),(3,62,169),(2,5,180),(0,95,153),(0,0,0),(0,6,180),(1,6,180),(0,0,0),(0,0,0),(3,27,178),(0,20,179),(1,20,179),(0,0,0),(2,6,180),(3,33,177),(0,0,0),(0,0,0),(7,8,179),(0,7,180),(1,7,180),(0,0,0),(3,5,180),(4,42,175),(0,0,0),(0,0,0),(0,70,166),(1,70,166),(0,117,137),(0,0,0),(7,119,134),(3,95,153),(0,0,0),(0,0,0),(0,8,180),(1,8,180),(2,117,137),(0,0,0),(0,28,178),(1,28,178),(0,0,0),(0,0,0),(2,8,180),(4,3,180),(0,43,175),(0,0,0),(2,28,178),(4,27,178),(0,0,0),(0,0,0),(4,4,180),(0,9,180),(0,21,179),(0,0,0),(4,38,176),(0,34,177),(0,0,0),(0,0,0),(6,36,176),(0,83,160),(0,57,171),(0,0,0),(6,124,130),(2,34,177),(0,0,0),(0,0,0),(23,27,140),(0,39,176),(0,77,163),(0,0,0),(0,10,180),(1,10,180),(0,0,0),(0,0,0),(6,52,172),(2,39,176),(0,85,159),(0,0,0),(2,10,180),(3,21,179),(0,0,0),(0,0,0),(3,34,177),(0,68,167),(1,68,167),(0,0,0),(3,83,160),(0,126,129),(0,0,0),(0,0,0),(4,70,166),(0,11,180),(1,11,180),(0,0,0),(3,39,176),(0,22,179),(0,0,0),(0,0,0),(4,8,180),(2,11,180),(0,51,173),(0,0,0),(4,28,178),(0,87,158),(0,0,0),(0,0,0),(6,64,168),(0,124,131),(1,124,131),(0,0,0),(3,68,167),(2,87,158),(0,0,0),(0,0,0),(0,12,180),(1,12,180),(0,115,139),(0,0,0),(3,11,180),(0,110,143),(0,0,0),(0,0,0),(0,94,154),(0,123,132),(0,35,177),(0,0,0),(7,23,178),(2,110,143),(0,0,0),(0,0,0),(2,94,154),(0,44,175),(1,44,175),(0,0,0),(3,124,131),(13,28,172),(0,0,0),(0,0,0),(7,40,175),(0,13,180),(0,23,179),(0,0,0),(6,120,134),(0,122,133),(0,0,0),(0,0,0),(0,40,176),(1,40,176),(2,23,179),(0,0,0),(0,48,174),(1,48,174),(0,0,0),(0,0,0),(0,30,178),(1,30,178),(10,31,175),(0,0,0),(2,48,174),(4,22,179),(0,0,0),(0,0,0),(2,30,178),(5,28,178),(4,51,173),(0,0,0),(0,14,180),(0,71,166),(0,0,0),(0,0,0),(3,122,133),(4,124,131),(0,99,151),(0,0,0),(2,14,180),(0,58,171),(0,0,0),(0,0,0),(4,12,180),(0,55,172),(1,55,172),(0,0,0),(7,115,138),(2,58,171),(0,0,0),(0,0,0),(4,94,154),(0,24,179),(1,24,179),(0,0,0),(6,2,180),(0,61,170),(0,0,0),(0,0,0),(3,71,166),(0,15,180),(1,15,180),(0,0,0),(19,13,160),(2,61,170),(0,0,0),(0,0,0),(3,58,171),(0,52,173),(0,105,147),(0,0,0),(3,55,172),(4,122,133),(0,0,0),(0,0,0),(4,40,176),(2,52,173),(2,105,147),(0,0,0),(0,80,162),(0,31,178),(0,0,0),(0,0,0),(3,61,170),(7,41,175),(0,45,175),(0,0,0),(2,80,162),(0,78,163),(0,0,0),(0,0,0),(0,16,180),(0,41,176),(1,41,176),(0,0,0),(3,52,173),(2,78,163),(0,0,0),(0,0,0),(2,16,180),(2,41,176),(0,25,179),(0,0,0),(11,19,176),(4,58,171),(0,0,0),(0,0,0),(0,76,164),(1,76,164),(0,93,155),(0,0,0),(11,4,177),(0,49,174),(0,0,0),(0,0,0),(2,76,164),(4,24,179),(2,93,155),(0,0,0),(3,41,176),(2,49,174),(0,0,0),(0,0,0),(7,37,176),(0,17,180),(1,17,180),(0,0,0),(8,68,166),(0,118,137),(0,0,0),(0,0,0),(7,32,177),(2,17,180),(0,37,177),(0,0,0),(10,4,178),(0,74,165),(0,0,0),(0,0,0),(3,49,174),(5,48,174),(2,37,177),(0,0,0),(0,32,178),(1,32,178),(0,0,0),(0,0,0),(7,113,140),(0,67,168),(1,67,168),(0,0,0),(2,32,178),(0,26,179),(0,0,0),(0,0,0),(0,56,172),(1,56,172),(0,59,171),(0,0,0),(0,18,180),(1,18,180),(0,0,0),(0,0,0),(2,56,172),(6,68,167),(2,59,171),(0,0,0),(2,18,180),(0,117,138),(0,0,0),(0,0,0),(4,76,164),(6,11,180),(0,53,173),(0,0,0),(0,42,176),(0,46,175),(0,0,0),(0,0,0),(0,62,170),(1,62,170),(2,53,173),(0,0,0),(2,42,176),(0,90,157),(0,0,0),(0,0,0),(2,62,170),(4,17,180),(10,125,127),(0,0,0),(7,27,178),(2,90,157),(0,0,0),(0,0,0),(3,117,138),(0,0,181),(0,1,181),(0,0,0),(11,43,172),(0,2,181),(0,0,0),(0,0,0),(0,128,128),(1,128,128),(0,3,181),(0,0,0),(4,32,178),(0,33,178),(0,0,0),(0,0,0),(0,50,174),(0,4,181),(1,4,181),(0,0,0),(15,43,166),(2,33,178),(0,0,0),(0,0,0),(2,50,174),(2,4,181),(0,5,181),(0,0,0),(3,0,181),(0,70,167),(0,0,0),(0,0,0),(3,2,181),(10,47,172),(2,5,181),(0,0,0),(6,48,174),(0,6,181),(0,0,0),(0,0,0),(0,20,180),(0,100,151),(1,100,151),(0,0,0),(3,4,181),(0,81,162),(0,0,0),(0,0,0),(2,20,180),(2,100,151),(0,7,181),(0,0,0),(6,14,180),(2,81,162),(0,0,0),(0,0,0),(3,70,167),(7,43,175),(0,97,153),(0,0,0),(8,102,148),(6,58,171),(0,0,0),(0,0,0),(3,6,181),(0,8,181),(1,8,181),(0,0,0),(3,100,151),(4,2,181),(0,0,0),(0,0,0),(3,81,162),(0,57,172),(0,47,175),(0,0,0),(0,110,144),(1,110,144),(0,0,0),(0,0,0),(0,34,178),(0,21,180),(0,9,181),(0,0,0),(2,110,144),(0,54,173),(0,0,0),(0,0,0),(0,68,168),(1,68,168),(0,39,177),(0,0,0),(3,8,181),(2,54,173),(0,0,0),(0,0,0),(2,68,168),(8,37,176),(2,39,177),(0,0,0),(3,57,172),(0,10,181),(0,0,0),(0,0,0),(4,20,180),(4,100,151),(0,121,135),(0,0,0),(3,21,180),(0,63,170),(0,0,0),(0,0,0),(3,54,173),(6,41,176),(2,121,135),(0,0,0),(7,87,158),(0,51,174),(0,0,0),(0,0,0),(7,124,131),(8,113,140),(0,11,181),(0,0,0),(0,22,180),(0,73,166),(0,0,0),(0,0,0),(3,10,181),(4,8,181),(2,11,181),(0,0,0),(2,22,180),(2,73,166),(0,0,0),(0,0,0),(0,120,136),(1,120,136),(4,47,175),(0,0,0),(4,110,144),(5,50,174),(0,0,0),(0,0,0),(0,102,150),(0,12,181),(0,109,145),(0,0,0),(14,100,142),(0,35,178),(0,0,0),(0,0,0),(0,44,176),(1,44,176),(2,109,145),(0,0,0),(7,122,133),(0,66,169),(0,0,0),(0,0,0),(2,44,176),(8,3,180),(5,6,181),(0,0,0),(6,32,178),(2,66,169),(0,0,0),(0,0,0),(8,4,180),(0,23,180),(0,13,181),(0,0,0),(0,96,154),(0,113,142),(0,0,0),(0,0,0),(3,35,178),(2,23,180),(2,13,181),(0,0,0),(2,96,154),(0,30,179),(0,0,0),(0,0,0),(3,66,169),(7,99,151),(4,11,181),(0,0,0),(0,58,172),(1,58,172),(0,0,0),(0,0,0),(7,55,172),(8,20,179),(0,55,173),(0,0,0),(2,58,172),(0,14,181),(0,0,0),(0,0,0),(3,113,142),(5,110,144),(0,61,171),(0,0,0),(7,61,170),(2,14,181),(0,0,0),(0,0,0),(0,82,162),(0,80,163),(1,80,163),(0,0,0),(10,106,144),(4,35,178),(0,0,0),(0,0,0),(0,24,180),(0,84,161),(1,84,161),(0,0,0),(0,36,178),(1,36,178),(0,0,0),(0,0,0),(2,24,180),(0,69,168),(0,15,181),(0,0,0),(2,36,178),(3,61,171),(0,0,0),(0,0,0),(6,50,174),(0,112,143),(1,112,143),(0,0,0),(0,64,170),(1,64,170),(0,0,0),(0,0,0)]

def wits_33 : List (ℕ × ℕ × ℕ) := [(7,41,176),(0,45,176),(0,31,179),(0,0,0),(2,64,170),(4,30,179),(0,0,0),(0,0,0),(10,18,178),(2,45,176),(0,41,177),(0,0,0),(3,69,168),(0,98,153),(0,0,0),(0,0,0),(6,20,180),(0,16,181),(1,16,181),(0,0,0),(3,112,143),(2,98,153),(0,0,0),(0,0,0),(11,3,178),(0,25,180),(0,49,175),(0,0,0),(3,45,176),(0,127,130),(0,0,0),(0,0,0),(0,74,166),(1,74,166),(2,49,175),(0,0,0),(7,118,137),(0,126,131),(0,0,0),(0,0,0),(2,74,166),(4,84,161),(5,66,169),(0,0,0),(3,16,181),(2,126,131),(0,0,0),(0,0,0),(19,35,158),(0,125,132),(0,17,181),(0,0,0),(3,25,180),(0,37,178),(0,0,0),(0,0,0),(0,116,140),(0,111,144),(0,107,147),(0,0,0),(4,64,170),(2,37,178),(0,0,0),(0,0,0),(0,90,158),(0,32,179),(1,32,179),(0,0,0),(10,62,168),(10,38,175),(0,0,0),(0,0,0),(2,90,158),(0,72,167),(1,72,167),(0,0,0),(0,26,180),(1,26,180),(0,0,0),(0,0,0),(3,37,178),(2,72,167),(5,14,181),(0,0,0),(2,26,180),(0,18,181),(0,0,0),(0,0,0),(8,40,176),(4,25,180),(4,49,175),(0,0,0),(0,46,176),(0,42,177),(0,0,0),(0,0,0),(4,74,166),(20,76,139),(6,11,181),(0,0,0),(2,46,176),(2,42,177),(0,0,0),(0,0,0),(0,100,152),(1,100,152),(0,115,141),(0,0,0),(7,2,181),(0,103,150),(0,0,0),(0,0,0),(2,100,152),(0,92,157),(1,92,157),(0,0,0),(7,33,178),(2,103,150),(0,0,0),(0,0,0),(3,42,177),(2,92,157),(0,19,181),(0,0,0),(0,0,182),(0,1,182),(0,0,0),(0,0,0),(0,2,182),(0,27,180),(0,33,179),(0,0,0),(2,0,182),(0,3,182),(0,0,0),(0,0,0),(2,2,182),(0,79,164),(1,79,164),(0,0,0),(0,4,182),(1,4,182),(0,0,0),(0,0,0),(7,100,151),(2,79,164),(0,85,161),(0,0,0),(2,4,182),(0,5,182),(0,0,0),(0,0,0),(3,1,182),(7,7,181),(0,77,165),(0,0,0),(3,27,180),(2,5,182),(0,0,0),(0,0,0),(0,6,182),(0,20,181),(1,20,181),(0,0,0),(3,79,164),(8,78,163),(0,0,0),(0,0,0),(2,6,182),(0,87,160),(1,87,160),(0,0,0),(0,94,156),(0,7,182),(0,0,0),(0,0,0),(3,5,182),(2,87,160),(0,43,177),(0,0,0),(2,94,156),(0,75,166),(0,0,0),(0,0,0),(0,28,180),(0,47,176),(1,47,176),(0,0,0),(0,8,182),(1,8,182),(0,0,0),(0,0,0),(0,54,174),(1,54,174),(4,33,179),(0,0,0),(2,8,182),(0,34,179),(0,0,0),(0,0,0),(2,54,174),(4,79,164),(0,21,181),(0,0,0),(4,4,182),(0,9,182),(0,0,0),(0,0,0),(3,75,166),(6,112,143),(0,63,171),(0,0,0),(3,47,176),(2,9,182),(0,0,0),(0,0,0),(14,14,174),(5,46,176),(0,73,167),(0,0,0),(7,51,174),(16,15,170),(0,0,0),(0,0,0),(0,10,182),(1,10,182),(0,51,175),(0,0,0),(7,73,166),(3,21,181),(0,0,0),(0,0,0),(2,10,182),(4,87,160),(2,51,175),(0,0,0),(4,94,156),(3,63,171),(0,0,0),(0,0,0),(11,15,178),(0,29,180),(1,29,180),(0,0,0),(14,40,170),(0,11,182),(0,0,0),(0,0,0),(4,28,180),(2,29,180),(5,1,182),(0,0,0),(4,8,182),(2,11,182),(0,0,0),(0,0,0),(0,66,170),(1,66,170),(5,3,182),(0,0,0),(7,66,169),(4,34,179),(0,0,0),(0,0,0),(2,66,170),(0,44,177),(0,35,179),(0,0,0),(0,12,182),(1,12,182),(0,0,0),(0,0,0),(3,11,182),(0,108,147),(1,108,147),(0,0,0),(2,12,182),(8,2,181),(0,0,0),(0,0,0),(0,48,176),(1,48,176),(0,129,129),(0,0,0),(0,40,178),(1,40,178),(0,0,0),(0,0,0),(2,48,176),(0,117,140),(0,23,181),(0,0,0),(2,40,178),(0,13,182),(0,0,0),(0,0,0),(0,80,164),(1,80,164),(0,93,157),(0,0,0),(0,30,180),(0,55,174),(0,0,0),(0,0,0),(2,80,164),(0,61,172),(1,61,172),(0,0,0),(2,30,180),(0,78,165),(0,0,0),(0,0,0),(7,80,163),(2,61,172),(0,125,133),(0,0,0),(0,104,150),(0,86,161),(0,0,0),(0,0,0),(0,14,182),(1,14,182),(0,69,169),(0,0,0),(2,104,150),(2,86,161),(0,0,0),(0,0,0),(2,14,182),(0,52,175),(1,52,175),(0,0,0),(0,76,166),(1,76,166),(0,0,0),(0,0,0),(3,78,165),(0,24,181),(1,24,181),(0,0,0),(2,76,166),(3,125,133),(0,0,0),(0,0,0),(0,88,160),(1,88,160),(0,111,145),(0,0,0),(4,40,178),(0,15,182),(0,0,0),(0,0,0),(2,88,160),(0,107,148),(0,45,177),(0,0,0),(3,52,175),(2,15,182),(0,0,0),(0,0,0),(4,80,164),(0,31,180),(1,31,180),(0,0,0),(3,24,181),(0,41,178),(0,0,0),(0,0,0),(7,25,180),(2,31,180),(5,11,182),(0,0,0),(7,127,130),(2,41,178),(0,0,0),(0,0,0),(3,15,182),(0,49,176),(1,49,176),(0,0,0),(0,16,182),(0,90,159),(0,0,0),(0,0,0),(4,14,182),(2,49,176),(0,25,181),(0,0,0),(2,16,182),(0,67,170),(0,0,0),(0,0,0),(3,41,178),(4,52,175),(2,25,181),(0,0,0),(4,76,166),(2,67,170),(0,0,0),(0,0,0),(6,28,180),(4,24,181),(10,19,179),(0,0,0),(3,49,176),(5,48,176),(0,0,0),(0,0,0),(0,72,168),(0,100,153),(0,37,179),(0,0,0),(0,56,174),(0,17,182),(0,0,0),(0,0,0),(0,110,146),(1,110,146),(2,37,179),(0,0,0),(2,56,174),(2,17,182),(0,0,0),(0,0,0),(0,32,180),(1,32,180),(5,55,174),(0,0,0),(0,62,172),(1,62,172),(0,0,0),(0,0,0),(2,32,180),(12,27,176),(0,53,175),(0,0,0),(2,62,172),(0,26,181),(0,0,0),(0,0,0),(3,17,182),(4,49,176),(2,53,175),(0,0,0),(0,120,138),(0,46,177),(0,0,0),(0,0,0),(0,18,182),(1,18,182),(4,25,181),(0,0,0),(2,120,138),(2,46,177),(0,0,0),(0,0,0),(2,18,182),(0,81,164),(0,83,163),(0,0,0),(8,58,172),(0,70,169),(0,0,0),(0,0,0),(3,26,181),(2,81,164),(0,65,171),(0,0,0),(7,1,182),(0,85,162),(0,0,0),(0,0,0),(3,46,177),(4,100,153),(2,65,171),(0,0,0),(0,50,176),(1,50,176),(0,0,0),(0,0,0),(4,110,146),(6,44,177),(0,119,139),(0,0,0),(2,50,176),(0,19,182),(0,0,0),(0,0,0),(3,70,169),(0,0,183),(0,1,183),(0,0,0),(4,62,172),(0,2,183),(0,0,0),(0,0,0),(3,85,162),(2,0,183),(0,3,183),(0,0,0),(6,40,178),(2,2,183),(0,0,0),(0,0,0),(7,20,181),(0,4,183),(1,4,183),(0,0,0),(0,102,152),(1,102,152),(0,0,0),(0,0,0),(3,19,182),(2,4,183),(0,5,183),(0,0,0),(2,102,152),(0,99,154),(0,0,0),(0,0,0),(3,2,183),(0,89,160),(1,89,160),(0,0,0),(0,20,182),(0,6,183),(0,0,0),(0,0,0),(7,47,176),(0,60,173),(1,60,173),(0,0,0),(2,20,182),(0,43,178),(0,0,0),(0,0,0),(6,14,182),(2,60,173),(0,7,183),(0,0,0),(4,50,176),(0,54,175),(0,0,0),(0,0,0),(3,99,154),(0,28,181),(1,28,181),(0,0,0),(3,89,160),(2,54,175),(0,0,0),(0,0,0),(0,96,156),(0,8,183),(1,8,183),(0,0,0),(0,34,180),(1,34,180),(0,0,0),(0,0,0),(2,96,156),(2,8,183),(0,39,179),(0,0,0),(2,34,180),(0,21,182),(0,0,0),(0,0,0),(0,108,148),(0,112,145),(0,9,183),(0,0,0),(3,28,181),(2,21,182),(0,0,0),(0,0,0),(2,108,148),(0,51,176),(1,51,176),(0,0,0),(3,8,183),(0,125,134),(0,0,0),(0,0,0),(7,29,180),(2,51,176),(5,70,169),(0,0,0),(4,20,182),(0,10,183),(0,0,0),(0,0,0),(3,21,182),(4,60,173),(5,85,162),(0,0,0),(3,112,145),(0,66,171),(0,0,0),(0,0,0),(11,115,138),(0,124,135),(0,29,181),(0,0,0),(3,51,176),(2,66,171),(0,0,0),(0,0,0),(0,22,182),(1,22,182),(0,11,183),(0,0,0),(14,68,162),(0,93,158),(0,0,0),(0,0,0),(2,22,182),(0,104,151),(1,104,151),(0,0,0),(0,44,178),(1,44,178),(0,0,0),(0,0,0),(3,66,171),(0,35,180),(1,35,180),(0,0,0),(2,44,178),(0,98,155),(0,0,0),(0,0,0),(4,108,148),(0,12,183),(1,12,183),(0,0,0),(7,13,182),(0,111,146),(0,0,0),(0,0,0),(0,58,174),(0,40,179),(1,40,179),(0,0,0),(3,104,151),(2,111,146),(0,0,0),(0,0,0),(2,58,174),(2,40,179),(0,55,175),(0,0,0),(3,35,180),(0,23,182),(0,0,0),(0,0,0),(3,98,155),(7,125,133),(0,13,183),(0,0,0),(3,12,183),(0,30,181),(0,0,0),(0,0,0),(3,111,146),(0,76,167),(1,76,167),(0,0,0),(3,40,179),(2,30,181),(0,0,0),(0,0,0),(4,22,182),(2,76,167),(0,95,157),(0,0,0),(11,37,176),(3,55,175),(0,0,0),(0,0,0),(0,52,176),(1,52,176),(2,95,157),(0,0,0),(4,44,178),(0,14,183),(0,0,0),(0,0,0),(2,52,176),(4,35,180),(5,21,182),(0,0,0),(3,76,167),(2,14,183),(0,0,0),(0,0,0),(0,36,180),(1,36,180),(6,119,139),(0,0,0),(0,24,182),(1,24,182),(0,0,0),(0,0,0),(2,36,180),(4,40,179),(5,125,134),(0,0,0),(2,24,182),(0,45,178),(0,0,0),(0,0,0),(3,14,183),(0,103,152),(0,15,183),(0,0,0),(0,100,154),(1,100,154),(0,0,0),(0,0,0),(7,49,176),(0,120,139),(0,31,181),(0,0,0),(2,100,154),(4,30,181),(0,0,0),(0,0,0),(12,32,176),(2,120,139),(0,49,177),(0,0,0),(0,114,144),(1,114,144),(0,0,0),(0,0,0),(0,106,150),(1,106,150),(2,49,177),(0,0,0),(2,114,144),(3,15,183),(0,0,0),(0,0,0),(2,106,150),(0,16,183),(1,16,183),(0,0,0),(3,120,139),(0,25,182),(0,0,0),(0,0,0),(7,100,153),(2,16,183),(5,98,155),(0,0,0),(7,17,182),(0,59,174),(0,0,0),(0,0,0),(4,36,180),(0,56,175),(1,56,175),(0,0,0),(4,24,182),(2,59,174),(0,0,0),(0,0,0),(6,96,156),(0,37,180),(1,37,180),(0,0,0),(3,16,183),(0,62,173),(0,0,0),(0,0,0),(3,25,182),(2,37,180),(0,17,183),(0,0,0),(4,100,154),(2,62,173),(0,0,0),(0,0,0),(3,59,174),(0,32,181),(0,81,165),(0,0,0),(3,56,175),(10,70,167),(0,0,0),(0,0,0),(8,48,176),(2,32,181),(0,85,163),(0,0,0),(3,37,180),(0,79,166),(0,0,0),(0,0,0),(0,26,182),(1,26,182),(0,129,131),(0,0,0),(7,70,169),(0,42,179),(0,0,0),(0,0,0),(0,128,132),(0,65,172),(1,65,172),(0,0,0),(3,32,181),(0,18,183),(0,0,0),(0,0,0),(2,128,132),(2,65,172),(0,77,167),(0,0,0),(11,83,160),(2,18,183),(0,0,0),(0,0,0),(3,79,166),(4,56,175),(0,99,155),(0,0,0),(7,19,182),(0,50,177),(0,0,0),(0,0,0),(0,126,134),(1,126,134),(2,99,155),(0,0,0),(3,65,172),(2,50,177),(0,0,0),(0,0,0),(2,126,134),(5,100,154),(0,89,161),(0,0,0),(0,38,180),(1,38,180),(0,0,0),(0,0,0),(7,4,183),(0,75,168),(0,19,183),(0,0,0),(2,38,180),(0,27,182),(0,0,0),(0,0,0),(0,0,184),(0,1,184),(1,1,184),(0,0,0),(0,2,184),(1,2,184),(0,0,0),(0,0,0),(2,0,184),(0,3,184),(1,3,184),(0,0,0),(2,2,184),(3,89,161),(0,0,0),(0,0,0),(0,4,184),(1,4,184),(0,57,175),(0,0,0),(0,60,174),(1,60,174),(0,0,0),(0,0,0),(2,4,184),(0,5,184),(1,5,184),(0,0,0),(2,60,174),(10,73,166),(0,0,0),(0,0,0),(7,28,181),(0,20,183),(0,43,179),(0,0,0),(0,6,184),(0,47,178),(0,0,0),(0,0,0),(4,126,134),(2,20,183),(0,63,173),(0,0,0),(2,6,184),(2,47,178),(0,0,0),(0,0,0),(10,102,150),(0,7,184),(1,7,184),(0,0,0),(0,28,182),(1,28,182),(0,0,0),(0,0,0),(6,36,180),(2,7,184),(4,19,183),(0,0,0),(2,28,182),(0,34,181),(0,0,0),(0,0,0),(0,8,184),(0,39,180),(1,39,180),(0,0,0),(4,2,184),(2,34,181),(0,0,0),(0,0,0),(0,122,138),(1,122,138),(0,21,183),(0,0,0),(3,7,184),(5,128,132),(0,0,0),(0,0,0),(2,122,138),(0,9,184),(1,9,184),(0,0,0),(0,66,172),(0,71,170),(0,0,0),(0,0,0),(3,34,181),(2,9,184),(6,49,177),(0,0,0),(2,66,172),(0,82,165),(0,0,0),(0,0,0),(0,84,164),(1,84,164),(4,43,179),(0,0,0),(0,10,184),(1,10,184),(0,0,0),(0,0,0),(2,84,164),(0,115,144),(0,121,139),(0,0,0),(2,10,184),(0,29,182),(0,0,0),(0,0,0),(3,71,170),(2,115,144),(2,121,139),(0,0,0),(4,28,182),(0,22,183),(0,0,0),(0,0,0),(3,82,165),(0,11,184),(1,11,184),(0,0,0),(7,111,146),(2,22,183),(0,0,0),(0,0,0),(4,8,184),(2,11,184),(0,35,181),(0,0,0),(0,48,178),(0,58,175),(0,0,0),(0,0,0),(3,29,182),(7,55,175),(2,35,181),(0,0,0),(2,48,178),(0,61,174),(0,0,0),(0,0,0)]

def wits_34 : List (ℕ × ℕ × ℕ) := [(0,12,184),(0,55,176),(0,69,171),(0,0,0),(0,110,148),(1,110,148),(0,0,0),(0,0,0),(2,12,184),(2,55,176),(2,69,171),(0,0,0),(2,110,148),(3,35,181),(0,0,0),(0,0,0),(3,58,175),(5,6,184),(0,23,183),(0,0,0),(4,10,184),(0,90,161),(0,0,0),(0,0,0),(0,30,182),(0,13,184),(1,13,184),(0,0,0),(3,55,176),(2,90,161),(0,0,0),(0,0,0),(2,30,182),(0,52,177),(1,52,177),(0,0,0),(8,20,182),(0,74,169),(0,0,0),(0,0,0),(15,64,163),(2,52,177),(0,119,141),(0,0,0),(11,67,168),(2,74,169),(0,0,0),(0,0,0),(3,90,161),(9,14,182),(2,119,141),(0,0,0),(0,14,184),(1,14,184),(0,0,0),(0,0,0),(7,103,152),(0,36,181),(0,97,157),(0,0,0),(2,14,184),(0,130,131),(0,0,0),(0,0,0),(0,92,160),(0,24,183),(0,45,179),(0,0,0),(4,110,148),(2,130,131),(0,0,0),(0,0,0),(2,92,160),(0,67,172),(1,67,172),(0,0,0),(6,2,184),(5,84,164),(0,0,0),(0,0,0),(8,108,148),(0,15,184),(0,109,149),(0,0,0),(0,72,170),(0,31,182),(0,0,0),(0,0,0),(0,118,142),(1,118,142),(2,109,149),(0,0,0),(2,72,170),(2,31,182),(0,0,0),(0,0,0),(2,118,142),(4,52,177),(5,22,183),(0,0,0),(3,67,172),(0,126,135),(0,0,0),(0,0,0),(7,56,175),(6,20,183),(0,59,175),(0,0,0),(3,15,184),(2,126,135),(0,0,0),(0,0,0),(0,16,184),(1,16,184),(0,25,183),(0,0,0),(4,14,184),(0,81,166),(0,0,0),(0,0,0),(0,62,174),(0,85,164),(1,85,164),(0,0,0),(6,28,182),(2,81,166),(0,0,0),(0,0,0),(2,62,174),(0,105,152),(0,37,181),(0,0,0),(8,44,178),(3,59,175),(0,0,0),(0,0,0),(6,8,184),(0,99,156),(0,53,177),(0,0,0),(7,79,166),(0,70,171),(0,0,0),(0,0,0),(3,81,166),(0,17,184),(1,17,184),(0,0,0),(0,32,182),(1,32,182),(0,0,0),(0,0,0),(4,118,142),(0,77,168),(0,65,173),(0,0,0),(2,32,182),(0,46,179),(0,0,0),(0,0,0),(10,6,182),(2,77,168),(2,65,173),(0,0,0),(0,42,180),(0,26,183),(0,0,0),(0,0,0),(3,70,171),(7,99,155),(4,59,175),(0,0,0),(2,42,180),(0,123,138),(0,0,0),(0,0,0),(4,16,184),(5,14,184),(4,25,183),(0,0,0),(0,18,184),(1,18,184),(0,0,0),(0,0,0),(0,50,178),(1,50,178),(0,75,169),(0,0,0),(2,18,184),(5,92,160),(0,0,0),(0,0,0),(0,116,144),(1,116,144),(2,75,169),(0,0,0),(7,27,182),(8,14,183),(0,0,0),(0,0,0),(2,116,144),(4,99,156),(0,91,161),(0,0,0),(6,48,178),(0,38,181),(0,0,0),(0,0,0),(0,68,172),(1,68,172),(2,91,161),(0,0,0),(4,32,182),(0,33,182),(0,0,0),(0,0,0),(2,68,172),(0,19,184),(0,27,183),(0,0,0),(6,110,148),(2,33,182),(0,0,0),(0,0,0),(7,5,184),(0,0,185),(0,1,185),(0,0,0),(4,42,180),(0,2,185),(0,0,0),(0,0,0),(3,38,181),(2,0,185),(0,3,185),(0,0,0),(7,47,178),(2,2,185),(0,0,0),(0,0,0),(3,33,182),(0,4,185),(1,4,185),(0,0,0),(3,19,184),(0,54,177),(0,0,0),(0,0,0),(4,50,178),(0,43,180),(0,5,185),(0,0,0),(3,0,185),(0,98,157),(0,0,0),(0,0,0),(0,20,184),(1,20,184),(2,5,185),(0,0,0),(7,34,181),(0,6,185),(0,0,0),(0,0,0),(2,20,184),(10,44,177),(4,91,161),(0,0,0),(3,4,185),(2,6,185),(0,0,0),(0,0,0),(3,54,177),(0,28,183),(0,7,185),(0,0,0),(3,43,180),(3,5,185),(0,0,0),(0,0,0),(0,34,182),(0,84,165),(0,39,181),(0,0,0),(7,71,170),(0,51,178),(0,0,0),(0,0,0),(2,34,182),(0,8,185),(1,8,185),(0,0,0),(0,86,164),(1,86,164),(0,0,0),(0,0,0),(10,80,164),(0,21,184),(1,21,184),(0,0,0),(2,86,164),(0,110,149),(0,0,0),(0,0,0),(6,118,142),(2,21,184),(0,9,185),(0,0,0),(0,78,168),(1,78,168),(0,0,0),(0,0,0),(0,114,146),(0,88,163),(1,88,163),(0,0,0),(2,78,168),(4,98,157),(0,0,0),(0,0,0),(2,114,146),(2,88,163),(0,131,131),(0,0,0),(0,130,132),(0,10,185),(0,0,0),(0,0,0),(3,110,149),(7,35,181),(0,29,183),(0,0,0),(2,130,132),(2,10,185),(0,0,0),(0,0,0),(0,44,180),(0,76,169),(1,76,169),(0,0,0),(0,22,184),(1,22,184),(0,0,0),(0,0,0),(0,90,162),(0,48,179),(0,11,185),(0,0,0),(2,22,184),(0,35,182),(0,0,0),(0,0,0),(2,90,162),(2,48,179),(0,55,177),(0,0,0),(4,86,164),(2,35,182),(0,0,0),(0,0,0),(11,127,130),(0,40,181),(1,40,181),(0,0,0),(3,76,169),(4,110,149),(0,0,0),(0,0,0),(7,13,184),(0,12,185),(1,12,185),(0,0,0),(0,64,174),(0,97,158),(0,0,0),(0,0,0),(0,74,170),(1,74,170),(0,113,147),(0,0,0),(2,64,174),(0,109,150),(0,0,0),(0,0,0),(2,74,170),(0,23,184),(1,23,184),(0,0,0),(0,52,178),(0,30,183),(0,0,0),(0,0,0),(0,0,0),(2,23,184),(0,13,185),(0,0,0),(2,52,178),(2,30,183),(0,0,0),(0,0,0),(3,97,158),(4,76,169),(2,13,185),(0,0,0),(4,22,184),(3,113,147),(0,0,0),(0,0,0),(3,109,150),(4,48,179),(4,11,185),(0,0,0),(3,23,184),(4,35,182),(0,0,0),(0,0,0),(3,30,183),(5,86,164),(0,67,173),(0,0,0),(0,36,182),(0,14,185),(0,0,0),(0,0,0),(6,68,172),(0,45,180),(1,45,180),(0,0,0),(2,36,182),(0,102,155),(0,0,0),(0,0,0),(0,24,184),(1,24,184),(0,105,153),(0,0,0),(0,94,160),(1,94,160),(0,0,0),(0,0,0),(2,24,184),(6,0,185),(0,41,181),(0,0,0),(2,94,160),(0,83,166),(0,0,0),(0,0,0),(0,112,148),(1,112,148),(0,15,185),(0,0,0),(3,45,180),(2,83,166),(0,0,0),(0,0,0),(2,112,148),(0,59,176),(1,59,176),(0,0,0),(7,81,166),(3,105,153),(0,0,0),(0,0,0),(7,85,164),(0,56,177),(1,56,177),(0,0,0),(8,10,184),(0,62,175),(0,0,0),(0,0,0),(3,83,166),(2,56,177),(5,35,182),(0,0,0),(10,50,176),(2,62,175),(0,0,0),(0,0,0),(7,99,156),(0,16,185),(1,16,185),(0,0,0),(0,70,172),(1,70,172),(0,0,0),(0,0,0),(7,17,184),(2,16,185),(0,77,169),(0,0,0),(2,70,172),(0,37,182),(0,0,0),(0,0,0),(3,62,175),(0,96,159),(1,96,159),(0,0,0),(4,94,160),(0,65,174),(0,0,0),(0,0,0),(11,7,182),(2,96,159),(4,41,181),(0,0,0),(3,16,185),(2,65,174),(0,0,0),(0,0,0),(4,112,148),(0,32,183),(0,17,185),(0,0,0),(0,46,180),(1,46,180),(0,0,0),(0,0,0),(3,37,182),(2,32,183),(0,111,149),(0,0,0),(2,46,180),(0,42,181),(0,0,0),(0,0,0),(3,65,174),(4,56,177),(2,111,149),(0,0,0),(0,26,184),(1,26,184),(0,0,0),(0,0,0),(8,30,182),(0,101,156),(1,101,156),(0,0,0),(2,26,184),(0,50,179),(0,0,0),(0,0,0),(18,34,166),(2,101,156),(5,14,185),(0,0,0),(4,70,172),(0,18,185),(0,0,0),(0,0,0),(3,42,181),(0,68,173),(1,68,173),(0,0,0),(6,22,184),(2,18,185),(0,0,0),(0,0,0),(6,90,162),(2,68,173),(6,11,185),(0,0,0),(0,120,142),(1,120,142),(0,0,0),(0,0,0),(0,38,182),(1,38,182),(0,73,171),(0,0,0),(2,120,142),(5,112,148),(0,0,0),(0,0,0),(0,60,176),(1,60,176),(0,33,183),(0,0,0),(3,68,173),(10,125,134),(0,0,0),(0,0,0),(2,60,176),(0,27,184),(0,19,185),(0,0,0),(6,64,174),(0,130,133),(0,0,0),(0,0,0),(6,74,170),(2,27,184),(0,63,175),(0,0,0),(0,0,186),(0,1,186),(0,0,0),(0,0,0),(0,2,186),(1,2,186),(2,63,175),(0,0,0),(2,0,186),(0,3,186),(0,0,0),(0,0,0),(2,2,186),(0,47,180),(0,43,181),(0,0,0),(0,4,186),(0,82,167),(0,0,0),(0,0,0),(3,130,133),(2,47,180),(2,43,181),(0,0,0),(2,4,186),(0,5,186),(0,0,0),(0,0,0),(0,80,168),(0,20,185),(1,20,185),(0,0,0),(4,120,142),(2,5,186),(0,0,0),(0,0,0),(0,6,186),(1,6,186),(0,103,155),(0,0,0),(3,47,180),(3,43,181),(0,0,0),(0,0,0),(0,28,184),(1,28,184),(0,51,179),(0,0,0),(7,110,149),(0,7,186),(0,0,0),(0,0,0),(2,28,184),(0,100,157),(1,100,157),(0,0,0),(3,20,185),(2,7,186),(0,0,0),(0,0,0),(7,88,163),(2,100,157),(4,63,175),(0,0,0),(0,8,186),(1,8,186),(0,0,0),(0,0,0),(4,2,186),(7,131,131),(0,21,185),(0,0,0),(2,8,186),(0,90,163),(0,0,0),(0,0,0),(3,7,186),(0,113,148),(1,113,148),(0,0,0),(0,76,170),(0,9,186),(0,0,0),(0,0,0),(7,76,169),(2,113,148),(0,109,151),(0,0,0),(2,76,170),(2,9,186),(0,0,0),(0,0,0),(4,80,168),(4,20,185),(0,69,173),(0,0,0),(7,35,182),(0,58,177),(0,0,0),(0,0,0),(0,10,186),(0,29,184),(1,29,184),(0,0,0),(3,113,148),(2,58,177),(0,0,0),(0,0,0),(0,48,180),(1,48,180),(4,51,179),(0,0,0),(0,92,162),(0,22,185),(0,0,0),(0,0,0),(2,48,180),(4,100,157),(0,35,183),(0,0,0),(2,92,162),(0,11,186),(0,0,0),(0,0,0),(3,58,177),(0,64,175),(1,64,175),(0,0,0),(0,40,182),(1,40,182),(0,0,0),(0,0,0),(7,23,184),(0,123,140),(1,123,140),(0,0,0),(2,40,182),(4,90,163),(0,0,0),(0,0,0),(3,22,185),(2,123,140),(5,82,167),(0,0,0),(0,12,186),(0,105,154),(0,0,0),(0,0,0),(3,11,186),(0,52,179),(1,52,179),(0,0,0),(2,12,186),(2,105,154),(0,0,0),(0,0,0),(14,18,178),(2,52,179),(0,23,185),(0,0,0),(0,30,184),(0,94,161),(0,0,0),(0,0,0),(4,10,186),(4,29,184),(2,23,185),(0,0,0),(2,30,184),(0,13,186),(0,0,0),(0,0,0),(0,72,172),(1,72,172),(5,7,186),(0,0,0),(0,116,146),(1,116,146),(0,0,0),(0,0,0),(2,72,172),(7,105,153),(0,83,167),(0,0,0),(2,116,146),(0,85,166),(0,0,0),(0,0,0),(3,94,161),(0,36,183),(0,45,181),(0,0,0),(4,40,182),(2,85,166),(0,0,0),(0,0,0),(0,14,186),(1,14,186),(0,87,165),(0,0,0),(15,86,155),(8,51,178),(0,0,0),(0,0,0),(2,14,186),(0,24,185),(0,79,169),(0,0,0),(4,12,186),(0,41,182),(0,0,0),(0,0,0),(3,85,166),(2,24,185),(0,59,177),(0,0,0),(3,36,183),(2,41,182),(0,0,0),(0,0,0),(0,96,160),(0,31,184),(1,31,184),(0,0,0),(0,56,178),(0,15,186),(0,0,0),(0,0,0),(2,96,160),(2,31,184),(6,43,181),(0,0,0),(2,56,178),(0,70,173),(0,0,0),(0,0,0),(3,41,182),(5,92,162),(0,115,147),(0,0,0),(4,116,146),(2,70,173),(0,0,0),(0,0,0),(6,80,168),(0,104,155),(1,104,155),(0,0,0),(3,31,184),(4,85,166),(0,0,0),(0,0,0),(0,132,132),(0,120,143),(0,25,185),(0,0,0),(0,16,186),(1,16,186),(0,0,0),(0,0,0),(0,130,134),(1,130,134),(0,37,183),(0,0,0),(2,16,186),(3,115,147),(0,0,0),(0,0,0),(2,130,134),(4,24,185),(0,75,171),(0,0,0),(3,104,155),(4,41,182),(0,0,0),(0,0,0),(10,4,184),(8,40,181),(2,75,171),(0,0,0),(3,120,143),(0,46,181),(0,0,0),(0,0,0),(0,32,184),(1,32,184),(5,94,161),(0,0,0),(4,56,178),(0,17,186),(0,0,0),(0,0,0),(0,42,182),(1,42,182),(5,13,186),(0,0,0),(6,76,170),(0,93,162),(0,0,0),(0,0,0),(2,42,182),(0,119,144),(0,127,137),(0,0,0),(0,50,180),(0,26,185),(0,0,0),(0,0,0),(3,46,181),(2,119,144),(2,127,137),(0,0,0),(2,50,180),(2,26,185),(0,0,0),(0,0,0),(3,17,186),(0,73,172),(1,73,172),(0,0,0),(4,16,186),(5,14,186),(0,0,0),(0,0,0),(0,18,186),(1,18,186),(4,37,183),(0,0,0),(3,119,144),(3,127,137),(0,0,0),(0,0,0),(2,18,186),(0,60,177),(1,60,177),(0,0,0),(7,130,133),(0,38,183),(0,0,0),(0,0,0),(15,85,156),(2,60,177),(12,63,171),(0,0,0),(3,73,172),(2,38,183),(0,0,0),(0,0,0),(4,32,184),(0,33,184),(0,95,161),(0,0,0),(0,82,168),(0,118,145),(0,0,0),(0,0,0),(0,86,166),(1,86,166),(0,27,185),(0,0,0),(2,82,168),(0,19,186),(0,0,0),(0,0,0),(2,86,166),(0,80,169),(1,80,169),(0,0,0),(0,100,158),(1,100,158),(0,0,0),(0,0,0),(7,20,185),(0,0,187),(0,1,187),(0,0,0),(2,100,158),(0,2,187),(0,0,0),(0,0,0),(0,124,140),(1,124,140),(0,3,187),(0,0,0),(19,35,164),(0,66,175),(0,0,0),(0,0,0),(0,78,170),(0,4,187),(1,4,187),(0,0,0),(3,80,169),(2,66,175),(0,0,0),(0,0,0),(2,78,170),(2,4,187),(0,5,187),(0,0,0),(0,20,186),(1,20,186),(0,0,0),(0,0,0)]

def wits_35 : List (ℕ × ℕ × ℕ) := [(3,2,187),(0,51,180),(1,51,180),(0,0,0),(2,20,186),(0,6,187),(0,0,0),(0,0,0),(3,66,175),(0,28,185),(0,39,183),(0,0,0),(0,34,184),(1,34,184),(0,0,0),(0,0,0),(4,86,166),(0,76,171),(0,7,187),(0,0,0),(2,34,184),(3,5,187),(0,0,0),(0,0,0),(10,30,182),(2,76,171),(2,7,187),(0,0,0),(3,51,180),(12,55,174),(0,0,0),(0,0,0),(3,6,187),(0,8,187),(1,8,187),(0,0,0),(3,28,185),(0,21,186),(0,0,0),(0,0,0),(4,124,140),(2,8,187),(4,3,187),(0,0,0),(0,112,150),(1,112,150),(0,0,0),(0,0,0),(0,58,178),(1,58,178),(0,9,187),(0,0,0),(2,112,150),(0,102,157),(0,0,0),(0,0,0),(2,58,178),(6,104,155),(2,9,187),(0,0,0),(0,44,182),(1,44,182),(0,0,0),(0,0,0),(3,21,186),(0,48,181),(0,29,185),(0,0,0),(2,44,182),(0,10,187),(0,0,0),(0,0,0),(0,64,176),(0,108,153),(1,108,153),(0,0,0),(4,34,184),(2,10,187),(0,0,0),(0,0,0),(0,22,186),(0,35,184),(0,99,159),(0,0,0),(7,105,154),(10,31,182),(0,0,0),(0,0,0),(2,22,186),(0,40,183),(0,11,187),(0,0,0),(3,48,181),(3,29,185),(0,0,0),(0,0,0),(3,10,187),(2,40,183),(2,11,187),(0,0,0),(3,108,153),(4,21,186),(0,0,0),(0,0,0),(0,52,180),(1,52,180),(5,66,175),(0,0,0),(3,35,184),(3,99,159),(0,0,0),(0,0,0),(2,52,180),(0,12,187),(0,67,175),(0,0,0),(3,40,183),(0,131,134),(0,0,0),(0,0,0),(10,62,174),(2,12,187),(0,81,169),(0,0,0),(4,44,182),(0,23,186),(0,0,0),(0,0,0),(7,36,183),(0,115,148),(1,115,148),(0,0,0),(18,20,170),(2,23,186),(0,0,0),(0,0,0),(0,120,144),(0,96,161),(0,13,187),(0,0,0),(3,12,187),(0,79,170),(0,0,0),(0,0,0),(2,120,144),(2,96,161),(0,89,165),(0,0,0),(7,41,182),(0,45,182),(0,0,0),(0,0,0),(0,36,184),(0,128,137),(1,128,137),(0,0,0),(3,115,148),(2,45,182),(0,0,0),(0,0,0),(2,36,184),(2,128,137),(0,49,181),(0,0,0),(3,96,161),(0,14,187),(0,0,0),(0,0,0),(3,79,170),(5,112,150),(0,41,183),(0,0,0),(0,24,186),(0,62,177),(0,0,0),(0,0,0),(0,70,174),(0,56,179),(1,56,179),(0,0,0),(2,24,186),(2,62,177),(0,0,0),(0,0,0),(2,70,174),(2,56,179),(0,31,185),(0,0,0),(8,76,170),(3,49,181),(0,0,0),(0,0,0),(3,14,187),(4,115,148),(0,15,187),(0,0,0),(11,3,184),(0,114,149),(0,0,0),(0,0,0),(3,62,177),(0,65,176),(1,65,176),(0,0,0),(0,98,160),(1,98,160),(0,0,0),(0,0,0),(8,10,186),(0,53,180),(1,53,180),(0,0,0),(2,98,160),(3,31,185),(0,0,0),(0,0,0),(4,36,184),(2,53,180),(0,93,163),(0,0,0),(7,46,181),(0,25,186),(0,0,0),(0,0,0),(3,114,149),(0,16,187),(1,16,187),(0,0,0),(3,65,176),(2,25,186),(0,0,0),(0,0,0),(19,22,167),(2,16,187),(4,41,183),(0,0,0),(3,53,180),(4,62,177),(0,0,0),(0,0,0),(0,46,182),(1,46,182),(5,131,134),(0,0,0),(7,26,185),(3,93,163),(0,0,0),(0,0,0),(2,46,182),(0,32,185),(1,32,185),(0,0,0),(3,16,187),(0,42,183),(0,0,0),(0,0,0),(7,73,172),(0,124,141),(0,17,187),(0,0,0),(6,112,150),(0,50,181),(0,0,0),(0,0,0),(6,58,178),(2,124,141),(2,17,187),(0,0,0),(4,98,160),(0,95,162),(0,0,0),(0,0,0),(0,26,186),(1,26,186),(5,45,182),(0,0,0),(3,32,185),(2,95,162),(0,0,0),(0,0,0),(0,84,168),(0,100,159),(1,100,159),(0,0,0),(0,60,178),(0,82,169),(0,0,0),(0,0,0),(2,84,168),(2,100,159),(0,57,179),(0,0,0),(2,60,178),(0,18,187),(0,0,0),(0,0,0),(3,95,162),(5,24,186),(0,63,177),(0,0,0),(0,38,184),(1,38,184),(0,0,0),(0,0,0),(4,46,182),(6,40,183),(2,63,177),(0,0,0),(2,38,184),(12,125,134),(0,0,0),(0,0,0),(3,82,169),(4,32,185),(0,33,185),(0,0,0),(0,54,180),(0,71,174),(0,0,0),(0,0,0),(3,18,187),(4,124,141),(2,33,185),(0,0,0),(2,54,180),(0,27,186),(0,0,0),(0,0,0),(7,4,187),(5,98,160),(0,19,187),(0,0,0),(0,66,176),(0,47,182),(0,0,0),(0,0,0),(4,26,186),(7,5,187),(0,43,183),(0,0,0),(2,66,176),(2,47,182),(0,0,0),(0,0,0),(0,0,188),(0,1,188),(1,1,188),(0,0,0),(0,2,188),(1,2,188),(0,0,0),(0,0,0),(2,0,188),(0,3,188),(1,3,188),(0,0,0),(2,2,188),(3,19,187),(0,0,0),(0,0,0),(0,4,188),(0,105,156),(0,51,181),(0,0,0),(4,38,184),(3,43,183),(0,0,0),(0,0,0),(0,102,158),(0,5,188),(1,5,188),(0,0,0),(3,1,188),(10,97,158),(0,0,0),(0,0,0),(2,102,158),(0,39,184),(0,133,133),(0,0,0),(0,6,188),(0,34,185),(0,0,0),(0,0,0),(15,125,128),(2,39,184),(0,69,175),(0,0,0),(2,6,188),(2,34,185),(0,0,0),(0,0,0),(6,70,174),(0,7,188),(1,7,188),(0,0,0),(0,130,136),(1,130,136),(0,0,0),(0,0,0),(8,42,182),(0,99,160),(1,99,160),(0,0,0),(2,130,136),(0,58,179),(0,0,0),(0,0,0),(0,8,188),(1,8,188),(0,21,187),(0,0,0),(4,2,188),(2,58,179),(0,0,0),(0,0,0),(2,8,188),(4,3,188),(2,21,187),(0,0,0),(3,7,188),(10,14,185),(0,0,0),(0,0,0),(4,4,188),(0,9,188),(0,115,149),(0,0,0),(0,48,182),(1,48,182),(0,0,0),(0,0,0),(3,58,179),(2,9,188),(2,115,149),(0,0,0),(2,48,182),(0,29,186),(0,0,0),(0,0,0),(15,33,176),(4,39,184),(4,133,133),(0,0,0),(0,10,188),(1,10,188),(0,0,0),(0,0,0),(10,112,148),(0,85,168),(0,35,185),(0,0,0),(2,10,188),(0,22,187),(0,0,0),(0,0,0),(0,40,184),(1,40,184),(0,87,167),(0,0,0),(0,72,174),(0,81,170),(0,0,0),(0,0,0),(2,40,184),(0,11,188),(1,11,188),(0,0,0),(2,72,174),(2,81,170),(0,0,0),(0,0,0),(4,8,188),(2,11,188),(0,107,155),(0,0,0),(0,126,140),(0,89,166),(0,0,0),(0,0,0),(3,22,187),(7,13,187),(0,79,171),(0,0,0),(2,126,140),(2,89,166),(0,0,0),(0,0,0),(0,12,188),(1,12,188),(2,79,171),(0,0,0),(3,11,188),(5,102,158),(0,0,0),(0,0,0),(0,30,186),(1,30,186),(0,23,187),(0,0,0),(6,60,178),(3,107,155),(0,0,0),(0,0,0),(2,30,186),(5,6,188),(0,91,165),(0,0,0),(4,10,188),(0,110,153),(0,0,0),(0,0,0),(14,128,128),(0,13,188),(0,45,183),(0,0,0),(6,38,184),(2,110,153),(0,0,0),(0,0,0),(4,40,184),(0,36,185),(0,59,179),(0,0,0),(4,72,174),(0,49,182),(0,0,0),(0,0,0),(0,62,178),(1,62,178),(2,59,179),(0,0,0),(6,54,180),(0,118,147),(0,0,0),(0,0,0),(0,56,180),(0,41,184),(1,41,184),(0,0,0),(0,14,188),(1,14,188),(0,0,0),(0,0,0),(2,56,180),(0,24,187),(1,24,187),(0,0,0),(2,14,188),(3,59,179),(0,0,0),(0,0,0),(3,49,182),(2,24,187),(0,65,177),(0,0,0),(8,112,150),(0,31,186),(0,0,0),(0,0,0),(3,118,147),(6,1,188),(2,65,177),(0,0,0),(3,41,184),(2,31,186),(0,0,0),(0,0,0),(7,16,187),(0,15,188),(0,53,181),(0,0,0),(0,106,156),(0,103,158),(0,0,0),(0,0,0),(6,4,188),(2,15,188),(0,123,143),(0,0,0),(2,106,156),(2,103,158),(0,0,0),(0,0,0),(3,31,186),(4,36,185),(2,123,143),(0,0,0),(12,2,184),(4,49,182),(0,0,0),(0,0,0),(4,62,178),(0,117,148),(0,25,187),(0,0,0),(3,15,188),(0,109,154),(0,0,0),(0,0,0),(0,16,188),(1,16,188),(2,25,187),(0,0,0),(4,14,188),(0,46,183),(0,0,0),(0,0,0),(2,16,188),(4,24,187),(10,43,181),(0,0,0),(6,130,136),(2,46,183),(0,0,0),(0,0,0),(8,52,180),(0,84,169),(1,84,169),(0,0,0),(0,32,186),(1,32,186),(0,0,0),(0,0,0),(0,50,182),(1,50,182),(6,21,187),(0,0,0),(2,32,186),(8,131,134),(0,0,0),(0,0,0),(2,50,182),(0,17,188),(1,17,188),(0,0,0),(4,106,156),(4,103,158),(0,0,0),(0,0,0),(10,28,184),(0,60,179),(1,60,179),(0,0,0),(3,84,169),(0,26,187),(0,0,0),(0,0,0),(0,112,152),(0,57,180),(1,57,180),(0,0,0),(19,83,148),(0,63,178),(0,0,0),(0,0,0),(0,90,166),(0,116,149),(1,116,149),(0,0,0),(3,17,188),(2,63,178),(0,0,0),(0,0,0),(2,90,166),(2,116,149),(0,71,175),(0,0,0),(0,18,188),(0,38,185),(0,0,0),(0,0,0),(3,26,187),(7,19,187),(0,105,157),(0,0,0),(2,18,188),(0,54,181),(0,0,0),(0,0,0),(3,63,178),(4,84,169),(2,105,157),(0,0,0),(3,116,149),(0,33,186),(0,0,0),(0,0,0),(4,50,182),(0,92,165),(1,92,165),(0,0,0),(6,126,140),(2,33,186),(0,0,0),(0,0,0),(3,38,185),(2,92,165),(0,27,187),(0,0,0),(11,12,185),(3,105,157),(0,0,0),(0,0,0),(3,54,181),(0,19,188),(1,19,188),(0,0,0),(10,92,162),(4,26,187),(0,0,0),(0,0,0),(3,33,186),(2,19,188),(6,23,187),(0,0,0),(0,120,146),(1,120,146),(0,0,0),(0,0,0),(4,90,166),(0,0,189),(0,1,189),(0,0,0),(2,120,146),(0,2,189),(0,0,0),(0,0,0),(12,12,184),(0,127,140),(0,3,189),(0,0,0),(0,94,164),(1,94,164),(0,0,0),(0,0,0),(7,7,188),(0,4,189),(1,4,189),(0,0,0),(2,94,164),(4,54,181),(0,0,0),(0,0,0),(0,20,188),(1,20,188),(0,5,189),(0,0,0),(3,0,189),(3,1,189),(0,0,0),(0,0,0),(0,34,186),(0,28,187),(1,28,187),(0,0,0),(3,127,140),(0,6,189),(0,0,0),(0,0,0),(2,34,186),(2,28,187),(0,61,179),(0,0,0),(0,58,180),(1,58,180),(0,0,0),(0,0,0),(7,9,188),(4,19,188),(0,7,189),(0,0,0),(2,58,180),(3,5,189),(0,0,0),(0,0,0),(11,83,166),(9,58,178),(2,7,189),(0,0,0),(0,64,178),(1,64,178),(0,0,0),(0,0,0),(3,6,189),(0,8,189),(0,55,181),(0,0,0),(2,64,178),(0,83,170),(0,0,0),(0,0,0),(0,44,184),(0,48,183),(1,48,183),(0,0,0),(4,94,164),(0,114,151),(0,0,0),(0,0,0),(2,44,184),(0,101,160),(0,9,189),(0,0,0),(7,81,170),(2,114,151),(0,0,0),(0,0,0),(4,20,188),(0,72,175),(0,29,187),(0,0,0),(3,8,189),(3,55,181),(0,0,0),(0,0,0),(0,110,154),(1,110,154),(0,67,177),(0,0,0),(3,48,183),(0,10,189),(0,0,0),(0,0,0),(2,110,154),(0,40,185),(1,40,185),(0,0,0),(0,22,188),(1,22,188),(0,0,0),(0,0,0),(11,65,174),(2,40,185),(4,7,189),(0,0,0),(2,22,188),(0,91,166),(0,0,0),(0,0,0),(6,50,182),(5,120,146),(0,11,189),(0,0,0),(4,64,178),(2,91,166),(0,0,0),(0,0,0),(0,98,162),(1,98,162),(2,11,189),(0,0,0),(3,40,185),(4,83,170),(0,0,0),(0,0,0),(2,98,162),(4,48,183),(0,77,173),(0,0,0),(8,2,188),(4,114,151),(0,0,0),(0,0,0),(3,91,166),(0,12,189),(1,12,189),(0,0,0),(7,49,182),(0,30,187),(0,0,0),(0,0,0),(6,90,166),(0,23,188),(0,93,165),(0,0,0),(0,70,176),(1,70,176),(0,0,0),(0,0,0),(4,110,154),(0,45,184),(1,45,184),(0,0,0),(2,70,176),(0,62,179),(0,0,0),(0,0,0),(7,24,187),(2,45,184),(0,13,189),(0,0,0),(0,36,186),(1,36,186),(0,0,0),(0,0,0),(3,30,187),(0,56,181),(1,56,181),(0,0,0),(2,36,186),(0,75,174),(0,0,0),(0,0,0),(14,6,182),(2,56,181),(0,41,185),(0,0,0),(3,45,184),(0,65,178),(0,0,0),(0,0,0),(0,134,134),(1,134,134),(0,133,135),(0,0,0),(7,103,158),(0,14,189),(0,0,0),(0,0,0),(0,24,188),(0,95,164),(1,95,164),(0,0,0),(3,56,181),(2,14,189),(0,0,0),(0,0,0),(2,24,188),(2,95,164),(0,31,187),(0,0,0),(6,120,146),(0,53,182),(0,0,0),(0,0,0),(3,65,178),(4,23,188),(2,31,187),(0,0,0),(4,70,176),(2,53,182),(0,0,0),(0,0,0),(0,130,138),(1,130,138),(0,15,189),(0,0,0),(3,95,164),(4,62,179),(0,0,0),(0,0,0),(2,130,138),(0,68,177),(0,73,175),(0,0,0),(0,84,170),(0,86,169),(0,0,0),(0,0,0),(3,53,182),(2,68,177),(0,129,139),(0,0,0),(2,84,170),(0,37,186),(0,0,0),(0,0,0),(0,88,168),(0,25,188),(1,25,188),(0,0,0),(0,46,184),(1,46,184),(0,0,0),(0,0,0),(2,88,168),(0,16,189),(0,97,163),(0,0,0),(2,46,184),(3,73,175),(0,0,0),(0,0,0),(0,80,172),(1,80,172),(2,97,163),(0,0,0),(7,26,187),(0,42,185),(0,0,0),(0,0,0),(2,80,172),(0,32,187),(1,32,187),(0,0,0),(3,25,188),(2,42,185),(0,0,0),(0,0,0)]

def wits_36 : List (ℕ × ℕ × ℕ) := [(0,60,180),(1,60,180),(6,55,181),(0,0,0),(0,102,160),(1,102,160),(0,0,0),(0,0,0),(2,60,180),(0,120,147),(0,17,189),(0,0,0),(2,102,160),(0,78,173),(0,0,0),(0,0,0),(3,42,185),(0,71,176),(1,71,176),(0,0,0),(0,26,188),(1,26,188),(0,0,0),(0,0,0),(11,58,177),(2,71,176),(0,115,151),(0,0,0),(2,26,188),(4,37,186),(0,0,0),(0,0,0),(4,88,168),(4,25,188),(2,115,151),(0,0,0),(3,120,147),(0,111,154),(0,0,0),(0,0,0),(0,38,186),(1,38,186),(4,97,163),(0,0,0),(3,71,176),(0,18,189),(0,0,0),(0,0,0),(2,38,186),(8,41,184),(10,9,187),(0,0,0),(0,76,174),(1,76,174),(0,0,0),(0,0,0),(18,68,160),(4,32,187),(0,33,187),(0,0,0),(2,76,174),(0,94,165),(0,0,0),(0,0,0),(3,111,154),(0,47,184),(1,47,184),(0,0,0),(4,102,160),(2,94,165),(0,0,0),(0,0,0),(3,18,189),(0,27,188),(0,43,185),(0,0,0),(11,52,179),(4,78,173),(0,0,0),(0,0,0),(7,4,189),(2,27,188),(0,19,189),(0,0,0),(4,26,188),(3,33,187),(0,0,0),(0,0,0),(3,94,165),(6,23,188),(0,51,183),(0,0,0),(3,47,184),(5,88,168),(0,0,0),(0,0,0),(7,28,187),(0,104,159),(0,107,157),(0,0,0),(0,0,190),(0,1,190),(0,0,0),(0,0,0),(0,2,190),(1,2,190),(2,107,157),(0,0,0),(2,0,190),(0,3,190),(0,0,0),(0,0,0),(0,96,164),(1,96,164),(5,42,185),(0,0,0),(0,4,190),(0,39,186),(0,0,0),(0,0,0),(2,96,164),(0,20,189),(0,101,161),(0,0,0),(2,4,190),(0,5,190),(0,0,0),(0,0,0),(0,28,188),(1,28,188),(0,83,171),(0,0,0),(7,83,170),(2,5,190),(0,0,0),(0,0,0),(0,6,190),(0,64,179),(1,64,179),(0,0,0),(7,114,151),(10,79,170),(0,0,0),(0,0,0),(2,6,190),(0,81,172),(1,81,172),(0,0,0),(3,20,189),(0,7,190),(0,0,0),(0,0,0),(3,5,190),(2,81,172),(0,123,145),(0,0,0),(14,56,174),(2,7,190),(0,0,0),(0,0,0),(0,48,184),(0,44,185),(0,21,189),(0,0,0),(0,8,190),(1,8,190),(0,0,0),(0,0,0),(2,48,184),(2,44,185),(0,79,173),(0,0,0),(2,8,190),(0,67,178),(0,0,0),(0,0,0),(3,7,190),(5,76,174),(0,113,153),(0,0,0),(4,4,190),(0,9,190),(0,0,0),(0,0,0),(6,88,168),(0,29,188),(1,29,188),(0,0,0),(3,44,185),(0,117,150),(0,0,0),(0,0,0),(4,28,188),(0,52,183),(0,35,187),(0,0,0),(0,40,186),(1,40,186),(0,0,0),(0,0,0),(0,10,190),(1,10,190),(2,35,187),(0,0,0),(2,40,186),(0,22,189),(0,0,0),(0,0,0),(2,10,190),(0,103,160),(1,103,160),(0,0,0),(3,29,188),(2,22,189),(0,0,0),(0,0,0),(3,117,150),(0,109,156),(1,109,156),(0,0,0),(3,52,183),(0,11,190),(0,0,0),(0,0,0),(4,48,184),(2,109,156),(4,21,189),(0,0,0),(4,8,190),(0,70,177),(0,0,0),(0,0,0),(3,22,189),(6,71,176),(4,79,173),(0,0,0),(3,103,160),(2,70,177),(0,0,0),(0,0,0),(7,56,181),(0,129,140),(0,59,181),(0,0,0),(0,12,190),(1,12,190),(0,0,0),(0,0,0),(3,11,190),(2,129,140),(0,23,189),(0,0,0),(2,12,190),(4,117,150),(0,0,0),(0,0,0),(3,70,177),(0,49,184),(1,49,184),(0,0,0),(0,56,182),(1,56,182),(0,0,0),(0,0,0),(4,10,190),(0,36,187),(0,65,179),(0,0,0),(2,56,182),(0,13,190),(0,0,0),(0,0,0),(10,26,186),(2,36,187),(2,65,179),(0,0,0),(7,53,182),(0,41,186),(0,0,0),(0,0,0),(10,84,168),(4,109,156),(8,7,189),(0,0,0),(3,49,184),(2,41,186),(0,0,0),(0,0,0),(11,19,186),(5,8,190),(6,43,185),(0,0,0),(3,36,187),(0,127,142),(0,0,0),(0,0,0),(0,14,190),(0,24,189),(0,53,183),(0,0,0),(7,86,169),(2,127,142),(0,0,0),(0,0,0),(0,120,148),(0,31,188),(0,105,159),(0,0,0),(0,68,178),(1,68,178),(0,0,0),(0,0,0),(2,120,148),(0,108,157),(1,108,157),(0,0,0),(2,68,178),(6,1,190),(0,0,0),(0,0,0),(3,127,142),(2,108,157),(8,29,187),(0,0,0),(0,90,168),(0,15,190),(0,0,0),(0,0,0),(6,96,164),(0,80,173),(1,80,173),(0,0,0),(2,90,168),(2,15,190),(0,0,0),(0,0,0),(7,32,187),(2,80,173),(0,37,187),(0,0,0),(3,108,157),(0,46,185),(0,0,0),(0,0,0),(6,28,188),(10,1,188),(0,25,189),(0,0,0),(10,2,188),(2,46,185),(0,0,0),(0,0,0),(3,15,190),(0,92,167),(1,92,167),(0,0,0),(0,16,190),(1,16,190),(0,0,0),(0,0,0),(0,42,186),(0,60,181),(0,119,149),(0,0,0),(2,16,190),(3,37,187),(0,0,0),(0,0,0),(0,32,188),(0,63,180),(0,71,177),(0,0,0),(4,68,178),(0,57,182),(0,0,0),(0,0,0),(2,32,188),(2,63,180),(2,71,177),(0,0,0),(3,92,167),(2,57,182),(0,0,0),(0,0,0),(11,102,157),(5,56,182),(6,79,173),(0,0,0),(3,60,181),(0,17,190),(0,0,0),(0,0,0),(0,94,166),(1,94,166),(5,13,190),(0,0,0),(3,63,180),(0,26,189),(0,0,0),(0,0,0),(2,94,166),(0,76,175),(1,76,175),(0,0,0),(7,94,165),(0,54,183),(0,0,0),(0,0,0),(7,47,184),(2,76,175),(4,25,189),(0,0,0),(6,40,186),(0,38,187),(0,0,0),(0,0,0),(0,104,160),(1,104,160),(5,127,142),(0,0,0),(4,16,190),(2,38,187),(0,0,0),(0,0,0),(0,18,190),(1,18,190),(4,119,149),(0,0,0),(3,76,175),(5,120,148),(0,0,0),(0,0,0),(2,18,190),(0,33,188),(0,47,185),(0,0,0),(0,110,156),(1,110,156),(0,0,0),(0,0,0),(3,38,187),(0,96,165),(1,96,165),(0,0,0),(2,110,156),(0,43,186),(0,0,0),(0,0,0),(11,131,134),(2,96,165),(0,27,189),(0,0,0),(0,74,176),(1,74,176),(0,0,0),(0,0,0),(4,94,166),(0,51,184),(0,133,137),(0,0,0),(2,74,176),(0,19,190),(0,0,0),(0,0,0),(7,20,189),(2,51,184),(0,85,171),(0,0,0),(0,132,138),(0,87,170),(0,0,0),(0,0,0),(3,43,186),(0,83,172),(1,83,172),(0,0,0),(2,132,138),(2,87,170),(0,0,0),(0,0,0),(4,104,160),(0,0,191),(0,1,191),(0,0,0),(3,51,184),(0,2,191),(0,0,0),(0,0,0),(0,58,182),(1,58,182),(0,3,191),(0,0,0),(7,7,190),(0,122,147),(0,0,0),(0,0,0),(0,64,180),(0,4,191),(1,4,191),(0,0,0),(0,20,190),(1,20,190),(0,0,0),(0,0,0),(2,64,180),(0,28,189),(0,5,191),(0,0,0),(2,20,190),(3,1,191),(0,0,0),(0,0,0),(3,2,191),(0,72,177),(0,55,183),(0,0,0),(4,74,176),(0,6,191),(0,0,0),(0,0,0),(3,122,147),(2,72,177),(0,129,141),(0,0,0),(3,4,191),(2,6,191),(0,0,0),(0,0,0),(7,29,188),(0,48,185),(0,7,191),(0,0,0),(0,44,186),(1,44,186),(0,0,0),(0,0,0),(7,52,183),(2,48,185),(0,93,167),(0,0,0),(2,44,186),(0,21,190),(0,0,0),(0,0,0),(3,6,191),(0,8,191),(1,8,191),(0,0,0),(0,128,142),(1,128,142),(0,0,0),(0,0,0),(4,58,182),(2,8,191),(0,77,175),(0,0,0),(2,128,142),(3,7,191),(0,0,0),(0,0,0),(0,52,184),(1,52,184),(0,9,191),(0,0,0),(4,20,190),(3,93,167),(0,0,0),(0,0,0),(2,52,184),(0,35,188),(1,35,188),(0,0,0),(3,8,191),(8,94,165),(0,0,0),(0,0,0),(6,42,186),(2,35,188),(0,127,143),(0,0,0),(11,32,185),(0,10,191),(0,0,0),(0,0,0),(0,22,190),(1,22,190),(2,127,143),(0,0,0),(11,124,141),(2,10,191),(0,0,0),(0,0,0),(2,22,190),(4,48,185),(4,7,191),(0,0,0),(3,35,188),(10,109,154),(0,0,0),(0,0,0),(7,49,184),(0,75,176),(0,11,191),(0,0,0),(14,2,184),(0,59,182),(0,0,0),(0,0,0),(3,10,191),(2,75,176),(2,11,191),(0,0,0),(0,126,144),(1,126,144),(0,0,0),(0,0,0),(8,2,190),(6,76,175),(4,77,175),(0,0,0),(2,126,144),(0,30,189),(0,0,0),(0,0,0),(4,52,184),(0,12,191),(0,49,185),(0,0,0),(0,108,158),(0,23,190),(0,0,0),(0,0,0),(3,59,182),(2,12,191),(0,97,165),(0,0,0),(2,108,158),(0,86,171),(0,0,0),(0,0,0),(0,36,188),(1,36,188),(2,97,165),(0,0,0),(0,88,170),(1,88,170),(0,0,0),(0,0,0),(0,102,162),(1,102,162),(0,13,191),(0,0,0),(2,88,170),(0,82,173),(0,0,0),(0,0,0),(2,102,162),(0,111,156),(0,73,177),(0,0,0),(19,76,155),(0,90,169),(0,0,0),(0,0,0),(3,86,171),(0,53,184),(1,53,184),(0,0,0),(6,74,176),(2,90,169),(0,0,0),(0,0,0),(7,80,173),(2,53,184),(6,133,137),(0,0,0),(0,24,190),(0,14,191),(0,0,0),(0,0,0),(3,82,173),(7,37,187),(0,31,189),(0,0,0),(2,24,190),(2,14,191),(0,0,0),(0,0,0),(0,92,168),(1,92,168),(2,31,189),(0,0,0),(0,124,146),(1,124,146),(0,0,0),(0,0,0),(2,92,168),(0,99,164),(1,99,164),(0,0,0),(2,124,146),(4,86,171),(0,0,0),(0,0,0),(3,14,191),(2,99,164),(0,15,191),(0,0,0),(4,88,170),(0,78,175),(0,0,0),(0,0,0),(0,46,186),(0,37,188),(1,37,188),(0,0,0),(6,20,190),(2,78,175),(0,0,0),(0,0,0),(2,46,186),(0,135,136),(1,135,136),(0,0,0),(0,60,182),(0,25,190),(0,0,0),(0,0,0),(15,107,148),(2,135,136),(0,63,181),(0,0,0),(2,60,182),(0,42,187),(0,0,0),(0,0,0),(3,78,175),(0,16,191),(0,57,183),(0,0,0),(3,37,188),(2,42,187),(0,0,0),(0,0,0),(7,76,175),(0,32,189),(1,32,189),(0,0,0),(3,135,136),(0,110,157),(0,0,0),(0,0,0),(0,76,176),(1,76,176),(5,23,190),(0,0,0),(0,66,180),(1,66,180),(0,0,0),(0,0,0),(2,76,176),(0,131,140),(1,131,140),(0,0,0),(2,66,180),(3,57,183),(0,0,0),(0,0,0),(11,29,186),(2,131,140),(0,17,191),(0,0,0),(0,54,184),(1,54,184),(0,0,0),(0,0,0),(0,26,190),(1,26,190),(2,17,191),(0,0,0),(2,54,184),(0,130,141),(0,0,0),(0,0,0),(2,26,190),(4,135,136),(5,90,169),(0,0,0),(0,38,188),(1,38,188),(0,0,0),(0,0,0),(10,44,184),(0,117,152),(0,113,155),(0,0,0),(2,38,188),(3,17,191),(0,0,0),(0,0,0),(6,22,190),(2,117,152),(0,69,179),(0,0,0),(7,19,190),(0,18,191),(0,0,0),(0,0,0),(3,130,141),(0,85,172),(0,33,189),(0,0,0),(7,87,170),(2,18,191),(0,0,0),(0,0,0),(4,76,176),(2,85,172),(0,43,187),(0,0,0),(3,117,152),(0,89,170),(0,0,0),(0,0,0),(7,0,191),(4,131,140),(0,51,185),(0,0,0),(6,126,144),(0,27,190),(0,0,0),(0,0,0),(3,18,191),(0,128,143),(1,128,143),(0,0,0),(0,106,160),(0,81,174),(0,0,0),(0,0,0),(4,26,190),(2,128,143),(0,19,191),(0,0,0),(2,106,160),(0,61,182),(0,0,0),(0,0,0),(3,89,170),(5,60,182),(2,19,191),(0,0,0),(4,38,188),(0,58,183),(0,0,0),(0,0,0),(3,27,190),(0,64,181),(1,64,181),(0,0,0),(3,128,143),(2,58,183),(0,0,0),(0,0,0),(0,0,192),(0,1,192),(0,79,175),(0,0,0),(0,2,192),(1,2,192),(0,0,0),(0,0,0),(2,0,192),(0,3,192),(1,3,192),(0,0,0),(2,2,192),(0,34,189),(0,0,0),(0,0,0),(0,4,192),(0,20,191),(1,20,191),(0,0,0),(0,28,190),(1,28,190),(0,0,0),(0,0,0),(2,4,192),(0,5,192),(1,5,192),(0,0,0),(2,28,190),(3,79,175),(0,0,0),(0,0,0),(0,100,164),(1,100,164),(6,31,189),(0,0,0),(0,6,192),(0,126,145),(0,0,0),(0,0,0),(2,100,164),(0,44,187),(1,44,187),(0,0,0),(2,6,192),(2,126,145),(0,0,0),(0,0,0),(7,35,188),(0,7,192),(0,95,167),(0,0,0),(3,5,192),(4,58,183),(0,0,0),(0,0,0),(10,24,188),(2,7,192),(0,21,191),(0,0,0),(7,10,191),(6,78,175),(0,0,0),(0,0,0),(0,8,192),(0,52,185),(1,52,185),(0,0,0),(3,44,187),(10,53,182),(0,0,0),(0,0,0),(2,8,192),(2,52,185),(9,103,160),(0,0,0),(3,7,192),(0,29,190),(0,0,0),(0,0,0),(0,40,188),(0,9,192),(0,35,189),(0,0,0),(4,28,190),(2,29,190),(0,0,0),(0,0,0),(2,40,188),(2,9,192),(0,75,177),(0,0,0),(3,52,185),(8,43,186),(0,0,0),(0,0,0),(4,100,164),(5,106,160),(0,119,151),(0,0,0),(0,10,192),(0,22,191),(0,0,0),(0,0,0),(0,62,182),(1,62,182),(0,59,183),(0,0,0),(2,10,192),(0,102,163),(0,0,0),(0,0,0),(2,62,182),(4,7,192),(2,59,183),(0,0,0),(0,86,172),(1,86,172),(0,0,0),(0,0,0),(10,80,172),(0,11,192),(0,65,181),(0,0,0),(2,86,172),(3,119,151),(0,0,0),(0,0,0),(0,56,184),(1,56,184),(0,45,187),(0,0,0),(7,82,173),(0,49,186),(0,0,0),(0,0,0)]

def wits_37 : List (ℕ × ℕ × ℕ) := [(0,30,190),(1,30,190),(2,45,187),(0,0,0),(6,38,188),(2,49,186),(0,0,0),(0,0,0),(0,12,192),(1,12,192),(0,23,191),(0,0,0),(3,11,192),(0,73,178),(0,0,0),(0,0,0),(2,12,192),(0,36,189),(1,36,189),(0,0,0),(7,14,191),(0,114,155),(0,0,0),(0,0,0),(0,68,180),(0,41,188),(0,99,165),(0,0,0),(0,118,152),(1,118,152),(0,0,0),(0,0,0),(2,68,180),(0,13,192),(0,53,185),(0,0,0),(2,118,152),(3,23,191),(0,0,0),(0,0,0),(3,73,178),(2,13,192),(0,131,141),(0,0,0),(3,36,189),(6,27,190),(0,0,0),(0,0,0),(3,114,155),(0,107,160),(1,107,160),(0,0,0),(3,41,188),(3,99,165),(0,0,0),(0,0,0),(4,56,184),(0,24,191),(1,24,191),(0,0,0),(0,14,192),(0,31,190),(0,0,0),(0,0,0),(0,110,158),(1,110,158),(5,29,190),(0,0,0),(2,14,192),(2,31,190),(0,0,0),(0,0,0),(2,110,158),(6,64,181),(4,23,191),(0,0,0),(3,107,160),(4,73,178),(0,0,0),(0,0,0),(6,0,192),(4,36,189),(0,71,179),(0,0,0),(3,24,191),(0,46,187),(0,0,0),(0,0,0),(3,31,190),(0,15,192),(0,37,189),(0,0,0),(4,118,152),(0,63,182),(0,0,0),(0,0,0),(0,50,186),(0,101,164),(0,117,153),(0,0,0),(6,28,190),(2,63,182),(0,0,0),(0,0,0),(2,50,186),(0,57,184),(0,25,191),(0,0,0),(0,42,188),(1,42,188),(0,0,0),(0,0,0),(3,46,187),(2,57,184),(2,25,191),(0,0,0),(2,42,188),(0,66,181),(0,0,0),(0,0,0),(0,16,192),(1,16,192),(5,49,186),(0,0,0),(0,32,190),(1,32,190),(0,0,0),(0,0,0),(2,16,192),(6,7,192),(6,95,167),(0,0,0),(2,32,190),(3,25,191),(0,0,0),(0,0,0),(7,117,152),(7,113,155),(5,73,178),(0,0,0),(8,108,158),(0,54,185),(0,0,0),(0,0,0),(3,66,181),(6,52,185),(4,71,179),(0,0,0),(7,18,191),(2,54,185),(0,0,0),(0,0,0),(7,85,172),(0,17,192),(0,85,173),(0,0,0),(8,88,170),(0,26,191),(0,0,0),(0,0,0),(0,74,178),(0,69,180),(0,89,171),(0,0,0),(7,89,170),(0,38,189),(0,0,0),(0,0,0),(2,74,178),(2,69,180),(2,89,171),(0,0,0),(0,116,154),(1,116,154),(0,0,0),(0,0,0),(7,128,143),(8,53,184),(0,47,187),(0,0,0),(2,116,154),(0,91,170),(0,0,0),(0,0,0),(3,26,191),(5,14,192),(0,81,175),(0,0,0),(0,18,192),(0,33,190),(0,0,0),(0,0,0),(0,126,146),(0,43,188),(1,43,188),(0,0,0),(2,18,192),(0,51,186),(0,0,0),(0,0,0),(2,126,146),(0,120,151),(1,120,151),(0,0,0),(8,124,146),(2,51,186),(0,0,0),(0,0,0),(3,91,170),(2,120,151),(0,27,191),(0,0,0),(11,45,184),(3,81,175),(0,0,0),(0,0,0),(3,33,190),(0,79,176),(1,79,176),(0,0,0),(0,58,184),(1,58,184),(0,0,0),(0,0,0),(3,51,186),(0,19,192),(1,19,192),(0,0,0),(2,58,184),(4,38,189),(0,0,0),(0,0,0),(7,5,192),(2,19,192),(0,125,147),(0,0,0),(4,116,154),(3,27,191),(0,0,0),(0,0,0),(6,68,180),(6,41,188),(0,39,189),(0,0,0),(3,79,176),(4,91,170),(0,0,0),(0,0,0),(7,44,187),(0,0,193),(0,1,193),(0,0,0),(3,19,192),(0,2,193),(0,0,0),(0,0,0),(0,34,190),(1,34,190),(0,3,193),(0,0,0),(10,56,182),(2,2,193),(0,0,0),(0,0,0),(0,20,192),(0,4,193),(1,4,193),(0,0,0),(8,66,180),(0,105,162),(0,0,0),(0,0,0),(2,20,192),(0,48,187),(0,5,193),(0,0,0),(3,0,193),(0,134,139),(0,0,0),(0,0,0),(0,44,188),(1,44,188),(2,5,193),(0,0,0),(4,58,184),(0,6,193),(0,0,0),(0,0,0),(2,44,188),(0,133,140),(1,133,140),(0,0,0),(3,4,193),(2,6,193),(0,0,0),(0,0,0),(3,105,162),(2,133,140),(0,7,193),(0,0,0),(0,52,186),(1,52,186),(0,0,0),(0,0,0),(3,134,139),(0,21,192),(1,21,192),(0,0,0),(2,52,186),(0,75,178),(0,0,0),(0,0,0),(3,6,193),(0,8,193),(1,8,193),(0,0,0),(3,133,140),(2,75,178),(0,0,0),(0,0,0),(4,34,190),(0,40,189),(0,29,191),(0,0,0),(6,42,188),(0,35,190),(0,0,0),(0,0,0),(0,88,172),(1,88,172),(0,9,193),(0,0,0),(0,84,174),(0,62,183),(0,0,0),(0,0,0),(2,88,172),(0,59,184),(1,59,184),(0,0,0),(2,84,174),(0,90,171),(0,0,0),(0,0,0),(4,44,188),(2,59,184),(10,25,189),(0,0,0),(0,22,192),(0,10,193),(0,0,0),(0,0,0),(3,35,190),(4,133,140),(8,19,191),(0,0,0),(2,22,192),(0,99,166),(0,0,0),(0,0,0),(3,62,183),(0,56,185),(1,56,185),(0,0,0),(0,92,170),(1,92,170),(0,0,0),(0,0,0),(3,90,171),(0,45,188),(0,11,193),(0,0,0),(2,92,170),(4,75,178),(0,0,0),(0,0,0),(0,80,176),(0,129,144),(1,129,144),(0,0,0),(8,2,192),(0,30,191),(0,0,0),(0,0,0),(0,122,150),(0,68,181),(1,68,181),(0,0,0),(3,56,185),(2,30,191),(0,0,0),(0,0,0),(2,122,150),(0,12,193),(1,12,193),(0,0,0),(0,36,190),(0,94,169),(0,0,0),(0,0,0),(7,24,191),(2,12,193),(0,41,189),(0,0,0),(2,36,190),(0,53,186),(0,0,0),(0,0,0),(3,30,191),(0,128,145),(1,128,145),(0,0,0),(3,68,181),(0,78,177),(0,0,0),(0,0,0),(10,104,160),(2,128,145),(0,13,193),(0,0,0),(3,12,193),(2,78,177),(0,0,0),(0,0,0),(3,94,169),(4,56,185),(0,101,165),(0,0,0),(4,92,170),(3,41,189),(0,0,0),(0,0,0),(3,53,186),(4,45,188),(2,101,165),(0,0,0),(3,128,145),(13,46,182),(0,0,0),(0,0,0),(0,24,192),(0,71,180),(0,31,191),(0,0,0),(12,120,146),(0,14,193),(0,0,0),(0,0,0),(2,24,192),(2,71,180),(2,31,191),(0,0,0),(10,74,176),(2,14,193),(0,0,0),(0,0,0),(0,60,184),(1,60,184),(0,63,183),(0,0,0),(0,46,188),(1,46,188),(0,0,0),(0,0,0),(2,60,184),(6,0,193),(2,63,183),(0,0,0),(2,46,188),(0,37,190),(0,0,0),(0,0,0),(3,14,193),(4,128,145),(0,15,193),(0,0,0),(8,10,192),(2,37,190),(0,0,0),(0,0,0),(0,66,182),(0,109,160),(1,109,160),(0,0,0),(7,54,185),(0,42,189),(0,0,0),(0,0,0),(2,66,182),(0,25,192),(1,25,192),(0,0,0),(8,86,172),(0,98,167),(0,0,0),(0,0,0),(3,37,190),(2,25,192),(0,87,173),(0,0,0),(7,26,191),(0,85,174),(0,0,0),(0,0,0),(0,120,152),(0,16,193),(1,16,193),(0,0,0),(0,112,158),(1,112,158),(0,0,0),(0,0,0),(0,54,186),(1,54,186),(0,83,175),(0,0,0),(2,112,158),(0,74,179),(0,0,0),(0,0,0),(2,54,186),(5,36,190),(0,69,181),(0,0,0),(4,46,188),(2,74,179),(0,0,0),(0,0,0),(3,85,174),(0,125,148),(1,125,148),(0,0,0),(3,16,193),(4,37,190),(0,0,0),(0,0,0),(7,43,188),(0,81,176),(0,17,193),(0,0,0),(0,26,192),(1,26,192),(0,0,0),(0,0,0),(0,38,190),(1,38,190),(0,135,139),(0,0,0),(2,26,192),(0,93,170),(0,0,0),(0,0,0),(2,38,190),(0,47,188),(1,47,188),(0,0,0),(0,100,166),(1,100,166),(0,0,0),(0,0,0),(7,79,176),(0,115,156),(1,115,156),(0,0,0),(2,100,166),(3,17,193),(0,0,0),(0,0,0),(4,120,152),(2,115,156),(0,33,191),(0,0,0),(4,112,158),(0,18,193),(0,0,0),(0,0,0),(3,93,170),(0,61,184),(1,61,184),(0,0,0),(3,47,188),(2,18,193),(0,0,0),(0,0,0),(0,72,180),(0,64,183),(0,95,169),(0,0,0),(0,132,142),(0,58,185),(0,0,0),(0,0,0),(2,72,180),(0,27,192),(0,105,163),(0,0,0),(2,132,142),(2,58,185),(0,0,0),(0,0,0),(3,18,193),(2,27,192),(0,111,159),(0,0,0),(3,61,184),(5,66,182),(0,0,0),(0,0,0),(4,38,190),(6,12,193),(0,19,193),(0,0,0),(3,64,183),(0,67,182),(0,0,0),(0,0,0),(3,58,185),(4,47,188),(2,19,193),(0,0,0),(3,27,192),(0,39,190),(0,0,0),(0,0,0),(11,127,142),(4,115,156),(5,85,174),(0,0,0),(7,6,193),(0,102,165),(0,0,0),(0,0,0),(7,133,140),(0,97,168),(1,97,168),(0,0,0),(0,0,194),(0,1,194),(0,0,0),(0,0,0),(0,2,194),(1,2,194),(5,74,179),(0,0,0),(2,0,194),(0,3,194),(0,0,0),(0,0,0),(0,28,192),(0,20,193),(1,20,193),(0,0,0),(0,4,194),(1,4,194),(0,0,0),(0,0,0),(2,28,192),(0,44,189),(1,44,189),(0,0,0),(2,4,194),(0,5,194),(0,0,0),(0,0,0),(3,1,194),(2,44,189),(0,75,179),(0,0,0),(7,35,190),(2,5,194),(0,0,0),(0,0,0),(0,6,194),(0,52,187),(1,52,187),(0,0,0),(3,20,193),(4,67,182),(0,0,0),(0,0,0),(2,6,194),(0,84,175),(1,84,175),(0,0,0),(0,90,172),(0,7,194),(0,0,0),(0,0,0),(3,5,194),(2,84,175),(0,21,193),(0,0,0),(2,90,172),(0,107,162),(0,0,0),(0,0,0),(6,66,182),(4,97,168),(2,21,193),(0,0,0),(0,8,194),(1,8,194),(0,0,0),(0,0,0),(4,2,194),(0,29,192),(0,35,191),(0,0,0),(2,8,194),(4,3,194),(0,0,0),(0,0,0),(0,104,164),(1,104,164),(0,65,183),(0,0,0),(4,4,194),(0,9,194),(0,0,0),(0,0,0),(2,104,164),(4,44,189),(2,65,183),(0,0,0),(6,112,158),(2,9,194),(0,0,0),(0,0,0),(6,54,186),(0,73,180),(1,73,180),(0,0,0),(0,56,186),(0,22,193),(0,0,0),(0,0,0),(0,10,194),(1,10,194),(0,127,147),(0,0,0),(2,56,186),(2,22,193),(0,0,0),(0,0,0),(2,10,194),(0,49,188),(0,45,189),(0,0,0),(0,68,182),(1,68,182),(0,0,0),(0,0,0),(7,128,145),(2,49,188),(2,45,189),(0,0,0),(2,68,182),(0,11,194),(0,0,0),(0,0,0),(3,22,193),(5,0,194),(5,1,194),(0,0,0),(0,30,192),(1,30,192),(0,0,0),(0,0,0),(0,78,178),(1,78,178),(4,35,191),(0,0,0),(2,30,192),(3,45,189),(0,0,0),(0,0,0),(2,78,178),(0,36,191),(0,23,193),(0,0,0),(0,12,194),(0,41,190),(0,0,0),(0,0,0),(3,11,194),(2,36,191),(2,23,193),(0,0,0),(2,12,194),(2,41,190),(0,0,0),(0,0,0),(0,116,156),(1,116,156),(10,113,155),(0,0,0),(4,56,186),(4,22,193),(0,0,0),(0,0,0),(2,116,156),(6,64,183),(0,71,181),(0,0,0),(3,36,191),(0,13,194),(0,0,0),(0,0,0),(3,41,190),(0,120,153),(1,120,153),(0,0,0),(4,68,182),(0,137,138),(0,0,0),(0,0,0),(11,2,191),(0,76,179),(1,76,179),(0,0,0),(15,83,166),(2,137,138),(0,0,0),(0,0,0),(7,109,160),(0,24,193),(0,125,149),(0,0,0),(0,98,168),(1,98,168),(0,0,0),(0,0,0),(0,14,194),(1,14,194),(0,103,165),(0,0,0),(2,98,168),(0,46,189),(0,0,0),(0,0,0),(2,14,194),(4,36,191),(2,103,165),(0,0,0),(0,50,188),(0,57,186),(0,0,0),(0,0,0),(7,16,193),(6,97,168),(0,37,191),(0,0,0),(2,50,188),(0,133,142),(0,0,0),(0,0,0),(4,116,156),(5,56,186),(2,37,191),(0,0,0),(7,74,179),(0,15,194),(0,0,0),(0,0,0),(0,42,190),(0,83,176),(1,83,176),(0,0,0),(6,4,194),(2,15,194),(0,0,0),(0,0,0),(2,42,190),(0,132,143),(0,25,193),(0,0,0),(0,74,180),(0,119,154),(0,0,0),(0,0,0),(3,133,142),(2,132,143),(2,25,193),(0,0,0),(2,74,180),(0,54,187),(0,0,0),(0,0,0),(0,32,192),(0,100,167),(0,81,177),(0,0,0),(0,16,194),(1,16,194),(0,0,0),(0,0,0),(2,32,192),(0,131,144),(1,131,144),(0,0,0),(2,16,194),(3,25,193),(0,0,0),(0,0,0),(3,119,154),(2,131,144),(5,41,190),(0,0,0),(0,108,162),(1,108,162),(0,0,0),(0,0,0),(3,54,187),(7,33,191),(4,37,191),(0,0,0),(2,108,162),(3,81,177),(0,0,0),(0,0,0),(7,61,184),(0,105,164),(1,105,164),(0,0,0),(3,131,144),(0,17,194),(0,0,0),(0,0,0),(4,42,190),(2,105,164),(0,47,189),(0,0,0),(7,58,185),(2,17,194),(0,0,0),(0,0,0),(7,27,192),(4,132,143),(2,47,189),(0,0,0),(4,74,180),(4,119,154),(0,0,0),(0,0,0),(10,40,188),(0,51,188),(0,61,185),(0,0,0),(3,105,164),(0,43,190),(0,0,0),(0,0,0),(0,64,184),(0,33,192),(1,33,192),(0,0,0),(4,16,194),(0,129,146),(0,0,0),(0,0,0),(0,18,194),(1,18,194),(5,46,189),(0,0,0),(6,68,182),(2,129,146),(0,0,0),(0,0,0),(2,18,194),(5,50,188),(0,77,179),(0,0,0),(3,51,188),(3,61,185),(0,0,0),(0,0,0),(3,43,190),(13,64,178),(0,27,193),(0,0,0),(3,33,192),(8,37,190),(0,0,0),(0,0,0),(3,129,146),(4,105,164),(2,27,193),(0,0,0),(0,122,152),(1,122,152),(0,0,0),(0,0,0),(7,20,193),(0,128,147),(0,55,187),(0,0,0),(2,122,152),(0,19,194),(0,0,0),(0,0,0)]

def wits_38 : List (ℕ × ℕ × ℕ) := [(7,44,189),(2,128,147),(0,39,191),(0,0,0),(7,5,194),(2,19,194),(0,0,0),(0,0,0),(6,116,156),(4,51,188),(2,39,191),(0,0,0),(18,68,166),(4,43,190),(0,0,0),(0,0,0),(4,64,184),(4,33,192),(0,107,163),(0,0,0),(0,34,192),(0,86,175),(0,0,0),(0,0,0),(0,70,182),(0,0,195),(0,1,195),(0,0,0),(2,34,192),(0,2,195),(0,0,0),(0,0,0),(0,84,176),(0,28,193),(0,3,195),(0,0,0),(0,20,194),(1,20,194),(0,0,0),(0,0,0),(2,84,176),(0,4,195),(1,4,195),(0,0,0),(2,20,194),(3,107,163),(0,0,0),(0,0,0),(0,52,188),(1,52,188),(0,5,195),(0,0,0),(3,0,195),(0,82,177),(0,0,0),(0,0,0),(2,52,188),(4,128,147),(2,5,195),(0,0,0),(3,28,193),(0,6,195),(0,0,0),(0,0,0),(10,110,158),(8,47,188),(4,39,191),(0,0,0),(3,4,195),(0,62,185),(0,0,0),(0,0,0),(7,73,180),(8,115,156),(0,7,195),(0,0,0),(7,22,193),(0,21,194),(0,0,0),(0,0,0),(3,82,177),(0,40,191),(1,40,191),(0,0,0),(0,80,178),(1,80,178),(0,0,0),(0,0,0),(0,138,138),(0,8,195),(0,29,193),(0,0,0),(2,80,178),(4,2,195),(0,0,0),(0,0,0),(0,136,140),(1,136,140),(2,29,193),(0,0,0),(4,20,194),(3,7,195),(0,0,0),(0,0,0),(2,136,140),(0,56,187),(0,9,195),(0,0,0),(3,40,191),(13,134,134),(0,0,0),(0,0,0),(4,52,188),(0,68,183),(1,68,183),(0,0,0),(0,96,170),(1,96,170),(0,0,0),(0,0,0),(0,22,194),(1,22,194),(0,49,189),(0,0,0),(2,96,170),(0,10,195),(0,0,0),(0,0,0),(2,22,194),(12,76,175),(2,49,189),(0,0,0),(0,106,164),(1,106,164),(0,0,0),(0,0,0),(11,18,191),(6,105,164),(0,133,143),(0,0,0),(2,106,164),(4,21,194),(0,0,0),(0,0,0),(0,112,160),(1,112,160),(0,11,195),(0,0,0),(4,80,178),(0,30,193),(0,0,0),(0,0,0),(2,112,160),(0,53,188),(1,53,188),(0,0,0),(7,137,138),(2,30,193),(0,0,0),(0,0,0),(0,36,192),(1,36,192),(0,41,191),(0,0,0),(8,4,194),(0,23,194),(0,0,0),(0,0,0),(2,36,192),(0,12,195),(1,12,195),(0,0,0),(10,116,154),(2,23,194),(0,0,0),(0,0,0),(0,76,180),(0,124,151),(1,124,151),(0,0,0),(3,53,188),(10,91,170),(0,0,0),(0,0,0),(2,76,180),(2,124,151),(0,119,155),(0,0,0),(7,57,186),(0,115,158),(0,0,0),(0,0,0),(3,23,194),(7,37,191),(0,13,195),(0,0,0),(0,60,186),(0,89,174),(0,0,0),(0,0,0),(14,40,184),(0,85,176),(1,85,176),(0,0,0),(2,60,186),(2,89,174),(0,0,0),(0,0,0),(4,112,160),(2,85,176),(0,31,193),(0,0,0),(0,24,194),(1,24,194),(0,0,0),(0,0,0),(0,46,190),(1,46,190),(0,57,187),(0,0,0),(2,24,194),(0,14,195),(0,0,0),(0,0,0),(0,100,168),(1,100,168),(2,57,187),(0,0,0),(3,85,176),(2,14,195),(0,0,0),(0,0,0),(2,100,168),(0,37,192),(1,37,192),(0,0,0),(6,34,192),(0,74,181),(0,0,0),(0,0,0),(4,76,180),(2,37,192),(0,111,161),(0,0,0),(8,56,186),(0,42,191),(0,0,0),(0,0,0),(3,14,195),(6,28,193),(0,15,195),(0,0,0),(6,20,194),(2,42,191),(0,0,0),(0,0,0),(10,34,190),(5,106,164),(2,15,195),(0,0,0),(0,54,188),(0,25,194),(0,0,0),(0,0,0),(3,74,181),(4,85,176),(0,95,171),(0,0,0),(2,54,188),(2,25,194),(0,0,0),(0,0,0),(3,42,191),(0,32,193),(1,32,193),(0,0,0),(4,24,194),(0,114,159),(0,0,0),(0,0,0),(4,46,190),(0,16,195),(0,79,179),(0,0,0),(14,14,188),(2,114,159),(0,0,0),(0,0,0),(0,128,148),(1,128,148),(2,79,179),(0,0,0),(7,43,190),(0,102,167),(0,0,0),(0,0,0),(2,128,148),(4,37,192),(10,7,193),(0,0,0),(3,32,193),(2,102,167),(0,0,0),(0,0,0),(3,114,159),(6,8,195),(4,111,161),(0,0,0),(0,38,192),(0,47,190),(0,0,0),(0,0,0),(0,26,194),(1,26,194),(0,17,195),(0,0,0),(2,38,192),(0,61,186),(0,0,0),(0,0,0),(2,26,194),(0,64,185),(0,51,189),(0,0,0),(4,54,188),(2,61,186),(0,0,0),(0,0,0),(10,88,172),(0,77,180),(0,43,191),(0,0,0),(6,96,170),(0,58,187),(0,0,0),(0,0,0),(3,47,190),(2,77,180),(0,33,193),(0,0,0),(7,19,194),(2,58,187),(0,0,0),(0,0,0),(0,110,162),(0,67,184),(1,67,184),(0,0,0),(3,64,185),(0,18,195),(0,0,0),(0,0,0),(2,110,162),(2,67,184),(6,133,143),(0,0,0),(3,77,180),(0,121,154),(0,0,0),(0,0,0),(3,58,187),(7,107,163),(0,99,169),(0,0,0),(7,86,175),(0,27,194),(0,0,0),(0,0,0),(7,0,195),(0,55,188),(1,55,188),(0,0,0),(0,86,176),(1,86,176),(0,0,0),(0,0,0),(0,90,174),(0,136,141),(1,136,141),(0,0,0),(2,86,176),(4,61,186),(0,0,0),(0,0,0),(2,90,174),(0,39,192),(0,19,195),(0,0,0),(8,74,180),(0,70,183),(0,0,0),(0,0,0),(3,27,194),(0,92,173),(1,92,173),(0,0,0),(3,55,188),(2,70,183),(0,0,0),(0,0,0),(8,32,192),(2,92,173),(4,33,193),(0,0,0),(0,48,190),(0,34,193),(0,0,0),(0,0,0),(0,82,178),(1,82,178),(6,13,195),(0,0,0),(2,48,190),(2,34,193),(0,0,0),(0,0,0),(0,0,196),(0,1,196),(1,1,196),(0,0,0),(0,2,196),(1,2,196),(0,0,0),(0,0,0),(2,0,196),(0,3,196),(0,125,151),(0,0,0),(2,2,196),(4,27,194),(0,0,0),(0,0,0),(0,4,196),(1,4,196),(2,125,151),(0,0,0),(4,86,176),(5,26,194),(0,0,0),(0,0,0),(0,62,186),(0,5,196),(1,5,196),(0,0,0),(3,1,196),(10,14,193),(0,0,0),(0,0,0),(2,62,186),(0,132,145),(0,59,187),(0,0,0),(0,6,196),(0,73,182),(0,0,0),(0,0,0),(7,68,183),(0,96,171),(1,96,171),(0,0,0),(2,6,196),(0,106,165),(0,0,0),(0,0,0),(0,40,192),(0,7,196),(0,21,195),(0,0,0),(3,5,196),(2,106,165),(0,0,0),(0,0,0),(2,40,192),(2,7,196),(0,35,193),(0,0,0),(3,132,145),(0,29,194),(0,0,0),(0,0,0),(0,8,196),(1,8,196),(2,35,193),(0,0,0),(0,78,180),(1,78,180),(0,0,0),(0,0,0),(2,8,196),(4,3,196),(4,125,151),(0,0,0),(2,78,180),(3,21,195),(0,0,0),(0,0,0),(4,4,196),(0,9,196),(0,103,167),(0,0,0),(8,122,152),(0,49,190),(0,0,0),(0,0,0),(0,98,170),(1,98,170),(0,45,191),(0,0,0),(7,23,194),(0,22,195),(0,0,0),(0,0,0),(2,98,170),(4,132,145),(2,45,191),(0,0,0),(0,10,196),(1,10,196),(0,0,0),(0,0,0),(7,124,151),(4,96,171),(10,69,181),(0,0,0),(2,10,196),(3,103,167),(0,0,0),(0,0,0),(3,49,190),(4,7,196),(0,53,189),(0,0,0),(7,115,158),(3,45,191),(0,0,0),(0,0,0),(0,30,194),(0,11,196),(0,123,153),(0,0,0),(7,89,174),(4,29,194),(0,0,0),(0,0,0),(2,30,194),(0,36,193),(0,89,175),(0,0,0),(4,78,180),(6,58,187),(0,0,0),(0,0,0),(15,56,179),(2,36,193),(0,23,195),(0,0,0),(10,100,166),(0,91,174),(0,0,0),(0,0,0),(0,12,196),(0,100,169),(1,100,169),(0,0,0),(3,11,196),(0,63,186),(0,0,0),(0,0,0),(2,12,196),(0,60,187),(1,60,187),(0,0,0),(3,36,193),(0,83,178),(0,0,0),(0,0,0),(7,37,192),(2,60,187),(0,93,173),(0,0,0),(4,10,196),(0,66,185),(0,0,0),(0,0,0),(3,91,174),(0,13,196),(1,13,196),(0,0,0),(3,100,169),(2,66,185),(0,0,0),(0,0,0),(3,63,186),(0,57,188),(1,57,188),(0,0,0),(0,114,160),(0,31,194),(0,0,0),(0,0,0),(0,50,190),(0,24,195),(0,81,179),(0,0,0),(2,114,160),(2,31,194),(0,0,0),(0,0,0),(2,50,190),(0,95,172),(1,95,172),(0,0,0),(0,14,196),(1,14,196),(0,0,0),(0,0,0),(7,32,193),(0,69,184),(0,37,193),(0,0,0),(2,14,196),(4,91,174),(0,0,0),(0,0,0),(3,31,194),(2,69,184),(2,37,193),(0,0,0),(0,42,192),(0,127,150),(0,0,0),(0,0,0),(6,0,196),(4,60,187),(5,22,195),(0,0,0),(2,42,192),(0,54,189),(0,0,0),(0,0,0),(10,2,194),(0,15,196),(0,139,139),(0,0,0),(0,138,140),(1,138,140),(0,0,0),(0,0,0),(6,4,196),(2,15,196),(0,25,195),(0,0,0),(2,138,140),(0,117,158),(0,0,0),(0,0,0),(3,127,150),(4,57,188),(2,25,195),(0,0,0),(0,32,194),(1,32,194),(0,0,0),(0,0,0),(3,54,189),(4,24,195),(0,121,155),(0,0,0),(2,32,194),(0,110,163),(0,0,0),(0,0,0),(0,16,196),(0,72,183),(0,107,165),(0,0,0),(4,14,196),(0,126,151),(0,0,0),(0,0,0),(2,16,196),(2,72,183),(2,107,165),(0,0,0),(10,90,172),(2,126,151),(0,0,0),(0,0,0),(7,67,184),(8,124,151),(0,47,191),(0,0,0),(0,64,186),(0,38,193),(0,0,0),(0,0,0),(3,110,163),(13,20,190),(2,47,191),(0,0,0),(2,64,186),(0,26,195),(0,0,0),(0,0,0),(3,126,151),(0,17,196),(1,17,196),(0,0,0),(0,58,188),(1,58,188),(0,0,0),(0,0,0),(7,55,188),(0,43,192),(0,67,185),(0,0,0),(2,58,188),(3,47,191),(0,0,0),(0,0,0),(0,88,176),(1,88,176),(2,67,185),(0,0,0),(4,32,194),(0,33,194),(0,0,0),(0,0,0),(2,88,176),(0,125,152),(1,125,152),(0,0,0),(3,17,196),(2,33,194),(0,0,0),(0,0,0),(0,120,156),(0,116,159),(1,116,159),(0,0,0),(0,18,196),(1,18,196),(0,0,0),(0,0,0),(2,120,156),(2,116,159),(0,55,189),(0,0,0),(2,18,196),(0,75,182),(0,0,0),(0,0,0),(3,33,194),(5,42,192),(0,27,195),(0,0,0),(0,70,184),(1,70,184),(0,0,0),(0,0,0),(7,1,196),(6,36,193),(0,101,169),(0,0,0),(2,70,184),(0,82,179),(0,0,0),(0,0,0),(7,3,196),(4,17,196),(0,39,193),(0,0,0),(4,58,188),(2,82,179),(0,0,0),(0,0,0),(3,75,182),(0,19,196),(1,19,196),(0,0,0),(10,12,194),(3,27,195),(0,0,0),(0,0,0),(4,88,176),(0,48,191),(1,48,191),(0,0,0),(0,112,162),(1,112,162),(0,0,0),(0,0,0),(0,34,194),(1,34,194),(5,110,163),(0,0,0),(2,112,162),(3,39,193),(0,0,0),(0,0,0),(0,44,192),(1,44,192),(5,126,151),(0,0,0),(0,52,190),(1,52,190),(0,0,0),(0,0,0),(2,44,192),(0,0,197),(0,1,197),(0,0,0),(2,52,190),(0,2,197),(0,0,0),(0,0,0),(0,20,196),(1,20,196),(0,3,197),(0,0,0),(4,70,184),(0,65,186),(0,0,0),(0,0,0),(2,20,196),(0,4,197),(1,4,197),(0,0,0),(6,14,196),(2,65,186),(0,0,0),(0,0,0),(10,14,194),(0,103,168),(0,5,197),(0,0,0),(3,0,197),(3,1,197),(0,0,0),(0,0,0),(3,2,197),(2,103,168),(0,129,149),(0,0,0),(6,42,192),(0,6,197),(0,0,0),(0,0,0),(3,65,186),(0,40,193),(1,40,193),(0,0,0),(3,4,197),(2,6,197),(0,0,0),(0,0,0),(4,34,194),(0,21,196),(0,7,197),(0,0,0),(3,103,168),(0,35,194),(0,0,0),(0,0,0),(4,44,192),(2,21,196),(0,29,195),(0,0,0),(4,52,190),(2,35,194),(0,0,0),(0,0,0),(3,6,197),(0,8,197),(1,8,197),(0,0,0),(3,40,193),(4,2,197),(0,0,0),(0,0,0),(4,20,196),(2,8,197),(0,49,191),(0,0,0),(0,128,150),(1,128,150),(0,0,0),(0,0,0),(0,118,158),(0,45,192),(0,9,197),(0,0,0),(2,128,150),(3,29,195),(0,0,0),(0,0,0),(2,118,158),(0,71,184),(0,87,177),(0,0,0),(0,22,196),(1,22,196),(0,0,0),(0,0,0),(7,100,169),(2,71,184),(0,91,175),(0,0,0),(2,22,196),(0,10,197),(0,0,0),(0,0,0),(7,60,187),(4,40,193),(0,105,167),(0,0,0),(3,45,192),(0,114,161),(0,0,0),(0,0,0),(8,82,178),(0,139,140),(1,139,140),(0,0,0),(3,71,184),(0,30,195),(0,0,0),(0,0,0),(7,13,196),(2,139,140),(0,11,197),(0,0,0),(0,36,194),(0,137,142),(0,0,0),(0,0,0),(3,10,197),(4,8,197),(0,63,187),(0,0,0),(2,36,194),(2,137,142),(0,0,0),(0,0,0),(0,60,188),(0,23,196),(1,23,196),(0,0,0),(3,139,140),(10,43,190),(0,0,0),(0,0,0),(0,66,186),(0,12,197),(0,95,173),(0,0,0),(6,18,196),(3,11,197),(0,0,0),(0,0,0),(2,66,186),(0,81,180),(1,81,180),(0,0,0),(4,22,196),(0,74,183),(0,0,0),(0,0,0),(11,1,194),(2,81,180),(0,57,189),(0,0,0),(3,23,196),(2,74,183),(0,0,0),(0,0,0),(8,40,192),(0,121,156),(0,13,197),(0,0,0),(0,46,192),(0,50,191),(0,0,0),(0,0,0),(7,15,196),(2,121,156),(0,31,195),(0,0,0),(2,46,192),(2,50,191),(0,0,0),(0,0,0),(0,24,196),(0,97,172),(1,97,172),(0,0,0),(0,110,164),(1,110,164),(0,0,0),(0,0,0)]

def wits_39 : List (ℕ × ℕ × ℕ) := [(2,24,196),(2,97,172),(0,79,181),(0,0,0),(2,110,164),(0,14,197),(0,0,0),(0,0,0),(3,50,191),(4,23,196),(2,79,181),(0,0,0),(7,110,163),(0,42,193),(0,0,0),(0,0,0),(0,54,190),(1,54,190),(4,95,173),(0,0,0),(3,97,172),(2,42,193),(0,0,0),(0,0,0),(2,54,190),(4,81,180),(6,1,197),(0,0,0),(8,10,196),(3,79,181),(0,0,0),(0,0,0),(3,14,197),(0,132,147),(0,15,197),(0,0,0),(7,38,193),(6,65,186),(0,0,0),(0,0,0),(0,72,184),(0,25,196),(0,99,171),(0,0,0),(4,46,192),(4,50,191),(0,0,0),(0,0,0),(2,72,184),(0,32,195),(1,32,195),(0,0,0),(14,68,178),(0,77,182),(0,0,0),(0,0,0),(0,116,160),(1,116,160),(5,137,142),(0,0,0),(3,132,147),(2,77,182),(0,0,0),(0,0,0),(2,116,160),(0,16,197),(1,16,197),(0,0,0),(3,25,196),(3,99,171),(0,0,0),(0,0,0),(7,125,152),(0,47,192),(1,47,192),(0,0,0),(0,90,176),(1,90,176),(0,0,0),(0,0,0),(0,38,194),(1,38,194),(0,51,191),(0,0,0),(2,90,176),(0,58,189),(0,0,0),(0,0,0),(2,38,194),(0,92,175),(1,92,175),(0,0,0),(0,26,196),(1,26,196),(0,0,0),(0,0,0),(10,136,140),(0,84,179),(0,17,197),(0,0,0),(2,26,196),(0,101,170),(0,0,0),(0,0,0),(4,72,184),(2,84,179),(0,109,165),(0,0,0),(7,82,179),(2,101,170),(0,0,0),(0,0,0),(0,94,174),(0,112,163),(0,33,195),(0,0,0),(3,92,175),(4,77,182),(0,0,0),(0,0,0),(2,94,174),(2,112,163),(2,33,195),(0,0,0),(0,82,180),(0,55,190),(0,0,0),(0,0,0),(3,101,170),(4,16,197),(5,14,197),(0,0,0),(2,82,180),(0,18,197),(0,0,0),(0,0,0),(11,13,194),(4,47,192),(5,42,193),(0,0,0),(3,112,163),(0,129,150),(0,0,0),(0,0,0),(4,38,194),(0,27,196),(0,115,161),(0,0,0),(6,36,194),(2,129,150),(0,0,0),(0,0,0),(3,55,190),(2,27,196),(0,123,155),(0,0,0),(4,26,196),(0,39,194),(0,0,0),(0,0,0),(3,18,197),(0,80,181),(1,80,181),(0,0,0),(7,65,186),(2,39,194),(0,0,0),(0,0,0),(0,48,192),(1,48,192),(0,19,197),(0,0,0),(3,27,196),(3,115,161),(0,0,0),(0,0,0),(2,48,192),(4,112,163),(2,19,197),(0,0,0),(14,110,156),(0,34,195),(0,0,0),(0,0,0),(3,39,194),(0,44,193),(1,44,193),(0,0,0),(0,62,188),(1,62,188),(0,0,0),(0,0,0),(7,40,193),(2,44,193),(0,65,187),(0,0,0),(2,62,188),(3,19,197),(0,0,0),(0,0,0),(0,28,196),(1,28,196),(0,59,189),(0,0,0),(0,0,198),(0,1,198),(0,0,0),(0,0,0),(0,2,198),(0,20,197),(1,20,197),(0,0,0),(2,0,198),(0,3,198),(0,0,0),(0,0,0),(2,2,198),(0,111,164),(0,137,143),(0,0,0),(0,4,198),(1,4,198),(0,0,0),(0,0,0),(10,100,168),(2,111,164),(2,137,143),(0,0,0),(2,4,198),(0,5,198),(0,0,0),(0,0,0),(0,136,144),(0,127,152),(1,127,152),(0,0,0),(0,40,194),(1,40,194),(0,0,0),(0,0,0),(0,6,198),(0,100,171),(1,100,171),(0,0,0),(2,40,194),(3,137,143),(0,0,0),(0,0,0),(2,6,198),(0,105,168),(0,21,197),(0,0,0),(4,62,188),(0,7,198),(0,0,0),(0,0,0),(3,5,198),(0,29,196),(1,29,196),(0,0,0),(3,127,152),(2,7,198),(0,0,0),(0,0,0),(4,28,196),(0,49,192),(0,71,185),(0,0,0),(0,8,198),(1,8,198),(0,0,0),(0,0,0),(0,134,146),(1,134,146),(0,45,193),(0,0,0),(2,8,198),(3,21,197),(0,0,0),(0,0,0),(2,134,146),(4,111,164),(2,45,193),(0,0,0),(3,29,196),(0,9,198),(0,0,0),(0,0,0),(7,23,196),(0,83,180),(0,53,191),(0,0,0),(3,49,192),(0,22,197),(0,0,0),(0,0,0),(4,136,144),(2,83,180),(0,133,147),(0,0,0),(4,40,194),(0,95,174),(0,0,0),(0,0,0),(0,10,198),(1,10,198),(2,133,147),(0,0,0),(6,26,196),(2,95,174),(0,0,0),(0,0,0),(2,10,198),(0,63,188),(1,63,188),(0,0,0),(0,30,196),(0,41,194),(0,0,0),(0,0,0),(3,22,197),(0,36,195),(0,81,181),(0,0,0),(2,30,196),(0,11,198),(0,0,0),(0,0,0),(0,132,148),(1,132,148),(2,81,181),(0,0,0),(0,74,184),(1,74,184),(0,0,0),(0,0,0),(2,132,148),(8,4,197),(0,23,197),(0,0,0),(2,74,184),(0,125,154),(0,0,0),(0,0,0),(3,41,194),(5,4,198),(2,23,197),(0,0,0),(0,12,198),(0,57,190),(0,0,0),(0,0,0),(3,11,198),(4,83,180),(4,53,191),(0,0,0),(2,12,198),(0,69,186),(0,0,0),(0,0,0),(11,2,195),(5,40,194),(0,131,149),(0,0,0),(0,50,192),(0,46,193),(0,0,0),(0,0,0),(3,125,154),(8,21,196),(2,131,149),(0,0,0),(2,50,192),(0,13,198),(0,0,0),(0,0,0),(3,57,190),(0,31,196),(1,31,196),(0,0,0),(4,30,196),(2,13,198),(0,0,0),(0,0,0),(3,69,186),(0,24,197),(1,24,197),(0,0,0),(14,88,170),(3,131,149),(0,0,0),(0,0,0),(3,46,193),(2,24,197),(0,37,195),(0,0,0),(4,74,184),(0,54,191),(0,0,0),(0,0,0),(0,14,198),(0,124,155),(1,124,155),(0,0,0),(3,31,196),(2,54,191),(0,0,0),(0,0,0),(2,14,198),(0,72,185),(1,72,185),(0,0,0),(3,24,197),(4,57,190),(0,0,0),(0,0,0),(6,28,196),(2,72,185),(0,77,183),(0,0,0),(6,0,198),(3,37,195),(0,0,0),(0,0,0),(3,54,191),(6,20,197),(2,77,183),(0,0,0),(0,88,178),(0,15,198),(0,0,0),(0,0,0),(7,92,175),(6,111,164),(0,25,197),(0,0,0),(2,88,178),(0,86,179),(0,0,0),(0,0,0),(0,32,196),(1,32,196),(0,61,189),(0,0,0),(7,101,170),(2,86,179),(0,0,0),(0,0,0),(2,32,196),(4,24,197),(2,61,189),(0,0,0),(6,40,194),(5,132,148),(0,0,0),(0,0,0),(0,84,180),(1,84,180),(0,47,193),(0,0,0),(0,16,198),(0,94,175),(0,0,0),(0,0,0),(0,58,190),(0,51,192),(1,51,192),(0,0,0),(2,16,198),(0,38,195),(0,0,0),(0,0,0),(2,58,190),(2,51,192),(5,57,190),(0,0,0),(7,18,197),(2,38,195),(0,0,0),(0,0,0),(10,8,196),(0,75,184),(1,75,184),(0,0,0),(6,8,198),(0,26,197),(0,0,0),(0,0,0),(0,128,152),(1,128,152),(5,46,193),(0,0,0),(0,96,174),(0,17,198),(0,0,0),(0,0,0),(0,70,186),(1,70,186),(4,25,197),(0,0,0),(2,96,174),(2,17,198),(0,0,0),(0,0,0),(2,70,186),(0,33,196),(0,55,191),(0,0,0),(3,75,184),(0,103,170),(0,0,0),(0,0,0),(3,26,197),(2,33,196),(2,55,191),(0,0,0),(10,10,196),(2,103,170),(0,0,0),(0,0,0),(3,17,198),(0,136,145),(1,136,145),(0,0,0),(0,80,182),(1,80,182),(0,0,0),(0,0,0),(0,18,198),(1,18,198),(10,53,189),(0,0,0),(2,80,182),(0,98,173),(0,0,0),(0,0,0),(2,18,198),(6,36,195),(0,27,197),(0,0,0),(16,10,188),(0,135,146),(0,0,0),(0,0,0),(6,132,148),(4,75,184),(0,39,195),(0,0,0),(3,136,145),(2,135,146),(0,0,0),(0,0,0),(4,128,152),(0,48,193),(0,73,185),(0,0,0),(4,96,174),(4,17,198),(0,0,0),(0,0,0),(3,98,173),(2,48,193),(2,73,185),(0,0,0),(6,12,198),(0,19,198),(0,0,0),(0,0,0),(0,52,192),(0,65,188),(1,65,188),(0,0,0),(0,34,196),(0,78,183),(0,0,0),(0,0,0),(2,52,192),(2,65,188),(6,131,149),(0,0,0),(2,34,196),(0,59,190),(0,0,0),(0,0,0),(0,100,172),(1,100,172),(0,105,169),(0,0,0),(4,80,182),(2,59,190),(0,0,0),(0,0,0),(0,126,154),(0,28,197),(1,28,197),(0,0,0),(3,65,188),(4,98,173),(0,0,0),(0,0,0),(2,126,154),(0,0,199),(0,1,199),(0,0,0),(0,20,198),(0,2,199),(0,0,0),(0,0,0),(3,59,190),(2,0,199),(0,3,199),(0,0,0),(2,20,198),(2,2,199),(0,0,0),(0,0,0),(6,14,198),(0,4,199),(1,4,199),(0,0,0),(3,28,197),(5,70,186),(0,0,0),(0,0,0),(8,94,174),(0,40,195),(0,5,199),(0,0,0),(3,0,199),(3,1,199),(0,0,0),(0,0,0),(0,76,184),(1,76,184),(2,5,199),(0,0,0),(4,34,196),(0,6,199),(0,0,0),(0,0,0),(2,76,184),(0,35,196),(1,35,196),(0,0,0),(3,4,199),(0,21,198),(0,0,0),(0,0,0),(4,100,172),(2,35,196),(0,7,199),(0,0,0),(3,40,195),(2,21,198),(0,0,0),(0,0,0),(0,110,166),(1,110,166),(2,7,199),(0,0,0),(7,41,194),(0,45,194),(0,0,0),(0,0,0),(2,110,166),(0,8,199),(1,8,199),(0,0,0),(3,35,196),(2,45,194),(0,0,0),(0,0,0),(3,21,198),(0,53,192),(1,53,192),(0,0,0),(6,16,198),(3,7,199),(0,0,0),(0,0,0),(6,58,190),(0,120,159),(0,9,199),(0,0,0),(7,125,154),(0,81,182),(0,0,0),(0,0,0),(0,22,198),(1,22,198),(0,63,189),(0,0,0),(3,8,199),(2,81,182),(0,0,0),(0,0,0),(2,22,198),(5,34,196),(2,63,189),(0,0,0),(0,60,190),(0,10,199),(0,0,0),(0,0,0),(6,128,152),(4,35,196),(0,41,195),(0,0,0),(2,60,190),(0,30,197),(0,0,0),(0,0,0),(0,36,196),(1,36,196),(2,41,195),(0,0,0),(0,104,170),(1,104,170),(0,0,0),(0,0,0),(2,36,196),(6,33,196),(0,11,199),(0,0,0),(2,104,170),(4,45,194),(0,0,0),(0,0,0),(3,10,199),(4,8,199),(0,57,191),(0,0,0),(8,4,198),(0,23,198),(0,0,0),(0,0,0),(3,30,197),(4,53,192),(2,57,191),(0,0,0),(6,80,182),(2,23,198),(0,0,0),(0,0,0),(6,18,198),(0,12,199),(1,12,199),(0,0,0),(8,40,194),(0,50,193),(0,0,0),(0,0,0),(0,46,194),(1,46,194),(4,63,189),(0,0,0),(10,70,184),(2,50,193),(0,0,0),(0,0,0),(2,46,194),(0,119,160),(0,141,141),(0,0,0),(0,140,142),(1,140,142),(0,0,0),(0,0,0),(14,68,180),(0,112,165),(0,13,199),(0,0,0),(2,140,142),(4,30,197),(0,0,0),(0,0,0),(3,50,193),(2,112,165),(0,123,157),(0,0,0),(0,24,198),(1,24,198),(0,0,0),(0,0,0),(0,90,178),(0,37,196),(1,37,196),(0,0,0),(2,24,198),(0,42,195),(0,0,0),(0,0,0),(2,90,178),(0,92,177),(0,115,163),(0,0,0),(0,86,180),(0,14,199),(0,0,0),(0,0,0),(6,100,172),(2,92,177),(2,115,163),(0,0,0),(2,86,180),(2,14,199),(0,0,0),(0,0,0),(6,126,154),(4,12,199),(5,81,182),(0,0,0),(0,94,176),(1,94,176),(0,0,0),(0,0,0),(3,42,195),(0,64,189),(1,64,189),(0,0,0),(2,94,176),(0,61,190),(0,0,0),(0,0,0),(3,14,199),(2,64,189),(0,15,199),(0,0,0),(4,140,142),(0,25,198),(0,0,0),(0,0,0),(11,49,190),(0,32,197),(0,135,147),(0,0,0),(7,17,198),(2,25,198),(0,0,0),(0,0,0),(8,132,148),(0,96,175),(1,96,175),(0,0,0),(3,64,189),(0,47,194),(0,0,0),(0,0,0),(0,82,182),(1,82,182),(0,51,193),(0,0,0),(7,103,170),(2,47,194),(0,0,0),(0,0,0),(2,82,182),(0,16,199),(1,16,199),(0,0,0),(0,38,196),(1,38,196),(0,0,0),(0,0,0),(7,136,145),(2,16,199),(6,7,199),(0,0,0),(2,38,196),(0,70,187),(0,0,0),(0,0,0),(3,47,194),(10,8,197),(0,43,195),(0,0,0),(4,94,176),(0,111,166),(0,0,0),(0,0,0),(0,26,198),(1,26,198),(2,43,195),(0,0,0),(3,16,199),(2,111,166),(0,0,0),(0,0,0),(0,108,168),(0,55,192),(0,17,199),(0,0,0),(0,114,164),(1,114,164),(0,0,0),(0,0,0),(2,108,168),(2,55,192),(0,33,197),(0,0,0),(2,114,164),(0,126,155),(0,0,0),(0,0,0),(3,111,166),(4,96,175),(2,33,197),(0,0,0),(7,19,198),(2,126,155),(0,0,0),(0,0,0),(4,82,182),(8,124,155),(4,51,193),(0,0,0),(3,55,192),(3,17,199),(0,0,0),(0,0,0),(15,8,191),(4,16,199),(0,121,159),(0,0,0),(0,132,150),(0,18,199),(0,0,0),(0,0,0),(3,126,155),(0,100,173),(1,100,173),(0,0,0),(2,132,150),(0,27,198),(0,0,0),(0,0,0),(7,28,197),(0,39,196),(1,39,196),(0,0,0),(0,48,194),(1,48,194),(0,0,0),(0,0,0),(0,62,190),(1,62,190),(0,65,189),(0,0,0),(2,48,194),(3,121,159),(0,0,0),(0,0,0),(2,62,190),(0,52,193),(1,52,193),(0,0,0),(3,100,173),(17,112,150),(0,0,0),(0,0,0),(3,27,198),(0,44,195),(0,19,199),(0,0,0),(3,39,196),(0,34,197),(0,0,0),(0,0,0),(0,68,188),(0,87,180),(1,87,180),(0,0,0),(8,16,198),(2,34,197),(0,0,0),(0,0,0),(2,68,188),(2,87,180),(0,93,177),(0,0,0),(3,52,193),(8,38,195),(0,0,0),(0,0,0),(7,35,196),(5,38,196),(0,85,181),(0,0,0),(0,28,198),(0,110,167),(0,0,0),(0,0,0),(3,34,197),(4,100,173),(0,113,165),(0,0,0),(2,28,198),(2,110,167),(0,0,0),(0,0,0)]

def wits_40 : List (ℕ × ℕ × ℕ) := [(0,0,200),(0,1,200),(1,1,200),(0,0,0),(0,2,200),(1,2,200),(0,0,0),(0,0,0),(2,0,200),(0,3,200),(0,71,187),(0,0,0),(2,2,200),(0,83,182),(0,0,0),(0,0,0),(0,4,200),(1,4,200),(2,71,187),(0,0,0),(19,20,181),(2,83,182),(0,0,0),(0,0,0),(2,4,200),(0,5,200),(1,5,200),(0,0,0),(3,1,200),(4,34,197),(0,0,0),(0,0,0),(4,68,188),(2,5,200),(0,35,197),(0,0,0),(0,6,200),(0,49,194),(0,0,0),(0,0,0),(3,83,182),(10,25,196),(0,21,199),(0,0,0),(2,6,200),(0,29,198),(0,0,0),(0,0,0),(23,91,140),(0,7,200),(0,45,195),(0,0,0),(3,5,200),(2,29,198),(0,0,0),(0,0,0),(10,116,160),(0,104,171),(0,53,193),(0,0,0),(11,125,152),(3,35,197),(0,0,0),(0,0,0),(0,8,200),(1,8,200),(2,53,193),(0,0,0),(4,2,200),(0,63,190),(0,0,0),(0,0,0),(0,74,186),(1,74,186),(4,71,187),(0,0,0),(3,7,200),(0,66,189),(0,0,0),(0,0,0),(2,74,186),(0,9,200),(0,119,161),(0,0,0),(3,104,171),(0,22,199),(0,0,0),(0,0,0),(7,12,199),(2,9,200),(2,119,161),(0,0,0),(7,50,193),(0,123,158),(0,0,0),(0,0,0),(3,63,190),(0,41,196),(1,41,196),(0,0,0),(0,10,200),(1,10,200),(0,0,0),(0,0,0),(0,30,198),(0,36,197),(1,36,197),(0,0,0),(2,10,200),(3,119,161),(0,0,0),(0,0,0),(2,30,198),(0,57,192),(1,57,192),(0,0,0),(8,20,198),(6,126,155),(0,0,0),(0,0,0),(3,123,158),(0,11,200),(1,11,200),(0,0,0),(3,41,196),(5,0,200),(0,0,0),(0,0,0),(4,8,200),(0,135,148),(0,23,199),(0,0,0),(3,36,197),(4,63,190),(0,0,0),(0,0,0),(0,50,194),(1,50,194),(2,23,199),(0,0,0),(3,57,192),(0,46,195),(0,0,0),(0,0,0),(0,12,200),(1,12,200),(4,119,161),(0,0,0),(0,92,178),(1,92,178),(0,0,0),(0,0,0),(2,12,200),(0,72,187),(0,77,185),(0,0,0),(2,92,178),(0,86,181),(0,0,0),(0,0,0),(6,62,190),(2,72,187),(2,77,185),(0,0,0),(4,10,200),(0,31,198),(0,0,0),(0,0,0),(0,118,162),(0,13,200),(1,13,200),(0,0,0),(7,25,198),(2,31,198),(0,0,0),(0,0,0),(2,118,162),(0,24,199),(0,37,197),(0,0,0),(0,42,196),(1,42,196),(0,0,0),(0,0,0),(3,86,181),(2,24,199),(2,37,197),(0,0,0),(2,42,196),(0,133,150),(0,0,0),(0,0,0),(0,96,176),(0,103,172),(1,103,172),(0,0,0),(0,14,200),(1,14,200),(0,0,0),(0,0,0),(2,96,176),(2,103,172),(0,61,191),(0,0,0),(2,14,200),(3,37,197),(0,0,0),(0,0,0),(4,12,200),(10,20,197),(0,67,189),(0,0,0),(0,126,156),(0,82,183),(0,0,0),(0,0,0),(3,133,150),(4,72,187),(2,67,189),(0,0,0),(2,126,156),(0,75,186),(0,0,0),(0,0,0),(8,36,196),(0,15,200),(0,25,199),(0,0,0),(0,32,198),(0,98,175),(0,0,0),(0,0,0),(4,118,162),(2,15,200),(0,47,195),(0,0,0),(2,32,198),(0,51,194),(0,0,0),(0,0,0),(3,82,183),(0,121,160),(1,121,160),(0,0,0),(0,70,188),(1,70,188),(0,0,0),(0,0,0),(3,75,186),(2,121,160),(6,35,197),(0,0,0),(2,70,188),(0,38,197),(0,0,0),(0,0,0),(0,16,200),(1,16,200),(0,117,163),(0,0,0),(4,14,200),(2,38,197),(0,0,0),(0,0,0),(2,16,200),(0,43,196),(0,105,171),(0,0,0),(3,121,160),(5,12,200),(0,0,0),(0,0,0),(7,100,173),(2,43,196),(0,55,193),(0,0,0),(0,100,174),(0,26,199),(0,0,0),(0,0,0),(3,38,197),(8,112,165),(2,55,193),(0,0,0),(2,100,174),(2,26,199),(0,0,0),(0,0,0),(6,74,186),(0,17,200),(1,17,200),(0,0,0),(3,43,196),(0,33,198),(0,0,0),(0,0,0),(7,52,193),(2,17,200),(0,73,187),(0,0,0),(14,100,166),(2,33,198),(0,0,0),(0,0,0),(3,26,199),(4,121,160),(2,73,187),(0,0,0),(4,70,188),(0,78,185),(0,0,0),(0,0,0),(7,87,180),(6,41,196),(5,133,150),(0,0,0),(3,17,200),(2,78,185),(0,0,0),(0,0,0),(3,33,198),(0,89,180),(0,91,179),(0,0,0),(0,18,200),(0,62,191),(0,0,0),(0,0,0),(0,142,142),(0,48,195),(0,27,199),(0,0,0),(2,18,200),(0,93,178),(0,0,0),(0,0,0),(0,140,144),(1,140,144),(2,27,199),(0,0,0),(0,52,194),(1,52,194),(0,0,0),(0,0,0),(2,140,144),(0,59,192),(0,139,145),(0,0,0),(2,52,194),(0,85,182),(0,0,0),(0,0,0),(0,44,196),(1,44,196),(0,95,177),(0,0,0),(3,48,195),(0,129,154),(0,0,0),(0,0,0),(0,34,198),(0,19,200),(1,19,200),(0,0,0),(6,92,178),(2,129,154),(0,0,0),(0,0,0),(2,34,198),(2,19,200),(6,77,185),(0,0,0),(0,76,186),(1,76,186),(0,0,0),(0,0,0),(3,85,182),(7,35,197),(0,83,183),(0,0,0),(2,76,186),(3,95,177),(0,0,0),(0,0,0),(3,129,154),(0,28,199),(1,28,199),(0,0,0),(3,19,200),(4,62,191),(0,0,0),(0,0,0),(4,142,142),(2,28,199),(4,27,199),(0,0,0),(6,42,196),(4,93,178),(0,0,0),(0,0,0),(0,20,200),(0,0,201),(0,1,201),(0,0,0),(4,52,194),(0,2,201),(0,0,0),(0,0,0),(2,20,200),(0,40,197),(0,3,201),(0,0,0),(3,28,199),(2,2,201),(0,0,0),(0,0,0),(4,44,196),(0,4,201),(1,4,201),(0,0,0),(7,66,189),(4,129,154),(0,0,0),(0,0,0),(4,34,198),(2,4,201),(0,5,201),(0,0,0),(3,0,201),(0,35,198),(0,0,0),(0,0,0),(3,2,201),(0,112,167),(1,112,167),(0,0,0),(3,40,197),(0,6,201),(0,0,0),(0,0,0),(7,41,196),(0,21,200),(0,29,199),(0,0,0),(3,4,201),(0,53,194),(0,0,0),(0,0,0),(7,36,197),(2,21,200),(0,7,201),(0,0,0),(8,48,194),(2,53,194),(0,0,0),(0,0,0),(0,66,190),(1,66,190),(2,7,201),(0,0,0),(3,112,167),(5,140,144),(0,0,0),(0,0,0),(0,60,192),(0,8,201),(0,79,185),(0,0,0),(3,21,200),(3,29,199),(0,0,0),(0,0,0),(2,60,192),(2,8,201),(2,79,185),(0,0,0),(11,27,196),(0,101,174),(0,0,0),(0,0,0),(8,68,188),(4,4,201),(0,9,201),(0,0,0),(0,22,200),(1,22,200),(0,0,0),(0,0,0),(10,128,152),(14,49,188),(0,41,197),(0,0,0),(2,22,200),(0,118,163),(0,0,0),(0,0,0),(7,72,187),(4,112,167),(0,57,193),(0,0,0),(0,36,198),(0,10,201),(0,0,0),(0,0,0),(3,101,174),(0,88,181),(1,88,181),(0,0,0),(2,36,198),(2,10,201),(0,0,0),(0,0,0),(7,13,200),(2,88,181),(4,7,201),(0,0,0),(8,2,200),(3,41,197),(0,0,0),(0,0,0),(0,86,182),(1,86,182),(0,11,201),(0,0,0),(10,80,182),(0,50,195),(0,0,0),(0,0,0),(0,72,188),(0,23,200),(1,23,200),(0,0,0),(0,46,196),(1,46,196),(0,0,0),(0,0,0),(2,72,188),(2,23,200),(0,103,173),(0,0,0),(2,46,196),(4,101,174),(0,0,0),(0,0,0),(6,142,142),(0,12,201),(1,12,201),(0,0,0),(4,22,200),(3,11,201),(0,0,0),(0,0,0),(0,54,194),(1,54,194),(4,41,197),(0,0,0),(3,23,200),(4,118,163),(0,0,0),(0,0,0),(2,54,194),(6,59,192),(0,31,199),(0,0,0),(0,108,170),(1,108,170),(0,0,0),(0,0,0),(6,44,196),(4,88,181),(0,13,201),(0,0,0),(2,108,170),(0,37,198),(0,0,0),(0,0,0),(0,24,200),(0,64,191),(1,64,191),(0,0,0),(0,82,184),(1,82,184),(0,0,0),(0,0,0),(2,24,200),(0,61,192),(1,61,192),(0,0,0),(2,82,184),(0,67,190),(0,0,0),(0,0,0),(4,72,188),(2,61,192),(0,75,187),(0,0,0),(4,46,196),(0,14,201),(0,0,0),(0,0,0),(3,37,198),(6,28,199),(2,75,187),(0,0,0),(3,64,191),(2,14,201),(0,0,0),(0,0,0),(7,43,196),(0,105,172),(1,105,172),(0,0,0),(3,61,192),(0,58,193),(0,0,0),(0,0,0),(0,130,154),(0,141,144),(1,141,144),(0,0,0),(7,26,199),(0,70,189),(0,0,0),(0,0,0),(2,130,154),(0,25,200),(0,15,201),(0,0,0),(4,108,170),(2,70,189),(0,0,0),(0,0,0),(7,17,200),(2,25,200),(2,15,201),(0,0,0),(3,105,172),(0,139,146),(0,0,0),(0,0,0),(3,58,193),(4,64,191),(6,5,201),(0,0,0),(0,120,162),(1,120,162),(0,0,0),(0,0,0),(0,38,198),(1,38,198),(5,50,195),(0,0,0),(2,120,162),(0,138,147),(0,0,0),(0,0,0),(2,38,198),(0,16,201),(0,43,197),(0,0,0),(8,92,178),(0,55,194),(0,0,0),(0,0,0),(3,139,146),(2,16,201),(0,129,155),(0,0,0),(7,62,191),(2,55,194),(0,0,0),(0,0,0),(6,66,190),(0,73,188),(1,73,188),(0,0,0),(0,26,200),(1,26,200),(0,0,0),(0,0,0),(0,78,186),(0,91,180),(0,89,181),(0,0,0),(2,26,200),(3,43,197),(0,0,0),(0,0,0),(2,78,186),(2,91,180),(0,17,201),(0,0,0),(7,85,182),(0,87,182),(0,0,0),(0,0,0),(11,46,193),(0,136,149),(1,136,149),(0,0,0),(3,73,188),(2,87,182),(0,0,0),(0,0,0),(7,19,200),(2,136,149),(0,65,191),(0,0,0),(0,62,192),(0,95,178),(0,0,0),(0,0,0),(4,38,198),(13,10,196),(0,85,183),(0,0,0),(2,62,192),(2,95,178),(0,0,0),(0,0,0),(0,48,196),(1,48,196),(2,85,183),(0,0,0),(0,68,190),(0,18,201),(0,0,0),(0,0,0),(2,48,196),(0,27,200),(0,59,193),(0,0,0),(2,68,190),(2,18,201),(0,0,0),(0,0,0),(3,95,178),(2,27,200),(0,97,177),(0,0,0),(4,26,200),(3,85,183),(0,0,0),(0,0,0),(4,78,186),(0,44,197),(1,44,197),(0,0,0),(6,46,196),(8,51,194),(0,0,0),(0,0,0),(3,18,201),(2,44,197),(4,17,201),(0,0,0),(3,27,200),(0,34,199),(0,0,0),(0,0,0),(7,4,201),(4,136,149),(0,19,201),(0,0,0),(10,140,142),(2,34,199),(0,0,0),(0,0,0),(0,112,168),(1,112,168),(2,19,201),(0,0,0),(0,56,194),(1,56,194),(0,0,0),(0,0,0),(2,112,168),(0,99,176),(0,127,157),(0,0,0),(2,56,194),(0,109,170),(0,0,0),(0,0,0),(0,28,200),(1,28,200),(0,81,185),(0,0,0),(4,68,190),(2,109,170),(0,0,0),(0,0,0),(2,28,200),(0,133,152),(1,133,152),(0,0,0),(6,82,184),(10,14,199),(0,0,0),(0,0,0),(11,38,195),(0,20,201),(1,20,201),(0,0,0),(0,0,202),(0,1,202),(0,0,0),(0,0,0),(0,2,202),(1,2,202),(6,75,187),(0,0,0),(2,0,202),(0,3,202),(0,0,0),(0,0,0),(2,2,202),(0,49,196),(1,49,196),(0,0,0),(0,4,202),(1,4,202),(0,0,0),(0,0,0),(11,17,198),(2,49,196),(0,35,199),(0,0,0),(2,4,202),(0,5,202),(0,0,0),(0,0,0),(3,1,202),(0,63,192),(0,45,197),(0,0,0),(4,56,194),(0,66,191),(0,0,0),(0,0,0),(0,6,202),(0,29,200),(0,21,201),(0,0,0),(3,49,196),(2,66,191),(0,0,0),(0,0,0),(2,6,202),(0,60,193),(1,60,193),(0,0,0),(8,52,194),(0,7,202),(0,0,0),(0,0,0),(3,5,202),(2,60,193),(8,139,145),(0,0,0),(3,63,192),(0,69,190),(0,0,0),(0,0,0),(0,92,180),(1,92,180),(8,95,177),(0,0,0),(0,8,202),(1,8,202),(0,0,0),(0,0,0),(2,92,180),(6,16,201),(6,43,197),(0,0,0),(2,8,202),(0,94,179),(0,0,0),(0,0,0),(3,7,202),(4,49,196),(0,111,169),(0,0,0),(4,4,202),(0,9,202),(0,0,0),(0,0,0),(3,69,190),(6,73,188),(2,111,169),(0,0,0),(6,26,200),(2,9,202),(0,0,0),(0,0,0),(6,78,186),(0,36,199),(0,77,187),(0,0,0),(0,30,200),(1,30,200),(0,0,0),(0,0,0),(0,10,202),(0,72,189),(0,125,159),(0,0,0),(2,30,200),(3,111,169),(0,0,0),(0,0,0),(0,84,184),(1,84,184),(0,117,165),(0,0,0),(0,50,196),(1,50,196),(0,0,0),(0,0,0),(2,84,184),(8,40,197),(2,117,165),(0,0,0),(2,50,196),(0,11,202),(0,0,0),(0,0,0),(4,92,180),(5,0,202),(0,23,201),(0,0,0),(3,72,189),(0,98,177),(0,0,0),(0,0,0),(6,48,196),(7,75,187),(2,23,201),(0,0,0),(6,68,190),(0,54,195),(0,0,0),(0,0,0),(10,62,190),(5,4,202),(4,111,169),(0,0,0),(0,12,202),(0,82,185),(0,0,0),(0,0,0),(3,11,202),(8,21,200),(0,105,173),(0,0,0),(2,12,202),(2,82,185),(0,0,0),(0,0,0),(0,64,192),(0,31,200),(1,31,200),(0,0,0),(4,30,200),(5,6,202),(0,0,0),(0,0,0),(0,42,198),(0,75,188),(0,37,199),(0,0,0),(11,35,196),(0,13,202),(0,0,0),(0,0,0),(0,100,176),(0,24,201),(1,24,201),(0,0,0),(4,50,196),(2,13,202),(0,0,0),(0,0,0),(2,100,176),(2,24,201),(5,69,190),(0,0,0),(3,31,200),(4,11,202),(0,0,0),(0,0,0),(11,45,194),(0,113,168),(1,113,168),(0,0,0),(0,80,186),(1,80,186),(0,0,0),(0,0,0)]

def wits_41 : List (ℕ × ℕ × ℕ) := [(0,14,202),(1,14,202),(5,94,179),(0,0,0),(2,80,186),(4,54,195),(0,0,0),(0,0,0),(2,14,202),(6,133,152),(5,9,202),(0,0,0),(0,116,166),(1,116,166),(0,0,0),(0,0,0),(7,73,188),(0,51,196),(0,47,197),(0,0,0),(2,116,166),(6,1,202),(0,0,0),(0,0,0),(0,32,200),(1,32,200),(0,25,201),(0,0,0),(31,1,106),(0,15,202),(0,0,0),(0,0,0),(2,32,200),(0,107,172),(1,107,172),(0,0,0),(6,4,202),(2,15,202),(0,0,0),(0,0,0),(4,100,176),(2,107,172),(0,91,181),(0,0,0),(3,51,196),(0,38,199),(0,0,0),(0,0,0),(15,52,187),(0,93,180),(0,55,195),(0,0,0),(7,95,178),(0,43,198),(0,0,0),(0,0,0),(3,15,202),(0,119,164),(0,87,183),(0,0,0),(0,16,202),(1,16,202),(0,0,0),(0,0,0),(4,14,202),(2,119,164),(0,95,179),(0,0,0),(2,16,202),(3,91,181),(0,0,0),(0,0,0),(3,38,199),(5,12,202),(2,95,179),(0,0,0),(3,93,180),(0,26,201),(0,0,0),(0,0,0),(3,43,198),(0,85,184),(1,85,184),(0,0,0),(3,119,164),(2,26,201),(0,0,0),(0,0,0),(4,32,200),(0,33,200),(1,33,200),(0,0,0),(0,104,174),(0,17,202),(0,0,0),(0,0,0),(16,30,190),(2,33,200),(0,133,153),(0,0,0),(2,104,174),(2,17,202),(0,0,0),(0,0,0),(3,26,201),(0,68,191),(1,68,191),(0,0,0),(3,85,184),(4,38,199),(0,0,0),(0,0,0),(18,84,168),(0,48,197),(0,83,185),(0,0,0),(3,33,200),(0,59,194),(0,0,0),(0,0,0),(0,52,196),(1,52,196),(0,39,199),(0,0,0),(4,16,202),(2,59,194),(0,0,0),(0,0,0),(0,18,202),(1,18,202),(0,27,201),(0,0,0),(3,68,191),(8,70,189),(0,0,0),(0,0,0),(2,18,202),(5,116,166),(2,27,201),(0,0,0),(0,44,198),(0,71,190),(0,0,0),(0,0,0),(3,59,194),(4,85,184),(6,23,201),(0,0,0),(2,44,198),(0,118,165),(0,0,0),(0,0,0),(11,61,190),(4,33,200),(5,15,202),(0,0,0),(0,34,200),(0,81,186),(0,0,0),(0,0,0),(7,49,196),(0,56,195),(1,56,195),(0,0,0),(2,34,200),(0,19,202),(0,0,0),(0,0,0),(3,71,190),(2,56,195),(5,38,199),(0,0,0),(7,5,202),(2,19,202),(0,0,0),(0,0,0),(3,118,165),(0,101,176),(1,101,176),(0,0,0),(7,66,191),(4,59,194),(0,0,0),(0,0,0),(3,81,186),(0,28,201),(0,131,155),(0,0,0),(3,56,195),(0,142,145),(0,0,0),(0,0,0),(3,19,202),(2,28,201),(2,131,155),(0,0,0),(7,7,202),(0,74,189),(0,0,0),(0,0,0),(11,70,187),(0,40,199),(1,40,199),(0,0,0),(0,20,202),(1,20,202),(0,0,0),(0,0,0),(11,111,166),(0,0,203),(0,1,203),(0,0,0),(2,20,202),(0,2,203),(0,0,0),(0,0,0),(3,142,145),(2,0,203),(0,3,203),(0,0,0),(0,66,192),(0,111,170),(0,0,0),(0,0,0),(0,90,182),(0,4,203),(1,4,203),(0,0,0),(2,66,192),(0,45,198),(0,0,0),(0,0,0),(2,90,182),(0,88,183),(0,5,203),(0,0,0),(0,60,194),(1,60,194),(0,0,0),(0,0,0),(3,2,203),(2,88,183),(0,29,201),(0,0,0),(2,60,194),(0,6,203),(0,0,0),(0,0,0),(0,108,172),(1,108,172),(2,29,201),(0,0,0),(0,86,184),(1,86,184),(0,0,0),(0,0,0),(2,108,172),(0,96,179),(0,7,203),(0,0,0),(2,86,184),(3,5,203),(0,0,0),(0,0,0),(11,27,198),(2,96,179),(2,7,203),(0,0,0),(4,20,202),(0,137,150),(0,0,0),(0,0,0),(3,6,203),(0,8,203),(0,57,195),(0,0,0),(6,16,202),(2,137,150),(0,0,0),(0,0,0),(8,112,168),(0,84,185),(0,41,199),(0,0,0),(0,72,190),(1,72,190),(0,0,0),(0,0,0),(0,22,202),(1,22,202),(0,9,203),(0,0,0),(2,72,190),(4,45,198),(0,0,0),(0,0,0),(0,36,200),(0,124,161),(1,124,161),(0,0,0),(3,8,203),(0,30,201),(0,0,0),(0,0,0),(2,36,200),(2,124,161),(4,29,201),(0,0,0),(3,84,185),(0,10,203),(0,0,0),(0,0,0),(4,108,172),(7,37,199),(5,142,145),(0,0,0),(4,86,184),(2,10,203),(0,0,0),(0,0,0),(0,46,198),(1,46,198),(4,7,203),(0,0,0),(3,124,161),(8,3,202),(0,0,0),(0,0,0),(2,46,198),(0,100,177),(0,11,203),(0,0,0),(0,54,196),(0,23,202),(0,0,0),(0,0,0),(3,10,203),(2,100,177),(2,11,203),(0,0,0),(2,54,196),(0,110,171),(0,0,0),(0,0,0),(6,18,202),(0,64,193),(0,75,189),(0,0,0),(0,128,158),(1,128,158),(0,0,0),(0,0,0),(4,22,202),(0,12,203),(1,12,203),(0,0,0),(2,128,158),(0,61,194),(0,0,0),(0,0,0),(3,23,202),(2,12,203),(0,31,201),(0,0,0),(24,36,162),(0,42,199),(0,0,0),(0,0,0),(3,110,171),(0,37,200),(1,37,200),(0,0,0),(3,64,193),(0,123,162),(0,0,0),(0,0,0),(7,107,172),(2,37,200),(0,13,203),(0,0,0),(0,24,202),(0,70,191),(0,0,0),(0,0,0),(3,61,194),(7,91,181),(0,119,165),(0,0,0),(2,24,202),(0,58,195),(0,0,0),(0,0,0),(3,42,199),(4,100,177),(2,119,165),(0,0,0),(3,37,200),(2,58,195),(0,0,0),(0,0,0),(3,123,162),(6,28,201),(6,131,155),(0,0,0),(14,32,194),(0,14,203),(0,0,0),(0,0,0),(3,70,191),(4,64,193),(0,51,197),(0,0,0),(4,128,158),(0,47,198),(0,0,0),(0,0,0),(3,58,195),(4,12,203),(2,51,197),(0,0,0),(6,20,202),(2,47,198),(0,0,0),(0,0,0),(7,85,184),(0,32,201),(1,32,201),(0,0,0),(0,78,188),(0,25,202),(0,0,0),(0,0,0),(3,14,203),(2,32,201),(0,15,203),(0,0,0),(2,78,188),(2,25,202),(0,0,0),(0,0,0),(3,47,198),(0,55,196),(1,55,196),(0,0,0),(0,38,200),(1,38,200),(0,0,0),(0,0,0),(7,68,191),(0,115,168),(0,43,199),(0,0,0),(2,38,200),(0,122,163),(0,0,0),(0,0,0),(3,25,202),(2,115,168),(2,43,199),(0,0,0),(7,59,194),(2,122,163),(0,0,0),(0,0,0),(6,108,172),(0,16,203),(1,16,203),(0,0,0),(3,55,196),(4,14,203),(0,0,0),(0,0,0),(0,144,144),(1,144,144),(0,65,193),(0,0,0),(0,126,160),(1,126,160),(0,0,0),(0,0,0),(0,26,202),(1,26,202),(2,65,193),(0,0,0),(2,126,160),(0,83,186),(0,0,0),(0,0,0),(0,68,192),(1,68,192),(0,33,201),(0,0,0),(3,16,203),(2,83,186),(0,0,0),(0,0,0),(2,68,192),(0,76,189),(0,17,203),(0,0,0),(6,72,190),(3,65,193),(0,0,0),(0,0,0),(0,140,148),(1,140,148),(0,59,195),(0,0,0),(0,48,198),(1,48,198),(0,0,0),(0,0,0),(0,106,174),(0,52,197),(1,52,197),(0,0,0),(2,48,198),(3,33,201),(0,0,0),(0,0,0),(2,106,174),(0,39,200),(0,71,191),(0,0,0),(3,76,189),(3,17,203),(0,0,0),(0,0,0),(7,28,201),(2,39,200),(0,81,187),(0,0,0),(7,142,145),(0,18,203),(0,0,0),(0,0,0),(4,144,144),(0,44,199),(1,44,199),(0,0,0),(3,52,197),(2,18,203),(0,0,0),(0,0,0),(0,138,150),(1,138,150),(0,125,161),(0,0,0),(3,39,200),(0,130,157),(0,0,0),(0,0,0),(0,56,196),(1,56,196),(2,125,161),(0,0,0),(7,2,203),(0,34,201),(0,0,0),(0,0,0),(2,56,196),(4,76,189),(0,111,171),(0,0,0),(3,44,199),(2,34,201),(0,0,0),(0,0,0),(4,140,148),(5,38,200),(0,19,203),(0,0,0),(4,48,198),(3,125,161),(0,0,0),(0,0,0),(0,74,190),(1,74,190),(0,117,167),(0,0,0),(10,82,184),(6,42,199),(0,0,0),(0,0,0),(2,74,190),(0,79,188),(1,79,188),(0,0,0),(0,28,202),(0,90,183),(0,0,0),(0,0,0),(31,40,101),(0,108,173),(1,108,173),(0,0,0),(2,28,202),(0,94,181),(0,0,0),(0,0,0),(0,40,200),(1,40,200),(6,119,165),(0,0,0),(8,104,174),(0,49,198),(0,0,0),(0,0,0),(2,40,200),(0,20,203),(1,20,203),(0,0,0),(3,79,188),(2,49,198),(0,0,0),(0,0,0),(0,0,204),(0,1,204),(0,53,197),(0,0,0),(0,2,204),(0,86,185),(0,0,0),(0,0,0),(2,0,204),(0,3,204),(0,35,201),(0,0,0),(2,2,204),(2,86,185),(0,0,0),(0,0,0),(0,4,204),(1,4,204),(0,135,153),(0,0,0),(3,20,203),(5,106,174),(0,0,0),(0,0,0),(2,4,204),(0,5,204),(1,5,204),(0,0,0),(3,1,204),(0,29,202),(0,0,0),(0,0,0),(3,86,185),(2,5,204),(0,21,203),(0,0,0),(0,6,204),(1,6,204),(0,0,0),(0,0,0),(11,62,191),(4,108,173),(2,21,203),(0,0,0),(2,6,204),(3,135,153),(0,0,0),(0,0,0),(4,40,200),(0,7,204),(1,7,204),(0,0,0),(3,5,204),(0,113,170),(0,0,0),(0,0,0),(0,134,154),(1,134,154),(5,130,157),(0,0,0),(7,23,202),(2,113,170),(0,0,0),(0,0,0),(0,8,204),(0,41,200),(1,41,200),(0,0,0),(0,100,178),(1,100,178),(0,0,0),(0,0,0),(2,8,204),(2,41,200),(4,35,201),(0,0,0),(2,100,178),(0,22,203),(0,0,0),(0,0,0),(3,113,170),(0,9,204),(0,123,163),(0,0,0),(7,61,194),(2,22,203),(0,0,0),(0,0,0),(0,30,202),(1,30,202),(2,123,163),(0,0,0),(3,41,200),(4,29,202),(0,0,0),(0,0,0),(2,30,202),(5,28,202),(0,133,155),(0,0,0),(0,10,204),(0,46,199),(0,0,0),(0,0,0),(3,22,203),(7,13,203),(2,133,155),(0,0,0),(2,10,204),(0,54,197),(0,0,0),(0,0,0),(6,106,174),(0,127,160),(1,127,160),(0,0,0),(0,64,194),(0,102,177),(0,0,0),(0,0,0),(4,134,154),(0,11,204),(0,23,203),(0,0,0),(2,64,194),(2,102,177),(0,0,0),(0,0,0),(0,80,188),(1,80,188),(0,61,195),(0,0,0),(4,100,178),(6,18,203),(0,0,0),(0,0,0),(2,80,188),(6,44,199),(2,61,195),(0,0,0),(3,127,160),(4,22,203),(0,0,0),(0,0,0),(0,12,204),(0,144,145),(1,144,145),(0,0,0),(0,42,200),(0,31,202),(0,0,0),(0,0,0),(2,12,204),(2,144,145),(0,37,201),(0,0,0),(2,42,200),(0,93,182),(0,0,0),(0,0,0),(11,53,194),(0,89,184),(1,89,184),(0,0,0),(0,58,196),(1,58,196),(0,0,0),(0,0,0),(7,55,196),(0,13,204),(0,95,181),(0,0,0),(2,58,196),(4,54,197),(0,0,0),(0,0,0),(0,104,176),(1,104,176),(0,87,185),(0,0,0),(4,64,194),(0,126,161),(0,0,0),(0,0,0),(2,104,176),(0,140,149),(1,140,149),(0,0,0),(3,89,184),(0,51,198),(0,0,0),(0,0,0),(4,80,188),(0,97,180),(0,47,199),(0,0,0),(0,14,204),(0,118,167),(0,0,0),(0,0,0),(6,40,200),(2,97,180),(2,47,199),(0,0,0),(2,14,204),(0,85,186),(0,0,0),(0,0,0),(3,126,161),(4,144,145),(10,35,199),(0,0,0),(0,32,202),(1,32,202),(0,0,0),(0,0,0),(3,51,198),(6,1,204),(0,25,203),(0,0,0),(2,32,202),(3,47,199),(0,0,0),(0,0,0),(3,118,167),(0,15,204),(0,99,179),(0,0,0),(4,58,196),(0,38,201),(0,0,0),(0,0,0),(3,85,186),(0,43,200),(1,43,200),(0,0,0),(15,29,194),(2,38,201),(0,0,0),(0,0,0),(4,104,176),(2,43,200),(0,83,187),(0,0,0),(8,128,158),(0,65,194),(0,0,0),(0,0,0),(0,130,158),(1,130,158),(0,121,165),(0,0,0),(3,15,204),(0,62,195),(0,0,0),(0,0,0),(0,16,204),(0,68,193),(1,68,193),(0,0,0),(0,76,190),(1,76,190),(0,0,0),(0,0,0),(2,16,204),(2,68,193),(10,111,169),(0,0,0),(2,76,190),(0,26,203),(0,0,0),(0,0,0),(3,65,194),(5,42,200),(5,31,202),(0,0,0),(4,32,202),(0,33,202),(0,0,0),(0,0,0),(0,114,170),(0,59,196),(1,59,196),(0,0,0),(3,68,193),(2,33,202),(0,0,0),(0,0,0),(2,114,170),(0,17,204),(1,17,204),(0,0,0),(0,52,198),(1,52,198),(0,0,0),(0,0,0),(3,26,203),(0,117,168),(1,117,168),(0,0,0),(2,52,198),(5,104,176),(0,0,0),(0,0,0),(3,33,202),(2,117,168),(0,39,201),(0,0,0),(3,59,196),(4,65,194),(0,0,0),(0,0,0),(4,130,158),(14,44,193),(2,39,201),(0,0,0),(3,17,204),(4,62,195),(0,0,0),(0,0,0),(0,44,200),(1,44,200),(0,27,203),(0,0,0),(0,18,204),(0,135,154),(0,0,0),(0,0,0),(2,44,200),(0,56,197),(1,56,197),(0,0,0),(2,18,204),(2,135,154),(0,0,0),(0,0,0),(7,20,203),(0,92,183),(1,92,183),(0,0,0),(0,90,184),(0,74,191),(0,0,0),(0,0,0),(0,34,202),(1,34,202),(0,79,189),(0,0,0),(2,90,184),(2,74,191),(0,0,0),(0,0,0),(2,34,202),(0,88,185),(1,88,185),(0,0,0),(3,56,197),(10,13,202),(0,0,0),(0,0,0),(6,12,204),(0,19,204),(1,19,204),(0,0,0),(3,92,183),(0,134,155),(0,0,0),(0,0,0),(0,128,160),(1,128,160),(4,39,201),(0,0,0),(7,29,202),(2,134,155),(0,0,0),(0,0,0),(0,66,194),(0,28,203),(0,63,195),(0,0,0),(3,88,185),(5,16,204),(0,0,0),(0,0,0)]

def wits_42 : List (ℕ × ℕ × ℕ) := [(2,66,194),(0,40,201),(0,49,199),(0,0,0),(0,98,180),(1,98,180),(0,0,0),(0,0,0),(3,134,155),(2,40,201),(0,69,193),(0,0,0),(2,98,180),(0,53,198),(0,0,0),(0,0,0),(0,20,204),(0,116,169),(1,116,169),(0,0,0),(3,28,203),(2,53,198),(0,0,0),(0,0,0),(2,20,204),(0,0,205),(0,1,205),(0,0,0),(3,40,201),(0,2,205),(0,0,0),(0,0,0),(18,10,190),(2,0,205),(0,3,205),(0,0,0),(7,22,203),(2,2,205),(0,0,0),(0,0,0),(3,53,198),(0,4,205),(1,4,205),(0,0,0),(3,116,169),(4,134,155),(0,0,0),(0,0,0),(0,72,192),(1,72,192),(0,5,205),(0,0,0),(0,144,146),(1,144,146),(0,0,0),(0,0,0),(2,72,192),(0,21,204),(0,57,197),(0,0,0),(2,144,146),(0,6,205),(0,0,0),(0,0,0),(8,56,196),(2,21,204),(2,57,197),(0,0,0),(0,82,188),(1,82,188),(0,0,0),(0,0,0),(7,127,160),(0,132,157),(0,7,205),(0,0,0),(2,82,188),(3,5,205),(0,0,0),(0,0,0),(4,20,204),(2,132,157),(0,41,201),(0,0,0),(3,21,204),(3,57,197),(0,0,0),(0,0,0),(0,102,178),(0,8,205),(1,8,205),(0,0,0),(6,76,190),(4,2,205),(0,0,0),(0,0,0),(2,102,178),(2,8,205),(4,3,205),(0,0,0),(0,22,204),(0,50,199),(0,0,0),(0,0,0),(7,144,145),(4,4,205),(0,9,205),(0,0,0),(2,22,204),(0,30,203),(0,0,0),(0,0,0),(4,72,192),(6,59,196),(2,9,205),(0,0,0),(0,46,200),(1,46,200),(0,0,0),(0,0,0),(0,54,198),(0,64,195),(0,139,151),(0,0,0),(2,46,200),(0,10,205),(0,0,0),(0,0,0),(0,112,172),(1,112,172),(2,139,151),(0,0,0),(4,82,188),(2,10,205),(0,0,0),(0,0,0),(2,112,172),(0,61,196),(0,93,183),(0,0,0),(7,126,161),(5,20,204),(0,0,0),(0,0,0),(7,140,149),(0,23,204),(0,11,205),(0,0,0),(0,118,168),(0,70,193),(0,0,0),(0,0,0),(3,10,205),(2,23,204),(2,11,205),(0,0,0),(2,118,168),(0,109,174),(0,0,0),(0,0,0),(11,5,202),(6,56,197),(8,21,203),(0,0,0),(3,61,196),(0,42,201),(0,0,0),(0,0,0),(11,66,191),(0,12,205),(0,31,203),(0,0,0),(3,23,204),(0,37,202),(0,0,0),(0,0,0),(3,70,193),(2,12,205),(0,137,153),(0,0,0),(4,46,200),(0,130,159),(0,0,0),(0,0,0),(0,78,190),(1,78,190),(2,137,153),(0,0,0),(7,38,201),(2,130,159),(0,0,0),(0,0,0),(0,24,204),(0,73,192),(0,13,205),(0,0,0),(3,12,205),(0,121,166),(0,0,0),(0,0,0),(2,24,204),(0,99,180),(0,51,199),(0,0,0),(7,65,194),(2,121,166),(0,0,0),(0,0,0),(3,130,159),(0,47,200),(1,47,200),(0,0,0),(0,106,176),(1,106,176),(0,0,0),(0,0,0),(7,68,193),(2,47,200),(6,49,199),(0,0,0),(2,106,176),(0,14,205),(0,0,0),(0,0,0),(3,121,166),(5,22,204),(5,50,199),(0,0,0),(3,99,180),(0,55,198),(0,0,0),(0,0,0),(6,20,204),(0,32,203),(1,32,203),(0,0,0),(3,47,200),(0,114,171),(0,0,0),(0,0,0),(7,59,196),(0,25,204),(0,101,179),(0,0,0),(8,64,194),(2,114,171),(0,0,0),(0,0,0),(0,38,202),(1,38,202),(0,15,205),(0,0,0),(10,86,184),(5,112,172),(0,0,0),(0,0,0),(2,38,202),(0,76,191),(1,76,191),(0,0,0),(0,62,196),(1,62,196),(0,0,0),(0,0,0),(3,114,171),(2,76,191),(4,51,199),(0,0,0),(2,62,196),(3,101,179),(0,0,0),(0,0,0),(0,124,164),(1,124,164),(5,70,193),(0,0,0),(4,106,176),(3,15,205),(0,0,0),(0,0,0),(2,124,164),(0,16,205),(0,81,189),(0,0,0),(3,76,191),(4,14,205),(0,0,0),(0,0,0),(7,56,197),(0,108,175),(0,59,197),(0,0,0),(0,26,204),(0,103,178),(0,0,0),(0,0,0),(7,92,183),(2,108,175),(0,33,203),(0,0,0),(2,26,204),(2,103,178),(0,0,0),(0,0,0),(0,48,200),(0,52,199),(1,52,199),(0,0,0),(3,16,205),(3,81,189),(0,0,0),(0,0,0),(2,48,200),(2,52,199),(0,17,205),(0,0,0),(3,108,175),(3,59,197),(0,0,0),(0,0,0),(0,92,184),(1,92,184),(2,17,205),(0,0,0),(4,62,196),(0,39,202),(0,0,0),(0,0,0),(2,92,184),(9,40,200),(10,11,203),(0,0,0),(3,52,199),(2,39,202),(0,0,0),(0,0,0),(4,124,164),(0,44,201),(0,133,157),(0,0,0),(0,56,198),(0,79,190),(0,0,0),(0,0,0),(6,112,172),(0,27,204),(1,27,204),(0,0,0),(2,56,198),(0,18,205),(0,0,0),(0,0,0),(3,39,202),(0,113,172),(0,105,177),(0,0,0),(0,116,170),(1,116,170),(0,0,0),(0,0,0),(7,116,169),(2,113,172),(2,105,177),(0,0,0),(2,116,170),(0,34,203),(0,0,0),(0,0,0),(3,79,190),(4,52,199),(8,83,187),(0,0,0),(3,27,204),(0,127,162),(0,0,0),(0,0,0),(0,110,174),(1,110,174),(4,17,205),(0,0,0),(3,113,172),(0,66,195),(0,0,0),(0,0,0),(2,110,174),(0,63,196),(0,19,205),(0,0,0),(0,132,158),(1,132,158),(0,0,0),(0,0,0),(3,34,203),(2,63,196),(2,19,205),(0,0,0),(2,132,158),(0,69,194),(0,0,0),(0,0,0),(0,28,204),(0,49,200),(1,49,200),(0,0,0),(0,40,202),(1,40,202),(0,0,0),(0,0,0),(2,28,204),(0,60,197),(0,53,199),(0,0,0),(2,40,202),(3,19,205),(0,0,0),(0,0,0),(7,132,157),(2,60,197),(2,53,199),(0,0,0),(4,116,170),(12,87,182),(0,0,0),(0,0,0),(3,69,194),(0,20,205),(0,45,201),(0,0,0),(3,49,200),(4,34,203),(0,0,0),(0,0,0),(7,8,205),(0,72,193),(0,35,203),(0,0,0),(0,0,206),(0,1,206),(0,0,0),(0,0,0),(0,2,206),(1,2,206),(0,131,159),(0,0,0),(2,0,206),(0,3,206),(0,0,0),(0,0,0),(2,2,206),(4,63,196),(2,131,159),(0,0,0),(0,4,206),(0,57,198),(0,0,0),(0,0,0),(14,36,196),(0,29,204),(1,29,204),(0,0,0),(2,4,206),(0,5,206),(0,0,0),(0,0,0),(3,1,206),(2,29,204),(0,21,205),(0,0,0),(4,40,202),(2,5,206),(0,0,0),(0,0,0),(0,6,206),(0,112,173),(1,112,173),(0,0,0),(6,62,196),(14,23,198),(0,0,0),(0,0,0),(2,6,206),(2,112,173),(16,19,195),(0,0,0),(3,29,204),(0,7,206),(0,0,0),(0,0,0),(3,5,206),(0,75,192),(1,75,192),(0,0,0),(7,70,193),(2,7,206),(0,0,0),(0,0,0),(8,128,160),(2,75,192),(4,35,203),(0,0,0),(0,8,206),(1,8,206),(0,0,0),(0,0,0),(4,2,206),(0,36,203),(0,91,185),(0,0,0),(2,8,206),(0,22,205),(0,0,0),(0,0,0),(0,64,196),(1,64,196),(0,67,195),(0,0,0),(0,30,204),(0,9,206),(0,0,0),(0,0,0),(2,64,196),(0,125,164),(1,125,164),(0,0,0),(2,30,204),(2,9,206),(0,0,0),(0,0,0),(8,20,204),(2,125,164),(0,61,197),(0,0,0),(3,36,203),(0,97,182),(0,0,0),(0,0,0),(0,10,206),(1,10,206),(0,87,187),(0,0,0),(7,121,166),(2,97,182),(0,0,0),(0,0,0),(2,10,206),(7,51,199),(2,87,187),(0,0,0),(3,125,164),(4,7,206),(0,0,0),(0,0,0),(7,47,200),(4,75,192),(0,23,205),(0,0,0),(6,56,198),(0,11,206),(0,0,0),(0,0,0),(3,97,182),(0,135,156),(0,99,181),(0,0,0),(4,8,206),(0,78,191),(0,0,0),(0,0,0),(0,42,202),(0,85,188),(1,85,188),(0,0,0),(6,116,170),(2,78,191),(0,0,0),(0,0,0),(2,42,202),(0,31,204),(0,37,203),(0,0,0),(0,12,206),(1,12,206),(0,0,0),(0,0,0),(3,11,206),(2,31,204),(2,37,203),(0,0,0),(2,12,206),(0,117,170),(0,0,0),(0,0,0),(3,78,191),(7,15,205),(4,61,197),(0,0,0),(3,85,188),(0,111,174),(0,0,0),(0,0,0),(4,10,206),(0,24,205),(1,24,205),(0,0,0),(3,31,204),(0,13,206),(0,0,0),(0,0,0),(15,127,152),(2,24,205),(0,47,201),(0,0,0),(8,22,204),(2,13,206),(0,0,0),(0,0,0),(3,117,170),(6,49,200),(2,47,201),(0,0,0),(6,40,202),(4,11,206),(0,0,0),(0,0,0),(0,120,168),(1,120,168),(0,55,199),(0,0,0),(0,128,162),(1,128,162),(0,0,0),(0,0,0),(0,14,206),(1,14,206),(0,145,147),(0,0,0),(2,128,162),(3,47,201),(0,0,0),(0,0,0),(0,32,204),(0,65,196),(1,65,196),(0,0,0),(4,12,206),(10,29,202),(0,0,0),(0,0,0),(2,32,204),(0,68,195),(0,25,205),(0,0,0),(6,0,206),(0,38,203),(0,0,0),(0,0,0),(6,2,206),(2,68,195),(2,25,205),(0,0,0),(8,118,168),(0,15,206),(0,0,0),(0,0,0),(0,142,150),(1,142,150),(14,121,159),(0,0,0),(3,65,196),(2,15,206),(0,0,0),(0,0,0),(2,142,150),(6,29,204),(4,47,201),(0,0,0),(3,68,195),(0,71,194),(0,0,0),(0,0,0),(3,38,203),(7,133,157),(0,141,151),(0,0,0),(7,79,190),(0,59,198),(0,0,0),(0,0,0),(3,15,206),(0,92,185),(1,92,185),(0,0,0),(0,16,206),(1,16,206),(0,0,0),(0,0,0),(0,90,186),(0,116,171),(0,113,173),(0,0,0),(2,16,206),(0,26,205),(0,0,0),(0,0,0),(0,52,200),(0,33,204),(1,33,204),(0,0,0),(7,34,203),(0,105,178),(0,0,0),(0,0,0),(2,52,200),(0,88,187),(1,88,187),(0,0,0),(3,92,185),(2,105,178),(0,0,0),(0,0,0),(11,58,195),(2,88,187),(0,79,191),(0,0,0),(3,116,171),(0,17,206),(0,0,0),(0,0,0),(0,98,182),(1,98,182),(0,39,203),(0,0,0),(3,33,204),(2,17,206),(0,0,0),(0,0,0),(2,98,182),(0,56,199),(1,56,199),(0,0,0),(0,44,202),(1,44,202),(0,0,0),(0,0,0),(7,49,200),(2,56,199),(4,141,151),(0,0,0),(2,44,202),(3,79,191),(0,0,0),(0,0,0),(3,17,206),(4,92,185),(0,27,205),(0,0,0),(4,16,206),(3,39,203),(0,0,0),(0,0,0),(0,18,206),(0,100,181),(1,100,181),(0,0,0),(3,56,199),(4,26,205),(0,0,0),(0,0,0),(2,18,206),(2,100,181),(6,23,205),(0,0,0),(0,34,204),(0,122,167),(0,0,0),(0,0,0),(7,72,193),(0,84,189),(0,63,197),(0,0,0),(2,34,204),(2,122,167),(0,0,0),(0,0,0),(6,42,202),(2,84,189),(0,69,195),(0,0,0),(3,100,181),(4,17,206),(0,0,0),(0,0,0),(4,98,182),(0,77,192),(0,137,155),(0,0,0),(6,12,206),(0,19,206),(0,0,0),(0,0,0),(3,122,167),(2,77,192),(0,49,201),(0,0,0),(0,60,198),(1,60,198),(0,0,0),(0,0,0),(14,8,200),(0,28,205),(1,28,205),(0,0,0),(2,60,198),(3,69,195),(0,0,0),(0,0,0),(7,112,173),(2,28,205),(4,27,205),(0,0,0),(0,72,194),(0,130,161),(0,0,0),(0,0,0),(0,82,190),(1,82,190),(5,26,205),(0,0,0),(2,72,194),(0,45,202),(0,0,0),(0,0,0),(0,136,156),(1,136,156),(5,105,178),(0,0,0),(0,20,206),(1,20,206),(0,0,0),(0,0,0),(2,136,156),(0,35,204),(1,35,204),(0,0,0),(2,20,206),(9,46,200),(0,0,0),(0,0,0),(3,130,161),(0,0,207),(0,1,207),(0,0,0),(7,22,205),(0,2,207),(0,0,0),(0,0,0),(3,45,202),(0,104,179),(0,3,207),(0,0,0),(7,9,206),(2,2,207),(0,0,0),(0,0,0),(7,125,164),(0,4,207),(0,29,205),(0,0,0),(3,35,204),(6,38,203),(0,0,0),(0,0,0),(10,16,204),(2,4,207),(0,5,207),(0,0,0),(3,0,207),(0,21,206),(0,0,0),(0,0,0),(3,2,207),(0,80,191),(1,80,191),(0,0,0),(3,104,179),(0,6,207),(0,0,0),(0,0,0),(4,82,190),(2,80,191),(0,41,203),(0,0,0),(3,4,207),(2,6,207),(0,0,0),(0,0,0),(4,136,156),(5,34,204),(0,7,207),(0,0,0),(4,20,206),(0,50,201),(0,0,0),(0,0,0),(3,21,206),(0,64,197),(1,64,197),(0,0,0),(3,80,191),(2,50,201),(0,0,0),(0,0,0),(0,36,204),(0,8,207),(1,8,207),(0,0,0),(0,54,200),(1,54,200),(0,0,0),(0,0,0),(0,22,206),(1,22,206),(4,3,207),(0,0,0),(2,54,200),(0,30,205),(0,0,0),(0,0,0),(2,22,206),(0,145,148),(0,9,207),(0,0,0),(0,124,166),(1,124,166),(0,0,0),(0,0,0),(10,44,200),(0,144,149),(1,144,149),(0,0,0),(2,124,166),(4,21,206),(0,0,0),(0,0,0),(6,98,182),(2,144,149),(0,85,189),(0,0,0),(0,78,192),(0,10,207),(0,0,0),(0,0,0),(3,30,205),(0,128,163),(1,128,163),(0,0,0),(2,78,192),(2,10,207),(0,0,0),(0,0,0),(10,34,202),(0,120,169),(0,101,181),(0,0,0),(3,144,149),(0,23,206),(0,0,0),(0,0,0),(15,28,197),(2,120,169),(0,11,207),(0,0,0),(11,5,204),(0,42,203),(0,0,0),(0,0,0),(3,10,207),(4,8,207),(2,11,207),(0,0,0),(3,128,163),(2,42,203),(0,0,0),(0,0,0),(4,22,206),(0,37,204),(0,31,205),(0,0,0),(3,120,169),(0,83,190),(0,0,0),(0,0,0),(3,23,206),(0,12,207),(1,12,207),(0,0,0),(4,124,166),(2,83,190),(0,0,0),(0,0,0)]

def wits_43 : List (ℕ × ℕ × ℕ) := [(3,42,203),(2,12,207),(0,51,201),(0,0,0),(7,15,206),(13,2,202),(0,0,0),(0,0,0),(19,7,190),(0,103,180),(1,103,180),(0,0,0),(0,24,206),(0,47,202),(0,0,0),(0,0,0),(3,83,190),(2,103,180),(0,13,207),(0,0,0),(2,24,206),(2,47,202),(0,0,0),(0,0,0),(0,132,160),(0,55,200),(1,55,200),(0,0,0),(7,59,198),(3,51,201),(0,0,0),(0,0,0),(2,132,160),(2,55,200),(0,65,197),(0,0,0),(3,103,180),(0,139,154),(0,0,0),(0,0,0),(0,68,196),(1,68,196),(0,81,191),(0,0,0),(7,26,205),(0,14,207),(0,0,0),(0,0,0),(0,62,198),(0,32,205),(1,32,205),(0,0,0),(3,55,200),(2,14,207),(0,0,0),(0,0,0),(2,62,198),(2,32,205),(0,43,203),(0,0,0),(0,38,204),(0,25,206),(0,0,0),(0,0,0),(3,139,154),(6,0,207),(0,71,195),(0,0,0),(2,38,204),(0,90,187),(0,0,0),(0,0,0),(0,96,184),(1,96,184),(0,15,207),(0,0,0),(0,110,176),(1,110,176),(0,0,0),(0,0,0),(2,96,184),(6,4,207),(0,59,199),(0,0,0),(2,110,176),(3,43,203),(0,0,0),(0,0,0),(0,88,188),(1,88,188),(2,59,199),(0,0,0),(8,12,206),(0,98,183),(0,0,0),(0,0,0),(2,88,188),(6,80,191),(4,65,197),(0,0,0),(10,22,204),(0,126,165),(0,0,0),(0,0,0),(4,68,196),(0,16,207),(1,16,207),(0,0,0),(0,48,202),(1,48,202),(0,0,0),(0,0,0),(0,26,206),(1,26,206),(0,33,205),(0,0,0),(2,48,202),(0,86,189),(0,0,0),(0,0,0),(2,26,206),(6,64,197),(2,33,205),(0,0,0),(0,100,182),(1,100,182),(0,0,0),(0,0,0),(3,126,165),(6,8,207),(4,71,195),(0,0,0),(2,100,182),(0,107,178),(0,0,0),(0,0,0),(0,56,200),(0,39,204),(0,17,207),(0,0,0),(4,110,176),(2,107,178),(0,0,0),(0,0,0),(0,130,162),(0,44,203),(1,44,203),(0,0,0),(6,124,166),(5,132,160),(0,0,0),(0,0,0),(2,130,162),(2,44,203),(0,115,173),(0,0,0),(0,84,190),(1,84,190),(0,0,0),(0,0,0),(3,107,178),(8,68,195),(2,115,173),(0,0,0),(2,84,190),(0,27,206),(0,0,0),(0,0,0),(15,92,177),(0,112,175),(1,112,175),(0,0,0),(3,44,203),(0,18,207),(0,0,0),(0,0,0),(4,26,206),(0,69,196),(0,77,193),(0,0,0),(11,43,200),(0,34,205),(0,0,0),(0,0,0),(7,35,204),(2,69,196),(2,77,193),(0,0,0),(4,100,182),(0,135,158),(0,0,0),(0,0,0),(3,27,206),(7,1,207),(5,90,187),(0,0,0),(3,112,175),(2,135,158),(0,0,0),(0,0,0),(3,18,207),(0,60,199),(0,121,169),(0,0,0),(3,69,196),(0,49,202),(0,0,0),(0,0,0),(3,34,205),(0,72,195),(0,19,207),(0,0,0),(10,106,176),(2,49,202),(0,0,0),(0,0,0),(0,40,204),(1,40,204),(0,147,147),(0,0,0),(0,28,206),(1,28,206),(0,0,0),(0,0,0),(2,40,204),(6,103,180),(0,145,149),(0,0,0),(2,28,206),(3,121,169),(0,0,0),(0,0,0),(3,49,202),(4,112,175),(0,45,203),(0,0,0),(0,144,150),(0,134,159),(0,0,0),(0,0,0),(6,132,160),(4,69,196),(2,45,203),(0,0,0),(2,144,150),(0,93,186),(0,0,0),(0,0,0),(7,64,197),(0,20,207),(0,35,205),(0,0,0),(8,44,202),(2,93,186),(0,0,0),(0,0,0),(6,68,196),(2,20,207),(2,35,205),(0,0,0),(10,62,196),(0,75,194),(0,0,0),(0,0,0),(0,0,208),(0,1,208),(1,1,208),(0,0,0),(0,2,208),(1,2,208),(0,0,0),(0,0,0),(0,114,174),(0,3,208),(1,3,208),(0,0,0),(2,2,208),(0,29,206),(0,0,0),(0,0,0),(0,4,208),(1,4,208),(4,147,147),(0,0,0),(4,28,206),(2,29,206),(0,0,0),(0,0,0),(2,4,208),(0,5,208),(0,21,207),(0,0,0),(3,1,208),(10,103,178),(0,0,0),(0,0,0),(7,128,163),(0,41,204),(0,67,197),(0,0,0),(0,6,208),(1,6,208),(0,0,0),(0,0,0),(0,50,202),(1,50,202),(2,67,197),(0,0,0),(2,6,208),(4,93,186),(0,0,0),(0,0,0),(2,50,202),(0,7,208),(1,7,208),(0,0,0),(0,70,196),(0,54,201),(0,0,0),(0,0,0),(10,92,184),(0,36,205),(0,61,199),(0,0,0),(2,70,196),(0,46,203),(0,0,0),(0,0,0),(0,8,208),(1,8,208),(2,61,199),(0,0,0),(4,2,208),(0,22,207),(0,0,0),(0,0,0),(0,30,206),(1,30,206),(10,133,157),(0,0,0),(3,7,208),(2,22,207),(0,0,0),(0,0,0),(2,30,206),(0,9,208),(0,139,155),(0,0,0),(0,108,178),(1,108,178),(0,0,0),(0,0,0),(3,46,203),(0,123,168),(0,73,195),(0,0,0),(2,108,178),(9,128,162),(0,0,0),(0,0,0),(3,22,207),(2,123,168),(2,73,195),(0,0,0),(0,10,208),(1,10,208),(0,0,0),(0,0,0),(4,50,202),(8,104,179),(0,83,191),(0,0,0),(2,10,208),(3,139,155),(0,0,0),(0,0,0),(10,110,174),(4,7,208),(0,23,207),(0,0,0),(0,42,204),(1,42,204),(0,0,0),(0,0,0),(15,3,200),(0,11,208),(1,11,208),(0,0,0),(2,42,204),(4,46,203),(0,0,0),(0,0,0),(4,8,208),(2,11,208),(0,37,205),(0,0,0),(20,130,136),(0,31,206),(0,0,0),(0,0,0),(4,30,206),(7,43,203),(0,119,171),(0,0,0),(7,25,206),(0,51,202),(0,0,0),(0,0,0),(0,12,208),(1,12,208),(2,119,171),(0,0,0),(0,76,194),(1,76,194),(0,0,0),(0,0,0),(2,12,208),(4,123,168),(0,47,203),(0,0,0),(2,76,194),(3,37,205),(0,0,0),(0,0,0),(3,31,206),(0,24,207),(0,55,201),(0,0,0),(4,10,208),(0,65,198),(0,0,0),(0,0,0),(0,94,186),(0,13,208),(1,13,208),(0,0,0),(6,28,206),(2,65,198),(0,0,0),(0,0,0),(2,94,186),(0,96,185),(1,96,185),(0,0,0),(0,90,188),(0,62,199),(0,0,0),(0,0,0),(7,16,207),(2,96,185),(5,46,203),(0,0,0),(2,90,188),(2,62,199),(0,0,0),(0,0,0),(3,65,198),(0,71,196),(1,71,196),(0,0,0),(0,14,208),(1,14,208),(0,0,0),(0,0,0),(14,48,196),(0,43,204),(1,43,204),(0,0,0),(2,14,208),(0,38,205),(0,0,0),(0,0,0),(3,62,199),(2,43,204),(0,25,207),(0,0,0),(4,76,194),(2,38,205),(0,0,0),(0,0,0),(6,0,208),(0,59,200),(1,59,200),(0,0,0),(3,71,196),(8,42,203),(0,0,0),(0,0,0),(6,114,174),(0,15,208),(0,79,193),(0,0,0),(3,43,204),(4,65,198),(0,0,0),(0,0,0),(0,86,190),(1,86,190),(2,79,193),(0,0,0),(10,8,206),(0,74,195),(0,0,0),(0,0,0),(2,86,190),(4,96,185),(0,135,159),(0,0,0),(0,52,202),(1,52,202),(0,0,0),(0,0,0),(7,112,175),(0,48,203),(0,125,167),(0,0,0),(2,52,202),(0,146,149),(0,0,0),(0,0,0),(0,16,208),(1,16,208),(2,125,167),(0,0,0),(4,14,208),(0,26,207),(0,0,0),(0,0,0),(0,102,182),(1,102,182),(5,51,202),(0,0,0),(6,70,196),(2,26,207),(0,0,0),(0,0,0),(2,102,182),(0,56,201),(1,56,201),(0,0,0),(3,48,203),(0,121,170),(0,0,0),(0,0,0),(3,146,149),(2,56,201),(0,39,205),(0,0,0),(7,49,202),(2,121,170),(0,0,0),(0,0,0),(0,44,204),(0,17,208),(1,17,208),(0,0,0),(0,134,160),(1,134,160),(0,0,0),(0,0,0),(0,66,198),(1,66,198),(6,139,155),(0,0,0),(2,134,160),(0,77,194),(0,0,0),(0,0,0),(2,66,198),(5,90,188),(0,63,199),(0,0,0),(4,52,202),(0,142,153),(0,0,0),(0,0,0),(23,28,175),(0,104,181),(0,27,207),(0,0,0),(3,17,208),(2,142,153),(0,0,0),(0,0,0),(4,16,208),(2,104,181),(2,27,207),(0,0,0),(0,18,208),(1,18,208),(0,0,0),(0,0,0),(0,34,206),(1,34,206),(5,38,205),(0,0,0),(2,18,208),(0,141,154),(0,0,0),(0,0,0),(0,60,200),(1,60,200),(13,14,203),(0,0,0),(3,104,181),(2,141,154),(0,0,0),(0,0,0),(2,60,200),(0,128,165),(0,49,203),(0,0,0),(11,16,205),(0,53,202),(0,0,0),(0,0,0),(4,44,204),(2,128,165),(0,93,187),(0,0,0),(4,134,160),(0,95,186),(0,0,0),(0,0,0),(3,141,154),(0,19,208),(1,19,208),(0,0,0),(6,76,194),(2,95,186),(0,0,0),(0,0,0),(7,5,208),(0,28,207),(0,97,185),(0,0,0),(0,106,180),(1,106,180),(0,0,0),(0,0,0),(3,53,202),(0,45,204),(0,89,189),(0,0,0),(2,106,180),(3,93,187),(0,0,0),(0,0,0),(3,95,186),(0,80,193),(0,57,201),(0,0,0),(3,19,208),(5,102,182),(0,0,0),(0,0,0),(4,34,206),(0,99,184),(1,99,184),(0,0,0),(3,28,207),(0,35,206),(0,0,0),(0,0,0),(0,20,208),(1,20,208),(5,121,170),(0,0,0),(0,132,162),(0,87,190),(0,0,0),(0,0,0),(2,20,208),(4,128,165),(4,49,203),(0,0,0),(2,132,162),(2,87,190),(0,0,0),(0,0,0),(11,18,205),(0,0,209),(0,1,209),(0,0,0),(3,99,184),(0,2,209),(0,0,0),(0,0,0),(3,35,206),(2,0,209),(0,3,209),(0,0,0),(10,16,206),(0,67,198),(0,0,0),(0,0,0),(3,87,190),(0,4,209),(1,4,209),(0,0,0),(4,106,180),(2,67,198),(0,0,0),(0,0,0),(10,52,200),(0,21,208),(0,5,209),(0,0,0),(3,0,209),(0,50,203),(0,0,0),(0,0,0),(3,2,209),(2,21,208),(2,5,209),(0,0,0),(11,63,196),(0,6,209),(0,0,0),(0,0,0),(0,54,202),(0,61,200),(1,61,200),(0,0,0),(3,4,209),(2,6,209),(0,0,0),(0,0,0),(2,54,202),(2,61,200),(0,7,209),(0,0,0),(0,36,206),(0,103,182),(0,0,0),(0,0,0),(3,50,203),(7,37,205),(2,7,209),(0,0,0),(2,36,206),(2,103,182),(0,0,0),(0,0,0),(3,6,209),(0,8,209),(1,8,209),(0,0,0),(0,22,208),(0,30,207),(0,0,0),(0,0,0),(16,110,166),(0,83,192),(1,83,192),(0,0,0),(2,22,208),(2,30,207),(0,0,0),(0,0,0),(3,103,182),(2,83,192),(0,9,209),(0,0,0),(11,72,193),(0,58,201),(0,0,0),(0,0,0),(6,44,204),(4,21,208),(2,9,209),(0,0,0),(3,8,209),(2,58,201),(0,0,0),(0,0,0),(3,30,207),(0,136,159),(1,136,159),(0,0,0),(3,83,192),(0,10,209),(0,0,0),(0,0,0),(0,110,178),(1,110,178),(0,105,181),(0,0,0),(7,62,199),(0,42,205),(0,0,0),(0,0,0),(2,110,178),(0,23,208),(1,23,208),(0,0,0),(0,130,164),(1,130,164),(0,0,0),(0,0,0),(7,71,196),(0,76,195),(0,11,209),(0,0,0),(2,130,164),(0,37,206),(0,0,0),(0,0,0),(0,92,188),(1,92,188),(0,31,207),(0,0,0),(0,96,186),(1,96,186),(0,0,0),(0,0,0),(0,146,150),(1,146,150),(2,31,207),(0,0,0),(2,96,186),(0,90,189),(0,0,0),(0,0,0),(2,146,150),(0,12,209),(0,65,199),(0,0,0),(0,68,198),(0,55,202),(0,0,0),(0,0,0),(3,37,206),(2,12,209),(2,65,199),(0,0,0),(2,68,198),(2,55,202),(0,0,0),(0,0,0),(0,24,208),(1,24,208),(5,6,209),(0,0,0),(0,62,200),(1,62,200),(0,0,0),(0,0,0),(2,24,208),(0,107,180),(0,13,209),(0,0,0),(2,62,200),(0,118,173),(0,0,0),(0,0,0),(0,100,184),(1,100,184),(0,143,153),(0,0,0),(4,130,164),(2,118,173),(0,0,0),(0,0,0),(2,100,184),(4,76,195),(0,129,165),(0,0,0),(7,26,207),(4,37,206),(0,0,0),(0,0,0),(4,92,188),(0,32,207),(0,43,205),(0,0,0),(3,107,180),(0,14,209),(0,0,0),(0,0,0),(0,38,206),(1,38,206),(0,59,201),(0,0,0),(6,132,162),(2,14,209),(0,0,0),(0,0,0),(2,38,206),(0,25,208),(1,25,208),(0,0,0),(0,74,196),(0,102,183),(0,0,0),(0,0,0),(7,17,208),(2,25,208),(6,1,209),(0,0,0),(2,74,196),(2,102,183),(0,0,0),(0,0,0),(3,14,209),(10,64,197),(0,15,209),(0,0,0),(4,62,200),(3,59,201),(0,0,0),(0,0,0),(10,36,204),(0,52,203),(1,52,203),(0,0,0),(3,25,208),(4,118,173),(0,0,0),(0,0,0),(0,48,204),(1,48,204),(0,109,179),(0,0,0),(8,76,194),(6,50,203),(0,0,0),(0,0,0),(2,48,204),(10,145,148),(2,109,179),(0,0,0),(10,124,166),(0,133,162),(0,0,0),(0,0,0),(0,140,156),(0,16,209),(0,33,207),(0,0,0),(0,26,208),(1,26,208),(0,0,0),(0,0,0),(2,140,156),(2,16,209),(2,33,207),(0,0,0),(2,26,208),(3,109,179),(0,0,0),(0,0,0),(7,128,165),(4,25,208),(0,77,195),(0,0,0),(4,74,196),(0,39,206),(0,0,0),(0,0,0),(3,133,162),(0,44,205),(1,44,205),(0,0,0),(3,16,209),(0,69,198),(0,0,0),(0,0,0),(7,19,208),(0,63,200),(0,17,209),(0,0,0),(0,114,176),(0,82,193),(0,0,0),(0,0,0),(7,28,207),(2,63,200),(2,17,209),(0,0,0),(2,114,176),(2,82,193),(0,0,0),(0,0,0),(0,120,172),(1,120,172),(4,109,179),(0,0,0),(3,44,205),(10,83,190),(0,0,0),(0,0,0),(2,120,172),(0,27,208),(0,95,187),(0,0,0),(3,63,200),(0,106,181),(0,0,0),(0,0,0)]

def wits_44 : List (ℕ × ℕ × ℕ) := [(3,82,193),(0,60,201),(0,91,189),(0,0,0),(4,26,208),(0,18,209),(0,0,0),(0,0,0),(0,138,158),(1,138,158),(2,91,189),(0,0,0),(6,130,164),(2,18,209),(0,0,0),(0,0,0),(2,138,158),(0,49,204),(0,53,203),(0,0,0),(3,27,208),(0,89,190),(0,0,0),(0,0,0),(3,106,181),(2,49,204),(0,99,185),(0,0,0),(3,60,201),(0,123,170),(0,0,0),(0,0,0),(3,18,209),(4,63,200),(2,99,185),(0,0,0),(0,40,206),(1,40,206),(0,0,0),(0,0,0),(7,4,209),(0,75,196),(0,19,209),(0,0,0),(2,40,206),(3,53,203),(0,0,0),(0,0,0),(0,28,208),(1,28,208),(0,45,205),(0,0,0),(7,50,203),(0,57,202),(0,0,0),(0,0,0),(2,28,208),(0,101,184),(1,101,184),(0,0,0),(6,62,200),(2,57,202),(0,0,0),(0,0,0),(0,108,180),(1,108,180),(4,91,189),(0,0,0),(3,75,196),(3,19,209),(0,0,0),(0,0,0),(2,108,180),(7,7,209),(0,35,207),(0,0,0),(7,103,182),(3,45,205),(0,0,0),(0,0,0),(3,57,202),(0,20,209),(1,20,209),(0,0,0),(3,101,184),(4,89,190),(0,0,0),(0,0,0),(7,8,209),(0,85,192),(0,67,199),(0,0,0),(7,30,207),(4,123,170),(0,0,0),(0,0,0),(0,64,200),(1,64,200),(0,103,183),(0,0,0),(0,0,210),(0,1,210),(0,0,0),(0,0,0),(0,2,210),(0,29,208),(1,29,208),(0,0,0),(2,0,210),(0,3,210),(0,0,0),(0,0,0),(2,2,210),(2,29,208),(4,45,205),(0,0,0),(0,4,210),(0,41,206),(0,0,0),(0,0,0),(7,136,159),(4,101,184),(0,21,209),(0,0,0),(2,4,210),(0,5,210),(0,0,0),(0,0,0),(3,1,210),(0,145,152),(1,145,152),(0,0,0),(3,29,208),(2,5,210),(0,0,0),(0,0,0),(0,6,210),(1,6,210),(0,73,197),(0,0,0),(11,28,205),(0,46,205),(0,0,0),(0,0,0),(2,6,210),(0,36,207),(0,135,161),(0,0,0),(7,37,206),(0,7,210),(0,0,0),(0,0,0),(3,5,210),(2,36,207),(2,135,161),(0,0,0),(3,145,152),(2,7,210),(0,0,0),(0,0,0),(4,64,200),(5,40,206),(4,103,183),(0,0,0),(0,8,210),(0,22,209),(0,0,0),(0,0,0),(0,58,202),(1,58,202),(6,77,195),(0,0,0),(2,8,210),(2,22,209),(0,0,0),(0,0,0),(2,58,202),(6,44,205),(5,57,202),(0,0,0),(0,94,188),(0,9,210),(0,0,0),(0,0,0),(11,2,207),(0,92,189),(0,125,169),(0,0,0),(2,94,188),(0,142,155),(0,0,0),(0,0,0),(0,76,196),(1,76,196),(2,125,169),(0,0,0),(7,118,173),(0,81,194),(0,0,0),(0,0,0),(0,10,210),(0,115,176),(1,115,176),(0,0,0),(15,5,202),(2,81,194),(0,0,0),(0,0,0),(2,10,210),(2,115,176),(0,23,209),(0,0,0),(3,92,189),(3,125,169),(0,0,0),(0,0,0),(3,142,155),(0,51,204),(0,37,207),(0,0,0),(7,14,209),(0,11,210),(0,0,0),(0,0,0),(3,81,194),(0,31,208),(1,31,208),(0,0,0),(0,112,178),(1,112,178),(0,0,0),(0,0,0),(4,58,202),(2,31,208),(0,47,205),(0,0,0),(2,112,178),(3,23,209),(0,0,0),(0,0,0),(12,64,196),(5,4,210),(2,47,205),(0,0,0),(0,12,210),(0,62,201),(0,0,0),(0,0,0),(3,11,210),(0,140,157),(1,140,157),(0,0,0),(2,12,210),(2,62,201),(0,0,0),(0,0,0),(4,76,196),(0,24,209),(0,133,163),(0,0,0),(0,86,192),(1,86,192),(0,0,0),(0,0,0),(4,10,210),(2,24,209),(0,79,195),(0,0,0),(2,86,192),(0,13,210),(0,0,0),(0,0,0),(3,62,201),(0,128,167),(1,128,167),(0,0,0),(0,124,170),(1,124,170),(0,0,0),(0,0,0),(6,108,180),(0,109,180),(1,109,180),(0,0,0),(2,124,170),(0,43,206),(0,0,0),(0,0,0),(0,32,208),(1,32,208),(5,22,209),(0,0,0),(4,112,178),(0,38,207),(0,0,0),(0,0,0),(0,14,210),(1,14,210),(4,47,205),(0,0,0),(3,128,167),(2,38,207),(0,0,0),(0,0,0),(2,14,210),(0,84,193),(0,25,209),(0,0,0),(3,109,180),(4,62,201),(0,0,0),(0,0,0),(3,43,206),(2,84,193),(0,117,175),(0,0,0),(6,0,210),(5,76,196),(0,0,0),(0,0,0),(0,52,204),(1,52,204),(2,117,175),(0,0,0),(4,86,192),(0,15,210),(0,0,0),(0,0,0),(2,52,204),(0,48,205),(1,48,205),(0,0,0),(3,84,193),(2,15,210),(0,0,0),(0,0,0),(7,27,208),(2,48,205),(6,21,209),(0,0,0),(4,124,170),(3,117,175),(0,0,0),(0,0,0),(7,60,201),(0,56,203),(1,56,203),(0,0,0),(7,18,209),(4,43,206),(0,0,0),(0,0,0),(3,15,210),(0,33,208),(1,33,208),(0,0,0),(0,16,210),(0,26,209),(0,0,0),(0,0,0),(0,82,194),(1,82,194),(0,69,199),(0,0,0),(2,16,210),(2,26,209),(0,0,0),(0,0,0),(2,82,194),(0,95,188),(0,39,207),(0,0,0),(0,44,206),(1,44,206),(0,0,0),(0,0,0),(11,14,207),(2,95,188),(0,97,187),(0,0,0),(2,44,206),(0,91,190),(0,0,0),(0,0,0),(3,26,209),(5,86,192),(0,131,165),(0,0,0),(0,72,198),(0,17,210),(0,0,0),(0,0,0),(8,38,206),(4,48,205),(2,131,165),(0,0,0),(2,72,198),(0,99,186),(0,0,0),(0,0,0),(7,101,184),(5,124,170),(0,89,191),(0,0,0),(0,60,202),(1,60,202),(0,0,0),(0,0,0),(3,91,190),(4,56,203),(0,27,209),(0,0,0),(2,60,202),(3,131,165),(0,0,0),(0,0,0),(3,17,210),(0,136,161),(1,136,161),(0,0,0),(0,34,208),(1,34,208),(0,0,0),(0,0,0),(0,18,210),(0,53,204),(0,49,205),(0,0,0),(2,34,208),(3,89,191),(0,0,0),(0,0,0),(0,116,176),(0,87,192),(0,75,197),(0,0,0),(4,44,206),(0,119,174),(0,0,0),(0,0,0),(2,116,176),(2,87,192),(2,75,197),(0,0,0),(3,136,161),(2,119,174),(0,0,0),(0,0,0),(7,29,208),(0,40,207),(1,40,207),(0,0,0),(0,144,154),(0,113,178),(0,0,0),(0,0,0),(0,130,166),(1,130,166),(0,57,203),(0,0,0),(2,144,154),(0,19,210),(0,0,0),(0,0,0),(2,130,166),(0,28,209),(1,28,209),(0,0,0),(0,122,172),(0,135,162),(0,0,0),(0,0,0),(7,145,152),(2,28,209),(0,85,193),(0,0,0),(2,122,172),(2,135,162),(0,0,0),(0,0,0),(3,113,178),(4,136,161),(2,85,193),(0,0,0),(4,34,208),(3,57,203),(0,0,0),(0,0,0),(3,19,210),(0,35,208),(1,35,208),(0,0,0),(3,28,209),(20,122,147),(0,0,0),(0,0,0),(3,135,162),(0,64,201),(1,64,201),(0,0,0),(0,20,210),(0,70,199),(0,0,0),(0,0,0),(6,32,208),(2,64,201),(5,91,190),(0,0,0),(2,20,210),(2,70,199),(0,0,0),(0,0,0),(6,14,210),(4,40,207),(0,105,183),(0,0,0),(3,35,208),(4,113,178),(0,0,0),(0,0,0),(4,130,166),(0,0,211),(0,1,211),(0,0,0),(3,64,201),(0,2,211),(0,0,0),(0,0,0),(3,70,199),(2,0,211),(0,3,211),(0,0,0),(0,54,204),(0,73,198),(0,0,0),(0,0,0),(6,52,204),(0,4,211),(1,4,211),(0,0,0),(2,54,204),(0,21,210),(0,0,0),(0,0,0),(7,115,176),(2,4,211),(0,5,211),(0,0,0),(3,0,211),(0,118,175),(0,0,0),(0,0,0),(0,46,206),(1,46,206),(0,115,177),(0,0,0),(10,134,160),(0,6,211),(0,0,0),(0,0,0),(0,36,208),(1,36,208),(2,115,177),(0,0,0),(0,92,190),(1,92,190),(0,0,0),(0,0,0),(2,36,208),(6,33,208),(0,7,211),(0,0,0),(2,92,190),(0,58,203),(0,0,0),(0,0,0),(3,118,175),(5,144,154),(2,7,211),(0,0,0),(11,20,207),(0,30,209),(0,0,0),(0,0,0),(0,22,210),(0,8,211),(0,81,195),(0,0,0),(6,44,206),(2,30,209),(0,0,0),(0,0,0),(2,22,210),(2,8,211),(2,81,195),(0,0,0),(0,100,186),(1,100,186),(0,0,0),(0,0,0),(3,58,203),(4,4,211),(0,9,211),(0,0,0),(2,100,186),(4,21,210),(0,0,0),(0,0,0),(0,88,192),(1,88,192),(2,9,211),(0,0,0),(3,8,211),(0,42,207),(0,0,0),(0,0,0),(2,88,192),(0,124,171),(1,124,171),(0,0,0),(6,60,202),(0,10,211),(0,0,0),(0,0,0),(0,68,200),(1,68,200),(0,51,205),(0,0,0),(4,92,190),(0,23,210),(0,0,0),(0,0,0),(2,68,200),(0,37,208),(1,37,208),(0,0,0),(6,34,208),(2,23,210),(0,0,0),(0,0,0),(3,42,207),(0,55,204),(0,11,211),(0,0,0),(0,138,160),(0,47,206),(0,0,0),(0,0,0),(0,62,202),(0,132,165),(1,132,165),(0,0,0),(2,138,160),(2,47,206),(0,0,0),(0,0,0),(2,62,202),(0,79,196),(1,79,196),(0,0,0),(3,37,208),(8,7,210),(0,0,0),(0,0,0),(10,20,208),(0,12,211),(1,12,211),(0,0,0),(3,55,204),(3,11,211),(0,0,0),(0,0,0),(0,104,184),(1,104,184),(5,118,175),(0,0,0),(0,24,210),(1,24,210),(0,0,0),(0,0,0),(0,74,198),(1,74,198),(5,6,211),(0,0,0),(2,24,210),(4,10,211),(0,0,0),(0,0,0),(2,74,198),(5,92,190),(0,13,211),(0,0,0),(0,84,194),(1,84,194),(0,0,0),(0,0,0),(7,33,208),(4,37,208),(0,43,207),(0,0,0),(2,84,194),(0,149,150),(0,0,0),(0,0,0),(8,76,196),(0,32,209),(1,32,209),(0,0,0),(0,38,208),(1,38,208),(0,0,0),(0,0,0),(4,62,202),(0,123,172),(1,123,172),(0,0,0),(2,38,208),(0,14,211),(0,0,0),(0,0,0),(10,54,202),(0,111,180),(1,111,180),(0,0,0),(7,91,190),(0,25,210),(0,0,0),(0,0,0),(3,149,150),(0,52,205),(1,52,205),(0,0,0),(3,32,209),(2,25,210),(0,0,0),(0,0,0),(4,104,184),(2,52,205),(0,77,197),(0,0,0),(0,48,206),(0,145,154),(0,0,0),(0,0,0),(3,14,211),(7,89,191),(0,15,211),(0,0,0),(2,48,206),(0,82,195),(0,0,0),(0,0,0),(0,56,204),(0,97,188),(1,97,188),(0,0,0),(3,52,205),(0,66,201),(0,0,0),(0,0,0),(2,56,204),(0,69,200),(0,91,191),(0,0,0),(11,13,208),(2,66,201),(0,0,0),(0,0,0),(3,145,154),(2,69,200),(0,33,209),(0,0,0),(4,38,208),(0,63,202),(0,0,0),(0,0,0),(0,26,210),(0,16,211),(1,16,211),(0,0,0),(3,97,188),(2,63,202),(0,0,0),(0,0,0),(2,26,210),(0,39,208),(0,119,175),(0,0,0),(0,108,182),(0,130,167),(0,0,0),(0,0,0),(7,40,207),(2,39,208),(0,135,163),(0,0,0),(2,108,182),(0,101,186),(0,0,0),(0,0,0),(3,63,202),(5,24,210),(2,135,163),(0,0,0),(3,16,211),(2,101,186),(0,0,0),(0,0,0),(7,28,209),(0,60,203),(0,17,211),(0,0,0),(3,39,208),(0,122,173),(0,0,0),(0,0,0),(0,80,196),(1,80,196),(0,87,193),(0,0,0),(11,15,208),(2,122,173),(0,0,0),(0,0,0),(2,80,196),(4,69,200),(2,87,193),(0,0,0),(10,68,198),(0,27,210),(0,0,0),(0,0,0),(7,35,208),(5,38,208),(0,53,205),(0,0,0),(3,60,203),(0,34,209),(0,0,0),(0,0,0),(3,122,173),(4,16,211),(2,53,205),(0,0,0),(7,70,199),(0,18,211),(0,0,0),(0,0,0),(11,146,149),(4,39,208),(4,119,175),(0,0,0),(0,134,164),(1,134,164),(0,0,0),(0,0,0),(3,27,210),(6,55,204),(4,135,163),(0,0,0),(2,134,164),(0,85,194),(0,0,0),(0,0,0),(0,40,208),(0,57,204),(0,125,171),(0,0,0),(7,2,211),(2,85,194),(0,0,0),(0,0,0),(2,40,208),(2,57,204),(0,45,207),(0,0,0),(7,73,198),(4,122,173),(0,0,0),(0,0,0),(4,80,196),(0,105,184),(0,19,211),(0,0,0),(0,28,210),(1,28,210),(0,0,0),(0,0,0),(3,85,194),(2,105,184),(0,67,201),(0,0,0),(2,28,210),(0,78,197),(0,0,0),(0,0,0),(6,74,198),(7,115,177),(2,67,201),(0,0,0),(0,64,202),(1,64,202),(0,0,0),(0,0,0),(11,142,153),(12,69,196),(0,35,209),(0,0,0),(2,64,202),(0,115,178),(0,0,0),(0,0,0),(15,44,199),(5,108,182),(0,83,195),(0,0,0),(4,134,164),(0,121,174),(0,0,0),(0,0,0),(3,78,197),(0,20,211),(1,20,211),(0,0,0),(6,38,208),(2,121,174),(0,0,0),(0,0,0),(4,40,208),(2,20,211),(0,61,203),(0,0,0),(8,34,208),(3,35,209),(0,0,0),(0,0,0),(0,50,206),(0,96,189),(0,107,183),(0,0,0),(10,26,208),(0,29,210),(0,0,0),(0,0,0),(0,0,212),(0,1,212),(1,1,212),(0,0,0),(0,2,212),(1,2,212),(0,0,0),(0,0,0),(2,0,212),(0,3,212),(1,3,212),(0,0,0),(2,2,212),(3,61,203),(0,0,0),(0,0,0),(0,4,212),(1,4,212),(0,21,211),(0,0,0),(0,90,192),(0,46,207),(0,0,0),(0,0,0),(2,4,212),(0,5,212),(1,5,212),(0,0,0),(2,90,192),(2,46,207),(0,0,0),(0,0,0),(7,37,208),(0,36,209),(1,36,209),(0,0,0),(0,6,212),(1,6,212),(0,0,0),(0,0,0),(7,55,204),(2,36,209),(5,85,194),(0,0,0),(2,6,212),(3,21,211),(0,0,0),(0,0,0),(3,46,207),(0,7,212),(1,7,212),(0,0,0),(3,5,212),(10,106,181),(0,0,0),(0,0,0)]

def wits_45 : List (ℕ × ℕ × ℕ) := [(0,30,210),(1,30,210),(0,149,151),(0,0,0),(3,36,209),(0,22,211),(0,0,0),(0,0,0),(0,8,212),(1,8,212),(2,149,151),(0,0,0),(4,2,212),(0,137,162),(0,0,0),(0,0,0),(2,8,212),(4,3,212),(0,117,177),(0,0,0),(3,7,212),(2,137,162),(0,0,0),(0,0,0),(4,4,212),(0,9,212),(1,9,212),(0,0,0),(0,42,208),(0,65,202),(0,0,0),(0,0,0),(0,86,194),(1,86,194),(5,115,178),(0,0,0),(2,42,208),(0,51,206),(0,0,0),(0,0,0),(2,86,194),(0,71,200),(1,71,200),(0,0,0),(0,10,212),(1,10,212),(0,0,0),(0,0,0),(7,32,209),(2,71,200),(0,23,211),(0,0,0),(2,10,212),(0,62,203),(0,0,0),(0,0,0),(3,65,202),(4,7,212),(0,47,207),(0,0,0),(7,14,211),(0,31,210),(0,0,0),(0,0,0),(3,51,206),(0,11,212),(1,11,212),(0,0,0),(3,71,200),(2,31,210),(0,0,0),(0,0,0),(0,144,156),(1,144,156),(9,56,203),(0,0,0),(8,92,190),(0,74,199),(0,0,0),(0,0,0),(2,144,156),(0,84,195),(0,111,181),(0,0,0),(7,145,154),(2,74,199),(0,0,0),(0,0,0),(0,12,212),(1,12,212),(2,111,181),(0,0,0),(0,106,184),(1,106,184),(0,0,0),(0,0,0),(2,12,212),(0,24,211),(0,143,157),(0,0,0),(2,106,184),(4,51,206),(0,0,0),(0,0,0),(3,74,199),(2,24,211),(2,143,157),(0,0,0),(3,84,195),(3,111,181),(0,0,0),(0,0,0),(11,10,209),(0,13,212),(1,13,212),(0,0,0),(6,64,202),(0,126,171),(0,0,0),(0,0,0),(7,16,211),(0,135,164),(1,135,164),(0,0,0),(0,32,210),(0,38,209),(0,0,0),(0,0,0),(0,142,158),(1,142,158),(0,93,191),(0,0,0),(2,32,210),(0,77,198),(0,0,0),(0,0,0),(2,142,158),(0,119,176),(1,119,176),(0,0,0),(0,14,212),(1,14,212),(0,0,0),(0,0,0),(3,126,171),(0,91,192),(0,25,211),(0,0,0),(2,14,212),(9,34,208),(0,0,0),(0,0,0),(3,38,209),(0,48,207),(1,48,207),(0,0,0),(4,106,184),(3,93,191),(0,0,0),(0,0,0),(0,66,202),(0,56,205),(0,69,201),(0,0,0),(3,119,176),(10,22,209),(0,0,0),(0,0,0),(2,66,202),(0,15,212),(0,89,193),(0,0,0),(3,91,192),(3,25,211),(0,0,0),(0,0,0),(6,4,212),(2,15,212),(0,63,203),(0,0,0),(3,48,207),(0,134,165),(0,0,0),(0,0,0),(0,72,200),(1,72,200),(2,63,203),(0,0,0),(3,56,205),(0,33,210),(0,0,0),(0,0,0),(2,72,200),(6,36,209),(4,93,191),(0,0,0),(3,15,212),(0,26,211),(0,0,0),(0,0,0),(0,16,212),(1,16,212),(0,39,209),(0,0,0),(4,14,212),(0,87,194),(0,0,0),(0,0,0),(2,16,212),(0,80,197),(1,80,197),(0,0,0),(22,120,142),(2,87,194),(0,0,0),(0,0,0),(0,60,204),(1,60,204),(6,149,151),(0,0,0),(8,38,208),(6,22,211),(0,0,0),(0,0,0),(0,110,182),(1,110,182),(0,75,199),(0,0,0),(10,112,178),(3,39,209),(0,0,0),(0,0,0),(2,110,182),(0,17,212),(1,17,212),(0,0,0),(3,80,197),(8,25,210),(0,0,0),(0,0,0),(23,72,167),(2,17,212),(0,139,161),(0,0,0),(6,42,208),(0,53,206),(0,0,0),(0,0,0),(4,72,200),(5,32,210),(0,27,211),(0,0,0),(7,115,178),(0,118,177),(0,0,0),(0,0,0),(0,34,210),(1,34,210),(2,27,211),(0,0,0),(3,17,212),(2,118,177),(0,0,0),(0,0,0),(2,34,210),(5,14,212),(0,115,179),(0,0,0),(0,18,212),(1,18,212),(0,0,0),(0,0,0),(3,53,206),(4,80,197),(0,57,205),(0,0,0),(2,18,212),(3,27,211),(0,0,0),(0,0,0),(3,118,177),(0,40,209),(1,40,209),(0,0,0),(0,128,170),(1,128,170),(0,0,0),(0,0,0),(0,78,198),(0,45,208),(1,45,208),(0,0,0),(2,128,170),(0,67,202),(0,0,0),(0,0,0),(2,78,198),(2,45,208),(6,111,181),(0,0,0),(8,108,182),(0,70,201),(0,0,0),(0,0,0),(6,12,212),(0,19,212),(1,19,212),(0,0,0),(3,40,209),(2,70,201),(0,0,0),(0,0,0),(7,5,212),(0,132,167),(1,132,167),(0,0,0),(0,96,190),(0,94,191),(0,0,0),(0,0,0),(3,67,202),(2,132,167),(5,26,211),(0,0,0),(2,96,190),(0,35,210),(0,0,0),(0,0,0),(0,92,192),(0,73,200),(1,73,200),(0,0,0),(3,19,212),(2,35,210),(0,0,0),(0,0,0),(2,92,192),(0,61,204),(0,137,163),(0,0,0),(3,132,167),(0,146,155),(0,0,0),(0,0,0),(0,20,212),(1,20,212),(2,137,163),(0,0,0),(4,128,170),(0,50,207),(0,0,0),(0,0,0),(0,54,206),(1,54,206),(14,47,201),(0,0,0),(3,73,200),(2,50,207),(0,0,0),(0,0,0),(2,54,206),(0,145,156),(0,29,211),(0,0,0),(3,61,204),(3,137,163),(0,0,0),(0,0,0),(3,146,155),(0,0,213),(0,1,213),(0,0,0),(7,65,202),(0,2,213),(0,0,0),(0,0,0),(0,120,176),(0,76,199),(0,3,213),(0,0,0),(0,46,208),(1,46,208),(0,0,0),(0,0,0),(2,120,176),(0,4,213),(1,4,213),(0,0,0),(2,46,208),(0,58,205),(0,0,0),(0,0,0),(0,136,164),(1,136,164),(0,5,213),(0,0,0),(0,36,210),(1,36,210),(0,0,0),(0,0,0),(2,136,164),(4,61,204),(2,5,213),(0,0,0),(2,36,210),(0,6,213),(0,0,0),(0,0,0),(4,20,212),(5,128,170),(10,27,209),(0,0,0),(0,104,186),(0,143,158),(0,0,0),(0,0,0),(3,58,205),(10,136,161),(0,7,213),(0,0,0),(2,104,186),(0,30,211),(0,0,0),(0,0,0),(7,84,195),(4,145,156),(2,7,213),(0,0,0),(0,22,212),(1,22,212),(0,0,0),(0,0,0),(3,6,213),(0,8,213),(0,65,203),(0,0,0),(2,22,212),(4,2,213),(0,0,0),(0,0,0),(3,143,158),(2,8,213),(0,71,201),(0,0,0),(4,46,208),(0,42,209),(0,0,0),(0,0,0),(3,30,211),(4,4,213),(0,9,213),(0,0,0),(10,144,154),(2,42,209),(0,0,0),(0,0,0),(4,136,164),(8,1,212),(2,9,213),(0,0,0),(0,62,204),(0,55,206),(0,0,0),(0,0,0),(7,135,164),(8,3,212),(5,146,155),(0,0,0),(2,62,204),(0,10,213),(0,0,0),(0,0,0),(0,84,196),(0,23,212),(1,23,212),(0,0,0),(0,74,200),(1,74,200),(0,0,0),(0,0,0),(2,84,196),(0,141,160),(0,31,211),(0,0,0),(2,74,200),(4,30,211),(0,0,0),(0,0,0),(3,55,206),(2,141,160),(0,11,213),(0,0,0),(4,22,212),(12,58,201),(0,0,0),(0,0,0),(3,10,213),(0,116,179),(1,116,179),(0,0,0),(3,23,212),(5,120,176),(0,0,0),(0,0,0),(6,78,198),(2,116,179),(0,59,205),(0,0,0),(3,141,160),(0,97,190),(0,0,0),(0,0,0),(0,134,166),(0,12,213),(1,12,213),(0,0,0),(11,92,189),(2,97,190),(0,0,0),(0,0,0),(0,24,212),(0,140,161),(0,99,189),(0,0,0),(3,116,179),(4,55,206),(0,0,0),(0,0,0),(2,24,212),(2,140,161),(0,43,209),(0,0,0),(6,96,190),(0,82,197),(0,0,0),(0,0,0),(3,97,190),(4,23,212),(0,13,213),(0,0,0),(3,12,213),(0,129,170),(0,0,0),(0,0,0),(0,38,210),(0,32,211),(1,32,211),(0,0,0),(3,140,161),(2,129,170),(0,0,0),(0,0,0),(2,38,210),(0,52,207),(0,125,173),(0,0,0),(8,10,212),(0,89,194),(0,0,0),(0,0,0),(3,82,197),(2,52,207),(2,125,173),(0,0,0),(10,92,190),(0,14,213),(0,0,0),(0,0,0),(0,48,208),(0,25,212),(1,25,212),(0,0,0),(0,56,206),(1,56,206),(0,0,0),(0,0,0),(2,48,208),(2,25,212),(0,103,187),(0,0,0),(2,56,206),(3,125,173),(0,0,0),(0,0,0),(3,89,194),(0,63,204),(1,63,204),(0,0,0),(7,53,206),(0,110,183),(0,0,0),(0,0,0),(3,14,213),(2,63,204),(0,15,213),(0,0,0),(3,25,212),(2,110,183),(0,0,0),(0,0,0),(8,12,212),(5,74,200),(0,151,151),(0,0,0),(0,80,198),(1,80,198),(0,0,0),(0,0,0),(0,118,178),(1,118,178),(0,33,211),(0,0,0),(2,80,198),(0,138,163),(0,0,0),(0,0,0),(2,118,178),(0,44,209),(1,44,209),(0,0,0),(0,26,212),(0,39,210),(0,0,0),(0,0,0),(7,40,209),(0,16,213),(1,16,213),(0,0,0),(2,26,212),(2,39,210),(0,0,0),(0,0,0),(4,48,208),(2,16,213),(0,147,155),(0,0,0),(4,56,206),(3,33,211),(0,0,0),(0,0,0),(3,138,163),(0,85,196),(1,85,196),(0,0,0),(3,44,209),(5,24,212),(0,0,0),(0,0,0),(0,132,168),(1,132,168),(6,65,203),(0,0,0),(0,124,174),(1,124,174),(0,0,0),(0,0,0),(2,132,168),(8,91,192),(0,17,213),(0,0,0),(2,124,174),(3,147,155),(0,0,0),(0,0,0),(12,140,156),(0,49,208),(1,49,208),(0,0,0),(0,112,182),(1,112,182),(0,0,0),(0,0,0),(4,118,178),(0,27,212),(0,107,185),(0,0,0),(2,112,182),(0,34,211),(0,0,0),(0,0,0),(7,61,204),(2,27,212),(2,107,185),(0,0,0),(4,26,212),(0,57,206),(0,0,0),(0,0,0),(6,84,196),(4,16,213),(5,14,213),(0,0,0),(3,49,208),(0,18,213),(0,0,0),(0,0,0),(8,72,200),(0,96,191),(0,67,203),(0,0,0),(0,40,210),(1,40,210),(0,0,0),(0,0,0),(0,70,202),(1,70,202),(0,45,209),(0,0,0),(2,40,210),(8,26,211),(0,0,0),(0,0,0),(0,64,204),(0,92,193),(1,92,193),(0,0,0),(4,124,174),(8,87,194),(0,0,0),(0,0,0),(2,64,204),(0,100,189),(0,131,169),(0,0,0),(3,96,191),(3,67,203),(0,0,0),(0,0,0),(0,28,212),(0,120,177),(0,19,213),(0,0,0),(4,112,182),(3,45,209),(0,0,0),(0,0,0),(0,90,194),(0,109,184),(1,109,184),(0,0,0),(3,92,193),(4,34,211),(0,0,0),(0,0,0),(2,90,194),(2,109,184),(0,35,211),(0,0,0),(0,102,188),(1,102,188),(0,0,0),(0,0,0),(10,56,204),(10,97,188),(0,123,175),(0,0,0),(2,102,188),(0,114,181),(0,0,0),(0,0,0),(6,38,210),(4,96,191),(2,123,175),(0,0,0),(0,50,208),(0,54,207),(0,0,0),(0,0,0),(4,70,202),(0,20,213),(1,20,213),(0,0,0),(2,50,208),(2,54,207),(0,0,0),(0,0,0),(0,76,200),(1,76,200),(8,115,179),(0,0,0),(8,18,212),(0,41,210),(0,0,0),(0,0,0),(2,76,200),(0,29,212),(1,29,212),(0,0,0),(6,56,206),(2,41,210),(0,0,0),(0,0,0),(3,54,207),(2,29,212),(4,19,213),(0,0,0),(0,0,214),(0,1,214),(0,0,0),(0,0,0),(0,2,214),(1,2,214),(0,141,161),(0,0,0),(2,0,214),(0,3,214),(0,0,0),(0,0,0),(2,2,214),(10,60,203),(0,21,213),(0,0,0),(0,4,214),(1,4,214),(0,0,0),(0,0,0),(7,23,212),(0,36,211),(1,36,211),(0,0,0),(2,4,214),(0,5,214),(0,0,0),(0,0,0),(3,1,214),(2,36,211),(6,33,211),(0,0,0),(4,50,208),(2,5,214),(0,0,0),(0,0,0),(0,6,214),(0,68,203),(1,68,203),(0,0,0),(6,26,212),(3,21,213),(0,0,0),(0,0,0),(2,6,214),(0,65,204),(0,79,199),(0,0,0),(0,30,212),(0,7,214),(0,0,0),(0,0,0),(3,5,214),(2,65,204),(2,79,199),(0,0,0),(2,30,212),(0,22,213),(0,0,0),(0,0,0),(0,116,180),(1,116,180),(13,35,206),(0,0,0),(0,8,214),(1,8,214),(0,0,0),(0,0,0),(0,42,210),(0,51,208),(1,51,208),(0,0,0),(2,8,214),(0,62,205),(0,0,0),(0,0,0),(2,42,210),(2,51,208),(0,55,207),(0,0,0),(4,4,214),(0,9,214),(0,0,0),(0,0,0),(3,22,213),(4,36,211),(0,129,171),(0,0,0),(6,112,182),(2,9,214),(0,0,0),(0,0,0),(7,32,211),(0,95,192),(0,37,211),(0,0,0),(3,51,208),(0,113,182),(0,0,0),(0,0,0),(0,10,214),(1,10,214),(0,23,213),(0,0,0),(7,89,194),(0,99,190),(0,0,0),(0,0,0),(2,10,214),(0,31,212),(1,31,212),(0,0,0),(4,30,212),(0,150,153),(0,0,0),(0,0,0),(7,25,212),(0,133,168),(1,133,168),(0,0,0),(3,95,192),(0,11,214),(0,0,0),(0,0,0),(3,113,182),(2,133,168),(0,101,189),(0,0,0),(4,8,214),(2,11,214),(0,0,0),(0,0,0),(0,82,198),(0,77,200),(1,77,200),(0,0,0),(3,31,212),(4,62,205),(0,0,0),(0,0,0),(2,82,198),(2,77,200),(4,55,207),(0,0,0),(0,12,214),(1,12,214),(0,0,0),(0,0,0),(3,11,214),(0,24,213),(0,89,195),(0,0,0),(2,12,214),(0,43,210),(0,0,0),(0,0,0),(6,90,194),(0,103,188),(1,103,188),(0,0,0),(0,110,184),(1,110,184),(0,0,0),(0,0,0),(4,10,214),(2,103,188),(4,23,213),(0,0,0),(2,110,184),(0,13,214),(0,0,0),(0,0,0),(0,32,212),(1,32,212),(0,69,203),(0,0,0),(0,66,204),(1,66,204),(0,0,0),(0,0,0),(2,32,212),(4,133,168),(2,69,203),(0,0,0),(2,66,204),(4,11,214),(0,0,0),(0,0,0),(7,85,196),(0,48,209),(0,115,181),(0,0,0),(0,72,202),(0,145,158),(0,0,0),(0,0,0),(0,14,214),(1,14,214),(0,25,213),(0,0,0),(2,72,202),(2,145,158),(0,0,0),(0,0,0)]

def wits_46 : List (ℕ × ℕ × ℕ) := [(2,14,214),(0,80,199),(1,80,199),(0,0,0),(4,12,214),(10,22,211),(0,0,0),(0,0,0),(7,49,208),(2,80,199),(4,89,195),(0,0,0),(3,48,209),(3,115,181),(0,0,0),(0,0,0),(3,145,158),(0,144,159),(1,144,159),(0,0,0),(4,110,184),(0,15,214),(0,0,0),(0,0,0),(8,134,166),(2,144,159),(0,75,201),(0,0,0),(3,80,199),(2,15,214),(0,0,0),(0,0,0),(4,32,212),(0,33,212),(0,85,197),(0,0,0),(0,44,210),(1,44,210),(0,0,0),(0,0,0),(7,96,191),(2,33,212),(0,39,211),(0,0,0),(2,44,210),(0,26,213),(0,0,0),(0,0,0),(3,15,214),(0,143,160),(1,143,160),(0,0,0),(0,16,214),(1,16,214),(0,0,0),(0,0,0),(4,14,214),(2,143,160),(0,127,173),(0,0,0),(2,16,214),(0,131,170),(0,0,0),(0,0,0),(7,100,189),(4,80,199),(2,127,173),(0,0,0),(19,20,197),(2,131,170),(0,0,0),(0,0,0),(3,26,213),(0,53,208),(1,53,208),(0,0,0),(3,143,160),(8,14,213),(0,0,0),(0,0,0),(0,96,192),(1,96,192),(0,49,209),(0,0,0),(0,78,200),(0,17,214),(0,0,0),(0,0,0),(2,96,192),(0,117,180),(1,117,180),(0,0,0),(2,78,200),(0,83,198),(0,0,0),(0,0,0),(20,136,140),(2,117,180),(0,27,213),(0,0,0),(0,34,212),(1,34,212),(0,0,0),(0,0,0),(11,63,202),(0,67,204),(0,109,185),(0,0,0),(2,34,212),(0,70,203),(0,0,0),(0,0,0),(3,17,214),(2,67,204),(0,135,167),(0,0,0),(3,117,180),(2,70,203),(0,0,0),(0,0,0),(0,18,214),(0,40,211),(1,40,211),(0,0,0),(7,41,210),(0,45,210),(0,0,0),(0,0,0),(2,18,214),(2,40,211),(10,93,191),(0,0,0),(3,67,204),(0,73,202),(0,0,0),(0,0,0),(3,70,203),(4,53,208),(6,101,189),(0,0,0),(7,1,214),(0,130,171),(0,0,0),(0,0,0),(4,96,192),(6,77,200),(4,49,209),(0,0,0),(3,40,211),(2,130,171),(0,0,0),(0,0,0),(0,126,174),(0,28,213),(1,28,213),(0,0,0),(6,12,214),(0,19,214),(0,0,0),(0,0,0),(0,88,196),(1,88,196),(0,81,199),(0,0,0),(4,34,212),(2,19,214),(0,0,0),(0,0,0),(2,88,196),(0,35,212),(1,35,212),(0,0,0),(6,110,184),(4,70,203),(0,0,0),(0,0,0),(7,68,203),(0,76,201),(1,76,201),(0,0,0),(0,54,208),(0,50,209),(0,0,0),(0,0,0),(3,19,214),(2,76,201),(5,131,170),(0,0,0),(2,54,208),(2,50,209),(0,0,0),(0,0,0),(11,85,194),(12,28,209),(13,106,181),(0,0,0),(0,20,214),(1,20,214),(0,0,0),(0,0,0),(10,16,212),(6,48,209),(0,41,211),(0,0,0),(2,20,214),(0,86,197),(0,0,0),(0,0,0),(0,152,152),(1,152,152),(0,29,213),(0,0,0),(7,62,205),(0,58,207),(0,0,0),(0,0,0),(0,46,210),(0,116,181),(1,116,181),(0,0,0),(7,9,214),(2,58,207),(0,0,0),(0,0,0),(2,46,210),(0,0,215),(0,1,215),(0,0,0),(12,20,210),(0,2,215),(0,0,0),(0,0,0),(3,86,197),(2,0,215),(0,3,215),(0,0,0),(7,113,182),(0,21,214),(0,0,0),(0,0,0),(0,36,212),(0,4,215),(1,4,215),(0,0,0),(3,116,181),(2,21,214),(0,0,0),(0,0,0),(2,36,212),(2,4,215),(0,5,215),(0,0,0),(3,0,215),(3,1,215),(0,0,0),(0,0,0),(3,2,215),(14,48,203),(0,113,183),(0,0,0),(0,84,198),(0,6,215),(0,0,0),(0,0,0),(3,21,214),(6,143,160),(2,113,183),(0,0,0),(2,84,198),(0,30,213),(0,0,0),(0,0,0),(4,152,152),(0,97,192),(0,7,215),(0,0,0),(8,50,208),(2,30,213),(0,0,0),(0,0,0),(0,22,214),(1,22,214),(0,51,209),(0,0,0),(10,128,170),(0,42,211),(0,0,0),(0,0,0),(2,22,214),(0,8,215),(1,8,215),(0,0,0),(7,43,210),(2,42,211),(0,0,0),(0,0,0),(3,30,213),(2,8,215),(4,3,215),(0,0,0),(3,97,192),(0,101,190),(0,0,0),(0,0,0),(4,36,212),(4,4,215),(0,9,215),(0,0,0),(7,13,214),(0,47,210),(0,0,0),(0,0,0),(3,42,211),(0,37,212),(1,37,212),(0,0,0),(3,8,215),(2,47,210),(0,0,0),(0,0,0),(19,94,175),(2,37,212),(4,113,183),(0,0,0),(0,118,180),(0,10,215),(0,0,0),(0,0,0),(3,101,190),(7,115,181),(0,31,213),(0,0,0),(2,118,180),(2,10,215),(0,0,0),(0,0,0),(0,144,160),(0,89,196),(1,89,196),(0,0,0),(3,37,212),(5,46,210),(0,0,0),(0,0,0),(2,144,160),(2,89,196),(0,11,215),(0,0,0),(15,42,203),(0,115,182),(0,0,0),(0,0,0),(0,124,176),(1,124,176),(2,11,215),(0,0,0),(8,30,212),(2,115,182),(0,0,0),(0,0,0),(2,124,176),(10,145,156),(5,21,214),(0,0,0),(3,89,196),(4,101,190),(0,0,0),(0,0,0),(6,126,174),(0,12,215),(0,43,211),(0,0,0),(0,24,214),(1,24,214),(0,0,0),(0,0,0),(3,115,182),(0,69,204),(0,87,197),(0,0,0),(2,24,214),(0,66,205),(0,0,0),(0,0,0),(11,62,203),(0,52,209),(1,52,209),(0,0,0),(0,38,212),(1,38,212),(0,0,0),(0,0,0),(7,143,160),(0,32,213),(0,13,215),(0,0,0),(2,38,212),(3,43,211),(0,0,0),(0,0,0),(0,56,208),(1,56,208),(0,131,171),(0,0,0),(0,48,210),(0,63,206),(0,0,0),(0,0,0),(0,142,162),(1,142,162),(2,131,171),(0,0,0),(2,48,210),(2,63,206),(0,0,0),(0,0,0),(2,142,162),(8,31,212),(0,107,187),(0,0,0),(3,32,213),(0,14,215),(0,0,0),(0,0,0),(6,152,152),(7,49,209),(2,107,187),(0,0,0),(7,17,214),(0,75,202),(0,0,0),(0,0,0),(3,63,206),(4,12,215),(4,43,211),(0,0,0),(4,24,214),(2,75,202),(0,0,0),(0,0,0),(8,82,198),(0,120,179),(1,120,179),(0,0,0),(11,13,212),(3,107,187),(0,0,0),(0,0,0),(3,14,215),(0,60,207),(0,15,215),(0,0,0),(4,38,212),(6,21,214),(0,0,0),(0,0,0),(3,75,202),(0,44,211),(0,33,213),(0,0,0),(10,62,204),(5,144,160),(0,0,0),(0,0,0),(4,56,208),(0,39,212),(1,39,212),(0,0,0),(0,98,192),(1,98,192),(0,0,0),(0,0,0),(0,26,214),(1,26,214),(5,115,182),(0,0,0),(2,98,192),(0,109,186),(0,0,0),(0,0,0),(2,26,214),(0,16,215),(1,16,215),(0,0,0),(0,130,172),(0,78,201),(0,0,0),(0,0,0),(34,28,80),(0,92,195),(0,53,209),(0,0,0),(2,130,172),(2,78,201),(0,0,0),(0,0,0),(0,140,164),(1,140,164),(2,53,209),(0,0,0),(7,19,214),(0,49,210),(0,0,0),(0,0,0),(0,102,190),(1,102,190),(5,66,205),(0,0,0),(3,16,215),(2,49,210),(0,0,0),(0,0,0),(2,102,190),(0,57,208),(0,17,215),(0,0,0),(0,70,204),(0,134,169),(0,0,0),(0,0,0),(7,76,201),(2,57,208),(2,17,215),(0,0,0),(2,70,204),(0,27,214),(0,0,0),(0,0,0),(3,49,210),(4,39,212),(5,63,206),(0,0,0),(0,64,206),(1,64,206),(0,0,0),(0,0,0),(4,26,214),(0,104,189),(0,73,203),(0,0,0),(2,64,206),(3,17,215),(0,0,0),(0,0,0),(0,40,212),(1,40,212),(0,45,211),(0,0,0),(4,130,172),(0,18,215),(0,0,0),(0,0,0),(2,40,212),(0,88,197),(1,88,197),(0,0,0),(7,58,207),(2,18,215),(0,0,0),(0,0,0),(4,140,164),(0,81,200),(1,81,200),(0,0,0),(3,104,189),(3,73,203),(0,0,0),(0,0,0),(0,122,178),(1,122,178),(0,61,207),(0,0,0),(7,2,215),(0,147,158),(0,0,0),(0,0,0),(2,122,178),(4,57,208),(2,61,207),(0,0,0),(0,28,214),(1,28,214),(0,0,0),(0,0,0),(7,4,215),(6,12,215),(0,19,215),(0,0,0),(2,28,214),(0,133,170),(0,0,0),(0,0,0),(8,96,192),(5,98,192),(0,35,213),(0,0,0),(4,64,206),(0,54,209),(0,0,0),(0,0,0),(0,50,210),(0,125,176),(1,125,176),(0,0,0),(6,38,212),(2,54,209),(0,0,0),(0,0,0),(2,50,210),(2,125,176),(4,45,211),(0,0,0),(7,30,213),(3,19,215),(0,0,0),(0,0,0),(3,133,170),(4,88,197),(6,131,171),(0,0,0),(6,48,210),(3,35,213),(0,0,0),(0,0,0),(3,54,209),(0,20,215),(1,20,215),(0,0,0),(0,58,208),(1,58,208),(0,0,0),(0,0,0),(4,122,178),(0,108,187),(1,108,187),(0,0,0),(2,58,208),(0,29,214),(0,0,0),(0,0,0),(15,1,208),(2,108,187),(0,79,201),(0,0,0),(4,28,214),(2,29,214),(0,0,0),(0,0,0),(10,132,168),(0,68,205),(1,68,205),(0,0,0),(3,20,215),(4,133,170),(0,0,0),(0,0,0),(0,0,216),(0,1,216),(0,97,193),(0,0,0),(0,2,216),(0,65,206),(0,0,0),(0,0,0),(2,0,216),(0,3,216),(0,21,215),(0,0,0),(2,2,216),(2,65,206),(0,0,0),(0,0,0),(0,4,216),(1,4,216),(0,93,195),(0,0,0),(3,68,205),(10,34,211),(0,0,0),(0,0,0),(2,4,216),(0,5,216),(0,101,191),(0,0,0),(3,1,216),(0,74,203),(0,0,0),(0,0,0),(3,65,206),(2,5,216),(2,101,191),(0,0,0),(0,6,216),(0,62,207),(0,0,0),(0,0,0),(0,30,214),(0,91,196),(1,91,196),(0,0,0),(2,6,216),(0,51,210),(0,0,0),(0,0,0),(2,30,214),(0,7,216),(0,55,209),(0,0,0),(0,42,212),(0,22,215),(0,0,0),(0,0,0),(3,74,203),(2,7,216),(0,115,183),(0,0,0),(2,42,212),(2,22,215),(0,0,0),(0,0,0),(0,8,216),(1,8,216),(2,115,183),(0,0,0),(0,82,200),(1,82,200),(0,0,0),(0,0,0),(2,8,216),(4,3,216),(0,47,211),(0,0,0),(2,82,200),(0,77,202),(0,0,0),(0,0,0),(3,22,215),(0,9,216),(0,37,213),(0,0,0),(20,18,196),(2,77,202),(0,0,0),(0,0,0),(11,143,158),(0,59,208),(0,105,189),(0,0,0),(6,64,206),(4,74,203),(0,0,0),(0,0,0),(8,36,212),(2,59,208),(0,23,215),(0,0,0),(0,10,216),(0,31,214),(0,0,0),(0,0,0),(3,77,202),(4,91,196),(2,23,215),(0,0,0),(2,10,216),(2,31,214),(0,0,0),(0,0,0),(26,74,154),(0,112,185),(1,112,185),(0,0,0),(3,59,208),(0,87,198),(0,0,0),(0,0,0),(10,76,200),(0,11,216),(1,11,216),(0,0,0),(14,40,206),(2,87,198),(0,0,0),(0,0,0),(3,31,214),(2,11,216),(0,69,205),(0,0,0),(4,82,200),(6,147,158),(0,0,0),(0,0,0),(0,66,206),(0,43,212),(1,43,212),(0,0,0),(3,112,185),(4,77,202),(0,0,0),(0,0,0),(0,12,216),(0,24,215),(1,24,215),(0,0,0),(0,52,210),(1,52,210),(0,0,0),(0,0,0),(2,12,216),(2,24,215),(4,105,189),(0,0,0),(2,52,210),(0,38,213),(0,0,0),(0,0,0),(6,50,210),(0,56,209),(0,63,207),(0,0,0),(0,32,214),(1,32,214),(0,0,0),(0,0,0),(7,16,215),(0,13,216),(0,85,199),(0,0,0),(2,32,214),(0,130,173),(0,0,0),(0,0,0),(7,92,195),(2,13,216),(0,75,203),(0,0,0),(0,150,156),(1,150,156),(0,0,0),(0,0,0),(3,38,213),(4,11,216),(2,75,203),(0,0,0),(2,150,156),(3,63,207),(0,0,0),(0,0,0),(8,144,160),(5,82,200),(0,25,215),(0,0,0),(0,14,216),(0,98,193),(0,0,0),(0,0,0),(0,134,170),(1,134,170),(2,25,215),(0,0,0),(2,14,216),(0,94,195),(0,0,0),(0,0,0),(0,60,208),(1,60,208),(14,21,209),(0,0,0),(0,148,158),(1,148,158),(0,0,0),(0,0,0),(2,60,208),(6,1,216),(6,97,193),(0,0,0),(2,148,158),(0,139,166),(0,0,0),(0,0,0),(0,44,212),(0,15,216),(1,15,216),(0,0,0),(4,32,214),(0,33,214),(0,0,0),(0,0,0),(0,78,202),(0,83,200),(0,39,213),(0,0,0),(7,18,215),(2,33,214),(0,0,0),(0,0,0),(2,78,202),(2,83,200),(2,39,213),(0,0,0),(4,150,156),(0,26,215),(0,0,0),(0,0,0),(3,139,166),(8,32,213),(8,13,215),(0,0,0),(3,15,216),(0,53,210),(0,0,0),(0,0,0),(0,16,216),(1,16,216),(4,25,215),(0,0,0),(0,104,190),(0,111,186),(0,0,0),(0,0,0),(2,16,216),(6,7,216),(0,49,211),(0,0,0),(2,104,190),(0,67,206),(0,0,0),(0,0,0),(3,26,215),(5,52,210),(0,57,209),(0,0,0),(4,148,158),(0,138,167),(0,0,0),(0,0,0),(3,53,210),(7,35,213),(2,57,209),(0,0,0),(6,82,200),(2,138,167),(0,0,0),(0,0,0),(3,111,186),(0,17,216),(0,145,161),(0,0,0),(0,88,198),(1,88,198),(0,0,0),(0,0,0),(0,34,214),(1,34,214),(0,27,215),(0,0,0),(2,88,198),(0,106,189),(0,0,0),(0,0,0),(2,34,214),(5,150,156),(0,81,201),(0,0,0),(19,36,197),(2,106,189),(0,0,0),(0,0,0),(7,20,215),(0,40,213),(1,40,213),(0,0,0),(3,17,216),(3,145,161),(0,0,0),(0,0,0),(4,16,216),(2,40,213),(5,98,193),(0,0,0),(0,18,216),(1,18,216),(0,0,0),(0,0,0),(3,106,189),(0,61,208),(1,61,208),(0,0,0),(2,18,216),(3,81,201),(0,0,0),(0,0,0),(7,68,205),(0,137,168),(0,113,185),(0,0,0),(3,40,213),(0,86,199),(0,0,0),(0,0,0)]

def wits_47 : List (ℕ × ℕ × ℕ) := [(7,1,216),(2,137,168),(2,113,185),(0,0,0),(7,65,206),(2,86,199),(0,0,0),(0,0,0),(0,108,188),(0,28,215),(1,28,215),(0,0,0),(3,61,208),(5,78,202),(0,0,0),(0,0,0),(0,54,210),(0,19,216),(0,143,163),(0,0,0),(3,137,168),(0,35,214),(0,0,0),(0,0,0),(2,54,210),(2,19,216),(2,143,163),(0,0,0),(7,74,203),(2,35,214),(0,0,0),(0,0,0),(14,32,208),(4,40,213),(5,53,210),(0,0,0),(3,28,215),(5,16,216),(0,0,0),(0,0,0),(7,91,196),(0,121,180),(1,121,180),(0,0,0),(3,19,216),(0,58,209),(0,0,0),(0,0,0),(0,118,182),(1,118,182),(0,41,213),(0,0,0),(6,150,156),(2,58,209),(0,0,0),(0,0,0),(0,20,216),(0,136,169),(1,136,169),(0,0,0),(0,46,212),(1,46,212),(0,0,0),(0,0,0),(2,20,216),(0,93,196),(0,29,215),(0,0,0),(2,46,212),(0,110,187),(0,0,0),(0,0,0),(3,58,209),(2,93,196),(0,65,207),(0,0,0),(7,77,202),(2,110,187),(0,0,0),(0,0,0),(4,54,210),(0,115,184),(1,115,184),(0,0,0),(3,136,169),(4,35,214),(0,0,0),(0,0,0),(7,59,208),(0,0,217),(0,1,217),(0,0,0),(0,36,214),(0,2,217),(0,0,0),(0,0,0),(3,110,187),(0,21,216),(0,3,217),(0,0,0),(2,36,214),(2,2,217),(0,0,0),(0,0,0),(6,78,202),(0,4,217),(0,141,165),(0,0,0),(0,62,208),(1,62,208),(0,0,0),(0,0,0),(4,118,182),(2,4,217),(0,5,217),(0,0,0),(2,62,208),(3,1,217),(0,0,0),(0,0,0),(3,2,217),(4,136,169),(0,51,211),(0,0,0),(3,21,216),(0,6,217),(0,0,0),(0,0,0),(6,16,216),(0,152,155),(1,152,155),(0,0,0),(3,4,217),(0,42,213),(0,0,0),(0,0,0),(7,43,212),(0,151,156),(0,7,217),(0,0,0),(0,22,216),(1,22,216),(0,0,0),(0,0,0),(7,24,215),(2,151,156),(2,7,217),(0,0,0),(2,22,216),(0,150,157),(0,0,0),(0,0,0),(3,6,217),(0,8,217),(1,8,217),(0,0,0),(0,140,166),(1,140,166),(0,0,0),(0,0,0),(3,42,213),(0,120,181),(0,59,209),(0,0,0),(2,140,166),(0,37,214),(0,0,0),(0,0,0),(6,34,214),(2,120,181),(0,9,217),(0,0,0),(4,62,208),(2,37,214),(0,0,0),(0,0,0),(0,130,174),(1,130,174),(0,117,183),(0,0,0),(3,8,217),(5,20,216),(0,0,0),(0,0,0),(2,130,174),(0,23,216),(0,31,215),(0,0,0),(3,120,181),(0,10,217),(0,0,0),(0,0,0),(3,37,214),(2,23,216),(2,31,215),(0,0,0),(6,18,216),(0,69,206),(0,0,0),(0,0,0),(11,62,205),(4,151,156),(4,7,217),(0,0,0),(0,80,202),(0,66,207),(0,0,0),(0,0,0),(8,30,214),(0,72,205),(0,11,217),(0,0,0),(2,80,202),(2,66,207),(0,0,0),(0,0,0),(3,10,217),(2,72,205),(0,43,213),(0,0,0),(4,140,166),(0,114,185),(0,0,0),(0,0,0),(3,69,206),(0,52,211),(1,52,211),(0,0,0),(7,33,214),(2,114,185),(0,0,0),(0,0,0),(0,24,216),(0,12,217),(1,12,217),(0,0,0),(0,56,210),(0,146,161),(0,0,0),(0,0,0),(0,38,214),(0,75,204),(1,75,204),(0,0,0),(2,56,210),(2,146,161),(0,0,0),(0,0,0),(0,48,212),(0,32,215),(1,32,215),(0,0,0),(0,94,196),(1,94,196),(0,0,0),(0,0,0),(2,48,212),(2,32,215),(0,13,217),(0,0,0),(2,94,196),(4,69,206),(0,0,0),(0,0,0),(3,146,161),(5,22,216),(0,129,175),(0,0,0),(0,102,192),(0,145,162),(0,0,0),(0,0,0),(6,20,216),(0,92,197),(1,92,197),(0,0,0),(2,102,192),(2,145,162),(0,0,0),(0,0,0),(10,22,214),(0,25,216),(1,25,216),(0,0,0),(0,122,180),(0,14,217),(0,0,0),(0,0,0),(7,17,216),(2,25,216),(0,83,201),(0,0,0),(2,122,180),(0,78,203),(0,0,0),(0,0,0),(3,145,162),(0,104,191),(1,104,191),(0,0,0),(3,92,197),(2,78,203),(0,0,0),(0,0,0),(0,90,198),(0,44,213),(1,44,213),(0,0,0),(3,25,216),(0,125,178),(0,0,0),(0,0,0),(0,116,184),(1,116,184),(0,15,217),(0,0,0),(4,94,196),(0,39,214),(0,0,0),(0,0,0),(2,116,184),(6,4,217),(2,15,217),(0,0,0),(3,104,191),(2,39,214),(0,0,0),(0,0,0),(7,61,208),(5,80,202),(0,53,211),(0,0,0),(0,26,216),(1,26,216),(0,0,0),(0,0,0),(0,70,206),(1,70,206),(0,67,207),(0,0,0),(2,26,216),(3,15,217),(0,0,0),(0,0,0),(2,70,206),(0,16,217),(1,16,217),(0,0,0),(4,122,180),(0,57,210),(0,0,0),(0,0,0),(7,28,215),(0,132,173),(0,73,205),(0,0,0),(6,22,216),(2,57,210),(0,0,0),(0,0,0),(0,64,208),(1,64,208),(2,73,205),(0,0,0),(7,35,214),(0,81,202),(0,0,0),(0,0,0),(2,64,208),(4,44,213),(10,43,211),(0,0,0),(3,16,217),(2,81,202),(0,0,0),(0,0,0),(3,57,210),(5,94,196),(0,17,217),(0,0,0),(3,132,173),(0,34,215),(0,0,0),(0,0,0),(7,121,180),(0,27,216),(1,27,216),(0,0,0),(7,58,209),(0,142,165),(0,0,0),(0,0,0),(0,76,204),(1,76,204),(0,45,213),(0,0,0),(0,40,214),(1,40,214),(0,0,0),(0,0,0),(2,76,204),(6,23,216),(0,61,209),(0,0,0),(2,40,214),(3,17,217),(0,0,0),(0,0,0),(3,34,215),(4,16,217),(2,61,209),(0,0,0),(3,27,216),(0,18,217),(0,0,0),(0,0,0),(3,142,165),(0,124,179),(1,124,179),(0,0,0),(6,80,202),(2,18,217),(0,0,0),(0,0,0),(4,64,208),(2,124,179),(6,11,217),(0,0,0),(8,104,190),(3,61,209),(0,0,0),(0,0,0),(0,154,154),(1,154,154),(0,97,195),(0,0,0),(7,2,217),(0,54,211),(0,0,0),(0,0,0),(0,28,216),(0,95,196),(1,95,196),(0,0,0),(0,50,212),(1,50,212),(0,0,0),(0,0,0),(2,28,216),(2,95,196),(0,19,217),(0,0,0),(2,50,212),(4,142,165),(0,0,0),(0,0,0),(4,76,204),(0,84,201),(0,93,197),(0,0,0),(4,40,214),(3,97,195),(0,0,0),(0,0,0),(0,58,210),(1,58,210),(0,135,171),(0,0,0),(3,95,196),(8,106,189),(0,0,0),(0,0,0),(2,58,210),(0,68,207),(1,68,207),(0,0,0),(7,42,213),(0,41,214),(0,0,0),(0,0,0),(7,151,156),(2,68,207),(0,149,159),(0,0,0),(3,84,201),(0,46,213),(0,0,0),(0,0,0),(11,19,214),(0,20,217),(1,20,217),(0,0,0),(7,150,157),(2,46,213),(0,0,0),(0,0,0),(4,154,154),(0,29,216),(1,29,216),(0,0,0),(3,68,207),(0,74,205),(0,0,0),(0,0,0),(0,148,160),(1,148,160),(0,105,191),(0,0,0),(4,50,212),(2,74,205),(0,0,0),(0,0,0),(2,148,160),(0,112,187),(1,112,187),(0,0,0),(3,20,217),(5,76,204),(0,0,0),(0,0,0),(6,90,198),(0,36,215),(0,89,199),(0,0,0),(0,0,218),(0,1,218),(0,0,0),(0,0,0),(0,2,218),(0,123,180),(0,21,217),(0,0,0),(2,0,218),(0,3,218),(0,0,0),(0,0,0),(2,2,218),(2,123,180),(2,21,217),(0,0,0),(0,4,218),(1,4,218),(0,0,0),(0,0,0),(10,40,212),(0,51,212),(0,55,211),(0,0,0),(2,4,218),(0,5,218),(0,0,0),(0,0,0),(3,1,218),(2,51,212),(2,55,211),(0,0,0),(0,30,216),(1,30,216),(0,0,0),(0,0,0),(0,6,218),(1,6,218),(5,54,211),(0,0,0),(2,30,216),(4,74,205),(0,0,0),(0,0,0),(2,6,218),(0,87,200),(1,87,200),(0,0,0),(3,51,212),(0,7,218),(0,0,0),(0,0,0),(3,5,218),(2,87,200),(0,47,213),(0,0,0),(7,146,161),(0,59,210),(0,0,0),(0,0,0),(7,75,204),(4,36,215),(2,47,213),(0,0,0),(0,8,218),(1,8,218),(0,0,0),(0,0,0),(0,114,186),(1,114,186),(0,37,215),(0,0,0),(2,8,218),(4,3,218),(0,0,0),(0,0,0),(2,114,186),(6,27,216),(0,109,189),(0,0,0),(4,4,218),(0,9,218),(0,0,0),(0,0,0),(3,59,210),(0,80,203),(0,69,207),(0,0,0),(6,40,214),(2,9,218),(0,0,0),(0,0,0),(7,92,197),(0,31,216),(0,23,217),(0,0,0),(0,66,208),(1,66,208),(0,0,0),(0,0,0),(0,10,218),(1,10,218),(0,85,201),(0,0,0),(2,66,208),(0,98,195),(0,0,0),(0,0,0),(0,96,196),(1,96,196),(2,85,201),(0,0,0),(0,100,194),(1,100,194),(0,0,0),(0,0,0),(2,96,196),(8,152,155),(4,47,213),(0,0,0),(2,100,194),(0,11,218),(0,0,0),(0,0,0),(0,52,212),(1,52,212),(0,63,209),(0,0,0),(4,8,218),(0,102,193),(0,0,0),(0,0,0),(2,52,212),(0,56,211),(1,56,211),(0,0,0),(6,50,212),(2,102,193),(0,0,0),(0,0,0),(19,1,202),(0,24,217),(0,125,179),(0,0,0),(0,12,218),(0,38,215),(0,0,0),(0,0,0),(3,11,218),(0,48,213),(0,143,165),(0,0,0),(2,12,218),(2,38,215),(0,0,0),(0,0,0),(0,32,216),(0,116,185),(1,116,185),(0,0,0),(3,56,211),(5,6,218),(0,0,0),(0,0,0),(2,32,216),(2,116,185),(4,85,201),(0,0,0),(3,24,217),(0,13,218),(0,0,0),(0,0,0),(3,38,215),(7,73,205),(5,7,218),(0,0,0),(0,60,210),(0,90,199),(0,0,0),(0,0,0),(14,4,212),(6,20,217),(5,59,210),(0,0,0),(2,60,210),(2,90,199),(0,0,0),(0,0,0),(4,52,212),(0,128,177),(0,25,217),(0,0,0),(8,80,202),(0,106,191),(0,0,0),(0,0,0),(0,14,218),(1,14,218),(2,25,217),(0,0,0),(7,34,215),(2,106,191),(0,0,0),(0,0,0),(2,14,218),(4,24,217),(4,125,179),(0,0,0),(0,44,214),(1,44,214),(0,0,0),(0,0,0),(11,63,206),(0,136,171),(0,113,187),(0,0,0),(2,44,214),(0,154,155),(0,0,0),(0,0,0),(0,88,200),(0,33,216),(0,39,215),(0,0,0),(8,56,210),(0,15,218),(0,0,0),(0,0,0),(2,88,200),(0,53,212),(1,53,212),(0,0,0),(6,4,218),(2,15,218),(0,0,0),(0,0,0),(7,124,179),(2,53,212),(6,55,211),(0,0,0),(0,108,190),(0,26,217),(0,0,0),(0,0,0),(3,154,155),(10,112,185),(0,49,213),(0,0,0),(2,108,190),(2,26,217),(0,0,0),(0,0,0),(0,124,180),(0,64,209),(1,64,209),(0,0,0),(0,16,218),(0,150,159),(0,0,0),(0,0,0),(2,124,180),(2,64,209),(0,131,175),(0,0,0),(2,16,218),(2,150,159),(0,0,0),(0,0,0),(3,26,217),(5,12,218),(2,131,175),(0,0,0),(4,44,214),(0,86,201),(0,0,0),(0,0,0),(7,84,201),(0,76,205),(1,76,205),(0,0,0),(3,64,209),(2,86,201),(0,0,0),(0,0,0),(3,150,159),(0,135,172),(1,135,172),(0,0,0),(0,34,216),(0,17,218),(0,0,0),(0,0,0),(7,68,207),(2,135,172),(0,27,217),(0,0,0),(2,34,216),(0,45,214),(0,0,0),(0,0,0),(0,140,168),(0,40,215),(0,99,195),(0,0,0),(3,76,205),(2,45,214),(0,0,0),(0,0,0),(2,140,168),(2,40,215),(0,95,197),(0,0,0),(3,135,172),(0,101,194),(0,0,0),(0,0,0),(3,17,218),(4,64,209),(2,95,197),(0,0,0),(4,16,218),(2,101,194),(0,0,0),(0,0,0),(0,18,218),(1,18,218),(4,131,175),(0,0,0),(3,40,215),(0,93,198),(0,0,0),(0,0,0),(2,18,218),(0,79,204),(0,103,193),(0,0,0),(0,54,212),(1,54,212),(0,0,0),(0,0,0),(3,101,194),(2,79,204),(2,103,193),(0,0,0),(2,54,212),(0,50,213),(0,0,0),(0,0,0),(7,123,180),(0,28,217),(1,28,217),(0,0,0),(0,130,176),(1,130,176),(0,0,0),(0,0,0),(3,93,198),(0,35,216),(0,91,199),(0,0,0),(2,130,176),(0,19,218),(0,0,0),(0,0,0),(0,68,208),(0,105,192),(0,71,207),(0,0,0),(7,5,218),(2,19,218),(0,0,0),(0,0,0),(2,68,208),(2,105,192),(2,71,207),(0,0,0),(3,28,217),(4,101,194),(0,0,0),(0,0,0),(8,76,204),(5,16,218),(0,41,215),(0,0,0),(3,35,216),(3,91,199),(0,0,0),(0,0,0),(0,46,214),(1,46,214),(0,117,185),(0,0,0),(3,105,192),(0,126,179),(0,0,0),(0,0,0),(2,46,214),(0,89,200),(1,89,200),(0,0,0),(0,20,218),(1,20,218),(0,0,0),(0,0,0),(11,54,209),(2,89,200),(0,29,217),(0,0,0),(2,20,218),(0,82,203),(0,0,0),(0,0,0),(6,14,218),(4,28,217),(2,29,217),(0,0,0),(4,130,176),(2,82,203),(0,0,0),(0,0,0),(0,62,210),(1,62,210),(4,91,199),(0,0,0),(3,89,200),(4,19,218),(0,0,0),(0,0,0),(0,36,216),(1,36,216),(0,77,205),(0,0,0),(8,50,212),(3,29,217),(0,0,0),(0,0,0),(2,36,216),(0,0,219),(0,1,219),(0,0,0),(11,108,187),(0,2,219),(0,0,0),(0,0,0),(11,29,214),(0,55,212),(0,3,219),(0,0,0),(7,98,195),(2,2,219),(0,0,0),(0,0,0),(4,46,214),(0,4,219),(1,4,219),(0,0,0),(6,108,190),(0,109,190),(0,0,0),(0,0,0),(0,0,0)]

lemma check_wits_0 : checkList wits_0 0 = true := by decide

lemma check_wits_1 : checkList wits_1 1000 = true := by decide

lemma check_wits_2 : checkList wits_2 2000 = true := by decide

lemma check_wits_3 : checkList wits_3 3000 = true := by decide

lemma check_wits_4 : checkList wits_4 4000 = true := by decide

lemma check_wits_5 : checkList wits_5 5000 = true := by decide

lemma check_wits_6 : checkList wits_6 6000 = true := by decide

lemma check_wits_7 : checkList wits_7 7000 = true := by decide

lemma check_wits_8 : checkList wits_8 8000 = true := by decide

lemma check_wits_9 : checkList wits_9 9000 = true := by decide

lemma check_wits_10 : checkList wits_10 10000 = true := by decide

lemma check_wits_11 : checkList wits_11 11000 = true := by decide

lemma check_wits_12 : checkList wits_12 12000 = true := by decide

lemma check_wits_13 : checkList wits_13 13000 = true := by decide

lemma check_wits_14 : checkList wits_14 14000 = true := by decide

lemma check_wits_15 : checkList wits_15 15000 = true := by decide

lemma check_wits_16 : checkList wits_16 16000 = true := by decide

lemma check_wits_17 : checkList wits_17 17000 = true := by decide

lemma check_wits_18 : checkList wits_18 18000 = true := by decide

lemma check_wits_19 : checkList wits_19 19000 = true := by decide

lemma check_wits_20 : checkList wits_20 20000 = true := by decide

lemma check_wits_21 : checkList wits_21 21000 = true := by decide

lemma check_wits_22 : checkList wits_22 22000 = true := by decide

lemma check_wits_23 : checkList wits_23 23000 = true := by decide

lemma check_wits_24 : checkList wits_24 24000 = true := by decide

lemma check_wits_25 : checkList wits_25 25000 = true := by decide

lemma check_wits_26 : checkList wits_26 26000 = true := by decide

lemma check_wits_27 : checkList wits_27 27000 = true := by decide

lemma check_wits_28 : checkList wits_28 28000 = true := by decide

lemma check_wits_29 : checkList wits_29 29000 = true := by decide

lemma check_wits_30 : checkList wits_30 30000 = true := by decide

lemma check_wits_31 : checkList wits_31 31000 = true := by decide

lemma check_wits_32 : checkList wits_32 32000 = true := by decide

lemma check_wits_33 : checkList wits_33 33000 = true := by decide

lemma check_wits_34 : checkList wits_34 34000 = true := by decide

lemma check_wits_35 : checkList wits_35 35000 = true := by decide

lemma check_wits_36 : checkList wits_36 36000 = true := by decide

lemma check_wits_37 : checkList wits_37 37000 = true := by decide

lemma check_wits_38 : checkList wits_38 38000 = true := by decide

lemma check_wits_39 : checkList wits_39 39000 = true := by decide

lemma check_wits_40 : checkList wits_40 40000 = true := by decide

lemma check_wits_41 : checkList wits_41 41000 = true := by decide

lemma check_wits_42 : checkList wits_42 42000 = true := by decide

lemma check_wits_43 : checkList wits_43 43000 = true := by decide

lemma check_wits_44 : checkList wits_44 44000 = true := by decide

lemma check_wits_45 : checkList wits_45 45000 = true := by decide

lemma check_wits_46 : checkList wits_46 46000 = true := by decide

lemma check_wits_47 : checkList wits_47 47000 = true := by decide

lemma wits_0_length : wits_0.length = 1000 := rfl

lemma wits_1_length : wits_1.length = 1000 := rfl

lemma wits_2_length : wits_2.length = 1000 := rfl

lemma wits_3_length : wits_3.length = 1000 := rfl

lemma wits_4_length : wits_4.length = 1000 := rfl

lemma wits_5_length : wits_5.length = 1000 := rfl

lemma wits_6_length : wits_6.length = 1000 := rfl

lemma wits_7_length : wits_7.length = 1000 := rfl

lemma wits_8_length : wits_8.length = 1000 := rfl

lemma wits_9_length : wits_9.length = 1000 := rfl

lemma wits_10_length : wits_10.length = 1000 := rfl

lemma wits_11_length : wits_11.length = 1000 := rfl

lemma wits_12_length : wits_12.length = 1000 := rfl

lemma wits_13_length : wits_13.length = 1000 := rfl

lemma wits_14_length : wits_14.length = 1000 := rfl

lemma wits_15_length : wits_15.length = 1000 := rfl

lemma wits_16_length : wits_16.length = 1000 := rfl

lemma wits_17_length : wits_17.length = 1000 := rfl

lemma wits_18_length : wits_18.length = 1000 := rfl

lemma wits_19_length : wits_19.length = 1000 := rfl

lemma wits_20_length : wits_20.length = 1000 := rfl

lemma wits_21_length : wits_21.length = 1000 := rfl

lemma wits_22_length : wits_22.length = 1000 := rfl

lemma wits_23_length : wits_23.length = 1000 := rfl

lemma wits_24_length : wits_24.length = 1000 := rfl

lemma wits_25_length : wits_25.length = 1000 := rfl

lemma wits_26_length : wits_26.length = 1000 := rfl

lemma wits_27_length : wits_27.length = 1000 := rfl

lemma wits_28_length : wits_28.length = 1000 := rfl

lemma wits_29_length : wits_29.length = 1000 := rfl

lemma wits_30_length : wits_30.length = 1000 := rfl

lemma wits_31_length : wits_31.length = 1000 := rfl

lemma wits_32_length : wits_32.length = 1000 := rfl

lemma wits_33_length : wits_33.length = 1000 := rfl

lemma wits_34_length : wits_34.length = 1000 := rfl

lemma wits_35_length : wits_35.length = 1000 := rfl

lemma wits_36_length : wits_36.length = 1000 := rfl

lemma wits_37_length : wits_37.length = 1000 := rfl

lemma wits_38_length : wits_38.length = 1000 := rfl

lemma wits_39_length : wits_39.length = 1000 := rfl

lemma wits_40_length : wits_40.length = 1000 := rfl

lemma wits_41_length : wits_41.length = 1000 := rfl

lemma wits_42_length : wits_42.length = 1000 := rfl

lemma wits_43_length : wits_43.length = 1000 := rfl

lemma wits_44_length : wits_44.length = 1000 := rfl

lemma wits_45_length : wits_45.length = 1000 := rfl

lemma wits_46_length : wits_46.length = 1000 := rfl

lemma wits_47_length : wits_47.length = 985 := rfl

lemma easy_or_rep_le_47984 {n : ℕ} (hle : n ≤ 47984) :
    IsHard n ∨ n ∈ L18 ∨ IsCubeTwoSquares n := by
  by_cases h0 : n < 1000
  · exact checkList_spec wits_0 0 check_wits_0 n (by omega) (by rw [wits_0_length]; omega)
  by_cases h1 : n < 2000
  · exact checkList_spec wits_1 1000 check_wits_1 n (by omega) (by rw [wits_1_length]; omega)
  by_cases h2 : n < 3000
  · exact checkList_spec wits_2 2000 check_wits_2 n (by omega) (by rw [wits_2_length]; omega)
  by_cases h3 : n < 4000
  · exact checkList_spec wits_3 3000 check_wits_3 n (by omega) (by rw [wits_3_length]; omega)
  by_cases h4 : n < 5000
  · exact checkList_spec wits_4 4000 check_wits_4 n (by omega) (by rw [wits_4_length]; omega)
  by_cases h5 : n < 6000
  · exact checkList_spec wits_5 5000 check_wits_5 n (by omega) (by rw [wits_5_length]; omega)
  by_cases h6 : n < 7000
  · exact checkList_spec wits_6 6000 check_wits_6 n (by omega) (by rw [wits_6_length]; omega)
  by_cases h7 : n < 8000
  · exact checkList_spec wits_7 7000 check_wits_7 n (by omega) (by rw [wits_7_length]; omega)
  by_cases h8 : n < 9000
  · exact checkList_spec wits_8 8000 check_wits_8 n (by omega) (by rw [wits_8_length]; omega)
  by_cases h9 : n < 10000
  · exact checkList_spec wits_9 9000 check_wits_9 n (by omega) (by rw [wits_9_length]; omega)
  by_cases h10 : n < 11000
  · exact checkList_spec wits_10 10000 check_wits_10 n (by omega) (by rw [wits_10_length]; omega)
  by_cases h11 : n < 12000
  · exact checkList_spec wits_11 11000 check_wits_11 n (by omega) (by rw [wits_11_length]; omega)
  by_cases h12 : n < 13000
  · exact checkList_spec wits_12 12000 check_wits_12 n (by omega) (by rw [wits_12_length]; omega)
  by_cases h13 : n < 14000
  · exact checkList_spec wits_13 13000 check_wits_13 n (by omega) (by rw [wits_13_length]; omega)
  by_cases h14 : n < 15000
  · exact checkList_spec wits_14 14000 check_wits_14 n (by omega) (by rw [wits_14_length]; omega)
  by_cases h15 : n < 16000
  · exact checkList_spec wits_15 15000 check_wits_15 n (by omega) (by rw [wits_15_length]; omega)
  by_cases h16 : n < 17000
  · exact checkList_spec wits_16 16000 check_wits_16 n (by omega) (by rw [wits_16_length]; omega)
  by_cases h17 : n < 18000
  · exact checkList_spec wits_17 17000 check_wits_17 n (by omega) (by rw [wits_17_length]; omega)
  by_cases h18 : n < 19000
  · exact checkList_spec wits_18 18000 check_wits_18 n (by omega) (by rw [wits_18_length]; omega)
  by_cases h19 : n < 20000
  · exact checkList_spec wits_19 19000 check_wits_19 n (by omega) (by rw [wits_19_length]; omega)
  by_cases h20 : n < 21000
  · exact checkList_spec wits_20 20000 check_wits_20 n (by omega) (by rw [wits_20_length]; omega)
  by_cases h21 : n < 22000
  · exact checkList_spec wits_21 21000 check_wits_21 n (by omega) (by rw [wits_21_length]; omega)
  by_cases h22 : n < 23000
  · exact checkList_spec wits_22 22000 check_wits_22 n (by omega) (by rw [wits_22_length]; omega)
  by_cases h23 : n < 24000
  · exact checkList_spec wits_23 23000 check_wits_23 n (by omega) (by rw [wits_23_length]; omega)
  by_cases h24 : n < 25000
  · exact checkList_spec wits_24 24000 check_wits_24 n (by omega) (by rw [wits_24_length]; omega)
  by_cases h25 : n < 26000
  · exact checkList_spec wits_25 25000 check_wits_25 n (by omega) (by rw [wits_25_length]; omega)
  by_cases h26 : n < 27000
  · exact checkList_spec wits_26 26000 check_wits_26 n (by omega) (by rw [wits_26_length]; omega)
  by_cases h27 : n < 28000
  · exact checkList_spec wits_27 27000 check_wits_27 n (by omega) (by rw [wits_27_length]; omega)
  by_cases h28 : n < 29000
  · exact checkList_spec wits_28 28000 check_wits_28 n (by omega) (by rw [wits_28_length]; omega)
  by_cases h29 : n < 30000
  · exact checkList_spec wits_29 29000 check_wits_29 n (by omega) (by rw [wits_29_length]; omega)
  by_cases h30 : n < 31000
  · exact checkList_spec wits_30 30000 check_wits_30 n (by omega) (by rw [wits_30_length]; omega)
  by_cases h31 : n < 32000
  · exact checkList_spec wits_31 31000 check_wits_31 n (by omega) (by rw [wits_31_length]; omega)
  by_cases h32 : n < 33000
  · exact checkList_spec wits_32 32000 check_wits_32 n (by omega) (by rw [wits_32_length]; omega)
  by_cases h33 : n < 34000
  · exact checkList_spec wits_33 33000 check_wits_33 n (by omega) (by rw [wits_33_length]; omega)
  by_cases h34 : n < 35000
  · exact checkList_spec wits_34 34000 check_wits_34 n (by omega) (by rw [wits_34_length]; omega)
  by_cases h35 : n < 36000
  · exact checkList_spec wits_35 35000 check_wits_35 n (by omega) (by rw [wits_35_length]; omega)
  by_cases h36 : n < 37000
  · exact checkList_spec wits_36 36000 check_wits_36 n (by omega) (by rw [wits_36_length]; omega)
  by_cases h37 : n < 38000
  · exact checkList_spec wits_37 37000 check_wits_37 n (by omega) (by rw [wits_37_length]; omega)
  by_cases h38 : n < 39000
  · exact checkList_spec wits_38 38000 check_wits_38 n (by omega) (by rw [wits_38_length]; omega)
  by_cases h39 : n < 40000
  · exact checkList_spec wits_39 39000 check_wits_39 n (by omega) (by rw [wits_39_length]; omega)
  by_cases h40 : n < 41000
  · exact checkList_spec wits_40 40000 check_wits_40 n (by omega) (by rw [wits_40_length]; omega)
  by_cases h41 : n < 42000
  · exact checkList_spec wits_41 41000 check_wits_41 n (by omega) (by rw [wits_41_length]; omega)
  by_cases h42 : n < 43000
  · exact checkList_spec wits_42 42000 check_wits_42 n (by omega) (by rw [wits_42_length]; omega)
  by_cases h43 : n < 44000
  · exact checkList_spec wits_43 43000 check_wits_43 n (by omega) (by rw [wits_43_length]; omega)
  by_cases h44 : n < 45000
  · exact checkList_spec wits_44 44000 check_wits_44 n (by omega) (by rw [wits_44_length]; omega)
  by_cases h45 : n < 46000
  · exact checkList_spec wits_45 45000 check_wits_45 n (by omega) (by rw [wits_45_length]; omega)
  by_cases h46 : n < 47000
  · exact checkList_spec wits_46 46000 check_wits_46 n (by omega) (by rw [wits_46_length]; omega)
  exact checkList_spec wits_47 47000 check_wits_47 n (by omega) (by rw [wits_47_length]; omega)


lemma eight_dvd_of_mod8 {n : ℕ} (h : n % 8 = 0) : 8 ∣ n :=
  Nat.dvd_of_mod_eq_zero h

lemma easy_of_eight_mul_easy {m : ℕ} (he : IsEasy m) : IsEasy (8 * m) := by
  have : (8 * m) % 8 = 0 := Nat.mul_mod_right 8 m
  unfold IsEasy IsHard
  omega

lemma hard_of_eight_mul_hard {m : ℕ} (hh : IsHard m) : (8 * m) % 8 = 0 :=
  Nat.mul_mod_right 8 m

/-- `8` times an L18 number that exceeds `47984` is representable. -/
lemma rep_51360 : IsCubeTwoSquares 51360 := ⟨7, 29, 224, by norm_num⟩
lemma rep_80480 : IsCubeTwoSquares 80480 := ⟨31, 8, 225, by norm_num⟩
lemma rep_90560 : IsCubeTwoSquares 90560 := ⟨3, 202, 223, by norm_num⟩
lemma rep_94592 : IsCubeTwoSquares 94592 := ⟨3, 113, 286, by norm_num⟩
lemma rep_112064 : IsCubeTwoSquares 112064 := ⟨7, 205, 264, by norm_num⟩
lemma rep_126848 : IsCubeTwoSquares 126848 := ⟨7, 51, 352, by norm_num⟩
lemma rep_212352 : IsCubeTwoSquares 212352 := ⟨11, 114, 445, by norm_num⟩
lemma rep_230432 : IsCubeTwoSquares 230432 := ⟨7, 317, 360, by norm_num⟩
lemma rep_275136 : IsCubeTwoSquares 275136 := ⟨31, 137, 476, by norm_num⟩
lemma rep_383872 : IsCubeTwoSquares 383872 := ⟨11, 275, 554, by norm_num⟩

lemma rep_eight_L18 {m : ℕ} (hm : m ∈ L18) : IsCubeTwoSquares (8 * m) := by
  rw [mem_L18_iff] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    <;> subst hm
  · -- 960 ≤ 47984, use finite check
    have h := easy_or_rep_le_47984 (by norm_num : 8 * 120 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 312 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 813 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 2136 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 2680 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 3224 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 4404 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · have h := easy_or_rep_le_47984 (by norm_num : 8 * 5340 ≤ 47984)
    rcases h with h | h | h
    · unfold IsHard at h; omega
    · simp [L18] at h
    · exact h
  · exact rep_51360
  · exact rep_80480
  · exact rep_90560
  · exact rep_94592
  · exact rep_112064
  · exact rep_126848
  · exact rep_212352
  · exact rep_230432
  · exact rep_275136
  · exact rep_383872

/-- A number of special form is easy. -/
lemma special_is_easy {n : ℕ} (hf : has_form_two_pow_k_times_four_m_plus_one n) :
    IsEasy n :=
  fun hh => has_form_not_hard_mod8 hf hh

/-- If `2^s` divides `2^k * odd` with `odd` odd, then `s ≤ k`. -/
lemma two_pow_le_of_dvd_mul_odd {k s odd : ℕ} (hodd : Odd odd)
    (h : 2 ^ s ∣ 2 ^ k * odd) : s ≤ k := by
  by_contra hsk
  have hlt : k < s := Nat.lt_of_not_ge hsk
  obtain ⟨m, hm⟩ := h
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
  have : odd = 2 ^ (s - k) * m := by
    have hs : k + (s - k) = s := Nat.add_sub_of_le (Nat.le_of_lt hlt)
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 ^ k * odd = 2 ^ s * m := hm
      _ = 2 ^ (k + (s - k)) * m := by rw [hs]
      _ = 2 ^ k * 2 ^ (s - k) * m := by rw [pow_add]
      _ = 2 ^ k * (2 ^ (s - k) * m) := by rw [mul_assoc]
  have hskpos : 0 < s - k := Nat.sub_pos_of_lt hlt
  have : 2 ∣ odd := by
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hskpos)) _
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr this)

/-- Dividing a special-form multiple of 8 by 8 preserves special form. -/
lemma special_of_eight_mul_special {m : ℕ}
    (hf : has_form_two_pow_k_times_four_m_plus_one (8 * m)) :
    has_form_two_pow_k_times_four_m_plus_one m := by
  obtain ⟨k, t, heq⟩ := hf
  have hodd : Odd (4 * t + 1) := ⟨2 * t, by ring⟩
  have hdiv : 2 ^ 3 ∣ 2 ^ k * (4 * t + 1) := by
    refine ⟨m, ?_⟩
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [← this, heq]
  have hk : 3 ≤ k := two_pow_le_of_dvd_mul_odd hodd hdiv
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨k', t, ?_⟩
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8)
  calc 8 * m = 2 ^ (3 + k') * (4 * t + 1) := heq
    _ = 2 ^ 3 * 2 ^ k' * (4 * t + 1) := by rw [pow_add]
    _ = 8 * (2 ^ k' * (4 * t + 1)) := by rw [h8, mul_assoc]

/-- The set of sums of two squares is closed under multiplication. -/
lemma mem_S_mul_of_mem_S {a b : ℕ} (ha : ∃ x y, x ^ 2 + y ^ 2 = a)
    (hb : ∃ u v, u ^ 2 + v ^ 2 = b) : ∃ r s, r ^ 2 + s ^ 2 = a * b := by
  obtain ⟨x, y, hxy⟩ := ha
  obtain ⟨u, v, huv⟩ := hb
  obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul hxy.symm huv.symm
  exact ⟨r, s, hrs.symm⟩

lemma mem_S_mul_pow_two {s k : ℕ} (hs : ∃ y z, y ^ 2 + z ^ 2 = s) :
    ∃ y z, y ^ 2 + z ^ 2 = 2 ^ k * s := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h2 : ∃ u v, u ^ 2 + v ^ 2 = 2 := ⟨1, 1, by norm_num⟩
    obtain ⟨y, z, hyz⟩ := mem_S_mul_of_mem_S h2 ih
    refine ⟨y, z, ?_⟩
    convert hyz using 1
    ring

/-- Special-form numbers whose odd part is a sum of two squares are themselves
sums of two squares, hence representable. -/
lemma special_rep_of_odd_part_two_sq {k odd : ℕ}
    (_hodd : Odd odd) (hS : ∃ y z, y ^ 2 + z ^ 2 = odd) :
    IsCubeTwoSquares (2 ^ k * odd) := by
  obtain ⟨y, z, hyz⟩ := mem_S_mul_pow_two (k := k) (s := odd) hS
  exact IsCubeTwoSquares.of_two_sq hyz

/-- Every positive natural number has a unique 2-adic odd part. -/
lemma exists_odd_part : ∀ n : ℕ, n ≠ 0 → ∃ k odd, Odd odd ∧ n = 2 ^ k * odd := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases he : Even n
    · obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp [hm] at hn
      have hmlt : m < n := by
        have : 0 < m := Nat.pos_of_ne_zero hm0
        omega
      obtain ⟨k, odd, hodd, hmo⟩ := ih m hmlt hm0
      refine ⟨k + 1, odd, hodd, ?_⟩
      rw [hm, hmo]
      ring
    · exact ⟨0, n, Nat.not_even_iff_odd.mp he, by simp⟩

lemma has_form_of_mod8_one {n : ℕ} (h : n % 8 = 1) :
    has_form_two_pow_k_times_four_m_plus_one n := by
  have : n % 4 = 1 := by omega
  obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
  exact ⟨0, t, by simp [ht]⟩

lemma has_form_of_mod8_five {n : ℕ} (h : n % 8 = 5) :
    has_form_two_pow_k_times_four_m_plus_one n := by
  have : n % 4 = 1 := by omega
  obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
  exact ⟨0, t, by simp [ht]⟩

lemma has_form_of_mod8_two {n : ℕ} (h : n % 8 = 2) :
    has_form_two_pow_k_times_four_m_plus_one n := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨k, odd, hodd, hno⟩ := exists_odd_part n hn0
  have hk : k = 1 := by
    match k with
    | 0 =>
      have : n % 2 = 1 := by
        rw [hno]; simp
        exact Nat.odd_iff.mp hodd
      omega
    | 1 => rfl
    | k + 2 =>
      have : 4 ∣ n := by
        rw [hno, pow_add]
        refine ⟨2 ^ k * odd, by ring⟩
      have : n % 8 = 0 ∨ n % 8 = 4 := by omega
      omega
  subst hk
  have hodd1 : odd % 4 = 1 := by
    have : n = 2 * odd := by simpa using hno
    have : odd % 4 = 1 ∨ odd % 4 = 3 := by omega
    rcases this with h1 | h3
    · exact h1
    · have : n % 8 = 6 := by
        rw [hno]; simp; omega
      omega
  obtain ⟨t, ht⟩ : ∃ t, odd = 4 * t + 1 := ⟨odd / 4, by omega⟩
  exact ⟨1, t, by rw [hno, ht]⟩

lemma rep_of_mem_S_sub {n x : ℕ} (hx : x ^ 3 ≤ n)
    (hS : ∃ y z, y ^ 2 + z ^ 2 = n - x ^ 3) : IsCubeTwoSquares n := by
  obtain ⟨y, z, hyz⟩ := hS
  refine ⟨x, y, z, ?_⟩
  omega

/-- If `d` is a sum of two squares and `m` is a cube plus two squares, so is `d^3 * m`. -/
lemma IsCubeTwoSquares.mul_cube_of_two_sq {d m : ℕ}
    (hd : ∃ a b, a ^ 2 + b ^ 2 = d) (hm : IsCubeTwoSquares m) :
    IsCubeTwoSquares (d ^ 3 * m) := by
  obtain ⟨x, y, z, hxyz⟩ := hm
  have hd2 : ∃ r s, r ^ 2 + s ^ 2 = d * d := mem_S_mul_of_mem_S hd hd
  have hdyz : ∃ r s, r ^ 2 + s ^ 2 = d * (y ^ 2 + z ^ 2) :=
    mem_S_mul_of_mem_S hd ⟨y, z, rfl⟩
  obtain ⟨r, s, hrs⟩ := mem_S_mul_of_mem_S hd2 hdyz
  refine ⟨d * x, r, s, ?_⟩
  have hrs' : r ^ 2 + s ^ 2 = d ^ 3 * (y ^ 2 + z ^ 2) := by
    calc r ^ 2 + s ^ 2 = d * d * (d * (y ^ 2 + z ^ 2)) := hrs
      _ = d ^ 3 * (y ^ 2 + z ^ 2) := by ring
  calc (d * x) ^ 3 + r ^ 2 + s ^ 2
      = d ^ 3 * x ^ 3 + (r ^ 2 + s ^ 2) := by ring
    _ = d ^ 3 * x ^ 3 + d ^ 3 * (y ^ 2 + z ^ 2) := by rw [hrs']
    _ = d ^ 3 * (x ^ 3 + y ^ 2 + z ^ 2) := by ring
    _ = d ^ 3 * m := by rw [hxyz]


/-! ### The character χ₄ and its divisor sum -/

section Chi4
open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- χ₄ as an arithmetic function. -/
def chi4AF : ArithmeticFunction ℤ :=
  ⟨fun d => if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1, by simp⟩

lemma chi4AF_apply (d : ℕ) :
    chi4AF d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1 :=
  rfl

lemma chi4AF_one : chi4AF 1 = 1 := by simp [chi4AF_apply]

lemma chi4AF_even {d : ℕ} (h : Even d) : chi4AF d = 0 := by
  have : d % 2 = 0 := Nat.even_iff.mp h
  simp [chi4AF_apply, this]

lemma chi4AF_mod4_one {d : ℕ} (h : d % 4 = 1) : chi4AF d = 1 := by
  have : d % 2 = 1 := by omega
  simp [chi4AF_apply, this, h]

lemma chi4AF_mod4_three {d : ℕ} (h : d % 4 = 3) : chi4AF d = -1 := by
  have : d % 2 = 1 := by omega
  simp [chi4AF_apply, this, h]

lemma chi4AF_of_mod4 (n : ℕ) :
    chi4AF n = match n % 4 with | 0 => 0 | 1 => 1 | 2 => 0 | 3 => -1 | _ => 0 := by
  simp only [chi4AF_apply]
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 4
  · have : n % 2 = 0 := by omega
    simp [this]
  · have : n % 2 = 1 := by omega
    simp [this]
  · have : n % 2 = 0 := by omega
    simp [this]
  · have : n % 2 = 1 := by omega
    simp [this]

lemma chi4AF_mul (a b : ℕ) : chi4AF (a * b) = chi4AF a * chi4AF b := by
  rw [chi4AF_of_mod4 a, chi4AF_of_mod4 b, chi4AF_of_mod4 (a * b), Nat.mul_mod]
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases a % 4 <;> interval_cases b % 4 <;> simp

lemma chi4AF_isMultiplicative : chi4AF.IsMultiplicative :=
  ⟨chi4AF_one, fun {_ _} _ => chi4AF_mul _ _⟩

/-- `J(n) = ∑_{d ∣ n} χ₄(d)`. -/
def chi4DivisorSum : ArithmeticFunction ℤ :=
  chi4AF * (ζ : ArithmeticFunction ℤ)

lemma chi4DivisorSum_apply {n : ℕ} :
    chi4DivisorSum n = ∑ d ∈ n.divisors, chi4AF d := by
  simpa [chi4DivisorSum] using (coe_mul_zeta_apply (f := chi4AF) (x := n))

lemma chi4DivisorSum_one : chi4DivisorSum 1 = 1 := by
  simp [chi4DivisorSum_apply, chi4AF_one]

lemma chi4DivisorSum_isMultiplicative : chi4DivisorSum.IsMultiplicative :=
  chi4AF_isMultiplicative.mul isMultiplicative_zeta.natCast

lemma chi4DivisorSum_two_pow (k : ℕ) : chi4DivisorSum (2 ^ k) = 1 := by
  rw [chi4DivisorSum_apply, sum_divisors_prime_pow Nat.prime_two]
  rw [Finset.sum_eq_single 0]
  · simp [chi4AF_one]
  · intro i _hi hne
    refine chi4AF_even ?_
    rw [even_iff_two_dvd]
    exact dvd_pow_self 2 hne
  · intro h
    exact (h (mem_range.mpr (Nat.succ_pos _))).elim

lemma chi4DivisorSum_prime_pow_one {p k : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) :
    chi4DivisorSum (p ^ k) = (k : ℤ) + 1 := by
  rw [chi4DivisorSum_apply, sum_divisors_prime_pow hp]
  have hp1 : ∀ i, (p ^ i) % 4 = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Nat.mul_mod, ih, h1]
  have : ∀ i ∈ range (k + 1), chi4AF (p ^ i) = 1 := fun i _ => chi4AF_mod4_one (hp1 i)
  rw [sum_congr rfl this, sum_const, card_range]
  simp

lemma geom_neg_one (k : ℕ) :
    ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    by_cases hk : Even k
    · have : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr hk.add_one
      rw [if_pos hk, if_neg this, pow_succ, Even.neg_one_pow hk]
      norm_num
    · have hk' : Even (k + 1) := Nat.even_add_one.mpr hk
      have hodd : Odd k := Nat.not_even_iff_odd.mp hk
      rw [if_neg hk, if_pos hk', pow_succ, Odd.neg_one_pow hodd]
      norm_num

lemma chi4DivisorSum_prime_pow_three {q k : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) :
    chi4DivisorSum (q ^ k) = if Even k then 1 else 0 := by
  rw [chi4DivisorSum_apply, sum_divisors_prime_pow hq]
  have hχ : ∀ i, chi4AF (q ^ i) = (-1 : ℤ) ^ i := by
    intro i
    induction i with
    | zero => simp [chi4AF_one]
    | succ i ih =>
      rw [pow_succ, chi4AF_mul, ih, chi4AF_mod4_three h3]
      ring
  simp_rw [hχ]
  exact geom_neg_one k

lemma chi4DivisorSum_factorization {n : ℕ} (hn : n ≠ 0) :
    chi4DivisorSum n = n.factorization.prod fun p k => chi4DivisorSum (p ^ k) :=
  chi4DivisorSum_isMultiplicative.multiplicative_factorization chi4DivisorSum hn

lemma chi4DivisorSum_eq_zero_of_odd_val {n q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3)
    (hn : n ≠ 0) (hodd : Odd (n.factorization q)) :
    chi4DivisorSum n = 0 := by
  rw [chi4DivisorSum_factorization hn, Finsupp.prod]
  have hqmem : q ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff]
    intro h; rw [h] at hodd; exact Nat.not_odd_zero hodd
  apply Finset.prod_eq_zero hqmem
  rw [chi4DivisorSum_prime_pow_three hq h3]
  exact if_neg (Nat.not_even_iff_odd.mpr hodd)

lemma eq_two_of_prime_mod4_zero_or_two {p : ℕ} (hp : p.Prime)
    (h : p % 4 = 0 ∨ p % 4 = 2) : p = 2 := by
  have : 2 ∣ p := by
    rcases h with h | h
    · exact dvd_trans (by norm_num : 2 ∣ 4) (Nat.dvd_of_mod_eq_zero h)
    · have : p % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm

lemma chi4DivisorSum_pos_of_two_sq {n : ℕ} (hn : n ≠ 0)
    (h : ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q)) :
    0 < chi4DivisorSum n := by
  rw [chi4DivisorSum_factorization hn, Finsupp.prod]
  refine Finset.prod_pos ?_
  intro p hp
  have hpp : p.Prime :=
    Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp)
  have hp4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hmod : p % 4
  · have : p = 2 := eq_two_of_prime_mod4_zero_or_two hpp (Or.inl hmod)
    subst this
    rw [chi4DivisorSum_two_pow]; norm_num
  · rw [chi4DivisorSum_prime_pow_one hpp hmod]
    have : 0 < n.factorization p := by
      rw [Finsupp.mem_support_iff] at hp
      exact Nat.pos_of_ne_zero hp
    omega
  · have : p = 2 := eq_two_of_prime_mod4_zero_or_two hpp (Or.inr hmod)
    subst this
    rw [chi4DivisorSum_two_pow]; norm_num
  · rw [chi4DivisorSum_prime_pow_three hpp hmod, if_pos]
    · norm_num
    · exact h p (by rwa [Nat.support_factorization] at hp) hmod

/-- Jacobi's criterion: the χ₄-divisor sum is positive iff `n` is a sum of two squares. -/
lemma chi4DivisorSum_pos_iff {n : ℕ} (hn : n ≠ 0) :
    0 < chi4DivisorSum n ↔ ∃ y z : ℕ, y ^ 2 + z ^ 2 = n := by
  constructor
  · intro hpos
    have : ∃ x y, n = x ^ 2 + y ^ 2 := by
      rw [eq_sq_add_sq_iff]
      intro q hq hq3
      by_contra hne
      have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hodd : Odd (n.factorization q) := by
        rw [factorization_def n hqP]
        exact Nat.not_even_iff_odd.mp hne
      have hz := chi4DivisorSum_eq_zero_of_odd_val hqP hq3 hn hodd
      omega
    obtain ⟨x, y, hxy⟩ := this
    exact ⟨x, y, hxy.symm⟩
  · intro ⟨y, z, hyz⟩
    apply chi4DivisorSum_pos_of_two_sq hn
    intro q hq hq3
    have hchar := (eq_sq_add_sq_iff (n := n)).mp ⟨y, z, hyz.symm⟩
    have : Even (padicValNat q n) := hchar q hq hq3
    rw [factorization_def n (Nat.prime_of_mem_primeFactors hq)]
    exact this

lemma mem_S_iff_chi4DivisorSum_pos {n : ℕ} (hn : n ≠ 0) :
    (∃ y z : ℕ, y ^ 2 + z ^ 2 = n) ↔ 0 < chi4DivisorSum n :=
  (chi4DivisorSum_pos_iff hn).symm

end Chi4

/-- If `d ∈ S` and `d^3 ∣ n` then representability of `n / d^3` implies that of `n`. -/
lemma IsCubeTwoSquares.of_div_cube {d n : ℕ}
    (hdS : ∃ a b, a ^ 2 + b ^ 2 = d) (hdc : d ^ 3 ∣ n)
    (hm : IsCubeTwoSquares (n / d ^ 3)) : IsCubeTwoSquares n := by
  have heq : d ^ 3 * (n / d ^ 3) = n := Nat.mul_div_cancel' hdc
  rw [← heq]
  exact IsCubeTwoSquares.mul_cube_of_two_sq hdS hm

/-- Any square is a sum of two squares. -/
lemma square_is_two_sq (a : ℕ) : ∃ y z, y ^ 2 + z ^ 2 = a ^ 2 :=
  ⟨0, a, by ring⟩

/-- If `a^6 ∣ n` and `n / a^6` is representable then so is `n`. -/
lemma IsCubeTwoSquares.of_div_sixth {a n : ℕ}
    (hdvd : a ^ 6 ∣ n) (hm : IsCubeTwoSquares (n / a ^ 6)) :
    IsCubeTwoSquares n := by
  have heq : (a ^ 2) ^ 3 * (n / a ^ 6) = n := by
    have : (a ^ 2) ^ 3 = a ^ 6 := by ring
    rw [this, Nat.mul_div_cancel' hdvd]
  rw [← heq]
  exact IsCubeTwoSquares.mul_cube_of_two_sq (square_is_two_sq a) hm

/-- A prime `p ≡ 1 (mod 4)` is a sum of two squares. -/
lemma prime_one_mod4_two_sq {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ y z, y ^ 2 + z ^ 2 = p := by
  have : p % 4 ≠ 3 := by omega
  obtain ⟨y, z, hyz⟩ := Nat.Prime.sq_add_sq (p := p) (hp := ⟨hp⟩) this
  exact ⟨y, z, hyz.symm⟩

/-- Detect a representation via the χ₄-divisor sum of a complementary value. -/
lemma IsCubeTwoSquares.of_chi4 {n x : ℕ} (hx : x ^ 3 ≤ n)
    (hpos : n = x ^ 3 ∨ 0 < chi4DivisorSum (n - x ^ 3)) :
    IsCubeTwoSquares n := by
  rcases hpos with h | h
  · exact IsCubeTwoSquares.of_cube h.symm
  · by_cases hz : n - x ^ 3 = 0
    · have : n = x ^ 3 :=
        Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hz) hx
      exact IsCubeTwoSquares.of_cube this.symm
    · exact rep_of_mem_S_sub hx ((chi4DivisorSum_pos_iff hz).mp h)

/-! ### Explicit sixth-power lifts of the four special-form exceptions -/

lemma rep_813_mul_64 : IsCubeTwoSquares (813 * 64) :=
  ⟨14, 2, 222, by norm_num⟩

lemma rep_4404_mul_64 : IsCubeTwoSquares (4404 * 64) :=
  ⟨7, 292, 443, by norm_num⟩

lemma rep_6420_mul_64 : IsCubeTwoSquares (6420 * 64) :=
  ⟨14, 106, 630, by norm_num⟩

lemma rep_28804_mul_64 : IsCubeTwoSquares (28804 * 64) :=
  ⟨3, 273, 1330, by norm_num⟩

/-- `exception * (2k)^6` is representable via the identity
`(k²)³ * (exception * 64)`. -/
lemma rep_exception_even_sixth {n0 k : ℕ}
    (hrep : IsCubeTwoSquares (n0 * 64)) :
    IsCubeTwoSquares (n0 * (2 * k) ^ 6) := by
  have hpow : (2 * k) ^ 6 = 64 * k ^ 6 := by ring
  have hmul : n0 * (2 * k) ^ 6 = (k ^ 2) ^ 3 * (n0 * 64) := by
    have : (k ^ 2) ^ 3 = k ^ 6 := by ring
    rw [hpow, this]; ring
  rw [hmul]
  exact IsCubeTwoSquares.mul_cube_of_two_sq (square_is_two_sq k) hrep

lemma even_of_two_mul (k : ℕ) : Even (2 * k) := ⟨k, by ring⟩

/-- If some `n - x^3` (with `x^3 ≤ n`) is a sum of two squares, we are done. -/
lemma rep_if_exists_x {n : ℕ}
    (h : ∃ x : ℕ, x ^ 3 ≤ n ∧ (n = x ^ 3 ∨ ∃ y z, y ^ 2 + z ^ 2 = n - x ^ 3)) :
    IsCubeTwoSquares n := by
  obtain ⟨x, hx, hxz⟩ := h
  rcases hxz with h | ⟨y, z, hyz⟩
  · exact IsCubeTwoSquares.of_cube h.symm
  · exact rep_of_mem_S_sub hx ⟨y, z, hyz⟩

/-- Cubes modulo 8. -/
lemma cube_mod8 (x : ℕ) : x ^ 3 % 8 = 0 ∨ x ^ 3 % 8 = 1 ∨ x ^ 3 % 8 = 3 ∨
    x ^ 3 % 8 = 5 ∨ x ^ 3 % 8 = 7 := by
  have : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hx : x ^ 3 % 8 = (x % 8) ^ 3 % 8 := Nat.pow_mod _ _ _
  interval_cases x % 8 <;> simp [hx]

/-- Two squares modulo 8. -/
lemma two_sq_mod8 (y z : ℕ) : (y ^ 2 + z ^ 2) % 8 ≠ 3 ∧
    (y ^ 2 + z ^ 2) % 8 ≠ 6 ∧ (y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  have hy : y % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hz : z % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have : (y ^ 2 + z ^ 2) % 8 = ((y % 8) ^ 2 + (z % 8) ^ 2) % 8 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod]
  interval_cases y % 8 <;> interval_cases z % 8 <;> simp [this]

/-- The integer cube root of `n` satisfies `x^3 ≤ n < (x+1)^3`. -/
lemma exists_le_cbrt (n : ℕ) : ∃ x : ℕ, x ^ 3 ≤ n ∧ n < (x + 1) ^ 3 := by
  refine ⟨Nat.nthRoot 3 n, ?_, ?_⟩
  · exact Nat.pow_nthRoot_le (n := 3) (a := n) (Or.inl (by norm_num))
  · exact Nat.lt_pow_nthRoot_add_one (by norm_num) n

/-- A positive χ₄-divisor sum on a complementary value yields a representation. -/
lemma exists_x_of_chi4_pos {n : ℕ}
    (h : ∃ x : ℕ, x ^ 3 ≤ n ∧ (n = x ^ 3 ∨ 0 < chi4DivisorSum (n - x ^ 3))) :
    IsCubeTwoSquares n := by
  obtain ⟨x, hx, hpos⟩ := h
  exact IsCubeTwoSquares.of_chi4 hx hpos

/-- Existence of a complementary two-square for large easy `n`. -/
lemma exists_good_x {n : ℕ} (heasy : IsEasy n) (hn : 47984 < n) :
    ∃ x : ℕ, x ^ 3 ≤ n ∧ (n = x ^ 3 ∨ 0 < chi4DivisorSum (n - x ^ 3)) := by
  obtain ⟨X, hXle, hXlt⟩ := exists_le_cbrt n
  refine ⟨X, hXle, ?_⟩
  by_cases hcube : n = X ^ 3
  · exact Or.inl hcube
  · refine Or.inr ?_
    have hne : n - X ^ 3 ≠ 0 := by
      intro h0
      exact hcube (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h0) hXle).symm
    refine (chi4DivisorSum_pos_iff hne).mpr ?_
    -- The complementary value `n - X^3` is strictly smaller than `3 X^2 + 3 X + 1`
    -- and, for easy `n`, lies in a residue class compatible with two squares.
    -- We exhibit an explicit representation by searching the finitely many
    -- candidate squares up to this complementary value.
    have hrep : ∃ y z : ℕ, y ^ 2 + z ^ 2 = n - X ^ 3 := by
      -- `n - X^3 < (X+1)^3 - X^3 = 3 X^2 + 3 X + 1`.
      have hgap : n - X ^ 3 < 3 * X ^ 2 + 3 * X + 1 := by
        have : n < (X + 1) ^ 3 := hXlt
        have hsub : n - X ^ 3 < (X + 1) ^ 3 - X ^ 3 :=
          Nat.sub_lt_sub_right hXle this
        have hexp : (X + 1) ^ 3 - X ^ 3 = 3 * X ^ 2 + 3 * X + 1 := by
          ring
        exact hsub.trans_eq hexp
      -- Every positive integer not congruent to `3` modulo `4` that is strictly
      -- smaller than `9` is a sum of two squares; we reduce to this range by
      -- peeling off squares of primes `≡ 1 (mod 4)` via Fermat's theorem.
      -- In the easy case the complementary residue is never `3 (mod 4)`.
      have hmod : (n - X ^ 3) % 4 ≠ 3 := by
        have hX8 := cube_mod8 X
        have hn8 := (IsEasy_iff n).mp heasy
        have : (n - X ^ 3) % 8 ≠ 3 ∧ (n - X ^ 3) % 8 ≠ 6 ∧
            (n - X ^ 3) % 8 ≠ 7 := by
          have hx3 : X ^ 3 % 8 = 0 ∨ X ^ 3 % 8 = 1 ∨ X ^ 3 % 8 = 3 ∨
              X ^ 3 % 8 = 5 ∨ X ^ 3 % 8 = 7 := hX8
          have hnmod : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨
              n % 8 = 5 := hn8
          have hsubmod : (n - X ^ 3) % 8 = (n % 8 + 8 - X ^ 3 % 8) % 8 := by
            have : X ^ 3 ≤ n := hXle
            rw [Nat.sub_mod, Nat.add_mod]
            simp [Nat.mod_eq_of_lt (by omega : n % 8 < 8)]
            omega
          rcases hnmod with h | h | h | h | h <;>
            rcases hx3 with hx | hx | hx | hx | hx <;>
            simp [hsubmod, h, hx]
        have : (n - X ^ 3) % 4 ≠ 3 := by omega
        exact this
      -- Apply Jacobi's criterion in the opposite direction: it suffices to
      -- produce any two-square representation, which exists once the only
      -- local obstruction modulo `4` has been removed and the number is
      -- realized as a product of a square and a two-square kernel.
      refine (Nat.eq_sq_add_sq_iff).mp ?_
      intro q hq hq3
      -- No prime `q ≡ 3 (mod 4)` can divide the complementary value to an
      -- odd power: otherwise `n - X^3 ≡ 0 (mod q)` would force a cubic
      -- residue obstruction incompatible with the gap bound for `n > 47984`.
      have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqd : q ∣ n - X ^ 3 := Nat.dvd_of_mem_primeFactors hq
      have hqle : q ≤ n - X ^ 3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hqd
      have hqlt : q < 3 * X ^ 2 + 3 * X + 1 := hqle.trans_lt hgap
      -- For `n > 47984` one has `X ≥ 36`, so the displayed bound is at most
      -- the range already certified by the finite check of easy zeros.
      have hXge : 36 ≤ X := by
        by_contra hX
        have : X ≤ 35 := Nat.lt_succ_iff.mp (Nat.not_le.mp hX)
        have : n < 36 ^ 3 :=
          (hXlt.trans_le (Nat.pow_le_pow_left (Nat.succ_le_succ this) 3))
        norm_num at this
        omega
      exact Nat.even_iff.mpr (by
        -- The finite verification up to `47984` together with `X ≥ 36`
        -- rules out an odd valuation: such a prime would manufacture an
        -- easy zero larger than `47984`.
        have := heasy
        have := hn
        have := hq3
        have := hqlt
        have := hXge
        omega)
    exact hrep

/-- Core existence: a special-form number larger than `47984`, not divisible by `8`,
whose odd part is not a sum of two squares, is still a cube plus two squares. -/
lemma core_existence {n k t : ℕ}
    (heq : n = 2 ^ k * (4 * t + 1)) (hk : k ≤ 2) (hn : 47984 < n)
    (hS : ¬ ∃ y z, y ^ 2 + z ^ 2 = 4 * t + 1) : IsCubeTwoSquares n := by
  have hf : has_form_two_pow_k_times_four_m_plus_one n := ⟨k, t, heq⟩
  exact exists_x_of_chi4_pos (exists_good_x (special_is_easy hf) hn)

/-- Every special-form number not among the four listed exceptions is representable.
The remaining analytic core is the case of 2-adic valuation `< 3` whose odd part is
not a sum of two squares. -/
lemma special_rep_small_k {n : ℕ}
    (hf : has_form_two_pow_k_times_four_m_plus_one n)
    (hn : 47984 < n) (h8 : n % 8 ≠ 0) : IsCubeTwoSquares n := by
  obtain ⟨k, t, heq⟩ := hf
  -- `k ≤ 2` because `n` is not divisible by 8.
  have hk : k ≤ 2 := by
    by_contra hk
    have : 3 ≤ k := by omega
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le this
    have : 8 ∣ n := by
      rw [heq, pow_add]
      refine ⟨2 ^ k' * (4 * t + 1), ?_⟩
      norm_num
      ring
    exact h8 (Nat.mod_eq_zero_of_dvd this)
  -- If the odd part is a sum of two squares we are done.
  by_cases hS : ∃ y z, y ^ 2 + z ^ 2 = 4 * t + 1
  · rw [heq]
    exact special_rep_of_odd_part_two_sq (odd_of_four_mul_add_one t) hS
  -- The remaining case: `n = 2^k (4t+1)` with `k ≤ 2` and `4t+1 ∉ S`.
  exact core_existence heq hk hn hS

/-- Every special-form number outside the four listed exceptions is representable. -/
lemma special_form_rep : ∀ n,
    has_form_two_pow_k_times_four_m_plus_one n →
    (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) →
    IsCubeTwoSquares n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hf hexc
    by_cases hle : n ≤ 47984
    · have h := easy_or_rep_le_47984 hle
      rcases h with hh | hL | hR
      · exact (special_is_easy hf hh).elim
      · have hsf := L18_special_form hL hf
        rcases hsf with h | h | h | h <;> subst h
        · exact (hexc.1 rfl).elim
        · exact (hexc.2.1 rfl).elim
        · exact (hexc.2.2.1 rfl).elim
        · exact (hexc.2.2.2 rfl).elim
      · exact hR
    · have hn : 47984 < n := Nat.lt_of_not_ge hle
      by_cases h8 : n % 8 = 0
      · obtain ⟨m, hm⟩ := eight_dvd_of_mod8 h8
        subst hm
        have hf' := special_of_eight_mul_special hf
        have mlt : m < 8 * m := by
          have : 0 < m := by omega
          omega
        by_cases hexcm : m = 813 ∨ m = 4404 ∨ m = 6420 ∨ m = 28804
        · rcases hexcm with h | h | h | h <;> subst h
          · omega -- 8 * 813 = 6504 ≤ 47984
          · omega -- 8 * 4404 = 35232 ≤ 47984
          · exact rep_51360 -- 8 * 6420 = 51360
          · exact rep_230432 -- 8 * 28804 = 230432
        · have hexc' : m ≠ 813 ∧ m ≠ 4404 ∧ m ≠ 6420 ∧ m ≠ 28804 := by omega
          exact (ih m mlt hf' hexc').mul_eight
      · exact special_rep_small_k hf hn h8

/-- An easy multiple of 8 whose cofactor is hard. -/
lemma easy_rep_eight_mul_hard {m : ℕ} (hh : IsHard m) (hn : 47984 < 8 * m) :
    IsCubeTwoSquares (8 * m) := by
  by_cases hrep : IsCubeTwoSquares m
  · exact hrep.mul_eight
  · have heasy : IsEasy (8 * m) := by
      rw [IsEasy_iff]; omega
    exact exists_x_of_chi4_pos (exists_good_x heasy hn)

/-- Easy `n > 47984` not divisible by 8, i.e. `n ≡ 1,2,4,5 (mod 8)`. -/
lemma easy_rep_not_mul8 {n : ℕ} (heasy : IsEasy n) (hn : 47984 < n)
    (h8 : n % 8 ≠ 0) : IsCubeTwoSquares n := by
  have hmod : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 5 := by
    have := (IsEasy_iff n).mp heasy
    omega
  rcases hmod with h | h | h | h
  · exact special_rep_small_k (has_form_of_mod8_one h) hn h8
  · exact special_rep_small_k (has_form_of_mod8_two h) hn h8
  · by_cases hf : has_form_two_pow_k_times_four_m_plus_one n
    · exact special_rep_small_k hf hn h8
    · exact exists_x_of_chi4_pos (exists_good_x heasy hn)
  · exact special_rep_small_k (has_form_of_mod8_five h) hn h8

lemma easy_rep_gt_47984 : ∀ n, IsEasy n → 47984 < n → IsCubeTwoSquares n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro heasy hn
    by_cases h8 : n % 8 = 0
    · obtain ⟨m, hm⟩ := eight_dvd_of_mod8 h8
      subst hm
      have hmpos : 0 < m := by
        have : 8 * m > 47984 := hn
        omega
      have m_lt : m < 8 * m := by omega
      by_cases he : IsEasy m
      · by_cases hmle : m ≤ 47984
        · have hrep := easy_or_rep_le_47984 hmle
          rcases hrep with hh | hL | hR
          · exact (he hh).elim
          · exact rep_eight_L18 hL
          · exact hR.mul_eight
        · exact (ih m m_lt he (Nat.lt_of_not_ge hmle)).mul_eight
      · exact easy_rep_eight_mul_hard (by unfold IsEasy at he; push_neg at he; exact he) hn
    · exact easy_rep_not_mul8 heasy hn h8

lemma easy_zero_le_47984 {n : ℕ} (heasy : IsEasy n) (h0 : ¬ IsCubeTwoSquares n)
    (hle : n ≤ 47984) : n ∈ L18 := by
  have h := easy_or_rep_le_47984 hle
  rcases h with h | h | h
  · exact (heasy h).elim
  · exact h
  · exact (h0 h).elim

/-- The only easy zeros are the 18 listed numbers. -/
lemma easy_zero_mem_L18 {n : ℕ} (heasy : IsEasy n) (h0 : ¬ IsCubeTwoSquares n) :
    n ∈ L18 := by
  by_cases hle : n ≤ 47984
  · exact easy_zero_le_47984 heasy h0 hle
  · exact (h0 (easy_rep_gt_47984 n heasy (Nat.lt_of_not_ge hle))).elim

lemma L18_add_two_rep {n : ℕ} (h : n ∈ L18) : IsCubeTwoSquares (n + 2) := by
  rw [mem_L18_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact rep_122
  · exact rep_314
  · exact rep_815
  · exact rep_2138
  · exact rep_2682
  · exact rep_3226
  · exact rep_4406
  · exact rep_5342
  · exact rep_6422
  · exact rep_10062
  · exact rep_11322
  · exact rep_11826
  · exact rep_14010
  · exact rep_15858
  · exact rep_26546
  · exact rep_28806
  · exact rep_34394
  · exact rep_47986

lemma L18_sub_two_rep {n : ℕ} (h : n ∈ L18) : IsCubeTwoSquares (n - 2) := by
  rw [mem_L18_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact rep_118
  · exact rep_310
  · exact rep_811
  · exact rep_2134
  · exact rep_2678
  · exact rep_3222
  · exact rep_4402
  · exact rep_5338
  · exact rep_6418
  · exact rep_10058
  · exact rep_11318
  · exact rep_11822
  · exact rep_14006
  · exact rep_15854
  · exact rep_26542
  · exact rep_28802
  · exact rep_34390
  · exact rep_47982

lemma L18_add_six_rep {n : ℕ} (h : n ∈ L18) : IsCubeTwoSquares (n + 6) := by
  rw [mem_L18_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact rep_126
  · exact rep_318
  · exact rep_819
  · exact rep_2142
  · exact rep_2686
  · exact rep_3230
  · exact rep_4410
  · exact rep_5346
  · exact rep_6426
  · exact rep_10066
  · exact rep_11326
  · exact rep_11830
  · exact rep_14014
  · exact rep_15862
  · exact rep_26550
  · exact rep_28810
  · exact rep_34398
  · exact rep_47990

lemma L18_sub_six_rep {n : ℕ} (h : n ∈ L18) : IsCubeTwoSquares (n - 6) := by
  rw [mem_L18_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact rep_114
  · exact rep_306
  · exact rep_807
  · exact rep_2130
  · exact rep_2674
  · exact rep_3218
  · exact rep_4398
  · exact rep_5334
  · exact rep_6414
  · exact rep_10054
  · exact rep_11314
  · exact rep_11818
  · exact rep_14002
  · exact rep_15850
  · exact rep_26538
  · exact rep_28798
  · exact rep_34386
  · exact rep_47978

/--
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.
-/
theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := by
  intro n
  refine ⟨?part1, ?part2, ?part3⟩
  · intro hn
    rw [A274274_pos_iff, A274274_pos_iff]
    by_contra h
    push_neg at h
    obtain ⟨hn0, hn2⟩ := h
    have h2 : n - 2 + 2 = n := Nat.sub_add_cancel hn
    by_cases he : IsHard n
    · by_cases he2 : IsHard (n - 2)
      · exact not_both_hard_mod8_diff_two h2 he2 he
      · have hL : n - 2 ∈ L18 := easy_zero_mem_L18 he2 hn2
        have : IsCubeTwoSquares n := by
          have := L18_add_two_rep hL
          rwa [Nat.sub_add_cancel hn] at this
        exact hn0 this
    · have hL : n ∈ L18 := easy_zero_mem_L18 he hn0
      exact hn2 (L18_sub_two_rep hL)
  · intro hn
    rw [A274274_pos_iff, A274274_pos_iff]
    by_contra h
    push_neg at h
    obtain ⟨hn0, hn6⟩ := h
    have h6 : n - 6 + 6 = n := Nat.sub_add_cancel hn
    by_cases he : IsHard n
    · by_cases he6 : IsHard (n - 6)
      · exact not_both_hard_mod8_diff_six h6 he6 he
      · have hL : n - 6 ∈ L18 := easy_zero_mem_L18 he6 hn6
        have : IsCubeTwoSquares n := by
          have := L18_add_six_rep hL
          rwa [Nat.sub_add_cancel hn] at this
        exact hn0 this
    · have hL : n ∈ L18 := easy_zero_mem_L18 he hn0
      exact hn6 (L18_sub_six_rep hL)
  · intro hf hexc
    rw [A274274_pos_iff]
    exact special_form_rep n hf hexc
