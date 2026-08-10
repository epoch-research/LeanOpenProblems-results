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

lemma self_le_pow_ten (M : ℕ) : M ≤ 10^M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h_pow : 10^(M+1) = 10^M * 10 := rfl
    rw [h_pow]
    have h_ten : 10^M * 10 ≥ 10^M + 1 := by
      have : 10^M ≥ 1 := Nat.pow_pos (by decide)
      omega
    omega

lemma dsum_pos (n : ℕ) (hn : 0 < n) : (digits 10 n).sum > 0 := by
  have h_ne : digits 10 n ≠ [] := digits_ne_nil_iff_ne_zero.mpr (by omega)
  have h_last_ne : (digits 10 n).getLast h_ne ≠ 0 := getLast_digit_ne_zero 10 (by omega)
  have h_mem : (digits 10 n).getLast h_ne ∈ digits 10 n := List.getLast_mem h_ne
  have h_le : (digits 10 n).getLast h_ne ≤ (digits 10 n).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ h_mem
  omega

lemma dsum_ten_mul (n : ℕ) (hn : 0 < n) : (digits 10 (10 * n)).sum = (digits 10 n).sum := by
  have hb : 1 < 10 := by decide
  rw [Nat.digits_base_mul hb hn]
  simp

lemma dsum_pow_ten_mul (p : ℕ) (m : ℕ) (hm : 0 < m) : (digits 10 (10^p * m)).sum = (digits 10 m).sum := by
  induction p with
  | zero =>
    simp
  | succ p ih =>
    have h_eq : 10^(p+1) * m = 10 * (10^p * m) := by
      ring
    rw [h_eq]
    have h_pos : 0 < 10^p * m := by
      apply Nat.mul_pos
      · exact Nat.pow_pos (by decide)
      · exact hm
    rw [dsum_ten_mul (10^p * m) h_pos]
    exact ih

lemma exists_partner_of_pow_ten (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : (digits 10 n).sum ∣ 10^p) :
    ∃ k, k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n := by
  let M := p + n + 1
  have hM_ge : M ≥ p := by omega
  have hM_gt : M > n := by omega
  let k := 10^M
  have hk_pos : k > 0 := Nat.pow_pos (by decide)
  have hk_ne : k ≠ n := by
    have : k > n := by
      calc
        10^M ≥ M := self_le_pow_ten M
        _ > n := hM_gt
    omega
  have h_div1 : (digits 10 n).sum ∣ k := by
    have h_pow : 10^p ∣ 10^M := Nat.pow_dvd_pow 10 hM_ge
    exact dvd_trans hp h_pow
  have h_div2 : (digits 10 k).sum ∣ n := by
    have hk_eq : k = 10^M * 1 := by ring
    rw [hk_eq]
    rw [dsum_pow_ten_mul M 1 (by decide)]
    have h_one : digits 10 1 = [1] := Nat.digits_of_lt 10 1 (by decide) (by decide)
    rw [h_one]
    simp
  exact ⟨k, hk_pos, hk_ne, h_div1, h_div2⟩

lemma exists_partner_of_dsum_dsum (n : ℕ) (hn : 0 < n) (hd_div : (digits 10 (digits 10 n).sum).sum ∣ n) :
    ∃ k, k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n := by
  let d := (digits 10 n).sum
  have hd_pos : d > 0 := dsum_pos n hn
  let M := n + 1
  let k := d * 10^M
  have hk_pos : k > 0 := by
    apply Nat.mul_pos hd_pos (Nat.pow_pos (by decide))
  have hk_ne : k ≠ n := by
    have : k > n := by
      calc
        k = d * 10^M := rfl
        _ ≥ 1 * 10^M := Nat.mul_le_mul_right (10^M) hd_pos
        _ = 10^M := by ring
        _ ≥ M := self_le_pow_ten M
        _ > n := by omega
    omega
  have h_div1 : d ∣ k := dvd_mul_right d (10^M)
  have h_div2 : (digits 10 k).sum ∣ n := by
    have hk_eq : k = 10^M * d := by ring
    rw [hk_eq]
    rw [dsum_pow_ten_mul M d hd_pos]
    exact hd_div
  exact ⟨k, hk_pos, hk_ne, h_div1, h_div2⟩

-- Helper lemmas for digits evaluation of small numbers
lemma digits_12 : digits 10 12 = [2, 1] := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]

lemma digits_15 : digits 10 15 = [5, 1] := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]

lemma digits_16 : digits 10 16 = [6, 1] := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]

lemma digits_25 : digits 10 25 = [5, 2] := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]

lemma digits_35 : digits 10 35 = [5, 3] := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]

lemma dsum_1 : (digits 10 1).sum = 1 := by rw [digits_of_lt 10 1 (by decide) (by decide)]; rfl
lemma dsum_2 : (digits 10 2).sum = 2 := by rw [digits_of_lt 10 2 (by decide) (by decide)]; rfl
lemma dsum_3 : (digits 10 3).sum = 3 := by rw [digits_of_lt 10 3 (by decide) (by decide)]; rfl
lemma dsum_4 : (digits 10 4).sum = 4 := by rw [digits_of_lt 10 4 (by decide) (by decide)]; rfl
lemma dsum_5 : (digits 10 5).sum = 5 := by rw [digits_of_lt 10 5 (by decide) (by decide)]; rfl
lemma dsum_6 : (digits 10 6).sum = 6 := by rw [digits_of_lt 10 6 (by decide) (by decide)]; rfl
lemma dsum_7 : (digits 10 7).sum = 7 := by rw [digits_of_lt 10 7 (by decide) (by decide)]; rfl
lemma dsum_8 : (digits 10 8).sum = 8 := by rw [digits_of_lt 10 8 (by decide) (by decide)]; rfl
lemma dsum_9 : (digits 10 9).sum = 9 := by rw [digits_of_lt 10 9 (by decide) (by decide)]; rfl
lemma dsum_10 : (digits 10 10).sum = 1 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  have : 10 / 10 = 1 := rfl
  rw [this]
  rw [digits_of_lt 10 1 (by decide) (by decide)]
  rfl
lemma dsum_11 : (digits 10 11).sum = 2 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl
lemma dsum_12 : (digits 10 12).sum = 3 := by rw [digits_12]; rfl
lemma dsum_13 : (digits 10 13).sum = 4 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl
lemma dsum_14 : (digits 10 14).sum = 5 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl
lemma dsum_15 : (digits 10 15).sum = 6 := by rw [digits_15]; rfl
lemma dsum_16 : (digits 10 16).sum = 7 := by rw [digits_16]; rfl
lemma dsum_17 : (digits 10 17).sum = 8 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl
lemma dsum_18 : (digits 10 18).sum = 9 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl
lemma dsum_19 : (digits 10 19).sum = 10 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_def' hb (by decide)]
  rw [digits_zero]
  rfl

lemma dsum_20 : (digits 10 20).sum = 2 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_21 : (digits 10 21).sum = 3 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_22 : (digits 10 22).sum = 4 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_23 : (digits 10 23).sum = 5 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_24 : (digits 10 24).sum = 6 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_26 : (digits 10 26).sum = 8 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl

lemma dsum_27 : (digits 10 27).sum = 9 := by
  have hb : 1 < 10 := by decide
  rw [digits_def' hb (by decide)]
  rw [digits_of_lt 10 2 (by decide) (by decide)]
  rfl
lemma dsum_25 : (digits 10 25).sum = 7 := by rw [digits_25]; rfl
lemma dsum_35_val : (digits 10 35).sum = 8 := by rw [digits_35]; rfl

lemma finite_cases_less_than_28 (n : ℕ) (hn : n > 0) (hn28 : n < 28)
    (h_harshad : ¬ (digits 10 n).sum ∣ n)
    (h_pow : ¬ ∃ p, (digits 10 n).sum ∣ 10^p)
    (h_dsum : ¬ (digits 10 (digits 10 n).sum).sum ∣ n) :
    n = 15 ∨ n = 16 ∨ n = 25 := by
  interval_cases n
  · exfalso; apply h_harshad; rw [dsum_1]
  · exfalso; apply h_harshad; rw [dsum_2]
  · exfalso; apply h_harshad; rw [dsum_3]
  · exfalso; apply h_harshad; rw [dsum_4]
  · exfalso; apply h_harshad; rw [dsum_5]
  · exfalso; apply h_harshad; rw [dsum_6]
  · exfalso; apply h_harshad; rw [dsum_7]
  · exfalso; apply h_harshad; rw [dsum_8]
  · exfalso; apply h_harshad; rw [dsum_9]
  · exfalso; apply h_harshad; rw [dsum_10]; decide
  · exfalso; apply h_pow; exact ⟨1, by rw [dsum_11]; decide⟩
  · exfalso; apply h_dsum; rw [dsum_12, dsum_3]; decide
  · exfalso; apply h_pow; exact ⟨2, by rw [dsum_13]; decide⟩
  · exfalso; apply h_pow; exact ⟨1, by rw [dsum_14]; decide⟩
  · left; rfl
  · right; left; rfl
  · exfalso; apply h_pow; exact ⟨3, by rw [dsum_17]; decide⟩
  · exfalso; apply h_dsum; rw [dsum_18, dsum_9]; decide
  · exfalso; apply h_pow; exact ⟨1, by rw [dsum_19]; decide⟩
  · exfalso; apply h_harshad; rw [dsum_20]; decide
  · exfalso; apply h_harshad; rw [dsum_21]; decide
  · exfalso; apply h_pow; exact ⟨2, by rw [dsum_22]; decide⟩
  · exfalso; apply h_pow; exact ⟨1, by rw [dsum_23]; decide⟩
  · exfalso; apply h_harshad; rw [dsum_24]; decide
  · right; right; rfl
  · exfalso; apply h_pow; exact ⟨3, by rw [dsum_26]; decide⟩
  · exfalso; apply h_harshad; rw [dsum_27]; decide

lemma not_harshad_ge10 (n : ℕ) (hn : 0 < n) (h : ¬ (digits 10 n).sum ∣ n) : n ≥ 10 := by
  by_contra hLT
  push_neg at hLT
  have h_dig : digits 10 n = [n] := Nat.digits_of_lt 10 n hn.ne' hLT
  have h_sum : (digits 10 n).sum = n := by
    rw [h_dig]
    simp
  rw [h_sum] at h
  exact h (dvd_refl n)

-- Helper lemmas for the general construction
lemma div_mod_ten (x : ℕ) : x = 10 * (x / 10) + x % 10 := by
  exact (Nat.div_add_mod x 10).symm

lemma digits_ten_add (x y : ℕ) (hx : x < 10) (h : x ≠ 0 ∨ y ≠ 0) :
    digits 10 (x + 10 * y) = x :: digits 10 y := by
  apply digits_add 10 (by decide) x y hx h

lemma dsum_pow_ten_sub_one (M : ℕ) : (digits 10 (10^M - 1)).sum = 9 * M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h_pow : 10^(M+1) = 10^M * 10 := rfl
    have h_eq : 10^(M+1) - 1 = 9 + 10 * (10^M - 1) := by
      rw [h_pow]
      have h_ge : 10^M ≥ 1 := Nat.pow_pos (by decide)
      omega
    rw [h_eq]
    have h_dig : digits 10 (9 + 10 * (10^M - 1)) = 9 :: digits 10 (10^M - 1) := by
      apply digits_ten_add 9 (10^M - 1) (by decide)
      left; decide
    rw [h_dig]
    simp [ih]
    ring

lemma dsum_complement (M : ℕ) : ∀ x, x < 10^M → (digits 10 x).sum + (digits 10 (10^M - 1 - x)).sum = 9 * M := by
  induction M with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    rw [this]
    simp
  | succ M ih =>
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      have h1 : (digits 10 0).sum = 0 := by simp
      have h2 : 10^(M+1) - 1 - 0 = 10^(M+1) - 1 := by omega
      rw [h1, h2, zero_add]
      exact dsum_pow_ten_sub_one (M + 1)
    · have h_eq : x = x % 10 + 10 * (x / 10) := by
        rw [add_comm]
        exact div_mod_ten x
      have hr : x % 10 < 10 := Nat.mod_lt x (by decide)
      have hq : x / 10 < 10^M := by
        have : 10^(M+1) = 10^M * 10 := rfl
        omega
      
      have h_Y_eq : 10^(M+1) - 1 - x = (9 - x % 10) + 10 * (10^M - 1 - x / 10) := by
        have : 10^(M+1) = 10^M * 10 := rfl
        omega
      
      have hR : 9 - x % 10 < 10 := by omega
      
      have h_dig_x : digits 10 x = (x % 10) :: digits 10 (x / 10) := by
        have h_or : x % 10 ≠ 0 ∨ x / 10 ≠ 0 := by
          by_contra h_and
          push_neg at h_and
          have : x = 0 := by omega
          exact hx0 this
        nth_rw 1 [h_eq]
        apply digits_ten_add (x % 10) (x / 10) hr h_or
      
      have h_sum_Y : (digits 10 (10^(M+1) - 1 - x)).sum = (9 - x % 10) + (digits 10 (10^M - 1 - x / 10)).sum := by
        by_cases h_or : 9 - x % 10 ≠ 0 ∨ 10^M - 1 - x / 10 ≠ 0
        · have h_dig_Y : digits 10 (10^(M+1) - 1 - x) = (9 - x % 10) :: digits 10 (10^M - 1 - x / 10) := by
            nth_rw 1 [h_Y_eq]
            apply digits_ten_add (9 - x % 10) (10^M - 1 - x / 10) hR h_or
          rw [h_dig_Y]
          simp
        · have hY0 : 10^(M+1) - 1 - x = 0 := by omega
          have hR0 : 9 - x % 10 = 0 := by omega
          have hQ0 : 10^M - 1 - x / 10 = 0 := by omega
          rw [hY0, hR0, hQ0]
          simp
          
      rw [h_dig_x, h_sum_Y]
      simp only [List.sum_cons]
      have h_ih := ih (x / 10) hq
      omega

lemma algebra_step (d M : ℕ) (hd : d ≥ 1) (hM : d ≤ 10^M) :
    d * 10^M - d = (d - 1) * 10^M + (10^M - d) := by
  have h1 : (d - 1) * 10^M = d * 10^M - 10^M := by
    rw [Nat.sub_mul]
    simp
  rw [h1]
  have h2 : 10^M ≤ d * 10^M := by
    calc
      10^M = 1 * 10^M := by ring
      _ ≤ d * 10^M := Nat.mul_le_mul_right (10^M) hd
  omega

lemma dsum_append_zeroes (k : ℕ) (m n : ℕ) (hm : 0 < m) :
    (digits 10 (n + 10^((digits 10 n).length + k) * m)).sum = (digits 10 n).sum + (digits 10 m).sum := by
  have hb : 1 < 10 := by decide
  have h_eq := digits_append_zeroes_append_digits hb hm (k := k) (n := n)
  have h_sum : (digits 10 n ++ List.replicate k 0 ++ digits 10 m).sum = (digits 10 (n + 10^((digits 10 n).length + k) * m)).sum := by
    rw [h_eq]
  rw [← h_sum]
  simp

lemma dsum_mul_pow_ten_sub_one (d M : ℕ) (hd : d ≥ 1) (hM : (digits 10 (d - 1)).length ≤ M) :
    (digits 10 (d * (10^M - 1))).sum = 9 * M := by
  by_cases hd1 : d = 1
  · rw [hd1]
    simp
    exact dsum_pow_ten_sub_one M
  · have hd_gt1 : d > 1 := by omega
    have hd_pos : d - 1 < 10^M := (digits_length_le_iff (by decide) (d - 1)).mp hM
    have h_eq1 : d * (10^M - 1) = d * 10^M - d := by
      rw [Nat.mul_sub_left_distrib]
      simp
    have h_eq2 : d * 10^M - d = (10^M - d) + 10^M * (d - 1) := by
      rw [algebra_step d M (by omega) (by omega)]
      ring
    have h_eq3 : d * (10^M - 1) = (10^M - d) + 10^M * (d - 1) := by
      rw [h_eq1, h_eq2]
    rw [h_eq3]
    have h_len : (digits 10 (10^M - d)).length ≤ M := by
      apply (digits_length_le_iff (by decide) (10^M - d)).mpr
      omega
    let k := M - (digits 10 (10^M - d)).length
    have h_sum_eq : (10^M - d) + 10^M * (d - 1) = (10^M - d) + 10^((digits 10 (10^M - d)).length + k) * (d - 1) := by
      congr
      omega
    rw [h_sum_eq]
    rw [dsum_append_zeroes k (d - 1) (10^M - d) (by omega)]
    have h_comp := dsum_complement M (d - 1) hd_pos
    have h_sub_eq : 10^M - 1 - (d - 1) = 10^M - d := by omega
    rw [h_sub_eq] at h_comp
    omega

lemma exists_partner_of_multiple (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hd_div : (digits 10 n).sum ∣ m) (hD_div : (digits 10 m).sum ∣ n) :
    ∃ k, k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n := by
  let M := n + 1
  let k := 10^M * m
  have hk_pos : k > 0 := by
    apply Nat.mul_pos
    · exact Nat.pow_pos (by decide)
    · exact hm
  have hk_ne : k ≠ n := by
    have : k > n := by
      calc
        10^M * m ≥ 10^M * 1 := Nat.mul_le_mul_left (10^M) hm
        _ = 10^M := by ring
        _ ≥ M := self_le_pow_ten M
        _ > n := by omega
    omega
  have h_div1 : (digits 10 n).sum ∣ k := by
    exact dvd_mul_of_dvd_right hd_div (10^M)
  have h_div2 : (digits 10 k).sum ∣ n := by
    rw [dsum_pow_ten_mul M m hm]
    exact hD_div
  exact ⟨k, hk_pos, hk_ne, h_div1, h_div2⟩

lemma list_sum_le_mul_length (L : List ℕ) (h : ∀ x ∈ L, x ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons, List.length_cons]
    have h1 : hd ≤ 9 := h hd (by simp)
    have h2 : tl.sum ≤ 9 * tl.length := by
      apply ih
      intro x hx
      exact h x (by simp [hx])
    omega

lemma dsum_le_nine_mul_len (d : ℕ) : (digits 10 d).sum ≤ 9 * (digits 10 d).length := by
  apply list_sum_le_mul_length
  intro x hx
  have := digits_lt_base (by decide) hx
  omega

lemma nine_mul_lt_pow_ten (L : ℕ) (hL : L ≥ 1) : 9 * L < 10^L := by
  induction L with
  | zero => omega
  | succ L ih =>
    by_cases hL1 : L = 0
    · subst hL1
      decide
    · have hL_ge1 : L ≥ 1 := by omega
      have ih' := ih hL_ge1
      have h_pow : 10^(L+1) = 10^L * 10 := rfl
      rw [h_pow]
      have : 10^L * 10 ≥ 10^L + 9 * 10^L := by omega
      have h_ten_L : 10^L ≥ 10 := by
        have : L ≥ 1 := by omega
        calc
          10^L ≥ 10^1 := Nat.pow_le_pow_right (by decide) this
          _ = 10 := rfl
      omega

lemma eighteen_mul_le_pow_ten (L : ℕ) (hL : L ≥ 12) : 18 * L ≤ 10^(L-1) := by
  induction L with
  | zero => omega
  | succ L ih =>
    by_cases hL12 : L = 11
    · subst hL12
      decide
    · have hL_ge12 : L ≥ 12 := by omega
      have ih' := ih hL_ge12
      have h_sub_eq : L + 1 - 1 = (L - 1) + 1 := by omega
      rw [h_sub_eq]
      have h_pow : 10^(L-1+1) = 10^(L-1) * 10 := rfl
      rw [h_pow]
      have h_ten_L : 10^(L-1) ≥ 2 := by
        have : L - 1 ≥ 11 := by omega
        calc
          10^(L-1) ≥ 10^11 := Nat.pow_le_pow_right (by decide) this
          _ ≥ 2 := by decide
      omega

lemma exists_partner (n : ℕ) (hn : 0 < n) : ∃ k, k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n := by
  by_cases h_harshad : (digits 10 n).sum ∣ n
  · refine ⟨10 * n, by omega, by omega, dvd_mul_of_dvd_right h_harshad 10, ?_⟩
    rw [dsum_ten_mul n hn]
    exact h_harshad
  · by_cases h_pow : ∃ p, (digits 10 n).sum ∣ 10^p
    · obtain ⟨p, hp⟩ := h_pow
      exact exists_partner_of_pow_ten n hn p hp
    · by_cases h_dsum : (digits 10 (digits 10 n).sum).sum ∣ n
      · exact exists_partner_of_dsum_dsum n hn h_dsum
      · -- The final general case!
        -- Since n is not Harshad, we have n >= 10.
        have hn10 : n ≥ 10 := not_harshad_ge10 n hn h_harshad
        -- Since n >= 10, we can use finite_cases_less_than_28 for n < 28
        by_cases hn28 : n < 28
        · have hn_cases := finite_cases_less_than_28 n hn hn28 h_harshad h_pow h_dsum
          rcases hn_cases with (rfl | rfl | rfl)
          · -- n = 15
            apply exists_partner_of_multiple 15 (by decide) 12 (by decide)
            · rw [dsum_15]; decide
            · rw [dsum_12]; decide
          · -- n = 16
            apply exists_partner_of_multiple 16 (by decide) 35 (by decide)
            · rw [dsum_16]; decide
            · rw [dsum_35_val]; decide
          · -- n = 25
            apply exists_partner_of_multiple 25 (by decide) 14 (by decide)
            · rw [dsum_25]; decide
            · rw [dsum_14]; decide
        · -- n >= 28!
          let d := (digits 10 n).sum
          have hd_pos : d > 0 := dsum_pos n hn
          have hd_ge1 : d ≥ 1 := by omega
          let d_d := (digits 10 d).sum
          have hn_mod : n ≡ d [MOD 9] := modEq_digits_sum 9 10 (by decide) n
          have hd_mod : d ≡ d_d [MOD 9] := modEq_digits_sum 9 10 (by decide) d
          have h_trans : n ≡ d_d [MOD 9] := Nat.ModEq.trans hn_mod hd_mod
          have hd_le : d_d ≤ d := digit_sum_le 10 d
          have hd_le2 : d ≤ n := digit_sum_le 10 n
          have hdd_le_n : d_d ≤ n := by omega
          have h_mod_eq : n % 9 = d_d % 9 := h_trans
          have h_div9 : 9 ∣ n - d_d := by omega
          let M := (n - d_d) / 9
          have h_M_eq : 9 * M = n - d_d := Nat.mul_div_cancel' h_div9
          let A := (digits 10 d).length
          let m := d * (10^M - 1) * 10^A + d
          have hm_pos : m > 0 := by
            have h_pow_A : 10^A > 0 := Nat.pow_pos (by decide)
            have h_pow_M : 10^M > 0 := Nat.pow_pos (by decide)
            omega
          apply exists_partner_of_multiple n hn m hm_pos
          · -- d | m
            use (10^M - 1) * 10^A + 1
            ring
          · -- (digits 10 m).sum | n
            -- We want to prove D(m) | n.
            -- Actually, we can show D(m) = n.
            have h_len : (digits 10 (d - 1)).length ≤ M := by
              by_cases hd100 : d < 100
              · have : d - 1 < 10^2 := by omega
                have h_len2 : (digits 10 (d - 1)).length ≤ 2 := (digits_length_le_iff (by decide) (d-1)).mpr this
                have h_M2 : M ≥ 2 := by
                  have h_len_d : (digits 10 d).length ≤ 2 := by
                    apply (digits_length_le_iff (by decide) d).mpr
                    omega
                  have h_dd_le : d_d ≤ 18 := by
                    have h_dsum := dsum_le_nine_mul_len d
                    omega
                  omega
                omega
              · -- d >= 100
                -- Since d = D(n) >= 100, n is extremely large (n >= 10^11).
                -- We can classically prove this inequality since both hd100 and hn28 are true.
                have hd_ge100 : d ≥ 100 := by omega
                let L := (digits 10 n).length
                have h_d_le_9L : d ≤ 9 * L := dsum_le_nine_mul_len n
                have h_9L_ge100 : 9 * L ≥ 100 := by omega
                have h_L_ge12 : L ≥ 12 := by omega
                have h_L_pos : L ≥ 1 := by omega
                have h9_L : 9 * L < 10^L := nine_mul_lt_pow_ten L h_L_pos
                have hd_lt_pow : d < 10^L := by omega
                have hA_le_L : A ≤ L := (digits_length_le_iff (by decide) d).mpr hd_lt_pow
                have h_dd_le_9A : d_d ≤ 9 * A := dsum_le_nine_mul_len d
                have h_pow_le : 10^L ≤ 10 * n := base_pow_length_digits_le 10 n (by decide) (by omega)
                have h_pow_eq : 10^L = 10^(L-1) * 10 := by
                  have : L = (L - 1) + 1 := by omega
                  nth_rw 1 [this]
                  rfl
                rw [h_pow_eq] at h_pow_le
                have h_n_ge_pow : n ≥ 10^(L-1) := by omega
                have h_18L_le : 18 * L ≤ 10^(L-1) := eighteen_mul_le_pow_ten L h_L_ge12
                have h_n_ge_18L : n ≥ 18 * L := by omega
                have h_n_ge_9A_dd : n ≥ 9 * A + d_d := by omega
                have h_9M : 9 * M = n - d_d := h_M_eq
                have h_9A_le_9M : 9 * A ≤ 9 * M := by omega
                have hA_le_M : A ≤ M := by omega
                -- Now d - 1 < d < 10^A <= 10^M
                have hd_lt_pow_A : d < 10^A := (digits_length_le_iff (by decide) d).mp (Nat.le_refl A)
                have hd_sub_lt_pow_M : d - 1 < 10^M := by
                  have h_pow_mono : 10^A ≤ 10^M := Nat.pow_le_pow_right (by decide) hA_le_M
                  omega
                exact (digits_length_le_iff (by decide) (d - 1)).mpr hd_sub_lt_pow_M
            have h_sum_eq : (digits 10 m).sum = n := by
              have hm_eq : m = d + 10^((digits 10 d).length + 0) * (d * (10^M - 1)) := by ring
              rw [hm_eq]
              rw [dsum_append_zeroes 0 (d * (10^M - 1)) d]
              · rw [dsum_mul_pow_ten_sub_one d M hd_ge1 h_len]
                omega
              · have h_M2 : M ≥ 2 := by
                  by_cases hd100 : d < 100
                  · have h_len_d : (digits 10 d).length ≤ 2 := (digits_length_le_iff (by decide) d).mpr (by omega)
                    have h_dd_le : d_d ≤ 18 := by
                      have h_dsum := dsum_le_nine_mul_len d
                      omega
                    omega
                  · have h_len_d : (digits 10 (d - 1)).length ≥ 2 := by
                      apply (lt_digits_length_iff (by decide) (d - 1)).mpr
                      have h_pow10 : 10^1 = 10 := rfl
                      rw [h_pow10]
                      omega
                    omega
                have h_pow_M : 10^M ≥ 100 := by
                  calc
                    10^M ≥ 10^2 := Nat.pow_le_pow_right (by decide) h_M2
                    _ = 100 := rfl
                have h_sub_pos : 10^M - 1 > 0 := by omega
                apply Nat.mul_pos hd_pos h_sub_pos
            rw [h_sum_eq]

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp only
  have h_nonempty : ({k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ).Nonempty := by
    obtain ⟨k, hk_pos, hk_ne, hk_div1, hk_div2⟩ := exists_partner n hn
    exact ⟨k, hk_pos, hk_ne, hk_div1, hk_div2⟩
  split_ifs
  have h_mem : sInf {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} ∈ {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} :=
    Nat.sInf_mem h_nonempty
  simp only [Set.mem_setOf_eq] at h_mem
  obtain ⟨h_pos, _⟩ := h_mem
  omega
