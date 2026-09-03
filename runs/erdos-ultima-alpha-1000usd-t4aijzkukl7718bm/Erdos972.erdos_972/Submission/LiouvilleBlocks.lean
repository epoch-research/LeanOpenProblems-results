import FormalConjecturesUtil

/-!
Divisibility blocks for a fixed Liouville slope. These obstruct overly strong
all-scale, arbitrary-coefficient bilinear estimates. They do not give a
counterexample to Erdős 972: the inputs in these blocks are composite.
-/
namespace Erdos972LiouvilleBlocks
open ArithmeticFunction Finset

noncomputable def slope : ℝ := 6 * (1 + liouvilleNumber 5)

theorem slope_irrational : Irrational slope := by
  have h := (liouville_liouvilleNumber (m := 5) (by decide)).irrational
  simpa [slope] using (h.natCast_add 1).natCast_mul (m := 6) (by decide)

theorem one_lt_slope : 1 < slope := by
  have h : 0 ≤ liouvilleNumber 5 := by
    exact tsum_nonneg (fun _ => by positivity)
  dsimp [slope]
  linarith

lemma vonMangoldt_eq_zero_of_six_dvd {n : ℕ} (hn : 6 ∣ n) : Λ n = 0 := by
  apply vonMangoldt_eq_zero_iff.mpr
  intro h
  obtain ⟨p, hp, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  have h2 := hu 2 ⟨Nat.prime_two, dvd_trans (by decide : 2 ∣ 6) hn⟩
  have h3 := hu 3 ⟨Nat.prime_three, dvd_trans (by decide : 3 ∣ 6) hn⟩
  omega

/-- The floor is exactly a multiple of six on a large rectangular collection
of product inputs. The denominator is `5^(j!)`. -/
theorem floor_on_block (K j : ℕ) (hj : 2 * K + 4 ≤ j) :
    ∃ a : ℕ, 6 ∣ a ∧ ∀ i m : ℕ,
      i ≤ (5 ^ j.factorial) ^ K → m ≤ (5 ^ j.factorial) ^ (K + 1) →
      ⌊slope * ((5 ^ j.factorial) * i) * m⌋₊ = a * i * m := by
  let b : ℕ := 5 ^ j.factorial
  let R : ℝ := LiouvilleNumber.remainder 5 j
  obtain ⟨p, hp⟩ := LiouvilleNumber.partialSum_eq_rat (m := 5) (by decide) j
  norm_num only [Nat.cast_ofNat] at hp
  have hb5 : 5 ≤ b := by
    exact Nat.le_self_pow (Nat.factorial_ne_zero j) 5
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hRpos : 0 < R := LiouvilleNumber.remainder_pos (by norm_num) j
  have hR : R < 1 / (b : ℝ) ^ j := by
    simpa [R, b, Nat.cast_pow] using
      LiouvilleNumber.remainder_lt j (m := (5 : ℝ)) (by norm_num)
  have hRT : R * (b : ℝ) ^ j < 1 :=
    (lt_div_iff₀ (pow_pos hbpos _)).mp hR
  have hdecomp : slope = 6 * (1 + p / (b : ℝ) + R) := by
    have h := LiouvilleNumber.partialSum_add_remainder (m := (5 : ℝ)) (by norm_num) j
    rw [hp] at h
    dsimp [slope, b, R]
    rw [← h]
    ring
  refine ⟨6 * (b + p), by omega, ?_⟩
  intro i m hi hm
  have hsize_nat : b * i * m ≤ b ^ (2 * K + 2) := by
    calc
      b * i * m ≤ (b * b ^ K) * b ^ (K + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left b hi) hm
      _ = b ^ (2 * K + 2) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
  have hsize : (b : ℝ) * i * m ≤ (b : ℝ) ^ (2 * K + 2) := by
    exact_mod_cast hsize_nat
  have hbsq : (25 : ℝ) ≤ (b : ℝ) ^ 2 := by
    have hb5' : (5 : ℝ) ≤ b := by exact_mod_cast hb5
    nlinarith
  have hpow : 25 * (b : ℝ) ^ (2 * K + 2) ≤ (b : ℝ) ^ j := by
    calc
      _ ≤ (b : ℝ) ^ 2 * (b : ℝ) ^ (2 * K + 2) :=
        mul_le_mul_of_nonneg_right hbsq (by positivity)
      _ = (b : ℝ) ^ (2 * K + 4) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (b : ℝ) ^ j := pow_le_pow_right₀ hb1 hj
  have hsmall : 6 * R * (b : ℝ) * i * m < 1 := by
    have h₁ := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 6 * R by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hpow hRpos.le
    have hP : 0 ≤ R * (b : ℝ) ^ (2 * K + 2) := by positivity
    nlinarith
  have he : slope * ((b : ℝ) * i) * m =
      (6 * (b + p) * i * m : ℕ) + 6 * R * (b : ℝ) * i * m := by
    rw [hdecomp]
    push_cast
    field_simp
  simp only [b, Nat.cast_pow, Nat.cast_ofNat] at he
  apply (Nat.floor_eq_iff (by rw [he]; positivity)).mpr
  rw [he]
  dsimp only [b] at hsmall ⊢
  push_cast at hsmall ⊢
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · linarith

/-- The von Mangoldt matrix vanishes on these blocks. -/
theorem vonMangoldt_on_block (K j : ℕ) (hj : 2 * K + 4 ≤ j) (i m : ℕ)
    (hi : i ≤ (5 ^ j.factorial) ^ K)
    (hm : m ≤ (5 ^ j.factorial) ^ (K + 1)) :
    Λ ⌊slope * ((5 ^ j.factorial) * i) * m⌋₊ = 0 := by
  obtain ⟨a, ha, hfloor⟩ := floor_on_block K j hj
  rw [hfloor i m hi hm]
  exact vonMangoldt_eq_zero_of_six_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ha i) m)

/-- In a full square of side `b^(K+1)`, taking only rows divisible by `b`
gives a discrepancy of exactly `-b^(2K+1)` from the constant-one matrix. -/
theorem block_discrepancy (K j : ℕ) (hj : 2 * K + 4 ≤ j) :
    (∑ i ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ K),
      ∑ m ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ (K + 1)),
        (Λ ⌊slope * ((5 ^ j.factorial) * i) * m⌋₊ - 1)) =
      -((5 : ℝ) ^ j.factorial) ^ (2 * K + 1) := by
  have hz : ∀ i ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ K),
      ∀ m ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ (K + 1)),
        (Λ ⌊slope * ((5 ^ j.factorial) * i) * m⌋₊ - 1) = -1 := by
    intro i hi m hm
    rw [vonMangoldt_on_block K j hj i m (mem_Icc.mp hi).2 (mem_Icc.mp hm).2]
    norm_num
  calc
    _ = ∑ i ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ K),
        ∑ m ∈ Icc (1 : ℕ) ((5 ^ j.factorial) ^ (K + 1)), (-1 : ℝ) := by
      apply sum_congr rfl
      intro i hi
      exact sum_congr rfl (hz i hi)
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        Nat.cast_pow]
      rw [← mul_assoc, ← pow_add]
      have he : K + (K + 1) = 2 * K + 1 := by omega
      simp only [he, Nat.cast_ofNat, mul_neg_one]

#print axioms slope_irrational
#print axioms block_discrepancy
end Erdos972LiouvilleBlocks
