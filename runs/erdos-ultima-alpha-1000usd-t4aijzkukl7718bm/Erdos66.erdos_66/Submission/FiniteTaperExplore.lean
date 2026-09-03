import Submission.IntegerBlockExplore
import Submission.ConstantProfileExplore

/-! Quantitative finite tapering on the natural-number line. This file does
not assert compatibility between distinct periods. -/
namespace Erdos66FiniteTaper
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66ConstantProfile
open scoped Classical

noncomputable def level (H k : ℕ) : ℕ := ⌊(H : ℝ) * b k⌋₊

lemma level_le (H k : ℕ) : (level H k : ℝ) ≤ (H : ℝ) * b k :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (b_pos k).le)

lemma level_error (H k : ℕ) : (H : ℝ) * b k - (level H k : ℝ) ≤ 1 := by
  have hh := Nat.lt_floor_add_one ((H : ℝ) * b k)
  dsimp [level]
  linarith

lemma level_zero (H : ℕ) : level H 0 = H := by simp [level]

lemma level_antitone (H : ℕ) : Antitone (level H) := by
  intro i j hij
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (b_antitone hij) (Nat.cast_nonneg _)

lemma level_le_H (H k : ℕ) : level H k ≤ H := by
  simpa only [level_zero] using level_antitone H (Nat.zero_le k)

lemma level_pos_of_one_le (H k : ℕ) (h : 1 ≤ (H : ℝ) * b k) : 0 < level H k := by
  have hh : 1 ≤ level H k := (Nat.le_floor_iff (mul_nonneg (Nat.cast_nonneg _) (b_pos k).le)).mpr (by simpa using h)
  omega

lemma level_product_bounds (H i j : ℕ) :
    (H : ℝ) ^ 2 * (b i * b j) - 2 * H ≤ (level H i : ℝ) * level H j ∧
      (level H i : ℝ) * level H j ≤ (H : ℝ) ^ 2 * (b i * b j) := by
  have hi := level_le H i
  have hj := level_le H j
  have hei := level_error H i
  have hej := level_error H j
  have hH := Nat.cast_nonneg (α := ℝ) H
  have hui := Nat.cast_nonneg (α := ℝ) (level H i)
  have huj := Nat.cast_nonneg (α := ℝ) (level H j)
  have hbi := (b_pos i).le
  have hbj := (b_pos j).le
  have hprod := mul_le_mul hi hj huj (mul_nonneg hH hbi)
  have he₁ := mul_le_mul_of_nonneg_right hei (mul_nonneg hH hbj)
  have he₂ := mul_le_mul_of_nonneg_left hej hui
  have hib := mul_le_mul_of_nonneg_left (b_le_one i) hH
  have hjb := mul_le_mul_of_nonneg_left (b_le_one j) hH
  constructor <;> nlinarith

lemma level_convolution_bounds (H q : ℕ) :
    (H : ℝ) ^ 2 - 2 * H * (q + 1) ≤
      (∑ k ∈ Finset.range (q + 1), (level H k : ℝ) * level H (q - k)) ∧
    (∑ k ∈ Finset.range (q + 1), (level H k : ℝ) * level H (q - k)) ≤ (H : ℝ) ^ 2 := by
  have he : (∑ k ∈ Finset.range (q + 1), b k * b (q - k)) = 1 := by
    simpa only [sumConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using b_convolution q
  have h₁ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k _ ↦ (level_product_bounds H k (q - k)).1)
  have h₂ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k _ ↦ (level_product_bounds H k (q - k)).2)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h₁ h₂
  constructor <;> nlinarith

lemma level_endpoint_bound (H q : ℕ) :
    (level H q : ℝ) * level H 0 ≤ (H : ℝ) ^ 2 * b q := by
  rw [level_zero]
  have hh := mul_le_mul_of_nonneg_right (level_le H q) (Nat.cast_nonneg (α := ℝ) H)
  nlinarith

/-- A finite taper made from nested cyclic sets. The error separates rounding,
endpoint, and cyclic-convolution contributions. -/
theorem taper_count_bound (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (hC : Antitone C) (H q t : ℕ) (hq : 0 < q) (ht : t < M)
    (β D : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hcounts : ∀ i ≤ q, ∀ j ≤ q,
      |(((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ) -
        β * (level H i : ℝ) * level H j| ≤ D) :
    |(sumRep (blockSet M C) (q * M + t) : ℝ) - β * H ^ 2| ≤
      β * (2 * H * (q + 1) + (H : ℝ) ^ 2 * b q) + (q + 2) * D := by
  let R (i j : ℕ) : ℝ := (((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ)
  have hr (i j : ℕ) (hi : i ≤ q) (hj : j ≤ q) :
      β * (level H i : ℝ) * level H j - D ≤ R i j ∧
      R i j ≤ β * (level H i : ℝ) * level H j + D := by
    have hh := abs_le.mp (hcounts i hi j hj)
    dsimp [R]
    constructor <;> linarith
  have hlow₀ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k hk ↦ (hr k (q - k) (by have := Finset.mem_range.mp hk; omega) (by omega)).1)
  have hupp₀ := Finset.sum_le_sum (s := Finset.range q)
    (fun k hk ↦ (hr k (q - k - 1) (by have := Finset.mem_range.mp hk; omega) (by omega)).2)
  have he₀ := (hr q 0 le_rfl (Nat.zero_le q)).2
  have hlevel := level_convolution_bounds H q
  have hlevel' : (∑ k ∈ Finset.range q, (level H k : ℝ) * level H (q - k - 1)) ≤
      (H : ℝ) ^ 2 := by
    have hh := (level_convolution_bounds H (q - 1)).2
    have hq' : q - 1 + 1 = q := by omega
    rw [hq'] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show q - k - 1 = q - 1 - k by omega]
  have hlow : β * ((H : ℝ) ^ 2 - 2 * H * (q + 1)) - (q + 1) * D ≤
      ∑ k ∈ Finset.range (q + 1), R k (q - k) := by
    simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hlow₀
    have hh := mul_le_mul_of_nonneg_left hlevel.1 hβ
    nlinarith
  have hupp : (∑ k ∈ Finset.range q, R k (q - k - 1)) ≤ β * (H : ℝ) ^ 2 + q * D := by
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hupp₀
    have hh := mul_le_mul_of_nonneg_left hlevel' hβ
    nlinarith
  have hend : R q 0 ≤ β * (H : ℝ) ^ 2 * b q + D := by
    have hh := mul_le_mul_of_nonneg_left (level_endpoint_bound H q) hβ
    nlinarith
  have hfiber := lower_add_upper M (C q) (C 0) t
  have hL : (lower M (C q) (C 0) t : ℝ) ≤ R q 0 := by
    dsimp [R]
    exact_mod_cast (show lower M (C q) (C 0) t ≤
      ((C q).filter (fun a ↦ (t : ZMod M) - a ∈ C 0)).card by omega)
  have hU : (upper M (C q) (C 0) t : ℝ) ≤ R q 0 := by
    dsimp [R]
    exact_mod_cast (show upper M (C q) (C 0) t ≤
      ((C q).filter (fun a ↦ (t : ZMod M) - a ∈ C 0)).card by omega)
  have hb := block_brackets M C hC q t ht
  have hb₁ : (∑ k ∈ Finset.range (q + 1), R k (q - k)) ≤
      (sumRep (blockSet M C) (q * M + t) : ℝ) + upper M (C q) (C 0) t := by
    dsimp [R]
    exact_mod_cast hb.1
  have hb₂ : (sumRep (blockSet M C) (q * M + t) : ℝ) ≤
      (∑ k ∈ Finset.range q, R k (q - k - 1)) + lower M (C q) (C 0) t := by
    dsimp [R]
    exact_mod_cast hb.2
  have hextra : 0 ≤ β * (2 * (H : ℝ) * (q + 1)) + D := by positivity
  rw [abs_le]
  constructor <;> nlinarith

lemma sumRep_restrict_below (A : Set ℕ) (L n : ℕ) (hn : n < L) :
    sumRep (A ∩ Set.Iio L) n = sumRep A n := by
  rw [sumRep_def, sumRep_def]
  congr 1
  ext ab
  simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_inter_iff, Set.mem_Iio]
  constructor
  · rintro ⟨hs, ⟨ha, haL⟩, ⟨hb, hbL⟩⟩
    exact ⟨hs, ha, hb⟩
  · rintro ⟨hs, ha, hb⟩
    exact ⟨hs, ⟨ha, by omega⟩, ⟨hb, by omega⟩⟩

noncomputable def algebraError (T : ℕ) : ℝ := 6 * T ^ 3 + 20 * T ^ 2 + 8

noncomputable def carryError (T K : ℕ) : ℝ :=
  (K : ℝ) ^ 2 * algebraError T + 2 * K * (4 * (T : ℝ) ^ 4 + algebraError T)

/-- Finite integer sets, with an explicit tapered representation bound.
The prime is chosen before the thickening parameter K, permitting later
logarithmic tuning of K. This does not make the finite sets compatible. -/
theorem exists_tapered_integer_blocks (T L N : ℕ)
    (hlevels : 1 ≤ ((T : ℝ) ^ 2) * b L) :
    ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ ∀ K : ℕ, 0 < K →
      ∃ A : Set ℕ, A.Finite ∧ ∀ q : ℕ, 0 < q → q ≤ L →
        ∀ t : ℕ, t < (p * K) ^ 2 →
          |(sumRep A (q * (p * K) ^ 2 + t) : ℝ) - 4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4| ≤
            4 * (K : ℝ) ^ 2 * (2 * (T : ℝ) ^ 2 * (q + 1) + (T : ℝ) ^ 4 * b q) +
              (q + 2) * carryError T K := by
  obtain ⟨p, hp, hpN, hp8, B, hmono, E, hB⟩ :=
    Erdos66RectangleRepair.exists_mixed_flat_prime_family (T ^ 2) N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, ?_⟩
  intro K hK
  letI : NeZero K := ⟨by omega⟩
  let M := (p * K) ^ 2
  let C : ℕ → Finset (ZMod M) := fun k ↦
    Erdos66CyclicThickening.thickenedSet p K (B (level (T ^ 2) k))
  have hC : Antitone C := by
    intro i j hij
    exact Erdos66MixedCyclicThickening.thickenedSet_mono p K
      (hmono (level_antitone (T ^ 2) hij))
  let A := blockSet M C ∩ Set.Iio ((L + 1) * M)
  refine ⟨A, (Set.finite_Iio _).subset Set.inter_subset_right, ?_⟩
  intro q hq hqL t ht
  have hb (i j : ℕ) (hi : i ≤ q) (hj : j ≤ q) :
      |(((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ) -
        (4 * (K : ℝ) ^ 2) * (level (T ^ 2) i : ℝ) * level (T ^ 2) j| ≤ carryError T K := by
    have hip : 0 < level (T ^ 2) i := by
      apply level_pos_of_one_le
      have hh := mul_le_mul_of_nonneg_left (b_antitone (show i ≤ L by omega))
        (sq_nonneg (T : ℝ))
      push_cast
      linarith
    have hjp : 0 < level (T ^ 2) j := by
      apply level_pos_of_one_le
      have hh := mul_le_mul_of_nonneg_left (b_antitone (show j ≤ L by omega))
        (sq_nonneg (T : ℝ))
      push_cast
      linarith
    obtain ⟨hE0, hEsq, hcounts⟩ := hB (level (T ^ 2) i) hip (level_le_H _ _)
      (level (T ^ 2) j) hjp (level_le_H _ _)
    have hui : (level (T ^ 2) i : ℝ) ≤ (T : ℝ) ^ 2 := by exact_mod_cast level_le_H (T ^ 2) i
    have huj : (level (T ^ 2) j : ℝ) ≤ (T : ℝ) ^ 2 := by exact_mod_cast level_le_H (T ^ 2) j
    let e : ℝ := E (level (T ^ 2) i) (level (T ^ 2) j)
    have he0 : 0 ≤ e := by dsimp [e]; exact_mod_cast hE0
    have hesq : e ^ 2 ≤ 16 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j *
        (level (T ^ 2) i + level (T ^ 2) j) := by dsimp [e]; exact_mod_cast hEsq
    have hepoly : 16 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j *
        (level (T ^ 2) i + level (T ^ 2) j) ≤ 32 * (T : ℝ) ^ 6 := by
      calc
        _ ≤ 16 * (T : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((T : ℝ) ^ 2 + (T : ℝ) ^ 2) := by gcongr
        _ = _ := by ring
    have he : e ≤ 6 * (T : ℝ) ^ 3 := by
      have hnon : 0 ≤ 6 * (T : ℝ) ^ 3 := by positivity
      apply (sq_le_sq₀ he0 hnon).mp
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) T) 6]
    have hμ : 4 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j ≤ 4 * (T : ℝ) ^ 4 := by
      calc
        _ ≤ 4 * (T : ℝ) ^ 2 * (T : ℝ) ^ 2 := by gcongr
        _ = _ := by ring
    have hErr : e + 10 * (level (T ^ 2) i : ℝ) + 10 * level (T ^ 2) j + 8 ≤ algebraError T := by
      dsimp [algebraError]
      linarith
    have hbase : ∀ x y : ZMod p,
        |((Erdos66MixedCyclicThickening.mixedFiber p (B (level (T ^ 2) i))
          (B (level (T ^ 2) j)) x y).card : ℝ) -
          4 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j| ≤
            e + 10 * (level (T ^ 2) i : ℝ) + 10 * level (T ^ 2) j + 8 := by
      intro x y
      have hh := hcounts (x, y)
      change |((Erdos66MixedCyclicThickening.mixedFiber p (B (level (T ^ 2) i))
        (B (level (T ^ 2) j)) x y).card : ℤ) -
        4 * level (T ^ 2) i * level (T ^ 2) j| ≤ _ at hh
      dsimp [e]
      exact_mod_cast hh
    have hh := Erdos66MixedCyclicThickening.thickenedSet_error p K
      (B (level (T ^ 2) i)) (B (level (T ^ 2) j))
      (4 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j)
      (e + 10 * (level (T ^ 2) i : ℝ) + 10 * level (T ^ 2) j + 8) hbase (t : ZMod M)
    have hbig : (K : ℝ) ^ 2 * (e + 10 * (level (T ^ 2) i : ℝ) + 10 * level (T ^ 2) j + 8) +
        2 * K * (4 * (level (T ^ 2) i : ℝ) * level (T ^ 2) j +
          (e + 10 * (level (T ^ 2) i : ℝ) + 10 * level (T ^ 2) j + 8)) ≤ carryError T K := by
      dsimp [carryError]
      gcongr
    dsimp only [C]
    convert hh.trans hbig using 2 <;> ring
  have hh := taper_count_bound M C hC (T ^ 2) q t hq ht (4 * (K : ℝ) ^ 2)
    (carryError T K) (by positivity) (by dsimp [carryError, algebraError]; positivity)
    (fun i hi j hj ↦ hb i j hi hj)
  have hsmall : q * M + t < (L + 1) * M := by
    have hMp : 0 < M := pow_pos (Nat.mul_pos hp.pos hK) 2
    have htM : t < M := ht
    nlinarith
  have heq : sumRep A (q * M + t) = sumRep (blockSet M C) (q * M + t) :=
    sumRep_restrict_below _ _ _ hsmall
  rw [heq]
  push_cast at hh
  dsimp only [M] at hh ⊢
  convert hh using 2 <;> ring

lemma algebraError_bound (T : ℕ) (hT : 1 ≤ T) : algebraError T ≤ 34 * (T : ℝ) ^ 3 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h₂ : (T : ℝ) ^ 2 ≤ (T : ℝ) ^ 3 := by nlinarith [sq_nonneg ((T : ℝ) - 1)]
  have h₃ : (1 : ℝ) ≤ (T : ℝ) ^ 3 := one_le_pow₀ hT'
  dsimp [algebraError]
  linarith

lemma carryError_bound (T K : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K) :
    carryError T K ≤ 112 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hTK' : (T : ℝ) ≤ K := by exact_mod_cast hTK
  calc
    carryError T K ≤ (K : ℝ) ^ 2 * (34 * (T : ℝ) ^ 3) +
        2 * K * (4 * (T : ℝ) ^ 4 + 34 * (T : ℝ) ^ 3) := by
      dsimp [carryError]
      gcongr <;> exact algebraError_bound T hT
    _ = 34 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 + 8 * K * (T : ℝ) ^ 3 * T +
        68 * K * (T : ℝ) ^ 3 * 1 := by ring
    _ ≤ 34 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 + 8 * K * (T : ℝ) ^ 3 * K +
        68 * K * (T : ℝ) ^ 3 * K := by gcongr
    _ ≤ 112 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (K : ℝ)) (pow_nonneg (Nat.cast_nonneg (α := ℝ) T) 3)]

lemma taper_error_bound (T K q L : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K) (hqL : q ≤ L) :
    4 * (K : ℝ) ^ 2 * (2 * (T : ℝ) ^ 2 * (q + 1) + (T : ℝ) ^ 4 * b q) +
        (q + 2) * carryError T K ≤
      4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4 * b q +
        128 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * (L + 2) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h₂ : (T : ℝ) ^ 2 ≤ (T : ℝ) ^ 3 := by nlinarith [sq_nonneg ((T : ℝ) - 1)]
  have hqL' : (q : ℝ) ≤ L := by exact_mod_cast hqL
  calc
    _ ≤ 4 * (K : ℝ) ^ 2 * (2 * (T : ℝ) ^ 3 * (L + 1) + (T : ℝ) ^ 4 * b q) +
        (L + 2) * (112 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3) := by
      gcongr
      · dsimp [carryError, algebraError]; positivity
      · exact carryError_bound T K hT hTK
    _ ≤ _ := by
      have hh : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by positivity
      have hh' : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * L := by positivity
      nlinarith

end Erdos66FiniteTaper
