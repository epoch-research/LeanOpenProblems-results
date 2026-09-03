import Submission.RootScaleArc

/-! Exact conversion of one Mangoldt factor along a Beatty row into a weighted
rotation-arc sum. This does not impose primality on the row index. -/
namespace Erdos972BeattyRows

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972WeightedPrimeRotation

lemma fract_sub_center {x a : ℝ} (ha : 0 < a) (ha2 : a < 1/2) :
    (a ≤ Int.fract (x-a) ∧ Int.fract (x-a) < 1-a) ↔ 2*a ≤ Int.fract x := by
  have he : Int.fract (x-a) = Int.fract (Int.fract x-a) := by
    have hh : x-a = (Int.fract x-a) + (⌊x⌋ : ℝ) := by linarith [Int.fract_add_floor x]
    rw [hh, Int.fract_add_intCast]
  rw [he]
  by_cases hx : a ≤ Int.fract x
  · rw [Int.fract_eq_self.mpr (show 0 ≤ Int.fract x-a ∧ Int.fract x-a < 1 by
      constructor <;> linarith [Int.fract_lt_one x])]
    constructor
    · intro hh
      linarith [hh.1]
    · intro hh
      constructor <;> linarith [Int.fract_lt_one x]
  · have hh : Int.fract (Int.fract x-a) = Int.fract x-a+1 := by
      rw [← Int.fract_add_one]
      apply Int.fract_eq_self.mpr
      constructor <;> linarith [Int.fract_nonneg x]
    rw [hh]
    constructor
    · intro h
      linarith [h.2, Int.fract_nonneg x]
    · intro h
      exfalso
      linarith

lemma floorMul_frac_lower {β : ℝ} (hβ : 1 < β) (hI : Irrational β) {n : ℕ} (hn : 0 < n) :
    1-1/β ≤ Int.fract ((floorMul β n : ℝ)/β) := by
  have hβ0 : 0 < β := by linarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlo : (floorMul β n : ℝ) ≤ β*n := Nat.floor_le (by positivity)
  have hhi : β*n < (floorMul β n : ℝ)+1 := Nat.lt_floor_add_one _
  have hne := (hI.mul_natCast (Nat.ne_of_gt hn)).ne_nat (floorMul β n)
  have hlo' : (floorMul β n : ℝ) < β*n := lt_of_le_of_ne hlo (Ne.symm hne)
  have hn1 : 1 ≤ n := hn
  have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
  have hfloor : ⌊(floorMul β n : ℝ)/β⌋₊ = n-1 := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    rw [hcast]
    constructor
    · apply (le_div_iff₀ hβ0).mpr
      nlinarith
    · apply (div_lt_iff₀ hβ0).mpr
      nlinarith
  rw [Int.fract, ← Int.natCast_floor_eq_floor (show 0 ≤ (floorMul β n : ℝ)/β by positivity)]
  simp only [hfloor, Int.cast_natCast, hcast]
  have hdiv : (n : ℝ)-1/β ≤ (floorMul β n : ℝ)/β := by
    apply (le_div_iff₀ hβ0).mpr
    have hh : ((n : ℝ)-1/β)*β = β*n-1 := by field_simp
    rw [hh]
    linarith
  linarith

lemma floorMul_image_iff {β : ℝ} (hβ : 1 < β) (hI : Irrational β) (N q : ℕ) (hq : 0 < q) :
    (∃ n ∈ Ioc 0 N, floorMul β n = q) ↔
      q ≤ floorMul β N ∧ 1-1/β ≤ Int.fract ((q : ℝ)/β) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(floorMul_strictMono hβ.le).monotone (mem_Ioc.mp hn).2,
      floorMul_frac_lower hβ hI (mem_Ioc.mp hn).1⟩
  · rintro ⟨hqN, hfrac⟩
    let n := ⌊(q : ℝ)/β⌋₊+1
    have hn : 0 < n := by dsimp [n]; omega
    have hβ0 : 0 < β := by linarith
    have hnR : (n : ℝ) = (⌊(q : ℝ)/β⌋₊ : ℝ)+1 := by dsimp [n]; push_cast; rfl
    have hlt : (q : ℝ) < β*n := by
      have hh := Nat.lt_floor_add_one ((q : ℝ)/β)
      rw [← hnR] at hh
      nlinarith [(div_lt_iff₀ hβ0).mp hh]
    have hle : β*n ≤ (q : ℝ)+1 := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor (show 0 ≤ (q : ℝ)/β by positivity)] at hfrac
      simp only [Int.cast_natCast] at hfrac
      have hh := mul_le_mul_of_nonneg_right hfrac hβ0.le
      have he : (1-1/β)*β = β-1 := by field_simp
      have he' : ((q : ℝ)/β - (⌊(q : ℝ)/β⌋₊ : ℝ))*β = q-β*(n-1) := by
        rw [hnR]
        field_simp
        ring
      rw [he, he'] at hh
      linarith
    have hne : β*n ≠ (q : ℝ)+1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (hI.mul_natCast (Nat.ne_of_gt hn)).ne_nat (q+1)
    have heq : floorMul β n = q := by
      exact (Nat.floor_eq_iff (show 0 ≤ β*n by positivity)).mpr ⟨hlt.le, lt_of_le_of_ne hle hne⟩
    refine ⟨n, mem_Ioc.mpr ⟨hn, ?_⟩, heq⟩
    exact (floorMul_strictMono hβ.le).le_iff_le.mp (heq ▸ hqN)

noncomputable def rowArcLeft (β : ℝ) : ℝ := (1-1/β)/2

lemma rowArcLeft_bounds {β : ℝ} (hβ : 1 < β) : 0 < rowArcLeft β ∧ rowArcLeft β < 1/2 := by
  have hβ0 : 0 < β := by linarith
  have hh : 1/β < (1:ℝ) := (div_lt_one hβ0).mpr hβ
  have hh0 : 0 < 1/β := by positivity
  unfold rowArcLeft
  constructor <;> linarith

noncomputable def mangoldtRow (β : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, vonMangoldt (floorMul β n)

/-- An exact finite row identity, including the original floor endpoints. -/
theorem mangoldtRow_eq_arc {β : ℝ} (hβ : 1 < β) (hI : Irrational β) (N : ℕ) :
    mangoldtRow β N = mangoldtArcSum (1/β) (-rowArcLeft β) (rowArcLeft β) (1-rowArcLeft β) (floorMul β N) := by
  classical
  have hb := rowArcLeft_bounds hβ
  have himage : (Ioc 0 N).image (floorMul β) =
      (Ioc 0 (floorMul β N)).filter (fun q : ℕ => rowArcLeft β ≤ Int.fract ((1/β)*q-rowArcLeft β) ∧
        Int.fract ((1/β)*q-rowArcLeft β) < 1-rowArcLeft β) := by
    ext q
    rw [mem_image, mem_filter, mem_Ioc]
    by_cases hq : 0 < q
    · rw [fract_sub_center hb.1 hb.2]
      have he : 2*rowArcLeft β = 1-1/β := by unfold rowArcLeft; ring
      rw [he, one_div_mul_eq_div, floorMul_image_iff hβ hI N q hq]
      tauto
    · constructor
      · rintro ⟨n, hn, he⟩
        exact (hq (he ▸ floorMul_pos hβ.le (mem_Ioc.mp hn).1)).elim
      · intro hh
        exact (hq hh.1.1).elim
  unfold mangoldtRow mangoldtArcSum
  rw [← sum_image (fun n hn m hm he => (floorMul_strictMono hβ.le).injective he), himage]
  congr 1

#print axioms floorMul_image_iff
#print axioms mangoldtRow_eq_arc

end Erdos972BeattyRows
