import Submission.ShiftedFiniteExplore
import Submission.UniformRowFamilyExplore
import Submission.RowSparseShiftExplore

/-! The finite tapered block construction with its row bound retained. -/
namespace Erdos66ShiftedFiniteRows
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66ConstantProfile
  Erdos66FiniteTaper Erdos66ShiftedProfile Erdos66ShiftedBlock Erdos66ShiftedFinite
  Erdos66UniformRowFamily Erdos66RowSparsePrefix Erdos66RowSparseShift
open scoped Classical
set_option maxHeartbeats 1500000

/-- The prime precedes the thickness; the global upper bound includes all
integer targets, not only the useful annulus. -/
theorem exists_shifted_finite_blocks_with_rows (T s L N : ℕ)
    (hlevels : 1 ≤ (T : ℝ) ^ 2 * b (L + s)) :
    ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ ∀ K : ℕ, 0 < K →
      ∃ A : Set ℕ, A.Finite ∧ A ⊆ Set.Iio ((L + 1) * (p * K) ^ 2) ∧
        RowSparse A (p*K) (K*(4*T^2+4)) ∧
        (∀ n : ℕ, (sumRep A n : ℝ) ≤
          4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4 * (1 + b s ^ 2) + (2 * L + 3) * carryError T K) ∧
        ∀ q : ℕ, q ≤ L → ∀ t : ℕ, t < (p * K) ^ 2 →
          |(sumRep A (q * (p * K) ^ 2 + t) : ℝ) - 4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4| ≤
            4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4 * (2 * s * b q + b s ^ 2) +
              8 * (K : ℝ) ^ 2 * (T : ℝ) ^ 2 * (q + 1) + (q + 2) * carryError T K := by
  obtain ⟨p, hp, hpN, hfamily⟩ := exists_uniform_row_family T N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, fun K hK ↦ ?_⟩
  letI : NeZero K := ⟨by omega⟩
  let M := (p * K) ^ 2
  obtain ⟨C, hC, hrows, hcounts⟩ := hfamily K hK
  let D : ℕ → Finset (ZMod M) := fun k ↦ if k ≤ L then C (level (T ^ 2) (k + s)) else ∅
  let A := blockSet M D
  have hD : Antitone D := truncated_antitone M C hC (T ^ 2) s L
  have hsupport : A ⊆ Set.Iio ((L + 1) * M) := truncated_block_support M C (T ^ 2) s L
  have hAfin : A.Finite := (Set.finite_Iio _).subset hsupport
  have hβ : 0 ≤ 4 * (K : ℝ) ^ 2 := by positivity
  have hErr : 0 ≤ carryError T K := by dsimp [carryError, algebraError]; positivity
  have hpos (i : ℕ) (hi : i ≤ L) : 0 < level (T ^ 2) (i + s) := by
    apply level_pos_of_one_le
    have hh := mul_le_mul_of_nonneg_left (b_antitone (show i + s ≤ L + s by omega))
      (sq_nonneg (T : ℝ))
    push_cast
    linarith
  have hgood (i j : ℕ) (hi : i ≤ L) (hj : j ≤ L) (z : ZMod M) :
      |(((D i).filter (fun a ↦ z - a ∈ D j)).card : ℝ) -
        (4 * (K : ℝ) ^ 2) * (level (T ^ 2) (i + s) : ℝ) * level (T ^ 2) (j + s)| ≤ carryError T K := by
    dsimp only [D]
    rw [if_pos hi, if_pos hj]
    exact hcounts _ (hpos i hi) (level_le_H _ _) _ (hpos j hj) (level_le_H _ _) z
  have hupper (i j : ℕ) (z : ZMod M) :
      (((D i).filter (fun a ↦ z - a ∈ D j)).card : ℝ) ≤
        (4 * (K : ℝ) ^ 2) * (level (T ^ 2) (i + s) : ℝ) * level (T ^ 2) (j + s) + carryError T K := by
    by_cases hi : i ≤ L
    · by_cases hj : j ≤ L
      · have hh := (abs_le.mp (hgood i j hi hj z)).2
        linarith
      · dsimp only [D]
        simp only [if_pos hi, if_neg hj, Finset.notMem_empty, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
        positivity
    · dsimp only [D]
      simp only [if_neg hi, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      positivity
  have hsub : A ⊆ blockSet M (fun _ ↦ C (T^2)) := by
    intro a ha
    change (a : ZMod M)∈D (a/M) at ha
    change (a : ZMod M)∈C (T^2)
    dsimp only [D] at ha
    split_ifs at ha with hi
    · exact hC (level_le_H _ _) ha
    · exact False.elim (Finset.notMem_empty _ ha)
  have hrowA : RowSparse A (p*K) (K*(4*T^2+4)) := rowSparse_mono hsub hrows
  refine ⟨A, hAfin, hsupport, hrowA, ?_, ?_⟩
  · intro n
    by_cases hn : 2 * ((L + 1) * M) ≤ n
    · rw [sumRep_zero_of_bounded hsupport hn, Nat.cast_zero]
      positivity
    · let q := n / M
      let t := n % M
      have ht : t < M := Nat.mod_lt n (NeZero.pos M)
      have he : q * M + t = n := Nat.div_add_mod' n M
      have hq : q ≤ 2 * L + 1 := by
        have hMp : 0 < M := NeZero.pos M
        by_contra hq
        have hq' : 2 * L + 2 ≤ q := by omega
        nlinarith
      have hh := shifted_block_upper M D hD (T ^ 2) s q t ht
        (4 * (K : ℝ) ^ 2) (carryError T K) hβ hErr (fun i _ j _ ↦ hupper i j (t : ZMod M))
      push_cast at hh
      have hq' : (q : ℝ) + 1 ≤ 2 * L + 3 := by exact_mod_cast (show q + 1 ≤ 2 * L + 3 by omega)
      have he' := mul_le_mul_of_nonneg_right hq' hErr
      change (sumRep (blockSet M D) n : ℝ) ≤ _
      rw [← he]
      nlinarith
  · intro q hq t ht
    have hh := shifted_block_error M D hD (T ^ 2) s q t ht
      (4 * (K : ℝ) ^ 2) (carryError T K) hβ hErr
      (fun i hi j hj ↦ hgood i j (hi.trans hq) (hj.trans hq) (t : ZMod M))
    push_cast at hh
    dsimp only [A, M]
    convert hh using 2 <;> ring


end Erdos66ShiftedFiniteRows
