import FormalConjecturesUtil
import Submission.CofactorSieve

/-! Rectangular cofactor sieve bounds. Unlike a common square box, a dyadic
rectangle costs a uniform multiple of `N / 4^k`, independently of its aspect
ratio. These are unsigned counting estimates. -/

namespace Erdos371CofactorRectangles

open Finset Erdos371CofactorSieve Erdos371SieveParameters
open Erdos371SieveEulerProduct Erdos371TwoLinearSieve

attribute [local instance] Classical.propDecidable

noncomputable def rectangle (k A U B V N : ℕ) : Finset ℕ :=
  (Icc A U).biUnion fun a => (Icc B V).biUnion fun b => cofactorInputs k a b N

lemma rectangle_card_bound {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (k U V N T : ℕ) (hT : N/(A*B)+1 ≤ T) (hlarge : threshold k ≤ T) :
    (rectangle k A U B V N).card ≤
      6*(Real.exp 1)^2*(T:ℝ)*U*V/(4:ℝ)^k := by
  let s := (cutoff k).primesBelow
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hc : (rectangle k A U B V N).card ≤
      ∑ a ∈ Icc A U, ∑ b ∈ Icc B V, (cofactorInputs k a b N).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  have hcard : (rectangle k A U B V N).card ≤
      (6*(T:ℝ)/(4:ℝ)^k) *
        (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a * weight s b) := by
    calc
      _ ≤ ∑ a ∈ Icc A U, ∑ b ∈ Icc B V, ((cofactorInputs k a b N).card:ℝ) := by
        exact_mod_cast hc
      _ ≤ ∑ a ∈ Icc A U, ∑ b ∈ Icc B V,
          6*(T:ℝ)*weight s a*weight s b/(4:ℝ)^k := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        have haA := (mem_Icc.mp ha).1
        have hbB := (mem_Icc.mp hb).1
        apply cofactorInputs_card_le (hA.trans_le haA) (hB.trans_le hbB) k N T _ hlarge
        have hden : A*B ≤ a*b := Nat.mul_le_mul haA hbB
        have hh := Nat.div_le_div_left hden (Nat.mul_pos hA hB) (a := N)
        omega
      _ = _ := by simp only [mul_sum]; congr 1; ext a; congr 1; ext b; ring
  have hsubA : Icc A U ⊆ Icc 1 U := by
    intro a ha
    obtain ⟨ha,hb⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega,hb⟩
  have hsubB : Icc B V ⊆ Icc 1 V := by
    intro b hb
    obtain ⟨ha,hb⟩ := mem_Icc.mp hb
    exact mem_Icc.mpr ⟨by omega,hb⟩
  have hsum : (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a*weight s b) ≤
      (Real.exp 1)^2*(U:ℝ)*V := by
    calc
      _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V, weight s a*weight s b := by
        apply (sum_le_sum (fun a _ =>
          sum_le_sum_of_subset_of_nonneg hsubB
            (fun b _ _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b)))).trans
        apply sum_le_sum_of_subset_of_nonneg hsubA
        intro a _ _
        exact sum_nonneg (fun b _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b))
      _ ≤ _ := weight_box_sum_le hs U V
  calc
    _ ≤ (6*(T:ℝ)/(4:ℝ)^k) *
        (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a*weight s b) := hcard
    _ ≤ (6*(T:ℝ)/(4:ℝ)^k) * ((Real.exp 1)^2*(U:ℝ)*V) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A dyadic rectangle has a bound independent of its aspect ratio. -/
theorem dyadic_rectangle_bound {A B N : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A*B ≤ N) (k : ℕ) (hlarge : threshold k ≤ N/(A*B)+1) :
    (rectangle k A (2*A) B (2*B) N).card ≤
      48*(Real.exp 1)^2*(N:ℝ)/(4:ℝ)^k := by
  have hh := rectangle_card_bound hA hB k (2*A) (2*B) N (N/(A*B)+1) le_rfl hlarge
  have hA' : (0:ℝ) < A := Nat.cast_pos.mpr hA
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB
  have hdiv : ((N/(A*B)+1:ℕ):ℝ) ≤ 2*(N:ℝ)/((A:ℝ)*B) := by
    have hcast : ((N/(A*B):ℕ):ℝ) ≤ (N:ℝ)/((A:ℝ)*B) := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := A*B))
    have hunit : (1:ℝ) ≤ (N:ℝ)/((A:ℝ)*B) := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa using (Nat.cast_le.mpr hAB : ((A*B:ℕ):ℝ) ≤ N)
    push_cast
    simp only [div_eq_mul_inv] at *
    linarith
  calc
    _ ≤ 6*(Real.exp 1)^2*((N/(A*B)+1:ℕ):ℝ)*((2*A:ℕ):ℝ)*((2*B:ℕ):ℝ)/(4:ℝ)^k := hh
    _ ≤ 6*(Real.exp 1)^2*(2*(N:ℝ)/((A:ℝ)*B))*((2*A:ℕ):ℝ)*((2*B:ℕ):ℝ)/(4:ℝ)^k := by
      gcongr
    _ = _ := by push_cast; field_simp; ring

/-- Include both orientations of the dyadic cofactor rectangle, and discard
boxes whose progression length is below the chosen sieve threshold. -/
noncomputable def admissibleBox (k i j N : ℕ) : Finset ℕ :=
  if 2^i*2^j ≤ N ∧ threshold k ≤ N/(2^i*2^j)+1 then
    rectangle k (2^i) (2*2^i) (2^j) (2*2^j) N ∪
      rectangle k (2^j) (2*2^j) (2^i) (2*2^i) N
  else ∅

lemma admissibleBox_card_bound (k i j N : ℕ) :
    (admissibleBox k i j N).card ≤ 96*(Real.exp 1)^2*(N:ℝ)/(4:ℝ)^k := by
  unfold admissibleBox
  split_ifs with h
  · have h1 := dyadic_rectangle_bound (Nat.two_pow_pos i) (Nat.two_pow_pos j) h.1 k h.2
    have h2 := dyadic_rectangle_bound (Nat.two_pow_pos j) (Nat.two_pow_pos i)
      (by simpa [mul_comm] using h.1) k (by simpa [mul_comm] using h.2)
    have hc := Nat.cast_le (α := ℝ) |>.mpr (card_union_le
      (rectangle k (2^i) (2*2^i) (2^j) (2*2^j) N)
      (rectangle k (2^j) (2*2^j) (2^i) (2*2^i) N))
    push_cast at hc
    exact hc.trans ((add_le_add h1 h2).trans_eq (by ring))
  · simp only [card_empty, Nat.cast_zero]
    positivity

noncomputable def diagonalCover (k L t N : ℕ) : Finset ℕ :=
  (range (t+1)).biUnion fun i => (Icc i (i+L)).biUnion fun j => admissibleBox k i j N

/-- Only the number of permitted dyadic aspect ratios is lost in the sum. -/
theorem diagonalCover_card_bound (k L t N : ℕ) :
    (diagonalCover k L t N).card ≤
      96*(Real.exp 1)^2*(N:ℝ)*(t+1:ℕ)*(L+1:ℕ)/(4:ℝ)^k := by
  have hc : (diagonalCover k L t N).card ≤
      ∑ i ∈ range (t+1), ∑ j ∈ Icc i (i+L), (admissibleBox k i j N).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  calc
    _ ≤ ∑ i ∈ range (t+1), ∑ j ∈ Icc i (i+L), ((admissibleBox k i j N).card:ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ i ∈ range (t+1), ∑ _j ∈ Icc i (i+L),
        96*(Real.exp 1)^2*(N:ℝ)/(4:ℝ)^k :=
      sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => admissibleBox_card_bound _ _ _ _))
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]
      have he (i : ℕ) : i+L+1-i=L+1 := by omega
      simp only [he, sum_const, card_range, nsmul_eq_mul]
      ring

end Erdos371CofactorRectangles

#print axioms Erdos371CofactorRectangles.dyadic_rectangle_bound
#print axioms Erdos371CofactorRectangles.diagonalCover_card_bound
