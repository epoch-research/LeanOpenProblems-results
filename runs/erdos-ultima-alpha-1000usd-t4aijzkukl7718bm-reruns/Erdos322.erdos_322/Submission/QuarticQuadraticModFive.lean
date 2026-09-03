import FormalConjecturesUtil

/-! A finite-field obstruction to quadratic quartic-norm squaring with
multiplier congruent to four modulo five. This is not a count bound. -/
namespace Erdos322Research.QuarticQuadraticModFive
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Vec := Fin 4 → ZMod 5

def zeroCount (x : Vec) : ℕ := (univ.filter (fun i ↦ x i = 0)).card

def middle : Finset Vec := univ.filter (fun x ↦ zeroCount x = 1 ∨ zeroCount x = 2)

lemma fourth_value (a : ZMod 5) : a ^ 4 = if a = 0 then 0 else 1 := by
  by_cases h : a = 0
  · simp [h]
  · simpa [h] using (FiniteField.pow_card_sub_one_eq_one a h)

lemma zeroCount_le (x : Vec) : zeroCount x ≤ 4 := by
  exact (card_filter_le _ _).trans (by simp)

lemma sum_fourth (x : Vec) : ∑ i, x i ^ 4 = 4 - (zeroCount x : ZMod 5) := by
  have h : ∀ i, x i ^ 4 + (if x i = 0 then (1 : ZMod 5) else 0) = 1 := by
    intro i
    rw [fourth_value]
    split_ifs <;> norm_num
  have hs := congrArg (fun f : Fin 4 → ZMod 5 ↦ ∑ i, f i) (funext h)
  simp only [sum_add_distrib, sum_boole, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  change (∑ i, x i ^ 4) + (zeroCount x : ZMod 5) = 4 * 1 at hs
  linear_combination hs

lemma zeroCount_of_sum_one (a : Vec) (h : ∑ i, a i ^ 4 = 1) : zeroCount a = 3 := by
  rw [sum_fourth] at h
  have hb := zeroCount_le a
  generalize zeroCount a = z at h hb ⊢
  interval_cases z <;> first | rfl | (revert h; decide)

lemma middle_forces_three (a x : Vec) (hx : x ∈ middle)
    (h : ∑ i, a i ^ 4 = 4 * (∑ i, x i ^ 4) ^ 2) : zeroCount a = 3 := by
  apply zeroCount_of_sum_one
  rw [h, sum_fourth]
  have hx' : zeroCount x = 1 ∨ zeroCount x = 2 := (mem_filter.mp hx).2
  rcases hx' with hx' | hx' <;> rw [hx'] <;> decide

lemma middle_card : middle.card = 352 := by decide +kernel

lemma quadratic_zero_bound (P : MvPolynomial (Fin 4) (ZMod 5))
    (hP : P ≠ 0) (hdeg : P.totalDegree ≤ 2) :
    (univ.filter (fun x : Vec ↦ MvPolynomial.eval x P = 0)).card ≤ 250 := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset (ZMod 5))
  have hpi : Fintype.piFinset (fun _ : Fin 4 ↦ (univ : Finset (ZMod 5))) = univ := by
    ext x
    simp
  rw [hpi] at h
  norm_num at h
  have hmul := (div_le_div_iff₀ (by norm_num : (0 : ℚ≥0) < 625)
    (by norm_num : (0 : ℚ≥0) < 5)).mp h
  have hm : (univ.filter (fun x : Vec ↦ MvPolynomial.eval x P = 0)).card * 5 ≤
      P.totalDegree * 625 := by exact_mod_cast hmul
  omega

lemma zero_double_count (P : Fin 4 → MvPolynomial (Fin 4) (ZMod 5)) :
    (∑ i, (univ.filter (fun x : Vec ↦ MvPolynomial.eval x (P i) = 0)).card) =
      ∑ x : Vec, zeroCount (fun i ↦ MvPolynomial.eval x (P i)) := by
  simp only [zeroCount, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- Even allowing arbitrary quadratic polynomials, there is no norm-squaring
formula with multiplier four over the five-element field. -/
theorem no_quadratic_square_multiplier_four
    (P : Fin 4 → MvPolynomial (Fin 4) (ZMod 5))
    (hdeg : ∀ i, (P i).totalDegree ≤ 2) :
    ¬ (∀ x : Vec, ∑ i, (MvPolynomial.eval x (P i)) ^ 4 =
      4 * (∑ i, x i ^ 4) ^ 2) := by
  intro h
  let e : Vec := ![1, 0, 0, 0]
  have he : ∑ i, (MvPolynomial.eval e (P i)) ^ 4 = 4 := by
    simpa [e, Fin.sum_univ_four] using h e
  have hz : zeroCount (fun i ↦ MvPolynomial.eval e (P i)) = 0 := by
    rw [sum_fourth] at he
    have hb := zeroCount_le (fun i ↦ MvPolynomial.eval e (P i))
    generalize zeroCount (fun i ↦ MvPolynomial.eval e (P i)) = z at he hb ⊢
    interval_cases z <;> first | rfl | (revert he; decide)
  have hp (i : Fin 4) : P i ≠ 0 := by
    intro hi
    have hf : i ∈ univ.filter (fun j ↦ MvPolynomial.eval e (P j) = 0) := by simp [hi]
    have hc := card_pos.mpr ⟨i, hf⟩
    change 0 < zeroCount (fun j ↦ MvPolynomial.eval e (P j)) at hc
    omega
  have hupper : (∑ i, (univ.filter (fun x : Vec ↦ MvPolynomial.eval x (P i) = 0)).card) ≤ 1000 := by
    calc
      _ ≤ ∑ i : Fin 4, 250 := sum_le_sum (fun i _ ↦ quadratic_zero_bound (P i) (hp i) (hdeg i))
      _ = 1000 := by norm_num
  have hlower : 1056 ≤ ∑ x : Vec, zeroCount (fun i ↦ MvPolynomial.eval x (P i)) := by
    calc
      1056 = ∑ _x ∈ middle, 3 := by rw [sum_const, middle_card]; norm_num
      _ = ∑ x ∈ middle, zeroCount (fun i ↦ MvPolynomial.eval x (P i)) := by
        apply sum_congr rfl
        intro x hx
        exact (middle_forces_three _ x hx (h x)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
  rw [zero_double_count] at hupper
  omega

end Erdos322Research.QuarticQuadraticModFive
