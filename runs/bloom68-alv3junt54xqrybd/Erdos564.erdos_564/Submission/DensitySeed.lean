import Submission.SmallRamsey

/-!
# Quantitative parity lower bound for monochromatic quadruples

This file is independent of `Submission.Spec`. It counts all quadruples with
an even number of red triples, not only balanced ones, and proves a finite
inequality implying asymptotic monochromatic density at least `5 / 84`.
No multiplicity recurrence is assumed.
-/

namespace Combinatorics.DensityRoute

open Finset SmallRamsey
universe u
variable {α : Type u} [DecidableEq α]

/-- Quadruple indicator for an even red-triple count. -/
def evenQuad (c : Finset α → Bool) (Q : Finset α) : ℕ :=
  if total Q 3 (colorWeight c true) % 2 = 0 then 1 else 0

/-- The two extreme red-triple counts, i.e. a monochromatic quadruple. -/
def monoFour (c : Finset α → Bool) (Q : Finset α) : ℕ :=
  if total Q 3 (colorWeight c true) = 0 ∨ total Q 3 (colorWeight c true) = 4 then 1 else 0

omit [DecidableEq α] in
lemma evenQuad_le_one (c : Finset α → Bool) (Q : Finset α) : evenQuad c Q ≤ 1 := by
  unfold evenQuad
  split_ifs <;> omega

omit [DecidableEq α] in
lemma red_count_le_four (c : Finset α → Bool) (Q : Finset α) (hQ : Q.card = 4) :
    total Q 3 (colorWeight c true) ≤ 4 := by
  have h := total_colors_add c Q 3
  norm_num [hQ] at h
  omega

omit [DecidableEq α] in
lemma evenQuad_eq (c : Finset α → Bool) (Q : Finset α) (hQ : Q.card = 4) :
    evenQuad c Q = monoFour c Q + balanced c Q := by
  have h := red_count_le_four c Q hQ
  have hc : total Q 3 (colorWeight c true) = 0 ∨
      total Q 3 (colorWeight c true) = 1 ∨
      total Q 3 (colorWeight c true) = 2 ∨
      total Q 3 (colorWeight c true) = 3 ∨
      total Q 3 (colorWeight c true) = 4 := by omega
  rcases hc with h | h | h | h | h <;> simp [evenQuad, monoFour, balanced, h]

omit [DecidableEq α] in
lemma monoFour_eq_one_iff (c : Finset α → Bool) (Q : Finset α) (hQ : Q.card = 4) :
    monoFour c Q = 1 ↔ ∃ color : Bool, ∀ e ∈ Q.powersetCard 3, c e = color := by
  classical
  have hcard : (Q.powersetCard 3).card = 4 := by simp [hQ]
  have hcount := total_color_eq_card c true Q 3
  rw [monoFour]
  split_ifs with h
  · constructor
    · intro _
      rcases h with hz | hf
      · refine ⟨false, ?_⟩
        intro e he
        have hempty : (Q.powersetCard 3).filter (fun e => c e = true) = ∅ := by
          apply card_eq_zero.mp
          rwa [← hcount]
        cases hc : c e with
        | false => rfl
        | true =>
          have hm : e ∈ (Q.powersetCard 3).filter (fun e => c e = true) :=
            mem_filter.mpr ⟨he, hc⟩
          rw [hempty] at hm
          simp at hm
      · refine ⟨true, ?_⟩
        have heq : (Q.powersetCard 3).filter (fun e => c e = true) = Q.powersetCard 3 :=
          eq_of_subset_of_card_le (filter_subset _ _) (by rw [hcard, ← hcount, hf])
        intro e he
        have hm : e ∈ (Q.powersetCard 3).filter (fun e => c e = true) := by
          rw [heq]
          exact he
        exact (mem_filter.mp hm).2
    · intro _
      rfl
  · constructor
    · norm_num
    · rintro ⟨color, hc⟩
      have hz : total Q 3 (colorWeight c true) = 0 ∨
          total Q 3 (colorWeight c true) = 4 := by
        cases color with
        | false =>
          left
          apply sum_eq_zero
          intro e he
          simp [colorWeight, hc e he]
        | true =>
          right
          have ht : total Q 3 (colorWeight c true) = ∑ e ∈ Q.powersetCard 3, 1 := by
            apply sum_congr rfl
            intro e he
            simp [colorWeight, hc e he]
          simpa [hQ] using ht
      exact (h hz).elim

/-- On every five-set, an odd number of quadruples have even red count. -/
lemma evenQuad_odd_five (c : Finset α → Bool) (V : Finset α) (hV : V.card = 5) :
    Odd (total V 4 (evenQuad c)) := by
  have hcounts := sum_totals_subsets V 4 3 (colorWeight c true) (by decide)
  norm_num [hV] at hcounts
  have hpoint : ∀ Q ∈ V.powersetCard 4,
      total Q 3 (colorWeight c true) + evenQuad c Q =
        1 + 2 * (total Q 3 (colorWeight c true) / 2) := by
    intro Q _
    unfold evenQuad
    split_ifs <;> omega
  have hsum : (∑ Q ∈ V.powersetCard 4, total Q 3 (colorWeight c true)) +
      total V 4 (evenQuad c) =
      5 + 2 * ∑ Q ∈ V.powersetCard 4, total Q 3 (colorWeight c true) / 2 := by
    calc
      _ = ∑ Q ∈ V.powersetCard 4,
          (total Q 3 (colorWeight c true) + evenQuad c Q) := by
        simp only [total, sum_add_distrib]
      _ = ∑ Q ∈ V.powersetCard 4,
          (1 + 2 * (total Q 3 (colorWeight c true) / 2)) := sum_congr rfl hpoint
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul,
          mul_one, card_powersetCard, hV]
        norm_num
  refine ⟨total V 4 (evenQuad c) / 2, ?_⟩
  omega

/-- The odd-cover theorem now applies with no no-monochromatic-set hypothesis. -/
theorem evenQuad_nine (c : Finset α → Bool) (V : Finset α) (hV : V.card = 9) :
    30 ≤ total V 4 (evenQuad c) := by
  let b : Finset α → ℕ := fun S => evenQuad c (V \ S)
  have hb : ∀ S ∈ V.powersetCard 5, b S ≤ 1 := by
    intro S _
    exact evenQuad_le_one c (V \ S)
  have ho : ∀ T ∈ V.powersetCard 4, Odd (degree V 5 b T) := by
    intro T hT
    obtain ⟨hTV, hT4⟩ := mem_powersetCard.mp hT
    have hcomp : (V \ T).card = 5 := by
      rw [card_sdiff_of_subset hTV, hV, hT4]
    have hodd := evenQuad_odd_five c (V \ T) hcomp
    have hdeg := degree_complement V T 5 (evenQuad c) hTV (by omega)
    change Odd (degree V 5 (fun S => evenQuad c (V \ S)) T)
    rw [hdeg]
    simpa only [hV, Nat.reduceSub] using hodd
  have h := odd_cover_nine V hV b hb ho
  have hcomp := degree_complement V ∅ 5 (evenQuad c) (empty_subset _) (by omega)
  have heq : total V 5 b = total V 4 (evenQuad c) := by
    simpa only [degree_empty, sdiff_empty, hV, Nat.reduceSub] using hcomp
  rwa [heq] at h

/-- Averaging the nine-point bound gives even-quadruple density at least `5/21`. -/
theorem evenQuad_density_bound (c : Finset α → Bool) (V : Finset α) (hV : 9 ≤ V.card) :
    5 * V.card.choose 4 ≤ 21 * total V 4 (evenQuad c) := by
  have hsum : (∑ A ∈ V.powersetCard 9, 30) ≤
      ∑ A ∈ V.powersetCard 9, total A 4 (evenQuad c) := by
    apply sum_le_sum
    intro A hA
    exact evenQuad_nine c A (mem_powersetCard.mp hA).2
  rw [sum_totals_subsets V 9 4 (evenQuad c) (by decide)] at hsum
  simp only [sum_const, smul_eq_mul, card_powersetCard] at hsum
  have hid := Nat.choose_mul (n := V.card) (by decide : 4 ≤ 9)
  norm_num [Nat.choose] at hid
  have hpos : 0 < (V.card - 4).choose 5 := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_left (c := (V.card - 4).choose 5) _ hpos
  nlinarith

omit [DecidableEq α] in
lemma mixed_quad_value (c : Finset α → Bool) (Q : Finset α) (hQ : Q.card = 4) :
    total Q 3 (colorWeight c true) * total Q 3 (colorWeight c false) +
        3 * monoFour c Q = 3 + balanced c Q := by
  have hcount := total_colors_add c Q 3
  norm_num [hQ] at hcount
  have hc : total Q 3 (colorWeight c true) = 0 ∨
      total Q 3 (colorWeight c true) = 1 ∨
      total Q 3 (colorWeight c true) = 2 ∨
      total Q 3 (colorWeight c true) = 3 ∨
      total Q 3 (colorWeight c true) = 4 := by omega
  rcases hc with h | h | h | h | h <;>
    simp only [monoFour, balanced, h] <;> norm_num <;> omega

/-- Unconditional mixed-triple counting, keeping the mono contribution. -/
lemma mixed_total_identity (c : Finset α → Bool) (V : Finset α) :
    (∑ P ∈ V.powersetCard 2,
      degree V 3 (colorWeight c true) P * degree V 3 (colorWeight c false) P) +
      3 * total V 4 (monoFour c) = 3 * V.card.choose 4 + total V 4 (balanced c) := by
  rw [mixed_triple_count V (colorWeight c true) (colorWeight c false)
    (fun e _ => colorWeight_mul c e)]
  calc
    _ = ∑ Q ∈ V.powersetCard 4,
        (total Q 3 (colorWeight c true) * total Q 3 (colorWeight c false) +
          3 * monoFour c Q) := by
      simp only [total, sum_add_distrib, ← mul_sum]
    _ = ∑ Q ∈ V.powersetCard 4, (3 + balanced c Q) := by
      apply sum_congr rfl
      intro Q hQ
      exact mixed_quad_value c Q (mem_powersetCard.mp hQ).2
    _ = _ := by
      simp only [total, sum_add_distrib, sum_const, smul_eq_mul, card_powersetCard]
      ring

lemma four_mul_product_le_square (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := by
  have h : (4 : ℤ) * ((a : ℤ) * (b : ℤ)) ≤ ((a : ℤ) + (b : ℤ)) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
  exact_mod_cast h

lemma mixed_total_upper (c : Finset α → Bool) (V : Finset α) :
    4 * (∑ P ∈ V.powersetCard 2,
      degree V 3 (colorWeight c true) P * degree V 3 (colorWeight c false) P) ≤
      V.card.choose 2 * (V.card - 2) ^ 2 := by
  calc
    _ = ∑ P ∈ V.powersetCard 2,
        4 * (degree V 3 (colorWeight c true) P * degree V 3 (colorWeight c false) P) :=
      mul_sum _ _ _
    _ ≤ ∑ P ∈ V.powersetCard 2, (V.card - 2) ^ 2 := by
      apply sum_le_sum
      intro P hP
      obtain ⟨hPV, hP2⟩ := mem_powersetCard.mp hP
      have h := four_mul_product_le_square (degree V 3 (colorWeight c true) P)
        (degree V 3 (colorWeight c false) P)
      have hs := degree_colors_add c V P hPV (by omega)
      simp only [hP2, Nat.reduceSub, Nat.choose_one_right] at hs
      rw [hs] at h
      exact h
    _ = _ := by simp

lemma choose_four_identity (N : ℕ) :
    12 * N.choose 4 = N.choose 2 * (N - 2) * (N - 3) := by
  have hc := Nat.choose_mul (n := N) (by decide : 2 ≤ 4)
  norm_num [Nat.choose] at hc
  have ht := Nat.descFactorial_eq_factorial_mul_choose (N - 2) 2
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero] at ht
  rw [show N - 2 - 1 = N - 3 by omega] at ht
  calc
    12 * N.choose 4 = 2 * (N.choose 4 * 6) := by ring
    _ = 2 * (N.choose 2 * (N - 2).choose 2) := by rw [hc]
    _ = N.choose 2 * (2 * (N - 2).choose 2) := by ring
    _ = N.choose 2 * ((N - 3) * (N - 2)) := by rw [← ht]
    _ = _ := by ring

/-- Balanced density is at most three times monochromatic density plus
`3/(N-3)`, with every denominator cleared. -/
theorem balanced_vs_mono (c : Finset α → Bool) (V : Finset α) :
    (V.card - 3) * total V 4 (balanced c) ≤
      3 * (V.card - 3) * total V 4 (monoFour c) + 3 * V.card.choose 4 := by
  have hid := mixed_total_identity c V
  have hup := mixed_total_upper c V
  have hchoose := choose_four_identity V.card
  have hscaled := Nat.mul_le_mul_left (V.card - 3) hup
  have hnext : (V.card - 3) * (V.card.choose 2 * (V.card - 2) ^ 2) =
      12 * (V.card - 2) * V.card.choose 4 := by
    calc
      _ = (V.card - 2) * (V.card.choose 2 * (V.card - 2) * (V.card - 3)) := by ring
      _ = (V.card - 2) * (12 * V.card.choose 4) := by rw [← hchoose]
      _ = _ := by ring
  rw [hnext] at hscaled
  by_cases hV : 3 ≤ V.card
  · have hn : V.card - 2 = (V.card - 3) + 1 := by omega
    rw [hn] at hscaled
    nlinarith [congrArg (fun x => (V.card - 3) * x) hid]
  · have hz : V.card - 3 = 0 := by omega
    simp [hz]

/-- A finite, unconditional seed bound for monochromatic quadruple density.
After division and taking the large-vertex limit this is `c₄ ≥ 5/84`. -/
theorem monochromatic_four_finite_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 9 ≤ V.card) :
    5 * (V.card - 3) * V.card.choose 4 ≤
      84 * (V.card - 3) * total V 4 (monoFour c) + 63 * V.card.choose 4 := by
  have heven := evenQuad_density_bound c V hV
  have heq : total V 4 (evenQuad c) = total V 4 (monoFour c) + total V 4 (balanced c) := by
    calc
      _ = ∑ Q ∈ V.powersetCard 4, (monoFour c Q + balanced c Q) := by
        apply sum_congr rfl
        intro Q hQ
        exact evenQuad_eq c Q (mem_powersetCard.mp hQ).2
      _ = _ := by simp only [total, sum_add_distrib]
  rw [heq] at heven
  have hscaled := Nat.mul_le_mul_left (V.card - 3) heven
  have hbalanced := balanced_vs_mono c V
  nlinarith

/-- The normalized finite bound, including its explicit error term. -/
theorem monochromatic_four_density_bound (c : Finset α → Bool) (V : Finset α)
    (hV : 9 ≤ V.card) :
    (5 : ℝ) / 84 - 3 / (4 * (V.card - 3 : ℕ)) ≤
      (total V 4 (monoFour c) : ℝ) / (V.card.choose 4 : ℝ) := by
  have h := monochromatic_four_finite_bound c V hV
  have hr : (5 : ℝ) * (V.card - 3 : ℕ) * (V.card.choose 4 : ℝ) ≤
      84 * (V.card - 3 : ℕ) * (total V 4 (monoFour c) : ℝ) +
        63 * (V.card.choose 4 : ℝ) := by exact_mod_cast h
  have ht : (0 : ℝ) < (V.card - 3 : ℕ) := by exact_mod_cast (show 0 < V.card - 3 by omega)
  have hQ : (0 : ℝ) < (V.card.choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 4 ≤ V.card by omega)
  apply (le_div_iff₀ hQ).2
  have heq : ((5 : ℝ) / 84 - 3 / (4 * (V.card - 3 : ℕ))) * (V.card.choose 4 : ℝ) =
      (5 * (V.card - 3 : ℕ) * (V.card.choose 4 : ℝ) - 63 * (V.card.choose 4 : ℝ)) /
        (84 * (V.card - 3 : ℕ)) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ (show (0 : ℝ) < 84 * (V.card - 3 : ℕ) by positivity)).2
  nlinarith

end Combinatorics.DensityRoute
