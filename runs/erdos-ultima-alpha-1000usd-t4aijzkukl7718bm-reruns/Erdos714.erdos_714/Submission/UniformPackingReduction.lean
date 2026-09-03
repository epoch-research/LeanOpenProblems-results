import Submission.BicliqueRegularization

/-!
Uniform nonempty row sizes can be imposed on a hypothetical fourth-case
construction at constant cost. This is a conditional positive reduction, not
an existence theorem and not a resolution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714Regularization
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Choose exactly d neighbors whenever there are at least d available. -/
def trim (S : A → Finset B) (d : ℕ) (a : A) : Finset B :=
  if h : d ≤ (S a).card then Classical.choose (exists_subset_card_eq h) else ∅

omit [Fintype A] [Fintype B] in
lemma trim_subset (S : A → Finset B) (d : ℕ) (a : A) : trim S d a ⊆ S a := by
  unfold trim
  split_ifs with h
  · exact (Classical.choose_spec (exists_subset_card_eq h)).1
  · exact empty_subset _

omit [Fintype A] [Fintype B] in
lemma trim_card (S : A → Finset B) (d : ℕ) (a : A) :
    (trim S d a).card = if d ≤ (S a).card then d else 0 := by
  unfold trim
  split_ifs with h
  · exact (Classical.choose_spec (exists_subset_card_eq h)).2
  · rfl

omit [Fintype B] in
/-- The loss estimate permits both empty and low-degree rows. -/
lemma trim_edge_bound (S : A → Finset B) (d D : ℕ) (hD : ∀ a, (S a).card ≤ D) :
    d*edges S ≤ D*edges (trim S d)+d^2*Fintype.card A := by
  have hrow (a : A) : d*(S a).card ≤ D*(trim S d a).card+d^2 := by
    rw [trim_card]
    by_cases ha : d ≤ (S a).card
    · rw [if_pos ha]
      have h := Nat.mul_le_mul_left d (hD a)
      nlinarith
    · rw [if_neg ha]
      have h := Nat.mul_le_mul_left d (show (S a).card ≤ d by omega)
      nlinarith
  unfold edges
  rw [mul_sum, mul_sum]
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset A)) => hrow a)
  simpa only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, mul_comm] using h

lemma dual_subset_of_subset (S T : A → Finset B) (hT : ∀ a, T a ⊆ S a) (b : B) :
    dual T b ⊆ dual S b := by
  intro a ha
  exact (mem_dual _ _ _).mpr (hT a ((mem_dual _ _ _).mp ha))

/-- Positive, nonempty row size and two useful bounds for the floor. -/
lemma trim_size_budget (q C : ℕ) (hC : 0 < C) (hq : 4*C ≤ q^3) :
    0 < q^3/(4*C) ∧ 4*C*(q^3/(4*C)) ≤ q^3 ∧ q^3 ≤ 8*C*(q^3/(4*C)) := by
  have hden : 0 < 4*C := by positivity
  have hd : 0 < q^3/(4*C) := Nat.div_pos hq hden
  have hlo : 4*C*(q^3/(4*C)) ≤ q^3 := Nat.mul_div_le _ _
  have hhi : q^3 < (q^3/(4*C)+1)*(4*C) :=
    (Nat.div_lt_iff_lt_mul hden).mp (by omega)
  have hc : 4*C ≤ 4*C*(q^3/(4*C)) := by nlinarith
  exact ⟨hd,hlo,by nlinarith⟩

/-- A hypothetical critical-scale packing may be assumed to have a common
nonzero row size, bounded column degrees, and a positive critical edge count.
All constants are independent of q. -/
theorem critical_uniform_trim (S : A → Finset B) (q C : ℕ) (hq : 0 < q) (hC : 0 < C)
    (hlarge : 4*C ≤ q^3) (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*edges S) :
    ∃ T : A → Finset B, (∀ a, T a ⊆ S a) ∧
      (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T) ∧
      (∀ a, (T a).card = 0 ∨ (T a).card = q^3/(4*C)) ∧
      (∀ b, (dual T b).card ≤ 16*C*q^3) ∧ q^7 ≤ 512*C^3*edges T := by
  obtain ⟨U,hUS,hUf,hUrow,hUcol,hUe⟩ := critical_degree_cap S q C hq hC hA hB hfree he
  let d := q^3/(4*C)
  let D := 16*C*q^3
  obtain ⟨hd,hdlo,hdhi⟩ := trim_size_budget q C hC hlarge
  have hTsub (a : A) : trim U d a ⊆ S a := (trim_subset U d a).trans (hUS a)
  refine ⟨trim U d,hTsub,free_of_subset U _ (trim_subset U d) hUf,?_,?_,?_⟩
  · intro a
    rw [trim_card]
    split_ifs <;> simp [d]
  · intro b
    exact (card_le_card (dual_subset_of_subset U _ (trim_subset U d) b)).trans (hUcol b)
  · have htrim := trim_edge_bound U d D hUrow
    have hsmall : 4*C*d^2*Fintype.card A ≤ q^7*d := by
      calc
        _ ≤ 4*C*d^2*q^4 := Nat.mul_le_mul_left _ hA
        _ = (4*C*d)*(d*q^4) := by ring
        _ ≤ q^3*(d*q^4) := Nat.mul_le_mul_right _ hdlo
        _ = _ := by ring
    have hretained : q^7*d ≤ 4*C*D*edges (trim U d) := by
      have h₁ := Nat.mul_le_mul_right d hUe
      have h₂ := Nat.mul_le_mul_left (2*C) htrim
      nlinarith
    have hh : q^3*q^7 ≤ q^3*(512*C^3*edges (trim U d)) := by
      calc
        _ ≤ (8*C*d)*q^7 := Nat.mul_le_mul_right _ hdhi
        _ = (8*C)*(q^7*d) := by ring
        _ ≤ (8*C)*(4*C*D*edges (trim U d)) := Nat.mul_le_mul_left _ hretained
        _ = _ := by dsimp [D]; ring
    exact Nat.le_of_mul_le_mul_left hh (pow_pos hq 3)

omit [Fintype B] in
/-- Uniform nonempty row sizes convert edge count directly into active-row count. -/
lemma uniform_edges (T : A → Finset B) (d : ℕ) (hd : 0 < d)
    (hT : ∀ a, (T a).card = 0 ∨ (T a).card = d) :
    edges T = d*(univ.filter (fun a => 0 < (T a).card)).card := by
  have hcard (a : A) : (T a).card = if 0 < (T a).card then d else 0 := by
    rcases hT a with h | h <;> simp [h,hd]
  unfold edges
  calc
    ∑ a, (T a).card = ∑ a, if 0 < (T a).card then d else 0 :=
      sum_congr rfl (fun a _ => hcard a)
    _ = _ := by
      rw [← sum_filter]
      simp [mul_comm]

omit [Fintype B] in
/-- A positive fraction of the original row budget remains active, not merely
one unusually large block. -/
theorem active_rows_bound (T : A → Finset B) (q C : ℕ) (hq : 0 < q) (hC : 0 < C)
    (hlarge : 4*C ≤ q^3)
    (hT : ∀ a, (T a).card = 0 ∨ (T a).card = q^3/(4*C))
    (he : q^7 ≤ 512*C^3*edges T) :
    q^4 ≤ 128*C^2*(univ.filter (fun a => 0 < (T a).card)).card := by
  obtain ⟨hd,hdlo,_⟩ := trim_size_budget q C hC hlarge
  rw [uniform_edges T _ hd hT] at he
  have h : q^3*q^4 ≤ q^3*(128*C^2*(univ.filter (fun a => 0 < (T a).card)).card) := by
    calc
      _ = q^7 := by ring
      _ ≤ 512*C^3*((q^3/(4*C))*(univ.filter (fun a => 0 < (T a).card)).card) := he
      _ = (128*C^2*(univ.filter (fun a => 0 < (T a).card)).card)*(4*C*(q^3/(4*C))) := by ring
      _ ≤ (128*C^2*(univ.filter (fun a => 0 < (T a).card)).card)*q^3 := Nat.mul_le_mul_left _ hdlo
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos hq 3)

#print axioms trim_subset
#print axioms trim_card
#print axioms trim_edge_bound
#print axioms trim_size_budget
#print axioms critical_uniform_trim
#print axioms uniform_edges
#print axioms active_rows_bound
end Erdos714Regularization
