import FormalConjecturesUtil
import Submission.ThetaSubquadraticCounterexample

/-! Every fixed subquadratic error is insufficient for a universal heavy-pair
bound, even with a unit column-degree cap and arbitrarily large uniform row
degree. This does not settle the light-pair-weighted estimate or Erdos 713. -/
namespace Erdos713ThetaAllSubquadraticObstruction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars Erdos713ThetaC4Deletion
open Erdos713ThetaGramSubquadraticSize
open Erdos713ThetaCappedUniformCounterexample (edges_of_rows)
set_option maxHeartbeats 2000000

lemma exists_exponent (β : ℝ) (hβ : β < 2) :
    ∃ s : ℕ, β*(den s : ℝ) ≤ (num s : ℝ) := by
  obtain ⟨s,hs⟩ := exists_nat_gt (1/(2-β))
  have hh := (div_lt_iff₀ (sub_pos.mpr hβ)).mp hs
  refine ⟨s,?_⟩
  simp only [den,num,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hh,hβ]

lemma rpow_le_of_shape (s k m : ℕ) (β : ℝ) (hk : 1 ≤ k)
    (hβ : β*(den s : ℝ) ≤ (num s : ℝ))
    (hshape : k^(num s) ≤ 4^(num s)*m^(den s)) :
    (k : ℝ)^β ≤ 16*(m : ℝ) := by
  have hFour : (4 : ℕ)^(num s) ≤ 16^(den s) := by
    calc
      _ ≤ 4^(2*den s) := Nat.pow_le_pow_right (by decide) (by unfold num den; omega)
      _ = _ := by rw [pow_mul]; rfl
  have hnat : k^(num s) ≤ (16*m)^(den s) := by
    rw [mul_pow]
    exact hshape.trans (Nat.mul_le_mul_right _ hFour)
  apply le_of_pow_le_pow_left₀ (by unfold den; omega : den s ≠ 0) (by positivity)
  calc
    ((k : ℝ)^β)^(den s) = (k : ℝ)^(β*(den s : ℝ)) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg k)]
    _ ≤ (k : ℝ)^(num s : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) hβ
    _ = (k : ℝ)^(num s) := Real.rpow_natCast _ _
    _ ≤ (16*(m : ℝ))^(den s) := by exact_mod_cast hnat

/-- The counterexamples preserve every original row and its degree. The
unit cap uses isolated-column padding; no minimum column degree is asserted. -/
theorem exists_counterexample (β C : ℝ) (hβ : β < 2) (hC : 0 < C) (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ N ≤ r ∧ 1 ≤ r ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      (Nat.card B : ℝ)^β ≤ 16*(Nat.card A : ℝ) ∧
      C*((edges R : ℝ)+(Nat.card B : ℝ)^β) < (heavyCount R : ℝ) := by
  obtain ⟨s,hs⟩ := exists_exponent β hβ
  obtain ⟨M,hM⟩ := exists_nat_gt (17*C)
  obtain ⟨A,B,iA,iB,R,r,hf,hm,hrN,hr,hrows,hcap,hshape,hbig⟩ :=
    Erdos713ThetaSubquadraticCounterexample.exists_unit_cap s M N
  have hk := Erdos713ThetaCappedGramPreparation.columns_pos_of_row_degree R hm r hr hrows
  have hpower := rpow_le_of_shape s (Nat.card B) (Nat.card A) β hk hs hshape
  have hE : Nat.card A ≤ edges R := by
    rw [edges_of_rows R r hrows]
    exact Nat.le_mul_of_pos_right _ hr
  have hER : (0 : ℝ) < edges R := Nat.cast_pos.mpr (hm.trans_le hE)
  have hmER : (Nat.card A : ℝ) ≤ edges R := by exact_mod_cast hE
  have hlo : (M : ℝ)*(edges R : ℝ) < heavyCount R := by exact_mod_cast hbig
  have hscaled := mul_lt_mul_of_pos_right hM hER
  refine ⟨A,B,iA,iB,R,r,hf,hm,hrN,hr,hrows,hcap,hpower,?_⟩
  have hp : (Nat.card B : ℝ)^β ≤ 16*(edges R : ℝ) := by linarith only [hpower,hmER]
  have hh := mul_le_mul_of_nonneg_left hp hC.le
  nlinarith only [hh,hscaled,hlo]

/-- Adding any fixed subquadratic column error does not salvage the
heavy-count/incidence bound, even under the unit column cap. -/
theorem no_capped_incidence_bound (β : ℝ) (hβ : β < 2) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (heavyCount R : ℝ) ≤ C*((edges R : ℝ)+(Nat.card B : ℝ)^β) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨A,B,iA,iB,R,_r,hf,_hm,_hrN,_hr,_hrows,hcap,_hpower,hbig⟩ :=
    exists_counterexample β C hβ hC 1
  exact (not_le_of_gt hbig) (hBound A B R hf hcap)

/-- In particular the corresponding row-count bound is false. -/
theorem no_capped_row_bound (β : ℝ) (hβ : β < 2) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (heavyCount R : ℝ) ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)^β) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨A,B,iA,iB,R,r,hf,_hm,_hrN,hr,hrows,hcap,_hpower,hbig⟩ :=
    exists_counterexample β C hβ hC 1
  have hE : Nat.card A ≤ edges R := by
    rw [edges_of_rows R r hrows]
    exact Nat.le_mul_of_pos_right _ hr
  have hER : (Nat.card A : ℝ) ≤ edges R := by exact_mod_cast hE
  have hu := hBound A B R hf hcap
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add_right hER ((Nat.card B : ℝ)^β)) hC.le
  exact (not_le_of_gt hbig) (hu.trans (by simpa only [add_comm] using hh))

#print axioms exists_counterexample
#print axioms no_capped_incidence_bound
#print axioms no_capped_row_bound
end Erdos713ThetaAllSubquadraticObstruction
