import Submission.UnbalancedBounds

/-!
Constant-loss degree capping at the fourth-case Zarankiewicz scale. These are
necessary reductions for a hypothetical construction, not its existence and
not a solution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714Regularization
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

def edges (S : A → Finset B) : ℕ := ∑ a, (S a).card

def tail (S : A → Finset B) (D : ℕ) : ℕ :=
  ∑ a, if D < (S a).card then (S a).card else 0

lemma fourth_moment (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ a, (S a).card^4) ≤ 24*Fintype.card B^4+648*Fintype.card A := by
  have ht : (∑ a, ((S a).card-3)^4) ≤ 3*Fintype.card B^4 := by
    calc
      _ ≤ ∑ a, (S a).card.descFactorial 4 := by
        apply sum_le_sum
        intro a _
        have h := Nat.pow_sub_le_descFactorial (S a).card 4
        exact h
      _ ≤ 3*(Fintype.card B).descFactorial 4 :=
        Erdos714Unbalanced.star_bound S (by decide) hfree
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  have hp (a : A) : (S a).card^4 ≤ 8*(((S a).card-3)^4+81) := by
    calc
      _ ≤ (((S a).card-3)+3)^4 := Nat.pow_le_pow_left (by omega) 4
      _ ≤ _ := by simpa using add_pow_le (Nat.zero_le ((S a).card-3)) (Nat.zero_le 3) 4
  calc
    _ ≤ ∑ a, 8*(((S a).card-3)^4+81) := sum_le_sum (fun a _ => hp a)
    _ = 8*((∑ a, ((S a).card-3)^4)+81*Fintype.card A) := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
      ring
    _ ≤ 8*(3*Fintype.card B^4+81*Fintype.card A) := by gcongr
    _ = _ := by ring

omit [Fintype B] in
lemma tail_moment (S : A → Finset B) (D : ℕ) :
    D^3*tail S D ≤ ∑ a, (S a).card^4 := by
  unfold tail
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  split_ifs with h
  · calc
      _ ≤ (S a).card^3*(S a).card := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h.le 3)
      _ = _ := by ring
  · simp

/-- No critical-scale packing can hide a fixed fraction of its edges at
arbitrarily large degrees. Both parts may have fewer than q^4 vertices. -/
theorem critical_tail (S : A → Finset B) (q C : ℕ) (hq : 0 < q) (hC : 0 < C)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    4*C*tail S (16*C*q^3) ≤ q^7 := by
  have hm : (∑ a, (S a).card^4) ≤ 672*q^16 := by
    have hpow : q^4 ≤ q^16 := pow_le_pow_right' hq (by decide)
    calc
      _ ≤ 24*Fintype.card B^4+648*Fintype.card A := fourth_moment S hfree
      _ ≤ 24*(q^4)^4+648*q^4 := by gcongr
      _ ≤ 672*q^16 := by nlinarith [show (q^4)^4 = q^16 by ring]
  have ht := (tail_moment S (16*C*q^3)).trans hm
  have hCpow : C ≤ C^3 := by
    simpa only [pow_one] using (pow_le_pow_right' hC (by decide : 1 ≤ 3))
  have hcoef : 2688*C ≤ 4096*C^3 := by omega
  have h : (16*C*q^3)^3*(4*C*tail S (16*C*q^3)) ≤ (16*C*q^3)^3*q^7 := by
    calc
      _ = (4*C)*((16*C*q^3)^3*tail S (16*C*q^3)) := by ring
      _ ≤ (4*C)*(672*q^16) := Nat.mul_le_mul_left _ ht
      _ = (2688*C)*q^16 := by ring
      _ ≤ (4096*C^3)*q^16 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-- Remove vertices of high ORIGINAL degree on both sides, retaining their
indices as isolated vertices. -/
def cap (S : A → Finset B) (D : ℕ) (a : A) : Finset B :=
  if (S a).card ≤ D then (S a).filter (fun b => (dual S b).card ≤ D) else ∅

omit [Fintype B] in
lemma cap_subset (S : A → Finset B) (D : ℕ) (a : A) : cap S D a ⊆ S a := by
  unfold cap
  split_ifs
  · exact filter_subset _ _
  · exact empty_subset _

omit [Fintype B] in
lemma cap_row_bound (S : A → Finset B) (D : ℕ) (a : A) : (cap S D a).card ≤ D := by
  unfold cap
  split_ifs with h
  · exact (card_filter_le _ _).trans h
  · simp

lemma cap_column_bound (S : A → Finset B) (D : ℕ) (b : B) : (dual (cap S D) b).card ≤ D := by
  by_cases hb : (dual S b).card ≤ D
  · apply (card_le_card (show dual (cap S D) b ⊆ dual S b from ?_)).trans hb
    intro a ha
    exact (mem_dual S a b).mpr (cap_subset S D a ((mem_dual _ a b).mp ha))
  · have he : dual (cap S D) b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h := (mem_dual _ a b).mp ha
      unfold cap at h
      split_ifs at h with hrow
      · exact hb (mem_filter.mp h).2
      · exact notMem_empty _ h
    simp [he]

/-- Reindexing a selected collection of incidences by its column endpoint. -/
lemma filter_columns_count (S : A → Finset B) (P : B → Prop) [DecidablePred P] :
    (∑ a, ((S a).filter P).card) = ∑ b, if P b then (dual S b).card else 0 := by
  have hc (a : A) : ((S a).filter P).card = ∑ b : B, if b ∈ S a ∧ P b then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext b
    simp
  simp_rw [hc]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  by_cases hb : P b <;> simp [hb, dual]

lemma cap_edge_loss (S : A → Finset B) (D : ℕ) :
    edges S ≤ edges (cap S D)+tail S D+tail (dual S) D := by
  have hr (a : A) : (S a).card ≤ (cap S D a).card+
      (if D < (S a).card then (S a).card else 0)+
      ((S a).filter (fun b => D < (dual S b).card)).card := by
    by_cases ha : (S a).card ≤ D
    · have hh := card_filter_add_card_filter_not (s := S a) (fun b => (dual S b).card ≤ D)
      simpa only [cap, if_pos ha, if_neg (by omega : ¬ D < (S a).card), add_zero,
        not_le] using hh.ge
    · simp [cap, ha, show D < (S a).card by omega]
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset A)) => hr a)
  rw [sum_add_distrib, sum_add_distrib] at h
  rw [filter_columns_count S (fun b => D < (dual S b).card)] at h
  exact h

omit [Fintype A] [Fintype B] in
lemma free_of_subset (S T : A → Finset B) (hT : ∀ a, T a ⊆ S a)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T) := by
  apply (free_iff_no_rectangle T (by decide)).mpr
  intro f g hfg
  exact (free_iff_no_rectangle S (by decide)).mp hfree f g (fun i j => hT _ (hfg i j))

lemma dual_free (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (dual S)) := by
  rw [free_iff_common_card _ (by decide)] at hfree ⊢
  exact (common_card_dual_iff S (by decide)).mp hfree

/-- Cap both maximum degrees while retaining at least half of a supplied
critical lower bound. No regularity of the original graph is assumed. -/
theorem critical_degree_cap (S : A → Finset B) (q C : ℕ) (hq : 0 < q) (hC : 0 < C)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*edges S) :
    ∃ T : A → Finset B, (∀ a, T a ⊆ S a) ∧
      (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T) ∧
      (∀ a, (T a).card ≤ 16*C*q^3) ∧ (∀ b, (dual T b).card ≤ 16*C*q^3) ∧
      q^7 ≤ 2*C*edges T := by
  refine ⟨cap S (16*C*q^3),cap_subset S _,free_of_subset S _ (cap_subset S _) hfree,
    cap_row_bound S _,cap_column_bound S _,?_⟩
  have hrow := critical_tail S q C hq hC hA hB hfree
  have hcol := critical_tail (dual S) q C hq hC hB hA (dual_free S hfree)
  have hloss := cap_edge_loss S (16*C*q^3)
  nlinarith

#print axioms fourth_moment
#print axioms critical_tail
#print axioms filter_columns_count
#print axioms cap_edge_loss
#print axioms critical_degree_cap
end Erdos714Regularization
