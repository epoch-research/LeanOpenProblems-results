import FormalConjecturesUtil
import Submission.FiniteOccupancy
import Submission.ThetaColumnSplitting
import Submission.ThetaHeavySparsifier

/-! Random column splitting and heavy pairs. This concerns an auxiliary
sparsifier target, not the original extremal-exponent conjecture. -/
open Finset
open scoped BigOperators Classical
namespace Erdos713ThetaRandomSplitting
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713GlobalLight
open Erdos713ThetaC4Deletion Erdos713ThetaAffineStars Erdos713FiniteOccupancy
variable {A B T : Type*}
set_option maxHeartbeats 2000000

def split (R : A → B → Prop) (s : A → B → T) (a : A) (b : B × T) : Prop :=
  R a b.1 ∧ s a b.1 = b.2

lemma no_theta {R : A → B → Prop} (hR : ¬ HasTheta R) (s : A → B → T) :
    ¬ HasTheta (split R s) := by
  apply mt (theta_of_projection Prod.fst (fun _ _ h => h.1) ?_) hR
  intro a b c hb hc he
  apply Prod.ext he
  exact hb.2.symm.trans ((congrArg (s a) he).trans hc.2)

lemma row_card (R : A → B → Prop) (s : A → B → T) (a : A) :
    Nat.card {b // split R s a b} = Nat.card {b // R a b} := by
  let e : {b // split R s a b} ≃ {b // R a b} :=
    { toFun := fun b => ⟨b.val.1,b.property.1⟩
      invFun := fun b => ⟨(b.val,s a b.val),b.property,rfl⟩
      left_inv := fun b => Subtype.ext (Prod.ext rfl b.property.2)
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

lemma edge_card [Fintype A] [Fintype B] [Fintype T]
    (R : A → B → Prop) (s : A → B → T) : edges (split R s) = edges R := by
  simp only [edges,edge_card_eq_rows,row_card]

lemma pair_indicator_mean [Fintype B] [DecidableEq B] [Fintype T] [Nonempty T]
    {x y : B} (hxy : x ≠ y) (i j : T) :
    (𝔼 (f : B → T), if f x = i ∧ f y = j then (1 : ℝ) else 0) =
      1/(Fintype.card T : ℝ)^2 := by
  have he (f : B → T) : (if f x = i ∧ f y = j then (1 : ℝ) else 0) =
      (if f x = i then (1 : ℝ) else 0)*(if f y = j then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [expect_eval_mul hxy (fun z => if z=i then (1 : ℝ) else 0)
    (fun z => if z=j then (1 : ℝ) else 0)]
  simp [pow_two]

lemma split_codegree_sum [Fintype A] (R : A → B → Prop) (s : A → B → T)
    (x y : B) (i j : T) :
    (codegree (split R s) (x,i) (y,j) : ℝ) =
      ∑ a ∈ (univ.filter (fun a => R a x ∧ R a y)),
        if s a x = i ∧ s a y = j then (1 : ℝ) else 0 := by
  simp only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype,split,
    sum_filter]
  rw [← sum_boole]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp_all

lemma pair_heavy_expect [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype T] [Nonempty T] (R : A → B → Prop) {x y : B} (hxy : x ≠ y)
    (hc : 8*(Fintype.card T)^2 ≤ codegree R x y) (i j : T) :
    (1/2 : ℝ) ≤ 𝔼 (s : A → B → T),
      if 3 ≤ codegree (split R s) (x,i) (y,j) then (1 : ℝ) else 0 := by
  let S : Finset A := univ.filter (fun a => R a x ∧ R a y)
  let g : (B → T) → ℝ := fun f => if f x = i ∧ f y = j then 1 else 0
  let p : ℝ := 1/(Fintype.card T : ℝ)^2
  let L : ℝ := (codegree R x y : ℝ)*p
  have hS : S.card = codegree R x y := by
    simp only [S,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hg : ∀ f, (g f)^2 = g f := by intro f; dsimp [g]; split_ifs <;> norm_num
  have hp : (𝔼 f : B → T, g f) = p := pair_indicator_mean hxy i j
  have hv := indicator_variance S g hg p hp
  rw [hS] at hv
  have he (s : A → B → T) : (codegree (split R s) (x,i) (y,j) : ℝ) =
      ∑ a ∈ S, g (s a) := split_codegree_sum R s x y i j
  simp_rw [← he] at hv
  have hcard : 0 < (Fintype.card T : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hp0
  have hv' : (𝔼 s : A → B → T,
      ((codegree (split R s) (x,i) (y,j) : ℝ)-L)^2) ≤ L := by
    change _ ≤ (codegree R x y : ℝ)*p
    rw [hv]
    change L*(1-p) ≤ L
    nlinarith
  have hL : 8 ≤ L := by
    have hcR : 8*(Fintype.card T : ℝ)^2 ≤ (codegree R x y : ℝ) := by exact_mod_cast hc
    dsimp [L,p]
    rw [mul_one_div,le_div_iff₀ (sq_pos_of_pos hcard)]
    exact hcR
  have hh := heavy_of_variance
    (fun s : A → B → T => (codegree (split R s) (x,i) (y,j) : ℝ)) L hL hv'
  convert hh using 1
  apply expect_congr rfl
  intro s _
  have hc : (3 : ℝ) ≤ (codegree (split R s) (x,i) (y,j) : ℝ) ↔
      3 ≤ codegree (split R s) (x,i) (y,j) := by exact_mod_cast Iff.rfl
  simp only [hc]

lemma heavy_sum [Fintype A] [Fintype B] [Fintype T]
    (R : A → B → Prop) (s : A → B → T) :
    (heavyCount (split R s) : ℝ) = ∑ p : B × B, ∑ u : T × T,
      if 3 ≤ codegree (split R s) (p.1,u.1) (p.2,u.2) then (1 : ℝ) else 0 := by
  let e : ((B × T) × (B × T)) ≃ ((B × B) × (T × T)) :=
    { toFun := fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))
      invFun := fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [heavyCount,Nat.card_eq_fintype_card,Fintype.card_subtype,← sum_boole]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma heavy_expect_lower [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype T] [Nonempty T] (R : A → B → Prop) (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*(Fintype.card T)^2 ≤ codegree R p.1 p.2) :
    (P.card : ℝ)*(Fintype.card T : ℝ)^2/2 ≤
      𝔼 (s : A → B → T), (heavyCount (split R s) : ℝ) := by
  simp_rw [heavy_sum,expect_sum_comm]
  calc
    _ = ∑ _p ∈ P, ∑ _u : T × T, (1/2 : ℝ) := by
      simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
      ring
    _ ≤ ∑ p ∈ P, ∑ u : T × T,
        𝔼 (s : A → B → T),
          if 3 ≤ codegree (split R s) (p.1,u.1) (p.2,u.2) then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro u _
      exact pair_heavy_expect R (hP p hp).1 (hP p hp).2 u.1 u.2
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ P)
      intro p _ _
      apply sum_nonneg
      intro u _
      exact expect_nonneg (fun s _ => by split_ifs <;> positivity)

/-- A universal heavy-count bound on all assignments bounds one codegree band. -/
lemma band_mass_le [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype T] [Nonempty T] (R : A → B → Prop) (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*(Fintype.card T)^2 ≤ codegree R p.1 p.2 ∧
      codegree R p.1 p.2 < 32*(Fintype.card T)^2)
    (M : ℕ) (hM : ∀ s : A → B → T, heavyCount (split R s) ≤ M) :
    (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*M := by
  have hlo := heavy_expect_lower (T := T) R P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)
  have hhi : (𝔼 (s : A → B → T), (heavyCount (split R s) : ℝ)) ≤ (M : ℝ) := by
    exact expect_le univ_nonempty (fun s _ => by exact_mod_cast hM s)
  have hw : (∑ p ∈ P, codegree R p.1 p.2) ≤ 32*(Fintype.card T)^2*P.card := by
    calc
      _ ≤ ∑ _p ∈ P, 32*(Fintype.card T)^2 := sum_le_sum (fun p hp => (hP p hp).2.2.le)
      _ = _ := by simp [Nat.mul_comm]
  have hwR : (∑ p ∈ P, (codegree R p.1 p.2 : ℝ)) ≤
      32*(Fintype.card T : ℝ)^2*P.card := by exact_mod_cast hw
  have hfin : (∑ p ∈ P, (codegree R p.1 p.2 : ℝ)) ≤ 64*(M : ℝ) := by
    nlinarith only [hwR,hlo,hhi]
  exact_mod_cast hfin

#print axioms no_theta
#print axioms edge_card
#print axioms pair_heavy_expect
#print axioms heavy_expect_lower
#print axioms band_mass_le
end Erdos713ThetaRandomSplitting
