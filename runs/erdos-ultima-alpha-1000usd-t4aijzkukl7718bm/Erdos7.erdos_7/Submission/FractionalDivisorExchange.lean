import FormalConjecturesUtil

/-! A downward exchange in a fractional resource assignment. This explains
why minimum-rank routing favors divisor closure; it is not a covering theorem. -/
namespace Erdos7FractionalDivisorExchange
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

section
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def cell (i : I) (a : A) (j : I) (b : A) : ℝ :=
  if j=i then if b=a then 1 else 0 else 0

def transfer (F : I → A → ℝ) (i : I) (a d : A) (δ : ℝ) (j : I) (b : A) : ℝ :=
  F j b + δ*cell i a j b - δ*cell i d j b

def Feasible (R : I → A → Prop) (b : I → ℝ) (F : I → A → ℝ) : Prop :=
  (∀ i a, 0 ≤ F i a) ∧ (∀ i a, ¬ R i a → F i a=0) ∧
    (∀ i, ∑ a, F i a=b i) ∧ ∀ a, (∑ i, F i a) ≤ 1

def cost (c : A → ℝ) (F : I → A → ℝ) : ℝ := ∑ i, ∑ a, c a*F i a

lemma row_cell (i j : I) (a : A) : (∑ b, cell i a j b) = if j=i then 1 else 0 := by
  by_cases hj : j=i <;> simp [cell,hj]

lemma col_cell (i : I) (a b : A) : (∑ j, cell i a j b) = if b=a then 1 else 0 := by
  by_cases hb : b=a <;> simp [cell,hb]

lemma weighted_cell (i : I) (a : A) (c : A → ℝ) :
    (∑ j, ∑ b, c b*cell i a j b)=c a := by
  simp [cell,mul_ite]

lemma transfer_row (F : I → A → ℝ) (i j : I) (a d : A) (δ : ℝ) :
    (∑ b, transfer F i a d δ j b)=∑ b, F j b := by
  simp only [transfer,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,row_cell]
  ring

lemma transfer_col (F : I → A → ℝ) (i : I) (a d b : A) (δ : ℝ) :
    (∑ j, transfer F i a d δ j b) = (∑ j, F j b) +
      δ*(if b=a then 1 else 0) - δ*(if b=d then 1 else 0) := by
  simp only [transfer,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,col_cell]

lemma transfer_cost (F : I → A → ℝ) (i : I) (a d : A) (δ : ℝ) (c : A → ℝ) :
    cost c (transfer F i a d δ)=cost c F+δ*(c a-c d) := by
  have he (j : I) (b : A) : c b*transfer F i a d δ j b =
      c b*F j b + δ*(c b*cell i a j b) - δ*(c b*cell i d j b) := by
    unfold transfer
    ring
  simp only [cost,he,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
    weighted_cell]
  ring

/-- Transfer mass from an occupied upper resource to unused lower capacity.
Row demands, support eligibility, nonnegativity, and unit column capacities
are all preserved. -/
theorem transfer_feasible (R : I → A → Prop) (b : I → ℝ) (F : I → A → ℝ)
    (hF : Feasible R b F) (i : I) (a d : A) (had : a ≠ d)
    (ha : R i a) (hd : R i d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδd : δ ≤ F i d) (hδa : δ ≤ 1-∑ j, F j a) :
    Feasible R b (transfer F i a d δ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j x
    by_cases hji : j=i
    · subst j
      by_cases hxa : x=a
      · subst x
        simpa [transfer,cell,had] using add_nonneg (hF.1 i a) hδ
      · by_cases hxd : x=d
        · subst x
          simpa [transfer,cell,had.symm] using sub_nonneg.mpr hδd
        · simpa [transfer,cell,hxa,hxd] using hF.1 i x
    · simpa [transfer,cell,hji] using hF.1 j x
  · intro j x hnot
    by_cases hji : j=i
    · subst j
      have hxa : x ≠ a := by rintro rfl; exact hnot ha
      have hxd : x ≠ d := by rintro rfl; exact hnot hd
      simpa [transfer,cell,hxa,hxd] using hF.2.1 i x hnot
    · simpa [transfer,cell,hji] using hF.2.1 j x hnot
  · intro j
    rw [transfer_row]
    exact hF.2.2.1 j
  · intro x
    rw [transfer_col]
    by_cases hxa : x=a
    · subst x
      have hh : (∑ j, F j a)+δ ≤ 1 := by linarith
      simpa [had] using hh
    · by_cases hxd : x=d
      · subst x
        have hh : (∑ j, F j d)-δ ≤ 1 := by linarith [hF.2.2.2 d]
        simpa [had.symm] using hh
      · simpa [hxa,hxd] using hF.2.2.2 x

/-- In a minimum-cost fractional matching with downward-closed eligibility,
any positive use of an upper resource forces every cheaper lower resource
to be completely occupied. Optimality is an explicit hypothesis. -/
theorem lower_saturated_of_upper_used
    (R : I → A → Prop) (b : I → ℝ) (F : I → A → ℝ) (hF : Feasible R b F)
    (Below : A → A → Prop) (c : A → ℝ)
    (hdown : ∀ i a d, Below a d → R i d → R i a)
    (hcost : ∀ a d, Below a d → c a < c d)
    (hmin : ∀ G, Feasible R b G → cost c F ≤ cost c G)
    (a d : A) (had : Below a d) (hd : 0 < ∑ i, F i d) :
    (∑ i, F i a)=1 := by
  by_contra hne
  have hlt : (∑ i, F i a)<1 := lt_of_le_of_ne (hF.2.2.2 a) hne
  have hex : ∃ i, 0 < F i d := by
    by_contra! hh
    have hsum : (∑ i, F i d) ≤ 0 := Finset.sum_nonpos (fun i _ => hh i)
    linarith
  obtain ⟨i,hi⟩ := hex
  have hid : R i d := by
    by_contra h
    have hh := hF.2.1 i d h
    linarith
  have hia := hdown i a d had hid
  have hcad := hcost a d had
  have hane : a ≠ d := by rintro rfl; exact (lt_irrefl _ hcad)
  let δ := min (F i d) (1-∑ j, F j a)
  have hδ : 0 < δ := lt_min hi (sub_pos.mpr hlt)
  have hnew := transfer_feasible R b F hF i a d hane hia hid δ hδ.le
    (min_le_left _ _) (min_le_right _ _)
  have hh := hmin (transfer F i a d δ) hnew
  rw [transfer_cost] at hh
  have hneg : δ*(c a-c d)<0 := mul_neg_of_pos_of_neg hδ (sub_neg.mpr hcad)
  linarith
end

#print axioms transfer_feasible
#print axioms lower_saturated_of_upper_used
end Erdos7FractionalDivisorExchange
