import FormalConjecturesUtil

/-!
A finite upper sieve with independently thinned local obstructions. This is
an abstract counting inequality, not a construction of cube-Sidon roots.
-/
namespace Erdos1206.FiniteThinnedSieve
open Finset
open scoped Classical
variable {ι : Type*} [DecidableEq ι]

noncomputable def weight (P : Finset ι) (q : ι → ℝ) (J : Finset ι) : ℝ :=
  (∏ p ∈ J, q p) * ∏ p ∈ P \ J, (1-q p)

lemma weight_nonneg (P : Finset ι) (q : ι → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) {J : Finset ι} (hJ : J ⊆ P) :
    0 ≤ weight P q J := by
  apply mul_nonneg
  · exact prod_nonneg (fun p hp => (hq p (hJ hp)).1)
  · exact prod_nonneg (fun p hp => sub_nonneg.mpr (hq p (mem_sdiff.mp hp).1).2)

lemma sum_weight (P : Finset ι) (q : ι → ℝ) :
    ∑ J ∈ P.powerset, weight P q J = 1 := by
  simp only [weight, ← prod_add]
  simp

lemma sum_weight_supersets (P S : Finset ι) (q : ι → ℝ) (hS : S ⊆ P) :
    (∑ J ∈ P.powerset, if S ⊆ J then weight P q J else 0) = ∏ p ∈ S, q p := by
  let g : ι → ℝ := fun p => if p ∈ S then 0 else 1-q p
  have hprod : (∏ p ∈ P, (q p+g p)) = ∏ p ∈ S, q p := by
    calc
      _ = ∏ p ∈ S, (q p+g p) := (prod_subset hS (fun p _ hp => by simp [g,hp])).symm
      _ = _ := prod_congr rfl (fun p hp => by simp [g,hp])
  rw [prod_add] at hprod
  rw [← hprod]
  apply sum_congr rfl
  intro J hJ
  by_cases hSJ : S ⊆ J
  · rw [if_pos hSJ]
    dsimp only [weight]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hpS : p ∉ S := fun hh => (mem_sdiff.mp hp).2 (hSJ hh)
    simp [g,hpS]
  · rw [if_neg hSJ]
    obtain ⟨p,hpS,hpJ⟩ := not_subset.mp hSJ
    have hz : (∏ p ∈ P \ J, g p)=0 := prod_eq_zero (mem_sdiff.mpr ⟨hS hpS,hpJ⟩) (by simp [g,hpS])
    rw [hz,mul_zero]

lemma sum_weight_disjoint (P S : Finset ι) (q : ι → ℝ) (hS : S ⊆ P) :
    (∑ J ∈ P.powerset, if Disjoint S J then weight P q J else 0) =
      ∏ p ∈ S, (1-q p) := by
  let f : ι → ℝ := fun p => if p ∈ S then 0 else q p
  have hprod : (∏ p ∈ P, (f p+(1-q p))) = ∏ p ∈ S, (1-q p) := by
    calc
      _ = ∏ p ∈ S, (f p+(1-q p)) := (prod_subset hS (fun p _ hp => by simp [f,hp])).symm
      _ = _ := prod_congr rfl (fun p hp => by simp [f,hp])
  rw [prod_add] at hprod
  rw [← hprod]
  apply sum_congr rfl
  intro J hJ
  by_cases hSJ : Disjoint S J
  · rw [if_pos hSJ]
    dsimp only [weight]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hpS : p ∉ S := fun hh => disjoint_left.mp hSJ hh hp
    simp [f,hpS]
  · rw [if_neg hSJ]
    obtain ⟨p,hpS,hpJ⟩ := not_disjoint_iff.mp hSJ
    have hz : (∏ p ∈ J, f p)=0 := prod_eq_zero hpJ (by simp [f,hpS])
    rw [hz,zero_mul]

/-- A divisor polynomial, with subsets in place of squarefree divisors. -/
noncomputable def poly (P : Finset ι) (lam : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  ∑ S ∈ P.powerset, if S ⊆ G then lam S else 0

lemma poly_empty (P : Finset ι) (lam : Finset ι → ℝ) : poly P lam ∅=lam ∅ := by
  simp [poly]

lemma poly_sq (P : Finset ι) (lam : Finset ι → ℝ) (G : Finset ι) :
    (poly P lam G)^2 = ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      if S ∪ T ⊆ G then lam S*lam T else 0 := by
  rw [pow_two,poly,sum_mul_sum]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro T hT
  simp only [union_subset_iff]
  split_ifs <;> simp_all

lemma thinned_square (P G : Finset ι) (q : ι → ℝ) (lam : Finset ι → ℝ) :
    (∑ J ∈ P.powerset, weight P q J*(poly P lam (G ∩ J))^2) =
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        if S ∪ T ⊆ G then lam S*lam T*(∏ p ∈ S ∪ T, q p) else 0 := by
  simp_rw [poly_sq,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  have hST : S ∪ T ⊆ P := union_subset (mem_powerset.mp hS) (mem_powerset.mp hT)
  have he : (∑ J ∈ P.powerset,
      weight P q J*(if S ∪ T ⊆ G ∩ J then lam S*lam T else 0)) =
      (if S ∪ T ⊆ G then (lam S*lam T)*
        (∑ J ∈ P.powerset, if S ∪ T ⊆ J then weight P q J else 0) else 0) := by
    by_cases hh : S ∪ T ⊆ G
    · rw [if_pos hh,mul_sum]
      apply sum_congr rfl
      intro J hJ
      simp only [subset_inter_iff,hh,true_and]
      split_ifs <;> ring
    · rw [if_neg hh]
      apply sum_eq_zero
      intro J hJ
      have hnot : ¬ S ∪ T ⊆ G ∩ J := fun h => hh (h.trans inter_subset_left)
      simp [hnot]
  rw [he,sum_weight_supersets P (S ∪ T) q hST]

/-- Thinning converts an upper sieve into an exponential bound on the
number of local obstructions. No independence in the arithmetic sample is
assumed; independence is only in the auxiliary thinning experiment. -/
theorem product_avoidance_le (P G : Finset ι) (q : ι → ℝ) (lam : Finset ι → ℝ)
    (hG : G ⊆ P) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (hlam : lam ∅=1) :
    (∏ p ∈ G, (1-q p)) ≤
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        if S ∪ T ⊆ G then lam S*lam T*(∏ p ∈ S ∪ T, q p) else 0 := by
  rw [← sum_weight_disjoint P G q hG, ← thinned_square]
  apply sum_le_sum
  intro J hJ
  have hw := weight_nonneg P q hq (mem_powerset.mp hJ)
  by_cases hd : Disjoint G J
  · have he : G ∩ J=∅ := disjoint_iff_inter_eq_empty.mp hd
    simp [hd,he,poly_empty,hlam]
  · simp only [if_neg hd]
    exact mul_nonneg hw (sq_nonneg _)

variable {α : Type*}

noncomputable def jointCount (X : Finset α) (G : α → Finset ι) (S : Finset ι) : ℝ :=
  ((X.filter (fun x => S ⊆ G x)).card : ℝ)

noncomputable def remainder (X : Finset α) (G : α → Finset ι)
    (r : ι → ℝ) (M : ℝ) (S : Finset ι) : ℝ :=
  jointCount X G S-M*(∏ p ∈ S, r p)

noncomputable def quadraticForm (P : Finset ι) (r : ι → ℝ)
    (lam : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
    lam S*lam T*(∏ p ∈ S ∪ T, r p)

lemma sum_avoidance_le (P : Finset ι) (X : Finset α) (G : α → Finset ι)
    (q : ι → ℝ) (lam : Finset ι → ℝ)
    (hG : ∀ x ∈ X, G x ⊆ P) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hlam : lam ∅=1) :
    (∑ x ∈ X, ∏ p ∈ G x, (1-q p)) ≤
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        lam S*lam T*(∏ p ∈ S ∪ T, q p)*jointCount X G (S ∪ T) := by
  calc
    _ ≤ ∑ x ∈ X, ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        if S ∪ T ⊆ G x then lam S*lam T*(∏ p ∈ S ∪ T, q p) else 0 :=
      sum_le_sum (fun x hx => product_avoidance_le P (G x) q lam (hG x hx) hq hlam)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro S hS
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      simp only [jointCount,mul_comm]

lemma sum_avoidance_le_main_error (P : Finset ι) (X : Finset α) (G : α → Finset ι)
    (q r : ι → ℝ) (M : ℝ) (lam : Finset ι → ℝ)
    (hG : ∀ x ∈ X, G x ⊆ P) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hlam : lam ∅=1) :
    (∑ x ∈ X, ∏ p ∈ G x, (1-q p)) ≤
      M*quadraticForm P (fun p => q p*r p) lam +
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        |lam S*lam T| *(∏ p ∈ S ∪ T, q p)* |remainder X G r M (S ∪ T)| := by
  apply (sum_avoidance_le P X G q lam hG hq hlam).trans
  have hterm (S T : Finset ι) (hS : S ⊆ P) (hT : T ⊆ P) :
      lam S*lam T*(∏ p ∈ S ∪ T, q p)*jointCount X G (S ∪ T) ≤
        M*(lam S*lam T*(∏ p ∈ S ∪ T, q p*r p)) +
        |lam S*lam T| *(∏ p ∈ S ∪ T, q p)* |remainder X G r M (S ∪ T)| := by
    have hq0 : 0 ≤ ∏ p ∈ S ∪ T, q p := prod_nonneg (fun p hp =>
      (hq p ((union_subset hS hT) hp)).1)
    have he : jointCount X G (S ∪ T) =
        M*(∏ p ∈ S ∪ T, r p)+remainder X G r M (S ∪ T) := by
      dsimp only [remainder]; ring
    rw [he,prod_mul_distrib]
    have hh : (lam S*lam T)*remainder X G r M (S ∪ T) ≤
        |lam S*lam T| * |remainder X G r M (S ∪ T)| := by
      rw [← abs_mul]; exact le_abs_self _
    have hh' := mul_le_mul_of_nonneg_right hh hq0
    nlinarith only [hh']
  calc
    _ ≤ ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        (M*(lam S*lam T*(∏ p ∈ S ∪ T, q p*r p)) +
        |lam S*lam T| *(∏ p ∈ S ∪ T, q p)* |remainder X G r M (S ∪ T)|) :=
      sum_le_sum (fun S hS => sum_le_sum (fun T hT =>
        hterm S T (mem_powerset.mp hS) (mem_powerset.mp hT)))
    _ = _ := by simp only [sum_add_distrib,← mul_sum,quadraticForm]

omit [DecidableEq ι] in
lemma few_hits_le_avoidance (X : Finset α) (G : α → Finset ι) (k : ℕ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (((X.filter (fun x => (G x).card ≤ k)).card : ℝ)*(1-q)^k) ≤
      ∑ x ∈ X, ∏ _p ∈ G x, (1-q) := by
  have hp0 : 0 ≤ 1-q := sub_nonneg.mpr hq1
  calc
    _ = ∑ x ∈ X, if (G x).card ≤ k then (1-q)^k else 0 := by
      rw [← sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro x hx
      rw [prod_const]
      split_ifs with h
      · exact pow_le_pow_of_le_one hp0 (by linarith) h
      · exact pow_nonneg hp0 _

/-- The sample need not consist of integers. The full error term records
all departures from the proposed multiplicative local densities r. -/
theorem few_hits_le_main_error (P : Finset ι) (X : Finset α)
    (G : α → Finset ι) (r : ι → ℝ) (M : ℝ) (lam : Finset ι → ℝ)
    (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hG : ∀ x ∈ X, G x ⊆ P) (hlam : lam ∅=1) :
    (((X.filter (fun x => (G x).card ≤ k)).card : ℝ)*(1-q)^k) ≤
      M*quadraticForm P (fun p => q*r p) lam +
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        |lam S*lam T| *q^((S ∪ T).card)* |remainder X G r M (S ∪ T)| := by
  apply (few_hits_le_avoidance X G k hq0 hq1).trans
  simpa only [prod_const] using sum_avoidance_le_main_error P X G
    (fun _ => q) r M lam hG (fun _ _ => ⟨hq0,hq1⟩) hlam

#print axioms sum_weight_supersets
#print axioms sum_weight_disjoint
#print axioms product_avoidance_le
#print axioms few_hits_le_main_error
end Erdos1206.FiniteThinnedSieve
