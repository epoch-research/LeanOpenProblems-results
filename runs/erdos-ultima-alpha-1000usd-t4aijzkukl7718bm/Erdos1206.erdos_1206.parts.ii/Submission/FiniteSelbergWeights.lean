import Submission.FiniteThinnedSieve

/-!
Finite Selberg weights from an orthogonal product basis. These algebraic
lemmas alone assert neither a sieve dimension nor a density construction.
-/
namespace Erdos1206.FiniteSelbergWeights
open Finset FiniteThinnedSieve
open scoped Classical
variable {ι : Type*} [DecidableEq ι]

noncomputable def odds (r : ι → ℝ) (p : ι) : ℝ := r p/(1-r p)
noncomputable def localMass (r : ι → ℝ) (S : Finset ι) : ℝ := ∏ p ∈ S, odds r p
noncomputable def basis (r : ι → ℝ) (S J : Finset ι) : ℝ :=
  ∏ p ∈ S, if p ∈ J then -1 else odds r p

lemma expectation_product (P : Finset ι) (r f g : ι → ℝ) :
    (∑ J ∈ P.powerset, weight P r J*(∏ p ∈ P, if p ∈ J then f p else g p)) =
      ∏ p ∈ P, (r p*f p+(1-r p)*g p) := by
  rw [prod_add]
  apply sum_congr rfl
  intro J hJ
  have hJP := mem_powerset.mp hJ
  rw [prod_ite,filter_mem_eq_inter,← sdiff_eq_filter,inter_eq_right.mpr hJP]
  simp only [weight,prod_mul_distrib]
  ring

lemma basis_as_product (P S J : Finset ι) (r : ι → ℝ) (hS : S ⊆ P) :
    basis r S J = ∏ p ∈ P,
      if p ∈ J then (if p ∈ S then -1 else 1) else (if p ∈ S then odds r p else 1) := by
  dsimp only [basis]
  apply prod_subset_one_on_sdiff hS
  · intro p hp
    have hpS := (mem_sdiff.mp hp).2
    simp [hpS]
  · intro p hp
    simp [hp]

lemma local_mean {r : ℝ} (hr : r ≠ 1) : r*(-1)+(1-r)*(r/(1-r))=0 := by
  have h : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp
  ring

lemma local_square_mean {r : ℝ} (hr : r ≠ 1) :
    r*((-1)*(-1))+(1-r)*((r/(1-r))*(r/(1-r)))=r/(1-r) := by
  have h : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp
  ring

lemma basis_inner_product (P S T : Finset ι) (r : ι → ℝ)
    (hS : S ⊆ P) (hT : T ⊆ P) (hr : ∀ p ∈ P, r p ≠ 1) :
    (∑ J ∈ P.powerset, weight P r J*(basis r S J*basis r T J)) =
      if S=T then localMass r S else 0 := by
  let f : ι → ℝ := fun p => (if p ∈ S then -1 else 1)*(if p ∈ T then -1 else 1)
  let g : ι → ℝ := fun p => (if p ∈ S then odds r p else 1)*(if p ∈ T then odds r p else 1)
  have he : (∑ J ∈ P.powerset, weight P r J*(basis r S J*basis r T J)) =
      ∏ p ∈ P, (r p*f p+(1-r p)*g p) := by
    calc
      _ = ∑ J ∈ P.powerset, weight P r J*(∏ p ∈ P, if p ∈ J then f p else g p) := by
        apply sum_congr rfl
        intro J hJ
        rw [basis_as_product P S J r hS,basis_as_product P T J r hT,← prod_mul_distrib]
        congr 1
        apply prod_congr rfl
        intro p hp
        dsimp only [f,g]
        split_ifs <;> rfl
      _ = _ := expectation_product P r f g
  rw [he]
  by_cases hST : S=T
  · subst T
    rw [if_pos rfl]
    calc
      _ = ∏ p ∈ S, (r p*f p+(1-r p)*g p) :=
        (prod_subset hS (fun p _ hp => by simp [f,g,hp])).symm
      _ = _ := by
        apply prod_congr rfl
        intro p hp
        simpa [f,g,hp,odds] using local_square_mean (hr p (hS hp))
  · rw [if_neg hST]
    have hex : (∃ p ∈ S, p ∉ T) ∨ (∃ p ∈ T, p ∉ S) := by
      by_contra! h
      apply hST
      exact subset_antisymm h.1 h.2
    rcases hex with ⟨p,hpS,hpT⟩ | ⟨p,hpT,hpS⟩
    · apply prod_eq_zero (hS hpS)
      simpa [f,g,hpS,hpT,odds] using local_mean (hr p (hS hpS))
    · apply prod_eq_zero (hT hpT)
      simpa [f,g,hpS,hpT,odds] using local_mean (hr p (hT hpT))

noncomputable def coefficient (r : ι → ℝ) (S T : Finset ι) : ℝ :=
  (∏ p ∈ T, (-1-odds r p))*(∏ p ∈ S \ T, odds r p)

lemma basis_expansion (S J : Finset ι) (r : ι → ℝ) :
    basis r S J = ∑ T ∈ S.powerset, if T ⊆ J then coefficient r S T else 0 := by
  let f : ι → ℝ := fun p => if p ∈ J then -1-odds r p else 0
  have he : basis r S J = ∏ p ∈ S, (f p+odds r p) := by
    apply prod_congr rfl
    intro p hp
    dsimp only [f]
    split_ifs <;> ring
  rw [he,prod_add]
  apply sum_congr rfl
  intro T hT
  by_cases hTJ : T ⊆ J
  · rw [if_pos hTJ]
    dsimp only [coefficient]
    congr 1
    exact prod_congr rfl (fun p hp => by simp [f,hTJ hp])
  · rw [if_neg hTJ]
    obtain ⟨p,hpT,hpJ⟩ := not_subset.mp hTJ
    have hz : (∏ p ∈ T, f p)=0 := prod_eq_zero hpT (by simp [f,hpJ])
    rw [hz,zero_mul]

noncomputable def sieveMass (r : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, localMass r S

noncomputable def selbergWeight (r : ι → ℝ) (D : Finset (Finset ι))
    (T : Finset ι) : ℝ :=
  (∑ S ∈ D, if T ⊆ S then coefficient r S T else 0)/sieveMass r D

lemma selbergWeight_empty (r : ι → ℝ) (D : Finset (Finset ι))
    (hG : sieveMass r D ≠ 0) : selbergWeight r D ∅=1 := by
  simp only [selbergWeight,empty_subset,if_true,coefficient,prod_empty,sdiff_empty,one_mul]
  exact div_self hG

lemma poly_selbergWeight (P J : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ S ∈ D, S ⊆ P) :
    poly P (selbergWeight r D) J = (∑ S ∈ D, basis r S J)/sieveMass r D := by
  calc
    _ = (∑ T ∈ P.powerset, ∑ S ∈ D,
        if T ⊆ S ∧ T ⊆ J then coefficient r S T else 0)/sieveMass r D := by
      dsimp only [poly,selbergWeight]
      rw [sum_div]
      apply sum_congr rfl
      intro T hT
      by_cases hTJ : T ⊆ J
      · simp [hTJ]
      · simp [hTJ]
    _ = (∑ S ∈ D, ∑ T ∈ P.powerset,
        if T ⊆ S ∧ T ⊆ J then coefficient r S T else 0)/sieveMass r D := by
      rw [sum_comm]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro S hS
      rw [basis_expansion]
      calc
        _ = ∑ T ∈ S.powerset, if T ⊆ S ∧ T ⊆ J then coefficient r S T else 0 := by
          symm
          apply sum_subset (powerset_mono.mpr (hD S hS))
          intro T hT hTS
          simp only [mem_powerset] at hTS
          simp [hTS]
        _ = _ := sum_congr rfl (fun T hT => by simp [mem_powerset.mp hT])

lemma quadraticForm_eq_expectation (P : Finset ι) (r : ι → ℝ)
    (lam : Finset ι → ℝ) : quadraticForm P r lam =
      ∑ J ∈ P.powerset, weight P r J*(poly P lam J)^2 := by
  have hh := thinned_square P P r lam
  calc
    _ = ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        if S ∪ T ⊆ P then lam S*lam T*(∏ p ∈ S ∪ T, r p) else 0 := by
      apply sum_congr rfl
      intro S hS
      apply sum_congr rfl
      intro T hT
      rw [if_pos (union_subset (mem_powerset.mp hS) (mem_powerset.mp hT))]
    _ = _ := hh.symm
    _ = _ := by
      apply sum_congr rfl
      intro J hJ
      rw [inter_eq_right.mpr (mem_powerset.mp hJ)]

lemma sum_basis_square (P : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ S ∈ D, S ⊆ P) (hr : ∀ p ∈ P, r p ≠ 1) :
    (∑ J ∈ P.powerset, weight P r J*(∑ S ∈ D, basis r S J)^2)=sieveMass r D := by
  simp_rw [pow_two,sum_mul_sum,mul_sum]
  rw [sum_comm]
  apply Eq.trans _ (show (∑ S ∈ D, localMass r S)=sieveMass r D from rfl)
  apply sum_congr rfl
  intro S hS
  rw [sum_comm]
  have he : (∑ T ∈ D, ∑ J ∈ P.powerset,
      weight P r J*(basis r S J*basis r T J)) =
      ∑ T ∈ D, if S=T then localMass r S else 0 := by
    apply sum_congr rfl
    intro T hT
    exact basis_inner_product P S T r (hD S hS) (hD T hT) hr
  rw [he]
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS; simp [Ne.symm hTS]
  · exact fun hh => (hh hS).elim

/-- The main quadratic form is exactly the reciprocal sieve mass. -/
theorem selbergWeight_main (P : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ S ∈ D, S ⊆ P) (hr : ∀ p ∈ P, r p ≠ 1)
    (hG : sieveMass r D ≠ 0) :
    quadraticForm P r (selbergWeight r D)=1/sieveMass r D := by
  rw [quadraticForm_eq_expectation]
  simp_rw [poly_selbergWeight P _ r D hD,div_pow]
  simp only [← mul_div_assoc]
  rw [← sum_div,sum_basis_square P r D hD hr]
  field_simp

lemma selbergWeight_support (r : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ S ∈ D, ∀ T, T ⊆ S → T ∈ D) {T : Finset ι} (hT : T ∉ D) :
    selbergWeight r D T=0 := by
  dsimp only [selbergWeight]
  rw [sum_eq_zero,zero_div]
  intro S hS
  exact if_neg (fun h => hT (hD S hS T h))

omit [DecidableEq ι] in
lemma sieveMass_pos (P : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ S ∈ D, S ⊆ P) (h0 : ∅ ∈ D)
    (hr : ∀ p ∈ P, 0 < r p ∧ r p < 1) : 0 < sieveMass r D := by
  have hm (S : Finset ι) (hS : S ∈ D) : 0 ≤ localMass r S := by
    apply prod_nonneg
    intro p hp
    exact (div_pos (hr p (hD S hS hp)).1 (sub_pos.mpr (hr p (hD S hS hp)).2)).le
  have hh := single_le_sum hm h0
  have he : localMass r ∅=1 := by simp [localMass]
  rw [he] at hh
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hh

omit [DecidableEq ι] in
lemma localMass_nonneg (P S : Finset ι) (r : ι → ℝ) (hS : S ⊆ P)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) : 0 ≤ localMass r S := by
  apply prod_nonneg
  intro p hp
  exact div_nonneg (hr p (hS hp)).1 (sub_pos.mpr (hr p (hS hp)).2).le

lemma abs_coefficient (P S T : Finset ι) (r : ι → ℝ)
    (hS : S ⊆ P) (hT : T ⊆ P) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) :
    |coefficient r S T| = (∏ p ∈ T, (1+odds r p))*localMass r (S \ T) := by
  rw [coefficient,abs_mul,abs_prod]
  change (∏ p ∈ T, |-1-odds r p|)* |localMass r (S \ T)| = _
  rw [abs_of_nonneg (localMass_nonneg P (S \ T) r (sdiff_subset.trans hS) hr)]
  congr 1
  apply prod_congr rfl
  intro p hp
  have hp0 : 0 ≤ odds r p := div_nonneg (hr p (hT hp)).1 (sub_pos.mpr (hr p (hT hp)).2).le
  rw [abs_of_nonpos (by linarith : -1-odds r p ≤ 0)]
  ring

lemma mass_of_supersets_le (P T : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hP : ∀ S ∈ D, S ⊆ P) (hD : ∀ S ∈ D, ∀ U, U ⊆ S → U ∈ D)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) :
    (∑ S ∈ D, if T ⊆ S then localMass r (S \ T) else 0) ≤ sieveMass r D := by
  let E := D.filter (fun S => T ⊆ S)
  have hinj : Set.InjOn (fun S : Finset ι => S \ T) (↑E : Set (Finset ι)) := by
    intro S hS U hU he
    dsimp only at he
    have hs := (mem_filter.mp hS).2
    have hu := (mem_filter.mp hU).2
    calc
      S = T ∪ (S \ T) := (union_sdiff_of_subset hs).symm
      _ = T ∪ (U \ T) := by rw [he]
      _ = U := union_sdiff_of_subset hu
  have hsub : E.image (fun S => S \ T) ⊆ D := by
    intro U hU
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hU
    exact hD S (mem_filter.mp hS).1 _ sdiff_subset
  calc
    _ = ∑ S ∈ E, localMass r (S \ T) := (sum_filter _ _).symm
    _ = ∑ U ∈ E.image (fun S => S \ T), localMass r U := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun U hU _ => localMass_nonneg P U r (hP U hU) hr)

/-- The coefficients do not incur a factor equal to the full sieve mass.
Downward closure of the truncation is essential for this estimate. -/
theorem selbergWeight_abs_le (P T : Finset ι) (r : ι → ℝ) (D : Finset (Finset ι))
    (hP : ∀ S ∈ D, S ⊆ P) (hT : T ⊆ P)
    (hD : ∀ S ∈ D, ∀ U, U ⊆ S → U ∈ D)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) (hG : 0 < sieveMass r D) :
    |selbergWeight r D T| ≤ ∏ p ∈ T, (1+odds r p) := by
  have hb0 : 0 ≤ ∏ p ∈ T, (1+odds r p) := by
    apply prod_nonneg
    intro p hp
    have hh : 0 ≤ odds r p := div_nonneg (hr p (hT hp)).1 (sub_pos.mpr (hr p (hT hp)).2).le
    linarith
  rw [selbergWeight,abs_div,abs_of_pos hG]
  apply (div_le_iff₀ hG).mpr
  calc
    _ ≤ ∑ S ∈ D, |if T ⊆ S then coefficient r S T else 0| := abs_sum_le_sum_abs _ _
    _ = (∏ p ∈ T, (1+odds r p))*
        (∑ S ∈ D, if T ⊆ S then localMass r (S \ T) else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S hS
      split_ifs with h
      · exact abs_coefficient P S T r (hP S hS) hT hr
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_of_supersets_le P T r D hP hD hr) hb0

#print axioms expectation_product
#print axioms basis_inner_product
#print axioms selbergWeight_main
#print axioms selbergWeight_support
#print axioms sieveMass_pos
#print axioms selbergWeight_abs_le
end Erdos1206.FiniteSelbergWeights
