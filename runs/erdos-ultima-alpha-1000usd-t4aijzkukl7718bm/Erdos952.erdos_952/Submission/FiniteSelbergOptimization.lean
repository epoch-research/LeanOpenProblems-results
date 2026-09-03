import FormalConjecturesUtil

/-! Exact optimization of the multiplicative Lambda-squared main term on a
finite downward-closed family of squarefree supports. Local densities are
arbitrary numbers strictly between zero and one; no prime-path estimate is
assumed or obtained from the optimization alone. -/
namespace Erdos952Investigation.FiniteSelbergOptimization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

variable {ι : Type*}

def mass (ν : ι → ℝ) (s : Finset ι) : ℝ := ∏ i ∈ s, ν i
def diagonal (ν : ι → ℝ) (s : Finset ι) : ℝ := ∏ i ∈ s, (1-ν i)/ν i
def sign (s : Finset ι) : ℝ := (-1)^s.card

def DownClosed (D : Finset (Finset ι)) : Prop :=
  ∀ s ∈ D, ∀ t, t ⊆ s → t ∈ D

def main (D : Finset (Finset ι)) (ν : ι → ℝ) (w : D → ℝ) : ℝ :=
  ∑ s : D, ∑ t : D, w s*w t*mass ν (s.val∪t.val)

def transform (D : Finset (Finset ι)) (ν : ι → ℝ) (w : D → ℝ) (r : D) : ℝ :=
  ∑ s : D, if r.val ⊆ s.val then w s*mass ν s.val else 0

def denominator (D : Finset (Finset ι)) (ν : ι → ℝ) : ℝ :=
  ∑ r : D, 1/diagonal ν r.val

lemma mass_pos (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (s : Finset ι) : 0 < mass ν s :=
  Finset.prod_pos (fun i _ => hν i)

lemma diagonal_pos (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) (s : Finset ι) :
    0 < diagonal ν s :=
  Finset.prod_pos (fun i _ => div_pos (sub_pos.mpr (hν i).2) (hν i).1)

lemma sign_sq (s : Finset ι) : sign s^2 = 1 := by
  dsimp [sign]
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

lemma sum_subsets (D : Finset (Finset ι)) (hD : DownClosed D)
    (s : Finset ι) (hs : s ∈ D) (f : Finset ι → ℝ) :
    (∑ r : D, if r.val ⊆ s then f r.val else 0) = ∑ r ∈ s.powerset, f r := by
  classical
  rw [Finset.sum_coe_sort D (fun r => if r ⊆ s then f r else 0),← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter,Finset.mem_powerset]
  exact ⟨fun h => h.2,fun h => ⟨hD s hs r h,h⟩⟩

lemma sum_sign_subsets (s : Finset ι) :
    (∑ r ∈ s.powerset, sign r) = if s = ∅ then 1 else 0 := by
  classical
  have hh := Finset.sum_powerset_neg_one_pow_card (x := s)
  dsimp only [sign]
  exact_mod_cast hh

lemma diagonal_powerset_sum (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (s : Finset ι) :
    (∑ r ∈ s.powerset, diagonal ν r) = 1/mass ν s := by
  unfold diagonal mass
  rw [← Finset.prod_add_one,one_div,← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  field_simp [(hν i).ne']
  ring

lemma union_mass (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (s t : Finset ι) :
    mass ν (s∪t) = mass ν s*mass ν t*∑ r ∈ (s∩t).powerset, diagonal ν r := by
  rw [diagonal_powerset_sum ν hν]
  have hi := (mass_pos ν hν (s∩t)).ne'
  have hh : mass ν (s∪t)*mass ν (s∩t) = mass ν s*mass ν t := Finset.prod_union_inter
  rw [hh.symm]
  field_simp

/-- Diagonalization is exact. A squarefree support is represented by the
finite set of its prime factors, so lcm corresponds to union. -/
theorem main_eq_sum_squares (D : Finset (Finset ι)) (hD : DownClosed D)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (w : D → ℝ) :
    main D ν w = ∑ r : D, diagonal ν r.val*(transform D ν w r)^2 := by
  classical
  have hentry (s t : D) : w s*w t*mass ν (s.val∪t.val) =
      ∑ r : D, diagonal ν r.val*
        (if r.val ⊆ s.val then w s*mass ν s.val else 0)*
        (if r.val ⊆ t.val then w t*mass ν t.val else 0) := by
    rw [union_mass ν hν,← sum_subsets D hD (s.val∩t.val)
      (hD s.val s.property _ Finset.inter_subset_left),Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.subset_inter_iff]
    by_cases hs : r.val ⊆ s.val <;> by_cases ht : r.val ⊆ t.val <;>
      simp only [hs,ht,and_self,if_true,if_false,false_and,and_false] <;> ring
  calc
    main D ν w = ∑ s : D, ∑ t : D, ∑ r : D, diagonal ν r.val*
        (if r.val ⊆ s.val then w s*mass ν s.val else 0)*
        (if r.val ⊆ t.val then w t*mass ν t.val else 0) := by
      unfold main
      exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => hentry s t))
    _ = ∑ s : D, ∑ r : D, ∑ t : D, diagonal ν r.val*
        (if r.val ⊆ s.val then w s*mass ν s.val else 0)*
        (if r.val ⊆ t.val then w t*mass ν t.val else 0) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ r : D, ∑ s : D, ∑ t : D, diagonal ν r.val*
        (if r.val ⊆ s.val then w s*mass ν s.val else 0)*
        (if r.val ⊆ t.val then w t*mass ν t.val else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [transform,pow_two,Finset.mul_sum,Finset.sum_mul,mul_assoc]
      exact Finset.sum_comm

/-- The normalization at the empty support is the alternating sum of the
transformed variables. Downward closure is essential here. -/
lemma transform_normalization (D : Finset (Finset ι)) (hD : DownClosed D)
    (h0 : ∅ ∈ D) (ν : ι → ℝ) (w : D → ℝ) :
    (∑ r : D, sign r.val*transform D ν w r) = w ⟨∅,h0⟩ := by
  classical
  simp only [transform,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hh (s : D) : (∑ r : D, sign r.val*(if r.val ⊆ s.val then w s*mass ν s.val else 0)) =
      w s*mass ν s.val*(if s.val = ∅ then 1 else 0) := by
    rw [← sum_sign_subsets,← sum_subsets D hD s.val s.property,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> ring
  simp_rw [hh]
  rw [Finset.sum_eq_single ⟨∅,h0⟩]
  · simp [mass]
  · intro s hs hne
    have hn : s.val ≠ ∅ := fun he => hne (Subtype.ext he)
    simp [hn]
  · simp

lemma denominator_pos (D : Finset (Finset ι)) (h0 : ∅ ∈ D)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) : 0 < denominator D ν := by
  apply Finset.sum_pos (fun r _ => one_div_pos.mpr (diagonal_pos ν hν r.val))
  exact ⟨⟨∅,h0⟩,Finset.mem_univ _⟩

/-- Every normalized choice of real weights has main term at least 1/G,
where G is the sum of the reciprocal diagonal coefficients. -/
theorem reciprocal_denominator_le_main (D : Finset (Finset ι)) (hD : DownClosed D)
    (h0 : ∅ ∈ D) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1)
    (w : D → ℝ) (hw : w ⟨∅,h0⟩ = 1) : 1/denominator D ν ≤ main D ν w := by
  have hh := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset D)
    (fun r => sign r.val*transform D ν w r)
    (g := fun r => 1/diagonal ν r.val)
    (fun r _ => one_div_pos.mpr (diagonal_pos ν hν r.val))
  rw [transform_normalization D hD h0 ν w,hw,one_pow] at hh
  rw [main_eq_sum_squares D hD ν (fun i => (hν i).1)]
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_pow,sign_sq,one_mul]
  simp only [one_div,div_inv_eq_mul,mul_comm]

/-- The change of variables is a triangular linear map. -/
def transformMap (D : Finset (Finset ι)) (ν : ι → ℝ) : (D → ℝ) →ₗ[ℝ] (D → ℝ) where
  toFun := transform D ν
  map_add' u v := by
    funext r
    simp only [transform,Pi.add_apply,add_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> ring
  map_smul' c u := by
    funext r
    simp only [transform,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> ring

lemma transform_injective (D : Finset (Finset ι)) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) :
    Function.Injective (transformMap D ν) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  by_contra hn
  have hn' : ∃ r : D, w r ≠ 0 := by
    by_contra! he
    apply hn
    funext r
    exact he r
  let S := Finset.univ.filter (fun r : D => w r ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨r,hr⟩ := hn'
    exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  obtain ⟨r,hr,hm⟩ := S.exists_max_image (fun r : D => r.val.card) hS
  have hwr : w r ≠ 0 := (Finset.mem_filter.mp hr).2
  have hzero : transform D ν w r = 0 := congrFun hw r
  have he : transform D ν w r = w r*mass ν r.val := by
    unfold transform
    rw [Finset.sum_eq_single r]
    · simp
    · intro s hs hsr
      by_cases hsub : r.val ⊆ s.val
      · rw [if_pos hsub]
        have hws : w s = 0 := by
          by_contra hws
          have hsS : s ∈ S := Finset.mem_filter.mpr ⟨hs,hws⟩
          exact hsr (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (hm s hsS)).symm)
        rw [hws,zero_mul]
      · simp [hsub]
    · simp
  rw [he] at hzero
  exact (mul_ne_zero hwr (mass_pos ν hν r.val).ne') hzero

/-- In particular the diagonal variables can be assigned arbitrarily. -/
lemma transform_surjective (D : Finset (Finset ι)) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) :
    Function.Surjective (transformMap D ν) :=
  LinearMap.surjective_of_injective (transform_injective D ν hν)

/-- The lower bound is attained. This optimizes ONLY the main quadratic
form, not the main term plus lattice-discrepancy error. -/
theorem exists_optimal_weights (D : Finset (Finset ι)) (hD : DownClosed D)
    (h0 : ∅ ∈ D) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) :
    ∃ w : D → ℝ, w ⟨∅,h0⟩ = 1 ∧ main D ν w = 1/denominator D ν := by
  let G := denominator D ν
  have hG : G ≠ 0 := (denominator_pos D h0 ν hν).ne'
  let y : D → ℝ := fun r => sign r.val/(diagonal ν r.val*G)
  obtain ⟨w,hw⟩ := transform_surjective D ν (fun i => (hν i).1) y
  have he (r : D) : transform D ν w r = y r := congrFun hw r
  refine ⟨w,?_,?_⟩
  · rw [← transform_normalization D hD h0 ν w]
    simp_rw [he]
    have hh (r : D) : sign r.val*y r = (1/diagonal ν r.val)/G := by
      dsimp [y]
      rw [← mul_div_assoc,← pow_two,sign_sq,div_mul_eq_div_div]
    simp_rw [hh]
    rw [← Finset.sum_div]
    change G/G = 1
    exact div_self hG
  · rw [main_eq_sum_squares D hD ν (fun i => (hν i).1)]
    simp_rw [he]
    have hh (r : D) : diagonal ν r.val*(y r)^2 = (1/diagonal ν r.val)/G^2 := by
      have hd := (diagonal_pos ν hν r.val).ne'
      dsimp [y]
      rw [div_pow,mul_pow,sign_sq]
      field_simp
    simp_rw [hh]
    rw [← Finset.sum_div]
    change G/G^2 = 1/G
    field_simp

#print axioms main_eq_sum_squares
#print axioms reciprocal_denominator_le_main
#print axioms exists_optimal_weights
end
end Erdos952Investigation.FiniteSelbergOptimization
