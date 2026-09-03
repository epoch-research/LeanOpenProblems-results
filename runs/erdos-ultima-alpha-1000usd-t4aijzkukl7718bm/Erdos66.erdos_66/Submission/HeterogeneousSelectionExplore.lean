import Submission.UniformSelectionExplore

/-! Finite independent selections with different choice spaces and different
hit tests in each coordinate. This is an auxiliary selection principle. -/
namespace Erdos66HeterogeneousSelection
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
  [∀ i, DecidableEq (α i)]

lemma mean_product (g : ∀ i, α i → ℝ) :
    mean (fun ω : ∀ i, α i ↦ ∏ i, g i (ω i)) = ∏ i, mean (g i) := by
  simp only [mean, Fintype.card_pi, Nat.cast_prod]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]

noncomputable def hits (S : ∀ i, Finset (α i)) (ω : ∀ i, α i) : ℝ :=
  ∑ i, if ω i ∈ S i then (1 : ℝ) else 0

noncomputable def hitMass (S : ∀ i, Finset (α i)) : ℝ :=
  ∑ i, (S i).card / (Fintype.card (α i) : ℝ)

lemma hits_nonneg (S : ∀ i, Finset (α i)) (ω : ∀ i, α i) : 0 ≤ hits S ω := by
  exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)

lemma hitMass_nonneg (S : ∀ i, Finset (α i)) : 0 ≤ hitMass S := by
  exact Finset.sum_nonneg (fun _ _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma hit_mgf_bound (S : ∀ i, Finset (α i)) (t : ℝ) :
    mean (fun ω : ∀ i, α i ↦ Real.exp (t * hits S ω)) ≤
      Real.exp (Real.exp t * hitMass S) := by
  have he : mean (fun ω : ∀ i, α i ↦ Real.exp (t * hits S ω)) =
      ∏ i, mean (fun x : α i ↦ Real.exp (t * (if x ∈ S i then (1 : ℝ) else 0))) := by
    simpa only [hits, Finset.mul_sum, Real.exp_sum] using
      (mean_product (fun i x ↦ Real.exp (t * (if x ∈ S i then (1 : ℝ) else 0))))
  rw [he]
  have hbound (i : ι) : mean (fun x : α i ↦ Real.exp (t * (if x ∈ S i then (1 : ℝ) else 0))) ≤
      Real.exp (Real.exp t * ((S i).card / (Fintype.card (α i) : ℝ))) := by
    rw [mean_exp_hit]
    have hs : (0 : ℝ) ≤ (S i).card / Fintype.card (α i) := by positivity
    have hh := mul_le_mul_of_nonneg_right (show Real.exp t - 1 ≤ Real.exp t by linarith) hs
    have hb := Real.add_one_le_exp (Real.exp t * ((S i).card / (Fintype.card (α i) : ℝ)))
    simp only [mul_div_assoc]
    linarith
  calc
    _ ≤ ∏ i, Real.exp (Real.exp t * ((S i).card / (Fintype.card (α i) : ℝ))) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)) (Nat.cast_nonneg _)
      · exact fun i _ ↦ hbound i
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]; rfl

/-- At most one forbidden value in a specified coordinate costs the reciprocal
of that coordinate's cardinality, even when the other choice spaces differ. -/
lemma one_fiber_indicator_bound (P : (∀ i, α i) → Prop) [DecidablePred P] (i : ι)
    (hP : ∀ f : ∀ i, α i, ∀ x y : α i,
      P (Function.update f i x) → P (Function.update f i y) → x = y) :
    mean (fun ω : ∀ i, α i ↦ if P ω then (1 : ℝ) else 0) ≤
      1 / Fintype.card (α i) := by
  let a₀ : α i := Classical.choice inferInstance
  let B : Finset (∀ i, α i) := Finset.univ.filter P
  let U : Finset (∀ i, α i) := Finset.univ.filter (fun f ↦ f i = a₀)
  have hsub : B.image (fun f ↦ Function.update f i a₀) ⊆ U := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    simp [U]
  have hinj : Set.InjOn (fun f : ∀ i, α i ↦ Function.update f i a₀) (B : Set (∀ i, α i)) := by
    intro f hf g hg he
    have hfP : P f := (Finset.mem_filter.mp hf).2
    have hgP : P g := (Finset.mem_filter.mp hg).2
    have he' : Function.update f i (g i) = g := by
      apply Function.update_eq_iff.mpr
      refine ⟨rfl, fun j hj ↦ ?_⟩
      have hh := congrFun he j
      simpa [Function.update_of_ne hj] using hh
    have hi : f i = g i := hP f (f i) (g i) (by simpa using hfP) (by rwa [he'])
    funext j
    by_cases hj : j = i
    · subst j; exact hi
    · have hh := congrFun he j
      simpa [Function.update_of_ne hj] using hh
  have hUcard : U.card = ∏ j ∈ Finset.univ.erase i, Fintype.card (α j) := by
    have hh := Fintype.card_filter_piFinset_eq_of_mem
      (fun j ↦ (Finset.univ : Finset (α j))) i (Finset.mem_univ a₀)
    simpa only [Fintype.piFinset_univ, Finset.card_univ] using hh
  have hcard : B.card ≤ ∏ j ∈ Finset.univ.erase i, Fintype.card (α j) := by
    rw [← hUcard, ← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hq : (0 : ℝ) < Fintype.card (α i) := by exact_mod_cast Fintype.card_pos
  have hprod : (0 : ℝ) < ∏ j ∈ Finset.univ.erase i, (Fintype.card (α j) : ℝ) := by
    apply Finset.prod_pos
    intro j hj
    exact_mod_cast Fintype.card_pos (α := α j)
  rw [mean_indicator, Fintype.card_pi, Nat.cast_prod]
  have hh : (B.card : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (Fintype.card (α j) : ℝ) := by
    exact_mod_cast hcard
  apply (div_le_div_of_nonneg_right hh (by positivity)).trans_eq
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  field_simp

/-- A joint potential bound with heterogeneous coordinate costs, hit masses,
thresholds, and exponential tilts. -/
theorem exists_avoid_and_small_hits {κ ζ : Type*}
    (E : Finset κ) (P : κ → (∀ i, α i) → Prop) [∀ e, DecidablePred (P e)]
    (v : κ → ι)
    (hP : ∀ e ∈ E, ∀ f : ∀ i, α i, ∀ x y : α (v e),
      P e (Function.update f (v e) x) → P e (Function.update f (v e) y) → x = y)
    (T : Finset ζ) (S : ζ → ∀ i, Finset (α i)) (R t : ζ → ℝ)
    (ht : ∀ z ∈ T, 0 < t z)
    (hsmall : (∑ e ∈ E, 1 / (Fintype.card (α (v e)) : ℝ)) +
      ∑ z ∈ T, Real.exp (Real.exp (t z) * hitMass (S z) - t z * R z) < 1) :
    ∃ ω : ∀ i, α i, (∀ e ∈ E, ¬ P e ω) ∧ ∀ z ∈ T, hits (S z) ω < R z := by
  let F : (∀ i, α i) → ℝ := fun ω ↦
    (∑ e ∈ E, if P e ω then (1 : ℝ) else 0) +
      ∑ z ∈ T, Real.exp (t z * (hits (S z) ω - R z))
  have hterm (z : ζ) :
      mean (fun ω : ∀ i, α i ↦ Real.exp (t z * (hits (S z) ω - R z))) ≤
        Real.exp (Real.exp (t z) * hitMass (S z) - t z * R z) := by
    have he (ω : ∀ i, α i) : Real.exp (t z * (hits (S z) ω - R z)) =
        Real.exp (-t z * R z) * Real.exp (t z * hits (S z) ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    rw [mean_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hit_mgf_bound (S z) (t z)) (Real.exp_pos (-t z * R z)).le
    apply hb.trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have hF : mean F < 1 := by
    dsimp only [F]
    rw [mean_add, mean_sum, mean_sum]
    have hb := Finset.sum_le_sum (fun e he ↦ one_fiber_indicator_bound (P e) (v e) (hP e he))
    have hs := Finset.sum_le_sum (fun z (_ : z ∈ T) ↦ hterm z)
    exact (add_le_add hb hs).trans_lt hsmall
  obtain ⟨ω, hω⟩ := exists_lt_of_mean_lt F 1 hF
  have hbad0 : 0 ≤ ∑ e ∈ E, if P e ω then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
  have hhit0 : 0 ≤ ∑ z ∈ T, Real.exp (t z * (hits (S z) ω - R z)) :=
    Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  refine ⟨ω, ?_, ?_⟩
  · intro e he heP
    have hh := Finset.single_le_sum
      (f := fun e ↦ if P e ω then (1 : ℝ) else 0)
      (fun _ _ ↦ by dsimp only; split_ifs <;> norm_num) he
    dsimp only at hh
    rw [if_pos heP] at hh
    dsimp only [F] at hω
    linarith
  · intro z hz
    have hh := Finset.single_le_sum
      (f := fun z ↦ Real.exp (t z * (hits (S z) ω - R z)))
      (fun _ _ ↦ (Real.exp_pos _).le) hz
    have he : Real.exp (t z * (hits (S z) ω - R z)) < 1 := by
      dsimp only [F] at hω
      linarith
    have he' := Real.exp_lt_one_iff.mp he
    have hz' := ht z hz
    nlinarith

end Erdos66HeterogeneousSelection
