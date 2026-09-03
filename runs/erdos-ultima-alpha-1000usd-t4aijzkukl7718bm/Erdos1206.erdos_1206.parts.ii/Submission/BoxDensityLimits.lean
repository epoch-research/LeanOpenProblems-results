import Submission.PrimeBoxCRT

/-! Limits for normalized periodic box counts, with the first axis removed. -/
namespace Erdos1206.BoxDensityLimits
open Finset Filter PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def box (N : ℕ) (P : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter P
noncomputable def positiveBox (N : ℕ) (P : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter (fun x => 0 < x.1 ∧ P x)

lemma remove_axis_bounds (N : ℕ) (P : ℕ × ℕ → Prop) :
    (positiveBox N P).card ≤ (box N P).card ∧
      (box N P).card ≤ (positiveBox N P).card+N := by
  constructor
  · exact card_le_card (fun x hx => mem_filter.mpr
      ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2⟩)
  · have hsub : box N P ⊆ positiveBox N P ∪ ({0} ×ˢ range N) := by
      intro x hx
      obtain ⟨hxN,hxP⟩ := mem_filter.mp hx
      by_cases hx0 : x.1=0
      · exact mem_union_right _ (mem_product.mpr ⟨by simp [hx0],(mem_product.mp hxN).2⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hxN,Nat.pos_of_ne_zero hx0,hxP⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simpa only [card_product,card_singleton,card_range,one_mul] using hh

lemma trimmed_discrepancy (N : ℕ) (P : ℕ × ℕ → Prop) (δ E : ℝ)
    (h : |((box N P).card:ℝ)-δ*(N:ℝ)^2| ≤ E) :
    |((positiveBox N P).card:ℝ)-δ*(N:ℝ)^2| ≤ E+N := by
  obtain ⟨hl,hu⟩ := remove_axis_bounds N P
  have hlR : ((positiveBox N P).card:ℝ) ≤ (box N P).card := by exact_mod_cast hl
  have huR : ((box N P).card:ℝ) ≤ (positiveBox N P).card+N := by exact_mod_cast hu
  obtain ⟨h1,h2⟩ := abs_le.mp h
  exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α := ℝ) N]⟩

lemma normalized_limit (f : ℕ → ℝ) (δ C D : ℝ)
    (h : ∀ N, |f N-δ*(N:ℝ)^2| ≤ C*N+D) :
    Tendsto (fun N => f N/(N:ℝ)^2) atTop (nhds δ) := by
  have hi : Tendsto (fun N : ℕ => (1:ℝ)/N) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have he : Tendsto (fun N : ℕ => C*(1/(N:ℝ))+D*(1/(N:ℝ))^2) atTop (nhds 0) := by
    simpa using (hi.const_mul C).add ((hi.pow 2).const_mul D)
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖f N/(N:ℝ)^2-δ‖ ≤ C*(1/(N:ℝ))+D*(1/(N:ℝ))^2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs]
    calc
      _ = |f N-δ*(N:ℝ)^2|/(N:ℝ)^2 := by
        have heq : f N/(N:ℝ)^2-δ=(f N-δ*(N:ℝ)^2)/(N:ℝ)^2 := by field_simp
        rw [heq,abs_div,abs_of_pos (sq_pos_of_pos hNR)]
      _ ≤ (C*N+D)/(N:ℝ)^2 := div_le_div_of_nonneg_right (h N) (sq_nonneg _)
      _ = _ := by field_simp
  have ht := (squeeze_zero_norm' hb he).add_const δ
  simpa only [sub_add_cancel,zero_add] using ht

/-- Removing one axis does not change the CRT density. -/
theorem joint_positive_density (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (G : (p : ℕ) → Finset (ZMod p × ZMod p)) :
    Tendsto (fun N : ℕ => ((positiveBox N (fun x =>
      ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p)).card:ℝ)/(N:ℝ)^2)
      atTop (nhds (∏p∈S,localDensity G p)) := by
  let d : ℝ := ∏p∈S,(p:ℝ)
  apply normalized_limit _ _ (2*d+1) (d^2)
  intro N
  have hh := trimmed_discrepancy N (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p)
    (∏p∈S,localDensity G p) (2*(N:ℝ)*d+d^2) (by
      have heq : box N (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p) =
          (range N ×ˢ range N).filter (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p) := by
        ext x
        simp only [box,mem_filter]
      rw [heq,mul_comm (∏p∈S,localDensity G p)]
      exact joint_box_discrepancy S hS G N)
  convert hh using 1; ring

#print axioms joint_positive_density
end Erdos1206.BoxDensityLimits
