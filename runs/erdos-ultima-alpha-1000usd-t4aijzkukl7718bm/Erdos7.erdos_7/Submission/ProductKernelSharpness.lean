import Submission.ProductRetentionKernel

/-! Sharpness of the area-only product-kernel retention guarantee. These
finite weighted examples are not arithmetic covering systems. -/
namespace Erdos7ProductKernelSharpness
open scoped BigOperators
open Erdos7ProductRetentionKernel Erdos7RootPruning
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

/-- The exact constraints of the product-retention kernel theorem, with all
rows and columns allowed. The coordinate laws may have masses U,V below one. -/
def Feasible (ρ σ : Fin 2 → ℝ) (D : Fin 2 → Fin 2 → Prop)
    (ca cb cab : ℝ) (ν : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ x y, 0 ≤ ν x y) ∧
  (∀ x y, ν x y ≤ cab*ρ x*σ y) ∧
  (∀ x, (∑ y, ν x y) ≤ ca*ρ x) ∧
  (∀ y, (∑ x, ν x y) ≤ cb*σ y) ∧
  (∀ x y, D x y → ν x y = 0)

/-- If the row or joint cap controls the scale, removing an entire bad row
attains that bound, regardless of how nonuniform the candidate kernel is. -/
lemma row_strip_upper (U V d ca cb cab s : ℝ) (hV : 0 < V)
    (hbind : s = ca/V ∨ s = cab)
    (ν : Fin 2 → Fin 2 → ℝ)
    (hν : Feasible ![d/V,U-d/V] ![V,0] (fun x _ => x=0) ca cb cab ν) :
    (∑ x, ∑ y, ν x y) ≤ s*(U*V-d) := by
  have h00 := hν.2.2.2.2 0 0 rfl
  have h01 := hν.2.2.2.2 0 1 rfl
  have h11 : ν 1 1 = 0 := by
    have hc := hν.2.1 1 1
    norm_num at hc
    exact le_antisymm hc (hν.1 1 1)
  have he : (∑ x, ∑ y, ν x y) = ν 1 0 := by
    simp only [Fin.sum_univ_two,h00,h01,h11,add_zero,zero_add]
  rw [he]
  rcases hbind with hbind | hbind
  · rw [hbind]
    have hr := hν.2.2.1 1
    simp only [Fin.sum_univ_two,h11,add_zero,Matrix.cons_val_one,
      Matrix.cons_val_zero] at hr
    have ha : ca*(U-d/V) = ca/V*(U*V-d) := by field_simp
    exact hr.trans_eq ha
  · rw [hbind]
    have hh := hν.2.1 1 0
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero] at hh
    have ha : cab*(U-d/V)*V = cab*(U*V-d) := by field_simp
    exact hh.trans_eq ha

lemma column_strip_upper (U V d ca cb cab s : ℝ) (hU : 0 < U)
    (hbind : s = cb/U)
    (ν : Fin 2 → Fin 2 → ℝ)
    (hν : Feasible ![U,0] ![d/U,V-d/U] (fun _ y => y=0) ca cb cab ν) :
    (∑ x, ∑ y, ν x y) ≤ s*(U*V-d) := by
  have h00 := hν.2.2.2.2 0 0 rfl
  have h10 := hν.2.2.2.2 1 0 rfl
  have h11 : ν 1 1 = 0 := by
    have hc := hν.2.1 1 1
    norm_num at hc
    exact le_antisymm hc (hν.1 1 1)
  have he : (∑ x, ∑ y, ν x y) = ν 0 1 := by
    simp only [Fin.sum_univ_two,h00,h10,h11,add_zero,zero_add]
  rw [he,hbind]
  have hc := hν.2.2.2.1 1
  simp only [Fin.sum_univ_two,h11,add_zero,Matrix.cons_val_one,
    Matrix.cons_val_zero] at hc
  have ha : cb*(V-d/U) = cb/U*(U*V-d) := by field_simp
  exact hc.trans_eq ha

/-- Sharp worst-case theorem for the information (U,V,d,ca,cb,cab) alone.
The same finite example supplies an attainable mass and bounds EVERY feasible
kernel above by that mass. No statement about congruence geometry is made. -/
theorem area_only_sharp (U V d ca cb cab : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hd : 0 ≤ d) (hdUV : d ≤ U*V)
    (ha : 0 ≤ ca) (hb : 0 ≤ cb) (hab : 0 ≤ cab) :
    let s := min cab (min (ca/V) (cb/U))
    ∃ (ρ σ : Fin 2 → ℝ) (D : Fin 2 → Fin 2 → Prop),
      (∀ x, 0 ≤ ρ x) ∧ (∀ y, 0 ≤ σ y) ∧
      (∑ x, ρ x) = U ∧ (∑ y, σ y) = V ∧
      (∑ x, ∑ y, if D x y then ρ x*σ y else 0) = d ∧
      (∃ ν, Feasible ρ σ D ca cb cab ν ∧ (∑ x, ∑ y, ν x y) = s*(U*V-d)) ∧
      (∀ ν, Feasible ρ σ D ca cb cab ν → (∑ x, ∑ y, ν x y) ≤ s*(U*V-d)) := by
  classical
  dsimp only
  let s := min cab (min (ca/V) (cb/U))
  have hs := density_caps U V ca cb cab hU hV ha hb hab
  change 0 ≤ s ∧ s ≤ cab ∧ s*V ≤ ca ∧ s*U ≤ cb at hs
  have hdV : d/V ≤ U := (div_le_iff₀ hV).mpr hdUV
  have hdU : d/U ≤ V := (div_le_iff₀ hU).mpr (by nlinarith)
  have hmass : 0 ≤ s*(U*V-d) := mul_nonneg hs.1 (sub_nonneg.mpr hdUV)
  have construct (ρ σ : Fin 2 → ℝ) (D : Fin 2 → Fin 2 → Prop)
      (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ y, 0 ≤ σ y)
      (hρsum : (∑ x, ρ x)=U) (hσsum : (∑ y, σ y)=V)
      (hD : (∑ x, ∑ y, if D x y then ρ x*σ y else 0)=d) :
      ∃ ν, Feasible ρ σ D ca cb cab ν ∧ (∑ x, ∑ y, ν x y)=s*(U*V-d) := by
    obtain ⟨ν,hn,hcell,hrow,hcol,hzero,hm⟩ := exists_kernel ρ σ hρ hσ
      (fun _ => True) (fun _ => True) D U V d ca cb cab s (s*(U*V-d))
      (by simpa [keep] using hρsum) (by simpa [keep] using hσsum) hD.le
      hs.1 hs.2.2.1 hs.2.2.2 hs.2.1 hmass (le_max_right _ _)
    exact ⟨ν,⟨hn,hcell,hrow,hcol,fun x y h => hzero x y (Or.inr (Or.inr h))⟩,hm⟩
  by_cases hr : s = ca/V ∨ s = cab
  · let ρ : Fin 2 → ℝ := ![d/V,U-d/V]
    let σ : Fin 2 → ℝ := ![V,0]
    let D : Fin 2 → Fin 2 → Prop := fun x _ => x=0
    have hρ : ∀ x, 0 ≤ ρ x := by
      intro x; fin_cases x <;> simp only [ρ,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact div_nonneg hd hV.le
      · exact sub_nonneg.mpr hdV
    have hσ : ∀ y, 0 ≤ σ y := by intro y; fin_cases y <;> simp [σ,hV.le]
    have hρsum : (∑ x, ρ x)=U := by simp [ρ,Fin.sum_univ_two]
    have hσsum : (∑ y, σ y)=V := by simp [σ,Fin.sum_univ_two]
    have hD : (∑ x, ∑ y, @ite ℝ (D x y) (Classical.propDecidable _) (ρ x*σ y) 0)=d := by
      simp [D,ρ,σ,Fin.sum_univ_two,ne_of_gt hV]
    exact ⟨ρ,σ,D,hρ,hσ,hρsum,hσsum,hD,construct ρ σ D hρ hσ hρsum hσsum hD,
      fun ν hν => row_strip_upper U V d ca cb cab s hV hr ν hν⟩
  · have hsbind : s=cb/U := by
      dsimp only [s] at hr ⊢
      rcases min_choice cab (min (ca/V) (cb/U)) with hh | hh
      · exact False.elim (hr (Or.inr hh))
      · rcases min_choice (ca/V) (cb/U) with hh' | hh'
        · exact False.elim (hr (Or.inl (hh.trans hh')))
        · exact hh.trans hh'
    let ρ : Fin 2 → ℝ := ![U,0]
    let σ : Fin 2 → ℝ := ![d/U,V-d/U]
    let D : Fin 2 → Fin 2 → Prop := fun _ y => y=0
    have hρ : ∀ x, 0 ≤ ρ x := by intro x; fin_cases x <;> simp [ρ,hU.le]
    have hσ : ∀ y, 0 ≤ σ y := by
      intro y; fin_cases y <;> simp only [σ,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact div_nonneg hd hU.le
      · exact sub_nonneg.mpr hdU
    have hρsum : (∑ x, ρ x)=U := by simp [ρ,Fin.sum_univ_two]
    have hσsum : (∑ y, σ y)=V := by simp [σ,Fin.sum_univ_two]
    have hD : (∑ x, ∑ y, @ite ℝ (D x y) (Classical.propDecidable _) (ρ x*σ y) 0)=d := by
      simp only [D,ρ,σ,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      norm_num
      field_simp
    exact ⟨ρ,σ,D,hρ,hσ,hρsum,hσsum,hD,construct ρ σ D hρ hσ hρsum hσsum hD,
      fun ν hν => column_strip_upper U V d ca cb cab s hU hsbind ν hν⟩

#print axioms row_strip_upper
#print axioms column_strip_upper
#print axioms area_only_sharp
end Erdos7ProductKernelSharpness
