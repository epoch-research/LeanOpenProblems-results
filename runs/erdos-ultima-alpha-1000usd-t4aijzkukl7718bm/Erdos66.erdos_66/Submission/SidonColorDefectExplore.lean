import Submission.SidonColorAnnuliExplore

/-! A quantitative defect version of the short-difference color budget.
The defect is repeated positive differences, not repeated sum targets. -/
namespace Erdos66SidonColorDefect
open Erdos66SidonColorBlockEnergy Erdos66SidonColorAnnuli
open scoped Classical
set_option maxHeartbeats 2000000
variable {I : Type*} [Fintype I]

noncomputable def forward (S : Finset ℕ) (col : ℕ → I) (u : ℕ) :=
  (sameCellPairs S col u).filter (fun ab ↦ ab.1<ab.2)

noncomputable def differenceDefect (S : Finset ℕ) (col : ℕ → I) (u : ℕ) : ℕ :=
  (forward S col u).card-
    ((forward S col u).image (fun ab ↦ (col ab.1,ab.2-ab.1))).card

lemma forward_defect_bound (S : Finset ℕ) (col : ℕ → I) (u : ℕ) (hu : 0<u) :
    (forward S col u).card≤Fintype.card I*u+differenceDefect S col u := by
  let P := forward S col u
  let f : ℕ×ℕ → I×ℕ := fun ab ↦ (col ab.1,ab.2-ab.1)
  have hsub : P.image f⊆(Finset.univ:Finset I)×ˢFinset.range u := by
    intro z hz
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hab,hablt⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb,hcol,hbin⟩ := mem_sameCellPairs.mp hab
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr
      (same_bin_difference_lt hu hablt hbin)⟩
  have hc : (P.image f).card≤Fintype.card I*u := by
    simpa only [Finset.card_product,Finset.card_univ,Finset.card_range] using Finset.card_le_card hsub
  have hi : (P.image f).card≤P.card := Finset.card_image_le
  change P.card≤Fintype.card I*u+(P.card-(P.image f).card)
  omega

lemma sameCellPairs_defect_bound (S : Finset ℕ) (col : ℕ → I) (u : ℕ) (hu : 0<u) :
    (sameCellPairs S col u).card≤S.card+2*Fintype.card I*u+2*differenceDefect S col u := by
  rw [sameCellPairs_card]
  have h := forward_defect_bound S col u hu
  dsimp [forward] at h
  nlinarith

theorem block_energy_defect_bound (S : Finset ℕ) (col : ℕ → I)
    (u : ℕ) (hu : 0<u) (B : Finset ℕ) :
    (∑ b∈B, (binMass S u b:ℝ)^2)≤
      (Fintype.card I:ℝ)*S.card+2*(Fintype.card I:ℝ)^2*u+
        2*Fintype.card I*differenceDefect S col u := by
  have hcs := Finset.sum_le_sum (s:=B) (fun b hb ↦ bin_color_cauchy S col u b)
  rw [←Finset.mul_sum] at hcs
  have hf := partial_fiber_square_sum S (fun a ↦ (col a,a/u)) ((Finset.univ:Finset I)×ˢB)
  have he : ((S×ˢS).filter (fun xy ↦ (col xy.1,xy.1/u)=(col xy.2,xy.2/u)))=
      sameCellPairs S col u := by
    ext xy
    simp only [sameCellPairs,Finset.mem_filter,Prod.mk.injEq]
  rw [he,Finset.sum_product] at hf
  have hfR : (∑ i : I, ∑ b∈B, (((S.filter (fun a ↦ col a=i ∧ a/u=b)).card:ℝ)^2))≤
      (sameCellPairs S col u).card := by
    have hh : (∑ i : I, ∑ b∈B, (((S.filter (fun a ↦ (col a,a/u)=(i,b))).card:ℝ)^2))≤
        (sameCellPairs S col u).card := by exact_mod_cast hf
    simpa only [Prod.mk.injEq] using hh
  rw [Finset.sum_comm] at hfR
  have hb : ((sameCellPairs S col u).card:ℝ)≤S.card+2*(Fintype.card I:ℝ)*u+
      2*differenceDefect S col u := by exact_mod_cast sameCellPairs_defect_bound S col u hu
  have hm := mul_le_mul_of_nonneg_left (hfR.trans hb)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card I))
  nlinarith

/-- Without assuming any coloring property, missing colors must be paid
for by repeated short differences. -/
theorem annular_defect_budget (S : Finset ℕ) (col : ℕ → I) (J : ℕ) (a : ℝ)
    (hprofile : ∀j∈Finset.Ico J (2*J), a^2*(4:ℝ)^j*J≤(shellMass S j:ℝ)^2) :
    a^2*(4:ℝ)^J*(J:ℝ)^2≤3*(Fintype.card I:ℝ)*S.card+
      6*(Fintype.card I:ℝ)^2*(4:ℝ)^J+
        6*Fintype.card I*differenceDefect S col (4^J) := by
  have hjbound (j : ℕ) (hj : j∈Finset.Ico J (2*J)) :
      a^2*(4:ℝ)^J*J≤3*∑ b∈shellBins J j, (binMass S (4^J) b:ℝ)^2 := by
    have hjJ := (Finset.mem_Ico.mp hj).1
    have hl := (hprofile j hj).trans (shell_cauchy S hjJ)
    have he : (4:ℝ)^j=(4:ℝ)^J*(4:ℝ)^(j-J) := by
      rw [←pow_add,Nat.add_sub_of_le hjJ]
    rw [he] at hl
    apply le_of_mul_le_mul_right (a:=(4:ℝ)^(j-J)) _ (by positivity)
    nlinarith
  have hs := Finset.sum_le_sum (s:=Finset.Ico J (2*J)) (fun j hj ↦ hjbound j hj)
  have hc : (Finset.Ico J (2*J)).card=J := by simp only [Nat.card_Ico]; omega
  simp only [Finset.sum_const,hc,nsmul_eq_mul] at hs
  rw [←Finset.mul_sum,←Finset.sum_biUnion (shellBins_disjoint J)] at hs
  have he := block_energy_defect_bound S col (4^J) (by positivity)
    ((Finset.Ico J (2*J)).biUnion (shellBins J))
  push_cast at he
  nlinarith

theorem small_color_defect_lower (S : Finset ℕ) (col : ℕ → I) (J : ℕ) (a b : ℝ)
    (hb : 0≤b)
    (hprofile : ∀j∈Finset.Ico J (2*J), a^2*(4:ℝ)^j*J≤(shellMass S j:ℝ)^2)
    (hsize : (S.card:ℝ)≤b*(4:ℝ)^J*J)
    (hm : (Fintype.card I:ℝ)≤ min 1 (a^2/(6*b+12))*J) :
    a^2*(4:ℝ)^J*(J:ℝ)^2≤12*Fintype.card I*differenceDefect S col (4^J) := by
  let m : ℝ := Fintype.card I
  have hm0 : 0≤ m := by positivity
  have hJ0 : (0:ℝ)≤J := by positivity
  have hmJ : m≤J := hm.trans (by
    have hh := mul_le_mul_of_nonneg_right (min_le_left 1 (a^2/(6*b+12))) hJ0
    simpa using hh)
  have hm' : m≤a^2/(6*b+12)*J := hm.trans
    (mul_le_mul_of_nonneg_right (min_le_right 1 (a^2/(6*b+12))) hJ0)
  have hden : 0<6*b+12 := by positivity
  have hprod : (6*b+12)*m≤a^2*J := by
    have hh := mul_le_mul_of_nonneg_left hm' hden.le
    field_simp at hh
    nlinarith
  have hsq : m^2≤ m*J := by nlinarith
  have hsmall : 3*b*m*J+6*m^2≤(a^2/2)*(J:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right hprod hJ0
    nlinarith
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (show 0≤(4:ℝ)^J by positivity)
  have hsize' := mul_le_mul_of_nonneg_left hsize (show 0≤3*m by positivity)
  have he := annular_defect_budget S col J a hprofile
  change a^2*(4:ℝ)^J*(J:ℝ)^2≤3*m*S.card+6*m^2*(4:ℝ)^J+
    6*m*differenceDefect S col (4^J) at he
  change a^2*(4:ℝ)^J*(J:ℝ)^2≤12*m*differenceDefect S col (4^J)
  nlinarith

end Erdos66SidonColorDefect
