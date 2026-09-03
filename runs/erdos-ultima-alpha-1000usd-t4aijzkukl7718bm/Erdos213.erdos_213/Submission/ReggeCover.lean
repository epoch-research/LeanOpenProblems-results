import Submission.ReggeCircle
import Submission.CircleCoverReduction

/-! A uniform four-generalized-circle cover for a fixed-triangle cyclic
Regge construction. No claim is made that arbitrary integral-distance sets
satisfy this construction hypothesis. -/
open EuclideanGeometry
namespace Erdos213.ReggeCover
open ReggeCircle CircleCoverReduction InversionReduction
noncomputable section
set_option maxHeartbeats 4000000

private lemma coordinates_nonzero {p : ℝ²} (h : p ≠ 0) : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
  by_contra! hn
  apply h
  ext i
  fin_cases i
  · simpa using hn.1
  · simpa using hn.2

private lemma coordinates_different {p q : ℝ²} (h : p ≠ q) :
    p 0 ≠ q 0 ∨ p 1 ≠ q 1 := by
  by_contra! hn
  apply h
  ext i
  fin_cases i <;> simp [hn.1,hn.2]

def circleLocus (b c : ℝ²) : Set ℝ² :=
  {p | ReggeCircle.circle (b 0) (b 1) (c 0) (c 1) (p 0) (p 1)=0}

def lineLocus (b c : ℝ²) (k : Fin 3) : Set ℝ² :=
  {p | ReggeCircle.parallel (b 0) (b 1) (c 0) (c 1) (p 0) (p 1) k=0}

lemma circleEval_bridge (b c p : ℝ²) :
    circleEval 0 b c p =
      ReggeCircle.circle (b 0) (b 1) (c 0) (c 1) (p 0) (p 1) := by
  simp only [circleEval,ca,cb,cc,qnorm,dx,dy,ReggeCircle.circle]
  simp
  ring

lemma circleLocus_generalized {b c : ℝ²} (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    OnGeneralizedCircle (circleLocus b c) := by
  have he : circleLocus b c = {p : ℝ² | circleEval 0 b c p=0} := by
    ext p
    simp only [circleLocus,Set.mem_setOf_eq,circleEval_bridge]
  rw [he]
  exact circleEval_generalized hb.symm hc.symm hbc

lemma lineLocus_generalized {b c : ℝ²} (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (k : Fin 3) : OnGeneralizedCircle (lineLocus b c k) := by
  have hb' := coordinates_nonzero hb
  have hc' := coordinates_nonzero hc
  have hbc' := coordinates_different hbc
  fin_cases k
  · refine ⟨0,-b 1,b 0,b 1*c 0-b 0*c 1,?_,?_⟩
    · apply Or.inr
      simpa only [neg_ne_zero] using hb'.symm
    · intro p hp
      change b 0*(p 1-c 1)-b 1*(p 0-c 0)=0 at hp
      dsimp [radiusSq]
      linear_combination hp
  · refine ⟨0,-c 1,c 0,c 1*b 0-c 0*b 1,?_,?_⟩
    · apply Or.inr
      simpa only [neg_ne_zero] using hc'.symm
    · intro p hp
      change c 0*(p 1-b 1)-c 1*(p 0-b 0)=0 at hp
      dsimp [radiusSq]
      linear_combination hp
  · refine ⟨0,c 1-b 1,b 0-c 0,0,?_,?_⟩
    · apply Or.inr
      rcases hbc' with hh | hh
      · exact Or.inr (sub_ne_zero.mpr hh)
      · exact Or.inl (sub_ne_zero.mpr hh.symm)
    · intro p hp
      change p 0*(c 1-b 1)-p 1*(c 0-b 0)=0 at hp
      dsimp [radiusSq]
      linear_combination hp

lemma anchors_mem_circleLocus (b c : ℝ²) :
    (0 : ℝ²) ∈ circleLocus b c ∧ b ∈ circleLocus b c ∧ c ∈ circleLocus b c := by
  dsimp [circleLocus,ReggeCircle.circle]
  simp
  constructor <;> ring

def coverFamily (b c : ℝ²) : Fin 4 → Set ℝ² :=
  ![circleLocus b c, lineLocus b c 0, lineLocus b c 1, lineLocus b c 2]

lemma coverFamily_zero (b c : ℝ²) : coverFamily b c 0 = circleLocus b c := rfl
lemma coverFamily_succ (b c : ℝ²) (k : Fin 3) :
    coverFamily b c k.succ = lineLocus b c k := by fin_cases k <;> rfl

/-- There is a common four-set cover even for infinite target sets. Each
non-anchor point may use a completely different special realized edge array. -/
theorem special_fixed_triangle_cover {S : Set ℝ²} {b c : ℝ²}
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h : ∀ p ∈ S, p ≠ 0 → p ≠ b → p ≠ c →
      ∃ e : ReggeMixed.Edges,
        Realizes e (b 0) (b 1) (c 0) (c 1) (p 0) (p 1) ∧ Special e) :
    CoveredBy S 4 := by
  classical
  let F : Finset (Set ℝ²) := Finset.univ.image (coverFamily b c)
  have hmem (i : Fin 4) : coverFamily b c i ∈ F :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  refine ⟨F,?_,?_,?_⟩
  · calc
      F.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by simp
  · intro C hC
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hC
    fin_cases i
    · exact circleLocus_generalized hb hc hbc
    · exact lineLocus_generalized hb hc hbc 0
    · exact lineLocus_generalized hb hc hbc 1
    · exact lineLocus_generalized hb hc hbc 2
  · intro p hp
    have hanchor : p ∈ circleLocus b c → ∃ C ∈ F, p ∈ C := by
      intro hh
      exact ⟨coverFamily b c 0,hmem 0,hh⟩
    by_cases hp0 : p=0
    · exact hanchor (by simpa [hp0] using (anchors_mem_circleLocus b c).1)
    by_cases hpb : p=b
    · exact hanchor (by simpa [hpb] using (anchors_mem_circleLocus b c).2.1)
    by_cases hpc : p=c
    · exact hanchor (by simpa [hpc] using (anchors_mem_circleLocus b c).2.2)
    obtain ⟨e,he,hs⟩ := h p hp hp0 hpb hpc
    rcases circle_or_parallel e (b 0) (b 1) (c 0) (c 1) (p 0) (p 1) he hs with hh | ⟨k,hk⟩
    · exact hanchor hh
    · refine ⟨coverFamily b c k.succ,hmem k.succ,?_⟩
      rw [coverFamily_succ]
      exact hk

/-- The source quadrilateral, its characteristic, the sequence of Regge moves,
vertex relabelings, and its real scale can all vary with the target point. -/
theorem cyclic_orbit_fixed_triangle_cover {S : Set ℝ²} {b c : ℝ²}
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h : ∀ p ∈ S, p ≠ 0 → p ≠ b → p ≠ c →
      ∃ e f : ReggeMixed.Edges, ∃ X Y U V Z W : ℝ,
        Realizes e X Y U V Z W ∧ (∀ i, 0 < e i) ∧
        ReggeCircle.circle X Y U V Z W=0 ∧ Orbit e f ∧
        Realizes f (b 0) (b 1) (c 0) (c 1) (p 0) (p 1)) : CoveredBy S 4 := by
  apply special_fixed_triangle_cover hb hc hbc
  intro p hp hp0 hpb hpc
  obtain ⟨e,f,X,Y,U,V,Z,W,he,hpos,hcircle,horbit,hf⟩ := h p hp hp0 hpb hpc
  exact ⟨f,hf,special_orbit horbit (special_of_circle e X Y U V Z W he hpos hcircle)⟩

/-- A consequence for this construction only; not an unrestricted bound. -/
theorem special_weak_card_le_twelve {S : Finset ℝ²} {b c : ℝ²}
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hS : NoFourGeneralized (S : Set ℝ²))
    (h : ∀ p ∈ S, p ≠ 0 → p ≠ b → p ≠ c →
      ∃ e : ReggeMixed.Edges,
        Realizes e (b 0) (b 1) (c 0) (c 1) (p 0) (p 1) ∧ Special e) : S.card ≤ 12 := by
  have hcov := special_fixed_triangle_cover hb hc hbc h
  simpa using weak_card_le_three_mul_cover hS hcov

/-- The first four vertices of the known heptad have these six edge lengths
before the common scale factor 2227. They are outside the special locus;
the cover hypothesis is not a property of all integral configurations. -/
theorem heptad_edge_control_not_special :
    ¬ Special (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) := by
  rintro ⟨i,hi⟩
  have h0 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 0=22270 := rfl
  have h1 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 1=8636 := rfl
  have h2 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 2=16637 := rfl
  have h3 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 3=13746 := rfl
  have h4 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 4=11397 := rfl
  have h5 : (![22270,8636,16637,13746,11397,11049] : ReggeMixed.Edges) 5=11049 := rfl
  fin_cases i <;> norm_num [form,h0,h1,h2,h3,h4,h5] at hi

#print axioms heptad_edge_control_not_special
#print axioms circleLocus_generalized
#print axioms lineLocus_generalized
#print axioms special_fixed_triangle_cover
#print axioms cyclic_orbit_fixed_triangle_cover
#print axioms special_weak_card_le_twelve
end
end Erdos213.ReggeCover
