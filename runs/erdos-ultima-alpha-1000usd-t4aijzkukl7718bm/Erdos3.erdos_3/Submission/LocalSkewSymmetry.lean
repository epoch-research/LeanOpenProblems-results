import Submission.BiasedSkewDifferences

/-! Extending cross control by local additivity, and intersecting two
Bogolyubov domains, yields uniform approximate symmetry on a common Bohr set. -/
namespace Erdos3LocalSkewSymmetry
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3FiniteFourier
  Erdos3TwistedCorrelationEnergy Erdos3AntidiagonalTwistedEnergy
  Erdos3LocalQuadraticIntegration Erdos3FiniteUniformity
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma local_sub {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxy : x-y ∈ P) :
    F (x-y) = F x-F y := by
  have hh := hF (x-y) hxy y hy (by simpa only [sub_add_cancel] using hx)
  rw [sub_add_cancel] at hh
  exact eq_sub_of_add_eq hh.symm

lemma skewPhase_add_left {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxy : x+y ∈ P) (d : G) :
    skewPhase F (x+y) d = skewPhase F x d*skewPhase F y d := by
  simp only [skewPhase,hF x hx y hy hxy,AddChar.add_apply,AddChar.map_add_eq_mul,map_mul]
  ring

lemma skewPhase_add_right {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    (x : G) {u v : G} (hu : u ∈ P) (hv : v ∈ P) (huv : u+v ∈ P) :
    skewPhase F x (u+v) = skewPhase F x u*skewPhase F x v := by
  simp only [skewPhase,hF u hu v hv huv,AddChar.add_apply,AddChar.map_add_eq_mul,map_mul]
  ring

lemma skewPhase_sub_right_local {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    (x : G) {u v : G} (hu : u ∈ P) (hv : v ∈ P) (huv : u-v ∈ P) :
    skewPhase F x (u-v) = skewPhase F x u*conj (skewPhase F x v) := by
  simp only [skewPhase,local_sub hF hu hv huv,character_sub_apply,char_sub,map_mul,starRingEnd_self_apply]
  ring

lemma norm_skewPhase_error (F : G → AddChar G ℂ) (x y : G) :
    ‖skewPhase F x y-1‖ = ‖F x y-F y x‖ := by
  have he : skewPhase F x y-1 = (F x y-F y x)*conj (F y x) := by
    rw [sub_mul,mul_conj_eq_one (AddChar.norm_apply _ _)]
    rfl
  rw [he,norm_mul,Complex.norm_conj,AddChar.norm_apply,mul_one]

lemma skew_add_error_left {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxy : x+y ∈ P) (d : G) :
    ‖skewPhase F (x+y) d-1‖ ≤ ‖skewPhase F x d-1‖+‖skewPhase F y d-1‖ := by
  rw [skewPhase_add_left hF hx hy hxy]
  exact norm_mul_sub_one_le (skewPhase_norm F x d)

lemma skew_add_error_right {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    (x : G) {u v : G} (hu : u ∈ P) (hv : v ∈ P) (huv : u+v ∈ P) :
    ‖skewPhase F x (u+v)-1‖ ≤ ‖skewPhase F x u-1‖+‖skewPhase F x v-1‖ := by
  rw [skewPhase_add_right hF x hu hv huv]
  exact norm_mul_sub_one_le (skewPhase_norm F x u)

lemma skew_sub_error_right {P : Set G} {F : G → AddChar G ℂ} (hF : LocallyAdditive P F)
    (x : G) {u v : G} (hu : u ∈ P) (hv : v ∈ P) (huv : u-v ∈ P) :
    ‖skewPhase F x (u-v)-1‖ ≤ ‖skewPhase F x u-1‖+‖skewPhase F x v-1‖ := by
  rw [skewPhase_sub_right_local hF x hu hv huv]
  have he : ‖conj (skewPhase F x v)-1‖ = ‖skewPhase F x v-1‖ := by
    simpa only [map_sub,map_one] using Complex.norm_conj (skewPhase F x v-1)
  exact (norm_mul_sub_one_le (skewPhase_norm F x u)).trans_eq (by rw [he])

/-- Fourfold difference membership can be written as a sum of two differences. -/
lemma mem_fourfold_split (X : Finset G) {z : G} (hz : z ∈ (X+X)-(X+X)) :
    ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, ∃ d ∈ X, z = (a-c)+(b-d) := by
  obtain ⟨p,hp,q,hq,rfl⟩ := mem_sub.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hp
  obtain ⟨c,hc,d,hd,rfl⟩ := mem_add.mp hq
  exact ⟨a,ha,b,hb,c,hc,d,hd,by abel⟩

/-- All local-domain conditions are explicit in the algebraic extension step. -/
theorem cross_control_fourfold {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (X D : Finset G)
    (hXdiff : (↑(X-X) : Set G) ⊆ P) (hXfour : (↑((X+X)-(X+X)) : Set G) ⊆ P)
    (hD : (D : Set G) ⊆ P) (hDdiff : (↑(D-D) : Set G) ⊆ P)
    (hDfour : (↑((D+D)-(D+D)) : Set G) ⊆ P)
    {ε : ℝ} (hcross : ∀ s ∈ X, ∀ t ∈ X, ∀ d ∈ D, ‖skewPhase F (s-t) d-1‖ ≤ ε)
    {z w : G} (hz : z ∈ (X+X)-(X+X)) (hw : w ∈ (D+D)-(D+D)) :
    ‖skewPhase F z w-1‖ ≤ 8*ε := by
  have hfirst (d : G) (hd : d ∈ D) : ‖skewPhase F z d-1‖ ≤ 2*ε := by
    obtain ⟨a,ha,b,hb,c,hc,e,he,hzrep⟩ := mem_fourfold_split X hz
    have h1 := hXdiff (sub_mem_sub ha hc)
    have h2 := hXdiff (sub_mem_sub hb he)
    have h3 : (a-c)+(b-e) ∈ P := hzrep ▸ hXfour hz
    rw [hzrep]
    have hh := (skew_add_error_left hF h1 h2 h3 d).trans
      (add_le_add (hcross a ha c hc d hd) (hcross b hb e he d hd))
    simpa only [two_mul] using hh
  have hsecond (u v : G) (hu : u ∈ D) (hv : v ∈ D) :
      ‖skewPhase F z (u-v)-1‖ ≤ 4*ε := by
    have hh := (skew_sub_error_right hF z (hD hu) (hD hv) (hDdiff (sub_mem_sub hu hv))).trans
      (add_le_add (hfirst u hu) (hfirst v hv))
    linarith
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hwrep⟩ := mem_fourfold_split D hw
  have h1 := hDdiff (sub_mem_sub ha hc)
  have h2 := hDdiff (sub_mem_sub hb hd)
  have h3 : (a-c)+(b-d) ∈ P := hwrep ▸ hDfour hw
  rw [hwrep]
  have hh := (skew_add_error_right hF z h1 h2 h3).trans
    (add_le_add (hsecond a c ha hc) (hsecond b d hb hd))
  linarith

lemma add_subset_bohr (B : Finset (AddChar G ℂ)) (A C : Finset G) {r s : ℝ}
    (hA : A ⊆ bohr B r) (hC : C ⊆ bohr B s) : A+C ⊆ bohr B (r+s) := by
  intro x hx
  obtain ⟨a,ha,c,hc,rfl⟩ := mem_add.mp hx
  exact bohr_add (hA ha) (hC hc)

lemma sub_subset_bohr (B : Finset (AddChar G ℂ)) (A C : Finset G) {r s : ℝ}
    (hA : A ⊆ bohr B r) (hC : C ⊆ bohr B s) : A-C ⊆ bohr B (r+s) := by
  intro x hx
  obtain ⟨a,ha,c,hc,rfl⟩ := mem_sub.mp hx
  simpa only [sub_eq_add_neg] using bohr_add (hA ha) (bohr_neg (hC hc))

lemma fourfold_subset_bohr (B : Finset (AddChar G ℂ)) (A : Finset G) {r : ℝ}
    (hA : A ⊆ bohr B r) : (A+A)-(A+A) ⊆ bohr B (4*r) := by
  have hh := sub_subset_bohr B (A+A) (A+A) (add_subset_bohr B A A hA hA) (add_subset_bohr B A A hA hA)
  simpa only [show r+r+(r+r) = 4*r by ring] using hh

/-- A common Bohr domain of approximate symmetry is obtained from cross control.
The deeper 1/16 localization verifies every use of local additivity. -/
theorem cross_control_bohr_symmetry (B : Finset (AddChar G ℂ)) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (bohr B (1/2) : Set G) F)
    (T X D : Finset G) (hT : T ⊆ bohr B (1/16))
    (hX : X.Nonempty) (hD : D.Nonempty) (hXT : X ⊆ T) (hDT : D ⊆ T-T)
    {ε : ℝ} (hcross : ∀ s ∈ X, ∀ t ∈ X, ∀ d ∈ D, ‖skewPhase F (s-t) d-1‖ ≤ ε) :
    ∃ E : Finset (AddChar G ℂ),
      (E.card : ℝ) ≤ 8/(Erdos3FiniteBogolyubov.density X)^2+8/(Erdos3FiniteBogolyubov.density D)^2 ∧
      bohr E (1/2) ⊆ bohr B (1/4) ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ 8*ε := by
  have hXr : X ⊆ bohr B (1/16) := hXT.trans hT
  have hDr : D ⊆ bohr B (1/8) := by
    have hh := hDT.trans (sub_subset_bohr B T T hT hT)
    norm_num only [show (1/16 : ℝ)+1/16 = 1/8 by norm_num] at hh
    exact hh
  have hXdiff : X-X ⊆ bohr B (1/8) := by
    simpa only [show (1/16 : ℝ)+1/16 = 1/8 by norm_num] using sub_subset_bohr B X X hXr hXr
  have hXfour : (X+X)-(X+X) ⊆ bohr B (1/4) := by
    simpa only [show (4 : ℝ)*(1/16) = 1/4 by norm_num] using fourfold_subset_bohr B X hXr
  have hDdiff : D-D ⊆ bohr B (1/4) := by
    simpa only [show (1/8 : ℝ)+1/8 = 1/4 by norm_num] using sub_subset_bohr B D D hDr hDr
  have hDfour : (D+D)-(D+D) ⊆ bohr B (1/2) := by
    simpa only [show (4 : ℝ)*(1/8) = 1/2 by norm_num] using fourfold_subset_bohr B D hDr
  obtain ⟨E₁,hE₁,_,hsub₁⟩ := Erdos3FiniteBogolyubov.bogolyubov X hX
  obtain ⟨E₂,hE₂,_,hsub₂⟩ := Erdos3FiniteBogolyubov.bogolyubov D hD
  let E := E₁ ∪ E₂
  have hto₁ {x : G} (hx : x ∈ bohr E (1/2)) : x ∈ (X+X)-(X+X) := by
    have hx₁ : x ∈ bohr E₁ (1/2) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hx χ (mem_union_left _ hχ))
    simpa only [two_nsmul,mem_sub,mem_add] using hsub₁ hx₁
  have hto₂ {x : G} (hx : x ∈ bohr E (1/2)) : x ∈ (D+D)-(D+D) := by
    have hx₂ : x ∈ bohr E₂ (1/2) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hx χ (mem_union_right _ hχ))
    simpa only [two_nsmul,mem_sub,mem_add] using hsub₂ hx₂
  refine ⟨E,?_,fun _ hx ↦ hXfour (hto₁ hx),?_⟩
  · have hh : (E.card : ℝ) ≤ (E₁.card : ℝ)+(E₂.card : ℝ) := by exact_mod_cast card_union_le E₁ E₂
    exact hh.trans (add_le_add hE₁ hE₂)
  · intro x hx y hy
    rw [← norm_skewPhase_error]
    exact cross_control_fourfold hF X D
      (fun _ hh ↦ bohr_mono B (by norm_num : (1/8 : ℝ) ≤ 1/2) (hXdiff hh))
      (fun _ hh ↦ bohr_mono B (by norm_num : (1/4 : ℝ) ≤ 1/2) (hXfour hh))
      (fun _ hh ↦ bohr_mono B (by norm_num : (1/8 : ℝ) ≤ 1/2) (hDr hh))
      (fun _ hh ↦ bohr_mono B (by norm_num : (1/4 : ℝ) ≤ 1/2) (hDdiff hh))
      hDfour hcross (hto₁ hx) (hto₂ hy)

#print axioms cross_control_fourfold
#print axioms cross_control_bohr_symmetry
end Erdos3LocalSkewSymmetry
