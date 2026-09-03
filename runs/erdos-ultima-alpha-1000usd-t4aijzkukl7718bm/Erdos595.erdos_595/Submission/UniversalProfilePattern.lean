import Submission.UniversalProfileSAT
import Submission.UniversalProfileDefinitions

/-! Kernel-checked realization of the complementary-profile obstruction.
The finite certificate is connected here to actual triangle-free index graphs. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false
open SimpleGraph Set
namespace Erdos595UniversalProfile
open Erdos595FiniteFiberUniversal
universe u
variable {I : Type u} (B : SimpleGraph I) (z : Fin 120 → I × Nine)
  (mark : Fin 2 → Fin 2 → Fin 9 → Prop) (hB : B.CliqueFree 3) (h : Conditions B z mark)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

include hB h in
private theorem c0 : ¬(((z 55).1 = (z 114).1) ∧ (B.Adj (z 55).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c1 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 55).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c2 : ¬(((z 56).1 = (z 114).1) ∧ (B.Adj (z 56).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c3 : ¬(((z 57).1 = (z 115).1) ∧ (B.Adj (z 57).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c4 : ¬(((z 59).1 = (z 114).1) ∧ (B.Adj (z 59).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c5 : ¬(((z 60).1 = (z 68).1) ∧ (B.Adj (z 60).1 (z 68).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c6 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 60).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c7 : ¬(((z 60).1 = (z 119).1) ∧ (B.Adj (z 60).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c8 : ¬(((z 61).1 = (z 68).1) ∧ (B.Adj (z 61).1 (z 68).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c9 : ¬(((z 61).1 = (z 114).1) ∧ (B.Adj (z 61).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c10 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 61).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c11 : ¬(((z 64).1 = (z 116).1) ∧ (B.Adj (z 64).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c12 : ¬(((z 65).1 = (z 116).1) ∧ (B.Adj (z 65).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c13 : ¬(((z 65).1 = (z 118).1) ∧ (B.Adj (z 65).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c14 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c15 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c16 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 68).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c17 : ¬(((z 68).1 = (z 118).1) ∧ (B.Adj (z 68).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c18 : ¬(((z 69).1 = (z 118).1) ∧ (B.Adj (z 69).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c19 : ¬(((z 70).1 = (z 118).1) ∧ (B.Adj (z 70).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c20 : ¬(((z 75).1 = (z 82).1) ∧ (B.Adj (z 75).1 (z 82).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c21 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 75).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c22 : ¬(((z 77).1 = (z 82).1) ∧ (B.Adj (z 77).1 (z 82).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c23 : ¬(((z 78).1 = (z 82).1) ∧ (B.Adj (z 78).1 (z 82).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c24 : ¬(((z 78).1 = (z 86).1) ∧ (B.Adj (z 78).1 (z 86).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c25 : ¬(((z 91).1 = (z 102).1) ∧ (B.Adj (z 91).1 (z 102).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c26 : ¬(((z 91).1 = (z 105).1) ∧ (B.Adj (z 91).1 (z 105).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c27 : ¬(((z 92).1 = (z 105).1) ∧ (B.Adj (z 92).1 (z 105).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c28 : ¬(((z 92).1 = (z 119).1) ∧ (B.Adj (z 92).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c29 : ¬(((z 93).1 = (z 118).1) ∧ (B.Adj (z 93).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c30 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c31 : ¬(((z 95).1 = (z 119).1) ∧ (B.Adj (z 95).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c32 : ¬(((z 97).1 = (z 119).1) ∧ (B.Adj (z 97).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c33 : ¬(((z 105).1 = (z 115).1) ∧ (B.Adj (z 105).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c34 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c35 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c36 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c37 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c38 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2.ne h1

include hB h in
private theorem c39 : ¬(((z 55).1 = (z 66).1) ∧ (B.Adj (z 66).1 (z 73).1) ∧ (¬(B.Adj (z 55).1 (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c40 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 55).1 (z 73).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c41 : ¬(((z 55).1 = (z 114).1) ∧ ((z 82).1 = (z 114).1) ∧ (¬((z 55).1 = (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c42 : ¬(((z 55).1 = (z 82).1) ∧ (B.Adj (z 55).1 (z 115).1) ∧ (¬(B.Adj (z 82).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c43 : ¬(((z 55).1 = (z 82).1) ∧ (B.Adj (z 82).1 (z 118).1) ∧ (¬(B.Adj (z 55).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c44 : ¬(((z 55).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 55).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c45 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 55).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c46 : ¬(((z 55).1 = (z 114).1) ∧ (B.Adj (z 55).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c47 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 55).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c48 : ¬((B.Adj (z 55).1 (z 114).1) ∧ (B.Adj (z 55).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c49 : ¬(((z 55).1 = (z 114).1) ∧ (B.Adj (z 55).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c50 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 55).1 (z 118).1) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c51 : ¬(((z 55).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 55).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c52 : ¬((B.Adj (z 56).1 (z 64).1) ∧ (B.Adj (z 56).1 (z 116).1) ∧ (B.Adj (z 64).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c53 : ¬(((z 56).1 = (z 66).1) ∧ (B.Adj (z 66).1 (z 73).1) ∧ (¬(B.Adj (z 56).1 (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c54 : ¬(((z 56).1 = (z 115).1) ∧ (B.Adj (z 56).1 (z 73).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c55 : ¬(((z 56).1 = (z 114).1) ∧ ((z 83).1 = (z 114).1) ∧ (¬((z 56).1 = (z 83).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c56 : ¬(((z 56).1 = (z 83).1) ∧ (B.Adj (z 56).1 (z 115).1) ∧ (¬(B.Adj (z 83).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c57 : ¬(((z 56).1 = (z 114).1) ∧ (B.Adj (z 87).1 (z 114).1) ∧ (¬(B.Adj (z 56).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c58 : ¬(((z 87).1 = (z 114).1) ∧ (B.Adj (z 56).1 (z 114).1) ∧ (¬(B.Adj (z 56).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c59 : ¬((B.Adj (z 56).1 (z 87).1) ∧ (B.Adj (z 56).1 (z 115).1) ∧ (B.Adj (z 87).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c60 : ¬(((z 56).1 = (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 56).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c61 : ¬(((z 56).1 = (z 115).1) ∧ (B.Adj (z 56).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c62 : ¬((B.Adj (z 56).1 (z 114).1) ∧ (B.Adj (z 56).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c63 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 56).1 (z 114).1) ∧ (¬(B.Adj (z 56).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c64 : ¬((B.Adj (z 56).1 (z 115).1) ∧ (B.Adj (z 56).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c65 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 56).1 (z 115).1) ∧ (¬(B.Adj (z 56).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c66 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 56).1 (z 119).1) ∧ (¬(B.Adj (z 56).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c67 : ¬(((z 57).1 = (z 64).1) ∧ ((z 64).1 = (z 116).1) ∧ (¬((z 57).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c68 : ¬(((z 57).1 = (z 119).1) ∧ (B.Adj (z 57).1 (z 66).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c69 : ¬(((z 57).1 = (z 70).1) ∧ (B.Adj (z 57).1 (z 119).1) ∧ (¬(B.Adj (z 70).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c70 : ¬(((z 57).1 = (z 114).1) ∧ (B.Adj (z 82).1 (z 114).1) ∧ (¬(B.Adj (z 57).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c71 : ¬(((z 57).1 = (z 115).1) ∧ (B.Adj (z 57).1 (z 82).1) ∧ (¬(B.Adj (z 82).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c72 : ¬(((z 57).1 = (z 114).1) ∧ ((z 84).1 = (z 114).1) ∧ (¬((z 57).1 = (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c73 : ¬(((z 57).1 = (z 84).1) ∧ (B.Adj (z 57).1 (z 115).1) ∧ (¬(B.Adj (z 84).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c74 : ¬(((z 57).1 = (z 84).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (¬(B.Adj (z 57).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c75 : ¬(((z 57).1 = (z 115).1) ∧ (B.Adj (z 101).1 (z 115).1) ∧ (¬(B.Adj (z 57).1 (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c76 : ¬(((z 57).1 = (z 119).1) ∧ (B.Adj (z 57).1 (z 101).1) ∧ (¬(B.Adj (z 101).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c77 : ¬(((z 57).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 57).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c78 : ¬(((z 57).1 = (z 114).1) ∧ (B.Adj (z 57).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c79 : ¬(((z 57).1 = (z 115).1) ∧ (B.Adj (z 57).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c80 : ¬((B.Adj (z 57).1 (z 114).1) ∧ (B.Adj (z 57).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c81 : ¬(((z 57).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 57).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c82 : ¬(((z 57).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 57).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c83 : ¬((B.Adj (z 59).1 (z 65).1) ∧ (B.Adj (z 59).1 (z 119).1) ∧ (B.Adj (z 65).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c84 : ¬((B.Adj (z 59).1 (z 66).1) ∧ (B.Adj (z 59).1 (z 114).1) ∧ (B.Adj (z 66).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c85 : ¬((B.Adj (z 59).1 (z 66).1) ∧ (B.Adj (z 59).1 (z 115).1) ∧ (B.Adj (z 66).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c86 : ¬(((z 59).1 = (z 115).1) ∧ (B.Adj (z 79).1 (z 115).1) ∧ (¬(B.Adj (z 59).1 (z 79).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c87 : ¬((B.Adj (z 59).1 (z 79).1) ∧ (B.Adj (z 59).1 (z 117).1) ∧ (B.Adj (z 79).1 (z 117).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c88 : ¬((B.Adj (z 59).1 (z 86).1) ∧ (B.Adj (z 59).1 (z 114).1) ∧ (B.Adj (z 86).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c89 : ¬(((z 86).1 = (z 119).1) ∧ (B.Adj (z 59).1 (z 119).1) ∧ (¬(B.Adj (z 59).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c90 : ¬(((z 88).1 = (z 114).1) ∧ (B.Adj (z 59).1 (z 114).1) ∧ (¬(B.Adj (z 59).1 (z 88).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c91 : ¬(((z 59).1 = (z 115).1) ∧ (B.Adj (z 59).1 (z 88).1) ∧ (¬(B.Adj (z 88).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c92 : ¬(((z 59).1 = (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 59).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c93 : ¬(((z 59).1 = (z 114).1) ∧ (B.Adj (z 59).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c94 : ¬(((z 59).1 = (z 115).1) ∧ (B.Adj (z 59).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c95 : ¬((B.Adj (z 59).1 (z 114).1) ∧ (B.Adj (z 59).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c96 : ¬(((z 59).1 = (z 114).1) ∧ (B.Adj (z 59).1 (z 116).1) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c97 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 59).1 (z 114).1) ∧ (¬(B.Adj (z 59).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c98 : ¬(((z 59).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 117).1) ∧ (¬(B.Adj (z 59).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c99 : ¬((B.Adj (z 59).1 (z 115).1) ∧ (B.Adj (z 59).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c100 : ¬(((z 59).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 59).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c101 : ¬(((z 59).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 59).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c102 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 59).1 (z 115).1) ∧ (¬(B.Adj (z 59).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c103 : ¬(((z 59).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 59).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c104 : ¬((B.Adj (z 60).1 (z 66).1) ∧ (B.Adj (z 60).1 (z 114).1) ∧ (B.Adj (z 66).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c105 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 60).1 (z 66).1) ∧ (¬(B.Adj (z 66).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c106 : ¬((B.Adj (z 60).1 (z 66).1) ∧ (B.Adj (z 60).1 (z 115).1) ∧ (B.Adj (z 66).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c107 : ¬(((z 60).1 = (z 119).1) ∧ (B.Adj (z 68).1 (z 119).1) ∧ (¬(B.Adj (z 60).1 (z 68).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c108 : ¬(((z 60).1 = (z 118).1) ∧ (B.Adj (z 60).1 (z 70).1) ∧ (¬(B.Adj (z 70).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c109 : ¬(((z 60).1 = (z 119).1) ∧ (B.Adj (z 60).1 (z 70).1) ∧ (¬(B.Adj (z 70).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c110 : ¬(((z 60).1 = (z 114).1) ∧ (B.Adj (z 83).1 (z 114).1) ∧ (¬(B.Adj (z 60).1 (z 83).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c111 : ¬(((z 83).1 = (z 114).1) ∧ (B.Adj (z 60).1 (z 114).1) ∧ (¬(B.Adj (z 60).1 (z 83).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c112 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 60).1 (z 83).1) ∧ (¬(B.Adj (z 83).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c113 : ¬(((z 60).1 = (z 105).1) ∧ (B.Adj (z 87).1 (z 105).1) ∧ (¬(B.Adj (z 60).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c114 : ¬(((z 60).1 = (z 114).1) ∧ ((z 87).1 = (z 114).1) ∧ (¬((z 60).1 = (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c115 : ¬(((z 60).1 = (z 114).1) ∧ (B.Adj (z 60).1 (z 87).1) ∧ (¬(B.Adj (z 87).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c116 : ¬((B.Adj (z 60).1 (z 87).1) ∧ (B.Adj (z 60).1 (z 114).1) ∧ (B.Adj (z 87).1 (z 114).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c117 : ¬(((z 60).1 = (z 87).1) ∧ (B.Adj (z 87).1 (z 115).1) ∧ (¬(B.Adj (z 60).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c118 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 87).1 (z 115).1) ∧ (¬(B.Adj (z 60).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c119 : ¬(((z 60).1 = (z 115).1) ∧ ((z 105).1 = (z 115).1) ∧ (¬((z 60).1 = (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c120 : ¬(((z 60).1 = (z 114).1) ∧ (B.Adj (z 60).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c121 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 60).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c122 : ¬((B.Adj (z 60).1 (z 114).1) ∧ (B.Adj (z 60).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c123 : ¬(((z 60).1 = (z 114).1) ∧ ((z 114).1 = (z 118).1) ∧ (¬((z 60).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c124 : ¬(((z 60).1 = (z 119).1) ∧ (B.Adj (z 60).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c125 : ¬(((z 60).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 60).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c126 : ¬(((z 60).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 60).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c127 : ¬(((z 61).1 = (z 65).1) ∧ (B.Adj (z 65).1 (z 119).1) ∧ (¬(B.Adj (z 61).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c128 : ¬(((z 61).1 = (z 66).1) ∧ (B.Adj (z 66).1 (z 73).1) ∧ (¬(B.Adj (z 61).1 (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c129 : ¬(((z 61).1 = (z 66).1) ∧ (B.Adj (z 61).1 (z 75).1) ∧ (¬(B.Adj (z 66).1 (z 75).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c130 : ¬(((z 61).1 = (z 66).1) ∧ (B.Adj (z 66).1 (z 114).1) ∧ (¬(B.Adj (z 61).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c131 : ¬(((z 61).1 = (z 68).1) ∧ ((z 68).1 = (z 95).1) ∧ (¬((z 61).1 = (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c132 : ¬(((z 61).1 = (z 95).1) ∧ (B.Adj (z 68).1 (z 95).1) ∧ (¬(B.Adj (z 61).1 (z 68).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c133 : ¬(((z 61).1 = (z 68).1) ∧ ((z 68).1 = (z 116).1) ∧ (¬((z 61).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c134 : ¬((B.Adj (z 61).1 (z 70).1) ∧ (B.Adj (z 61).1 (z 116).1) ∧ (B.Adj (z 70).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c135 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 61).1 (z 73).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c136 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 75).1 (z 115).1) ∧ (¬(B.Adj (z 61).1 (z 75).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c137 : ¬(((z 61).1 = (z 114).1) ∧ (B.Adj (z 86).1 (z 114).1) ∧ (¬(B.Adj (z 61).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c138 : ¬(((z 86).1 = (z 114).1) ∧ (B.Adj (z 61).1 (z 114).1) ∧ (¬(B.Adj (z 61).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c139 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 61).1 (z 86).1) ∧ (¬(B.Adj (z 86).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c140 : ¬(((z 61).1 = (z 95).1) ∧ (B.Adj (z 95).1 (z 115).1) ∧ (¬(B.Adj (z 61).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c141 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 61).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c142 : ¬(((z 61).1 = (z 114).1) ∧ (B.Adj (z 61).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c143 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 61).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c144 : ¬((B.Adj (z 61).1 (z 114).1) ∧ (B.Adj (z 61).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c145 : ¬(((z 61).1 = (z 119).1) ∧ (B.Adj (z 61).1 (z 114).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c146 : ¬(((z 61).1 = (z 116).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 61).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c147 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 61).1 (z 115).1) ∧ (¬(B.Adj (z 61).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c148 : ¬(((z 61).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 61).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c149 : ¬(((z 61).1 = (z 115).1) ∧ (B.Adj (z 61).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c150 : ¬(((z 64).1 = (z 73).1) ∧ ((z 73).1 = (z 84).1) ∧ (¬((z 64).1 = (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c151 : ¬(((z 64).1 = (z 116).1) ∧ ((z 73).1 = (z 116).1) ∧ (¬((z 64).1 = (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c152 : ¬(((z 64).1 = (z 84).1) ∧ (B.Adj (z 84).1 (z 91).1) ∧ (¬(B.Adj (z 64).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c153 : ¬(((z 64).1 = (z 91).1) ∧ (B.Adj (z 84).1 (z 91).1) ∧ (¬(B.Adj (z 64).1 (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c154 : ¬(((z 84).1 = (z 116).1) ∧ (B.Adj (z 64).1 (z 84).1) ∧ (¬(B.Adj (z 64).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c155 : ¬(((z 64).1 = (z 91).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 64).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c156 : ¬(((z 64).1 = (z 116).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 64).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c157 : ¬(((z 64).1 = (z 91).1) ∧ (B.Adj (z 64).1 (z 116).1) ∧ (¬(B.Adj (z 91).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c158 : ¬(((z 64).1 = (z 118).1) ∧ ((z 91).1 = (z 118).1) ∧ (¬((z 64).1 = (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c159 : ¬((B.Adj (z 64).1 (z 91).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (B.Adj (z 91).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c160 : ¬(((z 64).1 = (z 91).1) ∧ ((z 91).1 = (z 119).1) ∧ (¬((z 64).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c161 : ¬(((z 64).1 = (z 91).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (¬(B.Adj (z 64).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c162 : ¬(((z 91).1 = (z 119).1) ∧ (B.Adj (z 64).1 (z 119).1) ∧ (¬(B.Adj (z 64).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c163 : ¬(((z 64).1 = (z 116).1) ∧ (B.Adj (z 64).1 (z 93).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c164 : ¬(((z 64).1 = (z 118).1) ∧ (B.Adj (z 93).1 (z 118).1) ∧ (¬(B.Adj (z 64).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c165 : ¬(((z 93).1 = (z 118).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (¬(B.Adj (z 64).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c166 : ¬((B.Adj (z 64).1 (z 93).1) ∧ (B.Adj (z 64).1 (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c167 : ¬(((z 64).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 64).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c168 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 64).1 (z 116).1) ∧ (¬(B.Adj (z 64).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c169 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (¬(B.Adj (z 64).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c170 : ¬((B.Adj (z 64).1 (z 115).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c171 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 64).1 (z 115).1) ∧ (¬(B.Adj (z 64).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c172 : ¬(((z 64).1 = (z 116).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c173 : ¬(((z 64).1 = (z 118).1) ∧ (B.Adj (z 64).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c174 : ¬((B.Adj (z 64).1 (z 116).1) ∧ (B.Adj (z 64).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c175 : ¬(((z 64).1 = (z 119).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 64).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c176 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 64).1 (z 116).1) ∧ (¬(B.Adj (z 64).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c177 : ¬((B.Adj (z 64).1 (z 116).1) ∧ (B.Adj (z 64).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c178 : ¬(((z 65).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 65).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c179 : ¬(((z 65).1 = (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 65).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c180 : ¬(((z 65).1 = (z 116).1) ∧ (B.Adj (z 65).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c181 : ¬(((z 65).1 = (z 118).1) ∧ (B.Adj (z 65).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c182 : ¬((B.Adj (z 65).1 (z 116).1) ∧ (B.Adj (z 65).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c183 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 65).1 (z 116).1) ∧ (¬(B.Adj (z 65).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c184 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 73).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c185 : ¬(((z 73).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 73).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c186 : ¬(((z 73).1 = (z 119).1) ∧ (B.Adj (z 66).1 (z 73).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c187 : ¬(((z 66).1 = (z 75).1) ∧ (B.Adj (z 75).1 (z 115).1) ∧ (¬(B.Adj (z 66).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c188 : ¬(((z 66).1 = (z 116).1) ∧ ((z 75).1 = (z 116).1) ∧ (¬((z 66).1 = (z 75).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c189 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 75).1) ∧ (¬(B.Adj (z 66).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c190 : ¬(((z 66).1 = (z 75).1) ∧ ((z 75).1 = (z 119).1) ∧ (¬((z 66).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c191 : ¬(((z 66).1 = (z 114).1) ∧ ((z 82).1 = (z 114).1) ∧ (¬((z 66).1 = (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c192 : ¬(((z 82).1 = (z 114).1) ∧ (B.Adj (z 66).1 (z 82).1) ∧ (¬(B.Adj (z 66).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c193 : ¬(((z 66).1 = (z 82).1) ∧ ((z 82).1 = (z 119).1) ∧ (¬((z 66).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c194 : ¬(((z 66).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c195 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 91).1) ∧ (¬(B.Adj (z 91).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c196 : ¬((B.Adj (z 66).1 (z 91).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (B.Adj (z 91).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c197 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 91).1 (z 118).1) ∧ (¬(B.Adj (z 66).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c198 : ¬(((z 91).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (¬(B.Adj (z 66).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c199 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 92).1 (z 118).1) ∧ (¬(B.Adj (z 66).1 (z 92).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c200 : ¬(((z 92).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (¬(B.Adj (z 66).1 (z 92).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c201 : ¬((B.Adj (z 66).1 (z 92).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (B.Adj (z 92).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c202 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 93).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c203 : ¬(((z 93).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c204 : ¬((B.Adj (z 66).1 (z 93).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (B.Adj (z 93).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c205 : ¬(((z 66).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c206 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c207 : ¬(((z 66).1 = (z 118).1) ∧ ((z 96).1 = (z 118).1) ∧ (¬((z 66).1 = (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c208 : ¬(((z 66).1 = (z 96).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c209 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c210 : ¬(((z 66).1 = (z 118).1) ∧ ((z 114).1 = (z 118).1) ∧ (¬((z 66).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c211 : ¬(((z 114).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 114).1) ∧ (¬(B.Adj (z 66).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c212 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c213 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (¬(B.Adj (z 66).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c214 : ¬((B.Adj (z 66).1 (z 115).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c215 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c216 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 66).1 (z 115).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c217 : ¬((B.Adj (z 66).1 (z 115).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c218 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c219 : ¬((B.Adj (z 66).1 (z 116).1) ∧ (B.Adj (z 66).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c220 : ¬(((z 66).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 66).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c221 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c222 : ¬(((z 66).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c223 : ¬(((z 66).1 = (z 116).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c224 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 66).1 (z 116).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c225 : ¬((B.Adj (z 66).1 (z 116).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c226 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 118).1 (z 119).1) ∧ (¬(B.Adj (z 66).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c227 : ¬(((z 66).1 = (z 118).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c228 : ¬((B.Adj (z 66).1 (z 118).1) ∧ (B.Adj (z 66).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c229 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 95).1 (z 116).1) ∧ (¬(B.Adj (z 68).1 (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c230 : ¬(((z 68).1 = (z 118).1) ∧ ((z 95).1 = (z 118).1) ∧ (¬((z 68).1 = (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c231 : ¬((B.Adj (z 68).1 (z 95).1) ∧ (B.Adj (z 68).1 (z 118).1) ∧ (B.Adj (z 95).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c232 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 68).1 (z 97).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c233 : ¬(((z 68).1 = (z 118).1) ∧ (B.Adj (z 97).1 (z 118).1) ∧ (¬(B.Adj (z 68).1 (z 97).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c234 : ¬((B.Adj (z 68).1 (z 115).1) ∧ (B.Adj (z 68).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c235 : ¬(((z 68).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 68).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c236 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 68).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c237 : ¬(((z 68).1 = (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 68).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c238 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 68).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c239 : ¬(((z 68).1 = (z 118).1) ∧ (B.Adj (z 68).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c240 : ¬((B.Adj (z 68).1 (z 116).1) ∧ (B.Adj (z 68).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c241 : ¬(((z 68).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 68).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c242 : ¬(((z 69).1 = (z 116).1) ∧ (B.Adj (z 69).1 (z 92).1) ∧ (¬(B.Adj (z 92).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c243 : ¬(((z 69).1 = (z 118).1) ∧ (B.Adj (z 92).1 (z 118).1) ∧ (¬(B.Adj (z 69).1 (z 92).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c244 : ¬(((z 69).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 69).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c245 : ¬(((z 69).1 = (z 116).1) ∧ (B.Adj (z 69).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c246 : ¬(((z 69).1 = (z 118).1) ∧ (B.Adj (z 69).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c247 : ¬((B.Adj (z 69).1 (z 116).1) ∧ (B.Adj (z 69).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c248 : ¬(((z 70).1 = (z 116).1) ∧ (B.Adj (z 70).1 (z 95).1) ∧ (¬(B.Adj (z 95).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c249 : ¬((B.Adj (z 70).1 (z 95).1) ∧ (B.Adj (z 70).1 (z 116).1) ∧ (B.Adj (z 95).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c250 : ¬(((z 70).1 = (z 118).1) ∧ (B.Adj (z 95).1 (z 118).1) ∧ (¬(B.Adj (z 70).1 (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c251 : ¬(((z 95).1 = (z 118).1) ∧ (B.Adj (z 70).1 (z 118).1) ∧ (¬(B.Adj (z 70).1 (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c252 : ¬(((z 70).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 70).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c253 : ¬(((z 70).1 = (z 116).1) ∧ (B.Adj (z 70).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c254 : ¬(((z 70).1 = (z 118).1) ∧ (B.Adj (z 70).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c255 : ¬((B.Adj (z 70).1 (z 116).1) ∧ (B.Adj (z 70).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c256 : ¬((B.Adj (z 70).1 (z 116).1) ∧ (B.Adj (z 70).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c257 : ¬(((z 73).1 = (z 117).1) ∧ (B.Adj (z 73).1 (z 82).1) ∧ (¬(B.Adj (z 82).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c258 : ¬((B.Adj (z 73).1 (z 82).1) ∧ (B.Adj (z 73).1 (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c259 : ¬((B.Adj (z 73).1 (z 83).1) ∧ (B.Adj (z 73).1 (z 119).1) ∧ (B.Adj (z 83).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c260 : ¬(((z 73).1 = (z 84).1) ∧ ((z 84).1 = (z 119).1) ∧ (¬((z 73).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c261 : ¬(((z 73).1 = (z 86).1) ∧ (B.Adj (z 86).1 (z 91).1) ∧ (¬(B.Adj (z 73).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c262 : ¬(((z 73).1 = (z 87).1) ∧ (B.Adj (z 87).1 (z 115).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c263 : ¬((B.Adj (z 73).1 (z 88).1) ∧ (B.Adj (z 73).1 (z 119).1) ∧ (B.Adj (z 88).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c264 : ¬((B.Adj (z 73).1 (z 91).1) ∧ (B.Adj (z 73).1 (z 116).1) ∧ (B.Adj (z 91).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c265 : ¬(((z 73).1 = (z 105).1) ∧ (B.Adj (z 73).1 (z 115).1) ∧ (¬(B.Adj (z 105).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c266 : ¬(((z 73).1 = (z 116).1) ∧ ((z 105).1 = (z 116).1) ∧ (¬((z 73).1 = (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c267 : ¬(((z 73).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c268 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 73).1 (z 116).1) ∧ (¬(B.Adj (z 73).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c269 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 73).1 (z 115).1) ∧ (¬(B.Adj (z 73).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c270 : ¬(((z 73).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 73).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c271 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 73).1 (z 116).1) ∧ (¬(B.Adj (z 73).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c272 : ¬((B.Adj (z 74).1 (z 82).1) ∧ (B.Adj (z 74).1 (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c273 : ¬(((z 74).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 74).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c274 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 74).1 (z 116).1) ∧ (¬(B.Adj (z 74).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c275 : ¬((B.Adj (z 75).1 (z 77).1) ∧ (B.Adj (z 75).1 (z 84).1) ∧ (B.Adj (z 77).1 (z 84).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c276 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 77).1 (z 116).1) ∧ (¬(B.Adj (z 75).1 (z 77).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c277 : ¬(((z 75).1 = (z 82).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (¬(B.Adj (z 75).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c278 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 82).1 (z 116).1) ∧ (¬(B.Adj (z 75).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c279 : ¬(((z 75).1 = (z 83).1) ∧ (B.Adj (z 83).1 (z 114).1) ∧ (¬(B.Adj (z 75).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c280 : ¬(((z 75).1 = (z 83).1) ∧ (B.Adj (z 75).1 (z 116).1) ∧ (¬(B.Adj (z 83).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c281 : ¬(((z 75).1 = (z 83).1) ∧ ((z 83).1 = (z 119).1) ∧ (¬((z 75).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c282 : ¬(((z 75).1 = (z 83).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 75).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c283 : ¬(((z 75).1 = (z 83).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (¬(B.Adj (z 83).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c284 : ¬((B.Adj (z 75).1 (z 84).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c285 : ¬((B.Adj (z 75).1 (z 86).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c286 : ¬((B.Adj (z 75).1 (z 87).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (B.Adj (z 87).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c287 : ¬(((z 75).1 = (z 88).1) ∧ ((z 88).1 = (z 119).1) ∧ (¬((z 75).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c288 : ¬(((z 75).1 = (z 88).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 75).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c289 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 75).1 (z 114).1) ∧ (¬(B.Adj (z 75).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c290 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 75).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c291 : ¬(((z 75).1 = (z 116).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c292 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 75).1 (z 116).1) ∧ (¬(B.Adj (z 75).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c293 : ¬((B.Adj (z 75).1 (z 116).1) ∧ (B.Adj (z 75).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c294 : ¬(((z 77).1 = (z 82).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 77).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c295 : ¬(((z 77).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 77).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c296 : ¬((B.Adj (z 77).1 (z 84).1) ∧ (B.Adj (z 77).1 (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c297 : ¬(((z 77).1 = (z 87).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (¬(B.Adj (z 77).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c298 : ¬(((z 77).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 77).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c299 : ¬((B.Adj (z 77).1 (z 116).1) ∧ (B.Adj (z 77).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c300 : ¬(((z 78).1 = (z 82).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 78).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c301 : ¬(((z 78).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 78).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c302 : ¬(((z 78).1 = (z 115).1) ∧ (B.Adj (z 78).1 (z 84).1) ∧ (¬(B.Adj (z 84).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c303 : ¬((B.Adj (z 78).1 (z 84).1) ∧ (B.Adj (z 78).1 (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c304 : ¬(((z 78).1 = (z 86).1) ∧ (B.Adj (z 86).1 (z 96).1) ∧ (¬(B.Adj (z 78).1 (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c305 : ¬(((z 78).1 = (z 115).1) ∧ (B.Adj (z 86).1 (z 115).1) ∧ (¬(B.Adj (z 78).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c306 : ¬(((z 78).1 = (z 86).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 78).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c307 : ¬(((z 78).1 = (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 78).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c308 : ¬(((z 78).1 = (z 96).1) ∧ (B.Adj (z 78).1 (z 87).1) ∧ (¬(B.Adj (z 87).1 (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c309 : ¬(((z 78).1 = (z 115).1) ∧ (B.Adj (z 78).1 (z 88).1) ∧ (¬(B.Adj (z 88).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c310 : ¬((B.Adj (z 78).1 (z 88).1) ∧ (B.Adj (z 78).1 (z 119).1) ∧ (B.Adj (z 88).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c311 : ¬(((z 78).1 = (z 116).1) ∧ ((z 96).1 = (z 116).1) ∧ (¬((z 78).1 = (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c312 : ¬(((z 78).1 = (z 116).1) ∧ (B.Adj (z 78).1 (z 96).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c313 : ¬(((z 78).1 = (z 116).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 78).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c314 : ¬(((z 78).1 = (z 115).1) ∧ (B.Adj (z 78).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c315 : ¬(((z 78).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 78).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c316 : ¬(((z 78).1 = (z 116).1) ∧ (B.Adj (z 78).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c317 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 78).1 (z 116).1) ∧ (¬(B.Adj (z 78).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c318 : ¬((B.Adj (z 78).1 (z 116).1) ∧ (B.Adj (z 78).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c319 : ¬((B.Adj (z 79).1 (z 82).1) ∧ (B.Adj (z 79).1 (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c320 : ¬(((z 79).1 = (z 84).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (¬(B.Adj (z 79).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c321 : ¬((B.Adj (z 79).1 (z 88).1) ∧ (B.Adj (z 79).1 (z 119).1) ∧ (B.Adj (z 88).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c322 : ¬(((z 79).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 79).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c323 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 79).1 (z 116).1) ∧ (¬(B.Adj (z 79).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c324 : ¬(((z 79).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 79).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c325 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 79).1 (z 116).1) ∧ (¬(B.Adj (z 79).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c326 : ¬((B.Adj (z 79).1 (z 116).1) ∧ (B.Adj (z 79).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c327 : ¬(((z 91).1 = (z 114).1) ∧ (B.Adj (z 82).1 (z 114).1) ∧ (¬(B.Adj (z 82).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c328 : ¬((B.Adj (z 82).1 (z 91).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (B.Adj (z 91).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c329 : ¬(((z 96).1 = (z 118).1) ∧ (B.Adj (z 82).1 (z 96).1) ∧ (¬(B.Adj (z 82).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c330 : ¬(((z 96).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 82).1 (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c331 : ¬(((z 100).1 = (z 115).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (¬(B.Adj (z 82).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c332 : ¬(((z 100).1 = (z 115).1) ∧ (B.Adj (z 82).1 (z 100).1) ∧ (¬(B.Adj (z 82).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c333 : ¬((B.Adj (z 82).1 (z 100).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (B.Adj (z 100).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c334 : ¬(((z 100).1 = (z 116).1) ∧ (B.Adj (z 82).1 (z 100).1) ∧ (¬(B.Adj (z 82).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c335 : ¬(((z 100).1 = (z 117).1) ∧ (B.Adj (z 82).1 (z 117).1) ∧ (¬(B.Adj (z 82).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c336 : ¬(((z 100).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 82).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c337 : ¬(((z 82).1 = (z 114).1) ∧ ((z 114).1 = (z 115).1) ∧ (¬((z 82).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c338 : ¬(((z 82).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 82).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c339 : ¬(((z 82).1 = (z 114).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c340 : ¬((B.Adj (z 82).1 (z 114).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c341 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 82).1 (z 114).1) ∧ (¬(B.Adj (z 82).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c342 : ¬((B.Adj (z 82).1 (z 114).1) ∧ (B.Adj (z 82).1 (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c343 : ¬((B.Adj (z 82).1 (z 114).1) ∧ (B.Adj (z 82).1 (z 118).1) ∧ (B.Adj (z 114).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c344 : ¬((B.Adj (z 82).1 (z 114).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c345 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 82).1 (z 115).1) ∧ (¬(B.Adj (z 82).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c346 : ¬(((z 82).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 82).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c347 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 82).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c348 : ¬((B.Adj (z 82).1 (z 115).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c349 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (¬(B.Adj (z 82).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c350 : ¬((B.Adj (z 82).1 (z 116).1) ∧ (B.Adj (z 82).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c351 : ¬(((z 83).1 = (z 114).1) ∧ ((z 93).1 = (z 114).1) ∧ (¬((z 83).1 = (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c352 : ¬(((z 93).1 = (z 114).1) ∧ (B.Adj (z 83).1 (z 93).1) ∧ (¬(B.Adj (z 83).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c353 : ¬(((z 83).1 = (z 93).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c354 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 83).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c355 : ¬(((z 83).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 83).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c356 : ¬(((z 83).1 = (z 114).1) ∧ (B.Adj (z 83).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c357 : ¬((B.Adj (z 83).1 (z 114).1) ∧ (B.Adj (z 83).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c358 : ¬((B.Adj (z 83).1 (z 114).1) ∧ (B.Adj (z 83).1 (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c359 : ¬(((z 83).1 = (z 114).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c360 : ¬((B.Adj (z 83).1 (z 114).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c361 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 83).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c362 : ¬(((z 83).1 = (z 119).1) ∧ (B.Adj (z 83).1 (z 115).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c363 : ¬((B.Adj (z 83).1 (z 115).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c364 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (¬(B.Adj (z 83).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c365 : ¬((B.Adj (z 83).1 (z 116).1) ∧ (B.Adj (z 83).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c366 : ¬(((z 91).1 = (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (¬(B.Adj (z 84).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c367 : ¬(((z 93).1 = (z 114).1) ∧ (B.Adj (z 84).1 (z 114).1) ∧ (¬(B.Adj (z 84).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c368 : ¬((B.Adj (z 84).1 (z 93).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c369 : ¬(((z 95).1 = (z 114).1) ∧ (B.Adj (z 84).1 (z 114).1) ∧ (¬(B.Adj (z 84).1 (z 95).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c370 : ¬((B.Adj (z 84).1 (z 95).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (B.Adj (z 95).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c371 : ¬(((z 84).1 = (z 100).1) ∧ (B.Adj (z 100).1 (z 115).1) ∧ (¬(B.Adj (z 84).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c372 : ¬(((z 84).1 = (z 119).1) ∧ ((z 100).1 = (z 119).1) ∧ (¬((z 84).1 = (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c373 : ¬(((z 84).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 84).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c374 : ¬(((z 84).1 = (z 114).1) ∧ (B.Adj (z 84).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c375 : ¬(((z 84).1 = (z 114).1) ∧ ((z 114).1 = (z 116).1) ∧ (¬((z 84).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c376 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 84).1 (z 114).1) ∧ (¬(B.Adj (z 84).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c377 : ¬((B.Adj (z 84).1 (z 114).1) ∧ (B.Adj (z 84).1 (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c378 : ¬((B.Adj (z 84).1 (z 114).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c379 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (¬(B.Adj (z 84).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c380 : ¬((B.Adj (z 84).1 (z 115).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c381 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (¬(B.Adj (z 84).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c382 : ¬((B.Adj (z 84).1 (z 116).1) ∧ (B.Adj (z 84).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c383 : ¬(((z 91).1 = (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 86).1 (z 91).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c384 : ¬(((z 96).1 = (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 86).1 (z 96).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c385 : ¬(((z 86).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 86).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c386 : ¬(((z 86).1 = (z 114).1) ∧ (B.Adj (z 86).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c387 : ¬((B.Adj (z 86).1 (z 114).1) ∧ (B.Adj (z 86).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c388 : ¬(((z 86).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 116).1) ∧ (¬(B.Adj (z 86).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c389 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 86).1 (z 114).1) ∧ (¬(B.Adj (z 86).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c390 : ¬((B.Adj (z 86).1 (z 114).1) ∧ (B.Adj (z 86).1 (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c391 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 86).1 (z 116).1) ∧ (¬(B.Adj (z 86).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c392 : ¬(((z 86).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 86).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c393 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 86).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c394 : ¬((B.Adj (z 86).1 (z 115).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c395 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 86).1 (z 119).1) ∧ (¬(B.Adj (z 86).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c396 : ¬(((z 92).1 = (z 105).1) ∧ (B.Adj (z 87).1 (z 92).1) ∧ (¬(B.Adj (z 87).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c397 : ¬(((z 92).1 = (z 119).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (¬(B.Adj (z 87).1 (z 92).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c398 : ¬(((z 93).1 = (z 114).1) ∧ (B.Adj (z 87).1 (z 114).1) ∧ (¬(B.Adj (z 87).1 (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c399 : ¬((B.Adj (z 87).1 (z 93).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c400 : ¬((B.Adj (z 87).1 (z 96).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (B.Adj (z 96).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c401 : ¬(((z 87).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 87).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c402 : ¬(((z 114).1 = (z 115).1) ∧ (B.Adj (z 87).1 (z 114).1) ∧ (¬(B.Adj (z 87).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c403 : ¬((B.Adj (z 87).1 (z 114).1) ∧ (B.Adj (z 87).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c404 : ¬((B.Adj (z 87).1 (z 114).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c405 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (¬(B.Adj (z 87).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c406 : ¬((B.Adj (z 87).1 (z 115).1) ∧ (B.Adj (z 87).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c407 : ¬(((z 88).1 = (z 114).1) ∧ ((z 93).1 = (z 114).1) ∧ (¬((z 88).1 = (z 93).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c408 : ¬(((z 88).1 = (z 93).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c409 : ¬(((z 88).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 88).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c410 : ¬(((z 88).1 = (z 114).1) ∧ (B.Adj (z 88).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c411 : ¬(((z 88).1 = (z 114).1) ∧ ((z 114).1 = (z 116).1) ∧ (¬((z 88).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c412 : ¬((B.Adj (z 88).1 (z 114).1) ∧ (B.Adj (z 88).1 (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c413 : ¬(((z 88).1 = (z 114).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c414 : ¬((B.Adj (z 88).1 (z 114).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c415 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 88).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c416 : ¬((B.Adj (z 88).1 (z 115).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c417 : ¬(((z 88).1 = (z 116).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c418 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (¬(B.Adj (z 88).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c419 : ¬((B.Adj (z 88).1 (z 116).1) ∧ (B.Adj (z 88).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c420 : ¬(((z 92).1 = (z 118).1) ∧ (B.Adj (z 91).1 (z 118).1) ∧ (¬(B.Adj (z 91).1 (z 92).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c421 : ¬((B.Adj (z 91).1 (z 92).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 92).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c422 : ¬((B.Adj (z 91).1 (z 100).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 100).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c423 : ¬(((z 91).1 = (z 116).1) ∧ (B.Adj (z 91).1 (z 101).1) ∧ (¬(B.Adj (z 101).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c424 : ¬(((z 91).1 = (z 119).1) ∧ (B.Adj (z 91).1 (z 101).1) ∧ (¬(B.Adj (z 101).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c425 : ¬((B.Adj (z 91).1 (z 101).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 101).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c426 : ¬(((z 91).1 = (z 102).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 102).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c427 : ¬(((z 102).1 = (z 116).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 91).1 (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c428 : ¬(((z 91).1 = (z 105).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 105).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c429 : ¬(((z 105).1 = (z 116).1) ∧ (B.Adj (z 91).1 (z 116).1) ∧ (¬(B.Adj (z 91).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c430 : ¬(((z 91).1 = (z 105).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (¬(B.Adj (z 105).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c431 : ¬(((z 91).1 = (z 118).1) ∧ ((z 114).1 = (z 118).1) ∧ (¬((z 91).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c432 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 91).1 (z 118).1) ∧ (¬(B.Adj (z 91).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c433 : ¬((B.Adj (z 91).1 (z 115).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c434 : ¬(((z 91).1 = (z 119).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 91).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c435 : ¬(((z 91).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 91).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c436 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (¬(B.Adj (z 91).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c437 : ¬((B.Adj (z 91).1 (z 116).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c438 : ¬((B.Adj (z 91).1 (z 118).1) ∧ (B.Adj (z 91).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c439 : ¬((B.Adj (z 92).1 (z 100).1) ∧ (B.Adj (z 92).1 (z 104).1) ∧ (B.Adj (z 100).1 (z 104).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c440 : ¬((B.Adj (z 92).1 (z 100).1) ∧ (B.Adj (z 92).1 (z 118).1) ∧ (B.Adj (z 100).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c441 : ¬((B.Adj (z 92).1 (z 100).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (B.Adj (z 100).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c442 : ¬((B.Adj (z 92).1 (z 101).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (B.Adj (z 101).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c443 : ¬(((z 92).1 = (z 102).1) ∧ ((z 102).1 = (z 116).1) ∧ (¬((z 92).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c444 : ¬(((z 92).1 = (z 102).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (¬(B.Adj (z 102).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c445 : ¬(((z 104).1 = (z 116).1) ∧ (B.Adj (z 92).1 (z 104).1) ∧ (¬(B.Adj (z 92).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c446 : ¬((B.Adj (z 92).1 (z 104).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (B.Adj (z 104).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c447 : ¬(((z 92).1 = (z 105).1) ∧ ((z 105).1 = (z 116).1) ∧ (¬((z 92).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c448 : ¬(((z 92).1 = (z 105).1) ∧ (B.Adj (z 92).1 (z 116).1) ∧ (¬(B.Adj (z 105).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c449 : ¬(((z 92).1 = (z 105).1) ∧ (B.Adj (z 105).1 (z 119).1) ∧ (¬(B.Adj (z 92).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c450 : ¬(((z 92).1 = (z 119).1) ∧ (B.Adj (z 105).1 (z 119).1) ∧ (¬(B.Adj (z 92).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c451 : ¬(((z 92).1 = (z 106).1) ∧ ((z 106).1 = (z 119).1) ∧ (¬((z 92).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c452 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 92).1 (z 115).1) ∧ (¬(B.Adj (z 92).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c453 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (¬(B.Adj (z 92).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c454 : ¬((B.Adj (z 92).1 (z 116).1) ∧ (B.Adj (z 92).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c455 : ¬(((z 92).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 92).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c456 : ¬(((z 92).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 92).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c457 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (¬(B.Adj (z 92).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c458 : ¬((B.Adj (z 92).1 (z 116).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c459 : ¬(((z 92).1 = (z 118).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c460 : ¬(((z 92).1 = (z 119).1) ∧ (B.Adj (z 92).1 (z 118).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c461 : ¬((B.Adj (z 92).1 (z 118).1) ∧ (B.Adj (z 92).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c462 : ¬(((z 93).1 = (z 100).1) ∧ ((z 100).1 = (z 116).1) ∧ (¬((z 93).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c463 : ¬(((z 93).1 = (z 100).1) ∧ (B.Adj (z 93).1 (z 116).1) ∧ (¬(B.Adj (z 100).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c464 : ¬(((z 93).1 = (z 101).1) ∧ ((z 101).1 = (z 119).1) ∧ (¬((z 93).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c465 : ¬(((z 93).1 = (z 101).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 101).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c466 : ¬((B.Adj (z 93).1 (z 102).1) ∧ (B.Adj (z 93).1 (z 105).1) ∧ (B.Adj (z 102).1 (z 105).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c467 : ¬(((z 102).1 = (z 115).1) ∧ (B.Adj (z 93).1 (z 102).1) ∧ (¬(B.Adj (z 93).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c468 : ¬(((z 102).1 = (z 116).1) ∧ (B.Adj (z 93).1 (z 102).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c469 : ¬((B.Adj (z 93).1 (z 102).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (B.Adj (z 102).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c470 : ¬((B.Adj (z 93).1 (z 104).1) ∧ (B.Adj (z 93).1 (z 115).1) ∧ (B.Adj (z 104).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c471 : ¬((B.Adj (z 93).1 (z 104).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (B.Adj (z 104).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c472 : ¬((B.Adj (z 93).1 (z 105).1) ∧ (B.Adj (z 93).1 (z 115).1) ∧ (B.Adj (z 105).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c473 : ¬(((z 93).1 = (z 106).1) ∧ ((z 106).1 = (z 119).1) ∧ (¬((z 93).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c474 : ¬(((z 93).1 = (z 118).1) ∧ ((z 114).1 = (z 118).1) ∧ (¬((z 93).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c475 : ¬(((z 93).1 = (z 114).1) ∧ (B.Adj (z 114).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c476 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 93).1 (z 115).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c477 : ¬(((z 93).1 = (z 118).1) ∧ ((z 115).1 = (z 118).1) ∧ (¬((z 93).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c478 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 93).1 (z 118).1) ∧ (¬(B.Adj (z 93).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c479 : ¬(((z 93).1 = (z 118).1) ∧ (B.Adj (z 93).1 (z 115).1) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c480 : ¬((B.Adj (z 93).1 (z 115).1) ∧ (B.Adj (z 93).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c481 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c482 : ¬(((z 93).1 = (z 115).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c483 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c484 : ¬((B.Adj (z 93).1 (z 115).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c485 : ¬(((z 93).1 = (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c486 : ¬(((z 93).1 = (z 119).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 93).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c487 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c488 : ¬(((z 93).1 = (z 116).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c489 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c490 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c491 : ¬((B.Adj (z 93).1 (z 116).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c492 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1) ∧ (¬(B.Adj (z 93).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c493 : ¬(((z 93).1 = (z 118).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c494 : ¬(((z 93).1 = (z 119).1) ∧ (B.Adj (z 93).1 (z 118).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c495 : ¬((B.Adj (z 93).1 (z 118).1) ∧ (B.Adj (z 93).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c496 : ¬(((z 95).1 = (z 100).1) ∧ ((z 100).1 = (z 116).1) ∧ (¬((z 95).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c497 : ¬(((z 95).1 = (z 100).1) ∧ (B.Adj (z 95).1 (z 116).1) ∧ (¬(B.Adj (z 100).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c498 : ¬(((z 95).1 = (z 100).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (¬(B.Adj (z 100).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c499 : ¬((B.Adj (z 95).1 (z 101).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (B.Adj (z 101).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c500 : ¬((B.Adj (z 95).1 (z 102).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (B.Adj (z 102).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c501 : ¬(((z 95).1 = (z 105).1) ∧ (B.Adj (z 95).1 (z 116).1) ∧ (¬(B.Adj (z 105).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c502 : ¬(((z 95).1 = (z 118).1) ∧ ((z 114).1 = (z 118).1) ∧ (¬((z 95).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c503 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 95).1 (z 115).1) ∧ (¬(B.Adj (z 95).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c504 : ¬((B.Adj (z 95).1 (z 115).1) ∧ (B.Adj (z 95).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c505 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 95).1 (z 118).1) ∧ (¬(B.Adj (z 95).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c506 : ¬((B.Adj (z 95).1 (z 115).1) ∧ (B.Adj (z 95).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c507 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (¬(B.Adj (z 95).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c508 : ¬(((z 95).1 = (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 95).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c509 : ¬(((z 95).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 95).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c510 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (¬(B.Adj (z 95).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c511 : ¬((B.Adj (z 95).1 (z 116).1) ∧ (B.Adj (z 95).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c512 : ¬(((z 96).1 = (z 100).1) ∧ ((z 100).1 = (z 116).1) ∧ (¬((z 96).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c513 : ¬(((z 96).1 = (z 100).1) ∧ (B.Adj (z 96).1 (z 116).1) ∧ (¬(B.Adj (z 100).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c514 : ¬(((z 96).1 = (z 101).1) ∧ (B.Adj (z 101).1 (z 115).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c515 : ¬(((z 96).1 = (z 101).1) ∧ (B.Adj (z 96).1 (z 116).1) ∧ (¬(B.Adj (z 101).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c516 : ¬(((z 102).1 = (z 116).1) ∧ (B.Adj (z 96).1 (z 102).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c517 : ¬(((z 96).1 = (z 104).1) ∧ ((z 104).1 = (z 115).1) ∧ (¬((z 96).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c518 : ¬(((z 96).1 = (z 104).1) ∧ (B.Adj (z 104).1 (z 115).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c519 : ¬(((z 96).1 = (z 104).1) ∧ ((z 104).1 = (z 116).1) ∧ (¬((z 96).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c520 : ¬(((z 96).1 = (z 104).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 104).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c521 : ¬(((z 105).1 = (z 115).1) ∧ (B.Adj (z 96).1 (z 105).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c522 : ¬((B.Adj (z 96).1 (z 105).1) ∧ (B.Adj (z 96).1 (z 115).1) ∧ (B.Adj (z 105).1 (z 115).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c523 : ¬(((z 105).1 = (z 116).1) ∧ (B.Adj (z 96).1 (z 105).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c524 : ¬(((z 106).1 = (z 116).1) ∧ (B.Adj (z 96).1 (z 106).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c525 : ¬((B.Adj (z 96).1 (z 106).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (B.Adj (z 106).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c526 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 96).1 (z 115).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c527 : ¬(((z 96).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c528 : ¬(((z 96).1 = (z 115).1) ∧ (B.Adj (z 96).1 (z 118).1) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c529 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 96).1 (z 118).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c530 : ¬((B.Adj (z 96).1 (z 115).1) ∧ (B.Adj (z 96).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c531 : ¬(((z 96).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c532 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 96).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c533 : ¬(((z 96).1 = (z 119).1) ∧ (B.Adj (z 96).1 (z 115).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c534 : ¬((B.Adj (z 96).1 (z 115).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c535 : ¬(((z 96).1 = (z 118).1) ∧ (B.Adj (z 96).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c536 : ¬((B.Adj (z 96).1 (z 116).1) ∧ (B.Adj (z 96).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c537 : ¬(((z 96).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c538 : ¬(((z 96).1 = (z 116).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c539 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 96).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c540 : ¬((B.Adj (z 96).1 (z 116).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c541 : ¬(((z 96).1 = (z 118).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c542 : ¬((B.Adj (z 96).1 (z 118).1) ∧ (B.Adj (z 96).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c543 : ¬(((z 100).1 = (z 116).1) ∧ (B.Adj (z 97).1 (z 100).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c544 : ¬((B.Adj (z 97).1 (z 100).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (B.Adj (z 100).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c545 : ¬(((z 97).1 = (z 102).1) ∧ ((z 102).1 = (z 115).1) ∧ (¬((z 97).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c546 : ¬((B.Adj (z 97).1 (z 105).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (B.Adj (z 105).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c547 : ¬(((z 106).1 = (z 116).1) ∧ (B.Adj (z 97).1 (z 106).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c548 : ¬((B.Adj (z 97).1 (z 106).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (B.Adj (z 106).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c549 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 97).1 (z 115).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c550 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 97).1 (z 118).1) ∧ (¬(B.Adj (z 97).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c551 : ¬(((z 97).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 97).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c552 : ¬(((z 97).1 = (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c553 : ¬(((z 97).1 = (z 118).1) ∧ (B.Adj (z 97).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c554 : ¬((B.Adj (z 97).1 (z 116).1) ∧ (B.Adj (z 97).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c555 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (¬(B.Adj (z 97).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c556 : ¬((B.Adj (z 97).1 (z 116).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c557 : ¬((B.Adj (z 97).1 (z 118).1) ∧ (B.Adj (z 97).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c558 : ¬(((z 104).1 = (z 115).1) ∧ (B.Adj (z 100).1 (z 115).1) ∧ (¬(B.Adj (z 100).1 (z 104).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c559 : ¬(((z 100).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 100).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c560 : ¬(((z 100).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 100).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c561 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 100).1 (z 115).1) ∧ (¬(B.Adj (z 100).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c562 : ¬((B.Adj (z 100).1 (z 115).1) ∧ (B.Adj (z 100).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c563 : ¬(((z 100).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 100).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c564 : ¬(((z 100).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 100).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c565 : ¬(((z 100).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 100).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c566 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 100).1 (z 115).1) ∧ (¬(B.Adj (z 100).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c567 : ¬((B.Adj (z 100).1 (z 115).1) ∧ (B.Adj (z 100).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c568 : ¬(((z 100).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 100).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c569 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 100).1 (z 116).1) ∧ (¬(B.Adj (z 100).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c570 : ¬(((z 100).1 = (z 117).1) ∧ ((z 117).1 = (z 119).1) ∧ (¬((z 100).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c571 : ¬(((z 101).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 101).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c572 : ¬(((z 101).1 = (z 115).1) ∧ (B.Adj (z 101).1 (z 116).1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c573 : ¬((B.Adj (z 101).1 (z 115).1) ∧ (B.Adj (z 101).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c574 : ¬(((z 101).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 101).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c575 : ¬(((z 101).1 = (z 115).1) ∧ (B.Adj (z 101).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c576 : ¬(((z 101).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 101).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c577 : ¬(((z 105).1 = (z 115).1) ∧ (B.Adj (z 102).1 (z 115).1) ∧ (¬(B.Adj (z 102).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c578 : ¬(((z 102).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 102).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c579 : ¬((B.Adj (z 102).1 (z 115).1) ∧ (B.Adj (z 102).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c580 : ¬(((z 102).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 102).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c581 : ¬((B.Adj (z 102).1 (z 115).1) ∧ (B.Adj (z 102).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c582 : ¬(((z 102).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 102).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c583 : ¬(((z 104).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 104).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c584 : ¬((B.Adj (z 104).1 (z 115).1) ∧ (B.Adj (z 104).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c585 : ¬(((z 104).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 104).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c586 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 104).1 (z 115).1) ∧ (¬(B.Adj (z 104).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c587 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 104).1 (z 119).1) ∧ (¬(B.Adj (z 104).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c588 : ¬(((z 105).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 105).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c589 : ¬(((z 105).1 = (z 115).1) ∧ (B.Adj (z 105).1 (z 116).1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c590 : ¬((B.Adj (z 105).1 (z 115).1) ∧ (B.Adj (z 105).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c591 : ¬(((z 105).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 105).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c592 : ¬(((z 106).1 = (z 115).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 106).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c593 : ¬(((z 106).1 = (z 115).1) ∧ ((z 115).1 = (z 119).1) ∧ (¬((z 106).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c594 : ¬(((z 106).1 = (z 115).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 106).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c595 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 106).1 (z 115).1) ∧ (¬(B.Adj (z 106).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c596 : ¬(((z 106).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 106).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c597 : ¬(((z 114).1 = (z 116).1) ∧ ((z 115).1 = (z 116).1) ∧ (¬((z 114).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c598 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c599 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 114).1 (z 116).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c600 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c601 : ¬(((z 114).1 = (z 118).1) ∧ ((z 115).1 = (z 118).1) ∧ (¬((z 114).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c602 : ¬(((z 114).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c603 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 114).1 (z 118).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c604 : ¬(((z 114).1 = (z 118).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c605 : ¬((B.Adj (z 114).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c606 : ¬(((z 114).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c607 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 114).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c608 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 114).1 (z 115).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c609 : ¬((B.Adj (z 114).1 (z 115).1) ∧ (B.Adj (z 114).1 (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c610 : ¬(((z 114).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 114).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c611 : ¬(((z 114).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c612 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 114).1 (z 116).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c613 : ¬((B.Adj (z 114).1 (z 117).1) ∧ (B.Adj (z 114).1 (z 118).1) ∧ (B.Adj (z 117).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c614 : ¬(((z 114).1 = (z 118).1) ∧ (B.Adj (z 118).1 (z 119).1) ∧ (¬(B.Adj (z 114).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c615 : ¬((B.Adj (z 114).1 (z 118).1) ∧ (B.Adj (z 114).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c616 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c617 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c618 : ¬((B.Adj (z 115).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 118).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c619 : ¬(((z 115).1 = (z 116).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2))

include hB h in
private theorem c620 : ¬(((z 115).1 = (z 119).1) ∧ ((z 116).1 = (z 119).1) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 ((h1).trans (h2.symm))

include hB h in
private theorem c621 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c622 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c623 : ¬(((z 115).1 = (z 116).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c624 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h2)

include hB h in
private theorem c625 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c626 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 116).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2)

include hB h in
private theorem c627 : ¬((B.Adj (z 115).1 (z 116).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (B.Adj (z 116).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c628 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 118).1 (z 119).1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2)

include hB h in
private theorem c629 : ¬(((z 115).1 = (z 118).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c630 : ¬(((z 115).1 = (z 119).1) ∧ (B.Adj (z 115).1 (z 118).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c631 : ¬((B.Adj (z 115).1 (z 118).1) ∧ (B.Adj (z 115).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c632 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1) ∧ (¬(B.Adj (z 116).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)

include hB h in
private theorem c633 : ¬(((z 116).1 = (z 119).1) ∧ (B.Adj (z 116).1 (z 118).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h2.symm)

include hB h in
private theorem c634 : ¬((B.Adj (z 116).1 (z 118).1) ∧ (B.Adj (z 116).1 (z 119).1) ∧ (B.Adj (z 118).1 (z 119).1)) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)

include hB h in
private theorem c635 : ¬(((z 117).1 = (z 118).1) ∧ (B.Adj (z 117).1 (z 119).1) ∧ (¬(B.Adj (z 118).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)

include hB h in
private theorem c636 : ¬((¬((z 108).2 = coord 0)) ∧ (¬((z 108).2 = coord 1)) ∧ (¬((z 108).2 = coord 2)) ∧ (¬((z 108).2 = coord 3)) ∧ (¬((z 108).2 = coord 4)) ∧ (¬((z 108).2 = coord 5)) ∧ (¬((z 108).2 = coord 6)) ∧ (¬((z 108).2 = coord 7)) ∧ (¬((z 108).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 108).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c637 : ¬(((z 108).2 = coord 1) ∧ (¬(mark 0 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 1 h1)

include hB h in
private theorem c638 : ¬(((z 108).2 = coord 1) ∧ (¬(mark 0 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 1 h1)

include hB h in
private theorem c639 : ¬(((z 108).2 = coord 2) ∧ (¬(mark 0 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 2 h1)

include hB h in
private theorem c640 : ¬(((z 108).2 = coord 2) ∧ (¬(mark 0 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 2 h1)

include hB h in
private theorem c641 : ¬(((z 108).2 = coord 3) ∧ (¬(mark 0 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 3 h1)

include hB h in
private theorem c642 : ¬(((z 108).2 = coord 3) ∧ (¬(mark 0 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 3 h1)

include hB h in
private theorem c643 : ¬(((z 108).2 = coord 4) ∧ (¬(mark 0 0 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 4 h1)

include hB h in
private theorem c644 : ¬(((z 108).2 = coord 5) ∧ (¬(mark 0 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 5 h1)

include hB h in
private theorem c645 : ¬(((z 108).2 = coord 5) ∧ (¬(mark 0 0 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 5 h1)

include hB h in
private theorem c646 : ¬(((z 108).2 = coord 6) ∧ (¬(mark 0 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 6 h1)

include hB h in
private theorem c647 : ¬(((z 108).2 = coord 6) ∧ (¬(mark 0 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 6 h1)

include hB h in
private theorem c648 : ¬(((z 108).2 = coord 7) ∧ (¬(mark 0 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 0 7 h1)

include hB h in
private theorem c649 : ¬(((z 108).2 = coord 7) ∧ (¬(mark 0 0 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 7 h1)

include hB h in
private theorem c650 : ¬(((z 108).2 = coord 8) ∧ (¬(mark 0 0 8))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 0 8 h1)

include hB h in
private theorem c651 : ¬((¬((z 110).2 = coord 0)) ∧ (¬((z 110).2 = coord 1)) ∧ (¬((z 110).2 = coord 2)) ∧ (¬((z 110).2 = coord 3)) ∧ (¬((z 110).2 = coord 4)) ∧ (¬((z 110).2 = coord 5)) ∧ (¬((z 110).2 = coord 6)) ∧ (¬((z 110).2 = coord 7)) ∧ (¬((z 110).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 110).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c652 : ¬(((z 110).2 = coord 2) ∧ (¬(mark 0 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 2 2 h1)

include hB h in
private theorem c653 : ¬(((z 110).2 = coord 5) ∧ (¬(mark 0 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 2 5 h1)

include hB h in
private theorem c654 : ¬(((z 110).2 = coord 6) ∧ (¬(mark 0 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 2 6 h1)

include hB h in
private theorem c655 : ¬(((z 110).2 = coord 7) ∧ (¬(mark 0 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 2 7 h1)

include hB h in
private theorem c656 : ¬((¬((z 114).2 = coord 0)) ∧ (¬((z 114).2 = coord 1)) ∧ (¬((z 114).2 = coord 2)) ∧ (¬((z 114).2 = coord 3)) ∧ (¬((z 114).2 = coord 4)) ∧ (¬((z 114).2 = coord 5)) ∧ (¬((z 114).2 = coord 6)) ∧ (¬((z 114).2 = coord 7)) ∧ (¬((z 114).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 114).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c657 : ¬(((z 114).2 = coord 1) ∧ (¬(mark 0 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 1 h1)

include hB h in
private theorem c658 : ¬(((z 114).2 = coord 1) ∧ (¬(mark 1 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 6 1 h1)

include hB h in
private theorem c659 : ¬(((z 114).2 = coord 2) ∧ (¬(mark 0 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 2 h1)

include hB h in
private theorem c660 : ¬(((z 114).2 = coord 2) ∧ (¬(mark 1 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 6 2 h1)

include hB h in
private theorem c661 : ¬(((z 114).2 = coord 3) ∧ (¬(mark 0 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 3 h1)

include hB h in
private theorem c662 : ¬(((z 114).2 = coord 3) ∧ (¬(mark 1 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 6 3 h1)

include hB h in
private theorem c663 : ¬(((z 114).2 = coord 4) ∧ (¬(mark 0 1 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 4 h1)

include hB h in
private theorem c664 : ¬(((z 114).2 = coord 4) ∧ (¬(mark 1 0 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 6 4 h1)

include hB h in
private theorem c665 : ¬(((z 114).2 = coord 5) ∧ (¬(mark 0 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 5 h1)

include hB h in
private theorem c666 : ¬(((z 114).2 = coord 6) ∧ (¬(mark 0 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 6 h1)

include hB h in
private theorem c667 : ¬(((z 114).2 = coord 6) ∧ (¬(mark 1 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 6 6 h1)

include hB h in
private theorem c668 : ¬(((z 114).2 = coord 7) ∧ (¬(mark 0 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 6 7 h1)

include hB h in
private theorem c669 : ¬((¬((z 115).2 = coord 0)) ∧ (¬((z 115).2 = coord 1)) ∧ (¬((z 115).2 = coord 2)) ∧ (¬((z 115).2 = coord 3)) ∧ (¬((z 115).2 = coord 4)) ∧ (¬((z 115).2 = coord 5)) ∧ (¬((z 115).2 = coord 6)) ∧ (¬((z 115).2 = coord 7)) ∧ (¬((z 115).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 115).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c670 : ¬(((z 115).2 = coord 0) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (0 : Fin 9) ≠ 5) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c671 : ¬(((z 115).2 = coord 1) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (1 : Fin 9) ≠ 5) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c672 : ¬(((z 115).2 = coord 1) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (1 : Fin 9) ≠ 8) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c673 : ¬(((z 115).2 = coord 2) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (2 : Fin 9) ≠ 5) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c674 : ¬(((z 115).2 = coord 4) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (4 : Fin 9) ≠ 5) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c675 : ¬(((z 115).2 = coord 5) ∧ ((z 115).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (5 : Fin 9) ≠ 7) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c676 : ¬(((z 115).2 = coord 0) ∧ (¬(mark 0 1 0))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 0 h1)

include hB h in
private theorem c677 : ¬(((z 115).2 = coord 1) ∧ (¬(mark 0 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 1 h1)

include hB h in
private theorem c678 : ¬(((z 115).2 = coord 1) ∧ (¬(mark 1 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 1 h1)

include hB h in
private theorem c679 : ¬(((z 115).2 = coord 2) ∧ (¬(mark 0 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 2 h1)

include hB h in
private theorem c680 : ¬(((z 115).2 = coord 2) ∧ (¬(mark 1 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 2 h1)

include hB h in
private theorem c681 : ¬(((z 115).2 = coord 3) ∧ (¬(mark 0 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 3 h1)

include hB h in
private theorem c682 : ¬(((z 115).2 = coord 3) ∧ (¬(mark 1 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 3 h1)

include hB h in
private theorem c683 : ¬(((z 115).2 = coord 4) ∧ (¬(mark 0 1 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 4 h1)

include hB h in
private theorem c684 : ¬(((z 115).2 = coord 4) ∧ (¬(mark 1 0 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 4 h1)

include hB h in
private theorem c685 : ¬(((z 115).2 = coord 5) ∧ (¬(mark 0 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 5 h1)

include hB h in
private theorem c686 : ¬(((z 115).2 = coord 5) ∧ (¬(mark 1 0 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 5 h1)

include hB h in
private theorem c687 : ¬(((z 115).2 = coord 6) ∧ (¬(mark 0 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 6 h1)

include hB h in
private theorem c688 : ¬(((z 115).2 = coord 6) ∧ (¬(mark 1 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 6 h1)

include hB h in
private theorem c689 : ¬(((z 115).2 = coord 7) ∧ (¬(mark 0 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 7 h1)

include hB h in
private theorem c690 : ¬(((z 115).2 = coord 7) ∧ (¬(mark 1 0 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 7 7 h1)

include hB h in
private theorem c691 : ¬(((z 115).2 = coord 8) ∧ (¬(mark 0 1 8))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 7 8 h1)

include hB h in
private theorem c692 : ¬((¬((z 116).2 = coord 0)) ∧ (¬((z 116).2 = coord 1)) ∧ (¬((z 116).2 = coord 2)) ∧ (¬((z 116).2 = coord 3)) ∧ (¬((z 116).2 = coord 4)) ∧ (¬((z 116).2 = coord 5)) ∧ (¬((z 116).2 = coord 6)) ∧ (¬((z 116).2 = coord 7)) ∧ (¬((z 116).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 116).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c693 : ¬(((z 116).2 = coord 1) ∧ ((z 116).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (1 : Fin 9) ≠ 2) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c694 : ¬(((z 116).2 = coord 2) ∧ ((z 116).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (2 : Fin 9) ≠ 5) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c695 : ¬(((z 116).2 = coord 2) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (2 : Fin 9) ≠ 6) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c696 : ¬(((z 116).2 = coord 3) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (3 : Fin 9) ≠ 6) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c697 : ¬(((z 116).2 = coord 0) ∧ (¬(mark 1 1 0))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 0 h1)

include hB h in
private theorem c698 : ¬(((z 116).2 = coord 0) ∧ (¬(mark 0 0 0))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 0 h1)

include hB h in
private theorem c699 : ¬(((z 116).2 = coord 1) ∧ (¬(mark 1 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 1 h1)

include hB h in
private theorem c700 : ¬(((z 116).2 = coord 1) ∧ (¬(mark 0 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 1 h1)

include hB h in
private theorem c701 : ¬(((z 116).2 = coord 2) ∧ (¬(mark 1 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 2 h1)

include hB h in
private theorem c702 : ¬(((z 116).2 = coord 2) ∧ (¬(mark 0 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 2 h1)

include hB h in
private theorem c703 : ¬(((z 116).2 = coord 3) ∧ (¬(mark 1 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 3 h1)

include hB h in
private theorem c704 : ¬(((z 116).2 = coord 3) ∧ (¬(mark 0 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 3 h1)

include hB h in
private theorem c705 : ¬(((z 116).2 = coord 4) ∧ (¬(mark 1 1 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 4 h1)

include hB h in
private theorem c706 : ¬(((z 116).2 = coord 4) ∧ (¬(mark 0 0 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 4 h1)

include hB h in
private theorem c707 : ¬(((z 116).2 = coord 5) ∧ (¬(mark 1 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 5 h1)

include hB h in
private theorem c708 : ¬(((z 116).2 = coord 5) ∧ (¬(mark 0 0 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 5 h1)

include hB h in
private theorem c709 : ¬(((z 116).2 = coord 6) ∧ (¬(mark 1 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 6 h1)

include hB h in
private theorem c710 : ¬(((z 116).2 = coord 6) ∧ (¬(mark 0 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 6 h1)

include hB h in
private theorem c711 : ¬(((z 116).2 = coord 7) ∧ (¬(mark 1 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 8 7 h1)

include hB h in
private theorem c712 : ¬(((z 116).2 = coord 7) ∧ (¬(mark 0 0 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 7 h1)

include hB h in
private theorem c713 : ¬(((z 116).2 = coord 8) ∧ (¬(mark 0 0 8))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 8 8 h1)

include hB h in
private theorem c714 : ¬((¬((z 117).2 = coord 0)) ∧ (¬((z 117).2 = coord 1)) ∧ (¬((z 117).2 = coord 2)) ∧ (¬((z 117).2 = coord 3)) ∧ (¬((z 117).2 = coord 4)) ∧ (¬((z 117).2 = coord 5)) ∧ (¬((z 117).2 = coord 6)) ∧ (¬((z 117).2 = coord 7)) ∧ (¬((z 117).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 117).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c715 : ¬(((z 117).2 = coord 2) ∧ (¬(mark 1 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 9 2 h1)

include hB h in
private theorem c716 : ¬(((z 117).2 = coord 3) ∧ (¬(mark 1 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 9 3 h1)

include hB h in
private theorem c717 : ¬(((z 117).2 = coord 5) ∧ (¬(mark 1 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 9 5 h1)

include hB h in
private theorem c718 : ¬(((z 117).2 = coord 6) ∧ (¬(mark 1 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 9 6 h1)

include hB h in
private theorem c719 : ¬((¬((z 118).2 = coord 0)) ∧ (¬((z 118).2 = coord 1)) ∧ (¬((z 118).2 = coord 2)) ∧ (¬((z 118).2 = coord 3)) ∧ (¬((z 118).2 = coord 4)) ∧ (¬((z 118).2 = coord 5)) ∧ (¬((z 118).2 = coord 6)) ∧ (¬((z 118).2 = coord 7)) ∧ (¬((z 118).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 118).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c720 : ¬(((z 118).2 = coord 0) ∧ (¬(mark 1 1 0))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 0 h1)

include hB h in
private theorem c721 : ¬(((z 118).2 = coord 1) ∧ (¬(mark 1 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 1 h1)

include hB h in
private theorem c722 : ¬(((z 118).2 = coord 1) ∧ (¬(mark 0 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 1 h1)

include hB h in
private theorem c723 : ¬(((z 118).2 = coord 2) ∧ (¬(mark 1 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 2 h1)

include hB h in
private theorem c724 : ¬(((z 118).2 = coord 2) ∧ (¬(mark 0 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 2 h1)

include hB h in
private theorem c725 : ¬(((z 118).2 = coord 3) ∧ (¬(mark 1 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 3 h1)

include hB h in
private theorem c726 : ¬(((z 118).2 = coord 3) ∧ (¬(mark 0 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 3 h1)

include hB h in
private theorem c727 : ¬(((z 118).2 = coord 4) ∧ (¬(mark 1 1 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 4 h1)

include hB h in
private theorem c728 : ¬(((z 118).2 = coord 5) ∧ (¬(mark 1 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 5 h1)

include hB h in
private theorem c729 : ¬(((z 118).2 = coord 5) ∧ (¬(mark 0 0 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 5 h1)

include hB h in
private theorem c730 : ¬(((z 118).2 = coord 6) ∧ (¬(mark 1 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 6 h1)

include hB h in
private theorem c731 : ¬(((z 118).2 = coord 6) ∧ (¬(mark 0 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 6 h1)

include hB h in
private theorem c732 : ¬(((z 118).2 = coord 7) ∧ (¬(mark 1 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 10 7 h1)

include hB h in
private theorem c733 : ¬(((z 118).2 = coord 7) ∧ (¬(mark 0 0 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 7 h1)

include hB h in
private theorem c734 : ¬(((z 118).2 = coord 8) ∧ (¬(mark 0 0 8))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 10 8 h1)

include hB h in
private theorem c735 : ¬((¬((z 119).2 = coord 0)) ∧ (¬((z 119).2 = coord 1)) ∧ (¬((z 119).2 = coord 2)) ∧ (¬((z 119).2 = coord 3)) ∧ (¬((z 119).2 = coord 4)) ∧ (¬((z 119).2 = coord 5)) ∧ (¬((z 119).2 = coord 6)) ∧ (¬((z 119).2 = coord 7)) ∧ (¬((z 119).2 = coord 8))) := by
  classical
  rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  obtain ⟨c,hc⟩ := coord_surjective (z 119).2
  fin_cases c
  · exact h1 hc.symm
  · exact h2 hc.symm
  · exact h3 hc.symm
  · exact h4 hc.symm
  · exact h5 hc.symm
  · exact h6 hc.symm
  · exact h7 hc.symm
  · exact h8 hc.symm
  · exact h9 hc.symm

include hB h in
private theorem c736 : ¬(((z 119).2 = coord 2) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (2 : Fin 9) ≠ 3) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c737 : ¬(((z 119).2 = coord 2) ∧ ((z 119).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (2 : Fin 9) ≠ 7) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c738 : ¬(((z 119).2 = coord 3) ∧ ((z 119).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  exact (by decide : (3 : Fin 9) ≠ 7) (coord_injective (h1.symm.trans h2))

include hB h in
private theorem c739 : ¬(((z 119).2 = coord 0) ∧ (¬(mark 1 1 0))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 0 h1)

include hB h in
private theorem c740 : ¬(((z 119).2 = coord 1) ∧ (¬(mark 1 1 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 1 h1)

include hB h in
private theorem c741 : ¬(((z 119).2 = coord 1) ∧ (¬(mark 1 0 1))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 1 h1)

include hB h in
private theorem c742 : ¬(((z 119).2 = coord 2) ∧ (¬(mark 1 1 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 2 h1)

include hB h in
private theorem c743 : ¬(((z 119).2 = coord 2) ∧ (¬(mark 1 0 2))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 2 h1)

include hB h in
private theorem c744 : ¬(((z 119).2 = coord 3) ∧ (¬(mark 1 1 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 3 h1)

include hB h in
private theorem c745 : ¬(((z 119).2 = coord 3) ∧ (¬(mark 1 0 3))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 3 h1)

include hB h in
private theorem c746 : ¬(((z 119).2 = coord 4) ∧ (¬(mark 1 1 4))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 4 h1)

include hB h in
private theorem c747 : ¬(((z 119).2 = coord 5) ∧ (¬(mark 1 1 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 5 h1)

include hB h in
private theorem c748 : ¬(((z 119).2 = coord 5) ∧ (¬(mark 1 0 5))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 5 h1)

include hB h in
private theorem c749 : ¬(((z 119).2 = coord 6) ∧ (¬(mark 1 1 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 6 h1)

include hB h in
private theorem c750 : ¬(((z 119).2 = coord 6) ∧ (¬(mark 1 0 6))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 6 h1)

include hB h in
private theorem c751 : ¬(((z 119).2 = coord 7) ∧ (¬(mark 1 1 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 7 h1)

include hB h in
private theorem c752 : ¬(((z 119).2 = coord 7) ∧ (¬(mark 1 0 7))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_target 11 7 h1)

include hB h in
private theorem c753 : ¬(((z 119).2 = coord 8) ∧ (¬(mark 1 1 8))) := by
  classical
  rintro ⟨h1,h2⟩
  exact h2 (h.witness_source 11 8 h1)

include hB h in
private theorem c754 : ¬(((z 108).2 = coord 0) ∧ (mark 0 0 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 0 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 0) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c755 : ¬(((z 108).2 = coord 1) ∧ (mark 0 0 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 0 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 0) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c756 : ¬(((z 108).2 = coord 2) ∧ (mark 0 0 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 0 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 0) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c757 : ¬(((z 108).2 = coord 3) ∧ (mark 0 0 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 0 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 0) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c758 : ¬(((z 108).2 = coord 6) ∧ (mark 0 0 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 0 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 0) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c759 : ¬(((z 108).2 = coord 0) ∧ (mark 0 0 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 1 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 1) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c760 : ¬((mark 0 0 1) ∧ ((z 108).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 1 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 1) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c761 : ¬(((z 108).2 = coord 0) ∧ (mark 0 0 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 2 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 2) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c762 : ¬(((z 108).2 = coord 0) ∧ (mark 0 0 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 3 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 3) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c763 : ¬((mark 0 0 3) ∧ ((z 108).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 3 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 3) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c764 : ¬(((z 108).2 = coord 1) ∧ (mark 0 0 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 4 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 4) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c765 : ¬(((z 108).2 = coord 3) ∧ (mark 0 0 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 4 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 4) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c766 : ¬((mark 0 0 4) ∧ ((z 108).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 4 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c767 : ¬((mark 0 0 4) ∧ ((z 108).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 4 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c768 : ¬((mark 0 0 4) ∧ ((z 108).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 4 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c769 : ¬((mark 0 0 6) ∧ ((z 108).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 6 108 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 0 0 6) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c770 : ¬(((z 108).2 = coord 2) ∧ (mark 0 0 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 8 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 8) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c771 : ¬(((z 108).2 = coord 5) ∧ (mark 0 0 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 8 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 8) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c772 : ¬(((z 108).2 = coord 6) ∧ (mark 0 0 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 8 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 8) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c773 : ¬(((z 108).2 = coord 7) ∧ (mark 0 0 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 8 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 8) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c774 : ¬(((z 108).2 = coord 8) ∧ (mark 0 0 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 8 108 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 0 0 8) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c775 : ¬(((z 110).2 = coord 1) ∧ (mark 0 1 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 110 13 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 0 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c776 : ¬((mark 0 1 4) ∧ ((z 110).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 110 13 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 0 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c777 : ¬((mark 0 1 4) ∧ ((z 110).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 0 110 13 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 0 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c778 : ¬((mark 0 0 6) ∧ ((z 110).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 24 110 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 1 0 6) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c779 : ¬((mark 0 0 6) ∧ ((z 110).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 24 110 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 1 0 6) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c780 : ¬(((z 108).2 = coord 0) ∧ (mark 0 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 27 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c781 : ¬(((z 108).2 = coord 1) ∧ (mark 0 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 27 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c782 : ¬(((z 108).2 = coord 2) ∧ (mark 0 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 27 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c783 : ¬(((z 108).2 = coord 3) ∧ (mark 0 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 27 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c784 : ¬(((z 108).2 = coord 6) ∧ (mark 0 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 27 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c785 : ¬(((z 108).2 = coord 0) ∧ (mark 0 1 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 28 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c786 : ¬((mark 0 1 1) ∧ ((z 108).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 28 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c787 : ¬(((z 108).2 = coord 0) ∧ (mark 0 1 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 29 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 2) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c788 : ¬((mark 0 1 3) ∧ ((z 108).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 30 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c789 : ¬((mark 0 1 3) ∧ ((z 108).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 30 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c790 : ¬(((z 108).2 = coord 1) ∧ (mark 0 1 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 31 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c791 : ¬(((z 108).2 = coord 3) ∧ (mark 0 1 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 31 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c792 : ¬((mark 0 1 4) ∧ ((z 108).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 31 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c793 : ¬((mark 0 1 4) ∧ ((z 108).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 31 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c794 : ¬((mark 0 1 6) ∧ ((z 108).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 33 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c795 : ¬(((z 108).2 = coord 2) ∧ (mark 0 1 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 35 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 8) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c796 : ¬((mark 0 1 8) ∧ ((z 108).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 35 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 1 1 8) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c797 : ¬(((z 108).2 = coord 6) ∧ (mark 0 1 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 35 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 8) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c798 : ¬(((z 108).2 = coord 7) ∧ (mark 0 1 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 1 108 35 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 1 1 8) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c799 : ¬((mark 0 1 3) ∧ (mark 0 0 1) ∧ (¬((z 55).1 = (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 66 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 3 0 1) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c800 : ¬(((z 114).2 = coord 1) ∧ (mark 0 0 1) ∧ (¬(B.Adj (z 55).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c801 : ¬(((z 114).2 = coord 2) ∧ (mark 0 0 1) ∧ (¬(B.Adj (z 55).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c802 : ¬(((z 114).2 = coord 3) ∧ (mark 0 0 1) ∧ (¬((z 55).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c803 : ¬((mark 0 0 1) ∧ ((z 114).2 = coord 6) ∧ (¬((z 55).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c804 : ¬(((z 114).2 = coord 7) ∧ (mark 0 0 1) ∧ (¬(B.Adj (z 55).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c805 : ¬(((z 115).2 = coord 1) ∧ (mark 0 0 1) ∧ (¬(B.Adj (z 55).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c806 : ¬(((z 115).2 = coord 2) ∧ (mark 0 0 1) ∧ (¬(B.Adj (z 55).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c807 : ¬(((z 115).2 = coord 3) ∧ (mark 0 0 1) ∧ (¬((z 55).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c808 : ¬(((z 115).2 = coord 4) ∧ (mark 0 0 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c809 : ¬((mark 0 0 1) ∧ ((z 115).2 = coord 5) ∧ (¬((z 55).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c810 : ¬(((z 115).2 = coord 6) ∧ (mark 0 0 1) ∧ (¬((z 55).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 55 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c811 : ¬((mark 0 1 1) ∧ (mark 0 0 2) ∧ (¬(B.Adj (z 56).1 (z 64).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 64 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 3 0 2) (h.fixed 3 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c812 : ¬((mark 0 1 3) ∧ (mark 0 0 2) ∧ (¬((z 56).1 = (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 66 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 3 0 2) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c813 : ¬(((z 114).2 = coord 1) ∧ (mark 0 0 2) ∧ (¬(B.Adj (z 56).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c814 : ¬(((z 114).2 = coord 2) ∧ (mark 0 0 2) ∧ (¬(B.Adj (z 56).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c815 : ¬((mark 0 0 2) ∧ ((z 114).2 = coord 6) ∧ (¬((z 56).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c816 : ¬(((z 114).2 = coord 8) ∧ (mark 0 0 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 56 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 3 0 2) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c817 : ¬(((z 115).2 = coord 2) ∧ (mark 0 0 2) ∧ (¬(B.Adj (z 56).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c818 : ¬(((z 115).2 = coord 3) ∧ (mark 0 0 2) ∧ (¬((z 56).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c819 : ¬((mark 0 0 2) ∧ ((z 115).2 = coord 6) ∧ (¬((z 56).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 56 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c820 : ¬((mark 0 0 3) ∧ (mark 0 1 1) ∧ (¬((z 57).1 = (z 64).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 64 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 3) (h.fixed 3 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c821 : ¬((mark 0 1 3) ∧ (mark 0 0 3) ∧ (¬(B.Adj (z 57).1 (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 66 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 3 0 3) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c822 : ¬((mark 0 0 3) ∧ (mark 0 1 7) ∧ (¬((z 57).1 = (z 70).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 70 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 3) (h.fixed 3 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c823 : ¬(((z 114).2 = coord 1) ∧ (mark 0 0 3) ∧ (¬((z 57).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c824 : ¬(((z 114).2 = coord 2) ∧ (mark 0 0 3) ∧ (¬((z 57).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c825 : ¬(((z 114).2 = coord 3) ∧ (mark 0 0 3) ∧ (¬(B.Adj (z 57).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c826 : ¬((mark 0 0 3) ∧ ((z 114).2 = coord 6) ∧ (¬(B.Adj (z 57).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c827 : ¬((mark 0 0 3) ∧ ((z 114).2 = coord 7) ∧ (¬((z 57).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c828 : ¬(((z 115).2 = coord 1) ∧ (mark 0 0 3) ∧ (¬((z 57).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c829 : ¬(((z 115).2 = coord 2) ∧ (mark 0 0 3) ∧ (¬((z 57).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c830 : ¬(((z 115).2 = coord 3) ∧ (mark 0 0 3) ∧ (¬(B.Adj (z 57).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c831 : ¬((mark 0 0 3) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 57).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 57 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c832 : ¬((mark 0 0 5) ∧ (mark 0 1 2) ∧ (¬(B.Adj (z 59).1 (z 65).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 65 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 3 0 5) (h.fixed 3 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c833 : ¬((mark 0 0 5) ∧ (mark 0 1 3) ∧ (¬(B.Adj (z 59).1 (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 66 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 3 0 5) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c834 : ¬((mark 0 0 5) ∧ ((z 114).2 = coord 1) ∧ (¬((z 59).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c835 : ¬((mark 0 0 5) ∧ ((z 114).2 = coord 2) ∧ (¬(B.Adj (z 59).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c836 : ¬(((z 114).2 = coord 5) ∧ (mark 0 0 5) ∧ (¬(B.Adj (z 59).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 5) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c837 : ¬((mark 0 0 5) ∧ ((z 114).2 = coord 6) ∧ (¬((z 59).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c838 : ¬((mark 0 0 5) ∧ ((z 114).2 = coord 7) ∧ (¬((z 59).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c839 : ¬((mark 0 0 5) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 59 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c840 : ¬(((z 115).2 = coord 3) ∧ (mark 0 0 5) ∧ (¬(B.Adj (z 59).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 115 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 5) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c841 : ¬((mark 0 0 5) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 59).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c842 : ¬((mark 0 0 5) ∧ ((z 115).2 = coord 6) ∧ (¬((z 59).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c843 : ¬((mark 0 0 5) ∧ ((z 115).2 = coord 7) ∧ (¬((z 59).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 59 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c844 : ¬((mark 0 0 6) ∧ (mark 0 1 3) ∧ (¬(B.Adj (z 60).1 (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 66 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 3 0 6) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c845 : ¬((mark 0 0 6) ∧ (mark 0 1 5) ∧ (¬((z 60).1 = (z 68).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 68 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 6) (h.fixed 3 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c846 : ¬((mark 0 0 6) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 60).1 (z 70).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 70 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 3 0 6) (h.fixed 3 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c847 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 1) ∧ (¬((z 60).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c848 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 2) ∧ (¬((z 60).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c849 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 3) ∧ (¬(B.Adj (z 60).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c850 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 6) ∧ (¬(B.Adj (z 60).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c851 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 7) ∧ (¬(B.Adj (z 60).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c852 : ¬((mark 0 0 6) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 60 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c853 : ¬((mark 0 0 6) ∧ ((z 115).2 = coord 1) ∧ (¬((z 60).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c854 : ¬((mark 0 0 6) ∧ ((z 115).2 = coord 2) ∧ (¬((z 60).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c855 : ¬((mark 0 0 6) ∧ ((z 115).2 = coord 3) ∧ (¬(B.Adj (z 60).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c856 : ¬((mark 0 0 6) ∧ ((z 115).2 = coord 5) ∧ (¬((z 60).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c857 : ¬((mark 0 0 6) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 60).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 60 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 6) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c858 : ¬((mark 0 0 7) ∧ (mark 0 1 2) ∧ (¬((z 61).1 = (z 65).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 65 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 7) (h.fixed 3 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c859 : ¬((mark 0 0 7) ∧ (mark 0 1 3) ∧ (¬((z 61).1 = (z 66).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 66 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 7) (h.fixed 3 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c860 : ¬((mark 0 0 7) ∧ (mark 0 1 5) ∧ (¬((z 61).1 = (z 68).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 68 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 3 0 7) (h.fixed 3 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c861 : ¬((mark 0 0 7) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 61).1 (z 70).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 70 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 3 0 7) (h.fixed 3 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c862 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 1) ∧ (¬(B.Adj (z 61).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c863 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 2) ∧ (¬((z 61).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c864 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 5) ∧ (¬((z 61).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c865 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 6) ∧ (¬(B.Adj (z 61).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c866 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 7) ∧ (¬(B.Adj (z 61).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c867 : ¬((mark 0 0 7) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 61 114 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c868 : ¬((mark 0 0 7) ∧ ((z 115).2 = coord 0) ∧ (¬((z 61).1 = (z 115).1)) ∧ (¬(B.Adj (z 61).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 61 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c869 : ¬((mark 0 0 7) ∧ ((z 115).2 = coord 3) ∧ (¬((z 61).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c870 : ¬((mark 0 0 7) ∧ ((z 115).2 = coord 5) ∧ (¬((z 61).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c871 : ¬((mark 0 0 7) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 61).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c872 : ¬((mark 0 0 7) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 61).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 61 115 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 3 0 7) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c873 : ¬(((z 116).2 = coord 1) ∧ (mark 0 1 1) ∧ (¬(B.Adj (z 64).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c874 : ¬(((z 116).2 = coord 2) ∧ (mark 0 1 1) ∧ (¬(B.Adj (z 64).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c875 : ¬(((z 116).2 = coord 3) ∧ (mark 0 1 1) ∧ (¬((z 64).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c876 : ¬((mark 0 1 1) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 64 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c877 : ¬((mark 0 1 1) ∧ ((z 116).2 = coord 6) ∧ (¬((z 64).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 64 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c878 : ¬(((z 116).2 = coord 2) ∧ (mark 0 1 2) ∧ (¬(B.Adj (z 65).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 65 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c879 : ¬((mark 0 1 2) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 65).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 65 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c880 : ¬((mark 0 1 2) ∧ ((z 116).2 = coord 6) ∧ (¬((z 65).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 65 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c881 : ¬((mark 0 1 3) ∧ ((z 116).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c882 : ¬(((z 116).2 = coord 1) ∧ (mark 0 1 3) ∧ (¬((z 66).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c883 : ¬(((z 116).2 = coord 2) ∧ (mark 0 1 3) ∧ (¬((z 66).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c884 : ¬(((z 116).2 = coord 3) ∧ (mark 0 1 3) ∧ (¬(B.Adj (z 66).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c885 : ¬((mark 0 1 3) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c886 : ¬((mark 0 1 3) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 66).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c887 : ¬((mark 0 1 3) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 66).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c888 : ¬((mark 0 1 3) ∧ ((z 116).2 = coord 7) ∧ (¬((z 66).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c889 : ¬((mark 0 1 5) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 68).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c890 : ¬((mark 0 1 5) ∧ ((z 116).2 = coord 6) ∧ (¬((z 68).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c891 : ¬((mark 0 1 5) ∧ ((z 116).2 = coord 7) ∧ (¬((z 68).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c892 : ¬((mark 0 1 6) ∧ ((z 116).2 = coord 2) ∧ (¬((z 69).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 69 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c893 : ¬((mark 0 1 6) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 69).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 69 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c894 : ¬(((z 116).2 = coord 5) ∧ (mark 0 1 7) ∧ (¬((z 70).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c895 : ¬(((z 116).2 = coord 6) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 70).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c896 : ¬(((z 116).2 = coord 7) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 70).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c897 : ¬(((z 116).2 = coord 0) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c898 : ¬(((z 116).2 = coord 0) ∧ ((z 114).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c899 : ¬(((z 116).2 = coord 0) ∧ ((z 114).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c900 : ¬(((z 114).2 = coord 3) ∧ ((z 116).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c901 : ¬(((z 114).2 = coord 5) ∧ ((z 116).2 = coord 0) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c902 : ¬(((z 116).2 = coord 0) ∧ ((z 114).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c903 : ¬(((z 116).2 = coord 0) ∧ ((z 114).2 = coord 7) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c904 : ¬(((z 114).2 = coord 3) ∧ ((z 116).2 = coord 1) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c905 : ¬(((z 116).2 = coord 2) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c906 : ¬(((z 116).2 = coord 2) ∧ ((z 114).2 = coord 3) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c907 : ¬(((z 116).2 = coord 3) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c908 : ¬(((z 116).2 = coord 3) ∧ ((z 114).2 = coord 1) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c909 : ¬(((z 116).2 = coord 3) ∧ ((z 114).2 = coord 2) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c910 : ¬(((z 116).2 = coord 3) ∧ ((z 114).2 = coord 7) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c911 : ¬(((z 114).2 = coord 1) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c912 : ¬(((z 114).2 = coord 2) ∧ ((z 116).2 = coord 4) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c913 : ¬(((z 114).2 = coord 3) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c914 : ¬(((z 114).2 = coord 4) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c915 : ¬(((z 114).2 = coord 5) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c916 : ¬(((z 114).2 = coord 6) ∧ ((z 116).2 = coord 4) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c917 : ¬(((z 114).2 = coord 7) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c918 : ¬(((z 114).2 = coord 1) ∧ ((z 116).2 = coord 5) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c919 : ¬(((z 114).2 = coord 7) ∧ ((z 116).2 = coord 5) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c920 : ¬(((z 114).2 = coord 0) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c921 : ¬(((z 114).2 = coord 2) ∧ ((z 116).2 = coord 6) ∧ (¬((z 114).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c922 : ¬(((z 114).2 = coord 8) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c923 : ¬(((z 116).2 = coord 8) ∧ ((z 114).2 = coord 1) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c924 : ¬(((z 116).2 = coord 8) ∧ ((z 114).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c925 : ¬(((z 114).2 = coord 3) ∧ ((z 116).2 = coord 8) ∧ (¬((z 114).1 = (z 116).1)) ∧ (¬(B.Adj (z 114).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c926 : ¬(((z 114).2 = coord 5) ∧ ((z 116).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c927 : ¬(((z 116).2 = coord 8) ∧ ((z 114).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c928 : ¬(((z 116).2 = coord 8) ∧ ((z 114).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c929 : ¬(((z 116).2 = coord 8) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c930 : ¬(((z 116).2 = coord 0) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c931 : ¬(((z 116).2 = coord 0) ∧ ((z 115).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c932 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c933 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c934 : ¬(((z 116).2 = coord 0) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c935 : ¬(((z 116).2 = coord 0) ∧ ((z 115).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c936 : ¬(((z 116).2 = coord 0) ∧ ((z 115).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c937 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c938 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c939 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c940 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 1) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c941 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c942 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c943 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 6) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c944 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c945 : ¬(((z 116).2 = coord 1) ∧ ((z 115).2 = coord 8) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c946 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c947 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c948 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 2) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c949 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 3) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c950 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 2) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c951 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c952 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 6) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c953 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c954 : ¬(((z 116).2 = coord 2) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c955 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c956 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 1) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c957 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 2) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c958 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 3) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c959 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c960 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c961 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c962 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c963 : ¬(((z 116).2 = coord 3) ∧ ((z 115).2 = coord 8) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c964 : ¬(((z 115).2 = coord 1) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c965 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 4) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c966 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c967 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c968 : ¬(((z 115).2 = coord 5) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c969 : ¬(((z 115).2 = coord 6) ∧ ((z 116).2 = coord 4) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c970 : ¬(((z 115).2 = coord 7) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c971 : ¬(((z 115).2 = coord 0) ∧ ((z 116).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c972 : ¬(((z 115).2 = coord 1) ∧ ((z 116).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c973 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c974 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c975 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c976 : ¬(((z 116).2 = coord 5) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c977 : ¬(((z 115).2 = coord 6) ∧ ((z 116).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c978 : ¬(((z 115).2 = coord 7) ∧ ((z 116).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c979 : ¬(((z 115).2 = coord 8) ∧ ((z 116).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c980 : ¬(((z 115).2 = coord 0) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c981 : ¬(((z 115).2 = coord 1) ∧ ((z 116).2 = coord 6) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c982 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 6) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c983 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c984 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 6) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c985 : ¬(((z 116).2 = coord 6) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c986 : ¬(((z 116).2 = coord 6) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c987 : ¬(((z 115).2 = coord 7) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c988 : ¬(((z 115).2 = coord 8) ∧ ((z 116).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c989 : ¬(((z 115).2 = coord 0) ∧ ((z 116).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c990 : ¬(((z 115).2 = coord 1) ∧ ((z 116).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c991 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c992 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 7) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c993 : ¬(((z 115).2 = coord 4) ∧ ((z 116).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c994 : ¬(((z 116).2 = coord 7) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c995 : ¬(((z 116).2 = coord 7) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c996 : ¬(((z 116).2 = coord 7) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c997 : ¬(((z 115).2 = coord 8) ∧ ((z 116).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c998 : ¬(((z 116).2 = coord 8) ∧ ((z 115).2 = coord 1) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c999 : ¬(((z 115).2 = coord 2) ∧ ((z 116).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1000 : ¬(((z 115).2 = coord 3) ∧ ((z 116).2 = coord 8) ∧ (¬((z 115).1 = (z 116).1)) ∧ (¬(B.Adj (z 115).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1001 : ¬(((z 116).2 = coord 8) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1002 : ¬(((z 116).2 = coord 8) ∧ ((z 115).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1003 : ¬(((z 116).2 = coord 8) ∧ ((z 115).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1004 : ¬(((z 116).2 = coord 8) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 116 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1005 : ¬(((z 118).2 = coord 0) ∧ (mark 0 1 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1006 : ¬(((z 118).2 = coord 1) ∧ (mark 0 1 1) ∧ (¬(B.Adj (z 64).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1007 : ¬((mark 0 1 1) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 64).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1008 : ¬((mark 0 1 1) ∧ ((z 118).2 = coord 3) ∧ (¬((z 64).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1009 : ¬((mark 0 1 1) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1010 : ¬(((z 118).2 = coord 5) ∧ (mark 0 1 1) ∧ (¬((z 64).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1011 : ¬(((z 118).2 = coord 6) ∧ (mark 0 1 1) ∧ (¬((z 64).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1012 : ¬(((z 118).2 = coord 7) ∧ (mark 0 1 1) ∧ (¬(B.Adj (z 64).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 64 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1013 : ¬(((z 118).2 = coord 0) ∧ (mark 0 1 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 2) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1014 : ¬((mark 0 1 2) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 65).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1015 : ¬((mark 0 1 2) ∧ ((z 118).2 = coord 3) ∧ (¬((z 65).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1016 : ¬(((z 118).2 = coord 6) ∧ (mark 0 1 2) ∧ (¬((z 65).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1017 : ¬(((z 118).2 = coord 7) ∧ (mark 0 1 2) ∧ (¬((z 65).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1018 : ¬(((z 118).2 = coord 8) ∧ (mark 0 1 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 65 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 2) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1019 : ¬(((z 118).2 = coord 0) ∧ (mark 0 1 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1020 : ¬(((z 118).2 = coord 1) ∧ (mark 0 1 3) ∧ (¬((z 66).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1021 : ¬((mark 0 1 3) ∧ ((z 118).2 = coord 2) ∧ (¬((z 66).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1022 : ¬((mark 0 1 3) ∧ ((z 118).2 = coord 3) ∧ (¬(B.Adj (z 66).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1023 : ¬((mark 0 1 3) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1024 : ¬((mark 0 1 3) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 66).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1025 : ¬((mark 0 1 3) ∧ ((z 118).2 = coord 6) ∧ (¬(B.Adj (z 66).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1026 : ¬(((z 118).2 = coord 7) ∧ (mark 0 1 3) ∧ (¬((z 66).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 66 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1027 : ¬(((z 118).2 = coord 1) ∧ (mark 0 1 5) ∧ (¬((z 68).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1028 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 68).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1029 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 3) ∧ (¬(B.Adj (z 68).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1030 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1031 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 68).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1032 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 6) ∧ (¬((z 68).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1033 : ¬((mark 0 1 5) ∧ ((z 118).2 = coord 7) ∧ (¬((z 68).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1034 : ¬(((z 118).2 = coord 8) ∧ (mark 0 1 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 68 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 5) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1035 : ¬((mark 0 1 6) ∧ ((z 118).2 = coord 2) ∧ (¬((z 69).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 69 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 3 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1036 : ¬((mark 0 1 6) ∧ ((z 118).2 = coord 6) ∧ (¬(B.Adj (z 69).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 69 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 3 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1037 : ¬((mark 0 1 6) ∧ ((z 118).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 69 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 3 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1038 : ¬(((z 118).2 = coord 1) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 70).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1039 : ¬(((z 118).2 = coord 4) ∧ (mark 0 1 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1040 : ¬(((z 118).2 = coord 5) ∧ (mark 0 1 7) ∧ (¬((z 70).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1041 : ¬(((z 118).2 = coord 6) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 70).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1042 : ¬(((z 118).2 = coord 7) ∧ (mark 0 1 7) ∧ (¬(B.Adj (z 70).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1043 : ¬(((z 118).2 = coord 8) ∧ (mark 0 1 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 70 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 3 1 7) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1044 : ¬(((z 118).2 = coord 0) ∧ ((z 114).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1045 : ¬(((z 118).2 = coord 0) ∧ ((z 114).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1046 : ¬(((z 118).2 = coord 0) ∧ ((z 114).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1047 : ¬(((z 118).2 = coord 1) ∧ ((z 114).2 = coord 2) ∧ (¬(B.Adj (z 114).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1048 : ¬(((z 118).2 = coord 1) ∧ ((z 114).2 = coord 3) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1049 : ¬(((z 118).2 = coord 1) ∧ ((z 114).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1050 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 2) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1051 : ¬(((z 114).2 = coord 1) ∧ ((z 118).2 = coord 3) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1052 : ¬(((z 114).2 = coord 2) ∧ ((z 118).2 = coord 3) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1053 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 3) ∧ (¬(B.Adj (z 114).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1054 : ¬(((z 114).2 = coord 4) ∧ ((z 118).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1055 : ¬(((z 114).2 = coord 7) ∧ ((z 118).2 = coord 3) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1056 : ¬(((z 114).2 = coord 1) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1057 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1058 : ¬(((z 114).2 = coord 4) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1059 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 114).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1060 : ¬(((z 114).2 = coord 4) ∧ ((z 118).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1061 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 6) ∧ (¬(B.Adj (z 114).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1062 : ¬(((z 114).2 = coord 3) ∧ ((z 118).2 = coord 7) ∧ (¬((z 114).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1063 : ¬(((z 118).2 = coord 8) ∧ ((z 114).2 = coord 1) ∧ (¬((z 114).1 = (z 118).1)) ∧ (¬(B.Adj (z 114).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1064 : ¬(((z 118).2 = coord 8) ∧ ((z 114).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1065 : ¬(((z 114).2 = coord 5) ∧ ((z 118).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1066 : ¬(((z 118).2 = coord 8) ∧ ((z 114).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1067 : ¬(((z 118).2 = coord 8) ∧ ((z 114).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1068 : ¬(((z 118).2 = coord 8) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 114 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1069 : ¬(((z 118).2 = coord 0) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1070 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1071 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1072 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 2) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1073 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 3) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1074 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1075 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1076 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 6) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1077 : ¬(((z 118).2 = coord 1) ∧ ((z 115).2 = coord 8) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1078 : ¬(((z 115).2 = coord 0) ∧ ((z 118).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1079 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 2) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1080 : ¬(((z 115).2 = coord 5) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1081 : ¬(((z 115).2 = coord 8) ∧ ((z 118).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1082 : ¬(((z 115).2 = coord 0) ∧ ((z 118).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1083 : ¬(((z 115).2 = coord 2) ∧ ((z 118).2 = coord 3) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1084 : ¬(((z 115).2 = coord 3) ∧ ((z 118).2 = coord 3) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1085 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1086 : ¬(((z 118).2 = coord 3) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1087 : ¬(((z 115).2 = coord 7) ∧ ((z 118).2 = coord 3) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1088 : ¬(((z 115).2 = coord 8) ∧ ((z 118).2 = coord 3) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1089 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1090 : ¬(((z 115).2 = coord 7) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1091 : ¬(((z 115).2 = coord 0) ∧ ((z 118).2 = coord 5) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1092 : ¬(((z 115).2 = coord 2) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1093 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1094 : ¬(((z 118).2 = coord 5) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1095 : ¬(((z 118).2 = coord 5) ∧ ((z 115).2 = coord 7) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1096 : ¬(((z 115).2 = coord 8) ∧ ((z 118).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1097 : ¬(((z 118).2 = coord 6) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1098 : ¬(((z 115).2 = coord 2) ∧ ((z 118).2 = coord 6) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1099 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 6) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1100 : ¬(((z 118).2 = coord 6) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1101 : ¬(((z 118).2 = coord 6) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1102 : ¬(((z 118).2 = coord 6) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1103 : ¬(((z 118).2 = coord 7) ∧ ((z 115).2 = coord 0) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1104 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1105 : ¬(((z 118).2 = coord 7) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1106 : ¬(((z 118).2 = coord 7) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1107 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 1) ∧ (¬((z 115).1 = (z 118).1)) ∧ (¬(B.Adj (z 115).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1108 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1109 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1110 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1111 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1112 : ¬(((z 118).2 = coord 8) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 3 118 115 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1113 : ¬((mark 1 1 1) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 73).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 82 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 1) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1114 : ¬((mark 1 1 2) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 73).1 (z 83).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 83 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 1) (h.fixed 4 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1115 : ¬((mark 1 1 3) ∧ (mark 1 0 1) ∧ (¬((z 73).1 = (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 84 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 4 0 1) (h.fixed 4 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1116 : ¬((mark 1 0 1) ∧ (mark 1 1 5) ∧ (¬((z 73).1 = (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 86 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 1) (h.fixed 4 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1117 : ¬((mark 1 0 1) ∧ (mark 1 1 6) ∧ (¬((z 73).1 = (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 87 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 1) (h.fixed 4 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1118 : ¬((mark 1 0 1) ∧ (mark 1 1 7) ∧ (¬(B.Adj (z 73).1 (z 88).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 88 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 4 0 1) (h.fixed 4 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1119 : ¬(((z 116).2 = coord 1) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 73).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1120 : ¬(((z 116).2 = coord 2) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 73).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1121 : ¬(((z 116).2 = coord 3) ∧ (mark 1 0 1) ∧ (¬((z 73).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1122 : ¬((mark 1 0 1) ∧ ((z 116).2 = coord 5) ∧ (¬((z 73).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1123 : ¬((mark 1 0 1) ∧ ((z 116).2 = coord 6) ∧ (¬((z 73).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1124 : ¬(((z 116).2 = coord 7) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 73).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1125 : ¬((mark 1 0 1) ∧ ((z 117).2 = coord 3) ∧ (¬((z 73).1 = (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 73 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1126 : ¬((mark 1 1 1) ∧ (mark 1 0 2) ∧ (¬(B.Adj (z 74).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 74 82 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 2) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1127 : ¬((mark 1 0 2) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 74).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 74 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1128 : ¬((mark 1 0 2) ∧ ((z 116).2 = coord 7) ∧ (¬((z 74).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 74 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1129 : ¬((mark 1 0 3) ∧ (mark 1 1 1) ∧ (¬((z 75).1 = (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 82 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 3) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1130 : ¬((mark 1 0 3) ∧ (mark 1 1 2) ∧ (¬((z 75).1 = (z 83).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 83 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 3) (h.fixed 4 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1131 : ¬((mark 1 1 3) ∧ (mark 1 0 3) ∧ (¬(B.Adj (z 75).1 (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 84 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 3) (h.fixed 4 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1132 : ¬((mark 1 0 3) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 75).1 (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 86 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 4 0 3) (h.fixed 4 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1133 : ¬((mark 1 0 3) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 75).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 87 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 4 0 3) (h.fixed 4 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1134 : ¬((mark 1 0 3) ∧ (mark 1 1 7) ∧ (¬((z 75).1 = (z 88).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 88 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 3) (h.fixed 4 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1135 : ¬(((z 116).2 = coord 1) ∧ (mark 1 0 3) ∧ (¬((z 75).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1136 : ¬(((z 116).2 = coord 2) ∧ (mark 1 0 3) ∧ (¬((z 75).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1137 : ¬((mark 1 0 3) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 75).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1138 : ¬((mark 1 0 3) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 75).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1139 : ¬((mark 1 0 3) ∧ ((z 116).2 = coord 7) ∧ (¬((z 75).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 75 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1140 : ¬((mark 1 0 4) ∧ ((z 117).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 76 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 4 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1141 : ¬((mark 1 0 4) ∧ ((z 117).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 76 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 4 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1142 : ¬((mark 1 0 4) ∧ ((z 117).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 76 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 4 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1143 : ¬((mark 1 0 4) ∧ ((z 117).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 76 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 4 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1144 : ¬((mark 1 0 4) ∧ ((z 117).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 76 117 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 4 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1145 : ¬((mark 1 0 5) ∧ (mark 1 1 1) ∧ (¬((z 77).1 = (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 82 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 5) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1146 : ¬((mark 1 0 5) ∧ (mark 1 1 3) ∧ (¬(B.Adj (z 77).1 (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 84 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 4 0 5) (h.fixed 4 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1147 : ¬((mark 1 0 5) ∧ (mark 1 1 6) ∧ (¬((z 77).1 = (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 87 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 4 0 5) (h.fixed 4 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1148 : ¬((mark 1 0 5) ∧ ((z 116).2 = coord 2) ∧ (¬(B.Adj (z 77).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1149 : ¬((mark 1 0 5) ∧ ((z 116).2 = coord 3) ∧ (¬(B.Adj (z 77).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1150 : ¬((mark 1 0 5) ∧ ((z 116).2 = coord 6) ∧ (¬((z 77).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 77 116 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1151 : ¬((mark 1 1 1) ∧ (mark 1 0 6) ∧ (¬((z 78).1 = (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 82 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 4 0 6) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1152 : ¬((mark 1 1 3) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 78).1 (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 84 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 6) (h.fixed 4 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1153 : ¬((mark 1 1 5) ∧ (mark 1 0 6) ∧ (¬((z 78).1 = (z 86).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 86 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 4 0 6) (h.fixed 4 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1154 : ¬((mark 1 1 6) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 78).1 (z 87).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 87 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 6) (h.fixed 4 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1155 : ¬((mark 1 1 7) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 78).1 (z 88).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 88 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 6) (h.fixed 4 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1156 : ¬(((z 116).2 = coord 0) ∧ (mark 1 0 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1157 : ¬(((z 116).2 = coord 1) ∧ (mark 1 0 6) ∧ (¬((z 78).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1158 : ¬(((z 116).2 = coord 2) ∧ (mark 1 0 6) ∧ (¬((z 78).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1159 : ¬(((z 116).2 = coord 3) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 78).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1160 : ¬(((z 116).2 = coord 5) ∧ (mark 1 0 6) ∧ (¬((z 78).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1161 : ¬(((z 116).2 = coord 7) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 78).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 78 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1162 : ¬((mark 1 1 1) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 79).1 (z 82).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 82 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 7) (h.fixed 4 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1163 : ¬((mark 1 1 3) ∧ (mark 1 0 7) ∧ (¬((z 79).1 = (z 84).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 84 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 4 0 7) (h.fixed 4 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1164 : ¬((mark 1 1 7) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 79).1 (z 88).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 88 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 4 0 7) (h.fixed 4 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1165 : ¬(((z 116).2 = coord 0) ∧ (mark 1 0 7) ∧ (¬((z 79).1 = (z 116).1)) ∧ (¬(B.Adj (z 79).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 79 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1166 : ¬(((z 116).2 = coord 2) ∧ (mark 1 0 7) ∧ (¬((z 79).1 = (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 4 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1167 : ¬(((z 116).2 = coord 6) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 79).1 (z 116).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 116 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1168 : ¬(((z 117).2 = coord 7) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 79).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 79 117 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 4 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1169 : ¬((mark 1 1 1) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1170 : ¬((mark 1 1 1) ∧ ((z 114).2 = coord 1) ∧ (¬(B.Adj (z 82).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1171 : ¬((mark 1 1 1) ∧ ((z 114).2 = coord 2) ∧ (¬(B.Adj (z 82).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1172 : ¬(((z 114).2 = coord 3) ∧ (mark 1 1 1) ∧ (¬((z 82).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1173 : ¬(((z 114).2 = coord 4) ∧ (mark 1 1 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 1) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1174 : ¬(((z 114).2 = coord 5) ∧ (mark 1 1 1) ∧ (¬((z 82).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1175 : ¬((mark 1 1 1) ∧ ((z 114).2 = coord 6) ∧ (¬((z 82).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1176 : ¬((mark 1 1 1) ∧ ((z 114).2 = coord 7) ∧ (¬(B.Adj (z 82).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1177 : ¬((mark 1 1 2) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1178 : ¬((mark 1 1 2) ∧ ((z 114).2 = coord 1) ∧ (¬(B.Adj (z 83).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1179 : ¬((mark 1 1 2) ∧ ((z 114).2 = coord 2) ∧ (¬(B.Adj (z 83).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1180 : ¬(((z 114).2 = coord 3) ∧ (mark 1 1 2) ∧ (¬((z 83).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1181 : ¬((mark 1 1 2) ∧ ((z 114).2 = coord 6) ∧ (¬((z 83).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1182 : ¬((mark 1 1 2) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1183 : ¬((mark 1 1 3) ∧ ((z 114).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1184 : ¬((mark 1 1 3) ∧ ((z 114).2 = coord 1) ∧ (¬((z 84).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1185 : ¬((mark 1 1 3) ∧ ((z 114).2 = coord 3) ∧ (¬(B.Adj (z 84).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1186 : ¬(((z 114).2 = coord 4) ∧ (mark 1 1 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 84 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 3) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1187 : ¬((mark 1 1 3) ∧ ((z 114).2 = coord 7) ∧ (¬((z 84).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1188 : ¬(((z 114).2 = coord 4) ∧ (mark 1 1 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1189 : ¬(((z 114).2 = coord 5) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 86).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1190 : ¬(((z 114).2 = coord 7) ∧ (mark 1 1 5) ∧ (¬((z 86).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1191 : ¬(((z 114).2 = coord 8) ∧ (mark 1 1 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1192 : ¬(((z 114).2 = coord 0) ∧ (mark 1 1 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1193 : ¬(((z 114).2 = coord 2) ∧ (mark 1 1 6) ∧ (¬((z 87).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1194 : ¬(((z 114).2 = coord 3) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 87).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1195 : ¬((mark 1 1 6) ∧ ((z 114).2 = coord 6) ∧ (¬(B.Adj (z 87).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 87 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1196 : ¬(((z 114).2 = coord 8) ∧ (mark 1 1 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1197 : ¬(((z 114).2 = coord 2) ∧ (mark 1 1 7) ∧ (¬((z 88).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1198 : ¬(((z 114).2 = coord 3) ∧ (mark 1 1 7) ∧ (¬((z 88).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1199 : ¬(((z 114).2 = coord 4) ∧ (mark 1 1 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 7) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1200 : ¬(((z 114).2 = coord 5) ∧ (mark 1 1 7) ∧ (¬((z 88).1 = (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1201 : ¬((mark 1 1 7) ∧ ((z 114).2 = coord 6) ∧ (¬(B.Adj (z 88).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1202 : ¬((mark 1 1 7) ∧ ((z 114).2 = coord 7) ∧ (¬(B.Adj (z 88).1 (z 114).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1203 : ¬((mark 1 1 7) ∧ ((z 114).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 88 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 7) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1204 : ¬(((z 114).2 = coord 7) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 114 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1205 : ¬(((z 117).2 = coord 1) ∧ ((z 114).2 = coord 1) ∧ (¬(B.Adj (z 114).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1206 : ¬(((z 117).2 = coord 2) ∧ ((z 114).2 = coord 2) ∧ (¬(B.Adj (z 114).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1207 : ¬(((z 117).2 = coord 7) ∧ ((z 114).2 = coord 7) ∧ (¬(B.Adj (z 114).1 (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 114 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1208 : ¬(((z 119).2 = coord 0) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 81 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1209 : ¬(((z 119).2 = coord 6) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 81 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1210 : ¬((mark 1 1 1) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 82).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1211 : ¬((mark 1 1 1) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 82).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1212 : ¬((mark 1 1 1) ∧ ((z 119).2 = coord 3) ∧ (¬((z 82).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 82 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1213 : ¬((mark 1 1 2) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 83).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 83 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1214 : ¬(((z 119).2 = coord 6) ∧ (mark 1 1 2) ∧ (¬((z 83).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 83 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1215 : ¬(((z 119).2 = coord 7) ∧ (mark 1 1 2) ∧ (¬((z 83).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 83 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1216 : ¬((mark 1 1 3) ∧ ((z 119).2 = coord 1) ∧ (¬((z 84).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1217 : ¬((mark 1 1 3) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 84).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 84 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 4 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1218 : ¬((mark 1 1 4) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 85 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1219 : ¬((mark 1 1 4) ∧ ((z 119).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 85 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 4 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1220 : ¬(((z 119).2 = coord 2) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 86).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1221 : ¬(((z 119).2 = coord 5) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 86).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1222 : ¬(((z 119).2 = coord 7) ∧ (mark 1 1 5) ∧ (¬((z 86).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 86 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 4 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1223 : ¬(((z 119).2 = coord 3) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 87).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1224 : ¬(((z 119).2 = coord 6) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 87).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1225 : ¬(((z 119).2 = coord 7) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 87).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 87 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1226 : ¬((mark 1 1 7) ∧ ((z 119).2 = coord 2) ∧ (¬((z 88).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 88 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1227 : ¬(((z 119).2 = coord 7) ∧ (mark 1 1 7) ∧ (¬(B.Adj (z 88).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 88 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 4 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1228 : ¬(((z 119).2 = coord 8) ∧ (mark 1 1 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 89 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 4 1 8) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1229 : ¬(((z 116).2 = coord 0) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1230 : ¬(((z 116).2 = coord 1) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1231 : ¬(((z 116).2 = coord 2) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1232 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 1) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1233 : ¬(((z 116).2 = coord 4) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1234 : ¬(((z 116).2 = coord 5) ∧ ((z 119).2 = coord 1) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1235 : ¬(((z 116).2 = coord 6) ∧ ((z 119).2 = coord 1) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1236 : ¬(((z 116).2 = coord 7) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1237 : ¬(((z 116).2 = coord 8) ∧ ((z 119).2 = coord 1) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1238 : ¬(((z 116).2 = coord 0) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1239 : ¬(((z 116).2 = coord 1) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1240 : ¬(((z 116).2 = coord 2) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1241 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 2) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1242 : ¬(((z 119).2 = coord 2) ∧ ((z 116).2 = coord 4) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1243 : ¬(((z 116).2 = coord 5) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1244 : ¬(((z 116).2 = coord 6) ∧ ((z 119).2 = coord 2) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1245 : ¬(((z 116).2 = coord 7) ∧ ((z 119).2 = coord 2) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1246 : ¬(((z 116).2 = coord 8) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1247 : ¬(((z 116).2 = coord 0) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1248 : ¬(((z 116).2 = coord 1) ∧ ((z 119).2 = coord 3) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1249 : ¬(((z 116).2 = coord 2) ∧ ((z 119).2 = coord 3) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1250 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1251 : ¬(((z 119).2 = coord 3) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1252 : ¬(((z 119).2 = coord 3) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1253 : ¬(((z 116).2 = coord 6) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1254 : ¬(((z 116).2 = coord 7) ∧ ((z 119).2 = coord 3) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1255 : ¬(((z 116).2 = coord 8) ∧ ((z 119).2 = coord 3) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1256 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 0) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1257 : ¬(((z 116).2 = coord 1) ∧ ((z 119).2 = coord 5) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1258 : ¬(((z 116).2 = coord 2) ∧ ((z 119).2 = coord 5) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1259 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 5) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1260 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1261 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 5) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1262 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 6) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1263 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 7) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1264 : ¬(((z 119).2 = coord 5) ∧ ((z 116).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1265 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1266 : ¬(((z 116).2 = coord 1) ∧ ((z 119).2 = coord 6) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1267 : ¬(((z 116).2 = coord 2) ∧ ((z 119).2 = coord 6) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1268 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 6) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1269 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 4) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1270 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 5) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1271 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1272 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 7) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1273 : ¬(((z 119).2 = coord 6) ∧ ((z 116).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1274 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 0) ∧ (¬((z 116).1 = (z 119).1)) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1275 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 1) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1276 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 2) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1277 : ¬(((z 116).2 = coord 3) ∧ ((z 119).2 = coord 7) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1278 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1279 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 5) ∧ (¬((z 116).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1280 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 6) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1281 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 7) ∧ (¬(B.Adj (z 116).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1282 : ¬(((z 119).2 = coord 7) ∧ ((z 116).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 116 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1283 : ¬(((z 117).2 = coord 0) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1284 : ¬(((z 117).2 = coord 1) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 117).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1285 : ¬(((z 117).2 = coord 3) ∧ ((z 119).2 = coord 1) ∧ (¬((z 117).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1286 : ¬(((z 117).2 = coord 4) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1287 : ¬(((z 117).2 = coord 0) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1288 : ¬(((z 117).2 = coord 8) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1289 : ¬(((z 119).2 = coord 7) ∧ ((z 117).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1290 : ¬(((z 119).2 = coord 7) ∧ ((z 117).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 4 119 117 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1291 : ¬((mark 1 1 1) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 91).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 100 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 1) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1292 : ¬((mark 1 1 2) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 91).1 (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 101 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 1) (h.fixed 5 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1293 : ¬((mark 1 1 3) ∧ (mark 1 0 1) ∧ (¬((z 91).1 = (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 102 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 1) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1294 : ¬((mark 1 0 1) ∧ (mark 1 1 6) ∧ (¬((z 91).1 = (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 105 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 1) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1295 : ¬(((z 118).2 = coord 0) ∧ (mark 1 0 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1296 : ¬(((z 118).2 = coord 1) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 91).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1297 : ¬((mark 1 0 1) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 91).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1298 : ¬((mark 1 0 1) ∧ ((z 118).2 = coord 3) ∧ (¬((z 91).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1299 : ¬((mark 1 0 1) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1300 : ¬(((z 118).2 = coord 5) ∧ (mark 1 0 1) ∧ (¬((z 91).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1301 : ¬(((z 118).2 = coord 6) ∧ (mark 1 0 1) ∧ (¬((z 91).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1302 : ¬(((z 118).2 = coord 7) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 91).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1303 : ¬((mark 1 0 1) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 91).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1304 : ¬((mark 1 0 1) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 91).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1305 : ¬((mark 1 0 1) ∧ ((z 119).2 = coord 3) ∧ (¬((z 91).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1306 : ¬(((z 119).2 = coord 5) ∧ (mark 1 0 1) ∧ (¬((z 91).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1307 : ¬(((z 119).2 = coord 6) ∧ (mark 1 0 1) ∧ (¬((z 91).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1308 : ¬(((z 119).2 = coord 7) ∧ (mark 1 0 1) ∧ (¬(B.Adj (z 91).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 91 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 1) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1309 : ¬((mark 1 1 1) ∧ (mark 1 0 2) ∧ (¬(B.Adj (z 92).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 100 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 2) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1310 : ¬((mark 1 1 2) ∧ (mark 1 0 2) ∧ (¬(B.Adj (z 92).1 (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 101 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 2) (h.fixed 5 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1311 : ¬((mark 1 1 3) ∧ (mark 1 0 2) ∧ (¬((z 92).1 = (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 102 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 2) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1312 : ¬((mark 1 0 2) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 92).1 (z 104).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 104 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 2) (h.fixed 5 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1313 : ¬((mark 1 0 2) ∧ (mark 1 1 6) ∧ (¬((z 92).1 = (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 105 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 2) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1314 : ¬((mark 1 0 2) ∧ (mark 1 1 7) ∧ (¬((z 92).1 = (z 106).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 106 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 2) (h.fixed 5 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1315 : ¬(((z 118).2 = coord 0) ∧ (mark 1 0 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1316 : ¬(((z 118).2 = coord 1) ∧ (mark 1 0 2) ∧ (¬(B.Adj (z 92).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1317 : ¬((mark 1 0 2) ∧ ((z 118).2 = coord 2) ∧ (¬(B.Adj (z 92).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1318 : ¬((mark 1 0 2) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 92).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1319 : ¬((mark 1 0 2) ∧ ((z 118).2 = coord 6) ∧ (¬((z 92).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1320 : ¬(((z 118).2 = coord 7) ∧ (mark 1 0 2) ∧ (¬((z 92).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1321 : ¬(((z 118).2 = coord 8) ∧ (mark 1 0 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 92 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1322 : ¬((mark 1 0 2) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 92).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1323 : ¬((mark 1 0 2) ∧ ((z 119).2 = coord 3) ∧ (¬((z 92).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 2) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1324 : ¬(((z 119).2 = coord 6) ∧ (mark 1 0 2) ∧ (¬((z 92).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1325 : ¬(((z 119).2 = coord 7) ∧ (mark 1 0 2) ∧ (¬((z 92).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 92 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 2) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1326 : ¬((mark 1 0 3) ∧ (mark 1 1 1) ∧ (¬((z 93).1 = (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 100 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 3) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1327 : ¬((mark 1 0 3) ∧ (mark 1 1 2) ∧ (¬((z 93).1 = (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 101 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 3) (h.fixed 5 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1328 : ¬((mark 1 1 3) ∧ (mark 1 0 3) ∧ (¬(B.Adj (z 93).1 (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 102 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 3) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1329 : ¬((mark 1 0 3) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 93).1 (z 104).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 104 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 3) (h.fixed 5 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1330 : ¬((mark 1 0 3) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 93).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 105 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 3) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1331 : ¬((mark 1 0 3) ∧ (mark 1 1 7) ∧ (¬((z 93).1 = (z 106).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 106 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 3) (h.fixed 5 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1332 : ¬(((z 118).2 = coord 0) ∧ (mark 1 0 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 3) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1333 : ¬(((z 118).2 = coord 1) ∧ (mark 1 0 3) ∧ (¬((z 93).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1334 : ¬((mark 1 0 3) ∧ ((z 118).2 = coord 2) ∧ (¬((z 93).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1335 : ¬((mark 1 0 3) ∧ ((z 118).2 = coord 3) ∧ (¬(B.Adj (z 93).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1336 : ¬((mark 1 0 3) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1337 : ¬((mark 1 0 3) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 93).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1338 : ¬((mark 1 0 3) ∧ ((z 118).2 = coord 6) ∧ (¬(B.Adj (z 93).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1339 : ¬(((z 118).2 = coord 7) ∧ (mark 1 0 3) ∧ (¬((z 93).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1340 : ¬((mark 1 0 3) ∧ ((z 119).2 = coord 1) ∧ (¬((z 93).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1341 : ¬((mark 1 0 3) ∧ ((z 119).2 = coord 2) ∧ (¬((z 93).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1342 : ¬((mark 1 0 3) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 93).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 3) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1343 : ¬(((z 119).2 = coord 6) ∧ (mark 1 0 3) ∧ (¬(B.Adj (z 93).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1344 : ¬(((z 119).2 = coord 7) ∧ (mark 1 0 3) ∧ (¬((z 93).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 93 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 3) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1345 : ¬((mark 1 0 4) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 94 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 5 0 4) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1346 : ¬((mark 1 0 5) ∧ (mark 1 1 1) ∧ (¬((z 95).1 = (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 100 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 5) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1347 : ¬((mark 1 0 5) ∧ (mark 1 1 2) ∧ (¬(B.Adj (z 95).1 (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 101 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 5) (h.fixed 5 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1348 : ¬((mark 1 0 5) ∧ (mark 1 1 3) ∧ (¬(B.Adj (z 95).1 (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 102 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 5) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1349 : ¬((mark 1 0 5) ∧ (mark 1 1 6) ∧ (¬((z 95).1 = (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 105 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_equal B z hh (h.fixed 5 0 5) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1350 : ¬((mark 1 0 5) ∧ ((z 118).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 95 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1351 : ¬((mark 1 0 5) ∧ ((z 118).2 = coord 5) ∧ (¬(B.Adj (z 95).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1352 : ¬((mark 1 0 5) ∧ ((z 118).2 = coord 7) ∧ (¬((z 95).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1353 : ¬((mark 1 0 5) ∧ ((z 118).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 95 118 (by decide +kernel) (by decide +kernel) h1 trivial
  exact impossible B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1354 : ¬((mark 1 0 5) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 95).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1355 : ¬((mark 1 0 5) ∧ ((z 119).2 = coord 5) ∧ (¬(B.Adj (z 95).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 95 119 (by decide +kernel) (by decide +kernel) h1 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 5) h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1356 : ¬((mark 1 1 1) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 100 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 6) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1357 : ¬((mark 1 1 2) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 101).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 101 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 6) (h.fixed 5 1 2) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1358 : ¬((mark 1 1 3) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 102 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 6) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1359 : ¬((mark 1 1 5) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 104).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 104 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 6) (h.fixed 5 1 5) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1360 : ¬((mark 1 1 6) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 105 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 6) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1361 : ¬((mark 1 1 7) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 106).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 106 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 6) (h.fixed 5 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1362 : ¬(((z 118).2 = coord 0) ∧ (mark 1 0 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1363 : ¬(((z 118).2 = coord 1) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1364 : ¬(((z 118).2 = coord 2) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1365 : ¬(((z 118).2 = coord 5) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1366 : ¬(((z 118).2 = coord 6) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1367 : ¬(((z 118).2 = coord 7) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1368 : ¬(((z 118).2 = coord 8) ∧ (mark 1 0 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 96 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1369 : ¬(((z 119).2 = coord 2) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1370 : ¬(((z 119).2 = coord 5) ∧ (mark 1 0 6) ∧ (¬((z 96).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1371 : ¬(((z 119).2 = coord 6) ∧ (mark 1 0 6) ∧ (¬(B.Adj (z 96).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 96 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 6) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1372 : ¬((mark 1 1 1) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 97).1 (z 100).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 100 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 7) (h.fixed 5 1 1) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1373 : ¬((mark 1 1 3) ∧ (mark 1 0 7) ∧ (¬((z 97).1 = (z 102).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 102 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_equal B z hh (h.fixed 5 0 7) (h.fixed 5 1 3) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1374 : ¬((mark 1 0 7) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 97).1 (z 105).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 105 (by decide +kernel) (by decide +kernel) h1 h2
  exact h3 (only_cross B z hh (h.fixed 5 0 7) (h.fixed 5 1 6) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1375 : ¬((mark 1 1 7) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 97).1 (z 106).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 106 (by decide +kernel) (by decide +kernel) h2 h1
  exact h3 (only_cross B z hh (h.fixed 5 0 7) (h.fixed 5 1 7) (by simp [cross,fiber,coord]))

include hB h in
private theorem c1376 : ¬(((z 118).2 = coord 4) ∧ (mark 1 0 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 97 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 7) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1377 : ¬(((z 118).2 = coord 5) ∧ (mark 1 0 7) ∧ (¬((z 97).1 = (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_equal B z hh (h.fixed 5 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1378 : ¬(((z 118).2 = coord 7) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 97).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1379 : ¬(((z 118).2 = coord 8) ∧ (mark 1 0 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 97 118 (by decide +kernel) (by decide +kernel) h2 trivial
  exact impossible B z hh (h.fixed 5 0 7) h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1380 : ¬(((z 119).2 = coord 7) ∧ (mark 1 0 7) ∧ (¬(B.Adj (z 97).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 97 119 (by decide +kernel) (by decide +kernel) h2 trivial
  exact h3 (only_cross B z hh (h.fixed 5 0 7) h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1381 : ¬((mark 1 1 1) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 100).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1382 : ¬(((z 115).2 = coord 2) ∧ (mark 1 1 1) ∧ (¬(B.Adj (z 100).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1383 : ¬(((z 115).2 = coord 3) ∧ (mark 1 1 1) ∧ (¬((z 100).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1384 : ¬((mark 1 1 1) ∧ ((z 115).2 = coord 5) ∧ (¬((z 100).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1385 : ¬((mark 1 1 1) ∧ ((z 115).2 = coord 6) ∧ (¬((z 100).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1386 : ¬((mark 1 1 1) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 100).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 100 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1387 : ¬((mark 1 1 2) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 101).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 101 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 5 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1388 : ¬(((z 115).2 = coord 2) ∧ (mark 1 1 2) ∧ (¬(B.Adj (z 101).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 101 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1389 : ¬(((z 115).2 = coord 3) ∧ (mark 1 1 2) ∧ (¬((z 101).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 101 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1390 : ¬((mark 1 1 2) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 101).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 101 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 5 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1391 : ¬((mark 1 1 2) ∧ ((z 115).2 = coord 7) ∧ (¬((z 101).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 101 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 2) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1392 : ¬((mark 1 1 3) ∧ ((z 115).2 = coord 1) ∧ (¬((z 102).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 102 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1393 : ¬((mark 1 1 3) ∧ ((z 115).2 = coord 2) ∧ (¬((z 102).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 102 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1394 : ¬((mark 1 1 3) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 102).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 102 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_cross B z hh h2 (h.fixed 5 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1395 : ¬((mark 1 1 3) ∧ ((z 115).2 = coord 7) ∧ (¬((z 102).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 102 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 3) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1396 : ¬(((z 115).2 = coord 0) ∧ (mark 1 1 5) ∧ (¬((z 104).1 = (z 115).1)) ∧ (¬(B.Adj (z 104).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 104 (by decide +kernel) (by decide +kernel) trivial h2
  exact (projected B z hh).elim (fun he => h3 he.symm) (fun he => h4 he.symm)

include hB h in
private theorem c1397 : ¬(((z 115).2 = coord 1) ∧ (mark 1 1 5) ∧ (¬((z 104).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 104 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1398 : ¬(((z 115).2 = coord 2) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 104).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 104 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1399 : ¬(((z 115).2 = coord 3) ∧ (mark 1 1 5) ∧ (¬(B.Adj (z 104).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 104 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1400 : ¬(((z 115).2 = coord 7) ∧ (mark 1 1 5) ∧ (¬((z 104).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 104 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 5) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1401 : ¬(((z 115).2 = coord 1) ∧ (mark 1 1 6) ∧ (¬((z 105).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1402 : ¬(((z 115).2 = coord 2) ∧ (mark 1 1 6) ∧ (¬((z 105).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1403 : ¬(((z 115).2 = coord 3) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 105).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1404 : ¬((mark 1 1 6) ∧ ((z 115).2 = coord 5) ∧ (¬((z 105).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 105 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1405 : ¬(((z 115).2 = coord 7) ∧ (mark 1 1 6) ∧ (¬(B.Adj (z 105).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1406 : ¬(((z 115).2 = coord 1) ∧ (mark 1 1 7) ∧ (¬(B.Adj (z 106).1 (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 106 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_cross B z hh h1 (h.fixed 5 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1407 : ¬(((z 115).2 = coord 2) ∧ (mark 1 1 7) ∧ (¬((z 106).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 106 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1408 : ¬(((z 115).2 = coord 3) ∧ (mark 1 1 7) ∧ (¬((z 106).1 = (z 115).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 106 (by decide +kernel) (by decide +kernel) trivial h2
  exact h3 (only_equal B z hh h1 (h.fixed 5 1 7) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1409 : ¬(((z 115).2 = coord 4) ∧ ((z 118).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1410 : ¬(((z 115).2 = coord 0) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1411 : ¬(((z 115).2 = coord 0) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1412 : ¬(((z 115).2 = coord 0) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1413 : ¬(((z 119).2 = coord 5) ∧ ((z 115).2 = coord 0) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1414 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1415 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 0) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1416 : ¬(((z 115).2 = coord 1) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1417 : ¬(((z 115).2 = coord 1) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1418 : ¬(((z 115).2 = coord 1) ∧ ((z 119).2 = coord 3) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1419 : ¬(((z 115).2 = coord 1) ∧ ((z 119).2 = coord 5) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1420 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 1) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1421 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1422 : ¬(((z 115).2 = coord 2) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1423 : ¬(((z 115).2 = coord 2) ∧ ((z 119).2 = coord 2) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1424 : ¬(((z 115).2 = coord 2) ∧ ((z 119).2 = coord 3) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1425 : ¬(((z 115).2 = coord 2) ∧ ((z 119).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1426 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 2) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1427 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 2) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1428 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 1) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1429 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 2) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1430 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 3) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1431 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1432 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1433 : ¬(((z 115).2 = coord 3) ∧ ((z 119).2 = coord 7) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1434 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1435 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 2) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1436 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1437 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1438 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 6) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1439 : ¬(((z 115).2 = coord 4) ∧ ((z 119).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1440 : ¬(((z 119).2 = coord 2) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1441 : ¬(((z 119).2 = coord 3) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1442 : ¬(((z 119).2 = coord 5) ∧ ((z 115).2 = coord 5) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1443 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1444 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 5) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1445 : ¬(((z 119).2 = coord 2) ∧ ((z 115).2 = coord 6) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1446 : ¬(((z 119).2 = coord 3) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1447 : ¬(((z 119).2 = coord 5) ∧ ((z 115).2 = coord 6) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1448 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1449 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 6) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1450 : ¬(((z 115).2 = coord 7) ∧ ((z 119).2 = coord 1) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1451 : ¬(((z 115).2 = coord 7) ∧ ((z 119).2 = coord 2) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1452 : ¬(((z 115).2 = coord 7) ∧ ((z 119).2 = coord 3) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1453 : ¬(((z 119).2 = coord 5) ∧ ((z 115).2 = coord 7) ∧ (¬((z 115).1 = (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_equal B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1454 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1455 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 7) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h2 h1 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1456 : ¬(((z 115).2 = coord 8) ∧ ((z 119).2 = coord 1) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1457 : ¬(((z 115).2 = coord 8) ∧ ((z 119).2 = coord 2)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1458 : ¬(((z 115).2 = coord 8) ∧ ((z 119).2 = coord 3) ∧ (¬((z 115).1 = (z 119).1)) ∧ (¬(B.Adj (z 115).1 (z 119).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1459 : ¬(((z 119).2 = coord 5) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1460 : ¬(((z 119).2 = coord 6) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1461 : ¬(((z 119).2 = coord 7) ∧ ((z 115).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 115 119 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1462 : ¬(((z 117).2 = coord 0) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 99 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1463 : ¬(((z 117).2 = coord 1) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 99 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1464 : ¬(((z 117).2 = coord 2) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 99 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1465 : ¬((mark 1 1 0) ∧ ((z 117).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 99 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 5 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1466 : ¬(((z 117).2 = coord 6) ∧ (mark 1 1 0)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 99 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 0) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1467 : ¬((mark 1 1 1) ∧ ((z 117).2 = coord 3) ∧ (¬((z 100).1 = (z 117).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 117 100 (by decide +kernel) (by decide +kernel) trivial h1
  exact h3 (only_equal B z hh h2 (h.fixed 5 1 1) (by simp [cross,fiber,coord])).symm

include hB h in
private theorem c1468 : ¬((mark 1 1 4) ∧ ((z 117).2 = coord 1)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 103 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 5 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1469 : ¬((mark 1 1 4) ∧ ((z 117).2 = coord 3)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 103 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 5 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1470 : ¬((mark 1 1 4) ∧ ((z 117).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 103 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 5 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1471 : ¬((mark 1 1 4) ∧ ((z 117).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 103 (by decide +kernel) (by decide +kernel) trivial h1
  exact impossible B z hh h2 (h.fixed 5 1 4) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1472 : ¬(((z 117).2 = coord 0) ∧ (mark 1 1 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1473 : ¬(((z 117).2 = coord 8) ∧ (mark 1 1 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 105 (by decide +kernel) (by decide +kernel) trivial h2
  exact impossible B z hh h1 (h.fixed 5 1 6) (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1474 : ¬(((z 117).2 = coord 1) ∧ ((z 118).2 = coord 8) ∧ (¬((z 117).1 = (z 118).1)) ∧ (¬(B.Adj (z 117).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3,h4⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact (projected B z hh).elim h3 h4

include hB h in
private theorem c1475 : ¬(((z 117).2 = coord 2) ∧ ((z 118).2 = coord 1) ∧ (¬(B.Adj (z 117).1 (z 118).1))) := by
  classical
  rintro ⟨h1,h2,h3⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact h3 (only_cross B z hh h1 h2 (by simp [cross,fiber,coord]))

include hB h in
private theorem c1476 : ¬(((z 117).2 = coord 2) ∧ ((z 118).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h1 h2 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1477 : ¬(((z 118).2 = coord 1) ∧ ((z 117).2 = coord 4)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1478 : ¬(((z 118).2 = coord 8) ∧ ((z 117).2 = coord 5)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1479 : ¬(((z 118).2 = coord 0) ∧ ((z 117).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1480 : ¬(((z 118).2 = coord 8) ∧ ((z 117).2 = coord 6)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1481 : ¬(((z 118).2 = coord 8) ∧ ((z 117).2 = coord 7)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
private theorem c1482 : ¬(((z 118).2 = coord 8) ∧ ((z 117).2 = coord 8)) := by
  classical
  rintro ⟨h1,h2⟩
  have hh := h.edge 5 117 118 (by decide +kernel) (by decide +kernel) trivial trivial
  exact impossible B z hh h2 h1 (by simp [cross,fiber,coord]) (by simp [cross,fiber,coord])

include hB h in
theorem no_pattern : False := by
  classical
  have hh := Erdos595UniversalProfileSAT.finite_obstruction
    ((z 55).1 = (z 66).1)
    ((z 55).1 = (z 82).1)
    ((z 55).1 = (z 114).1)
    ((z 55).1 = (z 115).1)
    ((z 56).1 = (z 66).1)
    ((z 56).1 = (z 83).1)
    ((z 56).1 = (z 114).1)
    ((z 56).1 = (z 115).1)
    ((z 57).1 = (z 64).1)
    ((z 57).1 = (z 70).1)
    ((z 57).1 = (z 84).1)
    ((z 57).1 = (z 114).1)
    ((z 57).1 = (z 115).1)
    ((z 57).1 = (z 116).1)
    ((z 57).1 = (z 119).1)
    ((z 59).1 = (z 114).1)
    ((z 59).1 = (z 115).1)
    ((z 59).1 = (z 119).1)
    ((z 60).1 = (z 68).1)
    ((z 60).1 = (z 87).1)
    ((z 60).1 = (z 105).1)
    ((z 60).1 = (z 114).1)
    ((z 60).1 = (z 115).1)
    ((z 60).1 = (z 118).1)
    ((z 60).1 = (z 119).1)
    ((z 61).1 = (z 65).1)
    ((z 61).1 = (z 66).1)
    ((z 61).1 = (z 68).1)
    ((z 61).1 = (z 95).1)
    ((z 61).1 = (z 114).1)
    ((z 61).1 = (z 115).1)
    ((z 61).1 = (z 116).1)
    ((z 61).1 = (z 119).1)
    ((z 64).1 = (z 73).1)
    ((z 64).1 = (z 84).1)
    ((z 64).1 = (z 91).1)
    ((z 64).1 = (z 116).1)
    ((z 64).1 = (z 118).1)
    ((z 64).1 = (z 119).1)
    ((z 65).1 = (z 116).1)
    ((z 65).1 = (z 118).1)
    ((z 66).1 = (z 75).1)
    ((z 66).1 = (z 82).1)
    ((z 66).1 = (z 96).1)
    ((z 66).1 = (z 114).1)
    ((z 66).1 = (z 116).1)
    ((z 66).1 = (z 118).1)
    ((z 66).1 = (z 119).1)
    ((z 68).1 = (z 95).1)
    ((z 68).1 = (z 116).1)
    ((z 68).1 = (z 118).1)
    ((z 69).1 = (z 116).1)
    ((z 69).1 = (z 118).1)
    ((z 70).1 = (z 116).1)
    ((z 70).1 = (z 118).1)
    ((z 73).1 = (z 84).1)
    ((z 73).1 = (z 86).1)
    ((z 73).1 = (z 87).1)
    ((z 73).1 = (z 105).1)
    ((z 73).1 = (z 116).1)
    ((z 73).1 = (z 117).1)
    ((z 73).1 = (z 119).1)
    ((z 74).1 = (z 116).1)
    ((z 75).1 = (z 82).1)
    ((z 75).1 = (z 83).1)
    ((z 75).1 = (z 88).1)
    ((z 75).1 = (z 116).1)
    ((z 75).1 = (z 119).1)
    ((z 77).1 = (z 82).1)
    ((z 77).1 = (z 87).1)
    ((z 77).1 = (z 116).1)
    ((z 77).1 = (z 119).1)
    ((z 78).1 = (z 82).1)
    ((z 78).1 = (z 86).1)
    ((z 78).1 = (z 96).1)
    ((z 78).1 = (z 115).1)
    ((z 78).1 = (z 116).1)
    ((z 78).1 = (z 119).1)
    ((z 79).1 = (z 84).1)
    ((z 79).1 = (z 116).1)
    ((z 82).1 = (z 114).1)
    ((z 82).1 = (z 115).1)
    ((z 82).1 = (z 119).1)
    ((z 83).1 = (z 93).1)
    ((z 83).1 = (z 114).1)
    ((z 83).1 = (z 119).1)
    ((z 84).1 = (z 100).1)
    ((z 84).1 = (z 114).1)
    ((z 84).1 = (z 116).1)
    ((z 84).1 = (z 119).1)
    ((z 86).1 = (z 114).1)
    ((z 86).1 = (z 119).1)
    ((z 87).1 = (z 114).1)
    ((z 88).1 = (z 93).1)
    ((z 88).1 = (z 114).1)
    ((z 88).1 = (z 116).1)
    ((z 88).1 = (z 119).1)
    ((z 91).1 = (z 102).1)
    ((z 91).1 = (z 105).1)
    ((z 91).1 = (z 114).1)
    ((z 91).1 = (z 116).1)
    ((z 91).1 = (z 118).1)
    ((z 91).1 = (z 119).1)
    ((z 92).1 = (z 102).1)
    ((z 92).1 = (z 105).1)
    ((z 92).1 = (z 106).1)
    ((z 92).1 = (z 116).1)
    ((z 92).1 = (z 118).1)
    ((z 92).1 = (z 119).1)
    ((z 93).1 = (z 100).1)
    ((z 93).1 = (z 101).1)
    ((z 93).1 = (z 106).1)
    ((z 93).1 = (z 114).1)
    ((z 93).1 = (z 115).1)
    ((z 93).1 = (z 116).1)
    ((z 93).1 = (z 118).1)
    ((z 93).1 = (z 119).1)
    ((z 95).1 = (z 100).1)
    ((z 95).1 = (z 105).1)
    ((z 95).1 = (z 114).1)
    ((z 95).1 = (z 116).1)
    ((z 95).1 = (z 118).1)
    ((z 95).1 = (z 119).1)
    ((z 96).1 = (z 100).1)
    ((z 96).1 = (z 101).1)
    ((z 96).1 = (z 104).1)
    ((z 96).1 = (z 115).1)
    ((z 96).1 = (z 116).1)
    ((z 96).1 = (z 118).1)
    ((z 96).1 = (z 119).1)
    ((z 97).1 = (z 102).1)
    ((z 97).1 = (z 115).1)
    ((z 97).1 = (z 118).1)
    ((z 97).1 = (z 119).1)
    ((z 100).1 = (z 115).1)
    ((z 100).1 = (z 116).1)
    ((z 100).1 = (z 117).1)
    ((z 100).1 = (z 119).1)
    ((z 101).1 = (z 115).1)
    ((z 101).1 = (z 116).1)
    ((z 101).1 = (z 119).1)
    ((z 102).1 = (z 115).1)
    ((z 102).1 = (z 116).1)
    ((z 104).1 = (z 115).1)
    ((z 104).1 = (z 116).1)
    ((z 105).1 = (z 115).1)
    ((z 105).1 = (z 116).1)
    ((z 106).1 = (z 115).1)
    ((z 106).1 = (z 116).1)
    ((z 106).1 = (z 119).1)
    ((z 114).1 = (z 115).1)
    ((z 114).1 = (z 116).1)
    ((z 114).1 = (z 118).1)
    ((z 114).1 = (z 119).1)
    ((z 115).1 = (z 116).1)
    ((z 115).1 = (z 118).1)
    ((z 115).1 = (z 119).1)
    ((z 116).1 = (z 119).1)
    ((z 117).1 = (z 118).1)
    ((z 117).1 = (z 119).1)
    (B.Adj (z 55).1 (z 73).1)
    (B.Adj (z 55).1 (z 114).1)
    (B.Adj (z 55).1 (z 115).1)
    (B.Adj (z 55).1 (z 118).1)
    (B.Adj (z 55).1 (z 119).1)
    (B.Adj (z 56).1 (z 64).1)
    (B.Adj (z 56).1 (z 73).1)
    (B.Adj (z 56).1 (z 87).1)
    (B.Adj (z 56).1 (z 114).1)
    (B.Adj (z 56).1 (z 115).1)
    (B.Adj (z 56).1 (z 116).1)
    (B.Adj (z 56).1 (z 119).1)
    (B.Adj (z 57).1 (z 66).1)
    (B.Adj (z 57).1 (z 82).1)
    (B.Adj (z 57).1 (z 101).1)
    (B.Adj (z 57).1 (z 114).1)
    (B.Adj (z 57).1 (z 115).1)
    (B.Adj (z 57).1 (z 119).1)
    (B.Adj (z 59).1 (z 65).1)
    (B.Adj (z 59).1 (z 66).1)
    (B.Adj (z 59).1 (z 79).1)
    (B.Adj (z 59).1 (z 86).1)
    (B.Adj (z 59).1 (z 88).1)
    (B.Adj (z 59).1 (z 114).1)
    (B.Adj (z 59).1 (z 115).1)
    (B.Adj (z 59).1 (z 116).1)
    (B.Adj (z 59).1 (z 117).1)
    (B.Adj (z 59).1 (z 119).1)
    (B.Adj (z 60).1 (z 66).1)
    (B.Adj (z 60).1 (z 68).1)
    (B.Adj (z 60).1 (z 70).1)
    (B.Adj (z 60).1 (z 83).1)
    (B.Adj (z 60).1 (z 87).1)
    (B.Adj (z 60).1 (z 114).1)
    (B.Adj (z 60).1 (z 115).1)
    (B.Adj (z 60).1 (z 119).1)
    (B.Adj (z 61).1 (z 68).1)
    (B.Adj (z 61).1 (z 70).1)
    (B.Adj (z 61).1 (z 73).1)
    (B.Adj (z 61).1 (z 75).1)
    (B.Adj (z 61).1 (z 86).1)
    (B.Adj (z 61).1 (z 114).1)
    (B.Adj (z 61).1 (z 115).1)
    (B.Adj (z 61).1 (z 116).1)
    (B.Adj (z 61).1 (z 119).1)
    (B.Adj (z 64).1 (z 84).1)
    (B.Adj (z 64).1 (z 91).1)
    (B.Adj (z 64).1 (z 93).1)
    (B.Adj (z 64).1 (z 115).1)
    (B.Adj (z 64).1 (z 116).1)
    (B.Adj (z 64).1 (z 118).1)
    (B.Adj (z 64).1 (z 119).1)
    (B.Adj (z 65).1 (z 116).1)
    (B.Adj (z 65).1 (z 118).1)
    (B.Adj (z 65).1 (z 119).1)
    (B.Adj (z 66).1 (z 73).1)
    (B.Adj (z 66).1 (z 75).1)
    (B.Adj (z 66).1 (z 82).1)
    (B.Adj (z 66).1 (z 91).1)
    (B.Adj (z 66).1 (z 92).1)
    (B.Adj (z 66).1 (z 93).1)
    (B.Adj (z 66).1 (z 114).1)
    (B.Adj (z 66).1 (z 115).1)
    (B.Adj (z 66).1 (z 116).1)
    (B.Adj (z 66).1 (z 118).1)
    (B.Adj (z 66).1 (z 119).1)
    (B.Adj (z 68).1 (z 95).1)
    (B.Adj (z 68).1 (z 97).1)
    (B.Adj (z 68).1 (z 115).1)
    (B.Adj (z 68).1 (z 116).1)
    (B.Adj (z 68).1 (z 118).1)
    (B.Adj (z 68).1 (z 119).1)
    (B.Adj (z 69).1 (z 92).1)
    (B.Adj (z 69).1 (z 116).1)
    (B.Adj (z 69).1 (z 118).1)
    (B.Adj (z 70).1 (z 95).1)
    (B.Adj (z 70).1 (z 116).1)
    (B.Adj (z 70).1 (z 118).1)
    (B.Adj (z 70).1 (z 119).1)
    (B.Adj (z 73).1 (z 82).1)
    (B.Adj (z 73).1 (z 83).1)
    (B.Adj (z 73).1 (z 88).1)
    (B.Adj (z 73).1 (z 91).1)
    (B.Adj (z 73).1 (z 115).1)
    (B.Adj (z 73).1 (z 116).1)
    (B.Adj (z 73).1 (z 119).1)
    (B.Adj (z 74).1 (z 82).1)
    (B.Adj (z 74).1 (z 116).1)
    (B.Adj (z 74).1 (z 119).1)
    (B.Adj (z 75).1 (z 77).1)
    (B.Adj (z 75).1 (z 82).1)
    (B.Adj (z 75).1 (z 84).1)
    (B.Adj (z 75).1 (z 86).1)
    (B.Adj (z 75).1 (z 87).1)
    (B.Adj (z 75).1 (z 114).1)
    (B.Adj (z 75).1 (z 115).1)
    (B.Adj (z 75).1 (z 116).1)
    (B.Adj (z 75).1 (z 119).1)
    (B.Adj (z 77).1 (z 82).1)
    (B.Adj (z 77).1 (z 84).1)
    (B.Adj (z 77).1 (z 116).1)
    (B.Adj (z 77).1 (z 119).1)
    (B.Adj (z 78).1 (z 82).1)
    (B.Adj (z 78).1 (z 84).1)
    (B.Adj (z 78).1 (z 86).1)
    (B.Adj (z 78).1 (z 87).1)
    (B.Adj (z 78).1 (z 88).1)
    (B.Adj (z 78).1 (z 96).1)
    (B.Adj (z 78).1 (z 116).1)
    (B.Adj (z 78).1 (z 119).1)
    (B.Adj (z 79).1 (z 82).1)
    (B.Adj (z 79).1 (z 88).1)
    (B.Adj (z 79).1 (z 115).1)
    (B.Adj (z 79).1 (z 116).1)
    (B.Adj (z 79).1 (z 117).1)
    (B.Adj (z 79).1 (z 119).1)
    (B.Adj (z 82).1 (z 91).1)
    (B.Adj (z 82).1 (z 96).1)
    (B.Adj (z 82).1 (z 100).1)
    (B.Adj (z 82).1 (z 114).1)
    (B.Adj (z 82).1 (z 115).1)
    (B.Adj (z 82).1 (z 116).1)
    (B.Adj (z 82).1 (z 117).1)
    (B.Adj (z 82).1 (z 118).1)
    (B.Adj (z 82).1 (z 119).1)
    (B.Adj (z 83).1 (z 93).1)
    (B.Adj (z 83).1 (z 114).1)
    (B.Adj (z 83).1 (z 115).1)
    (B.Adj (z 83).1 (z 116).1)
    (B.Adj (z 83).1 (z 119).1)
    (B.Adj (z 84).1 (z 91).1)
    (B.Adj (z 84).1 (z 93).1)
    (B.Adj (z 84).1 (z 95).1)
    (B.Adj (z 84).1 (z 114).1)
    (B.Adj (z 84).1 (z 115).1)
    (B.Adj (z 84).1 (z 116).1)
    (B.Adj (z 84).1 (z 119).1)
    (B.Adj (z 86).1 (z 91).1)
    (B.Adj (z 86).1 (z 96).1)
    (B.Adj (z 86).1 (z 114).1)
    (B.Adj (z 86).1 (z 115).1)
    (B.Adj (z 86).1 (z 116).1)
    (B.Adj (z 86).1 (z 119).1)
    (B.Adj (z 87).1 (z 92).1)
    (B.Adj (z 87).1 (z 93).1)
    (B.Adj (z 87).1 (z 96).1)
    (B.Adj (z 87).1 (z 105).1)
    (B.Adj (z 87).1 (z 114).1)
    (B.Adj (z 87).1 (z 115).1)
    (B.Adj (z 87).1 (z 119).1)
    (B.Adj (z 88).1 (z 114).1)
    (B.Adj (z 88).1 (z 115).1)
    (B.Adj (z 88).1 (z 116).1)
    (B.Adj (z 88).1 (z 119).1)
    (B.Adj (z 91).1 (z 92).1)
    (B.Adj (z 91).1 (z 100).1)
    (B.Adj (z 91).1 (z 101).1)
    (B.Adj (z 91).1 (z 102).1)
    (B.Adj (z 91).1 (z 105).1)
    (B.Adj (z 91).1 (z 115).1)
    (B.Adj (z 91).1 (z 116).1)
    (B.Adj (z 91).1 (z 118).1)
    (B.Adj (z 91).1 (z 119).1)
    (B.Adj (z 92).1 (z 100).1)
    (B.Adj (z 92).1 (z 101).1)
    (B.Adj (z 92).1 (z 104).1)
    (B.Adj (z 92).1 (z 105).1)
    (B.Adj (z 92).1 (z 115).1)
    (B.Adj (z 92).1 (z 116).1)
    (B.Adj (z 92).1 (z 118).1)
    (B.Adj (z 92).1 (z 119).1)
    (B.Adj (z 93).1 (z 102).1)
    (B.Adj (z 93).1 (z 104).1)
    (B.Adj (z 93).1 (z 105).1)
    (B.Adj (z 93).1 (z 115).1)
    (B.Adj (z 93).1 (z 116).1)
    (B.Adj (z 93).1 (z 118).1)
    (B.Adj (z 93).1 (z 119).1)
    (B.Adj (z 95).1 (z 101).1)
    (B.Adj (z 95).1 (z 102).1)
    (B.Adj (z 95).1 (z 115).1)
    (B.Adj (z 95).1 (z 116).1)
    (B.Adj (z 95).1 (z 118).1)
    (B.Adj (z 95).1 (z 119).1)
    (B.Adj (z 96).1 (z 102).1)
    (B.Adj (z 96).1 (z 105).1)
    (B.Adj (z 96).1 (z 106).1)
    (B.Adj (z 96).1 (z 115).1)
    (B.Adj (z 96).1 (z 116).1)
    (B.Adj (z 96).1 (z 118).1)
    (B.Adj (z 96).1 (z 119).1)
    (B.Adj (z 97).1 (z 100).1)
    (B.Adj (z 97).1 (z 105).1)
    (B.Adj (z 97).1 (z 106).1)
    (B.Adj (z 97).1 (z 115).1)
    (B.Adj (z 97).1 (z 116).1)
    (B.Adj (z 97).1 (z 118).1)
    (B.Adj (z 97).1 (z 119).1)
    (B.Adj (z 100).1 (z 104).1)
    (B.Adj (z 100).1 (z 115).1)
    (B.Adj (z 100).1 (z 116).1)
    (B.Adj (z 100).1 (z 118).1)
    (B.Adj (z 100).1 (z 119).1)
    (B.Adj (z 101).1 (z 115).1)
    (B.Adj (z 101).1 (z 116).1)
    (B.Adj (z 101).1 (z 119).1)
    (B.Adj (z 102).1 (z 105).1)
    (B.Adj (z 102).1 (z 115).1)
    (B.Adj (z 102).1 (z 116).1)
    (B.Adj (z 102).1 (z 119).1)
    (B.Adj (z 104).1 (z 115).1)
    (B.Adj (z 104).1 (z 116).1)
    (B.Adj (z 104).1 (z 119).1)
    (B.Adj (z 105).1 (z 115).1)
    (B.Adj (z 105).1 (z 116).1)
    (B.Adj (z 105).1 (z 119).1)
    (B.Adj (z 106).1 (z 115).1)
    (B.Adj (z 106).1 (z 119).1)
    (B.Adj (z 114).1 (z 115).1)
    (B.Adj (z 114).1 (z 116).1)
    (B.Adj (z 114).1 (z 117).1)
    (B.Adj (z 114).1 (z 118).1)
    (B.Adj (z 114).1 (z 119).1)
    (B.Adj (z 115).1 (z 116).1)
    (B.Adj (z 115).1 (z 118).1)
    (B.Adj (z 115).1 (z 119).1)
    (B.Adj (z 116).1 (z 118).1)
    (B.Adj (z 116).1 (z 119).1)
    (B.Adj (z 117).1 (z 118).1)
    (B.Adj (z 117).1 (z 119).1)
    (B.Adj (z 118).1 (z 119).1)
    (mark 0 0 0)
    (mark 0 0 1)
    (mark 0 0 2)
    (mark 0 0 3)
    (mark 0 0 4)
    (mark 0 0 5)
    (mark 0 0 6)
    (mark 0 0 7)
    (mark 0 0 8)
    (mark 0 1 0)
    (mark 0 1 1)
    (mark 0 1 2)
    (mark 0 1 3)
    (mark 0 1 4)
    (mark 0 1 5)
    (mark 0 1 6)
    (mark 0 1 7)
    (mark 0 1 8)
    (mark 1 0 1)
    (mark 1 0 2)
    (mark 1 0 3)
    (mark 1 0 4)
    (mark 1 0 5)
    (mark 1 0 6)
    (mark 1 0 7)
    (mark 1 1 0)
    (mark 1 1 1)
    (mark 1 1 2)
    (mark 1 1 3)
    (mark 1 1 4)
    (mark 1 1 5)
    (mark 1 1 6)
    (mark 1 1 7)
    (mark 1 1 8)
    ((z 108).2 = coord 0)
    ((z 108).2 = coord 1)
    ((z 108).2 = coord 2)
    ((z 108).2 = coord 3)
    ((z 108).2 = coord 4)
    ((z 108).2 = coord 5)
    ((z 108).2 = coord 6)
    ((z 108).2 = coord 7)
    ((z 108).2 = coord 8)
    ((z 110).2 = coord 0)
    ((z 110).2 = coord 1)
    ((z 110).2 = coord 2)
    ((z 110).2 = coord 3)
    ((z 110).2 = coord 4)
    ((z 110).2 = coord 5)
    ((z 110).2 = coord 6)
    ((z 110).2 = coord 7)
    ((z 110).2 = coord 8)
    ((z 114).2 = coord 0)
    ((z 114).2 = coord 1)
    ((z 114).2 = coord 2)
    ((z 114).2 = coord 3)
    ((z 114).2 = coord 4)
    ((z 114).2 = coord 5)
    ((z 114).2 = coord 6)
    ((z 114).2 = coord 7)
    ((z 114).2 = coord 8)
    ((z 115).2 = coord 0)
    ((z 115).2 = coord 1)
    ((z 115).2 = coord 2)
    ((z 115).2 = coord 3)
    ((z 115).2 = coord 4)
    ((z 115).2 = coord 5)
    ((z 115).2 = coord 6)
    ((z 115).2 = coord 7)
    ((z 115).2 = coord 8)
    ((z 116).2 = coord 0)
    ((z 116).2 = coord 1)
    ((z 116).2 = coord 2)
    ((z 116).2 = coord 3)
    ((z 116).2 = coord 4)
    ((z 116).2 = coord 5)
    ((z 116).2 = coord 6)
    ((z 116).2 = coord 7)
    ((z 116).2 = coord 8)
    ((z 117).2 = coord 0)
    ((z 117).2 = coord 1)
    ((z 117).2 = coord 2)
    ((z 117).2 = coord 3)
    ((z 117).2 = coord 4)
    ((z 117).2 = coord 5)
    ((z 117).2 = coord 6)
    ((z 117).2 = coord 7)
    ((z 117).2 = coord 8)
    ((z 118).2 = coord 0)
    ((z 118).2 = coord 1)
    ((z 118).2 = coord 2)
    ((z 118).2 = coord 3)
    ((z 118).2 = coord 4)
    ((z 118).2 = coord 5)
    ((z 118).2 = coord 6)
    ((z 118).2 = coord 7)
    ((z 118).2 = coord 8)
    ((z 119).2 = coord 0)
    ((z 119).2 = coord 1)
    ((z 119).2 = coord 2)
    ((z 119).2 = coord 3)
    ((z 119).2 = coord 4)
    ((z 119).2 = coord 5)
    ((z 119).2 = coord 6)
    ((z 119).2 = coord 7)
    ((z 119).2 = coord 8)
  exact (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c0 B z mark hB h) (c1 B z mark hB h)) (fun hh => hh.elim (c2 B z mark hB h) (fun hh => hh.elim (c3 B z mark hB h) (c4 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c5 B z mark hB h) (fun hh => hh.elim (c6 B z mark hB h) (c7 B z mark hB h))) (fun hh => hh.elim (c8 B z mark hB h) (fun hh => hh.elim (c9 B z mark hB h) (c10 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c11 B z mark hB h) (fun hh => hh.elim (c12 B z mark hB h) (c13 B z mark hB h))) (fun hh => hh.elim (c14 B z mark hB h) (fun hh => hh.elim (c15 B z mark hB h) (c16 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c17 B z mark hB h) (fun hh => hh.elim (c18 B z mark hB h) (c19 B z mark hB h))) (fun hh => hh.elim (c20 B z mark hB h) (fun hh => hh.elim (c21 B z mark hB h) (c22 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c23 B z mark hB h) (c24 B z mark hB h)) (fun hh => hh.elim (c25 B z mark hB h) (fun hh => hh.elim (c26 B z mark hB h) (c27 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c28 B z mark hB h) (fun hh => hh.elim (c29 B z mark hB h) (c30 B z mark hB h))) (fun hh => hh.elim (c31 B z mark hB h) (fun hh => hh.elim (c32 B z mark hB h) (c33 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c34 B z mark hB h) (fun hh => hh.elim (c35 B z mark hB h) (c36 B z mark hB h))) (fun hh => hh.elim (c37 B z mark hB h) (fun hh => hh.elim (c38 B z mark hB h) (c39 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c40 B z mark hB h) (fun hh => hh.elim (c41 B z mark hB h) (c42 B z mark hB h))) (fun hh => hh.elim (c43 B z mark hB h) (fun hh => hh.elim (c44 B z mark hB h) (c45 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c46 B z mark hB h) (c47 B z mark hB h)) (fun hh => hh.elim (c48 B z mark hB h) (fun hh => hh.elim (c49 B z mark hB h) (c50 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c51 B z mark hB h) (fun hh => hh.elim (c52 B z mark hB h) (c53 B z mark hB h))) (fun hh => hh.elim (c54 B z mark hB h) (fun hh => hh.elim (c55 B z mark hB h) (c56 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c57 B z mark hB h) (fun hh => hh.elim (c58 B z mark hB h) (c59 B z mark hB h))) (fun hh => hh.elim (c60 B z mark hB h) (fun hh => hh.elim (c61 B z mark hB h) (c62 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c63 B z mark hB h) (fun hh => hh.elim (c64 B z mark hB h) (c65 B z mark hB h))) (fun hh => hh.elim (c66 B z mark hB h) (fun hh => hh.elim (c67 B z mark hB h) (c68 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c69 B z mark hB h) (c70 B z mark hB h)) (fun hh => hh.elim (c71 B z mark hB h) (fun hh => hh.elim (c72 B z mark hB h) (c73 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c74 B z mark hB h) (fun hh => hh.elim (c75 B z mark hB h) (c76 B z mark hB h))) (fun hh => hh.elim (c77 B z mark hB h) (fun hh => hh.elim (c78 B z mark hB h) (c79 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c80 B z mark hB h) (fun hh => hh.elim (c81 B z mark hB h) (c82 B z mark hB h))) (fun hh => hh.elim (c83 B z mark hB h) (fun hh => hh.elim (c84 B z mark hB h) (c85 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c86 B z mark hB h) (fun hh => hh.elim (c87 B z mark hB h) (c88 B z mark hB h))) (fun hh => hh.elim (c89 B z mark hB h) (fun hh => hh.elim (c90 B z mark hB h) (c91 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c92 B z mark hB h) (c93 B z mark hB h)) (fun hh => hh.elim (c94 B z mark hB h) (fun hh => hh.elim (c95 B z mark hB h) (c96 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c97 B z mark hB h) (fun hh => hh.elim (c98 B z mark hB h) (c99 B z mark hB h))) (fun hh => hh.elim (c100 B z mark hB h) (fun hh => hh.elim (c101 B z mark hB h) (c102 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c103 B z mark hB h) (fun hh => hh.elim (c104 B z mark hB h) (c105 B z mark hB h))) (fun hh => hh.elim (c106 B z mark hB h) (fun hh => hh.elim (c107 B z mark hB h) (c108 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c109 B z mark hB h) (fun hh => hh.elim (c110 B z mark hB h) (c111 B z mark hB h))) (fun hh => hh.elim (c112 B z mark hB h) (fun hh => hh.elim (c113 B z mark hB h) (c114 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c115 B z mark hB h) (c116 B z mark hB h)) (fun hh => hh.elim (c117 B z mark hB h) (fun hh => hh.elim (c118 B z mark hB h) (c119 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c120 B z mark hB h) (fun hh => hh.elim (c121 B z mark hB h) (c122 B z mark hB h))) (fun hh => hh.elim (c123 B z mark hB h) (fun hh => hh.elim (c124 B z mark hB h) (c125 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c126 B z mark hB h) (fun hh => hh.elim (c127 B z mark hB h) (c128 B z mark hB h))) (fun hh => hh.elim (c129 B z mark hB h) (fun hh => hh.elim (c130 B z mark hB h) (c131 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c132 B z mark hB h) (fun hh => hh.elim (c133 B z mark hB h) (c134 B z mark hB h))) (fun hh => hh.elim (c135 B z mark hB h) (fun hh => hh.elim (c136 B z mark hB h) (c137 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c138 B z mark hB h) (c139 B z mark hB h)) (fun hh => hh.elim (c140 B z mark hB h) (fun hh => hh.elim (c141 B z mark hB h) (c142 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c143 B z mark hB h) (fun hh => hh.elim (c144 B z mark hB h) (c145 B z mark hB h))) (fun hh => hh.elim (c146 B z mark hB h) (fun hh => hh.elim (c147 B z mark hB h) (c148 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c149 B z mark hB h) (fun hh => hh.elim (c150 B z mark hB h) (c151 B z mark hB h))) (fun hh => hh.elim (c152 B z mark hB h) (fun hh => hh.elim (c153 B z mark hB h) (c154 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c155 B z mark hB h) (fun hh => hh.elim (c156 B z mark hB h) (c157 B z mark hB h))) (fun hh => hh.elim (c158 B z mark hB h) (fun hh => hh.elim (c159 B z mark hB h) (c160 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c161 B z mark hB h) (fun hh => hh.elim (c162 B z mark hB h) (c163 B z mark hB h))) (fun hh => hh.elim (c164 B z mark hB h) (fun hh => hh.elim (c165 B z mark hB h) (c166 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c167 B z mark hB h) (fun hh => hh.elim (c168 B z mark hB h) (c169 B z mark hB h))) (fun hh => hh.elim (c170 B z mark hB h) (fun hh => hh.elim (c171 B z mark hB h) (c172 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c173 B z mark hB h) (fun hh => hh.elim (c174 B z mark hB h) (c175 B z mark hB h))) (fun hh => hh.elim (c176 B z mark hB h) (fun hh => hh.elim (c177 B z mark hB h) (c178 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c179 B z mark hB h) (fun hh => hh.elim (c180 B z mark hB h) (c181 B z mark hB h))) (fun hh => hh.elim (c182 B z mark hB h) (fun hh => hh.elim (c183 B z mark hB h) (c184 B z mark hB h))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c185 B z mark hB h) (c186 B z mark hB h)) (fun hh => hh.elim (c187 B z mark hB h) (fun hh => hh.elim (c188 B z mark hB h) (c189 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c190 B z mark hB h) (fun hh => hh.elim (c191 B z mark hB h) (c192 B z mark hB h))) (fun hh => hh.elim (c193 B z mark hB h) (fun hh => hh.elim (c194 B z mark hB h) (c195 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c196 B z mark hB h) (fun hh => hh.elim (c197 B z mark hB h) (c198 B z mark hB h))) (fun hh => hh.elim (c199 B z mark hB h) (fun hh => hh.elim (c200 B z mark hB h) (c201 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c202 B z mark hB h) (fun hh => hh.elim (c203 B z mark hB h) (c204 B z mark hB h))) (fun hh => hh.elim (c205 B z mark hB h) (fun hh => hh.elim (c206 B z mark hB h) (c207 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c208 B z mark hB h) (c209 B z mark hB h)) (fun hh => hh.elim (c210 B z mark hB h) (fun hh => hh.elim (c211 B z mark hB h) (c212 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c213 B z mark hB h) (fun hh => hh.elim (c214 B z mark hB h) (c215 B z mark hB h))) (fun hh => hh.elim (c216 B z mark hB h) (fun hh => hh.elim (c217 B z mark hB h) (c218 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c219 B z mark hB h) (fun hh => hh.elim (c220 B z mark hB h) (c221 B z mark hB h))) (fun hh => hh.elim (c222 B z mark hB h) (fun hh => hh.elim (c223 B z mark hB h) (c224 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c225 B z mark hB h) (fun hh => hh.elim (c226 B z mark hB h) (c227 B z mark hB h))) (fun hh => hh.elim (c228 B z mark hB h) (fun hh => hh.elim (c229 B z mark hB h) (c230 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c231 B z mark hB h) (c232 B z mark hB h)) (fun hh => hh.elim (c233 B z mark hB h) (fun hh => hh.elim (c234 B z mark hB h) (c235 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c236 B z mark hB h) (fun hh => hh.elim (c237 B z mark hB h) (c238 B z mark hB h))) (fun hh => hh.elim (c239 B z mark hB h) (fun hh => hh.elim (c240 B z mark hB h) (c241 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c242 B z mark hB h) (fun hh => hh.elim (c243 B z mark hB h) (c244 B z mark hB h))) (fun hh => hh.elim (c245 B z mark hB h) (fun hh => hh.elim (c246 B z mark hB h) (c247 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c248 B z mark hB h) (fun hh => hh.elim (c249 B z mark hB h) (c250 B z mark hB h))) (fun hh => hh.elim (c251 B z mark hB h) (fun hh => hh.elim (c252 B z mark hB h) (c253 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c254 B z mark hB h) (c255 B z mark hB h)) (fun hh => hh.elim (c256 B z mark hB h) (fun hh => hh.elim (c257 B z mark hB h) (c258 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c259 B z mark hB h) (fun hh => hh.elim (c260 B z mark hB h) (c261 B z mark hB h))) (fun hh => hh.elim (c262 B z mark hB h) (fun hh => hh.elim (c263 B z mark hB h) (c264 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c265 B z mark hB h) (fun hh => hh.elim (c266 B z mark hB h) (c267 B z mark hB h))) (fun hh => hh.elim (c268 B z mark hB h) (fun hh => hh.elim (c269 B z mark hB h) (c270 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c271 B z mark hB h) (fun hh => hh.elim (c272 B z mark hB h) (c273 B z mark hB h))) (fun hh => hh.elim (c274 B z mark hB h) (fun hh => hh.elim (c275 B z mark hB h) (c276 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c277 B z mark hB h) (c278 B z mark hB h)) (fun hh => hh.elim (c279 B z mark hB h) (fun hh => hh.elim (c280 B z mark hB h) (c281 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c282 B z mark hB h) (fun hh => hh.elim (c283 B z mark hB h) (c284 B z mark hB h))) (fun hh => hh.elim (c285 B z mark hB h) (fun hh => hh.elim (c286 B z mark hB h) (c287 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c288 B z mark hB h) (fun hh => hh.elim (c289 B z mark hB h) (c290 B z mark hB h))) (fun hh => hh.elim (c291 B z mark hB h) (fun hh => hh.elim (c292 B z mark hB h) (c293 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c294 B z mark hB h) (fun hh => hh.elim (c295 B z mark hB h) (c296 B z mark hB h))) (fun hh => hh.elim (c297 B z mark hB h) (fun hh => hh.elim (c298 B z mark hB h) (c299 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c300 B z mark hB h) (c301 B z mark hB h)) (fun hh => hh.elim (c302 B z mark hB h) (fun hh => hh.elim (c303 B z mark hB h) (c304 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c305 B z mark hB h) (fun hh => hh.elim (c306 B z mark hB h) (c307 B z mark hB h))) (fun hh => hh.elim (c308 B z mark hB h) (fun hh => hh.elim (c309 B z mark hB h) (c310 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c311 B z mark hB h) (fun hh => hh.elim (c312 B z mark hB h) (c313 B z mark hB h))) (fun hh => hh.elim (c314 B z mark hB h) (fun hh => hh.elim (c315 B z mark hB h) (c316 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c317 B z mark hB h) (fun hh => hh.elim (c318 B z mark hB h) (c319 B z mark hB h))) (fun hh => hh.elim (c320 B z mark hB h) (fun hh => hh.elim (c321 B z mark hB h) (c322 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c323 B z mark hB h) (c324 B z mark hB h)) (fun hh => hh.elim (c325 B z mark hB h) (fun hh => hh.elim (c326 B z mark hB h) (c327 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c328 B z mark hB h) (fun hh => hh.elim (c329 B z mark hB h) (c330 B z mark hB h))) (fun hh => hh.elim (c331 B z mark hB h) (fun hh => hh.elim (c332 B z mark hB h) (c333 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c334 B z mark hB h) (fun hh => hh.elim (c335 B z mark hB h) (c336 B z mark hB h))) (fun hh => hh.elim (c337 B z mark hB h) (fun hh => hh.elim (c338 B z mark hB h) (c339 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c340 B z mark hB h) (fun hh => hh.elim (c341 B z mark hB h) (c342 B z mark hB h))) (fun hh => hh.elim (c343 B z mark hB h) (fun hh => hh.elim (c344 B z mark hB h) (c345 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c346 B z mark hB h) (fun hh => hh.elim (c347 B z mark hB h) (c348 B z mark hB h))) (fun hh => hh.elim (c349 B z mark hB h) (fun hh => hh.elim (c350 B z mark hB h) (c351 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c352 B z mark hB h) (fun hh => hh.elim (c353 B z mark hB h) (c354 B z mark hB h))) (fun hh => hh.elim (c355 B z mark hB h) (fun hh => hh.elim (c356 B z mark hB h) (c357 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c358 B z mark hB h) (fun hh => hh.elim (c359 B z mark hB h) (c360 B z mark hB h))) (fun hh => hh.elim (c361 B z mark hB h) (fun hh => hh.elim (c362 B z mark hB h) (c363 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c364 B z mark hB h) (fun hh => hh.elim (c365 B z mark hB h) (c366 B z mark hB h))) (fun hh => hh.elim (c367 B z mark hB h) (fun hh => hh.elim (c368 B z mark hB h) (c369 B z mark hB h)))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c370 B z mark hB h) (c371 B z mark hB h)) (fun hh => hh.elim (c372 B z mark hB h) (fun hh => hh.elim (c373 B z mark hB h) (c374 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c375 B z mark hB h) (fun hh => hh.elim (c376 B z mark hB h) (c377 B z mark hB h))) (fun hh => hh.elim (c378 B z mark hB h) (fun hh => hh.elim (c379 B z mark hB h) (c380 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c381 B z mark hB h) (fun hh => hh.elim (c382 B z mark hB h) (c383 B z mark hB h))) (fun hh => hh.elim (c384 B z mark hB h) (fun hh => hh.elim (c385 B z mark hB h) (c386 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c387 B z mark hB h) (fun hh => hh.elim (c388 B z mark hB h) (c389 B z mark hB h))) (fun hh => hh.elim (c390 B z mark hB h) (fun hh => hh.elim (c391 B z mark hB h) (c392 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c393 B z mark hB h) (c394 B z mark hB h)) (fun hh => hh.elim (c395 B z mark hB h) (fun hh => hh.elim (c396 B z mark hB h) (c397 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c398 B z mark hB h) (fun hh => hh.elim (c399 B z mark hB h) (c400 B z mark hB h))) (fun hh => hh.elim (c401 B z mark hB h) (fun hh => hh.elim (c402 B z mark hB h) (c403 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c404 B z mark hB h) (fun hh => hh.elim (c405 B z mark hB h) (c406 B z mark hB h))) (fun hh => hh.elim (c407 B z mark hB h) (fun hh => hh.elim (c408 B z mark hB h) (c409 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c410 B z mark hB h) (fun hh => hh.elim (c411 B z mark hB h) (c412 B z mark hB h))) (fun hh => hh.elim (c413 B z mark hB h) (fun hh => hh.elim (c414 B z mark hB h) (c415 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c416 B z mark hB h) (c417 B z mark hB h)) (fun hh => hh.elim (c418 B z mark hB h) (fun hh => hh.elim (c419 B z mark hB h) (c420 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c421 B z mark hB h) (fun hh => hh.elim (c422 B z mark hB h) (c423 B z mark hB h))) (fun hh => hh.elim (c424 B z mark hB h) (fun hh => hh.elim (c425 B z mark hB h) (c426 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c427 B z mark hB h) (fun hh => hh.elim (c428 B z mark hB h) (c429 B z mark hB h))) (fun hh => hh.elim (c430 B z mark hB h) (fun hh => hh.elim (c431 B z mark hB h) (c432 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c433 B z mark hB h) (fun hh => hh.elim (c434 B z mark hB h) (c435 B z mark hB h))) (fun hh => hh.elim (c436 B z mark hB h) (fun hh => hh.elim (c437 B z mark hB h) (c438 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c439 B z mark hB h) (c440 B z mark hB h)) (fun hh => hh.elim (c441 B z mark hB h) (fun hh => hh.elim (c442 B z mark hB h) (c443 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c444 B z mark hB h) (fun hh => hh.elim (c445 B z mark hB h) (c446 B z mark hB h))) (fun hh => hh.elim (c447 B z mark hB h) (fun hh => hh.elim (c448 B z mark hB h) (c449 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c450 B z mark hB h) (fun hh => hh.elim (c451 B z mark hB h) (c452 B z mark hB h))) (fun hh => hh.elim (c453 B z mark hB h) (fun hh => hh.elim (c454 B z mark hB h) (c455 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c456 B z mark hB h) (fun hh => hh.elim (c457 B z mark hB h) (c458 B z mark hB h))) (fun hh => hh.elim (c459 B z mark hB h) (fun hh => hh.elim (c460 B z mark hB h) (c461 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c462 B z mark hB h) (c463 B z mark hB h)) (fun hh => hh.elim (c464 B z mark hB h) (fun hh => hh.elim (c465 B z mark hB h) (c466 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c467 B z mark hB h) (fun hh => hh.elim (c468 B z mark hB h) (c469 B z mark hB h))) (fun hh => hh.elim (c470 B z mark hB h) (fun hh => hh.elim (c471 B z mark hB h) (c472 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c473 B z mark hB h) (fun hh => hh.elim (c474 B z mark hB h) (c475 B z mark hB h))) (fun hh => hh.elim (c476 B z mark hB h) (fun hh => hh.elim (c477 B z mark hB h) (c478 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c479 B z mark hB h) (fun hh => hh.elim (c480 B z mark hB h) (c481 B z mark hB h))) (fun hh => hh.elim (c482 B z mark hB h) (fun hh => hh.elim (c483 B z mark hB h) (c484 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c485 B z mark hB h) (c486 B z mark hB h)) (fun hh => hh.elim (c487 B z mark hB h) (fun hh => hh.elim (c488 B z mark hB h) (c489 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c490 B z mark hB h) (fun hh => hh.elim (c491 B z mark hB h) (c492 B z mark hB h))) (fun hh => hh.elim (c493 B z mark hB h) (fun hh => hh.elim (c494 B z mark hB h) (c495 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c496 B z mark hB h) (fun hh => hh.elim (c497 B z mark hB h) (c498 B z mark hB h))) (fun hh => hh.elim (c499 B z mark hB h) (fun hh => hh.elim (c500 B z mark hB h) (c501 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c502 B z mark hB h) (fun hh => hh.elim (c503 B z mark hB h) (c504 B z mark hB h))) (fun hh => hh.elim (c505 B z mark hB h) (fun hh => hh.elim (c506 B z mark hB h) (c507 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c508 B z mark hB h) (c509 B z mark hB h)) (fun hh => hh.elim (c510 B z mark hB h) (fun hh => hh.elim (c511 B z mark hB h) (c512 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c513 B z mark hB h) (fun hh => hh.elim (c514 B z mark hB h) (c515 B z mark hB h))) (fun hh => hh.elim (c516 B z mark hB h) (fun hh => hh.elim (c517 B z mark hB h) (c518 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c519 B z mark hB h) (fun hh => hh.elim (c520 B z mark hB h) (c521 B z mark hB h))) (fun hh => hh.elim (c522 B z mark hB h) (fun hh => hh.elim (c523 B z mark hB h) (c524 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c525 B z mark hB h) (fun hh => hh.elim (c526 B z mark hB h) (c527 B z mark hB h))) (fun hh => hh.elim (c528 B z mark hB h) (fun hh => hh.elim (c529 B z mark hB h) (c530 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c531 B z mark hB h) (fun hh => hh.elim (c532 B z mark hB h) (c533 B z mark hB h))) (fun hh => hh.elim (c534 B z mark hB h) (fun hh => hh.elim (c535 B z mark hB h) (c536 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c537 B z mark hB h) (fun hh => hh.elim (c538 B z mark hB h) (c539 B z mark hB h))) (fun hh => hh.elim (c540 B z mark hB h) (fun hh => hh.elim (c541 B z mark hB h) (c542 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c543 B z mark hB h) (fun hh => hh.elim (c544 B z mark hB h) (c545 B z mark hB h))) (fun hh => hh.elim (c546 B z mark hB h) (fun hh => hh.elim (c547 B z mark hB h) (c548 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c549 B z mark hB h) (fun hh => hh.elim (c550 B z mark hB h) (c551 B z mark hB h))) (fun hh => hh.elim (c552 B z mark hB h) (fun hh => hh.elim (c553 B z mark hB h) (c554 B z mark hB h))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c555 B z mark hB h) (c556 B z mark hB h)) (fun hh => hh.elim (c557 B z mark hB h) (fun hh => hh.elim (c558 B z mark hB h) (c559 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c560 B z mark hB h) (fun hh => hh.elim (c561 B z mark hB h) (c562 B z mark hB h))) (fun hh => hh.elim (c563 B z mark hB h) (fun hh => hh.elim (c564 B z mark hB h) (c565 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c566 B z mark hB h) (fun hh => hh.elim (c567 B z mark hB h) (c568 B z mark hB h))) (fun hh => hh.elim (c569 B z mark hB h) (fun hh => hh.elim (c570 B z mark hB h) (c571 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c572 B z mark hB h) (fun hh => hh.elim (c573 B z mark hB h) (c574 B z mark hB h))) (fun hh => hh.elim (c575 B z mark hB h) (fun hh => hh.elim (c576 B z mark hB h) (c577 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c578 B z mark hB h) (c579 B z mark hB h)) (fun hh => hh.elim (c580 B z mark hB h) (fun hh => hh.elim (c581 B z mark hB h) (c582 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c583 B z mark hB h) (fun hh => hh.elim (c584 B z mark hB h) (c585 B z mark hB h))) (fun hh => hh.elim (c586 B z mark hB h) (fun hh => hh.elim (c587 B z mark hB h) (c588 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c589 B z mark hB h) (fun hh => hh.elim (c590 B z mark hB h) (c591 B z mark hB h))) (fun hh => hh.elim (c592 B z mark hB h) (fun hh => hh.elim (c593 B z mark hB h) (c594 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c595 B z mark hB h) (fun hh => hh.elim (c596 B z mark hB h) (c597 B z mark hB h))) (fun hh => hh.elim (c598 B z mark hB h) (fun hh => hh.elim (c599 B z mark hB h) (c600 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c601 B z mark hB h) (c602 B z mark hB h)) (fun hh => hh.elim (c603 B z mark hB h) (fun hh => hh.elim (c604 B z mark hB h) (c605 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c606 B z mark hB h) (fun hh => hh.elim (c607 B z mark hB h) (c608 B z mark hB h))) (fun hh => hh.elim (c609 B z mark hB h) (fun hh => hh.elim (c610 B z mark hB h) (c611 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c612 B z mark hB h) (fun hh => hh.elim (c613 B z mark hB h) (c614 B z mark hB h))) (fun hh => hh.elim (c615 B z mark hB h) (fun hh => hh.elim (c616 B z mark hB h) (c617 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c618 B z mark hB h) (fun hh => hh.elim (c619 B z mark hB h) (c620 B z mark hB h))) (fun hh => hh.elim (c621 B z mark hB h) (fun hh => hh.elim (c622 B z mark hB h) (c623 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c624 B z mark hB h) (fun hh => hh.elim (c625 B z mark hB h) (c626 B z mark hB h))) (fun hh => hh.elim (c627 B z mark hB h) (fun hh => hh.elim (c628 B z mark hB h) (c629 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c630 B z mark hB h) (fun hh => hh.elim (c631 B z mark hB h) (c632 B z mark hB h))) (fun hh => hh.elim (c633 B z mark hB h) (fun hh => hh.elim (c634 B z mark hB h) (c635 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c636 B z mark hB h) (fun hh => hh.elim (c637 B z mark hB h) (c638 B z mark hB h))) (fun hh => hh.elim (c639 B z mark hB h) (fun hh => hh.elim (c640 B z mark hB h) (c641 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c642 B z mark hB h) (fun hh => hh.elim (c643 B z mark hB h) (c644 B z mark hB h))) (fun hh => hh.elim (c645 B z mark hB h) (fun hh => hh.elim (c646 B z mark hB h) (c647 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c648 B z mark hB h) (c649 B z mark hB h)) (fun hh => hh.elim (c650 B z mark hB h) (fun hh => hh.elim (c651 B z mark hB h) (c652 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c653 B z mark hB h) (fun hh => hh.elim (c654 B z mark hB h) (c655 B z mark hB h))) (fun hh => hh.elim (c656 B z mark hB h) (fun hh => hh.elim (c657 B z mark hB h) (c658 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c659 B z mark hB h) (fun hh => hh.elim (c660 B z mark hB h) (c661 B z mark hB h))) (fun hh => hh.elim (c662 B z mark hB h) (fun hh => hh.elim (c663 B z mark hB h) (c664 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c665 B z mark hB h) (fun hh => hh.elim (c666 B z mark hB h) (c667 B z mark hB h))) (fun hh => hh.elim (c668 B z mark hB h) (fun hh => hh.elim (c669 B z mark hB h) (c670 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c671 B z mark hB h) (c672 B z mark hB h)) (fun hh => hh.elim (c673 B z mark hB h) (fun hh => hh.elim (c674 B z mark hB h) (c675 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c676 B z mark hB h) (fun hh => hh.elim (c677 B z mark hB h) (c678 B z mark hB h))) (fun hh => hh.elim (c679 B z mark hB h) (fun hh => hh.elim (c680 B z mark hB h) (c681 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c682 B z mark hB h) (fun hh => hh.elim (c683 B z mark hB h) (c684 B z mark hB h))) (fun hh => hh.elim (c685 B z mark hB h) (fun hh => hh.elim (c686 B z mark hB h) (c687 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c688 B z mark hB h) (fun hh => hh.elim (c689 B z mark hB h) (c690 B z mark hB h))) (fun hh => hh.elim (c691 B z mark hB h) (fun hh => hh.elim (c692 B z mark hB h) (c693 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c694 B z mark hB h) (c695 B z mark hB h)) (fun hh => hh.elim (c696 B z mark hB h) (fun hh => hh.elim (c697 B z mark hB h) (c698 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c699 B z mark hB h) (fun hh => hh.elim (c700 B z mark hB h) (c701 B z mark hB h))) (fun hh => hh.elim (c702 B z mark hB h) (fun hh => hh.elim (c703 B z mark hB h) (c704 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c705 B z mark hB h) (fun hh => hh.elim (c706 B z mark hB h) (c707 B z mark hB h))) (fun hh => hh.elim (c708 B z mark hB h) (fun hh => hh.elim (c709 B z mark hB h) (c710 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c711 B z mark hB h) (fun hh => hh.elim (c712 B z mark hB h) (c713 B z mark hB h))) (fun hh => hh.elim (c714 B z mark hB h) (fun hh => hh.elim (c715 B z mark hB h) (c716 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c717 B z mark hB h) (fun hh => hh.elim (c718 B z mark hB h) (c719 B z mark hB h))) (fun hh => hh.elim (c720 B z mark hB h) (fun hh => hh.elim (c721 B z mark hB h) (c722 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c723 B z mark hB h) (fun hh => hh.elim (c724 B z mark hB h) (c725 B z mark hB h))) (fun hh => hh.elim (c726 B z mark hB h) (fun hh => hh.elim (c727 B z mark hB h) (c728 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c729 B z mark hB h) (fun hh => hh.elim (c730 B z mark hB h) (c731 B z mark hB h))) (fun hh => hh.elim (c732 B z mark hB h) (fun hh => hh.elim (c733 B z mark hB h) (c734 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c735 B z mark hB h) (fun hh => hh.elim (c736 B z mark hB h) (c737 B z mark hB h))) (fun hh => hh.elim (c738 B z mark hB h) (fun hh => hh.elim (c739 B z mark hB h) (c740 B z mark hB h))))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c741 B z mark hB h) (c742 B z mark hB h)) (fun hh => hh.elim (c743 B z mark hB h) (fun hh => hh.elim (c744 B z mark hB h) (c745 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c746 B z mark hB h) (fun hh => hh.elim (c747 B z mark hB h) (c748 B z mark hB h))) (fun hh => hh.elim (c749 B z mark hB h) (fun hh => hh.elim (c750 B z mark hB h) (c751 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c752 B z mark hB h) (fun hh => hh.elim (c753 B z mark hB h) (c754 B z mark hB h))) (fun hh => hh.elim (c755 B z mark hB h) (fun hh => hh.elim (c756 B z mark hB h) (c757 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c758 B z mark hB h) (fun hh => hh.elim (c759 B z mark hB h) (c760 B z mark hB h))) (fun hh => hh.elim (c761 B z mark hB h) (fun hh => hh.elim (c762 B z mark hB h) (c763 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c764 B z mark hB h) (c765 B z mark hB h)) (fun hh => hh.elim (c766 B z mark hB h) (fun hh => hh.elim (c767 B z mark hB h) (c768 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c769 B z mark hB h) (fun hh => hh.elim (c770 B z mark hB h) (c771 B z mark hB h))) (fun hh => hh.elim (c772 B z mark hB h) (fun hh => hh.elim (c773 B z mark hB h) (c774 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c775 B z mark hB h) (fun hh => hh.elim (c776 B z mark hB h) (c777 B z mark hB h))) (fun hh => hh.elim (c778 B z mark hB h) (fun hh => hh.elim (c779 B z mark hB h) (c780 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c781 B z mark hB h) (fun hh => hh.elim (c782 B z mark hB h) (c783 B z mark hB h))) (fun hh => hh.elim (c784 B z mark hB h) (fun hh => hh.elim (c785 B z mark hB h) (c786 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c787 B z mark hB h) (c788 B z mark hB h)) (fun hh => hh.elim (c789 B z mark hB h) (fun hh => hh.elim (c790 B z mark hB h) (c791 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c792 B z mark hB h) (fun hh => hh.elim (c793 B z mark hB h) (c794 B z mark hB h))) (fun hh => hh.elim (c795 B z mark hB h) (fun hh => hh.elim (c796 B z mark hB h) (c797 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c798 B z mark hB h) (fun hh => hh.elim (c799 B z mark hB h) (c800 B z mark hB h))) (fun hh => hh.elim (c801 B z mark hB h) (fun hh => hh.elim (c802 B z mark hB h) (c803 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c804 B z mark hB h) (fun hh => hh.elim (c805 B z mark hB h) (c806 B z mark hB h))) (fun hh => hh.elim (c807 B z mark hB h) (fun hh => hh.elim (c808 B z mark hB h) (c809 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c810 B z mark hB h) (c811 B z mark hB h)) (fun hh => hh.elim (c812 B z mark hB h) (fun hh => hh.elim (c813 B z mark hB h) (c814 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c815 B z mark hB h) (fun hh => hh.elim (c816 B z mark hB h) (c817 B z mark hB h))) (fun hh => hh.elim (c818 B z mark hB h) (fun hh => hh.elim (c819 B z mark hB h) (c820 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c821 B z mark hB h) (fun hh => hh.elim (c822 B z mark hB h) (c823 B z mark hB h))) (fun hh => hh.elim (c824 B z mark hB h) (fun hh => hh.elim (c825 B z mark hB h) (c826 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c827 B z mark hB h) (fun hh => hh.elim (c828 B z mark hB h) (c829 B z mark hB h))) (fun hh => hh.elim (c830 B z mark hB h) (fun hh => hh.elim (c831 B z mark hB h) (c832 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c833 B z mark hB h) (c834 B z mark hB h)) (fun hh => hh.elim (c835 B z mark hB h) (fun hh => hh.elim (c836 B z mark hB h) (c837 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c838 B z mark hB h) (fun hh => hh.elim (c839 B z mark hB h) (c840 B z mark hB h))) (fun hh => hh.elim (c841 B z mark hB h) (fun hh => hh.elim (c842 B z mark hB h) (c843 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c844 B z mark hB h) (fun hh => hh.elim (c845 B z mark hB h) (c846 B z mark hB h))) (fun hh => hh.elim (c847 B z mark hB h) (fun hh => hh.elim (c848 B z mark hB h) (c849 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c850 B z mark hB h) (fun hh => hh.elim (c851 B z mark hB h) (c852 B z mark hB h))) (fun hh => hh.elim (c853 B z mark hB h) (fun hh => hh.elim (c854 B z mark hB h) (c855 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c856 B z mark hB h) (c857 B z mark hB h)) (fun hh => hh.elim (c858 B z mark hB h) (fun hh => hh.elim (c859 B z mark hB h) (c860 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c861 B z mark hB h) (fun hh => hh.elim (c862 B z mark hB h) (c863 B z mark hB h))) (fun hh => hh.elim (c864 B z mark hB h) (fun hh => hh.elim (c865 B z mark hB h) (c866 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c867 B z mark hB h) (fun hh => hh.elim (c868 B z mark hB h) (c869 B z mark hB h))) (fun hh => hh.elim (c870 B z mark hB h) (fun hh => hh.elim (c871 B z mark hB h) (c872 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c873 B z mark hB h) (fun hh => hh.elim (c874 B z mark hB h) (c875 B z mark hB h))) (fun hh => hh.elim (c876 B z mark hB h) (fun hh => hh.elim (c877 B z mark hB h) (c878 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c879 B z mark hB h) (c880 B z mark hB h)) (fun hh => hh.elim (c881 B z mark hB h) (fun hh => hh.elim (c882 B z mark hB h) (c883 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c884 B z mark hB h) (fun hh => hh.elim (c885 B z mark hB h) (c886 B z mark hB h))) (fun hh => hh.elim (c887 B z mark hB h) (fun hh => hh.elim (c888 B z mark hB h) (c889 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c890 B z mark hB h) (fun hh => hh.elim (c891 B z mark hB h) (c892 B z mark hB h))) (fun hh => hh.elim (c893 B z mark hB h) (fun hh => hh.elim (c894 B z mark hB h) (c895 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c896 B z mark hB h) (fun hh => hh.elim (c897 B z mark hB h) (c898 B z mark hB h))) (fun hh => hh.elim (c899 B z mark hB h) (fun hh => hh.elim (c900 B z mark hB h) (c901 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c902 B z mark hB h) (fun hh => hh.elim (c903 B z mark hB h) (c904 B z mark hB h))) (fun hh => hh.elim (c905 B z mark hB h) (fun hh => hh.elim (c906 B z mark hB h) (c907 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c908 B z mark hB h) (fun hh => hh.elim (c909 B z mark hB h) (c910 B z mark hB h))) (fun hh => hh.elim (c911 B z mark hB h) (fun hh => hh.elim (c912 B z mark hB h) (c913 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c914 B z mark hB h) (fun hh => hh.elim (c915 B z mark hB h) (c916 B z mark hB h))) (fun hh => hh.elim (c917 B z mark hB h) (fun hh => hh.elim (c918 B z mark hB h) (c919 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c920 B z mark hB h) (fun hh => hh.elim (c921 B z mark hB h) (c922 B z mark hB h))) (fun hh => hh.elim (c923 B z mark hB h) (fun hh => hh.elim (c924 B z mark hB h) (c925 B z mark hB h))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c926 B z mark hB h) (c927 B z mark hB h)) (fun hh => hh.elim (c928 B z mark hB h) (fun hh => hh.elim (c929 B z mark hB h) (c930 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c931 B z mark hB h) (fun hh => hh.elim (c932 B z mark hB h) (c933 B z mark hB h))) (fun hh => hh.elim (c934 B z mark hB h) (fun hh => hh.elim (c935 B z mark hB h) (c936 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c937 B z mark hB h) (fun hh => hh.elim (c938 B z mark hB h) (c939 B z mark hB h))) (fun hh => hh.elim (c940 B z mark hB h) (fun hh => hh.elim (c941 B z mark hB h) (c942 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c943 B z mark hB h) (fun hh => hh.elim (c944 B z mark hB h) (c945 B z mark hB h))) (fun hh => hh.elim (c946 B z mark hB h) (fun hh => hh.elim (c947 B z mark hB h) (c948 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c949 B z mark hB h) (c950 B z mark hB h)) (fun hh => hh.elim (c951 B z mark hB h) (fun hh => hh.elim (c952 B z mark hB h) (c953 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c954 B z mark hB h) (fun hh => hh.elim (c955 B z mark hB h) (c956 B z mark hB h))) (fun hh => hh.elim (c957 B z mark hB h) (fun hh => hh.elim (c958 B z mark hB h) (c959 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c960 B z mark hB h) (fun hh => hh.elim (c961 B z mark hB h) (c962 B z mark hB h))) (fun hh => hh.elim (c963 B z mark hB h) (fun hh => hh.elim (c964 B z mark hB h) (c965 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c966 B z mark hB h) (fun hh => hh.elim (c967 B z mark hB h) (c968 B z mark hB h))) (fun hh => hh.elim (c969 B z mark hB h) (fun hh => hh.elim (c970 B z mark hB h) (c971 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c972 B z mark hB h) (c973 B z mark hB h)) (fun hh => hh.elim (c974 B z mark hB h) (fun hh => hh.elim (c975 B z mark hB h) (c976 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c977 B z mark hB h) (fun hh => hh.elim (c978 B z mark hB h) (c979 B z mark hB h))) (fun hh => hh.elim (c980 B z mark hB h) (fun hh => hh.elim (c981 B z mark hB h) (c982 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c983 B z mark hB h) (fun hh => hh.elim (c984 B z mark hB h) (c985 B z mark hB h))) (fun hh => hh.elim (c986 B z mark hB h) (fun hh => hh.elim (c987 B z mark hB h) (c988 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c989 B z mark hB h) (fun hh => hh.elim (c990 B z mark hB h) (c991 B z mark hB h))) (fun hh => hh.elim (c992 B z mark hB h) (fun hh => hh.elim (c993 B z mark hB h) (c994 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c995 B z mark hB h) (fun hh => hh.elim (c996 B z mark hB h) (c997 B z mark hB h))) (fun hh => hh.elim (c998 B z mark hB h) (fun hh => hh.elim (c999 B z mark hB h) (c1000 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1001 B z mark hB h) (fun hh => hh.elim (c1002 B z mark hB h) (c1003 B z mark hB h))) (fun hh => hh.elim (c1004 B z mark hB h) (fun hh => hh.elim (c1005 B z mark hB h) (c1006 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1007 B z mark hB h) (fun hh => hh.elim (c1008 B z mark hB h) (c1009 B z mark hB h))) (fun hh => hh.elim (c1010 B z mark hB h) (fun hh => hh.elim (c1011 B z mark hB h) (c1012 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1013 B z mark hB h) (fun hh => hh.elim (c1014 B z mark hB h) (c1015 B z mark hB h))) (fun hh => hh.elim (c1016 B z mark hB h) (fun hh => hh.elim (c1017 B z mark hB h) (c1018 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1019 B z mark hB h) (c1020 B z mark hB h)) (fun hh => hh.elim (c1021 B z mark hB h) (fun hh => hh.elim (c1022 B z mark hB h) (c1023 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1024 B z mark hB h) (fun hh => hh.elim (c1025 B z mark hB h) (c1026 B z mark hB h))) (fun hh => hh.elim (c1027 B z mark hB h) (fun hh => hh.elim (c1028 B z mark hB h) (c1029 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1030 B z mark hB h) (fun hh => hh.elim (c1031 B z mark hB h) (c1032 B z mark hB h))) (fun hh => hh.elim (c1033 B z mark hB h) (fun hh => hh.elim (c1034 B z mark hB h) (c1035 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1036 B z mark hB h) (fun hh => hh.elim (c1037 B z mark hB h) (c1038 B z mark hB h))) (fun hh => hh.elim (c1039 B z mark hB h) (fun hh => hh.elim (c1040 B z mark hB h) (c1041 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1042 B z mark hB h) (c1043 B z mark hB h)) (fun hh => hh.elim (c1044 B z mark hB h) (fun hh => hh.elim (c1045 B z mark hB h) (c1046 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1047 B z mark hB h) (fun hh => hh.elim (c1048 B z mark hB h) (c1049 B z mark hB h))) (fun hh => hh.elim (c1050 B z mark hB h) (fun hh => hh.elim (c1051 B z mark hB h) (c1052 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1053 B z mark hB h) (fun hh => hh.elim (c1054 B z mark hB h) (c1055 B z mark hB h))) (fun hh => hh.elim (c1056 B z mark hB h) (fun hh => hh.elim (c1057 B z mark hB h) (c1058 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1059 B z mark hB h) (fun hh => hh.elim (c1060 B z mark hB h) (c1061 B z mark hB h))) (fun hh => hh.elim (c1062 B z mark hB h) (fun hh => hh.elim (c1063 B z mark hB h) (c1064 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1065 B z mark hB h) (c1066 B z mark hB h)) (fun hh => hh.elim (c1067 B z mark hB h) (fun hh => hh.elim (c1068 B z mark hB h) (c1069 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1070 B z mark hB h) (fun hh => hh.elim (c1071 B z mark hB h) (c1072 B z mark hB h))) (fun hh => hh.elim (c1073 B z mark hB h) (fun hh => hh.elim (c1074 B z mark hB h) (c1075 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1076 B z mark hB h) (fun hh => hh.elim (c1077 B z mark hB h) (c1078 B z mark hB h))) (fun hh => hh.elim (c1079 B z mark hB h) (fun hh => hh.elim (c1080 B z mark hB h) (c1081 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1082 B z mark hB h) (fun hh => hh.elim (c1083 B z mark hB h) (c1084 B z mark hB h))) (fun hh => hh.elim (c1085 B z mark hB h) (fun hh => hh.elim (c1086 B z mark hB h) (c1087 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1088 B z mark hB h) (fun hh => hh.elim (c1089 B z mark hB h) (c1090 B z mark hB h))) (fun hh => hh.elim (c1091 B z mark hB h) (fun hh => hh.elim (c1092 B z mark hB h) (c1093 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1094 B z mark hB h) (fun hh => hh.elim (c1095 B z mark hB h) (c1096 B z mark hB h))) (fun hh => hh.elim (c1097 B z mark hB h) (fun hh => hh.elim (c1098 B z mark hB h) (c1099 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1100 B z mark hB h) (fun hh => hh.elim (c1101 B z mark hB h) (c1102 B z mark hB h))) (fun hh => hh.elim (c1103 B z mark hB h) (fun hh => hh.elim (c1104 B z mark hB h) (c1105 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1106 B z mark hB h) (fun hh => hh.elim (c1107 B z mark hB h) (c1108 B z mark hB h))) (fun hh => hh.elim (c1109 B z mark hB h) (fun hh => hh.elim (c1110 B z mark hB h) (c1111 B z mark hB h)))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1112 B z mark hB h) (c1113 B z mark hB h)) (fun hh => hh.elim (c1114 B z mark hB h) (fun hh => hh.elim (c1115 B z mark hB h) (c1116 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1117 B z mark hB h) (fun hh => hh.elim (c1118 B z mark hB h) (c1119 B z mark hB h))) (fun hh => hh.elim (c1120 B z mark hB h) (fun hh => hh.elim (c1121 B z mark hB h) (c1122 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1123 B z mark hB h) (fun hh => hh.elim (c1124 B z mark hB h) (c1125 B z mark hB h))) (fun hh => hh.elim (c1126 B z mark hB h) (fun hh => hh.elim (c1127 B z mark hB h) (c1128 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1129 B z mark hB h) (fun hh => hh.elim (c1130 B z mark hB h) (c1131 B z mark hB h))) (fun hh => hh.elim (c1132 B z mark hB h) (fun hh => hh.elim (c1133 B z mark hB h) (c1134 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1135 B z mark hB h) (c1136 B z mark hB h)) (fun hh => hh.elim (c1137 B z mark hB h) (fun hh => hh.elim (c1138 B z mark hB h) (c1139 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1140 B z mark hB h) (fun hh => hh.elim (c1141 B z mark hB h) (c1142 B z mark hB h))) (fun hh => hh.elim (c1143 B z mark hB h) (fun hh => hh.elim (c1144 B z mark hB h) (c1145 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1146 B z mark hB h) (fun hh => hh.elim (c1147 B z mark hB h) (c1148 B z mark hB h))) (fun hh => hh.elim (c1149 B z mark hB h) (fun hh => hh.elim (c1150 B z mark hB h) (c1151 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1152 B z mark hB h) (fun hh => hh.elim (c1153 B z mark hB h) (c1154 B z mark hB h))) (fun hh => hh.elim (c1155 B z mark hB h) (fun hh => hh.elim (c1156 B z mark hB h) (c1157 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1158 B z mark hB h) (c1159 B z mark hB h)) (fun hh => hh.elim (c1160 B z mark hB h) (fun hh => hh.elim (c1161 B z mark hB h) (c1162 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1163 B z mark hB h) (fun hh => hh.elim (c1164 B z mark hB h) (c1165 B z mark hB h))) (fun hh => hh.elim (c1166 B z mark hB h) (fun hh => hh.elim (c1167 B z mark hB h) (c1168 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1169 B z mark hB h) (fun hh => hh.elim (c1170 B z mark hB h) (c1171 B z mark hB h))) (fun hh => hh.elim (c1172 B z mark hB h) (fun hh => hh.elim (c1173 B z mark hB h) (c1174 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1175 B z mark hB h) (fun hh => hh.elim (c1176 B z mark hB h) (c1177 B z mark hB h))) (fun hh => hh.elim (c1178 B z mark hB h) (fun hh => hh.elim (c1179 B z mark hB h) (c1180 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1181 B z mark hB h) (c1182 B z mark hB h)) (fun hh => hh.elim (c1183 B z mark hB h) (fun hh => hh.elim (c1184 B z mark hB h) (c1185 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1186 B z mark hB h) (fun hh => hh.elim (c1187 B z mark hB h) (c1188 B z mark hB h))) (fun hh => hh.elim (c1189 B z mark hB h) (fun hh => hh.elim (c1190 B z mark hB h) (c1191 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1192 B z mark hB h) (fun hh => hh.elim (c1193 B z mark hB h) (c1194 B z mark hB h))) (fun hh => hh.elim (c1195 B z mark hB h) (fun hh => hh.elim (c1196 B z mark hB h) (c1197 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1198 B z mark hB h) (fun hh => hh.elim (c1199 B z mark hB h) (c1200 B z mark hB h))) (fun hh => hh.elim (c1201 B z mark hB h) (fun hh => hh.elim (c1202 B z mark hB h) (c1203 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1204 B z mark hB h) (c1205 B z mark hB h)) (fun hh => hh.elim (c1206 B z mark hB h) (fun hh => hh.elim (c1207 B z mark hB h) (c1208 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1209 B z mark hB h) (fun hh => hh.elim (c1210 B z mark hB h) (c1211 B z mark hB h))) (fun hh => hh.elim (c1212 B z mark hB h) (fun hh => hh.elim (c1213 B z mark hB h) (c1214 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1215 B z mark hB h) (fun hh => hh.elim (c1216 B z mark hB h) (c1217 B z mark hB h))) (fun hh => hh.elim (c1218 B z mark hB h) (fun hh => hh.elim (c1219 B z mark hB h) (c1220 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1221 B z mark hB h) (fun hh => hh.elim (c1222 B z mark hB h) (c1223 B z mark hB h))) (fun hh => hh.elim (c1224 B z mark hB h) (fun hh => hh.elim (c1225 B z mark hB h) (c1226 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1227 B z mark hB h) (c1228 B z mark hB h)) (fun hh => hh.elim (c1229 B z mark hB h) (fun hh => hh.elim (c1230 B z mark hB h) (c1231 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1232 B z mark hB h) (fun hh => hh.elim (c1233 B z mark hB h) (c1234 B z mark hB h))) (fun hh => hh.elim (c1235 B z mark hB h) (fun hh => hh.elim (c1236 B z mark hB h) (c1237 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1238 B z mark hB h) (fun hh => hh.elim (c1239 B z mark hB h) (c1240 B z mark hB h))) (fun hh => hh.elim (c1241 B z mark hB h) (fun hh => hh.elim (c1242 B z mark hB h) (c1243 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1244 B z mark hB h) (fun hh => hh.elim (c1245 B z mark hB h) (c1246 B z mark hB h))) (fun hh => hh.elim (c1247 B z mark hB h) (fun hh => hh.elim (c1248 B z mark hB h) (c1249 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1250 B z mark hB h) (c1251 B z mark hB h)) (fun hh => hh.elim (c1252 B z mark hB h) (fun hh => hh.elim (c1253 B z mark hB h) (c1254 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1255 B z mark hB h) (fun hh => hh.elim (c1256 B z mark hB h) (c1257 B z mark hB h))) (fun hh => hh.elim (c1258 B z mark hB h) (fun hh => hh.elim (c1259 B z mark hB h) (c1260 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1261 B z mark hB h) (fun hh => hh.elim (c1262 B z mark hB h) (c1263 B z mark hB h))) (fun hh => hh.elim (c1264 B z mark hB h) (fun hh => hh.elim (c1265 B z mark hB h) (c1266 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1267 B z mark hB h) (fun hh => hh.elim (c1268 B z mark hB h) (c1269 B z mark hB h))) (fun hh => hh.elim (c1270 B z mark hB h) (fun hh => hh.elim (c1271 B z mark hB h) (c1272 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1273 B z mark hB h) (fun hh => hh.elim (c1274 B z mark hB h) (c1275 B z mark hB h))) (fun hh => hh.elim (c1276 B z mark hB h) (fun hh => hh.elim (c1277 B z mark hB h) (c1278 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1279 B z mark hB h) (fun hh => hh.elim (c1280 B z mark hB h) (c1281 B z mark hB h))) (fun hh => hh.elim (c1282 B z mark hB h) (fun hh => hh.elim (c1283 B z mark hB h) (c1284 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1285 B z mark hB h) (fun hh => hh.elim (c1286 B z mark hB h) (c1287 B z mark hB h))) (fun hh => hh.elim (c1288 B z mark hB h) (fun hh => hh.elim (c1289 B z mark hB h) (c1290 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1291 B z mark hB h) (fun hh => hh.elim (c1292 B z mark hB h) (c1293 B z mark hB h))) (fun hh => hh.elim (c1294 B z mark hB h) (fun hh => hh.elim (c1295 B z mark hB h) (c1296 B z mark hB h))))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1297 B z mark hB h) (c1298 B z mark hB h)) (fun hh => hh.elim (c1299 B z mark hB h) (fun hh => hh.elim (c1300 B z mark hB h) (c1301 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1302 B z mark hB h) (fun hh => hh.elim (c1303 B z mark hB h) (c1304 B z mark hB h))) (fun hh => hh.elim (c1305 B z mark hB h) (fun hh => hh.elim (c1306 B z mark hB h) (c1307 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1308 B z mark hB h) (fun hh => hh.elim (c1309 B z mark hB h) (c1310 B z mark hB h))) (fun hh => hh.elim (c1311 B z mark hB h) (fun hh => hh.elim (c1312 B z mark hB h) (c1313 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1314 B z mark hB h) (fun hh => hh.elim (c1315 B z mark hB h) (c1316 B z mark hB h))) (fun hh => hh.elim (c1317 B z mark hB h) (fun hh => hh.elim (c1318 B z mark hB h) (c1319 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1320 B z mark hB h) (c1321 B z mark hB h)) (fun hh => hh.elim (c1322 B z mark hB h) (fun hh => hh.elim (c1323 B z mark hB h) (c1324 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1325 B z mark hB h) (fun hh => hh.elim (c1326 B z mark hB h) (c1327 B z mark hB h))) (fun hh => hh.elim (c1328 B z mark hB h) (fun hh => hh.elim (c1329 B z mark hB h) (c1330 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1331 B z mark hB h) (fun hh => hh.elim (c1332 B z mark hB h) (c1333 B z mark hB h))) (fun hh => hh.elim (c1334 B z mark hB h) (fun hh => hh.elim (c1335 B z mark hB h) (c1336 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1337 B z mark hB h) (fun hh => hh.elim (c1338 B z mark hB h) (c1339 B z mark hB h))) (fun hh => hh.elim (c1340 B z mark hB h) (fun hh => hh.elim (c1341 B z mark hB h) (c1342 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1343 B z mark hB h) (c1344 B z mark hB h)) (fun hh => hh.elim (c1345 B z mark hB h) (fun hh => hh.elim (c1346 B z mark hB h) (c1347 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1348 B z mark hB h) (fun hh => hh.elim (c1349 B z mark hB h) (c1350 B z mark hB h))) (fun hh => hh.elim (c1351 B z mark hB h) (fun hh => hh.elim (c1352 B z mark hB h) (c1353 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1354 B z mark hB h) (fun hh => hh.elim (c1355 B z mark hB h) (c1356 B z mark hB h))) (fun hh => hh.elim (c1357 B z mark hB h) (fun hh => hh.elim (c1358 B z mark hB h) (c1359 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1360 B z mark hB h) (fun hh => hh.elim (c1361 B z mark hB h) (c1362 B z mark hB h))) (fun hh => hh.elim (c1363 B z mark hB h) (fun hh => hh.elim (c1364 B z mark hB h) (c1365 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1366 B z mark hB h) (fun hh => hh.elim (c1367 B z mark hB h) (c1368 B z mark hB h))) (fun hh => hh.elim (c1369 B z mark hB h) (fun hh => hh.elim (c1370 B z mark hB h) (c1371 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1372 B z mark hB h) (fun hh => hh.elim (c1373 B z mark hB h) (c1374 B z mark hB h))) (fun hh => hh.elim (c1375 B z mark hB h) (fun hh => hh.elim (c1376 B z mark hB h) (c1377 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1378 B z mark hB h) (fun hh => hh.elim (c1379 B z mark hB h) (c1380 B z mark hB h))) (fun hh => hh.elim (c1381 B z mark hB h) (fun hh => hh.elim (c1382 B z mark hB h) (c1383 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1384 B z mark hB h) (fun hh => hh.elim (c1385 B z mark hB h) (c1386 B z mark hB h))) (fun hh => hh.elim (c1387 B z mark hB h) (fun hh => hh.elim (c1388 B z mark hB h) (c1389 B z mark hB h)))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1390 B z mark hB h) (c1391 B z mark hB h)) (fun hh => hh.elim (c1392 B z mark hB h) (fun hh => hh.elim (c1393 B z mark hB h) (c1394 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1395 B z mark hB h) (fun hh => hh.elim (c1396 B z mark hB h) (c1397 B z mark hB h))) (fun hh => hh.elim (c1398 B z mark hB h) (fun hh => hh.elim (c1399 B z mark hB h) (c1400 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1401 B z mark hB h) (fun hh => hh.elim (c1402 B z mark hB h) (c1403 B z mark hB h))) (fun hh => hh.elim (c1404 B z mark hB h) (fun hh => hh.elim (c1405 B z mark hB h) (c1406 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1407 B z mark hB h) (fun hh => hh.elim (c1408 B z mark hB h) (c1409 B z mark hB h))) (fun hh => hh.elim (c1410 B z mark hB h) (fun hh => hh.elim (c1411 B z mark hB h) (c1412 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1413 B z mark hB h) (c1414 B z mark hB h)) (fun hh => hh.elim (c1415 B z mark hB h) (fun hh => hh.elim (c1416 B z mark hB h) (c1417 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1418 B z mark hB h) (fun hh => hh.elim (c1419 B z mark hB h) (c1420 B z mark hB h))) (fun hh => hh.elim (c1421 B z mark hB h) (fun hh => hh.elim (c1422 B z mark hB h) (c1423 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1424 B z mark hB h) (fun hh => hh.elim (c1425 B z mark hB h) (c1426 B z mark hB h))) (fun hh => hh.elim (c1427 B z mark hB h) (fun hh => hh.elim (c1428 B z mark hB h) (c1429 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1430 B z mark hB h) (fun hh => hh.elim (c1431 B z mark hB h) (c1432 B z mark hB h))) (fun hh => hh.elim (c1433 B z mark hB h) (fun hh => hh.elim (c1434 B z mark hB h) (c1435 B z mark hB h))))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1436 B z mark hB h) (c1437 B z mark hB h)) (fun hh => hh.elim (c1438 B z mark hB h) (fun hh => hh.elim (c1439 B z mark hB h) (c1440 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1441 B z mark hB h) (fun hh => hh.elim (c1442 B z mark hB h) (c1443 B z mark hB h))) (fun hh => hh.elim (c1444 B z mark hB h) (fun hh => hh.elim (c1445 B z mark hB h) (c1446 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1447 B z mark hB h) (fun hh => hh.elim (c1448 B z mark hB h) (c1449 B z mark hB h))) (fun hh => hh.elim (c1450 B z mark hB h) (fun hh => hh.elim (c1451 B z mark hB h) (c1452 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1453 B z mark hB h) (fun hh => hh.elim (c1454 B z mark hB h) (c1455 B z mark hB h))) (fun hh => hh.elim (c1456 B z mark hB h) (fun hh => hh.elim (c1457 B z mark hB h) (c1458 B z mark hB h)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1459 B z mark hB h) (fun hh => hh.elim (c1460 B z mark hB h) (c1461 B z mark hB h))) (fun hh => hh.elim (c1462 B z mark hB h) (fun hh => hh.elim (c1463 B z mark hB h) (c1464 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1465 B z mark hB h) (fun hh => hh.elim (c1466 B z mark hB h) (c1467 B z mark hB h))) (fun hh => hh.elim (c1468 B z mark hB h) (fun hh => hh.elim (c1469 B z mark hB h) (c1470 B z mark hB h))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (c1471 B z mark hB h) (fun hh => hh.elim (c1472 B z mark hB h) (c1473 B z mark hB h))) (fun hh => hh.elim (c1474 B z mark hB h) (fun hh => hh.elim (c1475 B z mark hB h) (c1476 B z mark hB h)))) (fun hh => hh.elim (fun hh => hh.elim (c1477 B z mark hB h) (fun hh => hh.elim (c1478 B z mark hB h) (c1479 B z mark hB h))) (fun hh => hh.elim (c1480 B z mark hB h) (fun hh => hh.elim (c1481 B z mark hB h) (c1482 B z mark hB h)))))))))))) hh

#print axioms no_pattern
end Erdos595UniversalProfile
