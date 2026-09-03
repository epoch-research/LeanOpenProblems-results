import Submission.PairAnchorSAT

/-! The finite pair-witness pattern underlying a uniform covering theorem
for the independent-pair family. All Boolean reasoning is reconstructed by
Mathlib's LRAT elaborator and checked by the kernel. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false
open Set SimpleGraph
namespace Erdos595PairAnchorPattern

/-- Two endpoint-anchor rows and one selected edge witness. -/
def edgeCoords (i : Fin 3) : Fin 10 → Fin 18 :=
  match i.val with
  | 0 => ![0,1,2,3,4,5,6,7,12,13]
  | 1 => ![0,1,2,3,8,9,10,11,14,15]
  | _ => ![4,5,6,7,8,9,10,11,16,17]

variable {V : Type*} (B : SimpleGraph V) (z : Fin 18 → V)

def Meet (a b c d : Fin 18) : Prop :=
  z a = z c ∨ z a = z d ∨ z b = z c ∨ z b = z d

structure Conditions : Prop where
  indep₀ : ¬B.Adj (z 12) (z 13)
  indep₁ : ¬B.Adj (z 14) (z 15)
  indep₂ : ¬B.Adj (z 16) (z 17)
  meet₀ : Meet z 2 3 12 13
  meet₁ : Meet z 2 3 14 15
  meet₂ : Meet z 4 5 12 13
  meet₃ : Meet z 6 7 16 17
  meet₄ : Meet z 8 9 14 15
  meet₅ : Meet z 8 9 16 17
  near₀ : B.Adj (z 12) (z 16) ∨ B.Adj (z 13) (z 16)
  near₁ : B.Adj (z 12) (z 16) ∨ B.Adj (z 12) (z 17)
  near₂ : B.Adj (z 12) (z 17) ∨ B.Adj (z 13) (z 17)
  eq_pattern : ∀ i j : Fin 3, ∀ a b : Fin 10,
    (z (edgeCoords i a) = z (edgeCoords i b) ↔
      z (edgeCoords j a) = z (edgeCoords j b))
  adj_pattern : ∀ i j : Fin 3, ∀ a b : Fin 10,
    (B.Adj (z (edgeCoords i a)) (z (edgeCoords i b)) ↔
      B.Adj (z (edgeCoords j a)) (z (edgeCoords j b)))

variable (hB : B.CliqueFree 3) (h : Conditions B z)

include hB h in
theorem no_pattern : False := by
  classical
  have c0 : ¬((z 13 = z 17) ∧ (B.Adj (z 13) (z 17))) := by
    rintro ⟨h1,h2⟩
    exact h2.ne (h1)
  have c1 : ¬((B.Adj (z 0) (z 12)) ∧ (B.Adj (z 0) (z 14)) ∧ (B.Adj (z 12) (z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)
  have c2 : ¬((B.Adj (z 1) (z 12)) ∧ (B.Adj (z 1) (z 14)) ∧ (B.Adj (z 12) (z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)
  have c3 : ¬((z 6 = z 16) ∧ (¬(B.Adj (z 2) (z 6))) ∧ (B.Adj (z 2) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h3)
  have c4 : ¬((z 2 = z 8) ∧ (z 8 = z 17) ∧ (¬(z 2 = z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h1).trans (h2))
  have c5 : ¬((z 2 = z 14) ∧ (z 2 = z 12) ∧ (¬(z 12 = z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c6 : ¬((z 2 = z 12) ∧ (¬(B.Adj (z 2) (z 16))) ∧ (B.Adj (z 12) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h3)
  have c7 : ¬((z 2 = z 13) ∧ (¬(B.Adj (z 2) (z 14))) ∧ (B.Adj (z 13) (z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h3)
  have c8 : ¬((z 2 = z 15) ∧ (z 2 = z 13) ∧ (¬(z 13 = z 15))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c9 : ¬((z 2 = z 17) ∧ (z 2 = z 13) ∧ (¬(z 13 = z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c10 : ¬((z 3 = z 12) ∧ (B.Adj (z 7) (z 12)) ∧ (¬(B.Adj (z 3) (z 7)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)
  have c11 : ¬((B.Adj (z 3) (z 11)) ∧ (B.Adj (z 3) (z 16)) ∧ (B.Adj (z 11) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)
  have c12 : ¬((z 3 = z 14) ∧ (z 3 = z 12) ∧ (¬(z 12 = z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c13 : ¬((z 3 = z 12) ∧ (¬(B.Adj (z 3) (z 16))) ∧ (B.Adj (z 12) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h3)
  have c14 : ¬((z 3 = z 15) ∧ (z 3 = z 13) ∧ (¬(z 13 = z 15))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c15 : ¬((z 4 = z 12) ∧ (¬(B.Adj (z 4) (z 16))) ∧ (B.Adj (z 12) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h3)
  have c16 : ¬((z 5 = z 12) ∧ (¬(B.Adj (z 5) (z 16))) ∧ (B.Adj (z 12) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h3)
  have c17 : ¬((z 8 = z 17) ∧ (z 6 = z 17) ∧ (¬(z 6 = z 8))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2).trans (h1.symm))
  have c18 : ¬((B.Adj (z 6) (z 10)) ∧ (B.Adj (z 6) (z 14)) ∧ (B.Adj (z 10) (z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1,h2,h3⟩)
  have c19 : ¬((z 6 = z 16) ∧ (B.Adj (z 12) (z 16)) ∧ (¬(B.Adj (z 6) (z 12)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)
  have c20 : ¬((z 6 = z 16) ∧ (B.Adj (z 14) (z 16)) ∧ (¬(B.Adj (z 6) (z 14)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)
  have c21 : ¬((z 6 = z 17) ∧ (¬(B.Adj (z 16) (z 17))) ∧ (B.Adj (z 6) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h3.symm)
  have c22 : ¬((z 7 = z 16) ∧ (B.Adj (z 12) (z 16)) ∧ (¬(B.Adj (z 7) (z 12)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)
  have c23 : ¬((z 8 = z 16) ∧ (z 8 = z 14) ∧ (¬(z 14 = z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c24 : ¬((z 8 = z 17) ∧ (z 8 = z 15) ∧ (¬(z 15 = z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c25 : ¬((z 9 = z 16) ∧ (z 9 = z 14) ∧ (¬(z 14 = z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c26 : ¬((z 9 = z 17) ∧ (z 9 = z 15) ∧ (¬(z 15 = z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h2.symm).trans (h1))
  have c27 : ¬((z 12 = z 14) ∧ (B.Adj (z 13) (z 14)) ∧ (¬(B.Adj (z 12) (z 13)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1.symm) (rfl)) h2.symm)
  have c28 : ¬((z 13 = z 17) ∧ (¬(B.Adj (z 12) (z 13))) ∧ (B.Adj (z 12) (z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h3)
  have c29 : ¬((z 12 = z 14) ∧ (B.Adj (z 12) (z 16)) ∧ (¬(B.Adj (z 14) (z 16)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)
  have c30 : ¬((z 14 = z 16) ∧ (¬(B.Adj (z 12) (z 14))) ∧ (B.Adj (z 12) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h3)
  have c31 : ¬((z 12 = z 14) ∧ (B.Adj (z 12) (z 17)) ∧ (¬(B.Adj (z 14) (z 17)))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 (Eq.mp (congrArg₂ B.Adj (h1) (rfl)) h2)
  have c32 : ¬((z 13 = z 15) ∧ (¬(B.Adj (z 14) (z 15))) ∧ (B.Adj (z 13) (z 14))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1)) h3.symm)
  have c33 : ¬((z 14 = z 16) ∧ (¬(B.Adj (z 13) (z 14))) ∧ (B.Adj (z 13) (z 16))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h3)
  have c34 : ¬((z 13 = z 15) ∧ (z 15 = z 17) ∧ (¬(z 13 = z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h3 ((h1).trans (h2))
  have c35 : ¬((z 15 = z 17) ∧ (¬(B.Adj (z 14) (z 15))) ∧ (B.Adj (z 14) (z 17))) := by
    rintro ⟨h1,h2,h3⟩
    exact h2 (Eq.mp (congrArg₂ B.Adj (rfl) (h1.symm)) h3)
  have c36 : ¬((B.Adj (z 12) (z 13))) := by
    intro h1
    exact h.indep₀ h1
  have c37 : ¬((B.Adj (z 14) (z 15))) := by
    intro h1
    exact h.indep₁ h1
  have c38 : ¬((B.Adj (z 16) (z 17))) := by
    intro h1
    exact h.indep₂ h1
  have c39 : ¬((¬(z 2 = z 12)) ∧ (¬(z 3 = z 12)) ∧ (¬(z 2 = z 13)) ∧ (¬(z 3 = z 13))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₀ with hm | hm | hm | hm
    · exact h1 hm
    · exact h3 hm
    · exact h2 hm
    · exact h4 hm
  have c40 : ¬((¬(z 2 = z 14)) ∧ (¬(z 3 = z 14)) ∧ (¬(z 2 = z 15)) ∧ (¬(z 3 = z 15))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₁ with hm | hm | hm | hm
    · exact h1 hm
    · exact h3 hm
    · exact h2 hm
    · exact h4 hm
  have c41 : ¬((¬(z 4 = z 12)) ∧ (¬(z 4 = z 13)) ∧ (¬(z 5 = z 12)) ∧ (¬(z 5 = z 13))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₂ with hm | hm | hm | hm
    · exact h1 hm
    · exact h2 hm
    · exact h3 hm
    · exact h4 hm
  have c42 : ¬((¬(z 6 = z 16)) ∧ (¬(z 7 = z 16)) ∧ (¬(z 6 = z 17)) ∧ (¬(z 7 = z 17))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₃ with hm | hm | hm | hm
    · exact h1 hm
    · exact h3 hm
    · exact h2 hm
    · exact h4 hm
  have c43 : ¬((¬(B.Adj (z 12) (z 16))) ∧ (¬(B.Adj (z 13) (z 16)))) := by
    rintro ⟨h1,h2⟩
    exact h.near₀.elim h1 h2
  have c44 : ¬((¬(B.Adj (z 12) (z 16))) ∧ (¬(B.Adj (z 12) (z 17)))) := by
    rintro ⟨h1,h2⟩
    exact h.near₁.elim h1 h2
  have c45 : ¬((¬(B.Adj (z 12) (z 17))) ∧ (¬(B.Adj (z 13) (z 17)))) := by
    rintro ⟨h1,h2⟩
    exact h.near₂.elim h1 h2
  have c46 : ¬((¬(z 8 = z 14)) ∧ (¬(z 8 = z 15)) ∧ (¬(z 9 = z 14)) ∧ (¬(z 9 = z 15))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₄ with hm | hm | hm | hm
    · exact h1 hm
    · exact h2 hm
    · exact h3 hm
    · exact h4 hm
  have c47 : ¬((¬(z 8 = z 16)) ∧ (¬(z 8 = z 17)) ∧ (¬(z 9 = z 16)) ∧ (¬(z 9 = z 17))) := by
    rintro ⟨h1,h2,h3,h4⟩
    rcases h.meet₅ with hm | hm | hm | hm
    · exact h1 hm
    · exact h2 hm
    · exact h3 hm
    · exact h4 hm
  have c48 : ¬((z 2 = z 4) ∧ (¬(z 2 = z 8))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 2 4
    change (z 2 = z 4 ↔ z 2 = z 8) at hp
    exact h2 (hp.mp h1)
  have c49 : ¬((B.Adj (z 2) (z 6)) ∧ (¬(B.Adj (z 6) (z 10)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 2 2 6
    change (B.Adj (z 2) (z 6) ↔ B.Adj (z 6) (z 10)) at hp
    exact h2 (hp.mp h1)
  have c50 : ¬((z 2 = z 13) ∧ (¬(z 2 = z 15))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 2 9
    change (z 2 = z 13 ↔ z 2 = z 15) at hp
    exact h2 (hp.mp h1)
  have c51 : ¬((z 2 = z 15) ∧ (¬(z 2 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 2 9
    change (z 2 = z 15 ↔ z 2 = z 13) at hp
    exact h2 (hp.mp h1)
  have c52 : ¬((z 2 = z 13) ∧ (¬(z 6 = z 17))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 2 2 9
    change (z 2 = z 13 ↔ z 6 = z 17) at hp
    exact h2 (hp.mp h1)
  have c53 : ¬((z 6 = z 17) ∧ (¬(z 2 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 2 9
    change (z 6 = z 17 ↔ z 2 = z 13) at hp
    exact h2 (hp.mp h1)
  have c54 : ¬((z 3 = z 12) ∧ (¬(z 3 = z 14))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 3 8
    change (z 3 = z 12 ↔ z 3 = z 14) at hp
    exact h2 (hp.mp h1)
  have c55 : ¬((z 3 = z 14) ∧ (¬(z 3 = z 12))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 3 8
    change (z 3 = z 14 ↔ z 3 = z 12) at hp
    exact h2 (hp.mp h1)
  have c56 : ¬((z 3 = z 12) ∧ (¬(z 7 = z 16))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 2 3 8
    change (z 3 = z 12 ↔ z 7 = z 16) at hp
    exact h2 (hp.mp h1)
  have c57 : ¬((z 7 = z 16) ∧ (¬(z 3 = z 12))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 3 8
    change (z 7 = z 16 ↔ z 3 = z 12) at hp
    exact h2 (hp.mp h1)
  have c58 : ¬((z 3 = z 13) ∧ (¬(z 3 = z 15))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 3 9
    change (z 3 = z 13 ↔ z 3 = z 15) at hp
    exact h2 (hp.mp h1)
  have c59 : ¬((z 3 = z 15) ∧ (¬(z 3 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 3 9
    change (z 3 = z 15 ↔ z 3 = z 13) at hp
    exact h2 (hp.mp h1)
  have c60 : ¬((z 7 = z 17) ∧ (¬(z 3 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 3 9
    change (z 7 = z 17 ↔ z 3 = z 13) at hp
    exact h2 (hp.mp h1)
  have c61 : ¬((z 6 = z 8) ∧ (¬(z 2 = z 4))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 2 4
    change (z 6 = z 8 ↔ z 2 = z 4) at hp
    exact h2 (hp.mp h1)
  have c62 : ¬((z 8 = z 15) ∧ (¬(z 4 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 4 9
    change (z 8 = z 15 ↔ z 4 = z 13) at hp
    exact h2 (hp.mp h1)
  have c63 : ¬((z 4 = z 13) ∧ (¬(z 8 = z 17))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 2 4 9
    change (z 4 = z 13 ↔ z 8 = z 17) at hp
    exact h2 (hp.mp h1)
  have c64 : ¬((z 8 = z 17) ∧ (¬(z 4 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 4 9
    change (z 8 = z 17 ↔ z 4 = z 13) at hp
    exact h2 (hp.mp h1)
  have c65 : ¬((z 5 = z 12) ∧ (¬(z 9 = z 14))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 5 8
    change (z 5 = z 12 ↔ z 9 = z 14) at hp
    exact h2 (hp.mp h1)
  have c66 : ¬((z 9 = z 14) ∧ (¬(z 5 = z 12))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 5 8
    change (z 9 = z 14 ↔ z 5 = z 12) at hp
    exact h2 (hp.mp h1)
  have c67 : ¬((z 5 = z 12) ∧ (¬(z 9 = z 16))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 2 5 8
    change (z 5 = z 12 ↔ z 9 = z 16) at hp
    exact h2 (hp.mp h1)
  have c68 : ¬((z 9 = z 16) ∧ (¬(z 5 = z 12))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 5 8
    change (z 9 = z 16 ↔ z 5 = z 12) at hp
    exact h2 (hp.mp h1)
  have c69 : ¬((z 9 = z 15) ∧ (¬(z 5 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 5 9
    change (z 9 = z 15 ↔ z 5 = z 13) at hp
    exact h2 (hp.mp h1)
  have c70 : ¬((z 5 = z 13) ∧ (¬(z 9 = z 17))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 2 5 9
    change (z 5 = z 13 ↔ z 9 = z 17) at hp
    exact h2 (hp.mp h1)
  have c71 : ¬((z 9 = z 17) ∧ (¬(z 5 = z 13))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 2 0 5 9
    change (z 9 = z 17 ↔ z 5 = z 13) at hp
    exact h2 (hp.mp h1)
  have c72 : ¬((z 3 = z 14) ∧ (¬(z 3 = z 12))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 1 0 3 8
    change (z 3 = z 14 ↔ z 3 = z 12) at hp
    exact h2 (hp.mp h1)
  have c73 : ¬((z 4 = z 13) ∧ (¬(z 8 = z 15))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 4 9
    change (z 4 = z 13 ↔ z 8 = z 15) at hp
    exact h2 (hp.mp h1)
  have c74 : ¬((z 5 = z 13) ∧ (¬(z 9 = z 15))) := by
    rintro ⟨h1,h2⟩
    have hp := h.eq_pattern 0 1 5 9
    change (z 5 = z 13 ↔ z 9 = z 15) at hp
    exact h2 (hp.mp h1)
  have c75 : ¬((B.Adj (z 4) (z 16)) ∧ (¬(B.Adj (z 0) (z 12)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 2 0 0 8
    change (B.Adj (z 4) (z 16) ↔ B.Adj (z 0) (z 12)) at hp
    exact h2 (hp.mp h1)
  have c76 : ¬((B.Adj (z 5) (z 16)) ∧ (¬(B.Adj (z 1) (z 12)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 2 0 1 8
    change (B.Adj (z 5) (z 16) ↔ B.Adj (z 1) (z 12)) at hp
    exact h2 (hp.mp h1)
  have c77 : ¬((B.Adj (z 2) (z 14)) ∧ (¬(B.Adj (z 2) (z 12)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 1 0 2 8
    change (B.Adj (z 2) (z 14) ↔ B.Adj (z 2) (z 12)) at hp
    exact h2 (hp.mp h1)
  have c78 : ¬((B.Adj (z 2) (z 12)) ∧ (¬(B.Adj (z 6) (z 16)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 2 2 8
    change (B.Adj (z 2) (z 12) ↔ B.Adj (z 6) (z 16)) at hp
    exact h2 (hp.mp h1)
  have c79 : ¬((B.Adj (z 6) (z 12)) ∧ (¬(B.Adj (z 10) (z 14)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 1 6 8
    change (B.Adj (z 6) (z 12) ↔ B.Adj (z 10) (z 14)) at hp
    exact h2 (hp.mp h1)
  have c80 : ¬((B.Adj (z 3) (z 7)) ∧ (¬(B.Adj (z 3) (z 11)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 1 3 7
    change (B.Adj (z 3) (z 7) ↔ B.Adj (z 3) (z 11)) at hp
    exact h2 (hp.mp h1)
  have c81 : ¬((B.Adj (z 7) (z 12)) ∧ (¬(B.Adj (z 11) (z 16)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 2 7 8
    change (B.Adj (z 7) (z 12) ↔ B.Adj (z 11) (z 16)) at hp
    exact h2 (hp.mp h1)
  have c82 : ¬((B.Adj (z 0) (z 12)) ∧ (¬(B.Adj (z 0) (z 14)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 1 0 8
    change (B.Adj (z 0) (z 12) ↔ B.Adj (z 0) (z 14)) at hp
    exact h2 (hp.mp h1)
  have c83 : ¬((B.Adj (z 1) (z 12)) ∧ (¬(B.Adj (z 1) (z 14)))) := by
    rintro ⟨h1,h2⟩
    have hp := h.adj_pattern 0 1 1 8
    change (B.Adj (z 1) (z 12) ↔ B.Adj (z 1) (z 14)) at hp
    exact h2 (hp.mp h1)
  have hh := Erdos595PairAnchorSAT.finite_obstruction
    (z 2 = z 4)
    (z 2 = z 8)
    (z 2 = z 12)
    (z 2 = z 13)
    (z 2 = z 14)
    (z 2 = z 15)
    (z 2 = z 17)
    (z 3 = z 12)
    (z 3 = z 13)
    (z 3 = z 14)
    (z 3 = z 15)
    (z 4 = z 12)
    (z 4 = z 13)
    (z 5 = z 12)
    (z 5 = z 13)
    (z 6 = z 8)
    (z 6 = z 16)
    (z 6 = z 17)
    (z 7 = z 16)
    (z 7 = z 17)
    (z 8 = z 14)
    (z 8 = z 15)
    (z 8 = z 16)
    (z 8 = z 17)
    (z 9 = z 14)
    (z 9 = z 15)
    (z 9 = z 16)
    (z 9 = z 17)
    (z 12 = z 14)
    (z 13 = z 15)
    (z 13 = z 17)
    (z 14 = z 16)
    (z 15 = z 17)
    (B.Adj (z 0) (z 12))
    (B.Adj (z 0) (z 14))
    (B.Adj (z 1) (z 12))
    (B.Adj (z 1) (z 14))
    (B.Adj (z 2) (z 6))
    (B.Adj (z 2) (z 12))
    (B.Adj (z 2) (z 14))
    (B.Adj (z 2) (z 16))
    (B.Adj (z 3) (z 7))
    (B.Adj (z 3) (z 11))
    (B.Adj (z 3) (z 16))
    (B.Adj (z 4) (z 16))
    (B.Adj (z 5) (z 16))
    (B.Adj (z 6) (z 10))
    (B.Adj (z 6) (z 12))
    (B.Adj (z 6) (z 14))
    (B.Adj (z 6) (z 16))
    (B.Adj (z 7) (z 12))
    (B.Adj (z 10) (z 14))
    (B.Adj (z 11) (z 16))
    (B.Adj (z 12) (z 13))
    (B.Adj (z 12) (z 14))
    (B.Adj (z 12) (z 16))
    (B.Adj (z 12) (z 17))
    (B.Adj (z 13) (z 14))
    (B.Adj (z 13) (z 16))
    (B.Adj (z 13) (z 17))
    (B.Adj (z 14) (z 15))
    (B.Adj (z 14) (z 16))
    (B.Adj (z 14) (z 17))
    (B.Adj (z 16) (z 17))
  exact (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c0 c1) (fun hh => hh.elim c2 (fun hh => hh.elim c3 c4))) (fun hh => hh.elim (fun hh => hh.elim c5 c6) (fun hh => hh.elim c7 (fun hh => hh.elim c8 c9)))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c10 c11) (fun hh => hh.elim c12 (fun hh => hh.elim c13 c14))) (fun hh => hh.elim (fun hh => hh.elim c15 (fun hh => hh.elim c16 c17)) (fun hh => hh.elim c18 (fun hh => hh.elim c19 c20))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c21 c22) (fun hh => hh.elim c23 (fun hh => hh.elim c24 c25))) (fun hh => hh.elim (fun hh => hh.elim c26 c27) (fun hh => hh.elim c28 (fun hh => hh.elim c29 c30)))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c31 c32) (fun hh => hh.elim c33 (fun hh => hh.elim c34 c35))) (fun hh => hh.elim (fun hh => hh.elim c36 (fun hh => hh.elim c37 c38)) (fun hh => hh.elim c39 (fun hh => hh.elim c40 c41)))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c42 c43) (fun hh => hh.elim c44 (fun hh => hh.elim c45 c46))) (fun hh => hh.elim (fun hh => hh.elim c47 c48) (fun hh => hh.elim c49 (fun hh => hh.elim c50 c51)))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c52 c53) (fun hh => hh.elim c54 (fun hh => hh.elim c55 c56))) (fun hh => hh.elim (fun hh => hh.elim c57 (fun hh => hh.elim c58 c59)) (fun hh => hh.elim c60 (fun hh => hh.elim c61 c62))))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c63 c64) (fun hh => hh.elim c65 (fun hh => hh.elim c66 c67))) (fun hh => hh.elim (fun hh => hh.elim c68 c69) (fun hh => hh.elim c70 (fun hh => hh.elim c71 c72)))) (fun hh => hh.elim (fun hh => hh.elim (fun hh => hh.elim c73 c74) (fun hh => hh.elim c75 (fun hh => hh.elim c76 c77))) (fun hh => hh.elim (fun hh => hh.elim c78 (fun hh => hh.elim c79 c80)) (fun hh => hh.elim c81 (fun hh => hh.elim c82 c83))))))) hh

#print axioms no_pattern
end Erdos595PairAnchorPattern
