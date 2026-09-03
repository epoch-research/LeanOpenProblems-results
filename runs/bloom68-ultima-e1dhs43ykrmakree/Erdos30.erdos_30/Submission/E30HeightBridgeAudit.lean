import Submission.E30HeightBridge

/-!
# Kernel dependency and semantic checks for the all-height bridge

No import of `Submission.Spec`. All examples use ordinary kernel-checked proofs.
The small examples check carries and doubled-summand collisions, not asymptotics.
-/

set_option pp.funBinderTypes true

#print axioms Erdos30Research.int_isSidon_iff_differences
#print axioms Erdos30Research.edgeResidue
#print axioms Erdos30Research.edgeHeight
#print axioms Erdos30Research.heightMark
#print axioms Erdos30Research.EdgeRowsInjective
#print axioms Erdos30Research.edge_data
#print axioms Erdos30Research.residue_height_unique
#print axioms Erdos30Research.heightMark_injective
#print axioms Erdos30Research.isSidon_of_edge_rows
#print axioms Erdos30Research.HeightIndex
#print axioms Erdos30Research.liftResidue
#print axioms Erdos30Research.liftHeight
#print axioms Erdos30Research.liftResidue_bounds
#print axioms Erdos30Research.lift_coordinates_injective
#print axioms Erdos30Research.liftMark_injective
#print axioms Erdos30Research.same_residue_heavy
#print axioms Erdos30Research.allHeight_isSidon
#print axioms Erdos30Research.edge_quotient_remainder
#print axioms Erdos30Research.heavy_light_carries
#print axioms Erdos30Research.light_light_carry
#print axioms Erdos30Research.nat_set_of_integer_marks
#print axioms Erdos30Research.allHeight_nat_set
#print axioms Erdos30Research.target_modulus_card
#print axioms Erdos30Research.target_diameter_identity
#print axioms Erdos30Research.AllHeightBox
#print axioms Erdos30Research.AllHeightBox.nat_set
#print axioms Erdos30Research.not_all_power_bounds_of_allHeight_saving
#print axioms Erdos30Research.diameter_saving_of_height_gap
#print axioms Erdos30Research.not_all_power_bounds_of_allHeight_gap

#check Erdos30Research.int_isSidon_iff_differences
#print Erdos30Research.EdgeRowsInjective
#print Erdos30Research.AllHeightBox
#check Erdos30Research.isSidon_of_edge_rows
#check Erdos30Research.liftMark_injective
#check Erdos30Research.allHeight_isSidon
#check Erdos30Research.edge_quotient_remainder
#check Erdos30Research.heavy_light_carries
#check Erdos30Research.light_light_carry
#check Erdos30Research.allHeight_nat_set
#check Erdos30Research.target_diameter_identity
#check Erdos30Research.AllHeightBox.nat_set
#check Erdos30Research.not_all_power_bounds_of_allHeight_saving
#check Erdos30Research.diameter_saving_of_height_gap
#check Erdos30Research.not_all_power_bounds_of_allHeight_gap

open Erdos30Research

-- The finite map is exactly the requested m*A plus singleton-light construction.
example {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ) (a : A) :
    heightMark (m : ℤ) (@liftResidue m A) (liftHeight b) (.inl a) = (m : ℤ) * a := by
  simp [heightMark, liftResidue, liftHeight]

example {m : ℕ} {A : Finset ℤ} (b : ℤ → ℤ) (s : Fin (m - 1)) :
    heightMark (m : ℤ) (@liftResidue m A) (liftHeight b) (.inr s) =
      (s.val : ℤ) + 1 + m * b ((s.val : ℤ) + 1) := rfl

-- Negative heights really are permitted before the optional box assumptions.
example : heightMark (5 : ℤ) (@liftResidue 5 ∅) (liftHeight (fun _ => -7))
    (.inr (1 : Fin 4)) = -33 := by
  norm_num [heightMark, liftResidue, liftHeight]

-- Nonwrapping light-light edge, wrapping light-light edge, and the heavy seam.
example : edgeResidue (5 : ℤ) (fun i : Fin 5 => (i : ℤ)) (3, 1) = 2 ∧
    edgeHeight (fun i : Fin 5 => (i : ℤ)) (fun _ => 0) (3, 1) = 0 := by
  norm_num [edgeResidue, edgeHeight]

example : edgeResidue (5 : ℤ) (fun i : Fin 5 => (i : ℤ)) (1, 4) = 2 ∧
    edgeHeight (fun i : Fin 5 => (i : ℤ)) (fun _ => 0) (1, 4) = -1 := by
  norm_num [edgeResidue, edgeHeight]

example : edgeResidue (5 : ℤ) (fun i : Fin 5 => (i : ℤ)) (0, 3) = 2 ∧
    edgeHeight (fun i : Fin 5 => (i : ℤ)) (fun _ => 0) (0, 3) = -1 := by
  norm_num [edgeResidue, edgeHeight]

-- Doubled summands are not excluded: 0+2=1+1 violates strong Sidonicity.
example : ¬ IsSidon ({0, 1, 2} : Set ℤ) := by
  intro hs
  have he := hs 0 (by simp) 1 (by simp) 2 (by simp) 1 (by simp) (by norm_num)
  norm_num at he

-- For m=2, A={0,1}, b_1=0 the two distinct residue-one edges have the same
-- high difference 0. The heavy set is Sidon but its lift {0,1,2} is not.
example : IsSidon ({0, 1} : Set ℤ) := by norm_num [IsSidon]

example : ¬ EdgeRowsInjective (2 : ℤ) (@liftResidue 2 {0, 1}) (liftHeight (fun _ => 0)) := by
  intro hrows
  let e₁ : {e : HeightIndex 2 {0, 1} × HeightIndex 2 {0, 1} //
      edgeResidue (2 : ℤ) liftResidue e = 1} :=
    ⟨(.inr 0, .inl ⟨0, by simp⟩), by norm_num [edgeResidue, liftResidue]⟩
  let e₂ : {e : HeightIndex 2 {0, 1} × HeightIndex 2 {0, 1} //
      edgeResidue (2 : ℤ) liftResidue e = 1} :=
    ⟨(.inl ⟨1, by simp⟩, .inr 0), by norm_num [edgeResidue, liftResidue]⟩
  have he : e₁ = e₂ := hrows 1 (by norm_num) (by norm_num)
    (by norm_num [e₁, e₂, edgeHeight, liftResidue, liftHeight])
  have bad := congrArg (fun e => e.val.1) he
  simp [e₁, e₂] at bad

-- Semantic converse check: for any injectively indexed Sidon set, the stated
-- nonzero edge-row test is necessary as well. It tests exactly the differences.
example {ι : Type*} {m : ℤ} {r v : ι → ℤ}
    (hr : ∀ i, 0 ≤ r i ∧ r i < m) (hinj : Function.Injective (heightMark m r v))
    (hS : IsSidon (Set.range (heightMark m r v))) : EdgeRowsInjective m r v := by
  intro t ht _ e₁ e₂ he
  change edgeHeight r v e₁.val = edgeHeight r v e₂.val at he
  have hne : e₁.val.1 ≠ e₁.val.2 := by
    intro h
    have hh := e₁.property
    simp [edgeResidue, h] at hh
    omega
  have hd : heightMark m r v e₁.val.1 - heightMark m r v e₁.val.2 =
      heightMark m r v e₂.val.1 - heightMark m r v e₂.val.2 := by
    rw [(edge_data hr e₁.val).2, (edge_data hr e₂.val).2, e₁.property, e₂.property, he]
  obtain ⟨h₁, h₂⟩ := (int_isSidon_iff_differences _).mp hS
    _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ (hinj.ne hne) hd
  exact Subtype.ext (Prod.ext (hinj h₁) (hinj h₂))

-- Exact target accounting, specialized only for an arithmetic sanity check.
example : ((4 ^ 2 + 1 : ℕ) : ℤ) ^ 2 - (((4 ^ 2 - 4 + 1) * (18 + 1) : ℕ) : ℤ) =
    (4 : ℤ) ^ 2 + ((4 ^ 2 - 4 + 1 : ℕ) : ℤ) * 2 :=
  target_diameter_identity (by norm_num) (by norm_num)

example {c₀ β : ℝ} (hc₀ : 0 < c₀) : 0 < (c₀ / 2) / (2 : ℝ) ^ (1 + β / 2) := by
  positivity
