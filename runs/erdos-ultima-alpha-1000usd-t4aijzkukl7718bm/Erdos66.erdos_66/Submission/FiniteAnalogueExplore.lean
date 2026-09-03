import Submission.CosetExplore

/-!
# A finite-group analogue with logarithmic-scale representation counts

This construction produces finite additive groups, not a set of natural numbers.
-/

namespace Erdos66FiniteAnalogue

open Erdos66Coset Erdos66OriginRepair

/-- The finite-field hypotheses can be realized for every odd extension degree at least three. -/
lemma exists_flat_finite_field (K : Type*) [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (d : ℕ) (hd : Odd d) (hdim : 2 ≤ d) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F),
      Fintype.card F = Fintype.card K ^ (2 * d) ∧
      ∃ (A : Finset (F × F)) (E : ℤ), 0 ≤ E ∧ E ^ 2 ≤ 3 * (Fintype.card K : ℤ) ^ 3 ∧
        ∀ z : F × F, |(pairCount A A z : ℤ) - (Fintype.card K : ℤ) ^ 2| ≤
          E + 2 * Fintype.card K + 6 := by
  classical
  let p := ringChar K
  letI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let L := FiniteField.Extension K p 2
  letI : Fintype L := Fintype.ofFinite L
  letI : CharP L p := charP_of_injective_algebraMap' K p
  letI : NeZero d := ⟨by omega⟩
  let F := FiniteField.Extension L p d
  letI : Fintype F := Fintype.ofFinite F
  letI : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  have hKL : Module.finrank K L = 2 := FiniteField.finrank_extension K p 2
  have hLF : Module.finrank L F = d := FiniteField.finrank_extension L p d
  have hcL : Fintype.card L = Fintype.card K ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.natCard_extension K p 2
  have hcF : Fintype.card F = Fintype.card K ^ (2 * d) := by
    rw [Module.card_eq_pow_finrank (K := L) (V := F), hLF, hcL, ← pow_mul]
  exact ⟨F, inferInstance, inferInstance, inferInstance, hcF,
    exists_flat_sumset_of_tower (K := K) (L := L) (F := F) hK hKL (hLF.symm ▸ hd) (hLF.symm ▸ hdim)⟩

end Erdos66FiniteAnalogue
