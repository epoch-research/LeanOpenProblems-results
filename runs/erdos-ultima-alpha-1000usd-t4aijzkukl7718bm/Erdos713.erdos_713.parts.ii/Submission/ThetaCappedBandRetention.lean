import FormalConjecturesUtil
import Submission.ThetaBalancedRandomSplitting
import Submission.ThetaSingletonRowPadding
import Submission.ThetaCappedGramPreparation

/-! Retaining a codegree band after balanced splitting, with a linear
column-degree cap and an explicit row-count budget. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCappedBandRetention
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
open Erdos713ThetaBalancedSplit Erdos713ThetaBalancedRandomSplitting
variable {A B : Type} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

lemma twice_rows_of_cube (m k : ℕ) (hm : 0 < m) (h : k^3 ≤ 8*m^2) : k ≤ 2*m := by
  have hp : m^2 ≤ m^3 := by
    simpa only [pow_succ] using Nat.le_mul_of_pos_right (m^2) hm
  have hc : k^3 ≤ (2*m)^3 := by
    calc
      _ ≤ 8*m^2 := h
      _ ≤ 8*m^3 := Nat.mul_le_mul_left 8 hp
      _ = _ := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hc

/-- All output columns have the same degree. The extra rows used to
balance the original neighborhoods are singletons or isolated. -/
theorem exists_retention (R : A → B → Prop) (hR : ¬ HasTheta R)
    (hm : 0 < Nat.card A) (hk : 0 < Nat.card B) (D T : ℕ) (hT : 0 < T)
    (hD : ∀ b, Nat.card {a // R a b} ≤ D)
    (hscale : D ≤ Nat.card B*T^2)
    (hshape : (Nat.card B*T)^3 ≤ 8*(Nat.card A)^2)
    (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*T^2 ≤ codegree R p.1 p.2 ∧
      codegree R p.1 p.2 < 32*T^2) :
    ∃ (A' B' : Type) (_ : Fintype A') (_ : Fintype B') (S : A' → B' → Prop),
      ¬ HasTheta S ∧ 0 < Nat.card A' ∧
      Nat.card A' ≤ 3*Nat.card A+D*Nat.card B ∧
      Nat.card B' = Nat.card B*T ∧
      (∀ b, Nat.card {a // S a b} ≤ 2*Nat.card B') ∧
      (Nat.card B')^3 ≤ 8*(Nat.card A')^2 ∧
      (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*heavyCount S := by
  classical
  let s := D/T+1
  let W := s*T
  obtain ⟨hs,hDW,hWD⟩ := balanced_cap (e := D) hT
  have hsmall : Nat.card B*T ≤ 2*Nat.card A := twice_rows_of_cube _ _ hm hshape
  have hsCap : s ≤ 2*(Nat.card B*T) := by
    have hd := Nat.div_le_div_right (c := T) hscale
    have he : Nat.card B*T^2/T = Nat.card B*T := by
      rw [pow_two,← mul_assoc,Nat.mul_div_cancel _ hT]
    rw [he] at hd
    have hp : 1 ≤ Nat.card B*T := Nat.mul_pos hk hT
    dsimp only [s]
    omega
  let A' := Erdos713ThetaSingletonRowPadding.Rows A B W
  let R' : A' → B → Prop := Erdos713ThetaSingletonRowPadding.Inc R W
  have hcol (b : B) : Nat.card {a // R' a b} = W :=
    Erdos713ThetaSingletonRowPadding.column_card R W b ((hD b).trans hDW)
  let e (b : B) : {a // R' a b} ≃ (Fin T × Fin s) := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hcol]
    simp only [Fintype.card_prod,Fintype.card_fin,W,Nat.mul_comm])
  haveI : Nonempty (Fin T) := ⟨⟨0,hT⟩⟩
  haveI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  let Ω := B → Equiv.Perm (Fin T × Fin s)
  let f : Ω → ℕ := fun σ => heavyCount (Inc R' e σ)
  obtain ⟨σ,_hσ,hσ⟩ := exists_max_image (univ : Finset Ω) f univ_nonempty
  have hband := band_mass_le R' e P (by
    intro p hp
    have hh := hP p hp
    rw [Erdos713ThetaSingletonRowPadding.pair_codegree R W hh.1]
    simpa only [Fintype.card_fin] using hh) (f σ) (fun τ => hσ τ (mem_univ _))
  have hband' : (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*f σ := by
    have he : (∑ p ∈ P, codegree R' p.1 p.2) = ∑ p ∈ P, codegree R p.1 p.2 := by
      apply sum_congr rfl
      intro p hp
      exact Erdos713ThetaSingletonRowPadding.pair_codegree R W (hP p hp).1
    rwa [he] at hband
  have hcardA : Nat.card A' = Nat.card A+Nat.card B*W :=
    Erdos713ThetaSingletonRowPadding.rows_card W
  have hAge : Nat.card A ≤ Nat.card A' := by rw [hcardA]; omega
  have hAupper : Nat.card A' ≤ 3*Nat.card A+D*Nat.card B := by
    have hh := Nat.mul_le_mul_left (Nat.card B) hWD
    change Nat.card B*W ≤ Nat.card B*(D+T) at hh
    rw [hcardA]
    nlinarith only [hh,hsmall]
  refine ⟨A',B × Fin T,inferInstance,inferInstance,Inc R' e σ,
    no_theta (Erdos713ThetaSingletonRowPadding.no_theta hR W) e σ,
    hm.trans_le hAge,hAupper,by simp only [Nat.card_prod,Nat.card_fin],?_,?_,hband'⟩
  · intro b
    rw [column_card,Nat.card_fin,Nat.card_prod,Nat.card_fin]
    exact hsCap
  · simp only [Nat.card_prod,Nat.card_fin]
    exact hshape.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hAge 2))

#print axioms exists_retention
end Erdos713ThetaCappedBandRetention
