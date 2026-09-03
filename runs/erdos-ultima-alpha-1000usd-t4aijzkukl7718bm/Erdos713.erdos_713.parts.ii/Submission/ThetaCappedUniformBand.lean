import FormalConjecturesUtil
import Submission.ThetaCappedBandRetention
import Submission.ThetaSingletonRowRemoval

/-! After balanced splitting, discard the singleton padding rows.
Original row degrees are unchanged; only diagonal heavy pairs can be lost. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCappedUniformBand
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
open Erdos713ThetaBalancedSplit Erdos713ThetaBalancedRandomSplitting
variable {A B : Type} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

theorem exists_retention (R : A → B → Prop) (hR : ¬ HasTheta R)
    (hm : 0 < Nat.card A) (hk : 0 < Nat.card B) (D T : ℕ) (hT : 0 < T)
    (hD : ∀ b, Nat.card {a // R a b} ≤ D)
    (hscale : D ≤ Nat.card B*T^2)
    (hshape : (Nat.card B*T)^3 ≤ 8*(Nat.card A)^2)
    (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*T^2 ≤ codegree R p.1 p.2 ∧
      codegree R p.1 p.2 < 32*T^2) :
    ∃ S : A → (B × Fin T) → Prop,
      ¬ HasTheta S ∧ (∀ a, Nat.card {b // S a b} = Nat.card {b // R a b}) ∧
      (∀ b, Nat.card {a // S a b} ≤ 2*(Nat.card B*T)) ∧
      (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*heavyCount S+128*Nat.card A := by
  classical
  let s := D/T+1
  let W := s*T
  obtain ⟨hs,hDW,_hWD⟩ := balanced_cap (e := D) hT
  have hsmall : Nat.card B*T ≤ 2*Nat.card A :=
    Erdos713ThetaCappedBandRetention.twice_rows_of_cube _ _ hm hshape
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
  let S (σ : Ω) := Erdos713ThetaSingletonRowRemoval.restrict (Inc R' e σ)
  have hDummy (σ : Ω) (d : B × Fin W) (x y : B × Fin T)
      (hx : Inc R' e σ (.inr d) x) (hy : Inc R' e σ (.inr d) y) : x = y := by
    rcases x with ⟨b,i⟩
    rcases y with ⟨c,j⟩
    have he : b = c := hx.choose.1.symm.trans hy.choose.1
    subst c
    exact Prod.ext rfl (hx.choose_spec.symm.trans hy.choose_spec)
  have hHeavy (σ : Ω) : heavyCount (Inc R' e σ) ≤ heavyCount (S σ)+Nat.card B*T := by
    simpa only [Nat.card_prod,Nat.card_fin] using
      Erdos713ThetaSingletonRowRemoval.heavy_le_add_columns (Inc R' e σ) (hDummy σ)
  let f : Ω → ℕ := fun σ => heavyCount (S σ)
  obtain ⟨σ,_hσ,hσ⟩ := exists_max_image (univ : Finset Ω) f univ_nonempty
  have hband := band_mass_le R' e P (by
    intro p hp
    have hh := hP p hp
    rw [Erdos713ThetaSingletonRowPadding.pair_codegree R W hh.1]
    simpa only [Fintype.card_fin] using hh) (f σ+Nat.card B*T) (by
      intro τ
      exact (hHeavy τ).trans (Nat.add_le_add_right (hσ τ (mem_univ _)) _))
  have hband' : (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*f σ+128*Nat.card A := by
    have he : (∑ p ∈ P, codegree R' p.1 p.2) = ∑ p ∈ P, codegree R p.1 p.2 := by
      apply sum_congr rfl
      intro p hp
      exact Erdos713ThetaSingletonRowPadding.pair_codegree R W (hP p hp).1
    rw [he] at hband
    nlinarith only [hband,hsmall]
  refine ⟨S σ,Erdos713ThetaSingletonRowRemoval.no_theta
    (no_theta (Erdos713ThetaSingletonRowPadding.no_theta hR W) e σ),?_,?_,hband'⟩
  · intro a
    change Nat.card {b // Inc R' e σ (.inl a) b} = _
    rw [Erdos713ThetaBalancedRandomSplitting.row_card]
    rfl
  · intro b
    have hh := Erdos713ThetaSingletonRowRemoval.column_le (Inc R' e σ) b
    rw [column_card,Nat.card_fin] at hh
    exact hh.trans hsCap

#print axioms exists_retention
end Erdos713ThetaCappedUniformBand
