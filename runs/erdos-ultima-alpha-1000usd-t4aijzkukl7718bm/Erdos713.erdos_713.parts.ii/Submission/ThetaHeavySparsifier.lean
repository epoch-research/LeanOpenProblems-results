import FormalConjecturesUtil
import Submission.ThetaC4DeletionObstruction
import Submission.ThetaAffineStars

/-! A conditional density gap from a heavy-pair-retaining C4-free subrelation.
No existence theorem for such sparsifiers is asserted here. -/
open Finset
namespace Erdos713ThetaHeavySparsifier
open Erdos713ThetaC4Deletion Erdos713ThetaAffineStars
open Erdos713ThetaCross Erdos713GlobalLight
variable {A B : Type*}
set_option maxHeartbeats 1000000

/-- This asks to retain heavy-pair mass, NOT a fixed fraction of all incidences.
It is a hypothesis; theta exclusion is not claimed to imply it. -/
def HasSparsifier (C : ℕ) (R : A → B → Prop) : Prop :=
  ∃ Q : A → B → Prop, (∀ a b, Q a b → R a b) ∧
    FourFree Q ∧ heavyCount R ≤ C * edges Q

lemma heavy_add_light [Fintype A] [Fintype B] (R : A → B → Prop) :
    heavyCount R + lightCount R = (Nat.card B)^2 := by
  classical
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset (B × B))) (p := fun p => 3 ≤ codegree R p.1 p.2)
  have he : (univ : Finset (B × B)).filter (fun p => ¬ 3 ≤ codegree R p.1 p.2) =
      univ.filter (fun p => codegree R p.1 p.2 ≤ 2) := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [he] at h
  simpa only [heavyCount, lightCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype, card_univ, Fintype.card_prod, pow_two] using h

/-- The real square-root form of the unbalanced C4 second-moment bound. -/
lemma four_free_real_bound [Fintype A] [Fintype B] {Q : A → B → Prop}
    (hQ : FourFree Q) :
    (edges Q : ℝ) ≤ Nat.card A + (Nat.card B : ℝ) * Real.sqrt (Nat.card A) := by
  let E : ℝ := edges Q
  let m : ℝ := Nat.card A
  let k : ℝ := Nat.card B
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hc : E^2 ≤ m*(E+k^2) := by
    dsimp only [E, m, k]
    exact_mod_cast four_free_second_moment hQ
  have hs : (Real.sqrt m)^2 = m := Real.sq_sqrt hm
  change E ≤ m+k*Real.sqrt m
  by_contra hn
  have hbad : m+k*Real.sqrt m < E := lt_of_not_ge hn
  have hE : 0 < E := (by positivity : 0 ≤ m+k*Real.sqrt m).trans_lt hbad
  have hks : 0 ≤ k*Real.sqrt m := mul_nonneg hk (Real.sqrt_nonneg _)
  have hprod : (k*Real.sqrt m)^2 < E*(E-m) := by
    calc
      _ ≤ E*(k*Real.sqrt m) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by linarith : k*Real.sqrt m ≤ E) hks
      _ < E*(E-m) := mul_lt_mul_of_pos_left (by linarith) hE
  have he : (k*Real.sqrt m)^2 = m*k^2 := by rw [mul_pow, hs]; ring
  rw [he] at hprod
  nlinarith only [hc, hprod]

/-- Heavy-pair retention gives a density gap. The existence of the
sparsifier remains an explicit, substantive hypothesis. -/
theorem density_gap [Fintype A] [Fintype B] {R : A → B → Prop} {C : ℕ}
    (hS : HasSparsifier C R) :
    (Nat.card B)^2 ≤ (C^2+2*C)*Nat.card A + 2*lightCount R := by
  obtain ⟨Q, _hQR, hQ, hmass⟩ := hS
  let m : ℝ := Nat.card A
  let k : ℝ := Nat.card B
  let t : ℝ := lightCount R
  let s : ℝ := Real.sqrt m
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hs : s^2 = m := Real.sq_sqrt hm
  have he := four_free_real_bound hQ
  have hmassR : (heavyCount R : ℝ) ≤ (C : ℝ)*edges Q := by exact_mod_cast hmass
  have hupper : (heavyCount R : ℝ) ≤ (C : ℝ)*(m+k*s) :=
    hmassR.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have htotal : (heavyCount R : ℝ)+t = k^2 := by
    dsimp only [t, k]
    exact_mod_cast heavy_add_light R
  have hcross : 2*(C : ℝ)*k*s ≤ k^2+(C : ℝ)^2*m := by
    have hp : ((C : ℝ)*s)^2 = (C : ℝ)^2*m := by rw [mul_pow, hs]
    nlinarith only [sq_nonneg (k-(C : ℝ)*s), hp]
  have hfin : k^2 ≤ ((C : ℝ)^2+2*C)*m+2*t := by
    nlinarith only [hupper, htotal, hcross]
  dsimp only [k, m, t] at hfin
  exact_mod_cast hfin

#print axioms heavy_add_light
#print axioms four_free_real_bound
#print axioms density_gap
end Erdos713ThetaHeavySparsifier
