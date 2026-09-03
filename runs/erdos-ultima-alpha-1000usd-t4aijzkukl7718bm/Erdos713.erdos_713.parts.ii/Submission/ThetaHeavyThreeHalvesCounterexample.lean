import FormalConjecturesUtil
import Submission.ThetaHeavyEdgeCounterexample
import Submission.ThetaGramPowerSize

/-! A three-halves error term does not restore a universal heavy-pair
bound for oriented-theta-free relations. This is not a disproof of Erdos 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaHeavyThreeHalvesCounterexample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaC4Deletion
open Erdos713ThetaAffineStars Erdos713ThetaRandomSplitting
open Erdos713ThetaHeavyEdgeCounterexample
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

lemma below_mass_le_ceiling (R : A → B → Prop) (M Q : ℕ)
    (hQ : ∀ x y, x ≠ y → codegree R x y ≤ Q)
    (hM : ∀ j : ℕ, 8*4^j ≤ Q → ∀ s : A → B → Fin (2^j),
      heavyCount (split R s) ≤ M) (L : ℕ) :
    (∑ p ∈ below R L, codegree R p.1 p.2) ≤ 8*(Nat.card B)^2+64*L*M := by
  induction L with
  | zero =>
    simp only [Nat.mul_zero,zero_mul,add_zero]
    calc
      _ ≤ ∑ _p ∈ below R 0, 8 := sum_le_sum (fun p hp => by
        have hh := (mem_filter.mp hp).2.2
        simpa only [pow_zero,mul_one] using hh.le)
      _ ≤ 8*Fintype.card (B × B) := by
        simpa only [sum_const,nsmul_eq_mul,card_univ,Nat.mul_comm] using
          Nat.mul_le_mul_left 8 (card_le_card (subset_univ (below R 0)))
      _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_prod,pow_two]
  | succ L ih =>
    have hb : (∑ p ∈ band R L, codegree R p.1 p.2) ≤ 64*M := by
      by_cases hcrit : 8*4^L ≤ Q
      · haveI : Nonempty (Fin (2^L)) := ⟨⟨0,pow_pos (by decide) _⟩⟩
        have hp : (2^L)^2 = 4^L := by rw [← pow_mul,Nat.mul_comm L 2,pow_mul]; rfl
        apply band_mass_le (T := Fin (2^L)) R (band R L) ?_ M (hM L hcrit)
        intro p hpP
        have hh := (mem_filter.mp hpP).2
        simp only [Fintype.card_fin,hp]
        refine ⟨hh.1,hh.2.1,?_⟩
        have he : 8*4^(L+1) = 32*4^L := by rw [pow_succ]; ring
        simpa only [he] using hh.2.2
      · have he : band R L = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          have hh := (mem_filter.mp hp).2
          exact hcrit (hh.2.1.trans (hQ p.1 p.2 hh.1))
        simp only [he,sum_empty]
        exact Nat.zero_le _
    rw [below_step]
    nlinarith only [ih,hb]

omit [Fintype A] [Fintype B] in
lemma exists_large_power (C D : ℕ) :
    ∃ t : ℕ, 64*C*(D+15300*t)+10 < 2^(2*t) := by
  let U := 64*C*(D+15300)
  let t := U+20
  have ht : 20 ≤ t := by dsimp [t]; omega
  have hDt : D ≤ D*t := Nat.le_mul_of_pos_right D (by omega)
  have hb : 64*C*(D+15300*t) ≤ U*t := by
    have hh := Nat.mul_le_mul_left (64*C) hDt
    dsimp only [U]
    nlinarith only [hh]
  have he : t*t = U*t+20*t := by dsimp only [t]; ring
  have hp := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  refine ⟨t,?_⟩
  nlinarith only [ht,hb,he,hp]

/-- The heavy-count/incidence ratio is unbounded even when the column
three-halves power is at most the row count. No column-degree cap is asserted. -/
theorem exists_counterexample (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ Nat.card A ≤ edges R ∧
      (Nat.card B)^3 ≤ (Nat.card A)^2 ∧ C*edges R < heavyCount R := by
  classical
  let D := Erdos713ThetaGramPowerSize.scale^75
  obtain ⟨t,ht⟩ := exists_large_power C D
  let r := 2^(2*t)
  let L := D+15300*t
  have hr : 1 ≤ r := Nat.one_le_pow _ _ (by decide)
  have hgap : 64*C*L+10 < r := ht
  obtain ⟨A,B,iA,iB,R,Q,hfree,hkm,hsize,hrows,hQ,hshape⟩ :=
    Erdos713ThetaGramPowerSize.exists_examples r hr
  have hA : 0 < Nat.card A := lt_of_le_of_lt (Nat.zero_le _) hkm
  have hedges : edges R = Nat.card A*r := by
    rw [edges, Erdos713ThetaSplit.edge_card_eq_rows]
    simp only [hrows, sum_const, card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.cast_id]
  have hm : Nat.card A < 8*4^L := by
    calc
      _ ≤ D*r^7650 := hsize
      _ ≤ 2^D*r^7650 := Nat.mul_le_mul_right _ (show D ≤ 2^D from Nat.lt_two_pow_self.le)
      _ = 2^L := by dsimp only [r,L]; rw [← pow_mul,← pow_add]; congr 1; ring
      _ ≤ 4^L := Nat.pow_le_pow_left (by decide) L
      _ < 8*4^L := by have hh := pow_pos (by decide : 0 < (4 : ℕ)) L; omega
  have hex : ∃ j : ℕ, 8*4^j ≤ Q ∧ ∃ s : A → B → Fin (2^j),
      C*edges R < heavyCount (split R s) := by
    by_contra! hn
    have hmass := below_mass_le_ceiling R (C*edges R) Q hQ hn L
    rw [full_mass R r hrows L hm,hedges] at hmass
    have hsmall : (Nat.card B)^2 ≤ Nat.card A := hkm.le
    have hfin : r*(r-1) ≤ 8+64*L*C*r := by
      apply Nat.le_of_mul_le_mul_left (c := Nat.card A) _ hA
      calc
        _ = Nat.card A*r*(r-1) := by ring
        _ ≤ 8*(Nat.card B)^2+64*L*(C*(Nat.card A*r)) := hmass
        _ ≤ Nat.card A*(8+64*L*C*r) := by nlinarith only [hsmall]
    have hsub : r-1+1 = r := Nat.sub_add_cancel hr
    have hprod := Nat.mul_le_mul_left r (show 64*C*L+10 ≤ r from hgap.le)
    nlinarith only [hfin,hsub,hprod,hr]
  obtain ⟨j,hj,s,hs⟩ := hex
  have hp : (2^j)^2 = 4^j := by rw [← pow_mul,Nat.mul_comm j 2,pow_mul]; rfl
  have hT : (2^j)^2 ≤ Q := by rw [hp]; omega
  refine ⟨A,B × Fin (2^j),inferInstance,inferInstance,split R s,
    no_theta hfree s,hA,?_,?_,?_⟩
  · rw [Erdos713ThetaRandomSplitting.edge_card,hedges]
    exact Nat.le_mul_of_pos_right _ hr
  · simpa only [Nat.card_prod,Nat.card_fin] using hshape (2^j) hT
  · simpa only [Erdos713ThetaRandomSplitting.edge_card] using hs

/-- The natural-number form avoids rounding or real-power conventions. -/
theorem exists_row_counterexample (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ (Nat.card B)^3 ≤ (Nat.card A)^2 ∧
      C*Nat.card A < heavyCount R := by
  obtain ⟨A,B,iA,iB,R,hf,hm,he,hsize,hbig⟩ := exists_counterexample C
  exact ⟨A,B,iA,iB,R,hf,hm,hsize,(Nat.mul_le_mul_left C he).trans_lt hbig⟩

lemma sqrt_term_le_of_cube_le (k m : ℕ) (h : k^3 ≤ m^2) :
    (k : ℝ)*Real.sqrt k ≤ m := by
  have he : ((k : ℝ)*Real.sqrt k)^2 = (k : ℝ)^3 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg k)]
    ring
  apply (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ k*Real.sqrt k) (Nat.cast_nonneg m)).mp
  rw [he]
  exact_mod_cast h

/-- There is no universal bound with a row term and a three-halves
column term, even under the additional cubic size restriction. -/
theorem no_three_halves_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (Nat.card B)^3 ≤ (Nat.card A)^2 →
        (heavyCount R : ℝ) ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card B)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C)
  obtain ⟨A,B,iA,iB,R,hfree,hm,hsize,hbig⟩ := exists_row_counterexample N
  have hmR : (0 : ℝ) < Nat.card A := Nat.cast_pos.mpr hm
  have hlo : (N : ℝ)*(Nat.card A : ℝ) < heavyCount R := by exact_mod_cast hbig
  have hu := hBound A B R hfree hsize
  have hsmall := sqrt_term_le_of_cube_le (Nat.card B) (Nat.card A) hsize
  have hscaled := mul_le_mul_of_nonneg_left hsmall hC.le
  have hNscaled := mul_lt_mul_of_pos_right hN hmR
  nlinarith only [hlo,hu,hscaled,hNscaled]

#print axioms below_mass_le_ceiling
#print axioms exists_counterexample
#print axioms exists_row_counterexample
#print axioms no_three_halves_bound
end Erdos713ThetaHeavyThreeHalvesCounterexample
