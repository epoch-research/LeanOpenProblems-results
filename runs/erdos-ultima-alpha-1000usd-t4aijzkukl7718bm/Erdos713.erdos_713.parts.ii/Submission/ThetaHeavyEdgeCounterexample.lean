import FormalConjecturesUtil
import Submission.ThetaRandomSplitting
import Submission.ThetaPolynomialSize

/-! Unbounded heavy-pair count per incidence in oriented-theta-free relations.
These are auxiliary counterexamples, not counterexamples to Erdos 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaHeavyEdgeCounterexample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaC4Deletion
open Erdos713ThetaAffineStars Erdos713ThetaRandomSplitting
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

noncomputable def below (R : A → B → Prop) (L : ℕ) : Finset (B × B) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ codegree R p.1 p.2 < 8*4^L)

noncomputable def band (R : A → B → Prop) (L : ℕ) : Finset (B × B) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ 8*4^L ≤ codegree R p.1 p.2 ∧
    codegree R p.1 p.2 < 8*4^(L+1))

omit [Fintype A] in
lemma below_step (R : A → B → Prop) (L : ℕ) :
    (∑ p ∈ below R (L+1), codegree R p.1 p.2) =
      (∑ p ∈ below R L, codegree R p.1 p.2) +
      ∑ p ∈ band R L, codegree R p.1 p.2 := by
  simp only [below,band,sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  have hcut : 8*4^L ≤ 8*4^(L+1) := by rw [pow_succ]; omega
  by_cases hne : p.1 = p.2
  · simp [hne]
  · by_cases hlo : codegree R p.1 p.2 < 8*4^L
    · have hhi := hlo.trans_le hcut
      simp [hne,hlo,hhi,Nat.not_le.mpr hlo]
    · by_cases hhi : codegree R p.1 p.2 < 8*4^(L+1)
      · simp [hne,hlo,hhi,Nat.le_of_not_gt hlo]
      · simp [hne,hlo,hhi]

lemma below_mass_le (R : A → B → Prop) (M : ℕ)
    (hM : ∀ j : ℕ, ∀ s : A → B → Fin (2^j), heavyCount (split R s) ≤ M)
    (L : ℕ) :
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
    haveI : Nonempty (Fin (2^L)) := ⟨⟨0,pow_pos (by decide) _⟩⟩
    have hp : (2^L)^2 = 4^L := by rw [← pow_mul,Nat.mul_comm L 2,pow_mul]; rfl
    have hb : (∑ p ∈ band R L, codegree R p.1 p.2) ≤ 64*M := by
      apply band_mass_le (T := Fin (2^L)) R (band R L) ?_ M (hM L)
      intro p hpP
      have hh := (mem_filter.mp hpP).2
      simp only [Fintype.card_fin,hp]
      refine ⟨hh.1,hh.2.1,?_⟩
      have he : 8*4^(L+1) = 32*4^L := by rw [pow_succ]; ring
      simpa only [he] using hh.2.2
    rw [below_step]
    nlinarith only [ih,hb]

lemma full_mass (R : A → B → Prop) (r : ℕ)
    (hr : ∀ a, Nat.card {b // R a b} = r) (L : ℕ) (hL : Nat.card A < 8*4^L) :
    (∑ p ∈ below R L, codegree R p.1 p.2) = Nat.card A*r*(r-1) := by
  have hc (x y : B) : codegree R x y < 8*4^L := by
    apply lt_of_le_of_lt _ hL
    simpa only [codegree,Nat.card_eq_fintype_card] using
      Fintype.card_subtype_le (fun a => R a x ∧ R a y)
  have he : below R L = (univ : Finset B).offDiag := by
    ext p
    simp [below,mem_offDiag,hc]
  rw [he]
  have hcd (p : B × B) : codegree R p.1 p.2 =
      (Erdos713ThetaAnchorPacking.commonRows R univ p).card := by
    simp only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype,
      Erdos713ThetaAnchorPacking.commonRows]
  simp_rw [hcd]
  rw [← Erdos713ThetaAnchorBudget.pair_incidence_sum]
  have hrow (a : A) : (Erdos713ThetaHeavyShadow.row R a).card = r := by
    simpa only [Erdos713ThetaHeavyShadow.row,Nat.card_eq_fintype_card,Fintype.card_subtype] using hr a
  simp only [offDiag_card,hrow,sum_const,card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id,Nat.mul_sub_left_distrib,mul_one,Nat.mul_assoc]

omit [Fintype A] [Fintype B] in
lemma exists_large_power (C D : ℕ) :
    ∃ t : ℕ, 64*C*(D+8892*t)+10 < 2^(2*t) := by
  let U := 64*C*(D+8892)
  let t := U+20
  have ht : 20 ≤ t := by dsimp [t]; omega
  have hDt : D ≤ D*t := Nat.le_mul_of_pos_right D (by omega)
  have hb : 64*C*(D+8892*t) ≤ U*t := by
    have hh := Nat.mul_le_mul_left (64*C) hDt
    dsimp only [U]
    nlinarith only [hh]
  have he : t*t = U*t+20*t := by dsimp only [t]; ring
  have hp := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  refine ⟨t,?_⟩
  nlinarith only [ht,hb,he,hp]

/-- Heavy ordered column pairs cannot be bounded by a fixed multiple of
incidences, even under oriented theta exclusion. -/
theorem exists_counterexample (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ C*edges R < heavyCount R := by
  classical
  let D := Erdos713ThetaPolynomialSize.scale^57
  obtain ⟨t,ht⟩ := exists_large_power C D
  let r := 2^(2*t)
  let L := D+8892*t
  have hr : 1 ≤ r := Nat.one_le_pow _ _ (by decide)
  have hgap : 64*C*L+10 < r := ht
  obtain ⟨A,B,iA,iB,R,hfree,hkm,hsize,hrows,hedges⟩ :=
    Erdos713ThetaPolynomialSize.exists_examples r hr
  have hm : Nat.card A < 8*4^L := by
    calc
      _ ≤ D*r^4446 := hsize
      _ ≤ 2^D*r^4446 := Nat.mul_le_mul_right _ (show D ≤ 2^D from Nat.lt_two_pow_self.le)
      _ = 2^L := by dsimp only [r,L]; rw [← pow_mul,← pow_add]; congr 1; ring
      _ ≤ 4^L := Nat.pow_le_pow_left (by decide) L
      _ < 8*4^L := by have hh := pow_pos (by decide : 0 < (4 : ℕ)) L; omega
  have hex : ∃ j : ℕ, ∃ s : A → B → Fin (2^j),
      C*edges R < heavyCount (split R s) := by
    by_contra! hn
    have hmass := below_mass_le R (C*edges R) hn L
    rw [full_mass R r hrows L hm] at hmass
    change Nat.card {p : A × B // R p.1 p.2} = _ at hedges
    change edges R = Nat.card A*r at hedges
    rw [hedges] at hmass
    have hA : 0 < Nat.card A := lt_of_le_of_lt (Nat.zero_le _) hkm
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
  obtain ⟨j,s,hs⟩ := hex
  refine ⟨A,B × Fin (2^j),inferInstance,inferInstance,split R s,no_theta hfree s,?_⟩
  simpa only [Erdos713ThetaRandomSplitting.edge_card] using hs

/-- In particular, the proposed heavy-pair-retaining C4-free sparsifiers
do not exist with a uniform constant for all theta-free relations. -/
theorem exists_no_sparsifier (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ ¬ Erdos713ThetaHeavySparsifier.HasSparsifier C R := by
  obtain ⟨A,B,iA,iB,R,hfree,hbig⟩ := exists_counterexample C
  refine ⟨A,B,iA,iB,R,hfree,?_⟩
  rintro ⟨Q,hQR,_hfour,hretain⟩
  have he : edges Q ≤ edges R := by
    have hh := edge_split hQR
    omega
  exact (not_le_of_gt hbig) (hretain.trans (Nat.mul_le_mul_left C he))

theorem no_universal_sparsifier :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → Erdos713ThetaHeavySparsifier.HasSparsifier C R := by
  rintro ⟨C,hC⟩
  obtain ⟨A,B,iA,iB,R,hfree,hno⟩ := exists_no_sparsifier C
  exact hno (hC A B R hfree)

#print axioms below_mass_le
#print axioms full_mass
#print axioms exists_large_power
#print axioms exists_counterexample
#print axioms exists_no_sparsifier
#print axioms no_universal_sparsifier
end Erdos713ThetaHeavyEdgeCounterexample
