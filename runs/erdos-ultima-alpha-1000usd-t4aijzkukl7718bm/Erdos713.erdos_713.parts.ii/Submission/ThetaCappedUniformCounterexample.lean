import FormalConjecturesUtil
import Submission.ThetaCappedUniformBand
import Submission.ThetaCappedHeavyCounterexample

/-! Capped theta-free counterexamples with every row of the same
arbitrarily large degree. The heavy count is unbounded per incidence. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCappedUniformCounterexample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
open Erdos713ThetaHeavyEdgeCounterexample Erdos713ThetaC4Deletion
set_option maxHeartbeats 2000000

/-- Singleton padding has been removed from these examples. -/
theorem exists_counterexample (C N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ N ≤ r ∧ 1 ≤ r ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ 2*Nat.card B) ∧
      (Nat.card B)^3 ≤ 8*(Nat.card A)^2 ∧ C*(Nat.card A*r) < heavyCount R := by
  classical
  by_contra! hBound
  let Z := Erdos713ThetaGramPowerSize.scale^75
  obtain ⟨t,ht⟩ := Erdos713ThetaCappedHeavyCounterexample.exists_large_power (64*C+256+N) Z
  let r := 2^(2*t)
  let L := Z+15300*t
  let b := 64*C+256
  have hr : 1 ≤ r := Nat.one_le_pow _ _ (by decide)
  have hZ : 0 < Z := by
    dsimp only [Z,Erdos713ThetaGramPowerSize.scale,Erdos713ThetaGramPowerSize.base]
    positivity
  have hL : 1 ≤ L := by dsimp only [L]; omega
  change (b+N)*L+40 < r at ht
  have hgap : b*L+40 < r := by nlinarith only [ht]
  have hrN : N ≤ r := by
    have hh : N ≤ N*L := Nat.le_mul_of_pos_right N hL
    nlinarith only [ht,hh]
  obtain ⟨A,B,iA,iB,R,Q,D,hfree,hm,hk,hDpos,hkm,hsize,hrows,hD,hDk,hQ,hshape⟩ :=
    Erdos713ThetaCappedGramPreparation.exists_examples r hr
  let E := Nat.card A*r
  have hmE : Nat.card A ≤ E := Nat.le_mul_of_pos_right _ hr
  change D*Nat.card B ≤ 4*E at hDk
  have hband (j : ℕ) : (∑ p ∈ band R j, codegree R p.1 p.2) ≤ b*E := by
    by_cases hcrit : 8*4^j ≤ Q
    · by_cases hcap : D ≤ Nat.card B*4^j
      · have hp : (2^j)^2 = 4^j := by rw [← pow_mul,Nat.mul_comm j 2,pow_mul]; rfl
        have hT : 0 < 2^j := pow_pos (by decide) j
        have hTQ : (2^j)^2 ≤ Q := by rw [hp]; omega
        obtain ⟨S,hSf,hSrows,hScap,hMass⟩ :=
          Erdos713ThetaCappedUniformBand.exists_retention R hfree hm hk D (2^j) hT hD
            (by simpa only [hp] using hcap) (hshape (2^j) hTQ) (band R j) (by
              intro p hpP
              have hh := (mem_filter.mp hpP).2
              have he : 8*4^(j+1) = 32*4^j := by rw [pow_succ]; ring
              simpa only [hp,he] using hh)
        have hRowsS (a : A) : Nat.card {z // S a z} = r := (hSrows a).trans (hrows a)
        have hCapS : ∀ z, Nat.card {a // S a z} ≤ 2*Nat.card (B × Fin (2^j)) := by
          simpa only [Nat.card_prod,Nat.card_fin] using hScap
        have hShapeS : (Nat.card (B × Fin (2^j)))^3 ≤ 8*(Nat.card A)^2 := by
          simpa only [Nat.card_prod,Nat.card_fin] using hshape (2^j) hTQ
        have hH := hBound A (B × Fin (2^j)) iA inferInstance S r
          hSf hm hrN hr hRowsS hCapS hShapeS
        change heavyCount S ≤ C*E at hH
        dsimp only [b]
        nlinarith only [hMass,hH,hmE]
      · have hCard : (band R j).card ≤ (Nat.card B)^2 := by
          simpa only [card_univ,Fintype.card_prod,Nat.card_eq_fintype_card,pow_two] using
            card_le_card (subset_univ (band R j))
        have hMass : (∑ p ∈ band R j, codegree R p.1 p.2) ≤ 32*4^j*(Nat.card B)^2 := by
          calc
            _ ≤ ∑ _p ∈ band R j, 32*4^j := sum_le_sum (fun p hp => by
              have hh := (mem_filter.mp hp).2.2.2
              have he : 8*4^(j+1) = 32*4^j := by rw [pow_succ]; ring
              simpa only [he] using hh.le)
            _ = 32*4^j*(band R j).card := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id]; ring
            _ ≤ _ := Nat.mul_le_mul_left _ hCard
        have hLow : Nat.card B*4^j ≤ D := Nat.le_of_lt (Nat.lt_of_not_ge hcap)
        have hh := Nat.mul_le_mul_right (32*Nat.card B) hLow
        have hdk := Nat.mul_le_mul_left 32 hDk
        dsimp only [b]
        nlinarith only [hMass,hh,hdk]
    · have he : band R j = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := (mem_filter.mp hp).2
        exact hcrit (hh.2.1.trans (hQ p.1 p.2 hh.1))
      simp only [he,sum_empty,Nat.zero_le]
  have hLarge : Nat.card A < 8*4^L := by
    calc
      _ ≤ Z*r^7650 := hsize
      _ ≤ 2^Z*r^7650 := Nat.mul_le_mul_right _ (show Z ≤ 2^Z from Nat.lt_two_pow_self.le)
      _ = 2^L := by dsimp only [r,L]; rw [← pow_mul,← pow_add]; congr 1; ring
      _ ≤ 4^L := Nat.pow_le_pow_left (by decide) L
      _ < 8*4^L := by have hh := pow_pos (by decide : 0 < (4 : ℕ)) L; omega
  have hMass := Erdos713ThetaCappedHeavyCounterexample.below_mass_of_bands R (b*E) hband L
  rw [full_mass R r hrows L hLarge] at hMass
  have hfin : r*(r-1) ≤ 32+L*b*r := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card A) _ hm
    calc
      _ = Nat.card A*r*(r-1) := by ring
      _ ≤ 8*(Nat.card B)^2+L*(b*E) := hMass
      _ ≤ Nat.card A*(32+L*b*r) := by
        dsimp only [E]
        nlinarith only [hkm]
  have hsub : r-1+1 = r := Nat.sub_add_cancel hr
  have hprod := Nat.mul_le_mul_left r (show b*L+40 ≤ r from hgap.le)
  nlinarith only [hfin,hsub,hprod,hr]

lemma edges_of_rows {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (r : ℕ) (hrows : ∀ a, Nat.card {b // R a b} = r) :
    edges R = Nat.card A*r := by
  rw [edges,Erdos713ThetaSplit.edge_card_eq_rows]
  simp only [hrows,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.card_eq_fintype_card]

/-- The cap can be exactly the column count; this step uses isolated
column padding, but adds no rows and preserves every row degree. -/
theorem exists_unit_cap (C N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ N ≤ r ∧ 1 ≤ r ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      (Nat.card B)^3 ≤ 64*(Nat.card A)^2 ∧ C*edges R < heavyCount R := by
  classical
  obtain ⟨A,B,iA,iB,R,r,hf,hm,hrN,hr,hrows,hcap,hshape,hbig⟩ := exists_counterexample C N
  have hk := Erdos713ThetaCappedGramPreparation.columns_pos_of_row_degree R hm r hr hrows
  letI : Nonempty B := (Nat.card_pos_iff.mp hk).1
  let S := Erdos713ThetaColumnPadding.pad (Sum.inl : B → B ⊕ B) R
  have hK : Nat.card (B ⊕ B) = 2*Nat.card B := by rw [Nat.card_sum]; omega
  have hrowsS (a : A) : Nat.card {b // S a b} = r :=
    (Erdos713ThetaColumnPadding.pad_row_card Sum.inl_injective R a).trans (hrows a)
  refine ⟨A,B ⊕ B,inferInstance,inferInstance,S,r,
    Erdos713ThetaColumnPadding.pad_no_theta Sum.inl_injective hf,hm,hrN,hr,hrowsS,?_,?_,?_⟩
  · intro b
    rw [hK]
    exact Erdos713ThetaColumnPadding.pad_column_le Sum.inl_injective R (2*Nat.card B) hcap b
  · rw [hK]
    calc
      _ = 8*(Nat.card B)^3 := by ring
      _ ≤ 8*(8*(Nat.card A)^2) := Nat.mul_le_mul_left 8 hshape
      _ = _ := by ring
  · rw [edges_of_rows S r hrowsS]
    exact hbig.trans_le (Erdos713ThetaCappedHeavyCounterexample.heavy_le_pad R Sum.inl_injective)

/-- Uniform heavy-pair retention by a bounded-incidence sparsifier fails
even under the unit column cap. -/
theorem no_capped_incidence_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (heavyCount R : ℝ) ≤ C*(edges R : ℝ) := by
  rintro ⟨C,_hC,hBound⟩
  obtain ⟨M,hM⟩ := exists_nat_gt C
  obtain ⟨A,B,iA,iB,R,r,hf,hm,_hrN,hr,hrows,hcap,_hshape,hbig⟩ := exists_unit_cap M 1
  have hE : 0 < edges R := by rw [edges_of_rows R r hrows]; exact Nat.mul_pos hm hr
  have hER : (0 : ℝ) < edges R := Nat.cast_pos.mpr hE
  have hlo : (M : ℝ)*(edges R : ℝ) < heavyCount R := by exact_mod_cast hbig
  have hu := hBound A B R hf hcap
  have hh := mul_lt_mul_of_pos_right hM hER
  linarith only [hlo,hu,hh]

theorem exists_no_capped_sparsifier (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      ¬ Erdos713ThetaHeavySparsifier.HasSparsifier C R := by
  obtain ⟨A,B,iA,iB,R,_r,hf,_hm,_hrN,_hr,_hrows,hcap,_hshape,hbig⟩ := exists_unit_cap C 1
  refine ⟨A,B,iA,iB,R,hf,hcap,?_⟩
  rintro ⟨Q,hQR,_hFour,hretain⟩
  have he : edges Q ≤ edges R := by have hh := edge_split hQR; omega
  exact (not_le_of_gt hbig) (hretain.trans (Nat.mul_le_mul_left C he))

#print axioms exists_counterexample
#print axioms exists_unit_cap
#print axioms no_capped_incidence_bound
#print axioms exists_no_capped_sparsifier
end Erdos713ThetaCappedUniformCounterexample
