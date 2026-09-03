import FormalConjecturesUtil
import Submission.ThetaCappedBandRetention
import Submission.ThetaHeavyThreeHalvesCounterexample

/-! The heavy-shadow three-halves bound fails even with a fixed linear
column-degree cap. This does not settle the all-light-pair density gap. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCappedHeavyCounterexample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
open Erdos713ThetaHeavyEdgeCounterexample
variable {A B : Type} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

omit [Fintype A] in
lemma below_mass_of_bands (R : A → B → Prop) (M : ℕ)
    (hM : ∀ j, (∑ p ∈ band R j, codegree R p.1 p.2) ≤ M) (L : ℕ) :
    (∑ p ∈ below R L, codegree R p.1 p.2) ≤ 8*(Nat.card B)^2+L*M := by
  induction L with
  | zero =>
    simp only [Nat.zero_mul,add_zero]
    calc
      _ ≤ ∑ _p ∈ below R 0, 8 := sum_le_sum (fun p hp => by
        have hh := (mem_filter.mp hp).2.2
        simpa only [pow_zero,mul_one] using hh.le)
      _ ≤ 8*Fintype.card (B × B) := by
        simpa only [sum_const,nsmul_eq_mul,card_univ,Nat.mul_comm] using
          Nat.mul_le_mul_left 8 (card_le_card (subset_univ (below R 0)))
      _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_prod,pow_two]
  | succ L ih =>
    rw [below_step]
    have hb := hM L
    nlinarith only [ih,hb]

omit [Fintype A] [Fintype B] in
lemma exists_large_power (C D : ℕ) :
    ∃ t : ℕ, C*(D+15300*t)+40 < 2^(2*t) := by
  let U := C*(D+15300)
  let t := U+40
  have ht : 40 ≤ t := by dsimp [t]; omega
  have hDt : D ≤ D*t := Nat.le_mul_of_pos_right D (by omega)
  have hb : C*(D+15300*t) ≤ U*t := by
    have hh := Nat.mul_le_mul_left C hDt
    dsimp only [U]
    nlinarith only [hh]
  have he : t*t = U*t+40*t := by dsimp only [t]; ring
  have hp := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  exact ⟨t,by nlinarith only [ht,hb,he,hp]⟩

/-- Both the row count and the three-halves column term are negligible
compared with the heavy count in examples of column degree at most twice
the column count. -/
theorem exists_counterexample (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧
      (∀ b, Nat.card {a // R a b} ≤ 2*Nat.card B) ∧
      (Nat.card B)^3 ≤ 8*(Nat.card A)^2 ∧ C*Nat.card A < heavyCount R := by
  classical
  by_contra! hBound
  let Z := Erdos713ThetaGramPowerSize.scale^75
  obtain ⟨t,ht⟩ := exists_large_power (448*C+128) Z
  let r := 2^(2*t)
  let L := Z+15300*t
  let b := 448*C+128
  have hr : 1 ≤ r := Nat.one_le_pow _ _ (by decide)
  have hgap : b*L+40 < r := ht
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
        obtain ⟨A',B',iA',iB',S,hSf,hSm,hSupper,_hK,hScap,hSshape,hMass⟩ :=
          Erdos713ThetaCappedBandRetention.exists_retention R hfree hm hk D (2^j) hT hD
            (by simpa only [hp] using hcap) (hshape (2^j) hTQ) (band R j) (by
              intro p hpP
              have hh := (mem_filter.mp hpP).2
              have he : 8*4^(j+1) = 32*4^j := by rw [pow_succ]; ring
              simpa only [hp,he] using hh)
        have hH := hBound A' B' iA' iB' S hSf hSm hScap hSshape
        have hM : Nat.card A' ≤ 7*E := by nlinarith only [hSupper,hmE,hDk]
        have hH' := hH.trans (Nat.mul_le_mul_left C hM)
        have hh := hMass.trans (Nat.mul_le_mul_left 64 hH')
        dsimp only [b]
        nlinarith only [hh]
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
  have hMass := below_mass_of_bands R (b*E) hband L
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

lemma heavy_le_pad {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    (R : A → B → Prop) {f : B → K} (hf : Function.Injective f) :
    heavyCount R ≤ heavyCount (Erdos713ThetaColumnPadding.pad f R) := by
  classical
  let g : {p : B × B // 3 ≤ codegree R p.1 p.2} →
      {p : K × K // 3 ≤ codegree (Erdos713ThetaColumnPadding.pad f R) p.1 p.2} :=
    fun p => ⟨(f p.val.1,f p.val.2),by
      simpa only [codegree,Erdos713ThetaColumnPadding.pad_image hf] using p.property⟩
  apply Nat.card_le_card_of_injective g
  intro p q he
  apply Subtype.ext
  exact Prod.ext (hf (congrArg (fun z => z.val.1) he))
    (hf (congrArg (fun z => z.val.2) he))

/-- Adding isolated columns changes the cap from 2k to k. This does not
claim a small light-pair set. -/
theorem exists_unit_cap (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      (Nat.card B)^3 ≤ 64*(Nat.card A)^2 ∧ C*Nat.card A < heavyCount R := by
  classical
  obtain ⟨A,B,iA,iB,R,hf,hm,hcap,hshape,hbig⟩ := exists_counterexample C
  have hp : 0 < heavyCount R := lt_of_le_of_lt (Nat.zero_le _) hbig
  haveI : Nonempty {p : B × B // 3 ≤ codegree R p.1 p.2} := (Nat.card_pos_iff.mp hp).1
  let p : {p : B × B // 3 ≤ codegree R p.1 p.2} := Classical.choice inferInstance
  letI : Nonempty B := ⟨p.val.1⟩
  let S := Erdos713ThetaColumnPadding.pad (Sum.inl : B → B ⊕ B) R
  have hK : Nat.card (B ⊕ B) = 2*Nat.card B := by rw [Nat.card_sum]; omega
  refine ⟨A,B ⊕ B,inferInstance,inferInstance,S,
    Erdos713ThetaColumnPadding.pad_no_theta Sum.inl_injective hf,hm,?_,?_,?_⟩
  · intro b
    rw [hK]
    exact Erdos713ThetaColumnPadding.pad_column_le Sum.inl_injective R (2*Nat.card B) hcap b
  · rw [hK]
    calc
      _ = 8*(Nat.card B)^3 := by ring
      _ ≤ 8*(8*(Nat.card A)^2) := Nat.mul_le_mul_left 8 hshape
      _ = _ := by ring
  · exact hbig.trans_le (heavy_le_pad R Sum.inl_injective)

/-- The three-halves candidate is false even with maximum column degree
at most the column count. -/
theorem no_column_capped_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (heavyCount R : ℝ) ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card B)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (9*C)
  obtain ⟨A,B,iA,iB,R,hf,hm,hcap,hshape,hbig⟩ := exists_unit_cap N
  have hshape' : (Nat.card B)^3 ≤ (8*Nat.card A)^2 := by nlinarith only [hshape]
  have hs := Erdos713ThetaHeavyThreeHalvesCounterexample.sqrt_term_le_of_cube_le _ _ hshape'
  have hs' : (Nat.card B : ℝ)*Real.sqrt (Nat.card B) ≤ 8*(Nat.card A : ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs
  have hu := hBound A B R hf hcap
  have hlo : (N : ℝ)*(Nat.card A : ℝ) < heavyCount R := by exact_mod_cast hbig
  have hmR : (0 : ℝ) < Nat.card A := Nat.cast_pos.mpr hm
  have hscaled := mul_le_mul_of_nonneg_left hs' hC.le
  have hNscaled := mul_lt_mul_of_pos_right hN hmR
  nlinarith only [hu,hlo,hscaled,hNscaled]

#print axioms exists_counterexample
#print axioms exists_unit_cap
#print axioms no_column_capped_bound
end Erdos713ThetaCappedHeavyCounterexample
