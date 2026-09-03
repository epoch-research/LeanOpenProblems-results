import Submission.ExceptionalLayers
import Submission.ExceptionalHybrid

/-!
# The no-3 box sieve with one exceptional coordinate class

The certified hinge prefix saves more than the final tower mass of the
exceptional cylinder. No minimum-cardinality assumption is used.
-/
namespace Erdos7ExceptionalBox
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7ExceptionalLayers Erdos7ExceptionalHybrid
set_option maxHeartbeats 6000000

/-- The distortion union bound with an additional event retained separately. -/
theorem coordinate_cover_with_exception {n : ℕ}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ) (hc : ∀ i, 1 ≤ c i)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v ∈ B j ↔ x ∈ B j)
    (C : Finset (∀ i, A i)) (hcover : ∀ x : ∀ i, A i, (∃ i, x ∈ B i) ∨ x ∈ C) :
    1 ≤ (∑ x ∈ C, towerWeights A B c n x) +
      ∑ i : Fin n, ∑ x : ∀ j, A j,
        towerWeights A B c i.val x * Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x) := by
  classical
  let μ := towerWeights A B c n
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A B c hc n
  have hpoint (x : ∀ i, A i) : μ x ≤ (if x∈C then μ x else 0)+
      ∑ i : Fin n, if x∈B i then μ x else 0 := by
    have hsum : 0 ≤ ∑ i : Fin n, if x∈B i then μ x else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> [exact hμ x; exact le_rfl])
    rcases hcover x with ⟨i,hi⟩ | hi
    · have hh := Finset.single_le_sum (f := fun j : Fin n => if x∈B j then μ x else 0)
        (fun j _ => by dsimp only; split_ifs <;> [exact hμ x; exact le_rfl]) (Finset.mem_univ i)
      have hc0 : 0 ≤ if x∈C then μ x else 0 := by split_ifs <;> [exact hμ x; exact le_rfl]
      simpa only [if_pos hi] using hh.trans (le_add_of_nonneg_left hc0)
    · simpa only [if_pos hi] using le_add_of_nonneg_right hsum
  have hunion : 1 ≤ (∑ x ∈ C, μ x)+∑ i : Fin n, ∑ x ∈ B i, μ x := by
    have hh := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ : Finset (∀ i, A i))) => hpoint x)
    rw [show (∑ x, μ x)=1 from towerWeights_total A B c hc n] at hh
    rw [Finset.sum_add_distrib,Finset.sum_comm] at hh
    simpa only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] using hh
  apply hunion.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hret := towerWeights_retains_event A B c hc hB i n (by have := i.isLt; omega) le_rfl
  dsimp only [μ]
  rw [hret,towerWeights_succ A B c i]
  exact resample_excluded A i _ (B i) (hc i)

/-- Distinct exponent boxes on primes at least5 cannot be repaired by one
coordinate cylinder of density at most the reciprocal of its prime. -/
theorem not_cover_with_exception {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 14 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 14, p (Fin.castLE hn i)=Erdos7ExceptionalScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    (i₀ : Fin n) (Y : Finset (A i₀)) (hY : fraction Y ≤ 1/(p i₀ : ℚ)) :
    ¬ (∀ x : ∀ i, A i, (∃ k, ∀ i, x i∈X k i) ∨ x i₀∈Y) := by
  classical
  intro hcover
  let S (k : κ) := expSupport (e k)
  have hne (k : κ) : (S k).Nonempty := by
    obtain ⟨i,hi⟩ := he0 k
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j≤σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  let c : Fin n → ℚ := fun _ => 5/4
  have hc (i : Fin n) : 1 ≤ c i := by norm_num [c]
  let L (i : Fin n) := ∑ x, towerWeights A B c i.val x *
    Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x)
  have hp1 (i : Fin n) : 1 < p i := by have := (hp i).2; omega
  have hpQ (i : Fin n) : (5 : ℚ) ≤ p i := by exact_mod_cast (hp i).2
  have hfrac (k : κ) (i : Fin n) : fraction (X k i) ≤ ((p i : ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k i
  have hraw (i : Fin n) : L i ≤ raw p i := by
    have hh := layer_raw_loss_bound A p hp1 e hei he0 X hX0 hX c
      (fun i => by norm_num [c]) σ hσ hS i
    convert hh using 1
    unfold raw Erdos7No23Sieve.charge Erdos7No23Sieve.multiplier
    dsimp only [c]
    norm_num
    ring
  have hearly (i : Fin n) (hi : i.val<14) : L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
        (fun x => Erdos7Distortion.residual (5/4) (1/(p i-1 : ℚ)*x)) i.val 1 := by
    apply layer_exponent_loss_bound A E c (fun i => 1/(p i-1 : ℚ))
      (fun i g => ((p i : ℚ)⁻¹)^g) (fun i => powerTail (p i) (c i) (E i)) hc
    · intro i; apply one_div_pos.mpr; linarith [hpQ i]
    · intros; positivity
    · intro i; exact positive_power_sum_le (p i) (hp1 i) (E i)
    · intro i; apply powerTail_zero_le_one (p i) (hp1 i) (c i); dsimp [c]; linarith [hpQ i]
    · intro i g hg; exact powerTail_decreasing (p i) (hp1 i) (c i) (by norm_num [c]) (E i) g
    · intro i; exact powerTail_terminal _ _ _
    · intro i g hg; simp only [powerTail,if_pos hg,le_refl]
    · exact hei
    · exact heE
    · exact hne
    · exact fun k i _ => hfrac k i
    · exact hσ
    · exact hS
  have hsmall := hybrid_lt_three_quarters hn p E hp hmono hpre L hraw hearly
  let C := Finset.univ.filter (fun x : ∀ i, A i => x i₀∈Y)
  have hcov : ∀ x : ∀ i, A i, (∃ i, x∈B i) ∨ x∈C := by
    intro x
    rcases hcover x with ⟨k,hk⟩ | hk
    · exact Or.inl ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun j _ => hk j⟩⟩
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩)
  have hb := coordinate_cover_with_exception A B c hc
    (layeredBad_invariant A S X σ hS) C hcov
  have hC : (∑ x∈C, towerWeights A B c n x) ≤ 1/4 := by
    let Y' : ∀ i, Finset (A i) := Function.update (fun _ => Finset.univ) i₀ Y
    have hh := towerWeights_box_bound A B c hc n le_rfl {i₀}
      (fun j hj => by have he : j=i₀ := Finset.mem_singleton.mp hj; subst j; exact i₀.isLt) Y'
    have he : boxMass A (towerWeights A B c n) {i₀} Y' =
        ∑ x∈C, towerWeights A B c n x := by
      simp [boxMass,boxIndicator,Y',C,Finset.sum_filter]
    rw [he] at hh
    simp only [Finset.prod_singleton,Y',Function.update_self] at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℚ)≤5/4)
    have hp0 : (0 : ℚ)<p i₀ := by linarith [hpQ i₀]
    have hdiv : (5/4 : ℚ)*(1/(p i₀ : ℚ)) ≤ 1/4 := by
      rw [mul_one_div]
      apply (div_le_iff₀ hp0).mpr
      linarith [hpQ i₀]
    simpa only [c] using hmul.trans hdiv
  change 1 ≤ (∑ x∈C, towerWeights A B c n x)+(∑ i,L i) at hb
  linarith

#print axioms coordinate_cover_with_exception
#print axioms not_cover_with_exception
end Erdos7ExceptionalBox
