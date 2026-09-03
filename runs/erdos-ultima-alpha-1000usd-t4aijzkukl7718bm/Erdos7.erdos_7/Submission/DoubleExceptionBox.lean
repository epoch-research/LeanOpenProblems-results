import Submission.ExceptionalLayers
import Submission.DoubleExceptionHybrid
import Submission.ExceptionalBox

/-!
# The no-3 box sieve with two exceptional coordinate classes

The certified hinge prefix saves more than the final tower mass of the
exceptional cylinders. No minimum-cardinality assumption is used.
-/
namespace Erdos7DoubleExceptionBox
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7ExceptionalLayers Erdos7DoubleExceptionHybrid
set_option maxHeartbeats 6000000

/-- Distinct exponent boxes on primes at least5 cannot be repaired by two
coordinate cylinders of density at most the reciprocal of their primes. -/
theorem not_cover_with_two_exceptions {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 94 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=Erdos7DoubleExceptionScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    (i₀ : Fin 2 → Fin n) (Y : ∀ j, Finset (A (i₀ j)))
    (hY : ∀ j, fraction (Y j) ≤ 1/(p (i₀ j) : ℚ)) :
    ¬ (∀ x : ∀ i, A i, (∃ k, ∀ i, x i∈X k i) ∨ (∃ j, x (i₀ j)∈Y j)) := by
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
  have hearly (i : Fin n) (hi : i.val<94) : L i ≤
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
  have hsmall := hybrid_lt_one_half hn p E hp hmono hpre L hraw hearly
  let C := Finset.univ.filter (fun x : ∀ i, A i => ∃ j, x (i₀ j)∈Y j)
  have hcov : ∀ x : ∀ i, A i, (∃ i, x∈B i) ∨ x∈C := by
    intro x
    rcases hcover x with ⟨k,hk⟩ | hk
    · exact Or.inl ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun j _ => hk j⟩⟩
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩)
  have hb := Erdos7ExceptionalBox.coordinate_cover_with_exception A B c hc
    (layeredBad_invariant A S X σ hS) C hcov
  let μ := towerWeights A B c n
  let Cj (j : Fin 2) := Finset.univ.filter (fun x : ∀ i, A i => x (i₀ j)∈Y j)
  have hCj (j : Fin 2) : (∑ x∈Cj j, μ x) ≤ 1/4 := by
    let Y' : ∀ i, Finset (A i) := Function.update (fun _ => Finset.univ) (i₀ j) (Y j)
    have hh := towerWeights_box_bound A B c hc n le_rfl {i₀ j}
      (fun k hk => by have he : k=i₀ j := Finset.mem_singleton.mp hk; subst k; exact (i₀ j).isLt) Y'
    have he : boxMass A (towerWeights A B c n) {i₀ j} Y' =
        ∑ x∈Cj j, μ x := by
      simp [boxMass,boxIndicator,Y',Cj,μ,Finset.sum_filter]
    rw [he] at hh
    simp only [Finset.prod_singleton,Y',Function.update_self] at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_left (hY j) (by norm_num : (0 : ℚ)≤5/4)
    have hp0 : (0 : ℚ)<p (i₀ j) := by linarith [hpQ (i₀ j)]
    have hdiv : (5/4 : ℚ)*(1/(p (i₀ j) : ℚ)) ≤ 1/4 := by
      rw [mul_one_div]
      apply (div_le_iff₀ hp0).mpr
      linarith [hpQ (i₀ j)]
    simpa only [c] using hmul.trans hdiv
  have hC : (∑ x∈C, μ x) ≤ 1/2 := by
    have hpoint (x : ∀ i, A i) :
        (if x∈C then μ x else 0) ≤ ∑ j : Fin 2, if x∈Cj j then μ x else 0 := by
      have hm : 0 ≤ μ x := towerWeights_nonneg A B c hc n x
      rw [Fin.sum_univ_two]
      simp only [C,Cj,Finset.mem_filter,Finset.mem_univ,true_and,Fin.exists_fin_two]
      split_ifs <;> simp_all <;> linarith
    have hh := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ : Finset (∀ i, A i))) => hpoint x)
    rw [Finset.sum_comm] at hh
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] at hh
    apply hh.trans
    rw [Fin.sum_univ_two]
    linarith [hCj 0,hCj 1]
  change 1 ≤ (∑ x∈C, towerWeights A B c n x)+(∑ i,L i) at hb
  linarith

#print axioms not_cover_with_two_exceptions
end Erdos7DoubleExceptionBox
