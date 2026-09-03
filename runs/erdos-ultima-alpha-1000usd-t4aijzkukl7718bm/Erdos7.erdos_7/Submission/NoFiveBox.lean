import Submission.ExceptionalLayers
import Submission.NoFiveHybrid

/-! The no-five box obstruction from the mixed-cap certificate. -/
namespace Erdos7NoFiveBox
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve Erdos7NoFiveScalar Erdos7NoFiveRaw
open Erdos7ExceptionalLayers Erdos7NoFiveHybrid
set_option maxHeartbeats 6000000

variable (hcert :
    (∀ i : Fin 366, 3 ≤ primes i ∧ primes i ≤ 2503 ∧
      Row (primes i) (states i.castSucc) (states i.succ)) ∧
    (∀ x : Fin 501, (states 366).values x=0) ∧
    (states 366).slope=0 ∧ (states 366).intercept=0)

include hcert in
theorem not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 366 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 3 ≤ p i ∧ p i ≠ 5) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=Erdos7NoFiveScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    : ¬ (∀ x : ∀ i, A i, ∃ k, ∀ i, x i∈X k i) := by
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
  let c : Fin n → ℚ := fun i => cap (p i)
  have hc (i : Fin n) : 1 ≤ c i := by
    dsimp [c]
    have := (cap_bounds (p i)).1
    linarith
  let L (i : Fin n) := ∑ x, towerWeights A B c i.val x *
    Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x)
  have hp1 (i : Fin n) : 1 < p i := by have := (hp i).2.1; omega
  have hpQ (i : Fin n) : (3 : ℚ) ≤ p i := by exact_mod_cast (hp i).2.1
  have hfrac (k : κ) (i : Fin n) : fraction (X k i) ≤ ((p i : ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k i
  have hraw (i : Fin n) : L i ≤ raw p i := by
    have hh := layer_raw_loss_bound A p hp1 e hei he0 X hX0 hX c
      (fun i => by dsimp [c]; have := (cap_bounds (p i)).1; linarith) σ hσ hS i
    convert hh using 1
    unfold raw chargeC multiplierC
    dsimp only [c]
    norm_num
    ring
  have hearly (i : Fin n) (hi : i.val<366) : L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
        (fun x => Erdos7Distortion.residual (cap (p i)) (1/(p i-1 : ℚ)*x)) i.val 1 := by
    apply layer_exponent_loss_bound A E c (fun i => 1/(p i-1 : ℚ))
      (fun i g => ((p i : ℚ)⁻¹)^g) (fun i => powerTail (p i) (c i) (E i)) hc
    · intro i; apply one_div_pos.mpr; linarith [hpQ i]
    · intros; positivity
    · intro i; exact positive_power_sum_le (p i) (hp1 i) (E i)
    · intro i; apply powerTail_zero_le_one (p i) (hp1 i) (c i); exact cap_le_prime (p i) (hp i).2.1
    · intro i g hg; exact powerTail_decreasing (p i) (hp1 i) (c i) (by dsimp [c]; have := (cap_bounds (p i)).1; linarith) (E i) g
    · intro i; exact powerTail_terminal _ _ _
    · intro i g hg; simp only [powerTail,if_pos hg,le_refl]
    · exact hei
    · exact heE
    · exact hne
    · exact fun k i _ => hfrac k i
    · exact hσ
    · exact hS
  have hsmall := hybrid_lt_one hcert hn p E hp hmono hpre L hraw hearly
  have hcov : ∀ x : ∀ i, A i, ∃ i, x∈B i := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    exact ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun j _ => hk j⟩⟩
  have hb := coordinate_residual_cover_bound A B c hc
    (layeredBad_invariant A S X σ hS) hcov
  change 1 ≤ ∑ i,L i at hb
  linarith

#print axioms not_cover
end Erdos7NoFiveBox
