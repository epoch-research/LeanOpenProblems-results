import Submission.LargeChildPropagation
import Submission.UniformRankin

/-!
# Explicit weighted masses of large-child ancestor layers

The constants in the fixed-depth summability argument are now retained. For
an initial exponent 1-1/R, the Lth layer has mass at most
M * (1+2R)^L * (2k)^(L^2). No assertion resolving Erdos 821 is made here.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

noncomputable def setPowerMass (A : Set ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, A.indicator (fun n : ℕ => (n : ℝ)^(-s)) n

lemma setPowerMass_nonneg (A : Set ℕ) (s : ℝ) : 0 ≤ setPowerMass A s :=
  tsum_nonneg (fun n => Set.indicator_nonneg
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)

lemma sum_largeChildParents_le (k : ℕ) (A : Set ℕ) (b s u : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u)
    (hexp : (k : ℝ)*(u-s)-u ≤ -b)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) (F : Finset ℕ) :
    (∑ p ∈ F, (largeChildParents k A).indicator (fun p : ℕ => (p : ℝ)^(-s)) p) ≤
      (∑' n : ℕ, (n : ℝ)^(-u)) * setPowerMass A b := by
  let P := F.filter (fun p => p ∈ largeChildParents k A)
  let D := P.image (fun p => p-1)
  have hp (p : ℕ) (hpP : p ∈ P) : p ∈ largeChildParents k A := (mem_filter.mp hpP).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hpP q hqP heq
    change p-1 = q-1 at heq
    have hp2 := (hp p hpP).1.two_le
    have hq2 := (hp q hqP).1.two_le
    omega
  have hD (d : ℕ) (hd : d ∈ D) : d ∈ largeDivisorLift k A := by
    obtain ⟨p, hpP, rfl⟩ := mem_image.mp hd
    obtain ⟨hpprime, q, hqA, hq, hqd, hqsize⟩ := hp p hpP
    exact ⟨by have := hpprime.two_le; omega, q, hqA, hq.pos, hqd, hqsize⟩
  calc
    _ = ∑ p ∈ P, (p : ℝ)^(-s) := by simp only [P, sum_filter, Set.indicator_apply]
    _ ≤ ∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s) := by
      apply sum_le_sum
      intro p hpP
      exact Real.rpow_le_rpow_of_nonpos
        (by exact_mod_cast (show 0 < p-1 by have := (hp p hpP).1.two_le; omega))
        (by exact_mod_cast Nat.sub_le p 1) (by linarith)
    _ = ∑ d ∈ D, (d : ℝ)^(-s) := (sum_image (f := fun d : ℕ => (d : ℝ)^(-s)) hinj).symm
    _ = ∑ d ∈ D, (largeDivisorLift k A).indicator (fun d : ℕ => (d : ℝ)^(-s)) d := by
      apply sum_congr rfl
      intro d hd
      rw [Set.indicator_of_mem (hD d hd)]
    _ ≤ _ := sum_largeDivisorLift_le k A b s u hsu hu hexp H D

lemma setPowerMass_largeChildParents_le (k : ℕ) (A : Set ℕ) (b s u : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u)
    (hexp : (k : ℝ)*(u-s)-u ≤ -b)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) :
    setPowerMass (largeChildParents k A) s ≤
      (∑' n : ℕ, (n : ℝ)^(-u)) * setPowerMass A b := by
  exact (summable_largeChildParents k A b s u hs hsu hu hexp H).tsum_le_of_sum_le
    (sum_largeChildParents_le k A b s u hs hsu hu hexp H)

lemma setPowerMass_exponent_mono (A : Set ℕ) (hA : 0 ∉ A) (b s : ℝ)
    (hbs : b ≤ s) (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) :
    setPowerMass A s ≤ setPowerMass A b := by
  apply Summable.tsum_le_tsum _ (summable_set_power_mono A b s hbs H) H
  intro n
  by_cases hn : n ∈ A
  · have hn0 : n ≠ 0 := by rintro rfl; exact hA hn
    rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
      (by linarith)
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

lemma setPowerMass_union_le (A B : Set ℕ) (s : ℝ)
    (HA : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-s))))
    (HB : Summable (B.indicator (fun n : ℕ => (n : ℝ)^(-s)))) :
    setPowerMass (A ∪ B) s ≤ setPowerMass A s + setPowerMass B s := by
  have hsum := HA.tsum_add HB
  unfold setPowerMass
  rw [← hsum]
  apply Summable.tsum_le_tsum _ (summable_set_power_union A B s HA HB) (HA.add HB)
  intro n
  change (A ∪ B).indicator (fun n : ℕ => (n : ℝ)^(-s)) n ≤
    A.indicator (fun n : ℕ => (n : ℝ)^(-s)) n +
      B.indicator (fun n : ℕ => (n : ℝ)^(-s)) n
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;>
    simp [hA, hB, Real.rpow_nonneg]

lemma zero_not_mem_largeChildLayer (k : ℕ) (A : Set ℕ) (hA : 0 ∉ A) (L : ℕ) :
    0 ∉ largeChildLayer k A L := by
  induction L with
  | zero => exact hA
  | succ L ih =>
    rintro (h | h)
    · exact ih h
    · exact Nat.not_prime_zero h.1

lemma largeChildLayerExponent_reciprocal (k R L : ℕ) (hk : 1 ≤ k) (_hR : 1 ≤ R) :
    largeChildLayerExponent k (1-1/(R : ℝ)) L =
      1-1/((R*(2*k)^L : ℕ) : ℝ) := by
  rw [largeChildLayerExponent_eq k hk]
  push_cast
  ring

/-- A one-step mass bound with an integer reciprocal gap. -/
lemma setPowerMass_largeChildParents_reciprocal_le (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    setPowerMass (largeChildParents k A) (1-1/((R*(2*k) : ℕ) : ℝ)) ≤
      (2*(R*(2*k) : ℕ) : ℝ) * setPowerMass A (1-1/(R : ℝ)) := by
  let T : ℕ := R*(2*k)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : 0 < 1/(T : ℝ) := one_div_pos.mpr (by linarith)
  have he1 : 1/(T : ℝ) ≤ 1 := (div_le_iff₀ (by linarith : (0 : ℝ) < T)).mpr (by linarith)
  have hR0 : (R : ℝ) ≠ 0 := by linarith
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hid : (2*(k : ℝ))*(1/(T : ℝ)) = 1/(R : ℝ) := by
    dsimp [T]
    push_cast
    field_simp
  have hmain := setPowerMass_largeChildParents_le k A (1-1/(R : ℝ))
    (1-1/(T : ℝ)) (1+1/(T : ℝ)) (by linarith) (by linarith) (by linarith)
    (by nlinarith only [hid, he]) H
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (pseries_one_add_inv_le T (by omega)) (setPowerMass_nonneg A _))

lemma reciprocal_exponent_bounds (R : ℕ) (hR : 1 ≤ R) :
    0 ≤ 1-1/(R : ℝ) ∧ 1-1/(R : ℝ) < 1 := by
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hp : 0 < 1/(R : ℝ) := one_div_pos.mpr (by linarith)
  have hle : 1/(R : ℝ) ≤ 1 := (div_le_iff₀ (by linarith : (0 : ℝ) < R)).mpr (by linarith)
  constructor <;> linarith

lemma nextLargeChildExponent_reciprocal (k R : ℕ) :
    nextLargeChildExponent k (1-1/(R : ℝ)) = 1-1/((R*(2*k) : ℕ) : ℝ) := by
  unfold nextLargeChildExponent
  push_cast
  ring

lemma summable_largeChildParents_reciprocal (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    Summable ((largeChildParents k A).indicator
      (fun n : ℕ => (n : ℝ)^(-(1-1/((R*(2*k) : ℕ) : ℝ))))) := by
  have hb := reciprocal_exponent_bounds R hR
  simpa only [nextLargeChildExponent_reciprocal] using
    summable_largeChildParents_next k hk A (1-1/(R : ℝ)) hb.1 hb.2 H

lemma summable_largeChildLayer_reciprocal (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    Summable ((largeChildLayer k A L).indicator
      (fun n : ℕ => (n : ℝ)^(-(1-1/((R*(2*k)^L : ℕ) : ℝ))))) := by
  have hb := reciprocal_exponent_bounds R hR
  simpa only [largeChildLayerExponent_reciprocal k R L hk hR] using
    summable_largeChildLayer k hk A (1-1/(R : ℝ)) hb.1 hb.2 H L

def largeChildMassFactor (k R L : ℕ) : ℕ := (1+2*R)^L * (2*k)^(L^2)

lemma largeChildMassFactor_step (k R L : ℕ) (hk : 1 ≤ k) :
    (1+2*(R*(2*k)^(L+1))) * largeChildMassFactor k R L ≤
      largeChildMassFactor k R (L+1) := by
  have hB : 1 ≤ 2*k := by omega
  have hp : 1 ≤ (2*k)^(L+1) := one_le_pow₀ hB
  have hcoef : 1+2*(R*(2*k)^(L+1)) ≤ (1+2*R)*(2*k)^(L+1) := by nlinarith
  calc
    _ ≤ ((1+2*R)*(2*k)^(L+1)) * largeChildMassFactor k R L :=
      Nat.mul_le_mul_right _ hcoef
    _ = (1+2*R)^(L+1) * (2*k)^(L^2+(L+1)) := by
      unfold largeChildMassFactor
      rw [pow_succ (1+2*R), pow_add]
      ring
    _ ≤ largeChildMassFactor k R (L+1) := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right hB (by nlinarith)

/-- All depth dependence of the mass is explicit. -/
theorem setPowerMass_largeChildLayer_le (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    setPowerMass (largeChildLayer k A L) (1-1/((R*(2*k)^L : ℕ) : ℝ)) ≤
      setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ) := by
  induction L with
  | zero => simp [largeChildLayer, largeChildMassFactor]
  | succ L ih =>
    let T : ℕ := R*(2*k)^L
    have hT : 1 ≤ T := Nat.mul_le_mul hR (one_le_pow₀ (by omega : 1 ≤ 2*k))
    have hTnext : T*(2*k) = R*(2*k)^(L+1) := by dsimp [T]; rw [pow_succ]; ring
    have hbT := reciprocal_exponent_bounds T hT
    have hstep : 1-1/(T : ℝ) ≤ 1-1/((R*(2*k)^(L+1) : ℕ) : ℝ) := by
      have h := (nextLargeChildExponent_bounds k hk (1-1/(T : ℝ)) hbT.1 hbT.2).1
      simpa only [nextLargeChildExponent_reciprocal, hTnext] using h
    have HL : Summable ((largeChildLayer k A L).indicator
        (fun n : ℕ => (n : ℝ)^(-(1-1/(T : ℝ))))) :=
      summable_largeChildLayer_reciprocal k R hk hR A H L
    have HP := summable_largeChildParents_reciprocal k T hk hT (largeChildLayer k A L) HL
    rw [hTnext] at HP
    have HLn := summable_set_power_mono _ _ _ hstep HL
    have hpar := setPowerMass_largeChildParents_reciprocal_le k T hk hT
      (largeChildLayer k A L) HL
    rw [hTnext] at hpar
    have hraise := setPowerMass_exponent_mono (largeChildLayer k A L)
      (zero_not_mem_largeChildLayer k A hA L) _ _ hstep HL
    have hcoef : 0 ≤ (1+2*(R*(2*k)^(L+1) : ℕ) : ℝ) := by positivity
    calc
      _ ≤ setPowerMass (largeChildLayer k A L) (1-1/((R*(2*k)^(L+1) : ℕ) : ℝ)) +
          setPowerMass (largeChildParents k (largeChildLayer k A L))
            (1-1/((R*(2*k)^(L+1) : ℕ) : ℝ)) :=
        setPowerMass_union_le _ _ _ HLn HP
      _ ≤ (1+2*(R*(2*k)^(L+1) : ℕ) : ℝ) *
          setPowerMass (largeChildLayer k A L) (1-1/(T : ℝ)) := by
        have h := _root_.add_le_add hraise hpar
        convert h using 1
        ring
      _ ≤ (1+2*(R*(2*k)^(L+1) : ℕ) : ℝ) *
          (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ)) :=
        mul_le_mul_of_nonneg_left ih hcoef
      _ = setPowerMass A (1-1/(R : ℝ)) *
          (((1+2*(R*(2*k)^(L+1))) * largeChildMassFactor k R L : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast largeChildMassFactor_step k R L hk)
        (setPowerMass_nonneg A _)

lemma card_set_le_rpow_mass (A : Set ℕ) (hA : 0 ∉ A) (s : ℝ) (hs : 0 ≤ s)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-s))))
    (N : ℕ) (_hN : 1 ≤ N) :
    (((range (N+1)).filter (fun n => n ∈ A)).card : ℝ) ≤
      (N : ℝ)^s * setPowerMass A s := by
  let F := (range (N+1)).filter (fun n => n ∈ A)
  have hsum : (∑ n ∈ F, (n : ℝ)^(-s)) ≤ setPowerMass A s := by
    calc
      _ = ∑ n ∈ F, A.indicator (fun n : ℕ => (n : ℝ)^(-s)) n := by
        apply sum_congr rfl
        intro n hn
        rw [Set.indicator_of_mem (mem_filter.mp hn).2]
      _ ≤ _ := H.sum_le_tsum _
        (fun n _ => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
  calc
    (F.card : ℝ) = ∑ _n ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ F, (N : ℝ)^s * (n : ℝ)^(-s) := by
      apply sum_le_sum
      intro n hn
      have hnA := (mem_filter.mp hn).2
      have hnN : n ≤ N := by have := mem_range.mp (mem_filter.mp hn).1; omega
      have hn0 : 0 < n := by
        have hnne : n ≠ 0 := by intro hz; exact hA (hz ▸ hnA)
        exact Nat.pos_of_ne_zero hnne
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      calc
        (1 : ℝ) = (n : ℝ)^s * (n : ℝ)^(-s) := by rw [← Real.rpow_add hnR]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hnR.le (by exact_mod_cast hnN) hs)
          (Real.rpow_nonneg hnR.le _)
    _ = (N : ℝ)^s * ∑ n ∈ F, (n : ℝ)^(-s) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The finite counting bound retains the full explicit mass factor. -/
theorem largeChildLayer_card_le (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ))))))
    (L N : ℕ) (hN : 1 ≤ N) :
    (((range (N+1)).filter (fun n => n ∈ largeChildLayer k A L)).card : ℝ) ≤
      (N : ℝ)^(1-1/((R*(2*k)^L : ℕ) : ℝ)) *
        (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ)) := by
  have hT : 1 ≤ R*(2*k)^L := Nat.mul_le_mul hR (one_le_pow₀ (by omega : 1 ≤ 2*k))
  exact (card_set_le_rpow_mass _ (zero_not_mem_largeChildLayer k A hA L) _
    (reciprocal_exponent_bounds _ hT).1
    (summable_largeChildLayer_reciprocal k R hk hR A H L) N hN).trans
      (mul_le_mul_of_nonneg_left (setPowerMass_largeChildLayer_le k R hk hR A hA H L)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end Erdos821
