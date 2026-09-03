import Submission.LargeChildMass

/-!
# Sharp finite-cofactor propagation of power-sparse sets

These estimates remove the extra factor two in the exponent gap of the
previous infinite-series majorant. They do not settle Erdos 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

lemma sum_Icc_neg_rpow_le (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    (∑ a ∈ Icc 1 N, (a : ℝ)^(-s)) ≤ (N : ℝ)^(1-s)/(1-s) := by
  rcases N with _ | N
  · simp [Real.zero_rpow (by linarith : 1-s ≠ 0)]
  have hf : AntitoneOn (fun x : ℝ => x^(-s)) (Set.Icc 1 (N+1 : ℕ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hi := AntitoneOn.sum_le_integral_Ico (by omega : 1 ≤ N+1)
    (show AntitoneOn (fun x : ℝ => x^(-s)) (Set.Icc ((1 : ℕ) : ℝ) (N+1 : ℕ)) by
      simpa only [Nat.cast_one] using hf)
  have he : (∑ a ∈ Icc 1 (N+1), (a : ℝ)^(-s)) =
      1 + ∑ a ∈ Ico 1 (N+1), ((a+1 : ℕ) : ℝ)^(-s) := by
    rw [Finset.sum_Ico_add' (fun a : ℕ => (a : ℝ)^(-s)) 1 (N+1) 1]
    have hset : Icc 1 (N+1) = insert 1 (Ico (1+1) ((N+1)+1)) := by
      ext a
      simp only [mem_insert, mem_Icc, mem_Ico]
      omega
    rw [hset, sum_insert (by simp)]
    norm_num
  rw [he]
  have hInt : (∫ x in (1 : ℝ)..(N+1 : ℕ), x^(-s)) =
      (((N+1 : ℕ) : ℝ)^(1-s)-1)/(1-s) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -s))]
    rw [show -s+1 = 1-s by ring, Real.one_rpow]
  simp only [Nat.cast_one] at hi
  rw [hInt] at hi
  have hp : 0 < 1-s := by linarith
  calc
    1 + ∑ a ∈ Ico 1 (N+1), ((a+1 : ℕ) : ℝ)^(-s) ≤
        1 + ((((N+1 : ℕ) : ℝ)^(1-s)-1)/(1-s)) := _root_.add_le_add le_rfl hi
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      rw [add_mul, div_mul_cancel₀ _ hp.ne']
      linarith

/-- The finite cofactor sum gives the endpoint exponent, without an auxiliary
summable infinite p-series. -/
lemma rough_divisor_weight_sum_sharp (D Q : Finset ℕ) (k : ℕ) (hk : 1 ≤ k)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1)
    (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ q ∈ Q, 0 < q)
    (hcover : ∀ d ∈ D, ∃ q ∈ Q, q ∣ d ∧ d ≤ q^k) :
    (∑ d ∈ D, (d : ℝ)^(-s)) ≤
      (1/(1-s)) * ∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(1-s)-1) := by
  have hqbound (q : ℕ) (hq : q ∈ Q) :
      (∑ d ∈ D with q ∣ d ∧ d ≤ q^k, (d : ℝ)^(-s)) ≤
        (q : ℝ)^((k : ℝ)*(1-s)-1)/(1-s) := by
    let E := D.filter (fun d => q ∣ d ∧ d ≤ q^k)
    have hqR : (0 : ℝ) < q := by exact_mod_cast hQ q hq
    have hinj : Set.InjOn (fun d : ℕ => d/q) (↑E : Set ℕ) := by
      intro d hd e he h
      change d/q = e/q at h
      rw [← Nat.mul_div_cancel' (mem_filter.mp hd).2.1,
        ← Nat.mul_div_cancel' (mem_filter.mp he).2.1, h]
    have hsub : E.image (fun d => d/q) ⊆ Icc 1 (q^(k-1)) := by
      intro a ha
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
      obtain ⟨hdD, hqd, hdk⟩ := mem_filter.mp hd
      have he : q*(d/q) = d := Nat.mul_div_cancel' hqd
      have hp : q^k = q*q^(k-1) := by
        rw [← _root_.pow_succ', Nat.sub_add_cancel hk]
      rw [hp, ← he] at hdk
      refine mem_Icc.mpr ⟨?_, Nat.le_of_mul_le_mul_left hdk (hQ q hq)⟩
      change 1 ≤ d/q
      have := hD d hdD
      by_contra hh
      have hz : (d/q : ℕ) = 0 := Nat.eq_zero_of_not_pos hh
      simp only [hz, mul_zero] at he
      omega
    calc
      (∑ d ∈ E, (d : ℝ)^(-s)) =
          (q : ℝ)^(-s) * ∑ a ∈ E.image (fun d => d/q), (a : ℝ)^(-s) := by
        rw [sum_image hinj, mul_sum]
        apply sum_congr rfl
        intro d hd
        nth_rw 1 [← Nat.mul_div_cancel' (mem_filter.mp hd).2.1]
        rw [Nat.cast_mul, Real.mul_rpow hqR.le (Nat.cast_nonneg _)]
      _ ≤ (q : ℝ)^(-s) * ∑ a ∈ Icc 1 (q^(k-1)), (a : ℝ)^(-s) :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity))
          (Real.rpow_nonneg hqR.le _)
      _ ≤ (q : ℝ)^(-s) * ((q^(k-1) : ℕ) : ℝ)^(1-s)/(1-s) := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
          (sum_Icc_neg_rpow_le (q^(k-1)) s hs hs1) (Real.rpow_nonneg hqR.le _)
      _ = _ := by
        rw [Nat.cast_pow, ← Real.rpow_natCast_mul hqR.le, ← Real.rpow_add hqR]
        congr 2
        rw [Nat.cast_sub hk, Nat.cast_one]
        ring
  calc
    (∑ d ∈ D, (d : ℝ)^(-s)) ≤
        ∑ d ∈ D, ∑ q ∈ Q, if q ∣ d ∧ d ≤ q^k then (d : ℝ)^(-s) else 0 := by
      apply sum_le_sum
      intro d hd
      obtain ⟨q, hq, hqd, hdk⟩ := hcover d hd
      have hsingle := single_le_sum
        (s := Q) (f := fun q => if q ∣ d ∧ d ≤ q^k then (d : ℝ)^(-s) else 0)
        (fun q _ => by dsimp only; split_ifs <;> positivity) hq
      simpa only [if_pos (And.intro hqd hdk)] using hsingle
    _ = ∑ q ∈ Q, ∑ d ∈ D with q ∣ d ∧ d ≤ q^k, (d : ℝ)^(-s) := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(1-s)-1)/(1-s) := sum_le_sum hqbound
    _ = _ := by rw [← sum_div]; ring

lemma sum_largeDivisorLift_sharp_le (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hexp : (k : ℝ)*(1-s)-1 ≤ -b)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) (F : Finset ℕ) :
    (∑ n ∈ F, (largeDivisorLift k A).indicator (fun n : ℕ => (n : ℝ)^(-s)) n) ≤
      (1/(1-s)) *
        ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
  let C : ℝ := (1/(1-s)) *
    ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q
  let D := F.filter (fun n => n ∈ largeDivisorLift k A)
  let Q := D.biUnion (fun n => n.divisors.filter (fun q => q ∈ A ∧ n ≤ q^k))
  have hD (n : ℕ) (hn : n ∈ D) : 0 < n := (mem_filter.mp hn).2.1
  have hQ (q : ℕ) (hq : q ∈ Q) : 0 < q ∧ q ∈ A := by
    obtain ⟨n, hn, hq⟩ := mem_biUnion.mp hq
    exact ⟨Nat.pos_of_mem_divisors (mem_filter.mp hq).1, (mem_filter.mp hq).2.1⟩
  have hcover (n : ℕ) (hn : n ∈ D) : ∃ q ∈ Q, q ∣ n ∧ n ≤ q^k := by
    obtain ⟨hnF, hn0, q, hqA, hq0, hqn, hnq⟩ := mem_filter.mp hn
    refine ⟨q, mem_biUnion.mpr ⟨n, hn, ?_⟩, hqn, hnq⟩
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqn, hn0.ne'⟩, hqA, hnq⟩
  have hsumQ : (∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(1-s)-1)) ≤
      ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
    calc
      _ ≤ ∑ q ∈ Q, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
        apply sum_le_sum
        intro q hq
        rw [Set.indicator_of_mem (hQ q hq).2]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (hQ q hq).1) hexp
      _ ≤ _ := Summable.sum_le_tsum _
        (fun q _ => Set.indicator_nonneg (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _) q) H
  have hC0 : 0 ≤ (1/(1-s) : ℝ) :=
    le_of_lt (one_div_pos.mpr (by linarith))
  calc
    _ = ∑ n ∈ D, (n : ℝ)^(-s) := by
      simp only [D, sum_filter, Set.indicator_apply]
    _ ≤ (1/(1-s)) * ∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(1-s)-1) :=
      rough_divisor_weight_sum_sharp D Q k hk s hs hs1 hD (fun q hq => (hQ q hq).1) hcover
    _ ≤ C := mul_le_mul_of_nonneg_left hsumQ hC0

lemma summable_largeDivisorLift_sharp (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hexp : (k : ℝ)*(1-s)-1 ≤ -b)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    Summable ((largeDivisorLift k A).indicator (fun n : ℕ => (n : ℝ)^(-s))) := by
  exact summable_of_sum_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
    (sum_largeDivisorLift_sharp_le k hk A b s hs hs1 hexp H)

lemma sum_largeChildParents_sharp_le (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hexp : (k : ℝ)*(1-s)-1 ≤ -b)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) (F : Finset ℕ) :
    (∑ p ∈ F, (largeChildParents k A).indicator (fun p : ℕ => (p : ℝ)^(-s)) p) ≤
      (1/(1-s)) * setPowerMass A b := by
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
    _ ≤ _ := sum_largeDivisorLift_sharp_le k hk A b s hs hs1 hexp H D

lemma summable_largeChildParents_sharp (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hexp : (k : ℝ)*(1-s)-1 ≤ -b)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) :
    Summable ((largeChildParents k A).indicator (fun n : ℕ => (n : ℝ)^(-s))) := by
  exact summable_of_sum_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
    (sum_largeChildParents_sharp_le k hk A b s hs hs1 hexp H)

lemma setPowerMass_largeChildParents_sharp_le (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hexp : (k : ℝ)*(1-s)-1 ≤ -b)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) :
    setPowerMass (largeChildParents k A) s ≤
      (1/(1-s)) * setPowerMass A b := by
  exact (summable_largeChildParents_sharp k hk A b s hs hs1 hexp H).tsum_le_of_sum_le
    (sum_largeChildParents_sharp_le k hk A b s hs hs1 hexp H)


noncomputable def sharpLargeChildExponent (k : ℕ) (b : ℝ) : ℝ :=
  1-(1-b)/(k : ℝ)

lemma sharpLargeChildExponent_bounds (k : ℕ) (hk : 1 ≤ k) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    b ≤ sharpLargeChildExponent k b ∧
      0 ≤ sharpLargeChildExponent k b ∧ sharpLargeChildExponent k b < 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < (k : ℝ) := by linarith
  have he : 0 < (1-b)/(k : ℝ) := div_pos (by linarith) hd
  have he' : (1-b)/(k : ℝ) ≤ 1-b := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  dsimp [sharpLargeChildExponent]
  constructor
  · linarith
  constructor <;> linarith

/-- Exact endpoint update for the counting exponent. -/
theorem summable_largeChildParents_endpoint (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-b)))) :
    Summable ((largeChildParents k A).indicator
      (fun n : ℕ => (n : ℝ)^(-sharpLargeChildExponent k b))) := by
  have hbnd := sharpLargeChildExponent_bounds k hk b hb hb1
  apply summable_largeChildParents_sharp k hk A b (sharpLargeChildExponent k b)
    hbnd.2.1 hbnd.2.2 _ H
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold sharpLargeChildExponent
  apply le_of_eq
  field_simp
  ring

lemma sharpLargeChildExponent_reciprocal (k R : ℕ) :
    sharpLargeChildExponent k (1-1/(R : ℝ)) = 1-1/((R*k : ℕ) : ℝ) := by
  unfold sharpLargeChildExponent
  push_cast
  ring

lemma summable_largeChildParents_reciprocal_sharp (k R : ℕ)
    (hk : 1 ≤ k) (hR : 1 ≤ R) (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    Summable ((largeChildParents k A).indicator
      (fun n : ℕ => (n : ℝ)^(-(1-1/((R*k : ℕ) : ℝ))))) := by
  have hb := reciprocal_exponent_bounds R hR
  simpa only [sharpLargeChildExponent_reciprocal] using
    summable_largeChildParents_endpoint k hk A (1-1/(R : ℝ)) hb.1 hb.2 H

lemma setPowerMass_largeChildParents_reciprocal_sharp_le (k R : ℕ)
    (hk : 1 ≤ k) (hR : 1 ≤ R) (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    setPowerMass (largeChildParents k A) (1-1/((R*k : ℕ) : ℝ)) ≤
      (R*k : ℕ) * setPowerMass A (1-1/(R : ℝ)) := by
  have hRK : 1 ≤ R*k := Nat.mul_le_mul hR hk
  have hb := reciprocal_exponent_bounds (R*k) hRK
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have he : (k : ℝ)*(1-(1-1/((R*k : ℕ) : ℝ)))-1 = -(1-1/(R : ℝ)) := by
    push_cast
    field_simp
    ring
  have hm := setPowerMass_largeChildParents_sharp_le k hk A
    (1-1/(R : ℝ)) (1-1/((R*k : ℕ) : ℝ)) hb.1 hb.2 he.le H
  simpa only [sub_sub_cancel, one_div_one_div] using hm

lemma summable_largeChildLayer_reciprocal_sharp (k R : ℕ)
    (hk : 1 ≤ k) (hR : 1 ≤ R) (A : Set ℕ)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    Summable ((largeChildLayer k A L).indicator
      (fun n : ℕ => (n : ℝ)^(-(1-1/((R*k^L : ℕ) : ℝ))))) := by
  induction L with
  | zero => simpa only [pow_zero, mul_one, largeChildLayer] using H
  | succ L ih =>
    have hT : 1 ≤ R*k^L := Nat.mul_le_mul hR (one_le_pow₀ hk)
    have he : (R*k^L)*k = R*k^(L+1) := by rw [pow_succ]; ring
    have hb := reciprocal_exponent_bounds (R*k^L) hT
    have hmono := (sharpLargeChildExponent_bounds k hk _ hb.1 hb.2).1
    rw [sharpLargeChildExponent_reciprocal, he] at hmono
    have hp := summable_largeChildParents_reciprocal_sharp k (R*k^L) hk hT _ ih
    rw [he] at hp
    exact summable_set_power_union _ _ _ (summable_set_power_mono _ _ _ hmono ih) hp

/-- Explicit depth-dependent cost with the sharp exponent gap k^(-L). -/
def sharpLargeChildMassFactor (k R L : ℕ) : ℕ := (1+R)^L*k^(L^2)

lemma sharpLargeChildMassFactor_step (k R L : ℕ) (hk : 1 ≤ k) :
    (1+R*k^(L+1))*sharpLargeChildMassFactor k R L ≤
      sharpLargeChildMassFactor k R (L+1) := by
  have hp : 1 ≤ k^(L+1) := one_le_pow₀ hk
  have hc : 1+R*k^(L+1) ≤ (1+R)*k^(L+1) := by nlinarith
  calc
    _ ≤ ((1+R)*k^(L+1))*sharpLargeChildMassFactor k R L :=
      Nat.mul_le_mul_right _ hc
    _ = (1+R)^(L+1)*k^(L^2+(L+1)) := by
      unfold sharpLargeChildMassFactor
      rw [pow_succ (1+R), pow_add]
      ring
    _ ≤ sharpLargeChildMassFactor k R (L+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hk (by nlinarith))

theorem setPowerMass_largeChildLayer_sharp_le (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    setPowerMass (largeChildLayer k A L) (1-1/((R*k^L : ℕ) : ℝ)) ≤
      setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ) := by
  induction L with
  | zero => simp [largeChildLayer, sharpLargeChildMassFactor]
  | succ L ih =>
    let T : ℕ := R*k^L
    have hT : 1 ≤ T := Nat.mul_le_mul hR (one_le_pow₀ hk)
    have hTnext : T*k = R*k^(L+1) := by dsimp [T]; rw [pow_succ]; ring
    have hbT := reciprocal_exponent_bounds T hT
    have hstep : 1-1/(T : ℝ) ≤ 1-1/((R*k^(L+1) : ℕ) : ℝ) := by
      have h := (sharpLargeChildExponent_bounds k hk (1-1/(T : ℝ)) hbT.1 hbT.2).1
      simpa only [sharpLargeChildExponent_reciprocal, hTnext] using h
    have HL : Summable ((largeChildLayer k A L).indicator
        (fun n : ℕ => (n : ℝ)^(-(1-1/(T : ℝ))))) :=
      summable_largeChildLayer_reciprocal_sharp k R hk hR A H L
    have HP := summable_largeChildParents_reciprocal_sharp k T hk hT (largeChildLayer k A L) HL
    rw [hTnext] at HP
    have HLn := summable_set_power_mono _ _ _ hstep HL
    have hpar := setPowerMass_largeChildParents_reciprocal_sharp_le k T hk hT
      (largeChildLayer k A L) HL
    rw [hTnext] at hpar
    have hraise := setPowerMass_exponent_mono (largeChildLayer k A L)
      (zero_not_mem_largeChildLayer k A hA L) _ _ hstep HL
    have hcoef : 0 ≤ (1+(R*k^(L+1) : ℕ) : ℝ) := by positivity
    calc
      _ ≤ setPowerMass (largeChildLayer k A L) (1-1/((R*k^(L+1) : ℕ) : ℝ)) +
          setPowerMass (largeChildParents k (largeChildLayer k A L))
            (1-1/((R*k^(L+1) : ℕ) : ℝ)) :=
        setPowerMass_union_le _ _ _ HLn HP
      _ ≤ (1+(R*k^(L+1) : ℕ) : ℝ) *
          setPowerMass (largeChildLayer k A L) (1-1/(T : ℝ)) := by
        have h := _root_.add_le_add hraise hpar
        convert h using 1
        ring
      _ ≤ (1+(R*k^(L+1) : ℕ) : ℝ) *
          (setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ)) :=
        mul_le_mul_of_nonneg_left ih hcoef
      _ = setPowerMass A (1-1/(R : ℝ)) *
          (((1+(R*k^(L+1))) * sharpLargeChildMassFactor k R L : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast sharpLargeChildMassFactor_step k R L hk)
        (setPowerMass_nonneg A _)


end Erdos821
