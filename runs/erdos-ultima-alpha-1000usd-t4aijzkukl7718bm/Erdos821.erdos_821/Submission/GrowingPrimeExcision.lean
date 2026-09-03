import Submission.SmoothPrimeCore
import Submission.RecordInputScale

/-!
# Excision of input primes up to a growing polylogarithmic cutoff

The weighted support decomposition permits a growing cutoff, rather than only
one fixed before taking the output to infinity. The resulting extraction
preserves an already attained exponent; it is not exponent amplification.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

noncomputable def gAboveCutoff (B n : ℕ) : ℕ :=
  gSquarefreeOn (fun p => B < p) n

lemma gAboveCutoff_le_g (B n : ℕ) : gAboveCutoff B n ≤ g n :=
  gSquarefreeOn_le_g _ _

lemma gAboveCutoff_antitone (n : ℕ) : Antitone (fun B => gAboveCutoff B n) := by
  intro A B hAB
  apply Set.ncard_le_ncard _ (finite_squarefreeOn_fiber (fun p => A < p) n)
  intro m hm
  exact ⟨hm.1, hm.2.1, fun p hp => hAB.trans_lt (hm.2.2 p hp)⟩

lemma small_shifted_weight_sum_le (n B : ℕ) (s u : ℝ) (hsu : s ≤ u) (hu : 1 < u) :
    (∑ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬B < p),
      ((p-1 : ℕ) : ℝ)^(-s)) ≤
      (B : ℝ)^(u-s) * ∑' a : ℕ, (a : ℝ)^(-u) := by
  let P := (shiftedPrimeDivisors n).filter (fun p => ¬B < p)
  let D := P.image (fun p => p-1)
  have hpr (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ B := by
    obtain ⟨hp, hB⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_filter.mp hp).2.1, Nat.le_of_not_gt hB⟩
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have := (hpr p hp).1.two_le
    have := (hpr q hq).1.two_le
    change p-1 = q-1 at he
    omega
  have hD : ∀ d ∈ D, 0 < d ∧ d ≤ B ∧ 1 ∣ d := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨Nat.sub_pos_of_lt (hpr p hp).1.one_lt,
      (Nat.sub_le p 1).trans (hpr p hp).2, one_dvd _⟩
  have h := bounded_multiples_rpow_sum D B 1 (by decide) s u hsu hu hD
  simpa only [D, Finset.sum_image hinj, Nat.cast_one, Real.one_rpow, mul_one] using h

/-- Finite weighted excision, uniform in the cutoff B. -/
lemma g_weight_le_aboveCutoff_sum (n B : ℕ) (hn : 0 < n)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u) :
    (g n : ℝ)*(n : ℝ)^(-s) ≤
      (∑ d ∈ n.divisors, (gAboveCutoff B d : ℝ)*(d : ℝ)^(-s)) *
        Real.exp ((B : ℝ)^(u-s) * ∑' a : ℕ, (a : ℝ)^(-u)) := by
  have hprod : (∏ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬B < p),
      (1+((p-1 : ℕ) : ℝ)^(-s))) ≤
      Real.exp ((B : ℝ)^(u-s) * ∑' a : ℕ, (a : ℝ)^(-u)) := by
    calc
      _ ≤ ∏ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬B < p),
          Real.exp (((p-1 : ℕ) : ℝ)^(-s)) := by
        apply Finset.prod_le_prod
        · intro p hp; positivity
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (((p-1 : ℕ) : ℝ)^(-s))
      _ = Real.exp (∑ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬B < p),
          ((p-1 : ℕ) : ℝ)^(-s)) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (small_shifted_weight_sum_le n B s u hsu hu)
  apply (g_weight_le_core_sum_mul_rough (fun p => B < p) n hn s hs).trans
  change (∑ d ∈ n.divisors, (gAboveCutoff B d : ℝ)*(d : ℝ)^(-s)) * _ ≤ _
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun d _ => by positivity))
  convert hprod using 1
  congr 2

/-- The cutoff grows with n. No fixed-cutoff asymptotic is used uniformly. -/
lemma eventually_polylog_prime_excision_cost (s u c ε : ℝ)
    (hsu : s ≤ u) (_hc : 0 < c) (hcu : c*(u-s) < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) *
        Real.exp ((⌊(Real.log (n : ℝ))^c⌋₊ : ℝ)^(u-s) *
          ∑' a : ℕ, (a : ℝ)^(-u)) ≤ (n : ℝ)^ε := by
  let C : ℝ := ∑' a : ℕ, (a : ℝ)^(-u)
  let b : ℝ := c*(u-s)
  have hC : 0 ≤ C := tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
  have hb : 0 < 1-b := by dsimp [b]; linarith
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (ε/2)*(Real.log (n : ℝ))^(1-b)) atTop atTop :=
    ((tendsto_rpow_atTop hb).comp hlog).const_mul_atTop (half_pos hε)
  filter_upwards [hlim.eventually (eventually_ge_atTop C),
    eventually_card_divisors_le_rpow (ε/2) (half_pos hε),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop 1]
    with n hCbound hτ hlogn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmass : (⌊(Real.log (n : ℝ))^c⌋₊ : ℝ)^(u-s)*C ≤ (ε/2)*Real.log n := by
    calc
      _ ≤ ((Real.log (n : ℝ))^c)^(u-s)*C :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (Nat.floor_le (Real.rpow_nonneg hlogn.le _)) (sub_nonneg.mpr hsu)) hC
      _ = (Real.log (n : ℝ))^b*C := by rw [← Real.rpow_mul hlogn.le]
      _ ≤ (Real.log (n : ℝ))^b*((ε/2)*(Real.log (n : ℝ))^(1-b)) :=
        mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg hlogn.le _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hlogn, add_sub_cancel, Real.rpow_one]
  have hExp : Real.exp ((⌊(Real.log (n : ℝ))^c⌋₊ : ℝ)^(u-s)*C) ≤ (n : ℝ)^(ε/2) := by
    apply (Real.exp_le_exp.mpr hmass).trans_eq
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  calc
    _ ≤ (n : ℝ)^(ε/2)*(n : ℝ)^(ε/2) :=
      mul_le_mul hτ hExp (Real.exp_pos _).le (Real.rpow_nonneg hnR.le _)
    _ = _ := by rw [← Real.rpow_add hnR]; congr 1; ring

/-- A divisor realizes the weighted excised count up to the finite excision cost. -/
lemma exists_divisor_aboveCutoff_weight (n B : ℕ) (hn : 0 < n)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u) :
    ∃ d ∈ n.divisors,
      (g n : ℝ)*(n : ℝ)^(-s) ≤
        ((n.divisors.card : ℝ)*Real.exp ((B : ℝ)^(u-s)*∑' a : ℕ, (a : ℝ)^(-u))) *
          ((gAboveCutoff B d : ℝ)*(d : ℝ)^(-s)) := by
  let w : ℕ → ℝ := fun d => (gAboveCutoff B d : ℝ)*(d : ℝ)^(-s)
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image n.divisors w
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  refine ⟨d, hd, ?_⟩
  have hsum : (∑ e ∈ n.divisors, w e) ≤ (n.divisors.card : ℝ)*w d := by
    calc
      _ ≤ ∑ _e ∈ n.divisors, w d := Finset.sum_le_sum hmax
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (∑ e ∈ n.divisors, w e)*Real.exp
        ((B : ℝ)^(u-s)*∑' a : ℕ, (a : ℝ)^(-u)) :=
      g_weight_le_aboveCutoff_sum n B hn s u hs hsu hu
    _ ≤ ((n.divisors.card : ℝ)*w d)*Real.exp
        ((B : ℝ)^(u-s)*∑' a : ℕ, (a : ℝ)^(-u)) :=
      mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = _ := by dsimp [w]; ring

/-- Every sufficiently large qualifying output has a divisor retaining large
multiplicity after exclusion up to a cutoff computed from the ORIGINAL output. -/
theorem eventually_extract_polylog_excluded_fiber (s c ε : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hc : 0 < c) (hcs : c*(1-s) < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^(s+ε) < g n →
      ∃ d ∈ n.divisors,
        (n : ℝ)^(ε/2)*(d : ℝ)^s <
          gAboveCutoff ⌊(Real.log (n : ℝ))^c⌋₊ d := by
  let u : ℝ := 1+(1-c*(1-s))/(2*c)
  have hu : 1 < u := by
    have : 0 < (1-c*(1-s))/(2*c) := div_pos (by linarith) (by positivity)
    dsimp [u]
    linarith
  have hsu : s ≤ u := hs1.le.trans hu.le
  have huid : c*(u-s) = (1+c*(1-s))/2 := by
    dsimp [u]
    field_simp
    ring
  have hcu : c*(u-s) < 1 := by rw [huid]; linarith
  filter_upwards [eventually_polylog_prime_excision_cost s u c (ε/2)
    hsu hc hcu (half_pos hε), eventually_ge_atTop 1] with n hcost hn
  intro hg
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let B : ℕ := ⌊(Real.log (n : ℝ))^c⌋₊
  obtain ⟨d, hd, hbound⟩ := exists_divisor_aboveCutoff_weight n B hn0 s u hs hsu hu
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hgweight : (n : ℝ)^ε < (g n : ℝ)*(n : ℝ)^(-s) := by
    have h := mul_lt_mul_of_pos_right hg (Real.rpow_pos_of_pos hnR (-s))
    rw [← Real.rpow_add hnR, show s+ε+(-s) = ε by ring] at h
    exact h
  have hprod : (n : ℝ)^(ε/2)*(n : ℝ)^(ε/2) <
      (n : ℝ)^(ε/2)*((gAboveCutoff B d : ℝ)*(d : ℝ)^(-s)) := by
    rw [← Real.rpow_add hnR, add_halves]
    exact hgweight.trans_le (hbound.trans (mul_le_mul_of_nonneg_right hcost (by positivity)))
  have hweight : (n : ℝ)^(ε/2) < (gAboveCutoff B d : ℝ)*(d : ℝ)^(-s) :=
    (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hnR (ε/2))).mp hprod
  refine ⟨d, hd, ?_⟩
  have h := mul_lt_mul_of_pos_right hweight (Real.rpow_pos_of_pos hdR s)
  simpa only [mul_assoc, ← Real.rpow_add hdR, neg_add_cancel, Real.rpow_zero, mul_one] using h

lemma polylog_cutoff_mono (c : ℝ) (hc : 0 ≤ c) {d n : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) :
    ⌊(Real.log (d : ℝ))^c⌋₊ ≤ ⌊(Real.log (n : ℝ))^c⌋₊ := by
  apply Nat.floor_mono
  apply Real.rpow_le_rpow (Real.log_natCast_nonneg _)
    (Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdn)) hc

/-- An attained exponent survives a growing polylogarithmic exclusion. The
hypothesis supplies the exponent; the conclusion does not improve it. -/
theorem infinite_gAbovePolylog_of_infinite_g (s c ε : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (hc : 0 < c) (hcs : c*(1-s) < 1) (hε : 0 < ε)
    (H : {n : ℕ | (n : ℝ)^(s+ε) < g n}.Infinite) :
    {d : ℕ | (d : ℝ)^s < gAboveCutoff ⌊(Real.log (d : ℝ))^c⌋₊ d}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C : ℕ := (Finset.range (N+1)).sup g
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((eventually_extract_polylog_excluded_fiber s c ε hs hs1 hc hcs hε).and
      ((hlim.eventually (eventually_ge_atTop (C : ℝ))).and
        (hlim.eventually (eventually_ge_atTop (1 : ℝ)))))
  obtain ⟨n, hnH, hnM⟩ := H.exists_gt M
  obtain ⟨hextract, hC, h1⟩ := hM n hnM.le
  obtain ⟨d, hd, hbig⟩ := hextract hnH
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdpow : (1 : ℝ) ≤ (d : ℝ)^s := Real.one_le_rpow (by exact_mod_cast hd0) hs
  have hNd : N < d := by
    by_contra h
    have hsup : g d ≤ C := Finset.le_sup (f := g) (Finset.mem_range.mpr (by omega))
    have hupper : (gAboveCutoff ⌊(Real.log (n : ℝ))^c⌋₊ d : ℝ) ≤ C := by
      exact_mod_cast (gAboveCutoff_le_g _ _).trans hsup
    have hlower : (C : ℝ) ≤ (n : ℝ)^(ε/2)*(d : ℝ)^s := by
      exact hC.trans (le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) hdpow)
    exact (hlower.trans_lt hbig).not_ge hupper
  refine ⟨d, ?_, hNd⟩
  have hgrowth : (d : ℝ)^s < gAboveCutoff ⌊(Real.log (n : ℝ))^c⌋₊ d :=
    (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) h1).trans_lt hbig
  exact hgrowth.trans_le (by
    exact_mod_cast gAboveCutoff_antitone d (polylog_cutoff_mono c hc.le hd0 (Nat.divisor_le hd)))

/-- Weakening the output exponent does not change the growing cutoff. -/
lemma infinite_gAbovePolylog_mono_exponent (s t c : ℝ) (hst : s ≤ t)
    (H : {n : ℕ | (n : ℝ)^t < gAboveCutoff ⌊(Real.log (n : ℝ))^c⌋₊ n}.Infinite) :
    {n : ℕ | (n : ℝ)^s < gAboveCutoff ⌊(Real.log (n : ℝ))^c⌋₊ n}.Infinite := by
  apply (H.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hst).trans_lt hn.1

/-- The admissible cutoff is governed by the SOURCE exponent gamma, not
by the weaker exponent s retained in the conclusion. -/
theorem infinite_gAbovePolylog_of_source_exponent (s γ c : ℝ)
    (hs : 0 ≤ s) (hsγ : s < γ) (hγ1 : γ ≤ 1) (hc : 0 < c)
    (hcγ : c*(1-γ) < 1)
    (H : {n : ℕ | (n : ℝ)^γ < g n}.Infinite) :
    {d : ℕ | (d : ℝ)^s < gAboveCutoff ⌊(Real.log (d : ℝ))^c⌋₊ d}.Infinite := by
  have hid : c*(1-(1-1/c)) = 1 := by field_simp; ring
  have hbound : 1-1/c < γ := by nlinarith
  let a := max s (1-1/c)
  have haγ : a < γ := max_lt hsγ hbound
  let t := (a+γ)/2
  have hat : a < t := by dsimp [t]; linarith
  have htγ : t < γ := by dsimp [t]; linarith
  have hst : s < t := (le_max_left _ _).trans_lt hat
  have ht0 : 0 ≤ t := hs.trans hst.le
  have ht1 : t < 1 := htγ.trans_le hγ1
  have hcut : c*(1-t) < 1 := by
    have hbt : 1-1/c < t := (le_max_right _ _).trans_lt hat
    nlinarith
  have hε : 0 < γ-t := sub_pos.mpr htγ
  have H' := infinite_gAbovePolylog_of_infinite_g t c (γ-t) ht0 ht1 hc hcut hε
    (by simpa only [add_sub_cancel] using H)
  exact infinite_gAbovePolylog_mono_exponent s t c hst.le H'

end Erdos821
