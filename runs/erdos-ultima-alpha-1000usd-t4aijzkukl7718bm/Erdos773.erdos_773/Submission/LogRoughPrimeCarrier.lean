import Submission.RoughPairNorms
import Submission.PrimeColorCollisions

/-!
Near-linear prime carriers whose pairwise norms avoid all odd primes up to
a fixed multiple of log n. Neither this property nor any fixed-cutoff
version implies Sidonness.
-/
namespace Erdos773.LogRoughPrimeCarrier
open Finset Filter RoughPairNorms
set_option maxHeartbeats 1000000

/-- Odd primes up to a real cutoff. -/
noncomputable def excluded (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ 2<p)

lemma excluded_prime {x : ℝ} {p : ℕ} (hp : p∈excluded x) : p.Prime ∧ 2<p :=
  (mem_filter.mp hp).2

lemma mem_excluded {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p∈excluded x ↔ p.Prime ∧ 2<p ∧ (p:ℝ)≤x := by
  simp only [excluded,mem_filter,mem_range]
  have he : p<⌊x⌋₊+1 ↔ (p:ℝ)≤x := by
    rw [Nat.lt_succ_iff,Nat.le_floor_iff hx]
  rw [he]
  tauto

lemma excluded_card (x : ℝ) : (excluded x).card ≤ Nat.primeCounting ⌊x⌋₊ := by
  rw [Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  apply card_le_card
  intro p hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(excluded_prime hp).1⟩

/-- The local color cost at any fixed multiple of log n is subpower. -/
theorem eventually_small_excluded (δ K : ℝ) (hδ : 0<δ) (hK : 0<K) :
    ∀ᶠ n : ℕ in atTop, ((excluded (K*Real.log (n:ℝ))).card:ℝ)≤
      δ/4*Real.log (n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => K*Real.log (n:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hK
  have hcount := ht.eventually (Chebyshev.eventually_primeCounting_le
    (by norm_num : (0:ℝ)<1))
  have hbig := (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop
    (4*K*(Real.log 4+1)/δ)
  filter_upwards [hcount,hbig,ht.eventually_ge_atTop 2,eventually_ge_atTop 1]
    with n hc hb hn hn1
  have hL : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hl : 0<Real.log (K*Real.log (n:ℝ)) := Real.log_pos (by linarith)
  have hb' : 4*K*(Real.log 4+1)≤δ*Real.log (K*Real.log (n:ℝ)) := by
    have hh := (div_le_iff₀ hδ).mp hb
    simpa only [Function.comp_apply,mul_comm] using hh
  calc
    _ ≤ (Nat.primeCounting ⌊K*Real.log (n:ℝ)⌋₊ : ℝ) := by
      exact_mod_cast excluded_card (K*Real.log (n:ℝ))
    _ ≤ (Real.log 4+1)*(K*Real.log (n:ℝ))/Real.log (K*Real.log (n:ℝ)) := hc
    _ ≤ δ/4*Real.log (n:ℝ) := by
      apply (div_le_iff₀ hl).mpr
      have hh := mul_le_mul_of_nonneg_right hb' hL
      nlinarith only [hh]

/-- A prime-root carrier of near-linear size with logarithmically rough
pairwise norms. This is not a Sidon lower bound. The roots are at most 2n. -/
theorem eventual_carrier (δ K : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hK : 0<K) :
    ∀ᶠ n : ℕ in atTop, ∃ B ⊆ Icc 1 (2*n),
      (n:ℝ)^(1-δ)≤B.card ∧ (∀ a∈B, a.Prime) ∧
      ∀ a∈B, ∀ b∈B, ∀ p : ℕ, p.Prime → 2<p → (p:ℝ)≤K*Real.log (n:ℝ) →
        ¬p ∣ a^2+b^2 := by
  filter_upwards [eventually_prime_carrier δ hδ hδ1,
    eventually_small_excluded δ K hδ hK,eventually_ge_atTop 1] with n hn hc hn1
  obtain ⟨B,hB,hcard,hr⟩ := hn (excluded (K*Real.log (n:ℝ)))
    (fun _ hp => excluded_prime hp) hc
  refine ⟨B,?_,hcard,?_,?_⟩
  · intro a ha
    obtain ⟨haR,haP,ha5⟩ := mem_filter.mp (hB ha)
    have har := mem_range.mp haR
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a ha
    exact (mem_filter.mp (hB ha)).2.1
  · intro a ha b hb p hp hp2 hpc
    apply hr a ha b hb p
    apply (mem_excluded (show 0≤K*Real.log (n:ℝ) by
      have hh := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn1)
      positivity)).mpr
    exact ⟨hp,hp2,hpc⟩

end Erdos773.LogRoughPrimeCarrier
#print axioms Erdos773.LogRoughPrimeCarrier.eventually_small_excluded
#print axioms Erdos773.LogRoughPrimeCarrier.eventual_carrier
