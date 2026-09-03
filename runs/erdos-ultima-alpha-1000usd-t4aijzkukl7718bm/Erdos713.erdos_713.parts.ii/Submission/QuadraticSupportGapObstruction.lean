import FormalConjecturesUtil
import Submission.QuadraticSupportTangents

/-! Integer secants obstruct bounded additive gaps between positive quadratic
supports of a superlinear, subquadratic pure-power sequence. This is a
necessary-condition diagnostic, not a proof of Erdős 713. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticSupportGapObstruction
open Erdos713ExactCloneSaturation Erdos713QuadraticSupportTangents
set_option maxHeartbeats 2000000

lemma eventually_small_curvature {f : ℕ → ℕ} {α c η : ℝ}
    (ha2 : α < 2) (hη : 0 < η)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, QuadSupport f ε n → ε < η := by
  have hz : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using Erdos713FutureRecords.higher_ratio_zero ha2 h
  filter_upwards [hz.eventually_lt_const hη, eventually_gt_atTop (0 : ℕ)] with n hn hnp
  intro ε hs
  have hh := hs 0
  have hp : 0 < (n : ℝ)^2 := by positivity
  have hb := (div_lt_iff₀ hp).mp hn
  have hf : 0 ≤ (f 0 : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_sub] at hh
  nlinarith

/-- At a sufficiently flat support, two adjacent secants with bounded
integer denominators cannot increase. -/
lemma flat_support_secants {f : ℕ → ℕ} {a b c L : ℕ} {ε : ℝ}
    (hab : a < b) (hbc : b < c) (habL : b-a ≤ L) (hbcL : c-b ≤ L)
    (hε : 0 ≤ ε) (hsmall : 2*ε*(L : ℝ)^3 < 1) (hs : QuadSupport f ε b) :
    ((f c : ℝ)-(f b : ℝ))/((c : ℝ)-(b : ℝ)) ≤
      ((f b : ℝ)-(f a : ℝ))/((b : ℝ)-(a : ℝ)) := by
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbcR : (b : ℝ) < c := by exact_mod_cast hbc
  have habLR : (b : ℝ)-(a : ℝ) ≤ L := by
    have hh : ((b-a : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast habL
    simpa only [Nat.cast_sub hab.le] using hh
  have hbcLR : (c : ℝ)-(b : ℝ) ≤ L := by
    have hh : ((c-b : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hbcL
    simpa only [Nat.cast_sub hbc.le] using hh
  have hleft := hs a
  have hright := hs c
  have h1 := mul_le_mul_of_nonneg_right hright (sub_nonneg.mpr habR.le)
  have h2 := mul_le_mul_of_nonneg_right hleft (sub_nonneg.mpr hbcR.le)
  have hdet : ((f c : ℝ)-(f b : ℝ))*((b : ℝ)-(a : ℝ)) -
      ((f b : ℝ)-(f a : ℝ))*((c : ℝ)-(b : ℝ)) ≤
      ε*((b : ℝ)-(a : ℝ))*((c : ℝ)-(b : ℝ))*((c : ℝ)-(a : ℝ)) := by
    nlinarith only [h1,h2]
  have hprod : ((b : ℝ)-(a : ℝ))*((c : ℝ)-(b : ℝ))*((c : ℝ)-(a : ℝ)) ≤
      2*(L : ℝ)^3 := by
    calc
      _ ≤ (L : ℝ)*L*(2*L) := mul_le_mul
        (mul_le_mul habLR hbcLR (sub_nonneg.mpr hbcR.le) (Nat.cast_nonneg L))
        (by linarith) (sub_nonneg.mpr (habR.trans hbcR).le) (by positivity)
      _ = _ := by ring
  have hlt : ((f c : ℝ)-(f b : ℝ))*((b : ℝ)-(a : ℝ)) -
      ((f b : ℝ)-(f a : ℝ))*((c : ℝ)-(b : ℝ)) < 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod hε
    nlinarith only [hdet,hh,hsmall]
  have hi : ((f c : ℤ)-(f b : ℤ))*((b : ℤ)-(a : ℤ)) -
      ((f b : ℤ)-(f a : ℤ))*((c : ℤ)-(b : ℤ)) < 1 := by exact_mod_cast hlt
  have hi0 : ((f c : ℤ)-(f b : ℤ))*((b : ℤ)-(a : ℤ)) -
      ((f b : ℤ)-(f a : ℤ))*((c : ℤ)-(b : ℤ)) ≤ 0 := by omega
  have hr0 : ((f c : ℝ)-(f b : ℝ))*((b : ℝ)-(a : ℝ)) -
      ((f b : ℝ)-(f a : ℝ))*((c : ℝ)-(b : ℝ)) ≤ 0 := by exact_mod_cast hi0
  apply (div_le_div_iff₀ (sub_pos.mpr hbcR) (sub_pos.mpr habR)).mpr
  linarith

noncomputable def secant (f : ℕ → ℕ) (n : ℕ → ℕ) (i : ℕ) : ℝ :=
  ((f (n (i+1)) : ℝ)-(f (n i) : ℝ))/((n (i+1) : ℝ)-(n i : ℝ))

lemma secants_top {f : ℕ → ℕ} {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n : ℕ → ℕ} {ε : ℕ → ℝ} (hn : StrictMono n)
    (hε : ∀ i, 0 ≤ ε i) (hs : ∀ i, QuadSupport f (ε i) (n i)) :
    Tendsto (secant f n) atTop atTop := by
  have hp : 0 < α-1 := by linarith
  have hshift : Tendsto (fun i => n (i+1)) atTop atTop :=
    hn.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow : Tendsto (fun i => (c/2)*(n (i+1) : ℝ)^(α-1)) atTop atTop :=
    ((tendsto_rpow_atTop hp).comp
      (tendsto_natCast_atTop_atTop.comp hshift)).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [hshift.eventually
    (eventually_support_lower h (show c < c*α by nlinarith))] with i hi
  have hib : n i < n (i+1) := hn (Nat.lt_succ_self i)
  have hibR : (n i : ℝ) < n (i+1) := by exact_mod_cast hib
  have hh := hs (i+1) (n i)
  have hslope : ε (i+1)*((n i : ℝ)+(n (i+1) : ℝ)) ≤ secant f n i := by
    apply (le_div_iff₀ (sub_pos.mpr hibR)).mpr
    nlinarith only [hh]
  have hfac := mul_le_mul_of_nonneg_left
    (show (2*(n (i+1) : ℝ)-1)/2 ≤ (n i : ℝ)+(n (i+1) : ℝ) by
      have hh := Nat.cast_nonneg (α := ℝ) (n i)
      linarith) (hε (i+1))
  have hlo := hi _ (hs (i+1))
  nlinarith only [hslope,hfac,hlo]

/-- No cofinal increasing sequence of positive quadratic support orders
can have bounded gaps when the integer sequence has exponent in (1,2). -/
theorem no_bounded_support_sequence {f : ℕ → ℕ} {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n : ℕ → ℕ} {ε : ℕ → ℝ} (hn : StrictMono n)
    (hε : ∀ i, 0 ≤ ε i) (hs : ∀ i, QuadSupport f (ε i) (n i))
    (L : ℕ) (hg : ∀ i, n (i+1)-n i ≤ L) : False := by
  have hL : 0 < L := lt_of_lt_of_le (Nat.sub_pos_of_lt (hn (Nat.lt_succ_self 0))) (hg 0)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hη : 0 < 1/(2*(L : ℝ)^3) := by positivity
  have hev : ∀ᶠ i : ℕ in atTop, 2*ε i*(L : ℝ)^3 < 1 := by
    filter_upwards [hn.tendsto_atTop.eventually
      (eventually_small_curvature ha2 hη h)] with i hi
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2*(L : ℝ)^3 by positivity)).mp (hi _ (hs i))
    nlinarith only [hh]
  obtain ⟨I,hI⟩ := eventually_atTop.mp hev
  have hstep (i : ℕ) (hi : I ≤ i) : secant f n (i+1) ≤ secant f n i := by
    exact flat_support_secants (hn (Nat.lt_succ_self i)) (hn (Nat.lt_succ_self (i+1)))
      (hg i) (hg (i+1)) (hε (i+1)) (hI (i+1) (by omega)) (hs (i+1))
  have hb (i : ℕ) (hi : I ≤ i) : secant f n i ≤ secant f n I := by
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ i hi ih => exact (hstep i hi).trans ih
  have ht := secants_top ha hc h hn hε hs
  obtain ⟨i,hi,hbig⟩ := ((eventually_ge_atTop I).and
    (ht.eventually_gt_atTop (secant f n I))).exists
  exact (not_le_of_gt hbig) (hb i hi)

lemma sequence_of_tail_windows {P : ℕ → Prop} {L N : ℕ}
    (h : ∀ k, N ≤ k → ∃ n, k ≤ n ∧ n ≤ k+L ∧ P n) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, P (n i)) ∧
      ∀ i, n (i+1)-n i ≤ L+1 := by
  classical
  choose g hlo hhi hP using fun k => h (max k N) (le_max_right _ _)
  let n : ℕ → ℕ := Nat.rec (g N) (fun _ v => g (v+1))
  have hnN (i : ℕ) : N ≤ n i := by
    cases i with
    | zero => exact (le_max_right N N).trans (hlo N)
    | succ i => exact (le_max_right (n i+1) N).trans (hlo (n i+1))
  have hnP (i : ℕ) : P (n i) := by
    cases i with
    | zero => exact hP N
    | succ i => exact hP (n i+1)
  have hn : StrictMono n := strictMono_nat_of_lt_succ fun i =>
    (Nat.lt_succ_self (n i)).trans_le ((le_max_left (n i+1) N).trans (hlo (n i+1)))
  refine ⟨n,hn,hnP,?_⟩
  intro i
  have hh := hhi (n i+1)
  rw [max_eq_left (by have := hnN i; omega)] at hh
  change n (i+1) ≤ n i+1+L at hh
  omega

/-- Arbitrarily late intervals of any prescribed bounded length have no
nonnegative-curvature quadratic support at any of their integer orders. -/
theorem support_free_windows {f : ℕ → ℕ} {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (L N : ℕ) : ∃ k : ℕ, N ≤ k ∧ ∀ n : ℕ, k ≤ n → n ≤ k+L →
      ∀ ε : ℝ, 0 ≤ ε → ¬ QuadSupport f ε n := by
  classical
  by_contra hbad
  push_neg at hbad
  obtain ⟨n,hn,hP,hgap⟩ := sequence_of_tail_windows hbad
  choose ε hε hs using hP
  exact no_bounded_support_sequence ha ha2 hc h hn hε hs (L+1) hgap

lemma curvature_pos {f : ℕ → ℕ} {α c ε : ℝ} {n : ℕ}
    (ha : 0 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hs : QuadSupport f ε n) : 0 < ε := by
  have ht : Tendsto (fun m : ℕ => (f m : ℝ)) atTop atTop := by
    simpa only [Real.rpow_zero,div_one] using Erdos713FutureRecords.lower_ratio_top ha hc h
  obtain ⟨m,hm,hfm⟩ := ((eventually_ge_atTop n).and
    (ht.eventually_gt_atTop (f n : ℝ))).exists
  have hmn : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsq : 0 ≤ (m : ℝ)^2-(n : ℝ)^2 := by nlinarith
  by_contra he
  have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt he) hsq
  have hb := hs m
  linarith

/-- This version excludes every real curvature, since any support of the
unbounded nonnegative sequence necessarily has positive curvature. -/
theorem support_free_windows_all {f : ℕ → ℕ} {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (L N : ℕ) : ∃ k : ℕ, N ≤ k ∧ ∀ n : ℕ, k ≤ n → n ≤ k+L →
      ∀ ε : ℝ, ¬ QuadSupport f ε n := by
  obtain ⟨k,hk,hgap⟩ := support_free_windows ha ha2 hc h L N
  refine ⟨k,hk,?_⟩
  intro n hn hnL ε hs
  exact hgap n hn hnL ε (curvature_pos (by linarith) hc h hs).le hs

/-- In particular, even an actual extremal-number sequence with a
superlinear pure-power asymptotic has arbitrarily long late support gaps.
This says nothing against the existence of extremal hosts at those orders. -/
theorem extremal_support_free_windows {W : Type*} (H : SimpleGraph W)
    {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (L N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∀ n : ℕ, k ≤ n → n ≤ k+L →
      ∀ ε : ℝ, ¬ QuadSupport (fun m => SimpleGraph.extremalNumber m H) ε n :=
  support_free_windows_all ha ha2 hc h L N

#print axioms flat_support_secants
#print axioms no_bounded_support_sequence
#print axioms support_free_windows_all
#print axioms extremal_support_free_windows
end Erdos713QuadraticSupportGapObstruction
