import Submission.RecursiveEnvelopeShape
import Submission.SeededReferenceTransfer

/-! A precise within-model redundancy result. If a block source is justified
by positivity of the same unseeded numerical envelope, then it is already
bounded by the earlier-prefix lower envelope. This does NOT apply to every
arithmetic Jacobsthal bound or to arbitrary interval/count bootstraps. -/
namespace Erdos970.RecursiveSieve
open Finset

lemma positive_linearEnvelope_mass_gt (q : ℕ → ℝ) (k : ℕ) (x : ℝ)
    (hpos : 0 < (linearEnvelope q k x).1) : (k : ℝ)+1 < x := by
  by_contra hh
  have hx : x ≤ (k : ℝ)+1 := le_of_not_gt hh
  rw [linearEnvelope] at hpos
  simp only [hx,if_true] at hpos
  exact lt_irrefl _ hpos

/-- A positive later-prefix certificate contains at least one unit of lower
mass for each of its additional coordinates, plus its positive final margin. -/
theorem linearEnvelope_positive_prefix_gap (q : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j)
    (hq : ∀ n < j, 0 ≤ q n ∧ q n ≤ 1) (x : ℝ) (hx : 0 ≤ x)
    (hpos : 0 < (linearEnvelope q j x).1) :
    ((j-i : ℕ) : ℝ)+(linearEnvelope q j x).1 ≤ (linearEnvelope q i x).1 := by
  let U (n : ℕ) := (linearEnvelope q n (x*q n)).2
  have hU (n : ℕ) (hn : n < j) : 1 ≤ U n := by
    have hnq : ∀ t < n, 0 ≤ q t ∧ q t ≤ 1 :=
      fun t ht => hq t (ht.trans hn)
    have hh := (linearEnvelope_density_bounds q n hnq (x*q n)
      (mul_nonneg hx (hq n hn).1)).2
    have hnn := mul_nonneg (mul_nonneg hx (hq n hn).1) (prefixDensity_nonneg q n hnq)
    dsimp only [U]
    linarith
  have hje : (linearEnvelope q j x).1 = max 0 (x-1-∑ n ∈ range j, U n) := by
    rw [linearEnvelope_lower_eq_max q j hq x hx,
      Fin.sum_univ_eq_sum_range (fun n => (linearEnvelope q n (x*q n)).2) j]
  have hr : 0 < x-1-∑ n ∈ range j, U n := by
    rw [hje] at hpos
    by_contra hh
    rw [max_eq_left (le_of_not_gt hh)] at hpos
    exact lt_irrefl _ hpos
  rw [max_eq_right hr.le] at hje
  have hil : x-1-∑ n ∈ range i, U n ≤ (linearEnvelope q i x).1 := by
    rw [linearEnvelope_lower_eq_max q i (fun n hn => hq n (hn.trans_le hij)) x hx,
      Fin.sum_univ_eq_sum_range (fun n => (linearEnvelope q n (x*q n)).2) i]
    exact le_max_right _ _
  have hs := sum_le_sum (s := Ico i j) (fun n hn => hU n (mem_Ico.mp hn).2)
  simp only [sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one] at hs
  have he := sum_range_add_sum_Ico U hij
  linarith

/-- The transferred double-core affine block source is dominated whenever
its source bound was itself certified by the plain envelope at the SAME
marginal sequence. Arithmetic source bounds with no such certificate are
not covered by this lemma. -/
theorem blockSource_le_of_plain_positive (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (j g : ℕ → ℕ) (i : ℕ)
    (hg : 0 < g i) (hpos : 0 < (linearEnvelope q (j i) (g i : ℝ)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    blockSource j g i x ≤ (linearEnvelope q i x).1 := by
  let t : ℕ := j i+1-2*i
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hgR : (0 : ℝ) < g i := by exact_mod_cast hg
  have hα : 0 ≤ (t : ℝ)/(g i : ℝ) := div_nonneg ht0 hgR.le
  change max 0 ((t : ℝ)/(g i : ℝ)*(x-1)-(t : ℝ)) ≤ _
  by_cases htg : t = 0
  · simp only [htg,Nat.cast_zero,zero_div,zero_mul,sub_zero,max_self]
    exact linearEnvelope_lower_nonneg q i x
  by_cases hi : i = 0
  · subst i
    have hgm := positive_linearEnvelope_mass_gt q (j 0) (g 0 : ℝ) hpos
    have ht : (t : ℝ) ≤ g 0 := by
      dsimp only [t]
      norm_num only [mul_zero,Nat.sub_zero,Nat.cast_add,Nat.cast_one]
      linarith
    have hα1 : (t : ℝ)/(g 0 : ℝ) ≤ 1 := (div_le_one hgR).mpr ht
    rw [linearEnvelope_lower_eq_max q 0 (by simp) x hx]
    simp only [Finset.univ_eq_empty,Finset.sum_empty,sub_zero]
    apply max_le (le_max_left _ _)
    by_cases hx1 : 1 ≤ x
    · have hh := mul_le_mul_of_nonneg_right hα1 (sub_nonneg.mpr hx1)
      have hl := le_max_right 0 (x-1)
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hα (by linarith : x-1 ≤ 0)
      exact (by linarith : (t : ℝ)/(g 0 : ℝ)*(x-1)-(t : ℝ) ≤ 0).trans (le_max_left _ _)
  · have hi1 : 1 ≤ i := by omega
    have htj : i ≤ j i := by dsimp only [t] at htg; omega
    have hti : t ≤ j i-i := by dsimp only [t]; omega
    have hgap := linearEnvelope_positive_prefix_gap q i (j i) htj (fun n _ => hq n)
      (g i : ℝ) hgR.le hpos
    have hLg : (t : ℝ) ≤ (linearEnvelope q i (g i : ℝ)).1 := by
      have htR : (t : ℝ) ≤ (j i-i : ℕ) := by exact_mod_cast hti
      linarith
    apply max_le (linearEnvelope_lower_nonneg q i x)
    by_cases hxg : x ≤ g i
    · have hh := mul_le_mul_of_nonneg_left (show x-1 ≤ (g i : ℝ) by linarith) hα
      rw [div_mul_cancel₀ _ hgR.ne'] at hh
      exact (by linarith : (t : ℝ)/(g i : ℝ)*(x-1)-(t : ℝ) ≤ 0).trans
        (linearEnvelope_lower_nonneg q i x)
    · have hscale := linearEnvelope_lower_scale q i (fun n _ => hq n)
        (g i : ℝ) (x/(g i : ℝ)) hgR.le ((one_le_div hgR).mpr (le_of_not_ge hxg))
      rw [div_mul_cancel₀ _ hgR.ne'] at hscale
      have hh := mul_le_mul_of_nonneg_left hLg (div_nonneg hx hgR.le)
      have he : (t : ℝ)/(g i : ℝ)*(x-1)-(t : ℝ) =
          (x/(g i : ℝ))*(t : ℝ)-((t : ℝ)/(g i : ℝ)+(t : ℝ)) := by ring
      rw [he]
      linarith

/-- Unpruned numerical recurrence with arbitrary verified lower sources. -/
noncomputable def seededLinearEnvelope (q : ℕ → ℝ) (seed : ℕ → ℝ → ℝ)
    (k : ℕ) (x : ℝ) : ℝ × ℝ :=
  (max (seed k x) (max 0 (x-1-∑ i : Fin k,
    (seededLinearEnvelope q seed i.val (x*q i.val)).2)),
    x+1-∑ i : Fin k, (seededLinearEnvelope q seed i.val (x*q i.val)).1)
termination_by k

/-- This is a genuinely recursive equality, not the old fixed-child-cost
redundancy statement. Its extra premise is domination by the plain envelope
at EVERY smaller recursive mass. -/
theorem seededLinearEnvelope_eq_plain (q : ℕ → ℝ) (seed : ℕ → ℝ → ℝ)
    (k : ℕ) (hq : ∀ n < k, 0 ≤ q n ∧ q n ≤ 1)
    (hs : ∀ n ≤ k, ∀ x : ℝ, 0 ≤ x → seed n x ≤ (linearEnvelope q n x).1)
    (x : ℝ) (hx : 0 ≤ x) : seededLinearEnvelope q seed k x = linearEnvelope q k x := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    have hc (i : Fin k) := ih i.val i.isLt (fun n hn => hq n (hn.trans i.isLt))
      (fun n hn y hy => hs n (hn.trans i.isLt.le) y hy) (x*q i.val)
      (mul_nonneg hx (hq i.val i.isLt).1)
    have hl := linearEnvelope_lower_eq_max q k hq x hx
    conv_lhs => rw [seededLinearEnvelope]
    simp only [hc]
    apply Prod.ext
    · dsimp only
      rw [← hl]
      exact max_eq_right (hs k le_rfl x hx)
    · conv_rhs => rw [linearEnvelope]

/-- Sources obtained from already positive plain certificates cannot create
new positivity through dynamic child feedback in this specified model. -/
theorem block_seeded_eq_plain_of_plain_certificates (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (j g : ℕ → ℕ) (k : ℕ)
    (hg : ∀ n ≤ k, 0 < g n)
    (hpos : ∀ n ≤ k, 0 < (linearEnvelope q (j n) (g n : ℝ)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    seededLinearEnvelope q (blockSource j g) k x = linearEnvelope q k x :=
  seededLinearEnvelope_eq_plain q (blockSource j g) k (fun n _ => hq n)
    (fun n hn y hy => blockSource_le_of_plain_positive q hq j g n (hg n hn) (hpos n hn) y hy)
    x hx

#print axioms linearEnvelope_positive_prefix_gap
#print axioms blockSource_le_of_plain_positive
#print axioms seededLinearEnvelope_eq_plain
#print axioms block_seeded_eq_plain_of_plain_certificates
end Erdos970.RecursiveSieve
