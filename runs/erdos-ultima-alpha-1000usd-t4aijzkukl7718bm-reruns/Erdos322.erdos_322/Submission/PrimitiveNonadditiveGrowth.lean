import Submission.Spec

/-! Quantitative size estimates for the primitive nonadditive quartic recurrence.
These estimates do not establish a positive-power lower bound. -/
namespace Erdos322Research.PrimitiveNonadditiveGrowth

open Erdos322.PrimitiveNonadditive

private def growthFactor (s t : ℝ) : ℝ :=
  3468*s^8 + 2448*s^6*t^2 + 612*s^4*t^4 + 68*s^2*t^6 + 3*t^8

private theorem growthFactor_lower (s t : ℝ) :
    (s^2+t^2)^4 ≤ growthFactor s t := by
  calc
    (s^2+t^2)^4 ≤ (s^2+t^2)^4 +
        (3467*s^8 + 2444*s^6*t^2 + 606*s^4*t^4 + 64*s^2*t^6 + 2*t^8) :=
      le_add_of_nonneg_right (by positivity)
    _ = growthFactor s t := by unfold growthFactor; ring

private theorem growthFactor_upper (s t : ℝ) :
    growthFactor s t ≤ 3468*(s^2+t^2)^4 := by
  calc
    growthFactor s t ≤ growthFactor s t +
        (11424*s^6*t^2 + 20196*s^4*t^4 + 13804*s^2*t^6 + 3465*t^8) :=
      le_add_of_nonneg_right (by positivity)
    _ = 3468*(s^2+t^2)^4 := by unfold growthFactor; ring

private theorem growth_step_bounds (s t w : ℝ)
    (hq : w^2 = 1207*s^2+213*t^2) (hw : 71 ≤ w) :
    w^2 ≤ w*growthFactor s t ∧ w*growthFactor s t ≤ w^11 := by
  have hw0 : 0 ≤ w := by linarith
  have hs := sq_nonneg s
  have ht := sq_nonneg t
  have hQ0 : 0 ≤ s^2+t^2 := by positivity
  have hQlo : s^2+t^2 ≤ w^2 := by nlinarith
  have hQhi : w^2 ≤ 1207*(s^2+t^2) := by nlinarith
  have hlo : w^8 ≤ (1207 : ℝ)^4*growthFactor s t := by
    calc
      w^8 = (w^2)^4 := by ring
      _ ≤ (1207*(s^2+t^2))^4 := pow_le_pow_left₀ (by positivity) hQhi 4
      _ = (1207 : ℝ)^4*(s^2+t^2)^4 := by ring
      _ ≤ (1207 : ℝ)^4*growthFactor s t := by
        gcongr
        exact growthFactor_lower s t
  have hc : (1207 : ℝ)^4 ≤ w^7 := by
    calc
      (1207 : ℝ)^4 ≤ 71^7 := by norm_num
      _ ≤ w^7 := pow_le_pow_left₀ (by norm_num) hw 7
  have hflo : w ≤ growthFactor s t := by
    have h : (1207 : ℝ)^4*w ≤ (1207 : ℝ)^4*growthFactor s t := by
      calc
        (1207 : ℝ)^4*w ≤ w^7*w := mul_le_mul_of_nonneg_right hc hw0
        _ = w^8 := by ring
        _ ≤ _ := hlo
    nlinarith
  have hchi : (3468 : ℝ) ≤ w^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 71) hw 2
    norm_num at h
    linarith
  have hfhi : growthFactor s t ≤ w^10 := by
    calc
      growthFactor s t ≤ 3468*(s^2+t^2)^4 := growthFactor_upper s t
      _ ≤ 3468*(w^2)^4 := by gcongr
      _ = 3468*w^8 := by ring
      _ ≤ w^2*w^8 := mul_le_mul_of_nonneg_right hchi (by positivity)
      _ = w^10 := by ring
  constructor
  · calc
      w^2 = w*w := by ring
      _ ≤ w*growthFactor s t := mul_le_mul_of_nonneg_left hflo hw0
  · calc
      w*growthFactor s t ≤ w*w^10 := mul_le_mul_of_nonneg_left hfhi hw0
      _ = w^11 := by ring

private theorem point_w_step (n : ℕ) :
    ((point (n+1)).w : ℝ) = (point n).w *
      growthFactor ((point n).s : ℝ) ((point n).t : ℝ) := by
  change (((point n).w * (3468*(point n).s^8 + 2448*(point n).s^6*(point n).t^2 +
    612*(point n).s^4*(point n).t^4 + 68*(point n).s^2*(point n).t^6 +
    3*(point n).t^8) : ℤ) : ℝ) = _
  push_cast
  rfl

theorem point_w_ge (n : ℕ) : (71 : ℝ) ≤ (point n).w := by
  induction n with
  | zero => norm_num [point]
  | succ n ih =>
    have hq : ((point n).w : ℝ)^2 =
        1207*((point n).s : ℝ)^2+213*((point n).t : ℝ)^2 := by
      exact_mod_cast (point_on_quadrics n).2
    have h := (growth_step_bounds _ _ _ hq ih).1
    rw [point_w_step]
    have hw : (71 : ℝ)^2 ≤ ((point n).w : ℝ)^2 :=
      pow_le_pow_left₀ (by norm_num) ih 2
    linarith

theorem point_w_bounds (n : ℕ) :
    (71 : ℝ)^(2^n) ≤ (point n).w ∧ (point n).w ≤ (71 : ℝ)^(11^n) := by
  induction n with
  | zero => norm_num [point]
  | succ n ih =>
    have hq : ((point n).w : ℝ)^2 =
        1207*((point n).s : ℝ)^2+213*((point n).t : ℝ)^2 := by
      exact_mod_cast (point_on_quadrics n).2
    obtain ⟨hl, hu⟩ := growth_step_bounds _ _ _ hq (point_w_ge n)
    rw [point_w_step]
    constructor
    · calc
        (71 : ℝ)^(2^(n+1)) = ((71 : ℝ)^(2^n))^2 := by rw [pow_succ, pow_mul]
        _ ≤ ((point n).w : ℝ)^2 := pow_le_pow_left₀ (by positivity) ih.1 2
        _ ≤ _ := hl
    · calc
        (point n).w * growthFactor ((point n).s : ℝ) ((point n).t : ℝ) ≤
            ((point n).w : ℝ)^11 := hu
        _ ≤ ((71 : ℝ)^(11^n))^11 :=
          pow_le_pow_left₀ (by have := point_w_ge n; linarith) ih.2 11
        _ = (71 : ℝ)^(11^(n+1)) := by rw [pow_succ (11 : ℕ) n, pow_mul]


private theorem point_w_nat_cast (n : ℕ) :
    ((point n).w.natAbs : ℝ) = ((point n).w : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg]
  have := point_w_ge n
  linarith

private theorem point_w_nat_ge (n : ℕ) : 71 ≤ (point n).w.natAbs := by
  have h := point_w_ge n
  rw [← point_w_nat_cast] at h
  exact_mod_cast h

private theorem point_w_nat_bounds (n : ℕ) :
    71^(2^n) ≤ (point n).w.natAbs ∧ (point n).w.natAbs ≤ 71^(11^n) := by
  have h := point_w_bounds n
  rw [← point_w_nat_cast] at h
  exact_mod_cast h

private theorem denominator_pos (m : ℕ) : 0 < commonDenominator m := by
  apply Finset.prod_pos
  intro i _
  have := point_w_nat_ge i
  omega

private theorem denominator_succ (m : ℕ) :
    commonDenominator (m+1) = commonDenominator m * (point (m+1)).w.natAbs := by
  unfold commonDenominator
  rw [Fin.prod_univ_castSucc]
  rfl

theorem commonDenominator_bounds (m : ℕ) :
    71^(2^m) ≤ commonDenominator m ∧ commonDenominator m ≤ 71^(11^(m+1)) := by
  constructor
  · have hd : (point m).w.natAbs ∣ commonDenominator m :=
      Finset.dvd_prod_of_mem (fun i : Fin (m+1) ↦ (point i).w.natAbs)
        (Finset.mem_univ (Fin.last m))
    exact (point_w_nat_bounds m).1.trans (Nat.le_of_dvd (denominator_pos m) hd)
  · induction m with
    | zero => norm_num [commonDenominator, point, Fin.prod_univ_succ]
    | succ m ih =>
      rw [denominator_succ]
      calc
        commonDenominator m * (point (m+1)).w.natAbs ≤
            71^(11^(m+1)) * 71^(11^(m+1)) :=
          Nat.mul_le_mul ih (point_w_nat_bounds (m+1)).2
        _ = 71^(2*11^(m+1)) := by rw [← pow_add]; congr 1; omega
        _ ≤ 71^(11^(m+1+1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [pow_succ (11 : ℕ) (m+1)]
          omega

/-- The represented numbers in this particular construction grow doubly
exponentially in the number of distinct tuples supplied by the construction. -/
theorem representedNumber_bounds (m : ℕ) :
    71^(2^m) ≤ representedNumber m ∧ representedNumber m ≤ 71^(11^(m+2)) := by
  obtain ⟨hlo, hhi⟩ := commonDenominator_bounds m
  have hL := denominator_pos m
  have hLpow : 1 ≤ commonDenominator m ^ 4 := Nat.one_le_pow 4 _ hL
  constructor
  · have hp : commonDenominator m ≤ commonDenominator m ^ 4 := Nat.le_pow (by decide)
    apply hlo.trans
    unfold representedNumber
    nlinarith [hp]
  · have hs : representedNumber m ≤ 71^3 * commonDenominator m ^ 4 := by
      unfold representedNumber
      nlinarith [hLpow]
    calc
      representedNumber m ≤ 71^3 * commonDenominator m ^ 4 := hs
      _ ≤ 71^3 * (71^(11^(m+1)))^4 := by gcongr
      _ = 71^(3+4*11^(m+1)) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ 71^(11^(m+2)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have hp : 1 ≤ (11 : ℕ)^(m+1) := Nat.one_le_pow _ _ (by decide)
        rw [show m+2 = (m+1)+1 by omega, pow_succ (11 : ℕ) (m+1)]
        omega

theorem representedNumber_strictMono : StrictMono representedNumber := by
  apply strictMono_nat_of_lt_succ
  intro m
  have hL : commonDenominator m < commonDenominator (m+1) := by
    rw [denominator_succ]
    have hw := point_w_nat_ge (m+1)
    have hp := denominator_pos m
    nlinarith
  unfold representedNumber
  gcongr


private theorem representedNumber_gt_one (m : ℕ) : 1 < representedNumber m := by
  have hL := denominator_pos m
  unfold representedNumber
  have : 0 < (2*commonDenominator m)^4 := by positivity
  omega

private theorem loglog_bound (m : ℕ) :
    Real.log (Real.log (representedNumber m : ℝ)) < 100*((m : ℝ)+1) := by
  have hN : (1 : ℝ) < representedNumber m := by exact_mod_cast representedNumber_gt_one m
  have hu : (representedNumber m : ℝ) ≤ (71 : ℝ)^(11^(m+2)) := by
    exact_mod_cast (representedNumber_bounds m).2
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < representedNumber m) hu
  rw [Real.log_pow] at hlog
  have hll := Real.log_le_log (Real.log_pos hN) hlog
  have h71 : 0 < Real.log 71 := Real.log_pos (by norm_num)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hll
  have he : (0 : ℝ) < (11 : ℝ)^(m+2) := by positivity
  rw [Real.log_mul he.ne' h71.ne', Real.log_pow] at hll
  have h11 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
  have h71u := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 71)
  have h71l := Real.log_le_sub_one_of_pos h71
  have hm : (0 : ℝ) ≤ m := by positivity
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hll
  nlinarith

/-- A logarithm-of-a-logarithm lower bound, for infinitely many represented
numbers, for the count that is simultaneously primitive and nonadditive. -/
theorem primitive_nonadditive_loglog_growth :
    {n : ℕ | Real.log (Real.log (n : ℝ)) / 100 <
      primitiveNonadditiveCount n}.Infinite := by
  apply (Set.infinite_range_of_injective representedNumber_strictMono.injective).mono
  rintro n ⟨m, rfl⟩
  have hl : (m : ℝ)+1 ≤ primitiveNonadditiveCount (representedNumber m) := by
    exact_mod_cast primitive_nonadditive_count_lower m
  have hu := loglog_bound m
  dsimp only [Set.mem_setOf_eq]
  linarith


/-- Only a bound on the number of points explicitly supplied by this recurrence,
not an upper bound on the full representation count at these numbers. -/
theorem certified_contribution_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ m : ℕ,
      (m : ℝ)+1 ≤ C*(representedNumber m : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := Erdos322.divisor_count_subpolynomial ε hε
  refine ⟨C, hC, ?_⟩
  intro m
  have hc : (71^m).divisors.card = m+1 := by
    rw [Nat.divisors_prime_pow (by decide : Nat.Prime 71)]
    simp
  have hpow : 71^m ≤ representedNumber m := by
    calc
      71^m ≤ 71^(2^m) := Nat.pow_le_pow_right (by decide) (Nat.lt_two_pow_self.le)
      _ ≤ representedNumber m := (representedNumber_bounds m).1
  have h := hb (71^m) (by positivity)
  rw [hc] at h
  calc
    (m : ℝ)+1 ≤ C*((71^m : ℕ) : ℝ)^ε := by exact_mod_cast h
    _ ≤ C*(representedNumber m : ℝ)^ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast hpow

end Erdos322Research.PrimitiveNonadditiveGrowth
