import Submission.MovingPrimeBlockVariance

/-!
A sharper elementary prime-score second moment: the entire bound is proportional
to the reciprocal-prime energy, with no additive constant. Weights may be arbitrary
real numbers. This file makes no cube-Sidon assertion.
-/
namespace Erdos1206.SharpPrimeBlockVariance
open Finset PrimeBlockVariance MovingPrimeBlockVariance
open scoped Classical

noncomputable def mass (P : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ p ∈ P, w p^2/p

lemma mass_nonneg (P : Finset ℕ) (w : ℕ → ℝ) : 0 ≤ mass P w := by
  dsimp [mass]
  positivity

lemma covariance_weighted (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    variance N P w ≤ (N:ℝ)*mass P w+3*(∑ p ∈ P, |w p|)^2 := by
  rw [variance_expand]
  have hterm (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      w p*w q*covariance N p q ≤
        (if p=q then (N:ℝ)*w p^2/p else 0)+3* |w p| * |w q| := by
    by_cases he : p=q
    · subst q
      rw [if_pos rfl]
      have hh := mul_le_mul_of_nonneg_left (covariance_self_le (hP p hp).two_le N)
        (sq_nonneg (w p))
      calc
        _ = w p^2*covariance N p p := by ring
        _ ≤ w p^2*((N:ℝ)/p) := hh
        _ = (N:ℝ)*w p^2/p := by ring
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg he,zero_add]
      have hc := covariance_abs_le (hP p hp).pos (hP q hq).pos
        ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr he) N
      calc
        _ ≤ |w p*w q*covariance N p q| := le_abs_self _
        _ = (|w p| * |w q|)* |covariance N p q| := by rw [abs_mul,abs_mul]
        _ ≤ (|w p| * |w q|)*3 := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ((if p=q then (N:ℝ)*w p^2/p else 0)+3* |w p| * |w q|) :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq => hterm p hp q hq))
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum]
      have he (p : ℕ) (hp : p ∈ P) :
          (∑ q ∈ P, if p=q then (N:ℝ)*w p^2/p else 0)=(N:ℝ)*w p^2/p := by simp [hp]
      simp only [sum_congr rfl he]
      simp only [mass,mul_sum,pow_two]
      ring_nf
      congr 1
      apply sum_congr rfl
      intro p hp
      rw [←sum_mul,←mul_sum]
      ring

lemma weighted_cauchy (P : Finset ℕ) (w : ℕ → ℝ) (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, |w p|)^2 ≤ mass P w*(∑ p ∈ P, (p:ℝ)) := by
  have hh := sum_mul_sq_le_sq_mul_sq P
    (fun p => |w p|/Real.sqrt (p:ℝ)) (fun p => Real.sqrt (p:ℝ))
  have hmul (p : ℕ) (hp : p ∈ P) : |w p|/Real.sqrt (p:ℝ)*Real.sqrt (p:ℝ)=|w p| := by
    exact div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hP p hp))
  have hsq (p : ℕ) (hp : p ∈ P) : (|w p|/Real.sqrt (p:ℝ))^2=w p^2/p := by
    rw [div_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg p)]
  simp only [sum_congr rfl hmul,sum_congr rfl hsq,Real.sq_sqrt (Nat.cast_nonneg _)] at hh
  exact hh

/-- No bound on the individual weights is needed. -/
theorem small_variance_le {N T : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ T) (hT : T^2 ≤ N) :
    variance N P w ≤ 4*(N:ℝ)*mass P w := by
  have hsub : P ⊆ Icc 1 T := fun p hp => mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2⟩
  have hcard : P.card ≤ T := by simpa using card_le_card hsub
  have hsum : (∑ p ∈ P, (p:ℝ)) ≤ (T:ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ P, (T:ℝ) := sum_le_sum (fun p hp => by exact_mod_cast (hP p hp).2)
      _ = (P.card:ℝ)*T := by simp
      _ ≤ (T:ℝ)*T := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  have hTR : (T:ℝ)^2 ≤ N := by exact_mod_cast hT
  have hcs := weighted_cauchy P w (fun p hp => (hP p hp).1.pos)
  have hm := mul_le_mul_of_nonneg_left (hsum.trans hTR) (mass_nonneg P w)
  have hh := covariance_weighted N P w (fun p hp => (hP p hp).1)
  nlinarith

/-- Above the square-root cutoff, distinct prime indicators have zero
cross terms on the prefix, so their total second moment is also small. -/
lemma tail_second_moment {N T : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ T < p) (hNT : N < (T+1)^2) :
    (∑ n ∈ Icc 1 N, (primeSum P w n)^2) ≤ (N:ℝ)*mass P w := by
  have hcross (n : ℕ) (hn : n ∈ Icc 1 N) (p : ℕ) (hp : p ∈ P)
      (q : ℕ) (hq : q ∈ P) (hpq : p ≠ q) :
      indicator p n*indicator q n=0 := by
    have hnot : ¬ (p ∣ n ∧ q ∣ n) := by
      rintro ⟨hpn,hqn⟩
      have hd := ((Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn
      have hle := Nat.le_of_dvd (mem_Icc.mp hn).1 hd
      have h₁ := (hP p hp).2
      have h₂ := (hP q hq).2
      have hmul : (T+1)^2 ≤ p*q := by nlinarith
      have hnN := (mem_Icc.mp hn).2
      omega
    dsimp [indicator]
    split_ifs <;> simp_all
  have hsquare (n : ℕ) (hn : n ∈ Icc 1 N) :
      (primeSum P w n)^2=∑ p ∈ P, w p^2*indicator p n := by
    simp only [primeSum,pow_two,sum_mul_sum]
    apply sum_congr rfl
    intro p hp
    have hterm (q : ℕ) (hq : q ∈ P) :
        w p*indicator p n*(w q*indicator q n)=if p=q then w p*w p*indicator p n else 0 := by
      by_cases he : p=q
      · subst q
        simp only [indicator]
        split_ifs <;> ring
      · rw [if_neg he]
        calc
          _ = w p*w q*(indicator p n*indicator q n) := by ring
          _ = 0 := by rw [hcross n hn p hp q hq he,mul_zero]
    rw [sum_congr rfl hterm]
    simp [hp]
  rw [sum_congr rfl hsquare,sum_comm]
  simp only [mass,mul_sum]
  apply sum_le_sum
  intro p hp
  rw [←mul_sum,sum_indicator]
  calc
    _ ≤ w p^2*((N:ℝ)/p) := mul_le_mul_of_nonneg_left Nat.cast_div_le (sq_nonneg _)
    _ = (N:ℝ)*(w p^2/p) := by ring

/-- A square-root split costs only a constant times the actual energy. -/
theorem prefix_variance_le {N T : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hT : T^2 ≤ N) (hNT : N < (T+1)^2) :
    (∑ n ∈ Icc 1 N, (primeSum P w n-mean (P.filter (fun p => p ≤ T)) w)^2) ≤
      8*(N:ℝ)*mass P w := by
  let S := P.filter (fun p => p ≤ T)
  let Q := P.filter (fun p => ¬ p ≤ T)
  have hS : ∀ p ∈ S, p.Prime ∧ p ≤ T := fun p hp =>
    ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  have hQ : ∀ p ∈ Q, p.Prime ∧ T < p := fun p hp =>
    ⟨hP p (mem_filter.mp hp).1,Nat.lt_of_not_ge (mem_filter.mp hp).2⟩
  have hsplit (n : ℕ) : primeSum P w n=primeSum S w n+primeSum Q w n :=
    (sum_filter_add_sum_filter_not P (fun p => p ≤ T) (fun p => w p*indicator p n)).symm
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (primeSum P w n-mean S w)^2 ≤
        2*(primeSum S w n-mean S w)^2+2*(primeSum Q w n)^2 := by
    rw [hsplit]
    nlinarith [sq_nonneg (primeSum S w n-mean S w-primeSum Q w n)]
  have hsum := sum_le_sum hterm
  have hsmall := small_variance_le S w hS hT
  have hlarge := tail_second_moment Q w hQ hNT
  have hmass : mass P w=mass S w+mass Q w :=
    (sum_filter_add_sum_filter_not P (fun p => p ≤ T) (fun p => w p^2/p)).symm
  simp only [sum_add_distrib,←mul_sum] at hsum
  change _ ≤ 2*variance N S w+2*∑ n ∈ Icc 1 N, (primeSum Q w n)^2 at hsum
  dsimp only [S] at hsum
  have hnon := mul_nonneg (Nat.cast_nonneg N) (mass_nonneg Q w)
  rw [hmass]
  nlinarith

private lemma geometric_bound (k : ℕ) :
    (∑ j ∈ range (k+1), (4:ℕ)^(j+1)) ≤ 6*4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ,pow_succ 4 k]
    have he : 4^(k+1+1)=16*4^k := by ring
    rw [he]
    omega

/-- Prefix-uniform, with arbitrary real weights and no additive error. -/
theorem moving_variance_le (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ Icc 1 N, (primeSum P w n-movingMean P w n)^2) ≤
      48*(N:ℝ)*mass P w := by
  classical
  by_cases hN : N=0
  · subst N; simp
  let L := Nat.log 4 N
  let H := mass P w
  have hH : 0 ≤ H := mass_nonneg P w
  let f (n : ℕ) : ℝ := (primeSum P w n-movingMean P w n)^2
  have hmap : ∀ n ∈ Icc 1 N, Nat.log 4 n ∈ range (L+1) := by
    intro n hn
    apply mem_range.mpr
    have hh := Nat.log_mono_right (mem_Icc.mp hn).2 (b := 4)
    dsimp [L]
    omega
  have he : (∑ n ∈ Icc 1 N, f n)=
      ∑ j ∈ range (L+1), ∑ n ∈ (Icc 1 N).filter (fun n => Nat.log 4 n=j), f n :=
    (sum_fiberwise_of_maps_to hmap f).symm
  have hblock (j : ℕ) :
      (∑ n ∈ (Icc 1 N).filter (fun n => Nat.log 4 n=j), f n) ≤
        8*(4^(j+1):ℕ)*H := by
    have hpow : (2^(j+1))^2=(4:ℕ)^(j+1) := by rw [←pow_mul,mul_comm (j+1) 2,pow_mul]; norm_num
    have hpre := prefix_variance_le (N := 4^(j+1)) (T := 2^(j+1)) P w hP
      hpow.le (by nlinarith [pow_pos (by decide : 0 < (2:ℕ)) (j+1)])
    have hsub : (Icc 1 N).filter (fun n => Nat.log 4 n=j) ⊆ Icc 1 (4^(j+1)) := by
      intro n hn
      obtain ⟨hn,hlog⟩ := mem_filter.mp hn
      have hh := Nat.lt_pow_succ_log_self (by decide : 1 < (4:ℕ)) n
      rw [hlog] at hh
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,hh.le⟩
    calc
      _ = ∑ n ∈ (Icc 1 N).filter (fun n => Nat.log 4 n=j),
          (primeSum P w n-mean (P.filter (fun p => p ≤ 2^(j+1))) w)^2 := by
        apply sum_congr rfl
        intro n hn
        simp only [f,movingMean,(mem_filter.mp hn).2]
      _ ≤ ∑ n ∈ Icc 1 (4^(j+1)),
          (primeSum P w n-mean (P.filter (fun p => p ≤ 2^(j+1))) w)^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hpre
  change (∑ n ∈ Icc 1 N, f n) ≤ 48*(N:ℝ)*H
  rw [he]
  calc
    _ ≤ ∑ j ∈ range (L+1), 8*(4^(j+1):ℕ)*H := sum_le_sum (fun j _ => hblock j)
    _ = 8*H*(∑ j ∈ range (L+1), (4^(j+1):ℕ)) := by
      rw [Nat.cast_sum,mul_sum]
      apply sum_congr rfl
      intros
      ring
    _ ≤ 8*H*(6*(4^L:ℕ)) := by
      gcongr
      exact_mod_cast geometric_bound L
    _ ≤ 48*(N:ℝ)*H := by
      have hpow : 4^L ≤ N := Nat.pow_log_le_self 4 hN
      have hpowR : ((4^L:ℕ):ℝ) ≤ N := by exact_mod_cast hpow
      nlinarith

#print axioms weighted_cauchy
#print axioms small_variance_le
#print axioms tail_second_moment
#print axioms moving_variance_le
end Erdos1206.SharpPrimeBlockVariance
