import Submission.PrimeBlockVariance

/-!
Uniform second moments for bounded strongly additive prime scores, centered at
a dyadically chosen square-root cutoff. No cube-Sidon assertion is made.
-/
namespace Erdos1206.MovingPrimeBlockVariance
open Finset PrimeBlockVariance
open scoped Classical

lemma tail_abs_le {N T n : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ T < p) (hw : ∀ p ∈ P, |w p| ≤ 1)
    (hn : 0 < n) (hnN : n ≤ N) (hNT : N < (T+1)^2) :
    |primeSum P w n| ≤ 1 := by
  let D := P.filter (fun p => p ∣ n)
  have hcard : D.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    have hpP := (mem_filter.mp hp).1
    have hqP := (mem_filter.mp hq).1
    by_contra hpq
    have hd : p*q ∣ n := ((Nat.coprime_primes (hP p hpP).1 (hP q hqP).1).mpr hpq).mul_dvd_of_dvd_of_dvd (mem_filter.mp hp).2 (mem_filter.mp hq).2
    have hh := Nat.le_of_dvd hn hd
    have hpT := (hP p hpP).2
    have hqT := (hP q hqP).2
    have hmul : (T+1)^2 ≤ p*q := by nlinarith
    omega
  have he : primeSum P w n = ∑ p ∈ D, w p := by
    simp only [primeSum,indicator,D,sum_filter]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp
  rw [he]
  calc
    _ ≤ ∑ p ∈ D, |w p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ D, (1:ℝ) := sum_le_sum (fun p hp => hw p (mem_filter.mp hp).1)
    _ ≤ 1 := by simpa using (show (D.card:ℝ) ≤ 1 by exact_mod_cast hcard)

/-- Primes above the square-root cutoff contribute at most one to a bounded
strongly additive score at each positive integer in the prefix. -/
theorem prefix_variance_le {N T : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, |w p| ≤ 1)
    (hT : T^2 ≤ N) (hNT : N < (T+1)^2) :
    (∑ n ∈ Icc 1 N,
      (primeSum P w n - mean (P.filter (fun p => p ≤ T)) w)^2) ≤
      2*(N:ℝ)*((∑ p ∈ P, w p^2/p)+4) := by
  let S := P.filter (fun p => p ≤ T)
  let Q := P.filter (fun p => ¬ p ≤ T)
  have hS : ∀ p ∈ S, p.Prime ∧ p ≤ T := fun p hp =>
    ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  have hwS : ∀ p ∈ S, |w p| ≤ 1 := fun p hp => hw p (mem_filter.mp hp).1
  have hQ : ∀ p ∈ Q, p.Prime ∧ T < p := fun p hp =>
    ⟨hP p (mem_filter.mp hp).1,Nat.lt_of_not_ge (mem_filter.mp hp).2⟩
  have hwQ : ∀ p ∈ Q, |w p| ≤ 1 := fun p hp => hw p (mem_filter.mp hp).1
  have hsplit (n : ℕ) : primeSum P w n = primeSum S w n + primeSum Q w n := by
    exact (sum_filter_add_sum_filter_not P (fun p => p ≤ T)
      (fun p => w p*indicator p n)).symm
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (primeSum P w n-mean S w)^2 ≤ 2*(primeSum S w n-mean S w)^2+2 := by
    have hh := tail_abs_le Q w hQ hwQ (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hNT
    have hh' : (primeSum Q w n)^2 ≤ 1 := by
      simpa using (sq_le_sq₀ (abs_nonneg (primeSum Q w n)) (by norm_num : (0:ℝ) ≤ 1)).mpr hh
    rw [hsplit]
    nlinarith [sq_nonneg (primeSum S w n-mean S w-primeSum Q w n)]
  have hsum := sum_le_sum hterm
  have hvar := variance_le_of_small_primes S w hS hwS hT
  have hH : (∑ p ∈ S, w p^2/p) ≤ ∑ p ∈ P, w p^2/p :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)
  have hH' := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg N)
  simp only [sum_add_distrib,←mul_sum,sum_const,Nat.card_Icc,
    Nat.add_sub_cancel,nsmul_eq_mul] at hsum
  change _ ≤ 2*variance N S w+(N:ℝ)*2 at hsum
  dsimp only [S] at hsum
  nlinarith

noncomputable def movingMean (P : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  mean (P.filter (fun p => p ≤ 2^(Nat.log 4 n+1))) w

private lemma geometric_bound (k : ℕ) :
    (∑ j ∈ range (k+1), (4:ℕ)^(j+1)) ≤ 6*4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ,pow_succ 4 k]
    have he : 4^(k+1+1)=16*4^k := by ring
    rw [he]
    omega

/-- One uniform constant for all finite prime blocks and all prefixes.
The cutoff in the centering depends on the integer, not on the prefix. -/
theorem moving_variance_le (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, |w p| ≤ 1) :
    (∑ n ∈ Icc 1 N, (primeSum P w n-movingMean P w n)^2) ≤
      12*(N:ℝ)*((∑ p ∈ P, w p^2/p)+4) := by
  classical
  by_cases hN : N=0
  · subst N; simp
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  let L := Nat.log 4 N
  let H : ℝ := (∑ p ∈ P, w p^2/p)+4
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let f (n : ℕ) : ℝ := (primeSum P w n-movingMean P w n)^2
  have hf : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  have hmap : ∀ n ∈ Icc 1 N, Nat.log 4 n ∈ range (L+1) := by
    intro n hn
    apply mem_range.mpr
    have hh := Nat.log_mono_right (mem_Icc.mp hn).2 (b := 4)
    dsimp [L]
    omega
  have he : (∑ n ∈ Icc 1 N, f n) =
      ∑ j ∈ range (L+1), ∑ n ∈ (Icc 1 N).filter (fun n => Nat.log 4 n=j), f n := by
    exact (sum_fiberwise_of_maps_to hmap f).symm
  have hblock (j : ℕ) :
      (∑ n ∈ (Icc 1 N).filter (fun n => Nat.log 4 n=j), f n) ≤
        2*(4^(j+1):ℕ)*H := by
    have hpow : (2^(j+1))^2=(4:ℕ)^(j+1) := by rw [←pow_mul, mul_comm (j+1) 2, pow_mul]; norm_num
    have hpre := prefix_variance_le (N := 4^(j+1)) (T := 2^(j+1)) P w hP hw
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
  change (∑ n ∈ Icc 1 N, f n) ≤ 12*(N:ℝ)*H
  rw [he]
  calc
    _ ≤ ∑ j ∈ range (L+1), 2*(4^(j+1):ℕ)*H := sum_le_sum (fun j _ => hblock j)
    _ = 2*H*(∑ j ∈ range (L+1), (4^(j+1):ℕ)) := by
      rw [Nat.cast_sum,mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ 2*H*(6*(4^L:ℕ)) := by
      gcongr
      exact_mod_cast geometric_bound L
    _ ≤ 12*(N:ℝ)*H := by
      have hpow : 4^L ≤ N := Nat.pow_log_le_self 4 hN
      have hpowR : ((4^L:ℕ):ℝ) ≤ N := by exact_mod_cast hpow
      nlinarith

#print axioms tail_abs_le
#print axioms prefix_variance_le
#print axioms moving_variance_le
end Erdos1206.MovingPrimeBlockVariance
