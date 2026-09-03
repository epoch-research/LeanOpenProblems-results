import Submission.PrimeBlockCenteredHighMoments

/-!
Uniform high-moment estimates for signed prime-divisor scores with bounded
weights. This analytic input does not assert separation of cubic collisions.
-/
namespace Erdos1206.UniformPrimeBlockHighMoments
open Finset Filter PrimeBlockVariance SharpPrimeBlockVariance SmallPrimeBlockMoments
open PrimeBlockCenteredHighMoments PrimeBlockMeanOscillation MovingPrimeBlockVariance
open scoped Classical

lemma primeSum_abs_le_card (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p∈P,|w p| ≤ 1) (n : ℕ) : |primeSum P w n| ≤ P.card := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _p∈P,(1:ℝ) := by
      apply sum_le_sum
      intro p hp
      by_cases hd : p∣n <;> simp only [indicator,hd,if_true,if_false,mul_one,mul_zero,abs_zero]
      · exact hw p hp
      · norm_num
    _ = _ := by simp

lemma mean_abs_le_card (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p∈P,|w p| ≤ 1) : |mean P w| ≤ P.card := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _p∈P,(1:ℝ) := by
      apply sum_le_sum
      intro p hp
      rw [abs_div,show |(p:ℝ)|=(p:ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
      apply (div_le_one (by exact_mod_cast (hP p hp).pos)).mpr
      exact (hw p hp).trans (by exact_mod_cast (hP p hp).one_lt.le)
    _ = _ := by simp

lemma prefix_card_le (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (H : ℕ) :
    (P.filter (fun p => p ≤ H)).card ≤ H := by
  have hs : P.filter (fun p => p ≤ H) ⊆ Icc 1 H := fun p hp =>
    mem_Icc.mpr ⟨(hP p (mem_filter.mp hp).1).pos,(mem_filter.mp hp).2⟩
  simpa using card_le_card hs

lemma power_window_center_bound {D : ℝ} (hD : 0 ≤ D) {H U r : ℕ}
    (hU : U ≤ H^r) (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1)
    (hmass : ∀ Q : Finset ℕ,(∀ p∈Q,p.Prime ∧ H < p ∧ p ≤ H^r) →
      (∑ p∈Q,(1:ℝ)/p) ≤ D*r) :
    |mean (P.filter (fun p => p ≤ U)) w| ≤ H+D*r := by
  rcases le_total H U with hHU | hUH
  · have hhead := mean_abs_le_card (P.filter (fun p => p ≤ H))
      (fun p hp => hP p (mem_filter.mp hp).1) w
      (fun p hp => hw p (mem_filter.mp hp).1)
    have hcard : ((P.filter (fun p => p ≤ H)).card:ℝ) ≤ H := by
      exact_mod_cast prefix_card_le P hP H
    have hdiff := prefix_mean_difference_abs P w hw hHU
    have htail := hmass (P.filter (fun p => H < p ∧ p ≤ U)) (fun p hp =>
      ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2.1,((mem_filter.mp hp).2.2).trans hU⟩)
    have hh := abs_add_le
      (mean (P.filter (fun p => p ≤ U)) w-mean (P.filter (fun p => p ≤ H)) w)
      (mean (P.filter (fun p => p ≤ H)) w)
    rw [sub_add_cancel] at hh
    linarith
  · have hh := mean_abs_le_card (P.filter (fun p => p ≤ U))
      (fun p hp => hP p (mem_filter.mp hp).1) w
      (fun p hp => hw p (mem_filter.mp hp).1)
    have hc : ((P.filter (fun p => p ≤ U)).card:ℝ) ≤ H := by
      exact_mod_cast (prefix_card_le P hP U).trans hUH
    have hDr : 0 ≤ D*r := mul_nonneg hD (Nat.cast_nonneg r)
    linarith

/-- One constant controls every even moment in every prefix, centered at
that prefix's dyadic square-root cutoff. -/
theorem exists_prefix_moment_constant :
    ∃ C : ℝ,0 < C ∧ ∀ (P : Finset ℕ) (w : ℕ → ℝ),
      (∀ p∈P,p.Prime) → (∀ p∈P,|w p| ≤ 1) →
      ∀ k : ℕ,0 < k → ∀ N : ℕ,
        (∑ n∈Icc 1 N,(primeSum P w n-mean (P.filter (fun p => p ≤ cutoff N)) w)^(2*k)) ≤
          (N:ℝ)*(C*(k:ℝ)*(mass P w+k))^k := by
  obtain ⟨D,hD,H₀,hwindow⟩ := PrimePowerWindowMass.eventually_window_mass
  let H := max H₀ 2
  have hH : 2 ≤ H := le_max_right _ _
  have hwin (U : ℕ) (hU : H ≤ U) := hwindow U ((le_max_left _ _).trans hU)
  let C₁ : ℝ := 16*max 12 ((4*D+2)^2)
  let C₂ : ℝ := (2*(H:ℝ)+2+2*D)^2
  let C : ℝ := max C₁ C₂
  have hC₁ : 0 < C₁ := by
    dsimp only [C₁]
    exact mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  refine ⟨C,hC,fun P w hP hw k hk N => ?_⟩
  by_cases hN : N=0
  · subst N; simp
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm := mass_nonneg P w
  obtain ⟨T,hTN,hNT⟩ := integer_root_cutoff (show 0 < 2*k by omega) N
  let U := cutoff N
  have hUN : U^2 ≤ 4*N := cutoff_upper hN0
  have hNU : N < U^2 := cutoff_lower N
  by_cases hHT : H ≤ T
  · have hT2 : 2 ≤ T := hH.trans hHT
    have hT0 : 0 < T := by omega
    have hTU : T ≤ U := by
      have hp : T^2 ≤ T^(2*k) := Nat.pow_le_pow_right hT0 (by omega)
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      omega
    have hnext : T+1 ≤ T^2 := by nlinarith
    have hNTpow : N ≤ T^(4*k) := by
      calc
        _ ≤ (T+1)^(2*k) := hNT.le
        _ ≤ (T^2)^(2*k) := Nat.pow_le_pow_left hnext _
        _ = _ := by rw [←pow_mul]; congr 1; omega
    have hfour : 4 ≤ T^(4*k) := by
      have ht : 4 ≤ T^2 := by nlinarith
      exact ht.trans (Nat.pow_le_pow_right hT0 (by omega))
    have hUpow : U ≤ T^(4*k) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      calc
        U^2 ≤ 4*N := hUN
        _ ≤ 4*T^(4*k) := Nat.mul_le_mul_left _ hNTpow
        _ ≤ T^(4*k)*T^(4*k) := Nat.mul_le_mul_right _ hfour
        _ = _ := by ring
    have hc := prefix_mean_difference_abs P w hw hTU
    have hwM := hwin T hHT (4*k) (by omega)
      (P.filter (fun p => T < p ∧ p ≤ U)) (fun p hp =>
        ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2.1,((mem_filter.mp hp).2.2).trans hUpow⟩)
    have hcenter : |mean (P.filter (fun p => p ≤ T)) w-
        mean (P.filter (fun p => p ≤ U)) w| ≤ (4*D)*k := by
      rw [abs_sub_comm]
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hwM
      linarith
    have hh := prefix_moment_of_center_comparison P hP w hw hk hTN hNT
      (by positivity : 0 ≤ 4*D) hcenter
    apply hh.trans
    dsimp only [C₁,C,U] at ⊢
    gcongr
    exact le_max_left _ _
  · have hTH : T+1 ≤ H := by omega
    have hNH : N < H^(2*k) := hNT.trans_le (Nat.pow_le_pow_left hTH _)
    have hH0 : 0 < H := by omega
    have hfour : 4 ≤ H^(2*k) := by
      have hh : 4 ≤ H^2 := by nlinarith
      exact hh.trans (Nat.pow_le_pow_right hH0 (by omega))
    have hUpow : U ≤ H^(2*k) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      calc
        U^2 ≤ 4*N := hUN
        _ ≤ 4*H^(2*k) := Nat.mul_le_mul_left _ hNH.le
        _ ≤ H^(2*k)*H^(2*k) := Nat.mul_le_mul_right _ hfour
        _ = _ := by ring
    have hc := power_window_center_bound hD.le hUpow P hP w hw (hwin H le_rfl (2*k) (by omega))
    let S := P.filter (fun p => p ≤ H)
    let Q := P.filter (fun p => ¬p ≤ H)
    have hhead (n : ℕ) : |primeSum S w n| ≤ H := by
      have hh := primeSum_abs_le_card S w (fun p hp => hw p (mem_filter.mp hp).1) n
      have hh' : (S.card:ℝ) ≤ H := by exact_mod_cast prefix_card_le P hP H
      exact hh.trans hh'
    have htail (n : ℕ) (hn : n∈Icc 1 N) : |primeSum Q w n| ≤ (2*k:ℕ) := by
      apply SmallPrimeBlockMoments.tail_abs_le Q w (T := H) (r := 2*k) (N := N)
        (fun p hp => ⟨hP p (mem_filter.mp hp).1,by have := (mem_filter.mp hp).2; omega⟩)
        (fun p hp => hw p (mem_filter.mp hp).1) (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
      exact hNH.trans_le (Nat.pow_le_pow_left (Nat.le_succ H) _)
    have hpoint (n : ℕ) (hn : n∈Icc 1 N) :
        (primeSum P w n-mean (P.filter (fun p => p ≤ U)) w)^(2*k) ≤
          (C*(k:ℝ)*(mass P w+k))^k := by
      have hs : primeSum P w n=primeSum S w n+primeSum Q w n :=
        (sum_filter_add_sum_filter_not P (fun p => p ≤ H) (fun p => w p*indicator p n)).symm
      have hab := abs_sub (primeSum P w n) (mean (P.filter (fun p => p ≤ U)) w)
      have has := abs_add_le (primeSum S w n) (primeSum Q w n)
      have ht := htail n hn
      rw [hs] at hab
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hc ht
      have hbound : |primeSum P w n-mean (P.filter (fun p => p ≤ U)) w| ≤
          (2*(H:ℝ)+2+2*D)*k := by
        rw [hs]
        have hHmul := mul_le_mul_of_nonneg_left hkR (show 0 ≤ 2*(H:ℝ) by positivity)
        nlinarith [hhead n]
      rw [←(even_two_mul k).pow_abs]
      apply (pow_le_pow_left₀ (abs_nonneg _) hbound (2*k)).trans
      rw [pow_mul]
      apply pow_le_pow_left₀ (sq_nonneg _)
      have hC₂ : C₂ ≤ C := le_max_right _ _
      have hkk : (k:ℝ)^2 ≤ (k:ℝ)*(mass P w+k) := by nlinarith
      calc
        _ = C₂*(k:ℝ)^2 := mul_pow _ _ _
        _ ≤ C*((k:ℝ)*(mass P w+k)) := mul_le_mul hC₂ hkk (sq_nonneg _) hC.le
        _ = _ := by ring
    have hh := sum_le_sum hpoint
    simpa only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,U] using hh

private lemma geometric_bound (j : ℕ) :
    (∑ i∈range (j+1),(4:ℕ)^(i+1)) ≤ 6*4^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [sum_range_succ,pow_succ 4 j]
    have he : (4:ℕ)^(j+1+1)=16*4^j := by ring
    rw [he]
    omega

/-- Uniform high moments about the integer-dependent moving center. The
constant is independent of the prime block, weights, moment order and prefix. -/
theorem exists_moving_moment_constant :
    ∃ C : ℝ,0 < C ∧ ∀ (P : Finset ℕ) (w : ℕ → ℝ),
      (∀ p∈P,p.Prime) → (∀ p∈P,|w p| ≤ 1) →
      ∀ k : ℕ,0 < k → ∀ N : ℕ,
        (∑ n∈Icc 1 N,(primeSum P w n-movingMean P w n)^(2*k)) ≤
          (N:ℝ)*(C*(k:ℝ)*(mass P w+k))^k := by
  obtain ⟨C,hC,hpre⟩ := exists_prefix_moment_constant
  refine ⟨6*C,by positivity,fun P w hP hw k hk N => ?_⟩
  by_cases hN : N=0
  · subst N; simp
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  let L := Nat.log 4 N
  let A : ℝ := (C*(k:ℝ)*(mass P w+k))^k
  have hM := mass_nonneg P w
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let f : ℕ → ℝ := fun n => (primeSum P w n-movingMean P w n)^(2*k)
  have hf : ∀ n,0 ≤ f n := fun n => (even_two_mul k).pow_nonneg _
  have hmap : ∀ n∈Icc 1 N,Nat.log 4 n∈range (L+1) := by
    intro n hn
    apply mem_range.mpr
    have hh := Nat.log_mono_right (mem_Icc.mp hn).2 (b := 4)
    dsimp only [L]
    omega
  have hsum : (∑ n∈Icc 1 N,f n)=
      ∑ j∈range (L+1),∑ n∈(Icc 1 N).filter (fun n => Nat.log 4 n=j),f n :=
    (sum_fiberwise_of_maps_to hmap f).symm
  have hblock (j : ℕ) :
      (∑ n∈(Icc 1 N).filter (fun n => Nat.log 4 n=j),f n) ≤ (4^(j+1):ℕ)*A := by
    let V := 4^(j+1)-1
    have hjp : 0 < (4:ℕ)^j := pow_pos (by norm_num) _
    have hVlo : 4^j ≤ V := by dsimp [V]; rw [pow_succ]; omega
    have hVhi : V < 4^(j+1) := by dsimp [V]; rw [pow_succ]; omega
    have hVlog : Nat.log 4 V=j := Nat.log_eq_of_pow_le_of_lt_pow hVlo hVhi
    have hcent : cutoff V=2^(j+1) := by simp only [cutoff,hVlog]
    have hh := hpre P w hP hw k hk V
    rw [hcent] at hh
    have hsub : (Icc 1 N).filter (fun n => Nat.log 4 n=j) ⊆ Icc 1 V := by
      intro n hn
      have hl := (mem_filter.mp hn).2
      have hu := Nat.lt_pow_succ_log_self (by decide : 1 < (4:ℕ)) n
      rw [hl] at hu
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1,by dsimp [V]; omega⟩
    calc
      _ = ∑ n∈(Icc 1 N).filter (fun n => Nat.log 4 n=j),
          (primeSum P w n-mean (P.filter (fun p => p ≤ 2^(j+1))) w)^(2*k) := by
        apply sum_congr rfl
        intro n hn
        simp only [f,movingMean,(mem_filter.mp hn).2]
      _ ≤ ∑ n∈Icc 1 V,(primeSum P w n-mean (P.filter (fun p => p ≤ 2^(j+1))) w)^(2*k) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (even_two_mul k).pow_nonneg _)
      _ ≤ (V:ℝ)*A := hh
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hVhi.le) hA
  have hgeom : (∑ j∈range (L+1),(4^(j+1):ℕ)) ≤ 6*(N:ℝ) := by
    have hh := geometric_bound L
    have hlog : 4^L ≤ N := Nat.pow_log_le_self 4 hN
    exact_mod_cast hh.trans (Nat.mul_le_mul_left 6 hlog)
  have hfinal : (∑ n∈Icc 1 N,f n) ≤ 6*(N:ℝ)*A := by
    rw [hsum]
    calc
      _ ≤ ∑ j∈range (L+1),(4^(j+1):ℕ)*A := sum_le_sum (fun j _ => hblock j)
      _ = (∑ j∈range (L+1),(4^(j+1):ℕ))*A := by rw [Nat.cast_sum,←sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeom hA
  have h6 : (6:ℝ) ≤ (6:ℝ)^k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 6) (show 1 ≤ k from hk)
  apply hfinal.trans
  calc
    _ = (N:ℝ)*6*A := by ring
    _ ≤ (N:ℝ)*(6:ℝ)^k*A := by gcongr
    _ = _ := by
      dsimp only [A]
      rw [mul_assoc,←mul_pow]
      congr 2
      ring


#print axioms power_window_center_bound
#print axioms exists_prefix_moment_constant
#print axioms exists_moving_moment_constant
end Erdos1206.UniformPrimeBlockHighMoments
