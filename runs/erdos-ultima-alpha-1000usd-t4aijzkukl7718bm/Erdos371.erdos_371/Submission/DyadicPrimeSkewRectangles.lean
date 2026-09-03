import Submission.PrimeSkewEndpointPerturbation

/-! A dyadic cofactor grid for the upper-half prime-band skew. It has
O(2^k log A) blocks and gives a total normalized approximation error at
most 2^(-k)+2/N. The remaining rectangular prime sums are not estimated. -/
namespace Erdos371
open Finset

def dyadicCofactorStep (k b : ℕ) : ℕ := 2^(Nat.log 2 b-k)
def dyadicCofactorRound (k b : ℕ) : ℕ := (b/dyadicCofactorStep k b)*dyadicCofactorStep k b

lemma dyadicCofactorStep_pos (k b : ℕ) : 0 < dyadicCofactorStep k b := by
  unfold dyadicCofactorStep
  positivity

lemma dyadicCofactorStep_le (k b : ℕ) (hb : 0 < b) : dyadicCofactorStep k b ≤ b := by
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.sub_le _ _)).trans
    (Nat.pow_log_le_self 2 hb.ne')

lemma dyadicCofactorRound_bounds (k b : ℕ) (hb : 0 < b) :
    0 < dyadicCofactorRound k b ∧ dyadicCofactorRound k b ≤ b := by
  have hh := dyadicCofactorStep_pos k b
  constructor
  · exact Nat.mul_pos (Nat.div_pos (dyadicCofactorStep_le k b hb) hh) hh
  · simpa only [dyadicCofactorRound,mul_comm] using Nat.mul_div_le b (dyadicCofactorStep k b)

lemma dyadicCofactorRound_eq_self (k b : ℕ) (hb : Nat.log 2 b ≤ k) :
    dyadicCofactorRound k b=b := by
  simp [dyadicCofactorRound,dyadicCofactorStep,Nat.sub_eq_zero_of_le hb]

lemma dyadicCofactorRound_log_lower (k b : ℕ) (hb : 0 < b) :
    2^(Nat.log 2 b) ≤ dyadicCofactorRound k b := by
  by_cases hj : Nat.log 2 b ≤ k
  · rw [dyadicCofactorRound_eq_self k b hj]
    exact Nat.pow_log_le_self 2 hb.ne'
  · have hj' : k ≤ Nat.log 2 b := by omega
    have hp : 2^k*dyadicCofactorStep k b=2^(Nat.log 2 b) := by
      rw [dyadicCofactorStep,← pow_add,Nat.add_sub_of_le hj']
    have hdiv : 2^k ≤ b/dyadicCofactorStep k b := by
      apply (Nat.le_div_iff_mul_le (dyadicCofactorStep_pos k b)).mpr
      rw [hp]
      exact Nat.pow_log_le_self 2 hb.ne'
    rw [← hp]
    exact Nat.mul_le_mul_right _ hdiv

/-- The rounding loses at most a 2^(-k) relative amount. -/
theorem dyadicCofactorRound_relative (k b : ℕ) :
    2^k*b ≤ (2^k+1)*dyadicCofactorRound k b := by
  by_cases hb : b=0
  · simp [hb,dyadicCofactorRound]
  by_cases hj : Nat.log 2 b ≤ k
  · rw [dyadicCofactorRound_eq_self k b hj]
    nlinarith
  · have hj' : k ≤ Nat.log 2 b := by omega
    have hp : 2^k*dyadicCofactorStep k b=2^(Nat.log 2 b) := by
      rw [dyadicCofactorStep,← pow_add,Nat.add_sub_of_le hj']
    have hlow : 2^k*dyadicCofactorStep k b ≤ dyadicCofactorRound k b := by
      rw [hp]
      exact dyadicCofactorRound_log_lower k b (by omega)
    have hrem := Nat.mod_lt b (dyadicCofactorStep_pos k b)
    have he : dyadicCofactorRound k b+b%dyadicCofactorStep k b=b := by
      simpa only [dyadicCofactorRound,mul_comm] using Nat.div_add_mod b (dyadicCofactorStep k b)
    have hm := (Nat.mul_le_mul_left (2^k) hrem.le).trans hlow
    nlinarith

lemma dyadicCofactorRound_quotient_lt (k b : ℕ) :
    b/dyadicCofactorStep k b < 2^(k+1) := by
  apply (Nat.div_lt_iff_lt_mul (dyadicCofactorStep_pos k b)).mpr
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
  have he : Nat.log 2 b+1 ≤ (k+1)+(Nat.log 2 b-k) := by omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  exact h.trans_le (by simpa only [dyadicCofactorStep,pow_add] using hpow)

def dyadicCofactorGrid (k A : ℕ) : Finset ℕ :=
  ((range (Nat.log 2 A+1)) ×ˢ (range (2^(k+1)))).image fun z => z.2*2^z.1

lemma dyadicCofactorRound_mem_grid (k A b : ℕ) (hb : b ≤ A) :
    dyadicCofactorRound k b ∈ dyadicCofactorGrid k A := by
  apply mem_image.mpr
  refine ⟨(Nat.log 2 b-k,b/dyadicCofactorStep k b),?_,rfl⟩
  apply mem_product.mpr
  constructor
  · apply mem_range.mpr
    have := Nat.log_mono_right (b := 2) hb
    omega
  · exact mem_range.mpr (dyadicCofactorRound_quotient_lt k b)

/-- Only logarithmically many cofactor blocks occur for fixed k. -/
theorem dyadicCofactorRound_image_card (k A : ℕ) :
    ((Icc 1 A).image (dyadicCofactorRound k)).card ≤ (Nat.log 2 A+1)*2^(k+1) := by
  have hs : (Icc 1 A).image (dyadicCofactorRound k) ⊆ dyadicCofactorGrid k A := by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hd
    exact dyadicCofactorRound_mem_grid k A b (mem_Icc.mp hb).2
  exact (card_le_card hs).trans (by
    simpa only [dyadicCofactorGrid,card_product,card_range] using
      (card_image_le (s := (range (Nat.log 2 A+1)) ×ˢ (range (2^(k+1))))
        (f := fun z : ℕ × ℕ => z.2*2^z.1)))

lemma dyadicCofactorRound_mono (k : ℕ) : Monotone (dyadicCofactorRound k) := by
  intro b c hbc
  by_cases hb : b=0
  · simp [hb,dyadicCofactorRound]
  have hc : 0 < c := by omega
  by_cases he : Nat.log 2 b=Nat.log 2 c
  · have hstep : dyadicCofactorStep k b=dyadicCofactorStep k c := by simp only [dyadicCofactorStep,he]
    unfold dyadicCofactorRound
    rw [hstep]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hbc)
  · have hl : Nat.log 2 b+1 ≤ Nat.log 2 c := by
      have := Nat.log_mono_right (b := 2) hbc
      omega
    calc
      dyadicCofactorRound k b ≤ b := (dyadicCofactorRound_bounds k b (by omega)).2
      _ ≤ 2^(Nat.log 2 c) :=
        (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b).le.trans
          (Nat.pow_le_pow_right (by norm_num) hl)
      _ ≤ dyadicCofactorRound k c := dyadicCofactorRound_log_lower k c hc

/-- Consequently every cofactor fiber is an interval, possibly truncated
by the ambient cofactor range. -/
lemma dyadicCofactorRound_fiber_interval (k a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (he : dyadicCofactorRound k a=dyadicCofactorRound k c) :
    dyadicCofactorRound k b=dyadicCofactorRound k a := by
  have h1 := dyadicCofactorRound_mono k hab
  have h2 := dyadicCofactorRound_mono k hbc
  omega

lemma dyadicCofactorRound_cross (k N b : ℕ) :
    b*N ≤ (N+N/2^k+1)*dyadicCofactorRound k b := by
  have hK : 0 < 2^k := by positivity
  have hN : N ≤ 2^k*(N/2^k+1) := by
    have := Nat.div_add_mod N (2^k)
    have := Nat.mod_lt N hK
    nlinarith
  apply Nat.le_of_mul_le_mul_right (c := 2^k) _ hK
  calc
    b*N*2^k = (2^k*b)*N := by ring
    _ ≤ ((2^k+1)*dyadicCofactorRound k b)*N :=
      Nat.mul_le_mul_right N (dyadicCofactorRound_relative k b)
    _ = N*dyadicCofactorRound k b*2^k+N*dyadicCofactorRound k b := by ring
    _ ≤ N*dyadicCofactorRound k b*2^k+(2^k*(N/2^k+1))*dyadicCofactorRound k b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hN) _
    _ = (N+N/2^k+1)*dyadicCofactorRound k b*2^k := by ring

/-- Explicit natural-scale rectangularization of the smooth-cutoff skew.
The square-root condition includes the small enlarged boundary interval. -/
theorem smoothCutoffSkew_dyadic_rounding_bound (B C N k : ℕ)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hsize : N+N/2^k+2 ≤ B^2) :
    |smoothCutoffSkew B C N -
      roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N (dyadicCofactorRound k)| ≤ (N/2^k : ℕ)+2 := by
  have h := smoothCutoffSkew_rounding_bound B C N (N+N/2^k+1) (dyadicCofactorRound k)
    hB hBC ((Nat.le_add_right N (N/2^k)).trans (Nat.le_succ _)) (fun b hb =>
      ⟨(dyadicCofactorRound_bounds k b (mem_Icc.mp hb).1).1,
        (dyadicCofactorRound_bounds k b (mem_Icc.mp hb).1).2,dyadicCofactorRound_cross k N b⟩)
      (by omega)
  have he : N+N/2^k+1-N=N/2^k+1 := by
    rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  rw [he] at h
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

/-- The normalized approximation error is uniform in all the cofactor
blocks and all primes in the band. This is not a cancellation assertion for
the rectangularized prime sums. -/
theorem smoothCutoffSkew_dyadic_rounding_ratio (B C N k : ℕ) (hN : 0 < N)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hsize : N+N/2^k+2 ≤ B^2) :
    |smoothCutoffSkew B C N -
      roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N (dyadicCofactorRound k)|/N ≤ 1/(2 : ℝ)^k+2/N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right (smoothCutoffSkew_dyadic_rounding_bound B C N k hB hBC hsize) hN0.le
  have hdiv := Nat.cast_div_le (α := ℝ) (m := N) (n := 2^k)
  push_cast at hdiv
  apply h.trans
  calc
    ((N/2^k : ℕ)+2 : ℝ)/N ≤ ((N : ℝ)/(2 : ℝ)^k+2)/N :=
      div_le_div_of_nonneg_right (add_le_add hdiv le_rfl) hN0.le
    _ = _ := by field_simp

noncomputable def roundedOddPrimeSkew (P S : Finset ℕ) (C N : ℕ) (r : ℕ → ℕ) : ℂ :=
  ∑ d ∈ S.image r, ∑ p ∈ P, (2/(p.totient : ℂ)) *
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      (∑ b ∈ S.filter (fun b => r b=d), χ (b : ZMod p)) *
        (∑ q ∈ (Ioc C (N/d)).filter Nat.Prime, χ (q : ZMod p))

/-- The rounded sum is exactly a finite sum of odd-character rectangular
blocks, with the original prime-modulus weights retained. -/
theorem roundedPrimeSkew_characters (P S : Finset ℕ) (C N : ℕ) (r : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ b ∈ S, 0 < b) :
    (roundedPrimeSkew P S C N r : ℂ) = roundedOddPrimeSkew P S C N r := by
  classical
  unfold roundedPrimeSkew roundedOddPrimeSkew
  push_cast
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro p hp
  have hpp := hP p hp
  letI : NeZero p := ⟨hpp.ne_zero⟩
  have he := cofactorSetOppositePrimeSkew_characters C (N/d) p
    (S.filter fun b => r b=d) (fun b hb => hS b (mem_filter.mp hb).1)
  have hφ : (p.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hpp.pos).ne'
  apply (mul_left_cancel₀ hφ)
  rw [he]
  field_simp

/-- A direct finite bound between the smooth-cutoff skew and its odd-character
rectangular expansion. The latter still requires a signed analytic estimate. -/
theorem smoothCutoffSkew_odd_rectangles_ratio (B C N k : ℕ) (hN : 0 < N)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hsize : N+N/2^k+2 ≤ B^2) :
    ‖(smoothCutoffSkew B C N : ℂ) -
      roundedOddPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N (dyadicCofactorRound k)‖/N ≤ 1/(2 : ℝ)^k+2/N := by
  rw [← roundedPrimeSkew_characters _ _ C N (dyadicCofactorRound k)
    (fun p hp => (mem_filter.mp hp).2.1) (fun b hb => (mem_Icc.mp hb).1),
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact smoothCutoffSkew_dyadic_rounding_ratio B C N k hN hB hBC hsize

#print axioms dyadicCofactorRound_relative
#print axioms dyadicCofactorRound_image_card
#print axioms dyadicCofactorRound_fiber_interval
#print axioms smoothCutoffSkew_dyadic_rounding_bound
#print axioms smoothCutoffSkew_dyadic_rounding_ratio
#print axioms roundedPrimeSkew_characters
#print axioms smoothCutoffSkew_odd_rectangles_ratio
end Erdos371
