import Submission.RestrictedCofactorWeights

/-! Conductor splitting with a nonnegative restricted Mangoldt weight. -/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def restrictedLargeConductor (f : ArithmeticFunction ℝ) (d R B N : ℕ) : ℝ :=
  ∑ c ∈ d.divisors.erase 1 with R < c, ∑ ψ ∈ Erdos821.primitiveCharacters c,
    cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖

lemma restrictedLargeConductor_nonneg (f : ArithmeticFunction ℝ) (d R B N : ℕ) :
    0 ≤ restrictedLargeConductor f d R B N :=
  sum_nonneg (fun _ _ => sum_nonneg (fun ψ _ =>
    mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg _)))

theorem restricted_bilinear_nonprincipal_split (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (d R B N : ℕ) (hd : d ≠ 0) :
    (∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc 1 B, χ (a : ZMod d)‖*
      ‖twistedArithmeticSum χ f N‖) ≤
      (2 : ℝ)^d.primeFactors.card*restrictedMass f N*smallConductorCofactorWeight d R+
        (2 : ℝ)^d.primeFactors.card*restrictedLargeConductor f d R B N+
          (B : ℝ)*(d : ℝ)*characterLiftError d N := by
  let L : ℝ := B
  let T : ℝ := (2 : ℝ)^d.primeFactors.card*restrictedMass f N
  let V : ℝ := (2 : ℝ)^d.primeFactors.card
  let F : DirichletCharacter ℂ d → ℝ := fun χ =>
    ‖∑ a ∈ Icc 1 B, χ (a : ZMod d)‖*‖twistedArithmeticSum χ f N‖
  have hF : ∀ χ, 0 ≤ F χ := fun χ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT : 0 ≤ T := mul_nonneg (by positivity) (restrictedMass_nonneg f hf N)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hpoint (c : {c : ℕ // c ∈ d.divisors.erase 1}) :
      (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
        F (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2) ψ)) ≤
        T*(if c.val ≤ R then (c.val : ℝ)*(Real.sqrt c.val*(1+Real.log c.val)) else 0)+
          V*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
            cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0)+
              L*(c.val.totient : ℝ)*characterLiftError d N := by
    have hc0 : 0 < c.val := Nat.pos_of_mem_divisors (mem_erase.mp c.property).2
    have hc2 : 2 ≤ c.val := by have := (mem_erase.mp c.property).1; omega
    have hcd : c.val ∣ d := Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2
    have hroot : 0 ≤ Real.sqrt c.val*(1+Real.log c.val) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg c.val])
    have hcard : ((Erdos821.primitiveCharacters c.val).card : ℝ) ≤ c.val.totient := by
      exact_mod_cast primitiveCharacters_card_le_totient c.val hc0.ne'
    by_cases hcR : c.val ≤ R
    · rw [if_pos hcR,if_neg (not_lt_of_ge hcR),mul_zero,add_zero]
      have hh : (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          F (DirichletCharacter.changeLevel hcd ψ)) ≤
          ((Erdos821.primitiveCharacters c.val).card : ℝ)*
            (T*(Real.sqrt c.val*(1+Real.log c.val))) := by
        calc
          _ ≤ ∑ _ψ ∈ Erdos821.primitiveCharacters c.val,
              T*(Real.sqrt c.val*(1+Real.log c.val)) := by
            apply sum_le_sum
            intro ψ hψ
            have hb := mul_le_mul
              (changeLevel_interval_character_bound hcd hc2 hd ψ (mem_filter.mp hψ).2 0 B)
              (restricted_norm_twisted_le f hf d (DirichletCharacter.changeLevel hcd ψ) N)
              (norm_nonneg _) (mul_nonneg (by positivity) hroot)
            convert hb using 1; dsimp [F,T]; ring
          _ = _ := by rw [sum_const,nsmul_eq_mul]
      have hcard' : ((Erdos821.primitiveCharacters c.val).card : ℝ) ≤ c.val :=
        hcard.trans (by exact_mod_cast Nat.totient_le c.val)
      have hbound := hh.trans (mul_le_mul_of_nonneg_right hcard' (mul_nonneg hT hroot))
      have herr : 0 ≤ L*(c.val.totient : ℝ)*characterLiftError d N :=
        mul_nonneg (mul_nonneg hL (Nat.cast_nonneg _)) (characterLiftError_nonneg d N)
      nlinarith only [hbound,herr]
    · rw [if_neg hcR,if_pos (Nat.lt_of_not_ge hcR),mul_zero,zero_add]
      have hh : (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          F (DirichletCharacter.changeLevel hcd ψ)) ≤
          V*(∑ ψ ∈ Erdos821.primitiveCharacters c.val,
            cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖)+
            L*((Erdos821.primitiveCharacters c.val).card : ℝ)*characterLiftError d N := by
        calc
          _ ≤ ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
              (V*(cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖)+
                L*characterLiftError d N) := by
            apply sum_le_sum
            intro ψ hψ
            have hp := mul_le_mul_of_nonneg_left (restricted_lift_bound f hf hΛ hcd hd ψ N)
              (norm_nonneg (∑ a ∈ Icc 1 B, (DirichletCharacter.changeLevel hcd ψ) (a : ZMod d)))
            rw [mul_add] at hp
            have ha := mul_le_mul_of_nonneg_right (changeLevel_prefix_le_max hcd hd ψ B)
              (norm_nonneg (twistedArithmeticSum ψ f N))
            have hb := mul_le_mul_of_nonneg_right
              (cofactor_character_sum_trivial (DirichletCharacter.changeLevel hcd ψ) 0 B)
              (characterLiftError_nonneg d N)
            simp only [zero_add,Nat.sub_zero] at hb
            have hs := hp.trans (_root_.add_le_add ha hb)
            convert hs using 1; dsimp [F,V,L]; ring
          _ = _ := by simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]; ring
      exact hh.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hL) (characterLiftError_nonneg d N)))
  have hmass : (∑ c ∈ d.divisors.erase 1, (c.totient : ℝ)) ≤ d := by
    calc
      _ ≤ ∑ c ∈ d.divisors, (c.totient : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun c _ _ => Nat.cast_nonneg _)
      _ = _ := by rw [← Nat.cast_sum,Nat.sum_totient]
  have hh := (nonprincipal_sum_le_primitive_lifts d hd F hF).trans
    (sum_le_sum (fun c _ => hpoint c))
  have he : (∑ c ∈ (d.divisors.erase 1).attach,
      (T*(if c.val ≤ R then (c.val : ℝ)*(Real.sqrt c.val*(1+Real.log c.val)) else 0)+
        V*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0)+
            L*(c.val.totient : ℝ)*characterLiftError d N)) =
      T*smallConductorCofactorWeight d R+V*restrictedLargeConductor f d R B N+
        L*(∑ c ∈ d.divisors.erase 1, (c.totient : ℝ))*characterLiftError d N := by
    rw [sum_attach (d.divisors.erase 1) (fun c : ℕ =>
      (T*(if c ≤ R then (c : ℝ)*(Real.sqrt c*(1+Real.log c)) else 0)+
        V*(if R < c then ∑ ψ ∈ Erdos821.primitiveCharacters c,
          cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0)+
            L*(c.totient : ℝ)*characterLiftError d N))]
    simp only [sum_add_distrib,← mul_sum,← sum_mul,← sum_filter,
      smallConductorCofactorWeight,restrictedLargeConductor]
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hL) (characterLiftError_nonneg d N)))

/-- The principal main term remains exact. -/
theorem restricted_bilinear_progression_split (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (d : ℕ) [NeZero d]
    (u : (ZMod d)ˣ) (R B N : ℕ) :
    |restrictedCofactorWeight f d u 0 B N-restrictedCofactorPrincipal f d 0 B N| ≤
      ((2 : ℝ)^d.primeFactors.card*restrictedMass f N*smallConductorCofactorWeight d R+
        (2 : ℝ)^d.primeFactors.card*restrictedLargeConductor f d R B N+
          (B : ℝ)*(d : ℝ)*characterLiftError d N)/(d.totient : ℝ) := by
  apply (restricted_cofactor_discrepancy f d u 0 B N).trans
  exact div_le_div_of_nonneg_right (restricted_bilinear_nonprincipal_split f hf hΛ d R B N (NeZero.ne d))
    (Nat.cast_nonneg _)


end Erdos821.AnalyticSieve
