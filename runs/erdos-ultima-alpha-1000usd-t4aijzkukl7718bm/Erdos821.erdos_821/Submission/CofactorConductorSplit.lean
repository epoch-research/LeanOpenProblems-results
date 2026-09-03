import Submission.CofactorAveragedProgression

/-!
# Small and large conductors in cofactor-averaged prime progressions

Small conductors are controlled by cancellation of the cofactor sum alone.
The large primitive prime sums remain explicit, and can be addressed by
mean-value estimates without a small-conductor prime-sum hypothesis.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma nonprincipal_sum_le_primitive_lifts (d : ℕ) (hd : d ≠ 0)
    (F : DirichletCharacter ℂ d → ℝ) (hF : ∀ χ, 0 ≤ F χ) :
    (∑ χ ∈ nonprincipalCharacters d, F χ) ≤
      ∑ c ∈ (d.divisors.erase 1).attach, ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
        F (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2) ψ) := by
  let C := d.divisors.erase 1
  let Z := (Σ c : {c : ℕ // c ∈ C}, DirichletCharacter ℂ c.val)
  let G : Finset Z := C.attach.sigma (fun c => Erdos821.primitiveCharacters c.val)
  let lift : Z → DirichletCharacter ℂ d := fun z =>
    DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors (mem_erase.mp z.1.property).2) z.2
  have hcover : nonprincipalCharacters d ⊆ G.image lift := by
    intro χ hχ
    have hc : χ.conductor ∈ C := nonprincipal_conductor_mem hd hχ
    refine mem_image.mpr ⟨⟨⟨χ.conductor,hc⟩,χ.primitiveCharacter⟩,?_,?_⟩
    · exact mem_sigma.mpr ⟨mem_attach _ _,
        mem_filter.mpr ⟨mem_univ _,χ.primitiveCharacter_isPrimitive⟩⟩
    · exact (character_eq_lift_primitive χ).symm
  calc
    _ ≤ ∑ χ ∈ G.image lift, F χ := sum_le_sum_of_subset_of_nonneg hcover (fun χ _ _ => hF χ)
    _ ≤ ∑ z ∈ G, F (lift z) := sum_image_le_of_nonneg (fun χ _ => hF χ)
    _ = _ := by rw [Finset.sum_sigma]

lemma primitiveCharacters_card_le_totient (c : ℕ) (hc : c ≠ 0) :
    (Erdos821.primitiveCharacters c).card ≤ c.totient := by
  have hh := Erdos821.primitiveCharacters_card_add_imprimitive c hc
  omega

noncomputable def smallConductorCofactorWeight (d R : ℕ) : ℝ :=
  ∑ c ∈ d.divisors.erase 1 with c ≤ R, (c : ℝ)*(Real.sqrt c*(1+Real.log c))

noncomputable def largePrimitiveConductorMangoldt (d R N : ℕ) : ℝ :=
  ∑ c ∈ d.divisors.erase 1 with R < c, ∑ ψ ∈ Erdos821.primitiveCharacters c,
    ‖twistedArithmeticSum ψ vonMangoldt N‖

lemma smallConductorCofactorWeight_nonneg (d R : ℕ) :
    0 ≤ smallConductorCofactorWeight d R := by
  apply sum_nonneg
  intro c hc
  exact mul_nonneg (Nat.cast_nonneg c)
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg c]))

lemma largePrimitiveConductorMangoldt_nonneg (d R N : ℕ) :
    0 ≤ largePrimitiveConductorMangoldt d R N :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => norm_nonneg _))

/-- A split estimate valid at every modulus and every cofactor interval. -/
theorem cofactor_nonprincipal_conductor_split (d R A B N : ℕ) (hd : d ≠ 0) :
    (∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
      ‖twistedArithmeticSum χ vonMangoldt N‖) ≤
      (2 : ℝ)^d.primeFactors.card*mangoldtSum N*smallConductorCofactorWeight d R+
        ((B-A : ℕ) : ℝ)*largePrimitiveConductorMangoldt d R N+
          ((B-A : ℕ) : ℝ)*(d : ℝ)*characterLiftError d N := by
  let L : ℝ := (B-A : ℕ)
  let T : ℝ := (2 : ℝ)^d.primeFactors.card*mangoldtSum N
  let F : DirichletCharacter ℂ d → ℝ := fun χ =>
    ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*‖twistedArithmeticSum χ vonMangoldt N‖
  have hF : ∀ χ, 0 ≤ F χ := fun χ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT : 0 ≤ T := mul_nonneg (by positivity) (mangoldtSum_nonneg N)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hpoint (c : {c : ℕ // c ∈ d.divisors.erase 1}) :
      (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
        F (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2) ψ)) ≤
        T*(if c.val ≤ R then (c.val : ℝ)*(Real.sqrt c.val*(1+Real.log c.val)) else 0)+
          L*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
            ‖twistedArithmeticSum ψ vonMangoldt N‖ else 0)+
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
              (changeLevel_interval_character_bound hcd hc2 hd ψ (mem_filter.mp hψ).2 A B)
              (norm_twisted_mangoldt_le d (DirichletCharacter.changeLevel hcd ψ) N)
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
          L*(∑ ψ ∈ Erdos821.primitiveCharacters c.val, ‖twistedArithmeticSum ψ vonMangoldt N‖)+
            L*((Erdos821.primitiveCharacters c.val).card : ℝ)*characterLiftError d N := by
        calc
          _ ≤ ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
              L*(‖twistedArithmeticSum ψ vonMangoldt N‖+characterLiftError d N) := by
            apply sum_le_sum
            intro ψ hψ
            exact mul_le_mul (cofactor_character_sum_trivial _ A B)
              (norm_twisted_changeLevel_le hcd hd ψ N) (norm_nonneg _) hL
          _ = _ := by simp only [mul_add,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]; ring
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
        L*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          ‖twistedArithmeticSum ψ vonMangoldt N‖ else 0)+
            L*(c.val.totient : ℝ)*characterLiftError d N)) =
      T*smallConductorCofactorWeight d R+L*largePrimitiveConductorMangoldt d R N+
        L*(∑ c ∈ d.divisors.erase 1, (c.totient : ℝ))*characterLiftError d N := by
    rw [sum_attach (d.divisors.erase 1) (fun c : ℕ =>
      (T*(if c ≤ R then (c : ℝ)*(Real.sqrt c*(1+Real.log c)) else 0)+
        L*(if R < c then ∑ ψ ∈ Erdos821.primitiveCharacters c,
          ‖twistedArithmeticSum ψ vonMangoldt N‖ else 0)+
            L*(c.totient : ℝ)*characterLiftError d N))]
    simp only [sum_add_distrib,← mul_sum,← sum_mul,← sum_filter,
      smallConductorCofactorWeight,largePrimitiveConductorMangoldt]
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hL) (characterLiftError_nonneg d N)))

/-- The small-conductor term has no cofactor-interval length factor. -/
theorem cofactor_averaged_progression_split (d : ℕ) [NeZero d]
    (u : (ZMod d)ˣ) (R A B N : ℕ) :
    |cofactorCongruenceWeight d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)/(d.totient : ℝ)| ≤
      ((2 : ℝ)^d.primeFactors.card*mangoldtSum N*smallConductorCofactorWeight d R+
        ((B-A : ℕ) : ℝ)*largePrimitiveConductorMangoldt d R N+
          ((B-A : ℕ) : ℝ)*(d : ℝ)*characterLiftError d N)/(d.totient : ℝ) := by
  apply (cofactor_congruence_discrepancy d u A B N).trans
  exact div_le_div_of_nonneg_right (cofactor_nonprincipal_conductor_split d R A B N (NeZero.ne d))
    (Nat.cast_nonneg _)

end Erdos821.AnalyticSieve
