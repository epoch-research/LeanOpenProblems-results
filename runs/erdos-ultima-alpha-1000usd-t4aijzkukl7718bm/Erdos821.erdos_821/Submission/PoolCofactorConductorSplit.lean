import Submission.MultiplicativeCofactorOrthogonality

/-!
# A retained-pool conductor split without lifting error

The unit-support assumptions are explicit for both the multiplier pool
and the arithmetic weight. They remove, rather than bound, the deleted-
prime contribution. The long-cofactor factor remains in the large part.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma pool_character_sum_trivial {d : ℕ} (χ : DirichletCharacter ℂ d) (P : Finset ℕ) :
    ‖∑ c ∈ P, χ (c : ZMod d)‖ ≤ (P.card : ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c ∈ P, (1 : ℝ) := sum_le_sum (fun c _ => χ.norm_le_one _)
    _ = _ := by simp

noncomputable def poolLargeConductor (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d R B N : ℕ) : ℝ :=
  ∑ c ∈ d.divisors.erase 1 with R < c, ∑ ψ ∈ Erdos821.primitiveCharacters c,
    ‖∑ z ∈ P, ψ (z : ZMod c)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖

lemma poolLargeConductor_nonneg (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d R B N : ℕ) : 0 ≤ poolLargeConductor f P d R B N := by
  exact sum_nonneg (fun c _ => sum_nonneg (fun ψ _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (cofactorMaxPrefix_nonneg ψ B)) (norm_nonneg _)))

noncomputable def poolCofactorPrincipal (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (d A B N : ℕ) : ℝ :=
  (P.card : ℝ)*(coprimeCofactorCount d A B : ℝ)*restrictedMass f N/(d.totient : ℝ)

/-- There is no residual term of size B*d*characterLiftError. -/
theorem pool_unit_nonprincipal_split (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (P : Finset ℕ) (d R B N : ℕ) (hd : d ≠ 0)
    (hP : ∀ c ∈ P, c.Coprime d)
    (hunit : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    (∑ χ ∈ nonprincipalCharacters d, ‖∑ z ∈ P, χ (z : ZMod d)‖*
      ‖∑ a ∈ Icc 1 B, χ (a : ZMod d)‖*‖twistedArithmeticSum χ f N‖) ≤
      (2 : ℝ)^d.primeFactors.card*
        ((P.card : ℝ)*restrictedMass f N*smallConductorCofactorWeight d R+
          poolLargeConductor f P d R B N) := by
  let V : ℝ := (2 : ℝ)^d.primeFactors.card
  let T : ℝ := V*(P.card : ℝ)*restrictedMass f N
  let F : DirichletCharacter ℂ d → ℝ := fun χ =>
    ‖∑ z ∈ P, χ (z : ZMod d)‖*‖∑ a ∈ Icc 1 B, χ (a : ZMod d)‖*
      ‖twistedArithmeticSum χ f N‖
  have hF : ∀ χ, 0 ≤ F χ := fun χ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hT : 0 ≤ T := by dsimp [T,V]; positivity [restrictedMass_nonneg f hf N]
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (c : {c : ℕ // c ∈ d.divisors.erase 1}) :
      (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
        F (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2) ψ)) ≤
        T*(if c.val ≤ R then (c.val : ℝ)*(Real.sqrt c.val*(1+Real.log c.val)) else 0)+
          V*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
            ‖∑ z ∈ P, ψ (z : ZMod c.val)‖*cofactorMaxPrefix ψ B*
              ‖twistedArithmeticSum ψ f N‖ else 0) := by
    have hc0 : 0 < c.val := Nat.pos_of_mem_divisors (mem_erase.mp c.property).2
    have hc2 : 2 ≤ c.val := by have := (mem_erase.mp c.property).1; omega
    have hcd : c.val ∣ d := Nat.dvd_of_mem_divisors (mem_erase.mp c.property).2
    have hroot : 0 ≤ Real.sqrt c.val*(1+Real.log c.val) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg c.val])
    by_cases hcR : c.val ≤ R
    · rw [if_pos hcR,if_neg (not_lt_of_ge hcR),mul_zero,add_zero]
      have hh : (∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          F (DirichletCharacter.changeLevel hcd ψ)) ≤
          ((Erdos821.primitiveCharacters c.val).card : ℝ)*(T*(Real.sqrt c.val*(1+Real.log c.val))) := by
        calc
          _ ≤ ∑ _ψ ∈ Erdos821.primitiveCharacters c.val, T*(Real.sqrt c.val*(1+Real.log c.val)) := by
            apply sum_le_sum
            intro ψ hψ
            have hp := pool_character_sum_trivial (DirichletCharacter.changeLevel hcd ψ) P
            have ha := changeLevel_interval_character_bound hcd hc2 hd ψ (mem_filter.mp hψ).2 0 B
            have hn := restricted_norm_twisted_le f hf d (DirichletCharacter.changeLevel hcd ψ) N
            simp only [zero_add] at ha
            have h := mul_le_mul (mul_le_mul hp ha (norm_nonneg _) (Nat.cast_nonneg P.card)) hn
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg P.card) (mul_nonneg hV hroot))
            convert h using 1; dsimp [F,T,V]; ring
          _ = _ := by rw [sum_const,nsmul_eq_mul]
      have hcard : ((Erdos821.primitiveCharacters c.val).card : ℝ) ≤ c.val := by
        have hh := (primitiveCharacters_card_le_totient c.val hc0.ne').trans (Nat.totient_le c.val)
        exact_mod_cast hh
      have hb := hh.trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg hT hroot))
      convert hb using 1; ring
    · rw [if_neg hcR,if_pos (Nat.lt_of_not_ge hcR),mul_zero,zero_add,mul_sum]
      apply sum_le_sum
      intro ψ hψ
      dsimp [F]
      rw [unit_pool_character_changeLevel P hcd ψ hP,
        unit_supported_twisted_changeLevel f hcd ψ N hunit]
      have ha := changeLevel_prefix_le_max hcd hd ψ B
      have hb := mul_le_mul_of_nonneg_left ha (norm_nonneg (∑ z ∈ P, ψ (z : ZMod c.val)))
      have hh := mul_le_mul_of_nonneg_right hb (norm_nonneg (twistedArithmeticSum ψ f N))
      convert hh using 1; dsimp [V]; ring
  have hh := (nonprincipal_sum_le_primitive_lifts d hd F hF).trans
    (sum_le_sum (fun c _ => hpoint c))
  have he : (∑ c ∈ (d.divisors.erase 1).attach,
      (T*(if c.val ≤ R then (c.val : ℝ)*(Real.sqrt c.val*(1+Real.log c.val)) else 0)+
        V*(if R < c.val then ∑ ψ ∈ Erdos821.primitiveCharacters c.val,
          ‖∑ z ∈ P, ψ (z : ZMod c.val)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0))) =
      T*smallConductorCofactorWeight d R+V*poolLargeConductor f P d R B N := by
    rw [sum_attach (d.divisors.erase 1) (fun c : ℕ =>
      (T*(if c ≤ R then (c : ℝ)*(Real.sqrt c*(1+Real.log c)) else 0)+
        V*(if R < c then ∑ ψ ∈ Erdos821.primitiveCharacters c,
          ‖∑ z ∈ P, ψ (z : ZMod c)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0)))]
    simp only [sum_add_distrib,← mul_sum,← sum_filter,smallConductorCofactorWeight,poolLargeConductor]
  rw [he] at hh
  convert hh using 1; dsimp [F,T,V]; ring

/-- The exact principal mass and the retained three-factor remainder. -/
theorem pool_unit_progression_split (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (P : Finset ℕ) (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (R B N : ℕ)
    (hP : ∀ c ∈ P, c.Coprime d)
    (hunit : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    |poolCofactorWeight f P d u 0 B N-poolCofactorPrincipal f P d 0 B N| ≤
      (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*
        ((P.card : ℝ)*restrictedMass f N*smallConductorCofactorWeight d R+
          poolLargeConductor f P d R B N) := by
  apply (pool_cofactor_discrepancy f P d u 0 B N hP hunit).trans
  have hh := div_le_div_of_nonneg_right
    (pool_unit_nonprincipal_split f hf P d R B N (NeZero.ne d) hP hunit) (Nat.cast_nonneg d.totient)
  convert hh using 1; ring

end Erdos821.AnalyticSieve
