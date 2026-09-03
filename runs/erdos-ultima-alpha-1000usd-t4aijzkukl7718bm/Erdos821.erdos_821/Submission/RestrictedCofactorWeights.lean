import Submission.CofactorBilinearLargeSieve
import Submission.CofactorPrincipalMean

/-!
# Cofactor character identities with restricted Mangoldt weights

These are finite estimates for a nonnegative arithmetic weight dominated
by the von Mangoldt function. The principal term retains the actual
restricted mass. None of these estimates asserts a lower bound on that
mass or removes the average over the cofactor.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def restrictedMass (f : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, f n

noncomputable def restrictedNonunitMass (f : ArithmeticFunction ℝ) (d N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if ¬n.Coprime d then f n else 0

noncomputable def restrictedCofactorWeight (f : ArithmeticFunction ℝ)
    (d : ℕ) (u : (ZMod d)ˣ) (A B N : ℕ) : ℝ :=
  ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N,
    if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then f n else 0

noncomputable def restrictedCofactorPrincipal (f : ArithmeticFunction ℝ)
    (d A B N : ℕ) : ℝ :=
  (coprimeCofactorCount d A B : ℝ)*
    (restrictedMass f N-restrictedNonunitMass f d N)/(d.totient : ℝ)

lemma restrictedMass_nonneg (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (N : ℕ) : 0 ≤ restrictedMass f N :=
  sum_nonneg (fun n _ => hf n)

lemma restrictedMass_le_mangoldt (f : ArithmeticFunction ℝ)
    (hf : ∀ n, f n ≤ vonMangoldt n) (N : ℕ) :
    restrictedMass f N ≤ mangoldtSum N :=
  sum_le_sum (fun n _ => hf n)

lemma restrictedNonunitMass_nonneg (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (d N : ℕ) : 0 ≤ restrictedNonunitMass f d N := by
  apply sum_nonneg
  intro n hn
  split_ifs <;> first | exact hf n | exact le_rfl

lemma restrictedNonunitMass_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n, f n ≤ vonMangoldt n) (d N : ℕ) :
    restrictedNonunitMass f d N ≤ nonunitMangoldt d N := by
  apply sum_le_sum
  intro n hn
  split_ifs <;> first | exact hf n | exact le_rfl

lemma restricted_twisted_principal (f : ArithmeticFunction ℝ) (d N : ℕ) :
    twistedArithmeticSum (1 : DirichletCharacter ℂ d) f N =
      ((restrictedMass f N-restrictedNonunitMass f d N : ℝ) : ℂ) := by
  simp only [twistedArithmeticSum,restrictedMass,restrictedNonunitMass,
    Complex.ofReal_sub,Complex.ofReal_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rw [principal_character_nat]
  by_cases h : n.Coprime d <;> simp [h]

lemma restricted_norm_twisted_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (d : ℕ) (χ : DirichletCharacter ℂ d) (N : ℕ) :
    ‖twistedArithmeticSum χ f N‖ ≤ restrictedMass f N := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf n)]
  exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (hf n)).trans_eq (mul_one _)

lemma restricted_lift_difference (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    {c d : ℕ} (hcd : c ∣ d) (ψ : DirichletCharacter ℂ c) (N : ℕ) :
    ‖twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) f N-
      twistedArithmeticSum ψ f N‖ ≤ restrictedNonunitMass f d N := by
  rw [twistedArithmeticSum,twistedArithmeticSum,← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  change ‖(f n : ℂ)*(DirichletCharacter.changeLevel hcd ψ) (n : ZMod d)-
    (f n : ℂ)*ψ (n : ZMod c)‖ ≤ if ¬n.Coprime d then f n else 0
  rw [changeLevel_apply_nat]
  by_cases hc : n.Coprime d
  · rw [if_pos hc,if_neg (not_not.mpr hc),sub_self,norm_zero]
  · simp only [hc,not_false_eq_true,if_true,if_false,mul_zero,zero_sub,norm_neg,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf n)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ψ.norm_le_one _) (hf n)

lemma restricted_lift_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    {c d : ℕ} (hcd : c ∣ d) (hd : d ≠ 0)
    (ψ : DirichletCharacter ℂ c) (N : ℕ) :
    ‖twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) f N‖ ≤
      ‖twistedArithmeticSum ψ f N‖+characterLiftError d N := by
  have hh := norm_le_norm_sub_add
    (twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) f N)
    (twistedArithmeticSum ψ f N)
  have hb := (restricted_lift_difference f hf hcd ψ N).trans
    ((restrictedNonunitMass_le f hΛ d N).trans (nonunitMangoldt_le_liftError d N hd))
  linarith

lemma restricted_cofactor_orthogonality (f : ArithmeticFunction ℝ)
    (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ) :
    (∑ χ : DirichletCharacter ℂ d, χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
      twistedArithmeticSum χ f N) =
      (d.totient : ℂ)*(restrictedCofactorWeight f d u A B N : ℂ) := by
  calc
    _ = ∑ a ∈ Icc (A+1) B, ∑ n ∈ Icc 1 N, (f n : ℂ)*
        (∑ χ : DirichletCharacter ℂ d, χ ((u : ZMod d)*(a : ZMod d)*(n : ZMod d))) := by
      simp only [twistedArithmeticSum,mul_sum,sum_mul]
      rw [sum_comm]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro χ hχ
      simp only [map_mul]
      ring
    _ = _ := by
      simp only [DirichletCharacter.sum_characters_eq,restrictedCofactorWeight,
        Complex.ofReal_sum,apply_ite Complex.ofReal,Complex.ofReal_zero,mul_sum,
        mul_ite,mul_zero]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring

/-- Exact principal term; the cofactor average is still present. -/
theorem restricted_cofactor_discrepancy (f : ArithmeticFunction ℝ)
    (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (A B N : ℕ) :
    |restrictedCofactorWeight f d u A B N-restrictedCofactorPrincipal f d A B N| ≤
      (∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
        ‖twistedArithmeticSum χ f N‖)/(d.totient : ℝ) := by
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos d)
  have h := sum_erase_add (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*twistedArithmeticSum χ f N)
    (mem_univ 1)
  dsimp only at h
  rw [restricted_cofactor_orthogonality,principal_cofactor_character_sum,
    restricted_twisted_principal,MulChar.one_apply u.isUnit,one_mul] at h
  have he : (((d.totient : ℝ)*restrictedCofactorWeight f d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(restrictedMass f N-restrictedNonunitMass f d N) : ℝ) : ℂ) =
      ∑ χ ∈ nonprincipalCharacters d, χ u*(∑ a ∈ Icc (A+1) B, χ (a : ZMod d))*
        twistedArithmeticSum χ f N := by
    have hs : nonprincipalCharacters d = (univ : Finset (DirichletCharacter ℂ d)).erase 1 := by
      ext χ
      simp only [nonprincipalCharacters,mem_erase,mem_univ,and_true]
    rw [hs]
    push_cast at h ⊢
    linear_combination -h
  have hb : |(d.totient : ℝ)*restrictedCofactorWeight f d u A B N-
      (coprimeCofactorCount d A B : ℝ)*(restrictedMass f N-restrictedNonunitMass f d N)| ≤
      ∑ χ ∈ nonprincipalCharacters d, ‖∑ a ∈ Icc (A+1) B, χ (a : ZMod d)‖*
        ‖twistedArithmeticSum χ f N‖ := by
    calc
      _ = ‖(((d.totient : ℝ)*restrictedCofactorWeight f d u A B N-
          (coprimeCofactorCount d A B : ℝ)*(restrictedMass f N-restrictedNonunitMass f d N) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by
        rw [he]
        apply (norm_sum_le _ _).trans_eq
        simp only [norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul]
  apply (le_div_iff₀ hφ).mpr
  calc
    _ = |(d.totient : ℝ)*restrictedCofactorWeight f d u A B N-
        (coprimeCofactorCount d A B : ℝ)*(restrictedMass f N-restrictedNonunitMass f d N)| := by
      calc
        _ = |(restrictedCofactorWeight f d u A B N-
            restrictedCofactorPrincipal f d A B N)*(d.totient : ℝ)| := by
          rw [abs_mul,abs_of_pos hφ]
        _ = _ := by unfold restrictedCofactorPrincipal; congr 1; field_simp
    _ ≤ _ := hb

/-- Replacing the exact principal term retains the restricted mass. Only
nonunit terms have to be charged separately. -/
lemma restricted_principal_density_error (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (d A B N : ℕ) (hd : 0 < d) :
    |restrictedCofactorPrincipal f d A B N-
      ((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)| ≤
      (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*restrictedMass f N+
        ((B-A : ℕ) : ℝ)*restrictedNonunitMass f d N/(d.totient : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hφ : (0 : ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hS := restrictedMass_nonneg f hf N
  have hU := restrictedNonunitMass_nonneg f hf d N
  have hcount : (coprimeCofactorCount d A B : ℝ) ≤ ((B-A : ℕ) : ℝ) := by
    exact_mod_cast coprimeCofactorCount_le_length d A B
  have he : restrictedCofactorPrincipal f d A B N-
      ((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ) =
      ((coprimeCofactorCount d A B : ℝ)-((B-A : ℕ) : ℝ)*(d.totient : ℝ)/(d : ℝ))*
        (restrictedMass f N/(d.totient : ℝ))-
          (coprimeCofactorCount d A B : ℝ)*restrictedNonunitMass f d N/(d.totient : ℝ) := by
    unfold restrictedCofactorPrincipal
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (div_nonneg hS hφ.le),
    abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hU) hφ.le)]
  have h1 := mul_le_mul_of_nonneg_right (coprimeCofactorCount_density_error d A B hd)
    (div_nonneg hS hφ.le)
  have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hU) hφ.le
  apply (_root_.add_le_add h1 h2).trans_eq
  ring

lemma restricted_principal_density_lift_error (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (d A B N : ℕ) (hd : 0 < d) :
    |restrictedCofactorPrincipal f d A B N-
      ((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)| ≤
      (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*restrictedMass f N+
        ((B-A : ℕ) : ℝ)*characterLiftError d N/(d.totient : ℝ) := by
  apply (restricted_principal_density_error f hf d A B N hd).trans
  apply _root_.add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact (restrictedNonunitMass_le f hΛ d N).trans (nonunitMangoldt_le_liftError d N hd.ne')

/-- The energy depends on the actual restricted mass, rather than N log²N. -/
lemma restricted_coefficient_energy (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖(f n : ℂ)‖^2) ≤ Real.log N*restrictedMass f N := by
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,restrictedMass,mul_sum]
  apply sum_le_sum
  intro n hn
  have hnN := (hΛ n).trans ((vonMangoldt_le_log (n := n)).trans
    (log_nat_mono (mem_Icc.mp hn).2))
  nlinarith [hf n]

noncomputable def restrictedBilinearKernel (f : ArithmeticFunction ℝ) (Q B N : ℕ) : ℝ :=
  (2+Real.log ((B : ℝ)+2))*Real.sqrt
    ((2*(Q : ℝ)^2+4*(2*Real.pi*B+1))*(2*(Q : ℝ)^2+4*(2*Real.pi*N+1))*
      (B : ℝ)*(Real.log N*restrictedMass f N))

/-- Restricting the prime weight preserves the adaptive large sieve, but does
not change the product half-level or eliminate the cofactor variable. -/
theorem restricted_primitive_maxPrefix_bilinear_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive) (B N : ℕ) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      cofactorMaxPrefix χ B*‖twistedArithmeticSum χ f N‖) ≤
        restrictedBilinearKernel f Q B N := by
  have hh := adaptive_prefix_bilinear_large_sieve_nat M Q hQ hM C hC
    (Icc 1 B) (Icc 1 N) (fun _ => 1) (fun n => (f n : ℂ)) B N
    (fun n hn => (mem_Icc.mp hn).2) (fun n hn => (mem_Icc.mp hn).2)
    (fun _ χ => cofactorPrefixSelector χ B)
    (fun _ _ χ _ => (cofactorPrefixSelector_spec χ B).1)
  simp only [cofactorPrefix_filter B _ (cofactorPrefixSelector_spec _ B).1,
    one_mul,norm_one,one_pow,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,
    mul_one] at hh
  change (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
    cofactorMaxPrefix χ B*‖twistedArithmeticSum χ f N‖) ≤ _ at hh
  apply hh.trans
  unfold restrictedBilinearKernel
  apply mul_le_mul_of_nonneg_left _ (by
    have hlog : 0 ≤ Real.log ((B : ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (restricted_coefficient_energy f hf hΛ N) (by positivity)

end Erdos821.AnalyticSieve
