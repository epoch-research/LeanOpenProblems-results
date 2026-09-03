import FormalConjecturesUtil

/-! An exact arithmetic obstruction for the odd coefficient equations at
the Euler fifth-power seed (27,84,110,133,144). This treats a restricted
polynomial construction, not unrestricted representation counts. -/
namespace Erdos322Research.QuinticEulerOddMoments

noncomputable section
open Finset
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private instance : Fact (Nat.Prime 67) := ⟨by decide⟩

def linear {R : Type*} [CommRing R] (b : Fin 4 → R) : R :=
  27^4*b 0+84^4*b 1+110^4*b 2+133^4*b 3

def cubic {R : Type*} [CommRing R] (b : Fin 4 → R) : R :=
  27^2*b 0^3+84^2*b 1^3+110^2*b 2^3+133^2*b 3^3

def fifth {R : Type*} [CommRing R] (b : Fin 4 → R) : R :=
  b 0^5+b 1^5+b 2^5+b 3^5

private lemma linear_scale {R : Type*} [CommRing R] (t : R) (b : Fin 4 → R) :
    linear (fun i ↦ t*b i) = t*linear b := by unfold linear; ring
private lemma cubic_scale {R : Type*} [CommRing R] (t : R) (b : Fin 4 → R) :
    cubic (fun i ↦ t*b i) = t^3*cubic b := by unfold cubic; ring
private lemma fifth_scale {R : Type*} [CommRing R] (t : R) (b : Fin 4 → R) :
    fifth (fun i ↦ t*b i) = t^5*fifth b := by unfold fifth; ring

private lemma chart₀ : ∀ x y : ZMod 67,
    59+21*x^3+40*y^3+(3+28*x+8*y)^3 = 0 →
    1+x^5+y^5+(3+28*x+8*y)^5 = 0 → False := by decide +kernel

private lemma chart₁ : ∀ y : ZMod 67,
    21+40*y^3+(28+8*y)^3 = 0 →
    1+y^5+(28+8*y)^5 = 0 → False := by decide +kernel

/-- The homogeneous system has no projective point over F₆₇. -/
theorem mod_sixty_seven_zero (b : Fin 4 → ZMod 67)
    (hl : linear b = 0) (hc : cubic b = 0) (hf : fifth b = 0) : ∀ i, b i = 0 := by
  have hb : b 3 = 3*b 0+28*b 1+8*b 2 := by
    norm_num [linear] at hl
    linear_combination (norm := (ring_nf; reduce_mod_char)) hl
  by_cases h₀ : b 0 = 0
  · by_cases h₁ : b 1 = 0
    · have h₂ : b 2 = 0 := by
        unfold cubic at hc
        rw [hb,h₀,h₁] at hc
        norm_num [cubic,mul_pow] at hc
        have hh : (16 : ZMod 67)*b 2^3 = 0 := by linear_combination (norm := (ring_nf; reduce_mod_char)) hc
        have hz := (mul_eq_zero.mp hh).resolve_left (by decide : (16 : ZMod 67) ≠ 0)
        exact eq_zero_of_pow_eq_zero hz
      have h₃ : b 3 = 0 := by simp [h₀,h₁,h₂] at hb; exact hb
      intro i
      fin_cases i <;> assumption
    · let v : Fin 4 → ZMod 67 := fun i ↦ (b 1)⁻¹*b i
      have hc' : cubic v = 0 := by rw [cubic_scale,hc,mul_zero]
      have hf' : fifth v = 0 := by rw [fifth_scale,hf,mul_zero]
      have hv : v = ![0,1,(b 1)⁻¹*b 2,28+8*((b 1)⁻¹*b 2)] := by
        funext i
        fin_cases i <;> simp [v,h₀,h₁,hb,mul_add,mul_left_comm]
        all_goals field_simp
      rw [hv] at hc' hf'
      norm_num [cubic,fifth,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons] at hc' hf'
      reduce_mod_char at hc' hf'
      exact (chart₁ _ hc' hf').elim
  · let v : Fin 4 → ZMod 67 := fun i ↦ (b 0)⁻¹*b i
    have hc' : cubic v = 0 := by rw [cubic_scale,hc,mul_zero]
    have hf' : fifth v = 0 := by rw [fifth_scale,hf,mul_zero]
    have hv : v = ![1,(b 0)⁻¹*b 1,(b 0)⁻¹*b 2,
        3+28*((b 0)⁻¹*b 1)+8*((b 0)⁻¹*b 2)] := by
      funext i
      fin_cases i <;> simp [v,h₀,hb,mul_add,mul_left_comm]
      all_goals field_simp
    rw [hv] at hc' hf'
    norm_num [cubic,fifth,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons] at hc' hf'
    reduce_mod_char at hc' hf'
    exact (chart₀ _ _ hc' hf').elim

/-- Homogeneous descent excludes nonzero integer solutions, without any
primitivity hypothesis on the input vector. -/
theorem integer_odd_moments_zero (b : Fin 4 → ℤ)
    (hl : linear b = 0) (hc : cubic b = 0) (hf : fifth b = 0) : ∀ i, b i = 0 := by
  suffices h : ∀ N : ℕ, ∀ b : Fin 4 → ℤ, (∑ i, (b i).natAbs) = N →
      linear b = 0 → cubic b = 0 → fifth b = 0 → ∀ i, b i = 0 by
    exact h _ b rfl hl hc hf
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro b hN hl hc hf
    by_cases hn : N = 0
    · intro i
      have hs := single_le_sum (f := fun j ↦ (b j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      rw [hN,hn] at hs
      exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
    · have hml : linear (fun i ↦ (b i : ZMod 67)) = 0 := by
        have hh := congrArg (Int.castRingHom (ZMod 67)) hl
        simpa [linear] using hh
      have hmc : cubic (fun i ↦ (b i : ZMod 67)) = 0 := by
        have hh := congrArg (Int.castRingHom (ZMod 67)) hc
        simpa [cubic] using hh
      have hmf : fifth (fun i ↦ (b i : ZMod 67)) = 0 := by
        have hh := congrArg (Int.castRingHom (ZMod 67)) hf
        simpa [fifth] using hh
      have hm := mod_sixty_seven_zero _ hml hmc hmf
      have hd : ∀ i, ∃ c : ℤ, b i = 67*c := fun i ↦
        (ZMod.intCast_zmod_eq_zero_iff_dvd (b i) 67).mp (hm i)
      choose c hb using hd
      have hbfun : b = fun i ↦ 67*c i := funext hb
      have hcl : linear c = 0 := by
        have he : (67 : ℤ)*linear c = 0 := by simpa only [hbfun,linear_scale] using hl
        exact (mul_eq_zero.mp he).resolve_left (by norm_num)
      have hcc : cubic c = 0 := by
        have he : (67 : ℤ)^3*cubic c = 0 := by simpa only [hbfun,cubic_scale] using hc
        exact (mul_eq_zero.mp he).resolve_left (by norm_num)
      have hcf : fifth c = 0 := by
        have he : (67 : ℤ)^5*fifth c = 0 := by simpa only [hbfun,fifth_scale] using hf
        exact (mul_eq_zero.mp he).resolve_left (by norm_num)
      have hscale : 67*(∑ i, (c i).natAbs) = N := by
        rw [←hN,mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hb i,Int.natAbs_mul]
        rfl
      have hsmall : (∑ i, (c i).natAbs) < N := by omega
      have hz := ih _ hsmall c rfl hcl hcc hcf
      intro i
      rw [hb i,hz i,mul_zero]

/-- The three odd moment equations have only the zero rational solution. -/
theorem rational_odd_moments_zero (b : Fin 4 → ℚ)
    (hl : linear b = 0) (hc : cubic b = 0) (hf : fifth b = 0) : ∀ i, b i = 0 := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) b
  choose c he using hd
  have hd0 : algebraMap ℤ ℚ d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℤ ℚ).ne
      (nonZeroDivisors.ne_zero d.prop)
  have he' (i : Fin 4) : (c i : ℚ) = algebraMap ℤ ℚ d * b i := by
    simpa only [Algebra.smul_def] using he i
  have hcl : linear c = 0 := by
    have hh : linear (fun i ↦ (c i : ℚ)) = 0 := by simp only [he',linear_scale,hl,mul_zero]
    unfold linear at hh ⊢
    dsimp only at hh
    exact_mod_cast hh
  have hcc : cubic c = 0 := by
    have hh : cubic (fun i ↦ (c i : ℚ)) = 0 := by simp only [he',cubic_scale,hc,mul_zero]
    unfold cubic at hh ⊢
    dsimp only at hh
    exact_mod_cast hh
  have hcf : fifth c = 0 := by
    have hh : fifth (fun i ↦ (c i : ℚ)) = 0 := by simp only [he',fifth_scale,hf,mul_zero]
    unfold fifth at hh ⊢
    dsimp only at hh
    exact_mod_cast hh
  have hz := integer_odd_moments_zero c hcl hcc hcf
  intro i
  have hh := he' i
  rw [hz i,Int.cast_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left hd0

open Polynomial

def seed : Fin 4 → ℚ := ![27,84,110,133]

private def corePolynomial (u v A C : ℚ) (b : Fin 4 → ℚ) : Polynomial ℚ :=
  (∑ i, (Polynomial.C (seed i)*(Polynomial.C u+Polynomial.C v*X^2)+
    Polynomial.C (b i)*X)^5)+(Polynomial.C C+Polynomial.C A*X^2)^5

private def oddQuotient (u v : ℚ) (b : Fin 4 → ℚ) : Polynomial ℚ :=
  Polynomial.C (5*linear b)*(Polynomial.C u+Polynomial.C v*X^2)^4+
  Polynomial.C (10*cubic b)*X^2*(Polynomial.C u+Polynomial.C v*X^2)^2+
  Polynomial.C (fifth b)*X^4

private lemma odd_difference (u v A C : ℚ) (b : Fin 4 → ℚ) :
    corePolynomial u v A C b - (corePolynomial u v A C b).comp (-X) =
      2*X*oddQuotient u v b := by
  simp only [corePolynomial,Fin.sum_univ_four,seed,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,add_comp,pow_comp,mul_comp,C_comp,X_comp,ofNat_comp,
    oddQuotient,linear,cubic,fifth,map_add,map_mul,map_pow,map_ofNat]
  ring

private lemma oddQuotient_expansion (u v : ℚ) (b : Fin 4 → ℚ) :
    oddQuotient u v b =
      Polynomial.C (5*linear b*u^4)+
      Polynomial.C (20*linear b*u^3*v+10*cubic b*u^2)*X^2+
      Polynomial.C (30*linear b*u^2*v^2+20*cubic b*u*v+fifth b)*X^4+
      Polynomial.C (20*linear b*u*v^3+10*cubic b*v^2)*X^6+
      Polynomial.C (5*linear b*v^4)*X^8 := by
  simp only [oddQuotient,map_add,map_mul,map_pow,map_ofNat]
  ring

/-- If the four Euler coordinates share any nonzero even quadratic core,
a constant fifth-power identity forces every odd linear term to vanish.
The fifth coordinate may be any even quadratic polynomial. -/
theorem common_core_odd_terms_zero (u v A C N : ℚ) (b : Fin 4 → ℚ)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (h : ∀ t : ℚ, (∑ i, (seed i*(u+v*t^2)+b i*t)^5)+(C+A*t^2)^5 = N) :
    ∀ i, b i = 0 := by
  have hp : corePolynomial u v A C b = Polynomial.C N := by
    apply Polynomial.funext
    intro t
    simpa [corePolynomial,eval_finset_sum] using h t
  have hg : oddQuotient u v b = 0 := by
    have hh : 2*X*oddQuotient u v b = 0 := by
      rw [←odd_difference,hp,C_comp,sub_self]
    exact (mul_eq_zero.mp hh).resolve_left
      (mul_ne_zero (by norm_num : (2 : Polynomial ℚ) ≠ 0) X_ne_zero)
  have hc₀ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 0) hg
  have hc₂ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 2) hg
  have hc₄ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 4) hg
  have hc₆ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 6) hg
  have hc₈ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 8) hg
  rw [oddQuotient_expansion] at hc₀ hc₂ hc₄ hc₆ hc₈
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_zero] at hc₀ hc₂ hc₄ hc₆ hc₈
  norm_num at hc₀ hc₂ hc₄ hc₆ hc₈
  have hl : linear b = 0 := by
    rcases huv with hu | hv
    · exact hc₀.resolve_right hu
    · exact hc₈.resolve_right hv
  have hc : cubic b = 0 := by
    simp only [hl,mul_zero,zero_mul,zero_add] at hc₂ hc₆
    rcases huv with hu | hv
    · exact (mul_eq_zero.mp ((mul_eq_zero.mp hc₂).resolve_right
        (pow_ne_zero _ hu))).resolve_left (by norm_num)
    · exact (mul_eq_zero.mp ((mul_eq_zero.mp hc₆).resolve_right
        (pow_ne_zero _ hv))).resolve_left (by norm_num)
  have hf : fifth b = 0 := by simpa [hl,hc] using hc₄
  exact rational_odd_moments_zero b hl hc hf

private lemma even_fifth_top (a c : ℚ) :
    ((Polynomial.C c+Polynomial.C a*X^2)^5).coeff 10 = a^5 ∧
    ((Polynomial.C c+Polynomial.C a*X^2)^5).coeff 8 = 5*a^4*c := by
  have he : (Polynomial.C c+Polynomial.C a*X^2)^5 =
      Polynomial.C (c^5)+Polynomial.C (5*c^4*a)*X^2+
      Polynomial.C (10*c^3*a^2)*X^4+Polynomial.C (10*c^2*a^3)*X^6+
      Polynomial.C (5*a^4*c)*X^8+Polynomial.C (a^5)*X^10 := by
    simp only [map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C]
  norm_num

/-- All nonzero constant-sum identities in the common-core Euler family
are constant tuples. This covers both signs of the quadratic leading core. -/
theorem common_core_constant_identity_classification (u v A C N : ℚ) (b : Fin 4 → ℚ)
    (huv : u ≠ 0 ∨ v ≠ 0) (hN : N ≠ 0)
    (h : ∀ t : ℚ, (∑ i, (seed i*(u+v*t^2)+b i*t)^5)+(C+A*t^2)^5 = N) :
    (∀ i, b i = 0) ∧ v = 0 ∧ A = 0 := by
  have hb := common_core_odd_terms_zero u v A C N b huv h
  have hn (t : ℚ) : (144*(u+v*t^2))^5+(C+A*t^2)^5 = N := by
    have hh := h t
    simp only [hb,zero_mul,add_zero] at hh
    have he : (∑ i, (seed i*(u+v*t^2))^5) = (144*(u+v*t^2))^5 := by
      norm_num [Fin.sum_univ_four,seed,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons]
      ring
    rwa [he] at hh
  have hp : (Polynomial.C (144*u)+Polynomial.C (144*v)*X^2)^5+
      (Polynomial.C C+Polynomial.C A*X^2)^5 = Polynomial.C N := by
    apply Polynomial.funext
    intro t
    have he : 144*(u+v*t^2) = 144*u+144*v*t^2 := by ring
    simpa [he] using hn t
  have h₁₀ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 10) hp
  have h₈ := congrArg (fun P : Polynomial ℚ ↦ P.coeff 8) hp
  simp only [coeff_add,(even_fifth_top _ _).1,(even_fifth_top _ _).2,
    coeff_C] at h₁₀ h₈
  norm_num at h₁₀ h₈
  have hA : A = -144*v := by
    apply (show Odd (5 : ℕ) by decide).pow_injective
    linear_combination h₁₀
  have hv : v = 0 := by
    by_contra hv
    have he : (5*144^4*v^4)*(144*u+C) = 0 := by
      rw [hA] at h₈
      linear_combination h₈
    have hsum : 144*u+C = 0 := (mul_eq_zero.mp he).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hv))
    have hC : C = -144*u := by linarith
    have hz := hn 0
    rw [hC] at hz
    apply hN
    linear_combination -hz
  exact ⟨hb,hv,by simpa [hv] using hA⟩

end
end Erdos322Research.QuinticEulerOddMoments
