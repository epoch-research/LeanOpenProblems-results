import FormalConjectures.Util.ProblemImports

open Finset Polynomial

namespace PrimeSign

private lemma sum_pow_card_sub_one (p : ℕ) [hp : Fact p.Prime] :
    (∑ x : ZMod p, x ^ (p - 1)) = -1 := by
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  classical
  let e : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have him : Finset.univ.map e = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl⟩
      exact Units.ne_zero u
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  calc
    (∑ x : ZMod p, x ^ (p - 1)) = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ (p - 1) := by
      rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ]
      simp [hpos.ne']
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ (p - 1)) := by
      rw [← him, Finset.sum_map]
      rfl
    _ = -1 := by
      rw [FiniteField.sum_pow_units]
      simp [ZMod.card]

private lemma sum_eval_monic (p : ℕ) [hp : Fact p.Prime]
    (P : (ZMod p)[X]) (hP : P.Monic) (hdeg : P.natDegree = p - 1) :
    ∑ x : ZMod p, P.eval x = -1 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ Finset.range (P.natDegree + 1), ∑ x : ZMod p, P.coeff i * x ^ i) =
        ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * ∑ x : ZMod p, x ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = -1 := by
      rw [hdeg]
      have hrange : Finset.range (p - 1 + 1) = Finset.range (p - 1) ∪ {p - 1} := by
        ext i
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
        omega
      rw [hrange, Finset.sum_union]
      · have hz : ∑ i ∈ Finset.range (p - 1), P.coeff i * ∑ x : ZMod p, x ^ i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by simpa [ZMod.card] using Finset.mem_range.mp hi), mul_zero]
        rw [hz, zero_add, Finset.sum_singleton, sum_pow_card_sub_one p]
        rw [← hdeg, hP.coeff_natDegree]
        simp
      · simp

private noncomputable def fallingPoly (p m : ℕ) : (ZMod p)[X] :=
  ∏ i ∈ Finset.range m, (Polynomial.X - Polynomial.C (i : ZMod p))

private lemma fallingPoly_monic (p m : ℕ) : (fallingPoly p m).Monic := by
  unfold fallingPoly
  apply Finset.prod_induction
  · intro a b ha hb
    exact ha.mul hb
  · exact Polynomial.monic_one
  · intro i hi
    exact Polynomial.monic_X_sub_C _

private lemma fallingPoly_natDegree (p m : ℕ) [Fact p.Prime] :
    (fallingPoly p m).natDegree = m := by
  unfold fallingPoly
  rw [Polynomial.natDegree_prod]
  · simp_rw [Polynomial.natDegree_X_sub_C]
    simp
  · intro i hi
    exact Polynomial.X_sub_C_ne_zero _

private lemma fallingPoly_eval_nat (p m n : ℕ) (h : m ≤ n + 1) :
    (fallingPoly p m).eval (n : ZMod p) = (n.descFactorial m : ZMod p) := by
  rw [fallingPoly, Polynomial.eval_prod, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hin : i ≤ n := by
    have hi' := Finset.mem_range.mp hi
    omega
  rw [Nat.cast_sub hin]

private noncomputable def choosePoly (p m : ℕ) : (ZMod p)[X] :=
  (fallingPoly p m).comp (Polynomial.X ^ 2 + Polynomial.C (m ^ 2 : ZMod p))

private lemma choosePoly_monic (p m : ℕ) [Fact p.Prime] : (choosePoly p m).Monic := by
  apply (fallingPoly_monic p m).comp
  · exact Polynomial.monic_X_pow_add_C (a := (m ^ 2 : ZMod p)) (by norm_num)
  · rw [Polynomial.natDegree_X_pow_add_C]
    norm_num

private lemma choosePoly_natDegree (p m : ℕ) [Fact p.Prime] :
    (choosePoly p m).natDegree = 2 * m := by
  rw [choosePoly, Polynomial.natDegree_comp, fallingPoly_natDegree]
  rw [Polynomial.natDegree_X_pow_add_C]
  omega

private lemma choosePoly_eval (p m a : ℕ) :
    (choosePoly p m).eval (a : ZMod p) =
      (m.factorial : ZMod p) * ((m ^ 2 + a ^ 2).choose m : ZMod p) := by
  rw [choosePoly, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [show (a : ZMod p) ^ 2 + (m ^ 2 : ZMod p) = ((m ^ 2 + a ^ 2 : ℕ) : ZMod p) by push_cast; ring]
  rw [fallingPoly_eval_nat p m (m ^ 2 + a ^ 2) (by nlinarith [Nat.zero_le a])]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_cast

private lemma sum_choose (p m : ℕ) [hp : Fact p.Prime] (hpm : p = 2 * m + 1) :
    (m.factorial : ZMod p) *
      (∑ a ∈ Finset.range p, ((m ^ 2 + a ^ 2).choose m : ZMod p)) = -1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hdeg : (choosePoly p m).natDegree = p - 1 := by
    rw [choosePoly_natDegree, hpm]
    omega
  have hs := sum_eval_monic p (choosePoly p m) (choosePoly_monic p m) hdeg
  have hsrange : (∑ x : ZMod p, (choosePoly p m).eval x) =
      ∑ a ∈ Finset.range p, (choosePoly p m).eval (a : ZMod p) := by
    apply Finset.sum_bij (fun x _ ↦ x.val)
    · intro x hx
      exact Finset.mem_range.mpr x.val_lt
    · intro x₁ hx₁ x₂ hx₂ he
      exact ZMod.val_injective p he
    · intro a ha
      refine ⟨(a : ZMod p), Finset.mem_univ _, ?_⟩
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
    · intro x hx
      rw [ZMod.natCast_zmod_val]
  rw [hsrange] at hs
  simp_rw [choosePoly_eval] at hs
  rw [← Finset.mul_sum] at hs
  exact hs

private lemma factorial_mul_oddProduct (m : ℕ) :
    m.factorial * (∏ r ∈ Finset.range m, (4 * (r + 1) - 2)) = (2 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, Nat.factorial_succ]
      rw [show 4 * (m + 1) - 2 = 4 * m + 2 by omega]
      calc
        (m + 1) * m.factorial *
            ((∏ x ∈ Finset.range m, (4 * (x + 1) - 2)) * (4 * m + 2)) =
            (m.factorial * ∏ x ∈ Finset.range m, (4 * (x + 1) - 2)) *
              ((m + 1) * (4 * m + 2)) := by ring
        _ = (2 * m).factorial * ((m + 1) * (4 * m + 2)) := by rw [ih]
        _ = (2 * (m + 1)).factorial := by
          rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
            Nat.factorial_succ, Nat.factorial_succ]
          ring

private lemma factorial_mul_oddProduct_mod (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) :
    (m.factorial : ZMod p) *
      (∏ r ∈ Finset.range m, (4 * (r + 1) - 2 : ℕ) : ZMod p) = -1 := by
  rw [← Nat.cast_prod, ← Nat.cast_mul, factorial_mul_oddProduct]
  have heq : 2 * m = p - 1 := by omega
  rw [heq]
  simpa using ZMod.wilsons_lemma p

private noncomputable def gaussPoly (R : Type*) [CommRing R] (p m : ℕ) : R[X] :=
  ∑ a ∈ Finset.range p, Polynomial.X ^ (m ^ 2 + a ^ 2)

private noncomputable def oddProductPoly (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  ∏ r ∈ Finset.range m, (Polynomial.X ^ (4 * (r + 1) - 2) - 1)

private lemma taylor_gaussPoly_coeff (p m : ℕ) [Fact p.Prime] :
    ((Polynomial.taylor (1 : ZMod p)) (gaussPoly (ZMod p) p m)).coeff m =
      ∑ a ∈ Finset.range p, ((m ^ 2 + a ^ 2).choose m : ZMod p) := by
  rw [gaussPoly, map_sum]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp_rw [Polynomial.lcoeff_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Polynomial.taylor_pow, Polynomial.taylor_X]
  simpa using Polynomial.coeff_X_add_one_pow (ZMod p) (m ^ 2 + a ^ 2) m

private noncomputable def geomFactor (R : Type*) [CommRing R] (e : ℕ) : R[X] :=
  ∑ i ∈ Finset.range e, (Polynomial.X + 1) ^ i

private lemma shifted_pow_sub_one (R : Type*) [CommRing R] (e : ℕ) :
    (Polynomial.X + 1 : R[X]) ^ e - 1 = Polynomial.X * geomFactor R e := by
  rw [geomFactor]
  have h := geom_sum_mul (Polynomial.X + 1 : R[X]) e
  rw [show (Polynomial.X + 1 : R[X]) - 1 = Polynomial.X by ring] at h
  rw [mul_comm] at h
  exact h.symm

private lemma taylor_oddProductPoly (p m : ℕ) :
    (Polynomial.taylor (1 : ZMod p)) (oddProductPoly (ZMod p) m) =
      Polynomial.X ^ m *
        ∏ r ∈ Finset.range m, geomFactor (ZMod p) (4 * (r + 1) - 2) := by
  rw [oddProductPoly]
  have aux (s : Finset ℕ) : (Polynomial.taylor (1 : ZMod p))
      (∏ r ∈ s, (Polynomial.X ^ (4 * (r + 1) - 2) - 1)) =
      Polynomial.X ^ s.card *
        ∏ r ∈ s, geomFactor (ZMod p) (4 * (r + 1) - 2) := by
    induction s using Finset.induction_on with
    | empty => simp [Polynomial.taylor_one]
    | @insert r s hr ih =>
        rw [Finset.prod_insert hr, Finset.prod_insert hr, Finset.card_insert_of_notMem hr,
          Polynomial.taylor_mul, ih]
        rw [map_sub, Polynomial.taylor_pow, Polynomial.taylor_X, Polynomial.taylor_one]
        simp only [Polynomial.C_1]
        rw [shifted_pow_sub_one]
        rw [pow_succ]
        ring
  simpa using aux (Finset.range m)

private lemma geomFactor_coeff_zero (p e : ℕ) :
    (geomFactor (ZMod p) e).coeff 0 = (e : ZMod p) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, geomFactor, Polynomial.eval_finset_sum]
  simp

private lemma taylor_oddProductPoly_coeff (p m : ℕ) :
    ((Polynomial.taylor (1 : ZMod p)) (oddProductPoly (ZMod p) m)).coeff m =
      ∏ r ∈ Finset.range m, (4 * (r + 1) - 2 : ℕ) := by
  rw [taylor_oddProductPoly]
  have hcoeff := Polynomial.coeff_X_pow_mul
    (∏ r ∈ Finset.range m, geomFactor (ZMod p) (4 * (r + 1) - 2)) m 0
  rw [zero_add] at hcoeff
  rw [hcoeff]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  rw [Nat.cast_prod]

  simp_rw [← Polynomial.coeff_zero_eq_eval_zero, geomFactor_coeff_zero]

private lemma wrongSign_taylor_coeff_ne_zero (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) :
    ((Polynomial.taylor (1 : ZMod p))
      (gaussPoly (ZMod p) p m + oddProductPoly (ZMod p) m)).coeff m ≠ 0 := by
  have hc : ((Polynomial.taylor (1 : ZMod p))
      (gaussPoly (ZMod p) p m + oddProductPoly (ZMod p) m)).coeff m =
      (∑ a ∈ Finset.range p, ((m ^ 2 + a ^ 2).choose m : ZMod p)) +
      ∏ r ∈ Finset.range m, (4 * (r + 1) - 2 : ℕ) := by
    rw [map_add, Polynomial.coeff_add, taylor_gaussPoly_coeff,
      taylor_oddProductPoly_coeff]
  intro hz
  rw [hc] at hz
  have hmul := congrArg (fun z : ZMod p ↦ (m.factorial : ZMod p) * z) hz
  change (m.factorial : ZMod p) *
      ((∑ a ∈ Finset.range p, ((m ^ 2 + a ^ 2).choose m : ZMod p)) +
        ∏ r ∈ Finset.range m, (4 * (r + 1) - 2 : ℕ)) =
      (m.factorial : ZMod p) * 0 at hmul
  rw [Nat.cast_prod] at hmul

  rw [mul_zero, mul_add, sum_choose p m hpm,
    factorial_mul_oddProduct_mod p m hpm] at hmul
  have hpne2 : p ≠ 2 := by omega
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2'
    · exact hp.out.ne_one hp1
    · exact hpne2 hp2'
  apply hp2
  calc
    (2 : ZMod p) = -(-1 + -1) := by ring
    _ = 0 := by rw [hmul, neg_zero]

private lemma cyclotomic_mod_prime (p : ℕ) [hp : Fact p.Prime] :
    Polynomial.cyclotomic p (ZMod p) =
      (Polynomial.X - 1) ^ (p - 1) := by
  apply mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : ZMod p))
  calc
    Polynomial.cyclotomic p (ZMod p) * (Polynomial.X - Polynomial.C 1) =
        Polynomial.X ^ p - 1 := by
          simpa only [Polynomial.C_1] using
            Polynomial.cyclotomic_prime_mul_X_sub_one (ZMod p) p
    _ = (Polynomial.X - Polynomial.C 1) ^ p := by
          simpa only [one_pow, Polynomial.C_1] using
            (sub_pow_char Polynomial.X (1 : (ZMod p)[X])).symm
    _ = (Polynomial.X - 1) ^ (p - 1) *
        (Polynomial.X - Polynomial.C 1) := by
          simp only [Polynomial.C_1]
          rw [← pow_succ]
          congr 2
          exact (Nat.sub_add_cancel hp.out.one_le).symm

private lemma no_wrong_sign (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    Polynomial.eval ζ
      (Polynomial.map (Int.castRingHom ℂ)
        (gaussPoly ℤ p m + oddProductPoly ℤ m)) ≠ 0 := by
  intro heval
  let U : ℤ[X] := gaussPoly ℤ p m + oddProductPoly ℤ m
  have hUeval : (Polynomial.aeval ζ) U = 0 := by
    simpa [U, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using heval
  have hdiv : Polynomial.cyclotomic p ℤ ∣ U := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ hp.out.pos]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hp.out.pos) hUeval
  have hdiv' := Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdiv
  rw [Polynomial.map_cyclotomic] at hdiv'
  have hmapU : Polynomial.map (Int.castRingHom (ZMod p)) U =
      gaussPoly (ZMod p) p m + oddProductPoly (ZMod p) m := by
    simp only [U, gaussPoly, oddProductPoly, Polynomial.map_add]
    simp_rw [Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rw [hmapU, cyclotomic_mod_prime] at hdiv'
  rcases hdiv' with ⟨Q, hQ⟩
  have htdiv : Polynomial.X ^ (p - 1) ∣
      (Polynomial.taylor (1 : ZMod p))
        (gaussPoly (ZMod p) p m + oddProductPoly (ZMod p) m) := by
    refine ⟨(Polynomial.taylor (1 : ZMod p)) Q, ?_⟩
    rw [hQ, Polynomial.taylor_mul, Polynomial.taylor_pow]
    rw [map_sub, Polynomial.taylor_X, Polynomial.taylor_one]
    simp
  have hmpos : 0 < m := by
    by_contra hm
    have : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    norm_num at hpm
    exact hp.out.ne_one hpm
  have hmlt : m < p - 1 := by omega
  have hzcoeff := (Polynomial.X_pow_dvd_iff.mp htdiv m hmlt)
  exact wrongSign_taylor_coeff_ne_zero p m hpm hzcoeff

private lemma sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M]
    (p : ℕ) [NeZero p] (f : ℕ → M) (g : ZMod p → M)
    (hfg : ∀ a, f a = g (a : ZMod p)) :
    ∑ a ∈ Finset.range p, f a = ∑ x : ZMod p, g x := by
  symm
  apply Finset.sum_bij (fun x _ ↦ x.val)
  · intro x hx
    exact Finset.mem_range.mpr x.val_lt
  · intro x₁ hx₁ x₂ hx₂ he
    exact ZMod.val_injective p he
  · intro a ha
    refine ⟨(a : ZMod p), Finset.mem_univ _, ?_⟩
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro x hx
    rw [hfg, ZMod.natCast_zmod_val]

private lemma sum_square_addChar_eq_gaussSum (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (∑ x : ZMod p, ζ ^ (x ^ 2).val) =
      gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        (AddChar.zmodChar p hζ.pow_eq_one) := by
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζ.pow_eq_one
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  calc
    (∑ x : ZMod p, ζ ^ (x ^ 2).val) = ∑ x : ZMod p, ψ (x ^ 2) := by rfl
    _ = ∑ y : ZMod p, ∑ x : {x : ZMod p // x ^ 2 = y}, ψ (x ^ 2) := by
      symm
      exact Fintype.sum_fiberwise (fun x : ZMod p ↦ x ^ 2) (fun x ↦ ψ (x ^ 2))
    _ = ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) + 1 : ℂ) * ψ y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hconst : ∀ x : {x : ZMod p // x ^ 2 = y}, ψ (x ^ 2) = ψ y := by
        intro x
        rw [x.property]
      rw [Finset.sum_congr rfl (fun x hx ↦ hconst x), Finset.sum_const,
        nsmul_eq_mul]
      congr 1
      rw [Finset.card_univ]
      have hcard : Fintype.card {x : ZMod p // x ^ 2 = y} =
          {x : ZMod p | x ^ 2 = y}.toFinset.card :=
        (Set.toFinset_card {x : ZMod p | x ^ 2 = y}).symm
      rw [hcard]
      exact_mod_cast quadraticChar_card_sqrts hchar y
    _ = (∑ y : ZMod p, χ y * ψ y) + ∑ y : ZMod p, ψ y := by
      have hχ (y : ZMod p) : χ y = ((quadraticChar (ZMod p) y : ℤ) : ℂ) := rfl
      simp only [hχ, Int.cast_add, Int.cast_one, add_mul, one_mul,
        Finset.sum_add_distrib]
    _ = gaussSum χ ψ := by
      have hψprim := AddChar.zmodChar_primitive_of_primitive_root p hζ
      have hψne : ψ ≠ 1 := by
        intro he
        have hone : ψ (1 : ZMod p) = 1 := by rw [he]; rfl
        have h10 : (1 : ZMod p) = 0 :=
          (hψprim.zmod_char_eq_one_iff p (1 : ZMod p)).mp hone
        exact one_ne_zero h10
      rw [AddChar.sum_eq_zero_of_ne_one hψne, add_zero]
      rfl

private lemma gaussPoly_square (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (Polynomial.eval ζ (gaussPoly ℂ p m)) ^ 2 =
      ζ ^ (2 * m ^ 2) * ((-1 : ℂ) ^ m * p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpne2 : p ≠ 2 := by omega
  have hrange : Polynomial.eval ζ (gaussPoly ℂ p m) =
      ζ ^ (m ^ 2) * ∑ x : ZMod p, ζ ^ (x ^ 2).val := by
    rw [gaussPoly, Polynomial.eval_finset_sum, Finset.mul_sum]
    apply sum_range_eq_sum_zmod p
    intro a
    rw [Polynomial.eval_pow, Polynomial.eval_X, pow_add]
    congr 1
    rw [pow_eq_pow_mod (a ^ 2) hζ.pow_eq_one]
    congr 1
    simp [pow_two, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod]
  rw [hrange, mul_pow, sum_square_addChar_eq_gaussSum p hpne2 hζ]
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζ.pow_eq_one
  have hchar : ringChar (ZMod p) ≠ 2 := by simpa [ZMod.ringChar_zmod_n] using hpne2
  have hχne : χ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℂ)))).mpr
      (quadraticChar_ne_one hchar)
  have hs := gaussSum_sq hχne ((quadraticChar_isQuadratic (ZMod p)).comp _)
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)
  rw [hs]
  simp only [χ, MulChar.ringHomComp_apply]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcard4 : (Fintype.card (ZMod p) : ZMod 4) = (p : ZMod 4) := by
    exact congrArg (fun n : ℕ ↦ (n : ZMod 4)) hcard
  have hpodd : p % 2 = 1 := by omega
  rw [quadraticChar_neg_one hchar, hcard4, ZMod.χ₄_eq_neg_one_pow hpodd]
  rw [hcard]
  have hpdiv : p / 2 = m := by omega
  rw [hpdiv]
  simp only [map_pow, map_neg, map_one]
  rw [← pow_mul]
  congr 2
  omega


private def signedOdd (p m : ℕ) : Fin m ⊕ Fin m → ZMod p
  | Sum.inl r => (2 : ZMod p) * (2 * r.val + 1 : ℕ)
  | Sum.inr r => -((2 : ZMod p) * (2 * r.val + 1 : ℕ))

private lemma two_ne_zero_zmod (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2
  · exact hp.out.ne_one hp1
  · omega

private lemma signedOdd_ne_zero (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (s : Fin m ⊕ Fin m) : signedOdd p m s ≠ 0 := by
  have h2 := two_ne_zero_zmod p m hpm
  have hodd (r : Fin m) : ((2 * r.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 * r.val + 1 := (ZMod.natCast_eq_zero_iff _ p).mp hz
    have hle : p ≤ 2 * r.val + 1 := Nat.le_of_dvd (by omega) hd
    omega
  rcases s with r | r
  · exact mul_ne_zero h2 (hodd r)
  · exact neg_ne_zero.mpr (mul_ne_zero h2 (hodd r))

private lemma signedOdd_injective (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) : Function.Injective (signedOdd p m) := by
  have h2 := two_ne_zero_zmod p m hpm
  have hlt (r : Fin m) : 2 * r.val + 1 < p := by omega
  have same {r s : Fin m}
      (h : ((2 * r.val + 1 : ℕ) : ZMod p) = ((2 * s.val + 1 : ℕ) : ZMod p)) : r = s := by
    apply Fin.ext
    have hv := congrArg ZMod.val h
    rw [ZMod.val_cast_of_lt (hlt r), ZMod.val_cast_of_lt (hlt s)] at hv
    omega
  have cross {r s : Fin m}
      (h : ((2 * r.val + 1 : ℕ) : ZMod p) = -((2 * s.val + 1 : ℕ) : ZMod p)) : False := by
    have hz : ((2 * r.val + 1 + (2 * s.val + 1) : ℕ) : ZMod p) = 0 := by
      calc
        ((2 * r.val + 1 + (2 * s.val + 1) : ℕ) : ZMod p) =
            ((2 * r.val + 1 : ℕ) : ZMod p) +
              ((2 * s.val + 1 : ℕ) : ZMod p) := by push_cast; rfl
        _ = -((2 * s.val + 1 : ℕ) : ZMod p) +
              ((2 * s.val + 1 : ℕ) : ZMod p) := by rw [h]
        _ = 0 := neg_add_cancel _
    have hd : p ∣ 2 * r.val + 1 + (2 * s.val + 1) :=
      (ZMod.natCast_eq_zero_iff _ p).mp hz
    have hsumpos : 0 < 2 * r.val + 1 + (2 * s.val + 1) := by omega
    have hple : p ≤ 2 * r.val + 1 + (2 * s.val + 1) :=
      Nat.le_of_dvd hsumpos hd
    have hsumlt : 2 * r.val + 1 + (2 * s.val + 1) < 2 * p := by omega
    have hdiv : (2 * r.val + 1 + (2 * s.val + 1)) / p = 1 := by
      exact Nat.div_eq_of_lt_le (by simpa using hple) (by simpa using hsumlt)
    have heq : p = 2 * r.val + 1 + (2 * s.val + 1) :=
      Nat.eq_of_dvd_of_div_eq_one hd hdiv
    omega
  intro a b hab
  rcases a with r | r <;> rcases b with s | s
  · congr 1
    apply same
    apply mul_left_cancel₀ h2
    change (2 : ZMod p) * ((2 * r.val + 1 : ℕ) : ZMod p) =
      (2 : ZMod p) * ((2 * s.val + 1 : ℕ) : ZMod p) at hab
    exact hab
  · exfalso
    apply cross (r := r) (s := s)
    apply mul_left_cancel₀ h2
    change (2 : ZMod p) * ((2 * r.val + 1 : ℕ) : ZMod p) =
      -((2 : ZMod p) * ((2 * s.val + 1 : ℕ) : ZMod p)) at hab
    rw [mul_neg]
    exact hab
  · exfalso
    apply cross (r := s) (s := r)
    apply mul_left_cancel₀ h2
    change -((2 : ZMod p) * ((2 * r.val + 1 : ℕ) : ZMod p)) =
      (2 : ZMod p) * ((2 * s.val + 1 : ℕ) : ZMod p) at hab
    rw [mul_neg]
    exact hab.symm
  · congr 1
    apply same
    apply mul_left_cancel₀ h2
    change -((2 : ZMod p) * ((2 * r.val + 1 : ℕ) : ZMod p)) =
      -((2 : ZMod p) * ((2 * s.val + 1 : ℕ) : ZMod p)) at hab
    exact neg_injective hab

private noncomputable def signedOddEquiv (p m : ℕ) [Fact p.Prime]
    (hpm : p = 2 * m + 1) :
    (Fin m ⊕ Fin m) ≃ {x : ZMod p // x ≠ 0} := by
  let f : Fin m ⊕ Fin m → {x : ZMod p // x ≠ 0} :=
    fun s ↦ ⟨signedOdd p m s, signedOdd_ne_zero p m hpm s⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro a b h
    exact signedOdd_injective p m hpm (Subtype.ext_iff.mp h)
  · simp [Fintype.card_subtype_compl, ZMod.card, hpm]
    omega

private lemma prod_nonzero_zmod (p : ℕ) [hp : Fact p.Prime]
    (hpodd : Odd p) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (∏ x : {x : ZMod p // x ≠ 0}, (ζ ^ x.val.val - 1)) = p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have heq : (∏ x : {x : ZMod p // x ≠ 0}, (ζ ^ x.val.val - 1)) =
      ∏ k ∈ Finset.range (p - 1), (ζ ^ (k + 1) - 1) := by
    apply Finset.prod_bij (fun x _ ↦ x.val.val - 1)
    · intro x hx
      have xpos : 0 < x.val.val := ZMod.val_pos.mpr x.property
      have xlt : x.val.val < p := x.val.val_lt
      exact Finset.mem_range.mpr (by omega : x.val.val - 1 < p - 1)
    · intro x₁ hx₁ x₂ hx₂ he
      apply Subtype.ext
      apply ZMod.val_injective p
      have h1 : 0 < x₁.val.val := ZMod.val_pos.mpr x₁.property
      have h2 : 0 < x₂.val.val := ZMod.val_pos.mpr x₂.property
      omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklt : k + 1 < p := by omega
      let x : {x : ZMod p // x ≠ 0} :=
        ⟨(k + 1 : ℕ), by
          intro hz
          have hv := congrArg ZMod.val hz
          rw [ZMod.val_cast_of_lt hklt, ZMod.val_zero] at hv
          omega⟩
      refine ⟨x, Finset.mem_univ _, ?_⟩
      dsimp [x]

      change ((((k + 1 : ℕ) : ZMod p).val)) - 1 = k
      rw [ZMod.val_cast_of_lt hklt]
      omega
    · intro x hx
      have xpos : 0 < x.val.val := ZMod.val_pos.mpr x.property
      congr 2
      omega
  rw [heq]
  have heven : Even (p - 1) := by
    rcases hpodd with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    omega
  have hnat : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
  have hζ' : IsPrimitiveRoot ζ ((p - 1) + 1) := by
    rw [hnat]
    exact hζ
  have hprod := hζ'.prod_pow_sub_one_eq_order
  rw [heven.neg_one_pow, one_mul] at hprod
  calc
    (∏ k ∈ Finset.range (p - 1), (ζ ^ (k + 1) - 1)) =
        ((p - 1 : ℕ) : ℂ) + 1 := hprod
    _ = p := by
      norm_cast

private lemma paired_oddProduct (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (∏ r : Fin m, (ζ ^ (4 * (r.val + 1) - 2) - 1)) *
      (∏ r : Fin m, ((ζ⁻¹) ^ (4 * (r.val + 1) - 2) - 1)) = p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζ.pow_eq_one
  let e := signedOddEquiv p m hpm
  have heq : (∏ s : Fin m ⊕ Fin m, (ψ (signedOdd p m s) - 1)) =
      ∏ x : {x : ZMod p // x ≠ 0}, (ψ x.val - 1) := by
    apply Fintype.prod_equiv e
    intro s
    rfl
  rw [Fintype.prod_sum_type] at heq
  have hleft (r : Fin m) : ψ (signedOdd p m (Sum.inl r)) =
      ζ ^ (4 * (r.val + 1) - 2) := by
    have he : 4 * (r.val + 1) - 2 = 2 * (2 * r.val + 1) := by omega
    rw [he]
    rw [show signedOdd p m (Sum.inl r) =
        ((2 * (2 * r.val + 1) : ℕ) : ZMod p) by
          simp only [signedOdd]
          push_cast
          rfl]
    exact AddChar.zmodChar_apply' hζ.pow_eq_one _
  have hright (r : Fin m) : ψ (signedOdd p m (Sum.inr r)) =
      (ζ⁻¹) ^ (4 * (r.val + 1) - 2) := by
    have he : 4 * (r.val + 1) - 2 = 2 * (2 * r.val + 1) := by omega
    rw [he]
    rw [show signedOdd p m (Sum.inr r) =
        -((2 * (2 * r.val + 1) : ℕ) : ZMod p) by
          simp only [signedOdd]
          push_cast
          rfl]
    rw [AddChar.map_neg_eq_inv, AddChar.zmodChar_apply', inv_pow]
  simp_rw [hleft, hright] at heq
  calc
    (∏ r : Fin m, (ζ ^ (4 * (r.val + 1) - 2) - 1)) *
        (∏ r : Fin m, ((ζ⁻¹) ^ (4 * (r.val + 1) - 2) - 1)) =
        ∏ x : {x : ZMod p // x ≠ 0}, (ψ x.val - 1) := heq
    _ = ∏ x : {x : ZMod p // x ≠ 0}, (ζ ^ x.val.val - 1) := by
      apply Finset.prod_congr rfl
      intro x hx
      rfl
    _ = p := prod_nonzero_zmod p ⟨m, hpm⟩ hζ

private lemma sum_oddExponents (m : ℕ) :
    ∑ r ∈ Finset.range m, (4 * (r + 1) - 2) = 2 * m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 4 * (m + 1) - 2 = 4 * m + 2 by omega]
      ring

private lemma oddFactor_relation {ζ : ℂ} (hζ : ζ ≠ 0) (e : ℕ) :
    ζ ^ e - 1 = -ζ ^ e * ((ζ⁻¹) ^ e - 1) := by
  rw [inv_pow]
  field_simp [pow_ne_zero e hζ]
  ring

private lemma oddProductPoly_square (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (Polynomial.eval ζ (oddProductPoly ℂ m)) ^ 2 =
      ζ ^ (2 * m ^ 2) * ((-1 : ℂ) ^ m * p) := by
  have hζne : ζ ≠ 0 := hζ.ne_zero hp.out.ne_zero
  let R : ℂ := ∏ r ∈ Finset.range m, (ζ ^ (4 * (r + 1) - 2) - 1)
  let N : ℂ := ∏ r ∈ Finset.range m, ((ζ⁻¹) ^ (4 * (r + 1) - 2) - 1)
  have heval : Polynomial.eval ζ (oddProductPoly ℂ m) = R := by
    rw [oddProductPoly, Polynomial.eval_prod]
    simp [R]
  have hpair : R * N = p := by
    have h := paired_oddProduct p m hpm hζ
    have hR : (∏ r : Fin m, (ζ ^ (4 * (r.val + 1) - 2) - 1)) = R := by
      exact Fin.prod_univ_eq_prod_range
        (fun r : ℕ ↦ ζ ^ (4 * (r + 1) - 2) - 1) m
    have hN : (∏ r : Fin m, ((ζ⁻¹) ^ (4 * (r.val + 1) - 2) - 1)) = N := by
      exact Fin.prod_univ_eq_prod_range
        (fun r : ℕ ↦ (ζ⁻¹) ^ (4 * (r + 1) - 2) - 1) m
    rw [hR, hN] at h
    exact h
  have hnegprod :
      (∏ r ∈ Finset.range m, (-ζ ^ (4 * (r + 1) - 2))) =
        (-1 : ℂ) ^ m * ζ ^ (2 * m ^ 2) := by
    rw [show (∏ r ∈ Finset.range m, (-ζ ^ (4 * (r + 1) - 2))) =
        (∏ _r ∈ Finset.range m, (-1 : ℂ)) *
          ∏ r ∈ Finset.range m, ζ ^ (4 * (r + 1) - 2) by
      rw [← Finset.prod_mul_distrib]
      simp]
    rw [Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum,
      sum_oddExponents]
  have hrel : R = (-1 : ℂ) ^ m * ζ ^ (2 * m ^ 2) * N := by
    dsimp only [R, N]
    simp_rw [oddFactor_relation hζne]
    rw [Finset.prod_mul_distrib, hnegprod]
  rw [heval, pow_two]
  nth_rewrite 2 [hrel]
  calc
    R * ((-1 : ℂ) ^ m * ζ ^ (2 * m ^ 2) * N) =
        ζ ^ (2 * m ^ 2) * ((-1 : ℂ) ^ m * (R * N)) := by ring
    _ = ζ ^ (2 * m ^ 2) * ((-1 : ℂ) ^ m * p) := by rw [hpair]


private lemma map_gaussPoly_int_complex (p m : ℕ) :
    Polynomial.map (Int.castRingHom ℂ) (gaussPoly ℤ p m) = gaussPoly ℂ p m := by
  simp only [gaussPoly, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]

private lemma map_oddProductPoly_int_complex (m : ℕ) :
    Polynomial.map (Int.castRingHom ℂ) (oddProductPoly ℤ m) = oddProductPoly ℂ m := by
  simp only [oddProductPoly, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]

private lemma prime_gauss_product_identity (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    Polynomial.eval ζ (gaussPoly ℂ p m) =
      Polynomial.eval ζ (oddProductPoly ℂ m) := by
  let A := Polynomial.eval ζ (gaussPoly ℂ p m)
  let B := Polynomial.eval ζ (oddProductPoly ℂ m)
  have hs : A ^ 2 = B ^ 2 := by
    rw [gaussPoly_square p m hpm hζ, oddProductPoly_square p m hpm hζ]
  have hz : (A - B) * (A + B) = 0 := by
    calc
      (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hs
  rcases mul_eq_zero.mp hz with hAB | hsum
  · exact sub_eq_zero.mp hAB
  · exfalso
    apply no_wrong_sign p m hpm hζ
    rw [Polynomial.map_add, map_gaussPoly_int_complex,
      map_oddProductPoly_int_complex, Polynomial.eval_add]
    exact hsum

private lemma sum_first_odds (m : ℕ) :
    ∑ r ∈ Finset.range m, (2 * r + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private lemma odd_difference_factor {ζ : ℂ} (hζ : ζ ≠ 0) (o : ℕ) :
    ζ ^ (2 * o) - 1 = ζ ^ o * (ζ ^ o - (ζ⁻¹) ^ o) := by
  rw [pow_mul, pow_two, inv_pow]
  field_simp [pow_ne_zero o hζ]
  ring

private lemma prime_gauss_odd_product (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    (∑ x : ZMod p, ζ ^ (x ^ 2).val) =
      ∏ r ∈ Finset.range m,
        (ζ ^ (2 * r + 1) - (ζ⁻¹) ^ (2 * r + 1)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hζne : ζ ≠ 0 := hζ.ne_zero hp.out.ne_zero
  let G : ℂ := ∑ x : ZMod p, ζ ^ (x ^ 2).val
  let P : ℂ := ∏ r ∈ Finset.range m,
    (ζ ^ (2 * r + 1) - (ζ⁻¹) ^ (2 * r + 1))
  have hA : Polynomial.eval ζ (gaussPoly ℂ p m) = ζ ^ (m ^ 2) * G := by
    rw [gaussPoly, Polynomial.eval_finset_sum, Finset.mul_sum]
    apply sum_range_eq_sum_zmod p
    intro a
    rw [Polynomial.eval_pow, Polynomial.eval_X, pow_add]
    congr 1
    rw [pow_eq_pow_mod (a ^ 2) hζ.pow_eq_one]
    congr 1
    simp [pow_two, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, G]
  have hB : Polynomial.eval ζ (oddProductPoly ℂ m) = ζ ^ (m ^ 2) * P := by
    rw [oddProductPoly, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    have he (r : ℕ) : 4 * (r + 1) - 2 = 2 * (2 * r + 1) := by omega
    simp_rw [he, odd_difference_factor hζne]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_first_odds]
  have h := prime_gauss_product_identity p m hpm hζ
  rw [hA, hB] at h
  have hpw : ζ ^ (m ^ 2) ≠ 0 := pow_ne_zero _ hζne
  exact (mul_left_cancel₀ hpw h)

private lemma exp_I_sub_inv (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) -
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      ((2 * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [← Complex.exp_neg]
  rw [Complex.exp_mul_I]
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I]
  have hcos (x : ℝ) : Complex.cos (x : ℂ) = (Real.cos x : ℂ) := by
    apply Complex.ext <;> simp
  have hsin (x : ℝ) : Complex.sin (x : ℂ) = (Real.sin x : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcos, hsin, hcos, hsin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private noncomputable def canonicalRoot (p : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / p)

private lemma canonicalRoot_pow (p o : ℕ) :
    canonicalRoot p ^ o =
      Complex.exp ((((2 * Real.pi * o / p : ℝ) : ℂ) * Complex.I)) := by
  rw [canonicalRoot, ← Complex.exp_nat_mul]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Nat.cast_ofNat, Nat.cast_mul]
  ring

private lemma canonicalRoot_odd_factor (p o : ℕ) :
    canonicalRoot p ^ o - (canonicalRoot p)⁻¹ ^ o =
      ((2 * Real.sin (2 * Real.pi * o / p) : ℝ) : ℂ) * Complex.I := by
  rw [inv_pow, canonicalRoot_pow]
  exact exp_I_sub_inv (2 * Real.pi * o / p)

private lemma canonical_sin_pos (p m r : ℕ) (hpm : p = 2 * m + 1)
    (hr : r < m - m / 2) :
    0 < Real.sin (2 * Real.pi * (2 * r + 1) / p) := by
  have hpN : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpN
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ hpR]
    have hn : 2 * (2 * r + 1) < p := by omega
    have hnR : (2 * (2 * r + 1) : ℝ) < p := by exact_mod_cast hn
    nlinarith [Real.pi_pos]

private lemma canonical_sin_neg (p m r : ℕ) (hpm : p = 2 * m + 1)
    (hrlo : m - m / 2 ≤ r) (hrhi : r < m) :
    Real.sin (2 * Real.pi * (2 * r + 1) / p) < 0 := by
  have hpN : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpN
  let x : ℝ := 2 * Real.pi * (2 * r + 1) / p
  have hxpi : Real.pi < x := by
    dsimp only [x]
    rw [lt_div_iff₀ hpR]
    have hn : p < 2 * (2 * r + 1) := by omega
    have hnR : (p : ℝ) < 2 * (2 * r + 1) := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hx2pi : x < 2 * Real.pi := by
    dsimp only [x]
    rw [div_lt_iff₀ hpR]
    have hn : 2 * r + 1 < p := by omega
    have hnR : (2 * r + 1 : ℝ) < p := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hpos : 0 < Real.sin (x - Real.pi) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  rw [Real.sin_sub_pi] at hpos
  linarith

private lemma canonical_sine_product_pos (p m : ℕ) (hpm : p = 2 * m + 1) :
    0 < (-1 : ℝ) ^ (m / 2) *
      ∏ r ∈ Finset.range m, (2 * Real.sin (2 * Real.pi * (2 * r + 1) / p)) := by
  let q := m / 2
  let t := m - q
  let f : ℕ → ℝ := fun r ↦ 2 * Real.sin (2 * Real.pi * (2 * r + 1) / p)
  have hqm : q ≤ m := by dsimp [q]; omega
  have htq : t + q = m := Nat.sub_add_cancel hqm
  have hpos1 : 0 < ∏ r ∈ Finset.range t, f r := by
    apply Finset.prod_pos
    intro r hr
    have hrt : r < t := Finset.mem_range.mp hr
    dsimp only [f]
    have hs := canonical_sin_pos p m r hpm (by simpa [t, q] using hrt)
    positivity
  have hpos2 : 0 < ∏ r ∈ Finset.range q, (-f (t + r)) := by
    apply Finset.prod_pos
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hlo : t ≤ t + r := Nat.le_add_right _ _
    have hhi : t + r < m := by omega
    dsimp only [f]
    have hs := canonical_sin_neg p m (t + r) hpm
      (by simpa [t, q] using hlo) hhi
    nlinarith
  have hnegprod :
      (∏ r ∈ Finset.range q, (-f (t + r))) =
        (-1 : ℝ) ^ q * ∏ r ∈ Finset.range q, f (t + r) := by
    rw [show (∏ r ∈ Finset.range q, (-f (t + r))) =
        (∏ _r ∈ Finset.range q, (-1 : ℝ)) *
          ∏ r ∈ Finset.range q, f (t + r) by
      rw [← Finset.prod_mul_distrib]
      simp]
    rw [Finset.prod_const, Finset.card_range]
  change 0 < (-1 : ℝ) ^ q * ∏ r ∈ Finset.range m, f r
  rw [← htq, Finset.prod_range_add]
  calc
    0 < (∏ r ∈ Finset.range t, f r) *
        (∏ r ∈ Finset.range q, (-f (t + r))) := mul_pos hpos1 hpos2
    _ = (-1 : ℝ) ^ q *
        ((∏ r ∈ Finset.range t, f r) *
          ∏ r ∈ Finset.range q, f (t + r)) := by rw [hnegprod]; ring

private lemma canonical_gauss_eq_sine_prod (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) :
    (∑ x : ZMod p, canonicalRoot p ^ (x ^ 2).val) =
      ((∏ r ∈ Finset.range m,
        (2 * Real.sin (2 * Real.pi * (2 * r + 1) / p)) : ℝ) : ℂ) *
          Complex.I ^ m := by
  have hprim : IsPrimitiveRoot (canonicalRoot p) p := by
    exact Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  rw [prime_gauss_odd_product p m hpm hprim]
  simp_rw [canonicalRoot_odd_factor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  congr 1
  norm_cast

private lemma canonical_gauss_even_re_pos (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Even m) :
    0 < (∑ x : ZMod p, canonicalRoot p ^ (x ^ 2).val).re := by
  obtain ⟨q, rfl⟩ := hm
  let S : ℝ := ∏ r ∈ Finset.range (q + q),
    (2 * Real.sin (2 * Real.pi * (2 * r + 1) / p))
  have hS : 0 < (-1 : ℝ) ^ q * S := by
    have h := canonical_sine_product_pos p (q + q) hpm
    have hdiv : (q + q) / 2 = q := by omega
    rw [hdiv] at h
    simpa [S] using h
  rw [canonical_gauss_eq_sine_prod p (q + q) hpm]
  rw [show Complex.I ^ (q + q) = ((-1 : ℝ) ^ q : ℂ) by
    rw [← two_mul, pow_mul, Complex.I_sq]
    norm_cast]
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa [S, mul_comm] using hS

private lemma canonical_gauss_odd_im_pos (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Odd m) :
    0 < (∑ x : ZMod p, canonicalRoot p ^ (x ^ 2).val).im := by
  obtain ⟨q, rfl⟩ := hm
  let S : ℝ := ∏ r ∈ Finset.range (2 * q + 1),
    (2 * Real.sin (2 * Real.pi * (2 * r + 1) / p))
  have hS : 0 < (-1 : ℝ) ^ q * S := by
    have h := canonical_sine_product_pos p (2 * q + 1) hpm
    have hdiv : (2 * q + 1) / 2 = q := by omega
    rw [hdiv] at h
    simpa [S] using h
  rw [canonical_gauss_eq_sine_prod p (2 * q + 1) hpm]
  rw [show Complex.I ^ (2 * q + 1) = ((-1 : ℝ) ^ q : ℂ) * Complex.I by
    rw [pow_succ, pow_mul, Complex.I_sq]
    norm_cast]
  rw [← Complex.ofReal_pow]
  simp only [mul_assoc, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
  simpa only [S, mul_comm, mul_left_comm, mul_assoc] using hS

private lemma zmodChar_canonical_eq_std (p : ℕ) [NeZero p] :
    AddChar.zmodChar p
      (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).pow_eq_one =
        ZMod.stdAddChar := by
  ext x
  rw [← ZMod.natCast_zmod_val x]
  rw [AddChar.zmodChar_apply']
  rw [show (x.val : ZMod p) = ((x.val : ℤ) : ZMod p) by norm_num,
    ZMod.stdAddChar_coe]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private lemma prime_quadratic_even (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Even m) :
    DirichletCharacter.Even
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) :
        DirichletCharacter ℂ p) := by
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := by omega
  have hpdiv : p / 2 = m := by omega
  change χ (-1) = 1
  rw [show χ (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) by rfl,
    quadraticChar_neg_one (by simpa [ZMod.ringChar_zmod_n] using hp2),
    ZMod.card p, ZMod.χ₄_eq_neg_one_pow hpodd, hpdiv, hm.neg_one_pow]
  norm_num

private lemma prime_quadratic_odd (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Odd m) :
    DirichletCharacter.Odd
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) :
        DirichletCharacter ℂ p) := by
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := by omega
  have hpdiv : p / 2 = m := by omega
  change χ (-1) = -1
  rw [show χ (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) by rfl,
    quadraticChar_neg_one (by simpa [ZMod.ringChar_zmod_n] using hp2),
    ZMod.card p, ZMod.χ₄_eq_neg_one_pow hpodd, hpdiv, hm.neg_one_pow]
  norm_num

private lemma complex_eq_sqrt_of_sq_eq {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hz : z ^ 2 = (a : ℂ)) (hzpos : 0 < z.re) :
    z = (Real.sqrt a : ℂ) := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  have hzim : z.im = 0 := by nlinarith
  have hsqrt := Real.sq_sqrt ha
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    nlinarith [Real.sqrt_nonneg a]
  · simp [hzim]

private lemma complex_eq_I_sqrt_of_sq_eq_neg {z : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hz : z ^ 2 = -(a : ℂ)) (hzpos : 0 < z.im) :
    z = (Real.sqrt a : ℂ) * Complex.I := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im] at hre him
  have hzre : z.re = 0 := by nlinarith
  have hsqrt := Real.sq_sqrt ha
  apply Complex.ext
  · simp [hzre]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
    nlinarith [Real.sqrt_nonneg a]

private lemma prime_gaussSum_even_eq_sqrt (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Even m) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        ZMod.stdAddChar = (Real.sqrt p : ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hp2 : p ≠ 2 := by omega
  have hprim : IsPrimitiveRoot (canonicalRoot p) p :=
    Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hid := sum_square_addChar_eq_gaussSum p hp2 hprim
  rw [zmodChar_canonical_eq_std p] at hid
  have hpos : 0 < (gaussSum χ ZMod.stdAddChar).re := by
    rw [← hid]
    exact canonical_gauss_even_re_pos p m hpm hm
  have hχne : χ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff
      (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℂ)))).mpr
        (quadraticChar_ne_one (by simpa [ZMod.ringChar_zmod_n] using hp2))
  have heven := prime_quadratic_even p m hpm hm
  have hs := gaussSum_sq hχne ((quadraticChar_isQuadratic (ZMod p)).comp _)
    (ZMod.isPrimitive_stdAddChar p)
  rw [heven, one_mul, ZMod.card p] at hs
  exact complex_eq_sqrt_of_sq_eq (by positivity) hs hpos

private lemma prime_gaussSum_odd_eq_I_sqrt (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) (hm : Odd m) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        ZMod.stdAddChar = (Real.sqrt p : ℂ) * Complex.I := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hp2 : p ≠ 2 := by omega
  have hprim : IsPrimitiveRoot (canonicalRoot p) p :=
    Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hid := sum_square_addChar_eq_gaussSum p hp2 hprim
  rw [zmodChar_canonical_eq_std p] at hid
  have hpos : 0 < (gaussSum χ ZMod.stdAddChar).im := by
    rw [← hid]
    exact canonical_gauss_odd_im_pos p m hpm hm
  have hχne : χ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff
      (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℂ)))).mpr
        (quadraticChar_ne_one (by simpa [ZMod.ringChar_zmod_n] using hp2))
  have hodd := prime_quadratic_odd p m hpm hm
  have hs := gaussSum_sq hχne ((quadraticChar_isQuadratic (ZMod p)).comp _)
    (ZMod.isPrimitive_stdAddChar p)
  rw [hodd, neg_one_mul, ZMod.card p] at hs
  exact complex_eq_I_sqrt_of_sq_eq_neg (by positivity) hs hpos

private lemma complex_cpow_half_nat_eq_sqrt (n : ℕ) :
    (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt n : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  change (((n : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt (n : ℝ) : ℂ)
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2 : ℝ)]
  rw [← Real.sqrt_eq_rpow]

lemma prime_quadratic_rootNumber_one (p m : ℕ) [hp : Fact p.Prime]
    (hpm : p = 2 * m + 1) :
    DirichletCharacter.rootNumber
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) :
        DirichletCharacter ℂ p) = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let χ : DirichletCharacter ℂ p :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hsqrt : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hp.out.pos)).ne'
  rcases Nat.even_or_odd m with hm | hm
  · have heven := prime_quadratic_even p m hpm hm
    rw [DirichletCharacter.rootNumber, if_pos heven, pow_zero, div_one,
      prime_gaussSum_even_eq_sqrt p m hpm hm, complex_cpow_half_nat_eq_sqrt,
      div_self hsqrt]
  · have hodd := prime_quadratic_odd p m hpm hm
    rw [DirichletCharacter.rootNumber, if_neg hodd.not_even, pow_one,
      prime_gaussSum_odd_eq_I_sqrt p m hpm hm, complex_cpow_half_nat_eq_sqrt]
    field_simp












end PrimeSign
