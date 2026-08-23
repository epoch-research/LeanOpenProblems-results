import FormalConjectures.CRTClassScratch
import FormalConjectures.OddPrimeClassPublic

open Finset
noncomputable section

private def EvalGood (N : ℕ) : Prop :=
  Odd N → ∀ (_hN : NeZero N) (χ : DirichletCharacter ℂ N),
    χ.IsQuadratic → χ.IsPrimitive →
      ∀ a : ℤ, χ (a : ZMod N) = (jacobiSym a N : ℂ)

private lemma evalGood_all : ∀ N, EvalGood N := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he
    intro hodd hN χ hq hprim
    have hp2 : p ≠ 2 := by
      intro h; subst p
      exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow).2 ⟨by decide, he.ne'⟩)) hodd
    letI : Fact p.Prime := ⟨hp⟩
    have he1 := primitive_quadratic_odd_prime_pow_level_one p e hp2 he χ hq hprim
    let P : ℕ → Prop := fun N ↦ ∀ (_hN : NeZero N) (ξ : DirichletCharacter ℂ N),
      ξ.IsQuadratic → ξ.IsPrimitive →
        ∀ a : ℤ, ξ (a : ZMod N) = (jacobiSym a N : ℂ)
    have hlocal : P p := by
      intro hpN ξ hξq hξp
      have heq : ξ = primeQuadratic p := by
        letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
        apply quadratic_character_unique_of_isCyclic hξq (primeQuadratic_quadratic p)
        · exact primitive_ne_one hp.ne_one hξp
        · exact primeQuadratic_ne_one hp2
      subst ξ
      intro a
      simp only [primeQuadratic, MulChar.ringHomComp_apply]
      exact congrArg (Int.castRingHom ℂ) (by
        simpa [legendreSym] using jacobiSym.legendreSym.to_jacobiSym p a)
    have hmod : p ^ e = p := by rw [he1, pow_one]
    exact (Eq.mpr (congrArg P hmod) hlocal) inferInstance χ hq hprim
  · intro h
    exact (Nat.not_odd_zero h).elim
  · intro _h hN χ hq hp a
    have hχ : χ = 1 := Subsingleton.elim _ _
    subst χ
    have hua : IsUnit (a : ZMod 1) := by
      rw [show (a : ZMod 1) = 1 by exact Subsingleton.elim _ _]
      exact isUnit_one
    simp [MulChar.one_apply hua]
  · intro m n hm hn hmn ihm ihn
    intro hodd hN χ hq hp
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    letI : NeZero m := ⟨hm0⟩
    letI : NeZero n := ⟨hn0⟩
    have hom : Odd m := (Nat.odd_mul.mp hodd).1
    have hon : Odd n := (Nat.odd_mul.mp hodd).2
    let α := crtLeft hmn χ
    let β := crtRight hmn χ
    have hαq := crtLeft_quadratic hmn χ hq
    have hβq := crtRight_quadratic hmn χ hq
    have hαp := crtLeft_primitive hmn χ hp
    have hβp := crtRight_primitive hmn χ hp
    have heq := eq_prodChar_crt hmn χ
    intro a
    rw [heq, GlobalSign.prodChar_apply hmn]
    have hcm : (ZMod.cast (a : ZMod (m*n)) : ZMod m) = (a : ZMod m) :=
      ZMod.cast_intCast (dvd_mul_right m n) a
    have hcn : (ZMod.cast (a : ZMod (m*n)) : ZMod n) = (a : ZMod n) :=
      ZMod.cast_intCast (dvd_mul_left n m) a
    rw [hcm, hcn]
    change α (a : ZMod m) * β (a : ZMod n) = _
    rw [ihm hom inferInstance α hαq hαp a, ihn hon inferInstance β hβq hβp a]
    push_cast
    rw [jacobiSym.mul_right' a hm0 hn0]
    exact (map_mul (Int.castRingHom ℂ) _ _).symm


lemma odd_primitive_quadratic_eval {N : ℕ} [NeZero N] (hodd : Odd N)
    (χ : DirichletCharacter ℂ N) (hq : χ.IsQuadratic) (hp : χ.IsPrimitive)
    (a : ℤ) : χ (a : ZMod N) = (jacobiSym a N : ℂ) :=
  evalGood_all N hodd inferInstance χ hq hp a

lemma odd_quadratic_reciprocity {m n : ℕ} [NeZero m] [NeZero n]
    (hom : Odd m) (hon : Odd n) (hcop : m.Coprime n)
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hαq : α.IsQuadratic) (hαp : α.IsPrimitive)
    (hβq : β.IsQuadratic) (hβp : β.IsPrimitive) :
    α (n : ZMod m) * β (m : ZMod n) =
      if α.Odd ∧ β.Odd then -1 else 1 := by
  have hncast : (n : ZMod m) = ((n : ℤ) : ZMod m) := by norm_num
  have hmcast : (m : ZMod n) = ((m : ℤ) : ZMod n) := by norm_num
  rw [hncast, hmcast, odd_primitive_quadratic_eval hom α hαq hαp (n : ℤ),
    odd_primitive_quadratic_eval hon β hβq hβp (m : ℤ)]
  push_cast
  have hj : jacobiSym (m : ℤ) n = 1 ∨ jacobiSym (m : ℤ) n = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    simpa using hcop.gcd_eq_one
  have hprod : jacobiSym (n : ℤ) m * jacobiSym (m : ℤ) n = qrSign m n := by
    rw [jacobiSym.quadratic_reciprocity' hon hom]
    rcases hj with hj | hj <;> rw [hj] <;> ring
  rw [← Int.cast_mul, hprod]
  rcases α.even_or_odd with hαe | hαo
  · rw [if_neg (fun h ↦ (DirichletCharacter.Even.not_odd α hαe) h.1)]
    rw [qrSign]
    have hv := odd_primitive_quadratic_eval hom α hαq hαp (-1)
    have hneg : ((-1 : ℤ) : ZMod m) = (-1 : ZMod m) := by norm_num
    rw [hneg, hαe, jacobiSym.at_neg_one hom] at hv
    have hz : ZMod.χ₄ (m : ZMod 4) = 1 := by exact_mod_cast hv.symm
    rw [hz, jacobiSym.one_left]
    norm_num
  · rcases β.even_or_odd with hβe | hβo
    · rw [if_neg (fun h ↦ (DirichletCharacter.Even.not_odd β hβe) h.2)]
      rw [qrSign]
      have hma := odd_primitive_quadratic_eval hom α hαq hαp (-1)
      have hnegm : ((-1 : ℤ) : ZMod m) = (-1 : ZMod m) := by norm_num
      rw [hnegm, hαo, jacobiSym.at_neg_one hom] at hma
      have hmz : ZMod.χ₄ (m : ZMod 4) = -1 := by exact_mod_cast hma.symm
      rw [hmz, jacobiSym.at_neg_one hon]
      have hnb := odd_primitive_quadratic_eval hon β hβq hβp (-1)
      have hnegn : ((-1 : ℤ) : ZMod n) = (-1 : ZMod n) := by norm_num
      rw [hnegn, hβe, jacobiSym.at_neg_one hon] at hnb
      exact_mod_cast hnb.symm
    · rw [if_pos ⟨hαo, hβo⟩]
      rw [qrSign]
      have hma := odd_primitive_quadratic_eval hom α hαq hαp (-1)
      have hnegm : ((-1 : ℤ) : ZMod m) = (-1 : ZMod m) := by norm_num
      rw [hnegm, hαo, jacobiSym.at_neg_one hom] at hma
      have hmz : ZMod.χ₄ (m : ZMod 4) = -1 := by exact_mod_cast hma.symm
      rw [hmz, jacobiSym.at_neg_one hon]
      have hnb := odd_primitive_quadratic_eval hon β hβq hβp (-1)
      have hnegn : ((-1 : ℤ) : ZMod n) = (-1 : ZMod n) := by norm_num
      rw [hnegn, hβo, jacobiSym.at_neg_one hon] at hnb
      exact_mod_cast hnb.symm

private def RootGood (N : ℕ) : Prop :=
  Odd N → ∀ (_hN : NeZero N) (χ : DirichletCharacter ℂ N),
    χ.IsQuadratic → χ.IsPrimitive → χ.rootNumber = 1

private lemma rootGood_all : ∀ N, RootGood N := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he hodd hN χ hq hprim
    have hp2 : p ≠ 2 := by
      intro h; subst p
      exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow).2 ⟨by decide, he.ne'⟩)) hodd
    letI : Fact p.Prime := ⟨hp⟩
    exact primitive_quadratic_odd_prime_pow_root_one p e hp2 he χ hq hprim
  · intro h
    exact (Nat.not_odd_zero h).elim
  · intro hodd hN χ hq hp
    have hχ : χ = 1 := Subsingleton.elim _ _
    subst χ
    exact DirichletCharacter.rootNumber_modOne 1
  · intro m n hm hn hmn ihm ihn hodd hN χ hq hp
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    letI : NeZero m := ⟨hm0⟩
    letI : NeZero n := ⟨hn0⟩
    have hom : Odd m := (Nat.odd_mul.mp hodd).1
    have hon : Odd n := (Nat.odd_mul.mp hodd).2
    let α := crtLeft hmn χ
    let β := crtRight hmn χ
    have hαq := crtLeft_quadratic hmn χ hq
    have hβq := crtRight_quadratic hmn χ hq
    have hαp := crtLeft_primitive hmn χ hp
    have hβp := crtRight_primitive hmn χ hp
    have hαr := ihm hom inferInstance α hαq hαp
    have hβr := ihn hon inferInstance β hβq hβp
    have hrec := odd_quadratic_reciprocity hom hon hmn α β hαq hαp hβq hβp
    rw [eq_prodChar_crt hmn χ]
    rcases α.even_or_odd with hαe | hαo
    · rcases β.even_or_odd with hβe | hβo
      · apply GlobalSign.rootNumber_prod_even_even hmn hm hn hαp hβp hαq hβq
          hαe hβe hαr hβr
        simpa [DirichletCharacter.Even.not_odd α hαe] using hrec
      · apply GlobalSign.rootNumber_prod_even_odd hmn hm hn hαp hβp hαq hβq
          hαe hβo hαr hβr
        simpa [DirichletCharacter.Even.not_odd α hαe] using hrec
    · rcases β.even_or_odd with hβe | hβo
      · apply GlobalSign.rootNumber_prod_odd_even hmn hm hn hαp hβp hαq hβq
          hαo hβe hαr hβr
        simpa [DirichletCharacter.Even.not_odd β hβe] using hrec
      · apply GlobalSign.rootNumber_prod_odd_odd hmn hm hn hαp hβp hαq hβq
          hαo hβo hαr hβr
        simpa [hαo, hβo] using hrec

lemma odd_primitive_quadratic_rootNumber_one {N : ℕ} [NeZero N] (hodd : Odd N)
    (χ : DirichletCharacter ℂ N) (hq : χ.IsQuadratic) (hp : χ.IsPrimitive) :
    χ.rootNumber = 1 := rootGood_all N hodd inferInstance χ hq hp
