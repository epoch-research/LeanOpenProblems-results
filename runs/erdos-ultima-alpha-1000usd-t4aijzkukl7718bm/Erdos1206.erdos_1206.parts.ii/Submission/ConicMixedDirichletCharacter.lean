import Submission.SquarefreeConicCharacterScore

/-! The mixed-prime condition is the negative class of one explicit
nonprincipal real Dirichlet character. No prime-distribution assertion. -/
namespace Erdos1206.ConicMixedDirichletCharacter
open SquarefreeConicCharacterScore

/-- The Jacobi symbol, viewed as a Dirichlet character in its numerator. -/
noncomputable def jacobiChar (N : ℕ) [Fact (1 < N)] : DirichletCharacter ℤ N where
  toFun x := jacobiSym (x.val:ℤ) N
  map_one' := by simp only [ZMod.val_one,Nat.cast_one,jacobiSym.one_left]
  map_mul' x y := by
    rw [ZMod.val_mul,Int.natCast_emod,Int.natCast_mul,←jacobiSym.mod_left,jacobiSym.mul_left]
  map_nonunit' x hx := by
    have hN : N ≠ 0 := by have := Fact.out (p := 1 < N); omega
    letI : NeZero N := ⟨hN⟩
    apply jacobiSym.eq_zero_iff_not_coprime.mpr
    intro hh
    apply hx
    have hc : Nat.Coprime x.val N := by simpa only [Int.gcd_natCast_natCast] using hh
    have hu := (ZMod.isUnit_iff_coprime x.val N).mpr hc
    simpa only [ZMod.natCast_zmod_val] using hu

lemma jacobiChar_natCast (N n : ℕ) [Fact (1 < N)] :
    jacobiChar N (n : ZMod N) = jacobiSym (n:ℤ) N := by
  change jacobiSym ((n:ZMod N).val:ℤ) N = _
  rw [ZMod.val_natCast,Int.natCast_emod,←jacobiSym.mod_left]

private instance : Fact (1 < (27834287:ℕ)) := ⟨by norm_num⟩

noncomputable def eta : DirichletCharacter ℤ 27834287 := jacobiChar 27834287
noncomputable def etaComplex : DirichletCharacter ℂ 27834287 :=
  eta.ringHomComp (Int.castRingHom ℂ)

lemma eta_apply_five : eta (5:ZMod 27834287) = -1 := by
  rw [eta,←Nat.cast_ofNat (R := ZMod 27834287) (n := 5),jacobiChar_natCast]
  norm_num

lemma eta_ne_one : eta ≠ 1 := by
  intro hh
  have hf := eta_apply_five
  rw [hh] at hf
  have hu : IsUnit (5:ZMod 27834287) := by
    exact (ZMod.isUnit_iff_coprime 5 27834287).mpr (by decide)
  simp [MulChar.one_apply hu] at hf

lemma etaComplex_ne_one : etaComplex ≠ 1 := by
  intro hh
  have hv := congrArg (fun f : DirichletCharacter ℂ 27834287 => f (5:ZMod 27834287)) hh
  have hu : IsUnit (5:ZMod 27834287) :=
    (ZMod.isUnit_iff_coprime 5 27834287).mpr (by decide)
  change ((eta (5:ZMod 27834287):ℤ):ℂ) = (1:DirichletCharacter ℂ 27834287) 5 at hv
  rw [eta_apply_five,MulChar.one_apply hu] at hv
  norm_num at hv

lemma product_symbols {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) :
    χ p*ψ p=eta (p:ZMod 27834287) := by
  have hpc : Nat.Coprime p 324 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 324) hd
    omega)
  have hc : Int.gcd 324 p=1 := by
    simpa only [Int.gcd_natCast_natCast] using hpc.symm.gcd_eq_one
  have hfac : (948996:ℤ)*(-3078972)=(324:ℤ)^2*(-27834287) := by norm_num
  rw [χ,ψ,←jacobiSym.mul_left,hfac,jacobiSym.mul_left,jacobiSym.sq_one' hc,one_mul]
  rw [eta,jacobiChar_natCast]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [show (-27834287:ℤ)=-(27834287:ℤ) by rfl,jacobiSym.neg _ hodd]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hp1 | hp3
  · rw [ZMod.χ₄_nat_one_mod_four hp1,one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four' (by decide) hp1
  · have hr := jacobiSym.quadratic_reciprocity_three_mod_four
      (by norm_num : 27834287 % 4=3) hp3
    norm_num only [Nat.cast_ofNat] at hr
    rw [ZMod.χ₄_nat_three_mod_four hp3,hr]
    ring

lemma mixed_iff_eta_neg_one {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) :
    χ p ≠ ψ p ↔ eta (p:ZMod 27834287) = -1 := by
  rw [←product_symbols hp hbig]
  obtain ⟨hx,hy⟩ := symbols hp hbig
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> norm_num [hx,hy]

lemma eta_trichotomy (n : ℕ) :
    eta (n:ZMod 27834287)=0 ∨ eta (n:ZMod 27834287)=1 ∨ eta (n:ZMod 27834287) = -1 := by
  rw [eta,jacobiChar_natCast]
  exact jacobiSym.trichotomy _ _

#print axioms jacobiChar
#print axioms jacobiChar_natCast
#print axioms product_symbols
#print axioms mixed_iff_eta_neg_one
#print axioms eta_trichotomy
#print axioms eta_ne_one
#print axioms etaComplex_ne_one
end Erdos1206.ConicMixedDirichletCharacter
