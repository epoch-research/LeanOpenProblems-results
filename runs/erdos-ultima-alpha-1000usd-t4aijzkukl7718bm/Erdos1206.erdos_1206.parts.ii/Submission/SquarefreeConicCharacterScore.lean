import Submission.ConicPrimeCharacterScore
import Submission.SquarefreeConicFamily

/-!
The prime-character contrast applied to the explicit squarefree conic family.
Only a finite-prime-block algebraic statement is proved, not a density estimate.
-/
namespace Erdos1206.SquarefreeConicCharacterScore
open Finset ConicPrimeCharacterScore SquarefreeConicFamily

noncomputable def χ (p : ℕ) : ℤ := jacobiSym 948996 p
noncomputable def ψ (p : ℕ) : ℤ := jacobiSym (-3078972) p

private lemma discr (i : Fin 4) :
    (b i : ℤ)^2-4*(a i : ℤ)*(c i : ℤ) =
      if i.val < 2 then 948996 else -3078972 := by
  fin_cases i <;> norm_num [a,b,c]

private lemma leading_regular {p : ℕ} (hp : 1000000000 < p) (i : Fin 4) :
    ¬ (p:ℤ) ∣ (a i : ℤ) := by
  intro hh
  have hd : p ∣ a i := by exact_mod_cast hh
  have ha0 : 0 < a i := by fin_cases i <;> norm_num [a]
  have hbound : a i ≤ 589 := by fin_cases i <;> norm_num [a]
  have := Nat.le_of_dvd ha0 hd
  omega

private lemma discr_regular {p : ℕ} (hp : 1000000000 < p) (i : Fin 4) :
    ¬ (p:ℤ) ∣ (b i : ℤ)^2-4*(a i : ℤ)*(c i : ℤ) := by
  intro hh
  have hh' := Int.natCast_dvd.mp hh
  rw [discr] at hh'
  split_ifs at hh' with hi
  · norm_num at hh'
    have := Nat.le_of_dvd (by decide : 0 < 948996) hh'
    omega
  · norm_num at hh'
    have := Nat.le_of_dvd (by decide : 0 < 3078972) hh'
    omega

lemma symbols {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) :
    (χ p=1 ∨ χ p = -1) ∧ (ψ p=1 ∨ ψ p = -1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hχ : ¬ (p:ℤ) ∣ 948996 := by simpa [discr] using discr_regular hbig 0
  have hψ : ¬ (p:ℤ) ∣ -3078972 := by simpa [discr] using discr_regular hbig 2
  have hx : ((948996:ℤ) : ZMod p) ≠ 0 := fun h =>
    hχ ((ZMod.intCast_zmod_eq_zero_iff_dvd 948996 p).mp h)
  have hy : ((-3078972:ℤ) : ZMod p) ≠ 0 := fun h =>
    hψ ((ZMod.intCast_zmod_eq_zero_iff_dvd (-3078972) p).mp h)
  simp only [χ,ψ,←jacobiSym.legendreSym.to_jacobiSym]
  exact ⟨legendreSym.eq_one_or_neg_one p hx,legendreSym.eq_one_or_neg_one p hy⟩

lemma prime_divisor_symbol {p t u : ℕ} (hp : p.Prime)
    (hbig : 1000000000 < p) (hcop : Nat.Coprime t u) (i : Fin 4)
    (hd : p ∣ F i t u) : (if i.val < 2 then χ p else ψ p)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hf : (p:ℤ) ∣ (a i : ℤ)*(u:ℤ)^2+(b i : ℤ)*u*t+(c i : ℤ)*(t:ℤ)^2 := by
    have hh : (p:ℤ) ∣ (F i t u : ℤ) := by exact_mod_cast hd
    simpa only [F,QuadraticSquarefreeSieve.quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      mul_comm,mul_left_comm,mul_assoc] using hh
  have hh := legendre_discriminant_of_dvd hp (a i) (b i) (c i) hcop.symm
    (leading_regular hbig i) (discr_regular hbig i) hf
  change legendreSym p ((b i : ℤ)^2-4*(a i : ℤ)*(c i : ℤ))=1 at hh
  rw [discr] at hh
  split_ifs at hh ⊢ with hi
  · simpa only [χ,jacobiSym.legendreSym.to_jacobiSym] using hh
  · simpa only [ψ,jacobiSym.legendreSym.to_jacobiSym] using hh

/-- The two different norm fields give an exact nonnegative contrast on
all primitive parameter pairs, including after arbitrary positive dilation. -/
theorem family_contrast (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 1000000000 < p)
    {t u v : ℕ} (hcop : Nat.Coprime t u) (hu : 0 < u) (hv : 0 < v) :
    contrast P (fun p => χ p-ψ p)
      (v*F 0 t u) (v*F 1 t u) (v*F 2 t u) (v*F 3 t u) =
      2*(mixedMass P χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u) : ℤ) := by
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered t u hu
  rw [contrast_dilation P _ ha (ha.trans hab) (ha.trans (hab.trans hbc))
    (ha.trans (hab.trans (hbc.trans hcd))) hv]
  apply contrast_eq_twice_mixedMass
  · intro p hp; exact (symbols (hP p hp).1 (hP p hp).2).1
  · intro p hp; exact (symbols (hP p hp).1 (hP p hp).2).2
  all_goals
    intro p hp hval
    have hdiv := not_not.mp (fun h => hval (Nat.factorization_eq_zero_of_not_dvd h))
    have hh := prime_divisor_symbol (hP p hp).1 (hP p hp).2 hcop _ hdiv
    simpa using hh

#print axioms symbols
#print axioms prime_divisor_symbol
#print axioms family_contrast
end Erdos1206.SquarefreeConicCharacterScore
