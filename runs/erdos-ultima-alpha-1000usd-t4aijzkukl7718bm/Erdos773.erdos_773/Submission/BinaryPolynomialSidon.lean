import FormalConjecturesUtil

/-!
Binary-coefficient polynomials have Sidon squares in `ℤ[X]`.
This is a formal polynomial statement, not a statement about integer evaluation.
-/
namespace Erdos773.BinaryPolynomialSidon
open Polynomial
noncomputable section

/-- A transversal for reduction modulo two has Sidon squares if the quotient is a domain. -/
theorem transversal_pair_matching
    {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [CharP S 2]
    (f : R →+* S) (hker : ∀ x, f x = 0 → (2 : R) ∣ x)
    {A : Set R} (hinj : Set.InjOn f A)
    {a b c d : R} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (he : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hsum : f a + f b = f c + f d := by
    have hh := congrArg f he
    simp only [map_add, map_pow] at hh
    rw [← CharTwo.add_sq, ← CharTwo.add_sq] at hh
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  have hz : f (a+b-c-d)=0 := by
    simp only [map_sub, map_add]
    linear_combination hsum
  obtain ⟨t, ht⟩ := hker (a+b-c-d) hz
  have hbform : b=c+d-a+2*t := by linear_combination ht
  have htwice : 2*((a-c)*(a-d)+2*t*(c+d-a+t))=0 := by
    rw [hbform] at he
    linear_combination he
  have hhalf : (a-c)*(a-d)+2*t*(c+d-a+t)=0 :=
    (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  have hp : (f a-f c)*(f a-f d)=0 := by
    have hh := congrArg f hhalf
    simpa only [map_add, map_mul, map_sub, map_ofNat, map_zero,
      CharTwo.two_eq_zero, zero_mul, add_zero] using hh
  rcases mul_eq_zero.mp hp with hp | hp
  · have hac : a=c := hinj ha hc (sub_eq_zero.mp hp)
    left
    refine ⟨hac, hinj hb hd ?_⟩
    simpa only [hac, add_right_inj] using hsum
  · have had : a=d := hinj ha hd (sub_eq_zero.mp hp)
    right
    refine ⟨had, hinj hb hc ?_⟩
    rw [had] at hsum
    linear_combination hsum

/-- Every coefficient is zero or one. -/
def Binary (P : ℤ[X]) : Prop := ∀ n, P.coeff n=0 ∨ P.coeff n=1

def reduction : ℤ[X] →+* (ZMod 2)[X] :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod 2))

lemma reduction_coeff (P : ℤ[X]) (n : ℕ) :
    (reduction P).coeff n = (P.coeff n : ZMod 2) := by
  simp [reduction]

lemma reduction_kernel (P : ℤ[X]) (hP : reduction P=0) : (2 : ℤ[X]) ∣ P := by
  have hh : C (2 : ℤ) ∣ P := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    have hc := congrArg (fun Q : (ZMod 2)[X] => Q.coeff n) hP
    dsimp only at hc
    rw [reduction_coeff, coeff_zero] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc
  simpa using hh

lemma reduction_injective_binary : Set.InjOn reduction {P | Binary P} := by
  intro P hP Q hQ he
  ext n
  have hh := congrArg (fun F : (ZMod 2)[X] => F.coeff n) he
  dsimp only at hh
  rw [reduction_coeff, reduction_coeff] at hh
  rcases hP n with hp | hp <;> rcases hQ n with hq | hq <;>
    simp_all

/-- Binary polynomials are matched, as roots, by equality of formal square sums. -/
theorem binary_pair_matching {P Q R S : ℤ[X]}
    (hP : Binary P) (hQ : Binary Q) (hR : Binary R) (hS : Binary S)
    (he : P^2+Q^2=R^2+S^2) :
    (P=R ∧ Q=S) ∨ (P=S ∧ Q=R) :=
  transversal_pair_matching reduction reduction_kernel reduction_injective_binary
    hP hQ hR hS he

/-- The entire infinite set of binary-polynomial square values is Sidon in `ℤ[X]`. -/
theorem binary_squares_sidon : IsSidon ((fun P : ℤ[X] => P^2) '' {P | Binary P}) := by
  intro p hp r hr q hq s hs he
  obtain ⟨P,hP,rfl⟩ := hp
  obtain ⟨Q,hQ,rfl⟩ := hq
  obtain ⟨R,hR,rfl⟩ := hr
  obtain ⟨S,hS,rfl⟩ := hs
  rcases binary_pair_matching hP hQ hR hS he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩

/-- Four short binary words, with coefficients written in increasing powers. -/
def word : Fin 4 → ℤ[X] := ![
  1+X, 1+X+X^3, 1+X+X^2, 1+X^3]

lemma example_binary (i : Fin 4) : Binary (word i) := by
  intro n
  by_cases hn : n≤3
  · interval_cases n <;> fin_cases i <;> norm_num [word, Matrix.cons_val, coeff_one, coeff_X]
  · have h0 : n≠0 := by omega
    have h1 : n≠1 := by omega
    have h2 : n≠2 := by omega
    have h3 : n≠3 := by omega
    fin_cases i <;> simp [word, coeff_one, coeff_X, h0, Ne.symm h1, h2, h3]

/-- The discrepancy is nonzero formally, but vanishes at the integer base two. -/
theorem example_discrepancy :
    word 0^2+word 1^2-word 2^2-word 3^2 =
      X*(X-2)*(X-1)*(X+1) := by
  simp only [word, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

lemma example_values :
    (word 0).eval 2=3 ∧ (word 1).eval 2=11 ∧
    (word 2).eval 2=7 ∧ (word 3).eval 2=9 := by
  change (1+X : ℤ[X]).eval 2=3 ∧ (1+X+X^3 : ℤ[X]).eval 2=11 ∧
    (1+X+X^2 : ℤ[X]).eval 2=7 ∧ (1+X^3 : ℤ[X]).eval 2=9
  norm_num

/-- Ordinary integer evaluation does not preserve the proved polynomial Sidonness. -/
theorem binary_evaluation_not_sidon :
    ¬ IsSidon ((fun P : ℤ[X] => (P.eval 2)^2) '' {P | Binary P}) := by
  intro h
  have hm (i : Fin 4) : (word i).eval 2 ^ 2 ∈
      (fun P : ℤ[X] => (P.eval 2)^2) '' {P | Binary P} :=
    ⟨word i, example_binary i, rfl⟩
  obtain ⟨h0,h1,h2,h3⟩ := example_values
  have he : (word 0).eval 2 ^ 2 + (word 1).eval 2 ^ 2 =
      (word 2).eval 2 ^ 2 + (word 3).eval 2 ^ 2 := by
    rw [h0,h1,h2,h3]
    norm_num
  have hh := h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) he
  rw [h0,h1,h2,h3] at hh
  norm_num at hh

#print axioms transversal_pair_matching
#print axioms binary_pair_matching
#print axioms binary_squares_sidon
#print axioms example_discrepancy
#print axioms binary_evaluation_not_sidon
end
end Erdos773.BinaryPolynomialSidon
