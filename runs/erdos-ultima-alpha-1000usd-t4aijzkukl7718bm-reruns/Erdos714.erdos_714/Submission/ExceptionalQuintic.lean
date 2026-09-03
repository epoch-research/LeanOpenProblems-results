import FormalConjecturesUtil

/-!
An arithmetic root bound considered as a possible ingredient for Erdős Problem 714.
No graph construction or proof of the conjecture is asserted here.
-/

open Polynomial

namespace Erdos714Exceptional

variable {F : Type*} [Field F] [CharP F 3]

noncomputable def quintic (a b : F) : F[X] := X ^ 5 + C a * X ^ 3 + C b

lemma quintic_monic (a b : F) : (quintic a b).Monic := by
  unfold quintic
  monicity!

lemma quintic_natDegree (a b : F) : (quintic a b).natDegree = 5 := by
  unfold quintic
  compute_degree!

lemma quintic_derivative (a b : F) : (quintic a b).derivative = -X ^ 4 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h5 : (5 : F) = -1 := by linear_combination 2 * h3
  simp [quintic, derivative_pow, derivative_mul, h3, h5]

private lemma vandermonde_five (x₀ x₁ x₂ x₃ x₄ : F) :
    ((x₀-x₁)*(x₀-x₂)*(x₀-x₃)*(x₀-x₄)*(x₁-x₂)*(x₁-x₃)*(x₁-x₄)*
      (x₂-x₃)*(x₂-x₄)*(x₃-x₄)) ^ 2 =
    ((x₀-x₁)*(x₀-x₂)*(x₀-x₃)*(x₀-x₄)) *
    ((x₁-x₀)*(x₁-x₂)*(x₁-x₃)*(x₁-x₄)) *
    ((x₂-x₀)*(x₂-x₁)*(x₂-x₃)*(x₂-x₄)) *
    ((x₃-x₀)*(x₃-x₁)*(x₃-x₂)*(x₃-x₄)) *
    ((x₄-x₀)*(x₄-x₁)*(x₄-x₂)*(x₄-x₃)) := by
  have h (a b c d e f g h i j : F) :
      (a*b*c*d*e*f*g*h*i*j)^2 =
      (a*b*c*d)*((-a)*e*f*g)*((-b)*(-e)*h*i)*
      ((-c)*(-f)*(-h)*j)*((-d)*(-g)*(-i)*(-j)) := by ring
  simpa only [neg_sub] using h
    (x₀-x₁) (x₀-x₂) (x₀-x₃) (x₀-x₄) (x₁-x₂)
    (x₁-x₃) (x₁-x₄) (x₂-x₃) (x₂-x₄) (x₃-x₄)

/-- Such a quintic cannot split completely when its constant term is nonzero. -/
lemma no_five_factorization (a b : F) (hb : b ≠ 0) (hns : ¬IsSquare (-1 : F))
    (x₀ x₁ x₂ x₃ x₄ : F)
    (hfac : quintic a b =
      (X-C x₀)*(X-C x₁)*(X-C x₂)*(X-C x₃)*(X-C x₄)) : False := by
  have hc : b = -(x₀*x₁*x₂*x₃*x₄) := by
    have h := congrArg (Polynomial.eval (0 : F)) hfac
    simpa [quintic, mul_assoc] using h
  have hd := congrArg Polynomial.derivative hfac
  rw [quintic_derivative] at hd
  have hd₀ : (x₀-x₁)*(x₀-x₂)*(x₀-x₃)*(x₀-x₄) = -x₀^4 := by
    have h := congrArg (Polynomial.eval x₀) hd
    simpa [derivative_mul, mul_assoc] using h.symm
  have hd₁ : (x₁-x₀)*(x₁-x₂)*(x₁-x₃)*(x₁-x₄) = -x₁^4 := by
    have h := congrArg (Polynomial.eval x₁) hd
    simpa [derivative_mul, mul_assoc] using h.symm
  have hd₂ : (x₂-x₀)*(x₂-x₁)*(x₂-x₃)*(x₂-x₄) = -x₂^4 := by
    have h := congrArg (Polynomial.eval x₂) hd
    simpa [derivative_mul, mul_assoc] using h.symm
  have hd₃ : (x₃-x₀)*(x₃-x₁)*(x₃-x₂)*(x₃-x₄) = -x₃^4 := by
    have h := congrArg (Polynomial.eval x₃) hd
    simpa [derivative_mul, mul_assoc] using h.symm
  have hd₄ : (x₄-x₀)*(x₄-x₁)*(x₄-x₂)*(x₄-x₃) = -x₄^4 := by
    have h := congrArg (Polynomial.eval x₄) hd
    simpa [derivative_mul, mul_assoc] using h.symm
  let D := (x₀-x₁)*(x₀-x₂)*(x₀-x₃)*(x₀-x₄)*(x₁-x₂)*(x₁-x₃)*(x₁-x₄)*
      (x₂-x₃)*(x₂-x₄)*(x₃-x₄)
  have hD : D ^ 2 = -b^4 := by
    dsimp [D]
    rw [vandermonde_five, hd₀, hd₁, hd₂, hd₃, hd₄, hc]
    ring
  apply hns
  refine ⟨D / b^2, ?_⟩
  rw [← pow_two, div_pow, ← pow_mul]
  norm_num only [Nat.reduceMul]
  apply (eq_div_iff (pow_ne_zero 4 hb)).2
  simpa using hD.symm

/-- Four roots counted with multiplicity force a monic quintic to split. -/
private lemma roots_card_five (p : F[X]) (hdeg : p.natDegree = 5)
    (hcard : 4 ≤ p.roots.card) : p.roots.card = 5 := by
  obtain ⟨q, _, hsum, hq⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hqdeg : q.natDegree ≤ 1 := by omega
  have hs := (Polynomial.Splits.of_natDegree_le_one hqdeg).natDegree_eq_card_roots
  rw [hq, Multiset.card_zero] at hs
  omega

/-- For nonzero constant term even the root multiset has cardinality at most three. -/
theorem roots_card_le_three (a b : F) (hb : b ≠ 0) (hns : ¬IsSquare (-1 : F)) :
    (quintic a b).roots.card ≤ 3 := by
  classical
  by_contra h
  have hc := roots_card_five (quintic a b) (quintic_natDegree a b) (by omega)
  obtain ⟨x₀, hx₀⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (quintic a b).roots.card)
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hx₀
  have hs4 : s.card = 4 := by simpa [hs] using hc
  obtain ⟨x₁, x₂, x₃, x₄, hs'⟩ := Multiset.card_eq_four.mp hs4
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (quintic_monic a b)
    (hc.trans (quintic_natDegree a b).symm)
  rw [hs, hs'] at hfac
  apply no_five_factorization a b hb hns x₀ x₁ x₂ x₃ x₄
  simpa [Multiset.insert_eq_cons, mul_assoc] using hfac.symm

open Classical in
/-- The zero-constant case still has at most three distinct roots. -/
theorem distinct_roots_le_three (a b : F) (hns : ¬IsSquare (-1 : F)) :
    (quintic a b).roots.toFinset.card ≤ 3 := by
  classical
  by_cases hb : b = 0
  · subst b
    have hfac : quintic a 0 = (X ^ 3 : F[X]) * (X ^ 2 + C a) := by
      unfold quintic
      simp only [map_zero, add_zero]
      ring
    have hne : (X ^ 3 : F[X]) * (X ^ 2 + C a) ≠ 0 := by
      rw [← hfac]
      exact (quintic_monic a 0).ne_zero
    rw [hfac, roots_mul hne, Multiset.toFinset_add]
    have hX : (X ^ 3 : F[X]).roots.toFinset.card = 1 := by
      simp [roots_X_pow]
    have hQ : (X ^ 2 + C a : F[X]).roots.toFinset.card ≤ 2 := by
      apply (Multiset.toFinset_card_le _).trans
      have hdeg : (X ^ 2 + C a : F[X]).natDegree = 2 := by compute_degree!
      exact (X ^ 2 + C a : F[X]).card_roots' |>.trans_eq hdeg
    have h := Finset.card_union_le (X ^ 3 : F[X]).roots.toFinset
      (X ^ 2 + C a : F[X]).roots.toFinset
    omega
  · exact (Multiset.toFinset_card_le _).trans (roots_card_le_three a b hb hns)

/-- A root-count formulation that can be applied to finite common-neighbor sets. -/
theorem finite_root_bound (a b : F) (hns : ¬IsSquare (-1 : F))
    (T : Finset F) (hT : ∀ x ∈ T, x^5 + a*x^3 + b = 0) : T.card ≤ 3 := by
  classical
  apply (Finset.card_le_card (show T ⊆ (quintic a b).roots.toFinset from ?_)).trans
    (distinct_roots_le_three a b hns)
  intro x hx
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (quintic_monic a b).ne_zero]
  simpa [Polynomial.IsRoot, quintic] using hT x hx

/-- The required nonsquare condition is automatic for field order three modulo four. -/
theorem finite_field_root_bound [Fintype F] (hcard : Fintype.card F % 4 = 3)
    (a b : F) (T : Finset F) (hT : ∀ x ∈ T, x^5 + a*x^3 + b = 0) : T.card ≤ 3 := by
  apply finite_root_bound a b _ T hT
  rw [FiniteField.isSquare_neg_one_iff, hcard]
  simp

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The arithmetic root bound is available over arbitrarily large fields. -/
theorem odd_galois_field_root_bound (k : ℕ)
    (a b : GaloisField 3 (2*k+1)) (T : Finset (GaloisField 3 (2*k+1)))
    (hT : ∀ x ∈ T, x^5 + a*x^3 + b = 0) : T.card ≤ 3 := by
  letI : Fintype (GaloisField 3 (2*k+1)) := Fintype.ofFinite _
  apply finite_field_root_bound _ a b T hT
  rw [Fintype.card_eq_nat_card, GaloisField.card 3 (2*k+1) (by omega)]
  rw [pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

#print axioms roots_card_le_three
#print axioms finite_root_bound
#print axioms odd_galois_field_root_bound

end Erdos714Exceptional
