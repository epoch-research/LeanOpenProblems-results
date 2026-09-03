import FormalConjecturesUtil

/-!
An actual Sidon construction in the polynomial ring, using Gaussian
Eisenstein irreducibility. Integer evaluation is NOT asserted to preserve it.
-/
namespace Erdos773.FormalGaussianSidon
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

abbrev G := GaussianInt

def imag : G := ⟨0,1⟩

def gauss (P : ℤ[X]) : G[X] := P.map (Int.castRingHom G)

/-- The lower polynomial has constant coefficient 1 modulo 3. -/
def Admissible (d : ℕ) (P : ℤ[X]) : Prop :=
  P.natDegree<d ∧ P.coeff 0 % 3=1

def encoding (d : ℕ) (P : ℤ[X]) : ℤ[X] := X^d+C 6*P

/-- This is (encoding(P)+encoding(Q))/2 + i*(encoding(Q)-encoding(P))/2,
written without division. It is monic over the Gaussian integers. -/
def pairPoly (d : ℕ) (P Q : ℤ[X]) : G[X] :=
  X^d+C 3*(gauss P+gauss Q)+C (3*imag)*(gauss Q-gauss P)

lemma pair_coeff (d n : ℕ) (P Q : ℤ[X]) :
    (pairPoly d P Q).coeff n = (if n=d then 1 else 0)+
      3*((P.coeff n : G)+Q.coeff n)+3*imag*((Q.coeff n : G)-P.coeff n) := by
  simp [pairPoly, gauss, coeff_X_pow, coeff_C_mul, mul_assoc]

lemma pair_monic_degree {d : ℕ} {P Q : ℤ[X]}
    (hP : P.natDegree<d) (hQ : Q.natDegree<d) :
    (pairPoly d P Q).Monic ∧ (pairPoly d P Q).natDegree=d := by
  have hd : (pairPoly d P Q).coeff d=1 := by
    rw [pair_coeff, coeff_eq_zero_of_natDegree_lt hP,
      coeff_eq_zero_of_natDegree_lt hQ]
    simp
  have hle : (pairPoly d P Q).natDegree≤d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [pair_coeff, coeff_eq_zero_of_natDegree_lt (hP.trans hn),
      coeff_eq_zero_of_natDegree_lt (hQ.trans hn)]
    simp [ne_of_gt hn]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one d hle hd,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hd]; exact one_ne_zero)⟩

lemma pair_injective (d : ℕ) {P Q R S : ℤ[X]}
    (he : pairPoly d P Q=pairPoly d R S) : P=R ∧ Q=S := by
  have hh (n : ℕ) : P.coeff n=R.coeff n ∧ Q.coeff n=S.coeff n := by
    have hc := congrArg (fun F : G[X] => F.coeff n) he
    have hr := congrArg Zsqrtd.re hc
    have hi := congrArg Zsqrtd.im hc
    dsimp only at hr hi
    rw [pair_coeff, pair_coeff] at hr hi
    by_cases hn : n=d
    · subst n
      simp [imag] at hr hi
      omega
    · simp [hn, imag] at hr hi
      omega
  exact ⟨Polynomial.ext (fun n => (hh n).1), Polynomial.ext (fun n => (hh n).2)⟩

lemma pair_irreducible {d : ℕ} {P Q : ℤ[X]}
    (hP : Admissible d P) (hQ : Admissible d Q) :
    Irreducible (pairPoly d P Q) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hthree : Prime (3 : G) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).mpr (by decide)
  let J : Ideal G := Ideal.span {3}
  have hJ : J.IsPrime := (Ideal.span_singleton_prime hthree.ne_zero).mpr hthree
  obtain ⟨hmon,hdeg⟩ := pair_monic_degree hP.1 hQ.1
  have hmem {n : ℕ} (hn : n<(pairPoly d P Q).natDegree) :
      (pairPoly d P Q).coeff n∈J := by
    rw [hdeg] at hn
    apply Ideal.mem_span_singleton.mpr
    refine ⟨((P.coeff n : G)+Q.coeff n)+imag*((Q.coeff n : G)-P.coeff n), ?_⟩
    rw [pair_coeff, if_neg (ne_of_lt hn)]
    ring
  have hnot : (pairPoly d P Q).coeff 0 ∉ J^2 := by
    intro hz
    dsimp only [J] at hz
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
    obtain ⟨z,hz⟩ := hz
    have hr := congrArg Zsqrtd.re hz
    rw [pair_coeff] at hr
    have hd0 : (0 : ℕ) ≠ d := by have hh := hP.1; omega
    norm_num [hd0, imag, pow_two] at hr
    have hp0 := hP.2
    have hq0 := hQ.2
    omega
  have hE := hmon.isEisensteinAt_of_mem_of_notMem hJ.ne_top hmem hnot
  apply hE.irreducible hJ hmon.isPrimitive
  rw [hdeg]
  have hh := hP.1
  omega

lemma imag_sq : imag^2=(-1 : G) := by
  ext <;> norm_num [imag, pow_two]

/-- The Gaussian factorization is a formal polynomial identity. -/
lemma gauss_encoding (d : ℕ) (P : ℤ[X]) :
    gauss (encoding d P)=X^d+6*gauss P := by
  simp [gauss, encoding]

lemma norm_identity (d : ℕ) (P Q : ℤ[X]) :
    (2 : G[X])*(pairPoly d P Q*pairPoly d Q P) =
      (gauss (encoding d P))^2+(gauss (encoding d Q))^2 := by
  have hi : (C imag : G[X])^2 = -1 := by
    rw [← map_pow, imag_sq]
    simp
  rw [gauss_encoding, gauss_encoding]
  unfold pairPoly
  simp only [map_mul, map_ofNat]
  linear_combination -18*(gauss Q-gauss P)^2*hi

/-- Equal square sums of admissible polynomial encodings are trivial. -/
theorem encoding_pair_matching {d : ℕ} {P Q R S : ℤ[X]}
    (hP : Admissible d P) (hQ : Admissible d Q)
    (hR : Admissible d R) (hS : Admissible d S)
    (he : (encoding d P)^2+(encoding d Q)^2=(encoding d R)^2+(encoding d S)^2) :
    (P=R ∧ Q=S) ∨ (P=S ∧ Q=R) := by
  have hprod : pairPoly d P Q*pairPoly d Q P=pairPoly d R S*pairPoly d S R := by
    apply mul_left_cancel₀ (show (2 : G[X]) ≠ 0 by norm_num)
    rw [norm_identity, norm_identity]
    have hh := congrArg gauss he
    simpa only [gauss, Polynomial.map_add, Polynomial.map_pow] using hh
  have hprime := (pair_irreducible hP hQ).prime
  have hdiv : pairPoly d P Q ∣ pairPoly d R S*pairPoly d S R := by
    rw [← hprod]
    exact dvd_mul_right _ _
  obtain ⟨hmon,hdeg⟩ := pair_monic_degree hP.1 hQ.1
  rcases hprime.dvd_or_dvd hdiv with h | h
  · obtain ⟨hmon',hdeg'⟩ := pair_monic_degree hR.1 hS.1
    have heq := eq_of_monic_of_dvd_of_natDegree_le hmon hmon' h (by omega)
    exact Or.inl (pair_injective d heq.symm)
  · obtain ⟨hmon',hdeg'⟩ := pair_monic_degree hS.1 hR.1
    have heq := eq_of_monic_of_dvd_of_natDegree_le hmon hmon' h (by omega)
    exact Or.inr (pair_injective d heq.symm)

/-- Sidonness is proved in ℤ[X], not after evaluating at an integer. -/
theorem formal_sidon (d : ℕ) :
    IsSidon ((fun P : ℤ[X] => (encoding d P)^2) '' {P | Admissible d P}) := by
  intro a ha c hc b hb e he hab
  obtain ⟨P,hP,rfl⟩ := ha
  obtain ⟨R,hR,rfl⟩ := hc
  obtain ⟨Q,hQ,rfl⟩ := hb
  obtain ⟨S,hS,rfl⟩ := he
  rcases encoding_pair_matching hP hQ hR hS hab with h | h
  · left; simp [h.1,h.2]
  · right; simp [h.1,h.2]

#print axioms pair_irreducible
#print axioms norm_identity
#print axioms encoding_pair_matching
#print axioms formal_sidon
end
end Erdos773.FormalGaussianSidon
