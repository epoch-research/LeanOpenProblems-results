import FormalConjecturesUtil

/-! Leading terms of even polynomial powers do not cancel over the integers.
These statements concern polynomial identities, not unrestricted integer counts. -/
namespace Erdos322Research.EvenPolynomialNormDegree

open Polynomial Finset
set_option Elab.async false

/-- An even-power norm identity automatically bounds every numerator degree
by the degree of its common denominator. No monicity or nonzero multiplier
hypothesis is needed. -/
theorem numerator_degree_le {ι : Type*} [Fintype ι]
    (f : ℤ[X]) (g : ι → ℤ[X]) (N : ℤ) (m : ℕ) (hm : 0 < m)
    (hnorm : ∑ i, g i ^ (2*m) = Polynomial.C N * f ^ (2*m)) :
    ∀ i, (g i).natDegree ≤ f.natDegree := by
  classical
  intro i
  by_contra hi
  let d : ℕ := Finset.univ.sup (fun j => (g j).natDegree)
  have hle (j : ι) : (g j).natDegree ≤ d :=
    Finset.le_sup (f := fun j => (g j).natDegree) (Finset.mem_univ j)
  have hd : f.natDegree < d := (Nat.lt_of_not_ge hi).trans_le (hle i)
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ
    (show (Finset.univ : Finset ι).Nonempty from ⟨i,Finset.mem_univ i⟩)
    (fun j => (g j).natDegree)
  change d=(g j).natDegree at he
  have hgj : g j ≠ 0 := by
    intro hz
    rw [he,hz,natDegree_zero] at hd
    omega
  have hjpos : 0 < ((g j).coeff d)^(2*m) := by
    rw [he,coeff_natDegree]
    exact (even_two_mul m).pow_pos (leadingCoeff_ne_zero.mpr hgj)
  have hsumpos : 0 < ∑ j, ((g j).coeff d)^(2*m) :=
    hjpos.trans_le (Finset.single_le_sum
      (fun j _ => (even_two_mul m).pow_nonneg ((g j).coeff d)) hj)
  have hcoeff : (∑ j, g j^(2*m)).coeff ((2*m)*d) =
      ∑ j, ((g j).coeff d)^(2*m) := by
    simp only [finset_sum_coeff]
    exact Finset.sum_congr rfl (fun j _ => coeff_pow_of_natDegree_le (hle j))
  have hdeg : (Polynomial.C N * f^(2*m)).natDegree < (2*m)*d := by
    calc
      (Polynomial.C N * f^(2*m)).natDegree ≤ (f^(2*m)).natDegree :=
        natDegree_C_mul_le _ _
      _ = (2*m)*f.natDegree := natDegree_pow _ _
      _ < (2*m)*d := Nat.mul_lt_mul_of_pos_left hd (by omega)
  rw [← hcoeff, hnorm, coeff_eq_zero_of_natDegree_lt hdeg] at hsumpos
  exact (lt_irrefl (0 : ℤ)) hsumpos

/-- A reduced even-power rational norm identity has no real denominator
zeros. This includes every positive even exponent. -/
theorem denominator_no_real_zero {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hC : 0 < C)
    (hnorm : ∑ i, g i^(2*m)=Polynomial.C N*f^(2*m))
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ)) :
    ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
  intro t ht
  have he : 2*m ≠ 0 := by omega
  have hh := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) t) hnorm
  simp only [eval₂_finset_sum, eval₂_pow, eval₂_mul, eval₂_C, ht,
    zero_pow he, mul_zero] at hh
  have hg (i : ι) : (g i).eval₂ (Int.castRingHom ℝ) t=0 := by
    apply (pow_eq_zero_iff he).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => (even_two_mul m).pow_nonneg _)).mp hh i (Finset.mem_univ i)
  have hb := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) t) hbez
  simp only [eval₂_add, eval₂_finset_sum, eval₂_mul, eval₂_C, ht, hg,
    mul_zero, Finset.sum_const_zero, add_zero] at hb
  have hp : (0 : ℝ) < C := by exact_mod_cast hC
  have hz : (0 : ℝ) = C := by simpa using hb
  linarith

end Erdos322Research.EvenPolynomialNormDegree
