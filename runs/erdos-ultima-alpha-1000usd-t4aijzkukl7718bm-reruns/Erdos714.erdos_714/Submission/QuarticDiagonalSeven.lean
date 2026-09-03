import Submission.QuarticDiagonalNorm

/-! A kernel-checked finite obstruction to the diagonal quartic norm slice.
Not a disproof of Erdős714. -/
noncomputable section
open Polynomial Finset SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Erdos714QuarticDiagonalSeven
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def p : (ZMod 7)[X] := X^4+6*X^3+2*X+6

lemma degree_p : p.natDegree = 4 := by unfold p; compute_degree!

lemma monic_p : p.Monic := by
  unfold p
  monicity <;> norm_num

lemma no_root : ∀ a : ZMod 7, p.eval a ≠ 0 := by
  intro a
  fin_cases a <;> norm_num [p] <;> decide

lemma no_quad : ∀ a b c d : ZMod 7,
    ¬ (a*c = 6 ∧ a*d+b*c = 2 ∧ a+c+b*d = 0 ∧ b+d = 6) := by decide

lemma irreducible_p : Irreducible p := by
  apply monic_p.irreducible_iff_natDegree'.mpr
  constructor
  · intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [degree_p, natDegree_one] at hdeg
    omega
  · intro f g hf hg he hd
    have hdg : g.natDegree = 1 ∨ g.natDegree = 2 := by
      rw [degree_p] at hd
      simp only [Nat.reduceDiv, mem_Ioc] at hd
      omega
    rcases hdg with hdg | hdg
    · have hg1 : g = X+C (g.coeff 0) := by
        have hgcoef1 : g.coeff 1 = 1 := hdg ▸ hg.coeff_natDegree
        rw [g.as_sum_range_C_mul_X_pow, hdg]
        simp [sum_range_succ, hgcoef1, add_comm]
      have h := congrArg (fun q : (ZMod 7)[X] => q.eval (-g.coeff 0)) he
      change (f*g).eval (-g.coeff 0) = p.eval (-g.coeff 0) at h
      rw [eval_mul, hg1] at h
      simp at h
      exact no_root _ h.symm
    · have hdf : f.natDegree = 2 := by
        have h := congrArg Polynomial.natDegree he
        rw [hf.natDegree_mul hg, degree_p, hdg] at h
        omega
      have hf2 : f.coeff 2 = 1 := hdf ▸ hf.coeff_natDegree
      have hg2 : g.coeff 2 = 1 := hdg ▸ hg.coeff_natDegree
      have hf3 : f.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hg3 : g.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h0 := congrArg (fun q : (ZMod 7)[X] => q.coeff 0) he
      have h1 := congrArg (fun q : (ZMod 7)[X] => q.coeff 1) he
      have h2 := congrArg (fun q : (ZMod 7)[X] => q.coeff 2) he
      have h3 := congrArg (fun q : (ZMod 7)[X] => q.coeff 3) he
      simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, p, hf2, hg2, hf3, hg3, coeff_X] at h0 h1 h2 h3
      exact no_quad (f.coeff 0) (f.coeff 1) (g.coeff 0) (g.coeff 1)
        ⟨h0,h1,by linear_combination h2,h3⟩

/-- The diagonal slice with c=1/2=4 fails in the actual quartic field
F7[T]/(T^4+6T^3+2T+6), using rows 1,2,3,4. -/
theorem not_free :
    letI : Fact (Irreducible p) := ⟨irreducible_p⟩
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714QuarticDiagonal.graph (F := ZMod 7) (E := AdjoinRoot p) (4 : ZMod 7)) := by
  exact Erdos714QuarticDiagonal.irreducible_not_free p irreducible_p monic_p degree_p
    ![1,2,3,4] (by decide) 4 (by decide)
    (by norm_num [p]; decide)
    (by intro i; fin_cases i <;> norm_num [p] <;> decide)

#print axioms irreducible_p
#print axioms not_free
end Erdos714QuarticDiagonalSeven
