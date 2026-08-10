import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 100000

private theorem not_ss_gen (K q e : ℕ) (hq : q.Prime) (h3 : q % 4 = 3)
    (hde : q^e ∣ K) (hde2 : ¬ q^(e+1) ∣ K) (hodd : Odd e) (hK : K ≠ 0) :
    ¬ ∃ x y, K = x^2 + y^2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have he : e ≠ 0 := by rintro rfl; simp at hodd
  rw [Nat.eq_sq_add_sq_iff]
  push_neg
  refine ⟨q, ?_, h3, ?_⟩
  · rw [Nat.mem_primeFactors]
    exact ⟨hq, dvd_trans (dvd_pow_self q he) hde, hK⟩
  · have hv1 : e ≤ padicValNat q K := by rw [← padicValNat_dvd_iff_le hK]; exact hde
    have hv2 : ¬ e+1 ≤ padicValNat q K := by rw [← padicValNat_dvd_iff_le hK]; exact hde2
    have : padicValNat q K = e := by omega
    rw [this]; exact Nat.not_even_iff_odd.mpr hodd

example : ¬ ∃ x y : ℕ, (40000000000009 : ℕ) = x^2 + y^2 :=
  not_ss_gen 40000000000009 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms not_ss_gen
