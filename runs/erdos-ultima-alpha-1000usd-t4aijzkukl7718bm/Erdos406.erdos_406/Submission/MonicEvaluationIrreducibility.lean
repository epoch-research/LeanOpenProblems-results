import Submission.NewmanFactorCount

/-! An irreducibility criterion from positivity and two integer evaluations.
No Newman-divisibility assertion is part of this general criterion. -/
namespace Erdos406EvaluationIrreducible
open Polynomial Erdos406FactorParity Erdos406FactorCount

lemma factor_eval_one_ge_two (P : ℤ[X]) (hP : P.Monic) (k : ℕ)
    (hthree : P.eval 3 = (2 : ℤ) ^ k)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 < (P.map (Int.castRingHom ℝ)).eval x)
    (hroots : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2)
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ P) (hdeg : 0 < Q.natDegree) :
    2 ≤ Q.eval 1 := by
  have hQr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2 := by
    intro z hz
    apply hroots z
    apply (mem_roots (hP.map _).ne_zero).mpr
    have hh := (mem_roots (hQ.map _).ne_zero).mp hz
    have hv := eval_dvd (x := z) (map_dvd (Int.castRingHom ℂ) hd)
    change (Q.map (Int.castRingHom ℂ)).eval z = 0 at hh
    rwa [hh, zero_dvd_iff] at hv
  have hnorm := monic_norm_eval_three_gt_one (Q.map (Int.castRingHom ℂ))
    (hQ.map _) (by rwa [hQ.natDegree_map]) hQr
  have hp (a : ℤ) (ha : 0 ≤ a) : 0 < Q.eval a := by
    have hh := monic_factor_positive (hQ.map (Int.castRingHom ℝ))
      (map_dvd (Int.castRingHom ℝ) hd) hpos (a : ℝ) (by exact_mod_cast ha)
    rw [eval_map_int] at hh
    exact_mod_cast hh
  have h3pos := hp 3 (by norm_num)
  have he : (Q.map (Int.castRingHom ℂ)).eval 3 = ((Q.eval 3 : ℤ) : ℂ) := by
    rw [eval_map]
    exact eval₂_at_apply (Int.castRingHom ℂ) 3
  rw [he, Complex.norm_intCast, abs_of_pos (by exact_mod_cast h3pos)] at hnorm
  have h3gt : 1 < Q.eval 3 := by exact_mod_cast hnorm
  have hv := eval_dvd (x := (3 : ℤ)) hd
  rw [hthree] at hv
  have hn : (Q.eval 3).natAbs ∣ 2 ^ k := by simpa using Int.natAbs_dvd_natAbs.mpr hv
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  have hj0 : j ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hj
    have hh := Int.natAbs_of_nonneg h3pos.le
    rw [hj] at hh
    norm_num at hh
    omega
  have h2 : (2 : ℤ) ∣ Q.eval 3 := by
    apply Int.natAbs_dvd_natAbs.mp
    change 2 ∣ (Q.eval 3).natAbs
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hdiff : (2 : ℤ) ∣ Q.eval 3 - Q.eval 1 := sub_dvd_eval_sub 3 1 Q
  have h21 : (2 : ℤ) ∣ Q.eval 1 := by
    convert dvd_sub h2 hdiff using 1
    ring
  have h1pos := hp 1 (by norm_num)
  obtain ⟨t, ht⟩ := h21
  omega

/-- If P is monic, positive on the nonnegative ray, all roots have norm<2,
P(3) is a power of two and P(1)=2, then P is irreducible. -/
theorem irreducible_of_eval_one_two (P : ℤ[X]) (hP : P.Monic) (k : ℕ)
    (hthree : P.eval 3 = (2 : ℤ) ^ k) (hone : P.eval 1 = 2)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 < (P.map (Int.castRingHom ℝ)).eval x)
    (hroots : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2) :
    Irreducible P := by
  have hP1 : P ≠ 1 := by intro hh; simp [hh] at hone
  apply (irreducible_of_monic hP hP1).mpr
  intro Q R hQ hR he
  by_cases hQ1 : Q = 1
  · exact Or.inl hQ1
  by_cases hR1 : R = 1
  · exact Or.inr hR1
  have hqd : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit (by simpa [hQ.isUnit_iff])
  have hrd : 0 < R.natDegree := hR.natDegree_pos_of_not_isUnit (by simpa [hR.isUnit_iff])
  have hq := factor_eval_one_ge_two P hP k hthree hpos hroots Q hQ
    (by rw [← he]; exact dvd_mul_right _ _) hqd
  have hr := factor_eval_one_ge_two P hP k hthree hpos hroots R hR
    (by rw [← he]; exact dvd_mul_left _ _) hrd
  have hv := congrArg (eval (1 : ℤ)) he
  rw [eval_mul, hone] at hv
  nlinarith

#print axioms irreducible_of_eval_one_two
end Erdos406EvaluationIrreducible
