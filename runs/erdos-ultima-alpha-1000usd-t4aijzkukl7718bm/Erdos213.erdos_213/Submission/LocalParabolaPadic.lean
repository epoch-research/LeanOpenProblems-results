import Submission.LocalParabola
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.NormNum

/-! These auxiliary lemmas strengthen the finite congruence control to any
prescribed finite set of p-adic places. They are not a local-global principle. -/
namespace Erdos213.LocalParabola

open Polynomial

lemma padic_one_add_sq_isSquare {p : ℕ} [Fact p.Prime] (t : ℤ_[p])
    (ht : ‖t‖ < ‖(2 : ℤ_[p])‖) : IsSquare (1+t^2) := by
  let F : Polynomial ℤ_[p] := X^2-C (1+t^2)
  have hF (z : ℤ_[p]) : F.aeval z=z^2-(1+t^2) := by simp [F]
  have hder : F.derivative.aeval (1 : ℤ_[p])=2 := by
    dsimp [F]
    rw [derivative_sub, derivative_C, derivative_X_pow]
    norm_num
  have hval : F.aeval (1 : ℤ_[p])= -t^2 := by rw [hF]; ring
  have hn : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖^2 := by
    rw [hval, hder, norm_neg, norm_pow]
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr ht
  obtain ⟨z,hz,-⟩ := hensels_lemma hn
  refine ⟨z, ?_⟩
  rw [hF] at hz
  simpa only [pow_two] using (sub_eq_zero.mp hz).symm

lemma padic_multiple_norm_lt_two {p : ℕ} [hp : Fact p.Prime]
    {M : ℤ} (hM : 2*(p : ℤ) ∣ M) (s : ℤ) :
    ‖((M*s : ℤ) : ℤ_[p])‖ < ‖(2 : ℤ_[p])‖ := by
  obtain ⟨k,rfl⟩ := hM
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ)<p := lt_trans zero_lt_one hpR
  have hpn : ‖(p : ℤ_[p])‖<1 := by
    rw [PadicInt.norm_p]
    exact (inv_lt_one₀ hp0).mpr hpR
  have htwo : (0 : ℝ)<‖(2 : ℤ_[p])‖ := norm_pos_iff.mpr (by norm_num)
  have he : (((2*(p : ℤ)*k)*s : ℤ) : ℤ_[p]) =
      (2 : ℤ_[p])*(p : ℤ_[p])*((k*s : ℤ) : ℤ_[p]) := by
    push_cast
    ring
  rw [he, norm_mul, norm_mul]
  calc
    ‖(2 : ℤ_[p])‖*‖(p : ℤ_[p])‖*‖((k*s : ℤ) : ℤ_[p])‖ ≤
        ‖(2 : ℤ_[p])‖*‖(p : ℤ_[p])‖*1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
    _ < ‖(2 : ℤ_[p])‖ := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hpn htwo

/-- Any chosen p-adic place admits every distance in this family as a square
once 2p divides M. Over the rationals the positive distinct-parameter distances
remain nonsquares, by `sqDist_not_rational_square`. -/
theorem sqDist_padic_square {p : ℕ} [Fact p.Prime] {M : ℤ}
    (hM : 2*(p : ℤ) ∣ M) (a b : ℤ) : IsSquare (sqDist M a b : ℤ_[p]) := by
  have hs := padic_one_add_sq_isSquare ((M*(a+b) : ℤ) : ℤ_[p])
    (padic_multiple_norm_lt_two hM (a+b))
  rw [sqDist_factorization]
  push_cast at hs ⊢
  exact (IsSquare.sq ((a : ℤ_[p])-b)).mul hs

lemma exists_local_multiplier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ M : ℤ, 0<M ∧ ∀ p ∈ P, 2*(p : ℤ) ∣ M := by
  refine ⟨2*(∏ p ∈ P, (p : ℤ)), ?_, ?_⟩
  · apply mul_pos (by norm_num)
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hP p hp).pos
  · intro p hp
    exact mul_dvd_mul_left 2 (Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hp)

/-- One positive multiplier works at every prime in any prescribed finite set.
The same multiplier works for all integer parameters a,b, not merely a bounded
list. No rational square root follows from these finitely many local roots. -/
theorem simultaneous_local_squares (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ M : ℤ, 0<M ∧ ∀ (p : ℕ) (hp : p ∈ P),
      letI : Fact p.Prime := ⟨hP p hp⟩
      ∀ a b : ℤ, IsSquare (sqDist M a b : ℤ_[p]) := by
  obtain ⟨M,hM,hdiv⟩ := exists_local_multiplier P hP
  refine ⟨M,hM,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hP p hp⟩
  exact sqDist_padic_square (hdiv p hp)

#print axioms simultaneous_local_squares

#print axioms padic_one_add_sq_isSquare
#print axioms sqDist_padic_square

end Erdos213.LocalParabola
