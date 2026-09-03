import FormalConjecturesUtil

/-! Rational-length ray perturbations pass arbitrary prescribed finite sets of
p-adic tests. They are not global rational-distance extensions. -/
namespace Erdos213.FixedSourceLocal
open Polynomial
set_option maxHeartbeats 2000000

/-- A sufficiently divisible perturbation of an integer square remains a square
in the p-adic integers, even when the square is not a p-adic unit. -/
lemma perturbation_isSquare_padic {p : ℕ} [hp : Fact p.Prime]
    {r t : ℤ} (hr : r ≠ 0) (ht : 4*(p : ℤ)*r^2 ∣ t) (a b : ℤ) :
    IsSquare ((r^2+t*(a*t+b) : ℤ) : ℤ_[p]) := by
  obtain ⟨k,hk⟩ := ht
  let F : Polynomial ℤ_[p] := X^2-C ((r^2+t*(a*t+b) : ℤ) : ℤ_[p])
  have hf (z : ℤ_[p]) : F.aeval z=z^2-((r^2+t*(a*t+b) : ℤ) : ℤ_[p]) := by
    simp [F]
  have hd : F.derivative.aeval (r : ℤ_[p])=2*(r : ℤ_[p]) := by
    dsimp only [F]
    rw [derivative_sub,derivative_C,derivative_X_pow]
    norm_num
  have hv : F.aeval (r : ℤ_[p]) =
      -(2*(r : ℤ_[p]))^2*(p : ℤ_[p])*((k*(a*t+b) : ℤ) : ℤ_[p]) := by
    rw [hf]
    have hk' : (t : ℤ_[p])=4*(p : ℤ_[p])*(r : ℤ_[p])^2*(k : ℤ_[p]) := by
      exact_mod_cast hk
    push_cast
    rw [hk']
    ring
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp.out.one_lt
  have hpn : ‖(p : ℤ_[p])‖<1 := by
    rw [PadicInt.norm_p]
    exact (inv_lt_one₀ (by positivity)).mpr hpR
  have hrp : (r : ℤ_[p])≠0 := by exact_mod_cast hr
  have hpos : 0<‖2*(r : ℤ_[p])‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (mul_ne_zero (by norm_num) hrp))
  have hn : ‖F.aeval (r : ℤ_[p])‖ < ‖F.derivative.aeval (r : ℤ_[p])‖^2 := by
    rw [hv,hd,norm_mul,norm_mul,norm_neg,norm_pow]
    calc
      ‖2*(r : ℤ_[p])‖^2*‖(p : ℤ_[p])‖*‖((k*(a*t+b) : ℤ) : ℤ_[p])‖ ≤
          ‖2*(r : ℤ_[p])‖^2*‖(p : ℤ_[p])‖*1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ < ‖2*(r : ℤ_[p])‖^2 := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hpn hpos
  obtain ⟨z,hz,-⟩ := hensels_lemma hn
  refine ⟨z,?_⟩
  rw [hf] at hz
  simpa only [pow_two] using (sub_eq_zero.mp hz).symm

/-- There are arbitrarily large integer parameters passing all the listed local
square tests around any finite list of nonzero square values. -/
theorem simultaneous_local_perturbations (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {ι : Type*} [Fintype ι] (r a b : ι → ℤ) (hr : ∀ i, r i≠0) (N : ℤ) :
    ∃ t : ℤ, N<t ∧ ∀ (p : ℕ) (hp : p ∈ P),
      letI : Fact p.Prime := ⟨hP p hp⟩
      ∀ i, IsSquare (((r i)^2+t*(a i*t+b i) : ℤ) : ℤ_[p]) := by
  let M : ℤ := 4*(∏ p ∈ P, (p : ℤ))*(∏ i, (r i)^2)
  have hM : 0<M := by
    dsimp [M]
    apply mul_pos
    · apply mul_pos (by norm_num)
      apply Finset.prod_pos
      intro p hp
      exact_mod_cast (hP p hp).pos
    · apply Finset.prod_pos
      intro i _
      exact sq_pos_of_ne_zero (hr i)
  refine ⟨M*(|N|+1),?_,?_⟩
  · have : 1≤M := hM
    nlinarith [le_abs_self N,abs_nonneg N]
  · intro p hp
    letI : Fact p.Prime := ⟨hP p hp⟩
    intro i
    apply perturbation_isSquare_padic (hr i) _ (a i) (b i)
    apply dvd_mul_of_dvd_left
    dsimp [M]
    exact mul_dvd_mul
      (mul_dvd_mul_left 4 (Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hp))
      (Finset.dvd_prod_of_mem (fun j : ι => (r j)^2) (Finset.mem_univ i))

/-- An elementary global obstruction for the very same quadratic ray families:
a positive constant correction eventually lies strictly between consecutive
integer squares after multiplication by a fixed square. -/
lemma ray_quadratic_not_isSquare {w A R t : ℤ}
    (hC : 0<w^2*R^2-A^2) (ht : w^2*R^2-A^2≤w^2*t-A) :
    ¬ IsSquare (w^2*t^2-2*A*t+R^2) := by
  rintro ⟨z,hz⟩
  have he : (w*z)^2=(w^2*t-A)^2+(w^2*R^2-A^2) := by
    nlinarith only [congrArg (fun u : ℤ => w^2*u) hz]
  have hk : 0≤w^2*t-A := by omega
  have hlow : w^2*t-A < |w*z| := by
    apply (sq_lt_sq₀ hk (abs_nonneg _)).mp
    rw [sq_abs]
    linarith only [he,hC]
  have hhigh : |w*z| < w^2*t-A+1 := by
    apply (sq_lt_sq₀ (abs_nonneg _) (by omega)).mp
    rw [sq_abs]
    nlinarith only [he,ht,hC]
  omega

lemma ray_quadratic_not_rational_square {w A R t : ℤ}
    (hC : 0<w^2*R^2-A^2) (ht : w^2*R^2-A^2≤w^2*t-A) :
    ¬ IsSquare (((w^2*t^2-2*A*t+R^2 : ℤ)) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  exact ray_quadratic_not_isSquare hC ht

#print axioms perturbation_isSquare_padic
#print axioms simultaneous_local_perturbations
#print axioms ray_quadratic_not_rational_square
end Erdos213.FixedSourceLocal
