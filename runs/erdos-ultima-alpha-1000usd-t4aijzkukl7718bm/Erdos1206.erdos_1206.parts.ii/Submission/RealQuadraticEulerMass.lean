import FormalConjecturesUtil

/-! Real logarithmic Euler-product estimates for integer-valued Dirichlet
characters. These are analytic estimates, not a Sidon construction. -/
namespace Erdos1206.RealQuadraticEulerMass
open Finset
open scoped Classical

noncomputable def complexChar {N : ℕ} (χ : DirichletCharacter ℤ N) :
    DirichletCharacter ℂ N := χ.ringHomComp (Int.castRingHom ℂ)

noncomputable def primePower (s : ℝ) (p : Nat.Primes) : ℝ := (p:ℝ)^(-s)

lemma primePower_pos (s : ℝ) (p : Nat.Primes) : 0 < primePower s p :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _

lemma primePower_le_half {s : ℝ} (hs : 1 < s) (p : Nat.Primes) : primePower s p ≤ 1/2 := by
  have hp : (1:ℝ) ≤ p := by exact_mod_cast p.prop.one_le
  calc
    _ ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hp (by linarith)
    _ = 1/(p:ℝ) := by rw [Real.rpow_neg_one,one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast p.prop.two_le)

lemma summable_primePower {s : ℝ} (hs : 1 < s) : Summable (primePower s) := by
  exact Nat.Primes.summable_rpow.mpr (by linarith)

lemma primePower_cpow (s : ℝ) (p : Nat.Primes) :
    (primePower s p:ℂ) = (p:ℂ)^(-(s:ℂ)) := by
  simpa only [primePower,Complex.ofReal_neg,Complex.ofReal_natCast] using
    Complex.ofReal_cpow (show (0:ℝ) ≤ p by positivity) (-s)

lemma log_remainder {x : ℝ} (hx : |x| ≤ 1/2) :
    |Real.log (1-x)+x| ≤ 2*x^2 := by
  have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hx (by norm_num)) 1
  norm_num only [sum_range_succ,sum_range_zero,zero_add,zero_pow,one_pow,
    Nat.cast_zero,add_zero,zero_add,pow_one,div_one,Nat.reduceAdd] at h
  have hd : 0 < 1-|x| := by linarith
  have hle : |x|^2/(1-|x|) ≤ 2*x^2 := by
    apply (div_le_iff₀ hd).mpr
    rw [sq_abs]
    nlinarith [sq_nonneg x,mul_nonneg (sq_nonneg x) (show 0 ≤ 1/2-|x| by linarith)]
  have hh : |Real.log (1-x)+x| ≤ |x|^2/(1-|x|) := by
    simpa only [add_comm] using h
  exact hh.trans hle

lemma integer_abs_le_one {z : ℤ} (hz : z=0 ∨ z=1 ∨ z = -1) : |(z:ℝ)| ≤ 1 := by
  rcases hz with rfl | rfl | rfl <;> norm_num

lemma real_log_euler {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    {s : ℝ} (hs : 1 < s) :
    Real.log ‖LSeries (fun n => complexChar χ (n:ZMod N)) (s:ℂ)‖ =
      ∑' p : Nat.Primes, -Real.log (1-(χ (p:ZMod N):ℝ)*primePower s p) := by
  have hsC : 1 < (s:ℂ).re := hs
  have hsum := (summable_dirichletSummand (complexChar χ) hsC).of_norm.clog_one_sub.neg.subtype
    (fun p : ℕ => p.Prime)
  change Summable (fun p : Nat.Primes => -Complex.log
    (1-complexChar χ (p:ZMod N)*(p:ℂ)^(-(s:ℂ)))) at hsum
  rw [←DirichletCharacter.LSeries_eulerProduct_exp_log (complexChar χ) hsC,
    Complex.norm_exp,Real.log_exp,Complex.re_tsum hsum]
  apply tsum_congr
  intro p
  have hx : |(χ (p:ZMod N):ℝ)*primePower s p| ≤ 1/2 := by
    rw [abs_mul,abs_of_pos (primePower_pos s p)]
    calc
      _ ≤ 1*primePower s p := mul_le_mul_of_nonneg_right
        (integer_abs_le_one (hχ p)) (primePower_pos s p).le
      _ ≤ 1/2 := by simpa only [one_mul] using primePower_le_half hs p
  have hxpos : 0 < 1-(χ (p:ZMod N):ℝ)*primePower s p := by
    have := (le_abs_self ((χ (p:ZMod N):ℝ)*primePower s p)).trans hx
    linarith
  have he : 1-complexChar χ (p:ZMod N)*(p:ℂ)^(-(s:ℂ)) =
      ((1-(χ (p:ZMod N):ℝ)*primePower s p:ℝ):ℂ) := by
    rw [←primePower_cpow]
    simp only [complexChar,MulChar.ringHomComp_apply,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_intCast]
    rfl
  rw [Complex.neg_re,Complex.log_re,he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]

lemma summable_real_log {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1-(χ (p:ZMod N):ℝ)*primePower s p)) := by
  have hsum := (summable_primePower hs).mul_left 2
  apply hsum.of_norm_bounded
  intro p
  let x : ℝ := (χ (p:ZMod N):ℝ)*primePower s p
  have hx : |x| ≤ primePower s p := by
    dsimp only [x]
    rw [abs_mul,abs_of_pos (primePower_pos s p)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (integer_abs_le_one (hχ p)) (primePower_pos s p).le
  have hxhalf := hx.trans (primePower_le_half hs p)
  have hrem := log_remainder hxhalf
  have habs : |Real.log (1-x)| ≤ |Real.log (1-x)+x|+|x| := by
    simpa only [←sub_eq_add_neg,add_sub_cancel_right,abs_neg] using abs_add_le (Real.log (1-x)+x) (-x)
  have hsq : 2*x^2 ≤ |x| := by
    nlinarith [sq_abs x,mul_nonneg (abs_nonneg x) (show 0 ≤ 1/2-|x| by linarith)]
  simpa only [Real.norm_eq_abs,abs_neg] using habs.trans (by linarith)

lemma real_log_zeta {s : ℝ} (hs : 1 < s) :
    Real.log ‖riemannZeta (s:ℂ)‖ =
      ∑' p : Nat.Primes, -Real.log (1-primePower s p) := by
  have hh := real_log_euler (1:DirichletCharacter ℤ 1)
    (fun n => Or.inr (Or.inl (by simp [MulChar.one_apply (isUnit_of_subsingleton _)]))) hs
  simp only [complexChar,MulChar.ringHomComp_one,
    MulChar.one_apply (isUnit_of_subsingleton _),Int.cast_one,one_mul] at hh
  change Real.log ‖LSeries 1 (s:ℂ)‖ = _ at hh
  rwa [LSeries_one_eq_riemannZeta (show 1 < (s:ℂ).re from hs)] at hh

noncomputable def weightedMass {N : ℕ} (χ : DirichletCharacter ℤ N) (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (1-(χ (p:ZMod N):ℝ))*primePower s p

lemma summable_weightedMass {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => (1-(χ (p:ZMod N):ℝ))*primePower s p) := by
  apply ((summable_primePower hs).mul_left 2).of_nonneg_of_le
  · intro p
    have hh := integer_abs_le_one (hχ p)
    have hu := le_abs_self (χ (p:ZMod N):ℝ)
    exact mul_nonneg (by linarith) (primePower_pos s p).le
  · intro p
    have hh := integer_abs_le_one (hχ p)
    have hl := neg_abs_le (χ (p:ZMod N):ℝ)
    exact mul_le_mul_of_nonneg_right (by linarith) (primePower_pos s p).le

noncomputable def squareError : ℝ := 4*∑' p : Nat.Primes, (p:ℝ)^(-2:ℝ)

lemma log_ratio_le_weightedMass {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    {s : ℝ} (hs : 1 < s) :
    Real.log ‖riemannZeta (s:ℂ)‖ -
      Real.log ‖LSeries (fun n => complexChar χ (n:ZMod N)) (s:ℂ)‖ ≤
        weightedMass χ s+squareError := by
  have hsq : Summable (fun p : Nat.Primes => (p:ℝ)^(-2:ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have htriv := summable_real_log (1:DirichletCharacter ℤ 1)
    (fun n => Or.inr (Or.inl (by simp [MulChar.one_apply (isUnit_of_subsingleton _)]))) hs
  simp only [MulChar.one_apply (isUnit_of_subsingleton _),Int.cast_one,one_mul] at htriv
  rw [real_log_zeta hs,real_log_euler χ hχ hs,←htriv.tsum_sub (summable_real_log χ hχ hs)]
  change _ ≤ (∑' p : Nat.Primes, (1-(χ (p:ZMod N):ℝ))*primePower s p)+
    4*(∑' p : Nat.Primes, (p:ℝ)^(-2:ℝ))
  rw [←tsum_mul_left,←(summable_weightedMass χ hχ hs).tsum_add (hsq.mul_left 4)]
  apply Summable.tsum_le_tsum _ (htriv.sub (summable_real_log χ hχ hs))
    ((summable_weightedMass χ hχ hs).add (hsq.mul_left 4))
  intro p
  let x := primePower s p
  let y : ℝ := (χ (p:ZMod N):ℝ)*x
  have hxpos : 0 < x := primePower_pos s p
  have hxhalf : x ≤ 1/2 := primePower_le_half hs p
  have hyabs : |y| ≤ x := by
    dsimp only [y]
    rw [abs_mul,abs_of_pos hxpos]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (integer_abs_le_one (hχ p)) hxpos.le
  have hxrem := log_remainder (show |x| ≤ 1/2 by rwa [abs_of_pos hxpos])
  have hyrem := log_remainder (hyabs.trans hxhalf)
  have hy2 : y^2 ≤ x^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hxpos.le).mpr hyabs
  have hx2 : x^2 ≤ (p:ℝ)^(-2:ℝ) := by
    dsimp only [x,primePower]
    rw [←Real.rpow_mul_natCast (show (0:ℝ) ≤ p by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ p by exact_mod_cast p.prop.one_le) (by norm_num only [Nat.cast_ofNat]; linarith)
  have hxL := (abs_le.mp hxrem).1
  have hyU := (abs_le.mp hyrem).2
  change -Real.log (1-x)-(-Real.log (1-y)) ≤ (1-(χ (p:ZMod N):ℝ))*x+4*(p:ℝ)^(-2:ℝ)
  dsimp only [y] at hyU hy2 ⊢
  nlinarith only [hxL,hyU,hy2,hx2]

#print axioms primePower_le_half
#print axioms log_remainder
#print axioms real_log_zeta
#print axioms log_ratio_le_weightedMass
#print axioms real_log_euler
#print axioms summable_real_log
end Erdos1206.RealQuadraticEulerMass
