import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

/-! Auxiliary square-value detection for polynomial construction attempts.
This file by itself does not assert anything about unrestricted integral-distance sets. -/
namespace Erdos213.PolynomialSquareValues
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000

/-- Schur's prime-divisor argument, with a lower bound on the evaluation point
and an arbitrary nonzero integer whose prime divisors must be avoided. -/
lemma fresh_prime_divisor (f : ℤ[X]) (hf : 0 < f.natDegree) (M N : ℤ) (hM : M ≠ 0) :
    ∃ (n : ℤ) (p : ℕ), N ≤ n ∧ p.Prime ∧ (p : ℤ) ∣ f.eval n ∧ ¬ (p : ℤ) ∣ M := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  obtain ⟨a,ha⟩ : ∃ a : ℤ, f.eval a ≠ 0 := by
    by_contra! h
    exact hf0 (zero_of_eval_zero f h)
  let c := f.eval a
  let d := c*M
  have hd : d ≠ 0 := mul_ne_zero ha hM
  let F := f.comp (C (d^2)*X+C a)
  have hdeg : F.natDegree=f.natDegree := by
    dsimp [F]
    rw [natDegree_comp]
    have hh : (C (d^2)*X+C a : ℤ[X]).natDegree=1 := by compute_degree!
    rw [hh,mul_one]
  have hne (b : ℤ) : F-C b ≠ 0 := by
    intro hh
    have he : F=C b := sub_eq_zero.mp hh
    have hz := congrArg natDegree he
    simp only [natDegree_C,hdeg] at hz
    omega
  obtain ⟨t,ht,ht'⟩ := (Set.Ici_infinite (max 0 (N-a))).exists_notMem_finite
    ((finite_setOf_isRoot (hne c)).union (finite_setOf_isRoot (hne (-c))))
  have htp : 0 ≤ t := le_trans (le_max_left _ _) ht
  have htN : N-a ≤ t := le_trans (le_max_right _ _) ht
  let n := a+d^2*t
  have hn : N ≤ n := by
    have hd2 : (1 : ℤ) ≤ d^2 := by nlinarith [sq_pos_of_ne_zero hd]
    dsimp [n]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd2) htp]
  have heval : F.eval t=f.eval n := by simp [F,n,add_comm]
  have hv1 : f.eval n ≠ c := by
    intro h
    apply ht'
    left
    simp [IsRoot,heval,h]
  have hv2 : f.eval n ≠ -c := by
    intro h
    apply ht'
    right
    simp [IsRoot,heval,h]
  have hdvd : c*M ∣ f.eval n-c := by
    apply dvd_trans ?_ (sub_dvd_eval_sub n a f)
    refine ⟨d*t,?_⟩
    dsimp [n,d]
    ring
  obtain ⟨k,hk⟩ := hdvd
  have hv : f.eval n=c*(1+M*k) := by linear_combination hk
  have hq : (1+M*k).natAbs ≠ 1 := by
    intro he
    rcases Int.natAbs_eq_iff.mp he with h | h
    · apply hv1; simp [hv,h]
    · apply hv2; rw [hv,h]; ring
  obtain ⟨p,hp,hpq⟩ := Nat.exists_prime_and_dvd hq
  have hpq' : (p : ℤ) ∣ 1+M*k := Int.natCast_dvd.mpr hpq
  refine ⟨n,p,hn,hp,?_,?_⟩
  · rw [hv]; exact dvd_mul_of_dvd_right hpq' c
  · intro hpM
    have hdiv : (p : ℤ) ∣ 1 := by
      convert dvd_sub hpq' (dvd_mul_of_dvd_left hpM k) using 1; ring
    exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast hdiv))

lemma eval_step_remainder (f : ℤ[X]) (a p : ℤ) :
    ∃ r : ℤ, f.eval (a+p)=f.eval a+p*f.derivative.eval a+p^2*r := by
  have hd : (X : ℤ[X])^2 ∣ f.taylor a-C (f.eval a)-C (f.derivative.eval a)*X := by
    rw [X_pow_dvd_iff]
    intro i hi
    interval_cases i <;> simp only [coeff_sub,coeff_C,coeff_C_mul,coeff_X,
      taylor_coeff_zero,taylor_coeff_one] <;> norm_num
  have he := eval_dvd (x := p) hd
  simp only [eval_pow,eval_X,eval_sub,eval_C,eval_mul,taylor_eval] at he
  obtain ⟨r,hr⟩ := he
  refine ⟨r,?_⟩
  rw [add_comm a p]
  linear_combination hr

/-- A prime dividing a polynomial value but not the derivative can be made to
occur exactly once, at the same argument or at its translate by that prime. -/
lemma simple_prime_value (f : ℤ[X]) (a : ℤ) (p : ℕ) (hp : p.Prime)
    (hval : (p : ℤ) ∣ f.eval a) (hder : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    ∃ n : ℤ, a ≤ n ∧ (p : ℤ) ∣ f.eval n ∧ ¬ (p : ℤ)^2 ∣ f.eval n := by
  by_cases h2 : (p : ℤ)^2 ∣ f.eval a
  · refine ⟨a+p,by omega,?_,?_⟩
    obtain ⟨r,hr⟩ := eval_step_remainder f a p
    · rw [hr]
      exact dvd_add (dvd_add hval (dvd_mul_right _ _))
        (dvd_mul_of_dvd_left (dvd_pow_self _ (by norm_num)) r)
    · intro hh
      obtain ⟨r,hr⟩ := eval_step_remainder f a p
      have hs : (p : ℤ)^2 ∣ (p : ℤ)*f.derivative.eval a := by
        convert dvd_sub (dvd_sub hh h2) (dvd_mul_right ((p : ℤ)^2) r) using 1
        rw [hr]
        ring
      rw [pow_two,mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)] at hs
      exact hder hs
  · exact ⟨a,le_rfl,hval,h2⟩

lemma not_square_of_simple_prime {z : ℤ} {p : ℕ} (hp : p.Prime)
    (hz : (p : ℤ) ∣ z) (h2 : ¬ (p : ℤ)^2 ∣ z) : ¬ IsSquare z := by
  rintro ⟨r,rfl⟩
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hr : (p : ℤ) ∣ r := (hp'.dvd_mul.mp hz).elim id id
  exact h2 (by simpa only [pow_two] using mul_dvd_mul hr hr)

/-- Clearing one polynomial's rational coefficient denominators. -/
lemma clear_denominator (f : ℚ[X]) :
    ∃ (d : ℤ) (F : ℤ[X]), d ≠ 0 ∧ F.map (Int.castRingHom ℚ)=C (d : ℚ)*f := by
  obtain ⟨d,hd⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) f
  refine ⟨d,IsLocalization.integerNormalization (nonZeroDivisors ℤ) f,?_,?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp d.property
  · simpa only [Algebra.smul_def,algebraMap_eq,Int.coe_castRingHom] using hd

lemma integral_bezout (F : ℤ[X])
    (hF : Squarefree (F.map (Int.castRingHom ℚ))) :
    ∃ (A B : ℤ[X]) (D : ℤ), D ≠ 0 ∧ A*F+B*F.derivative=C D := by
  obtain ⟨a,b,hab⟩ := (PerfectField.separable_iff_squarefree.mpr hF :
    (F.map (Int.castRingHom ℚ)).Separable)
  obtain ⟨d,A,hd,hA⟩ := clear_denominator a
  obtain ⟨e,B,he,hB⟩ := clear_denominator b
  refine ⟨C e*A,C d*B,d*e,mul_ne_zero hd he,?_⟩
  apply (Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ)))
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
    Int.coe_castRingHom,Int.cast_mul,hA,hB,← derivative_map]
  simp only [map_mul]
  linear_combination (C (d : ℚ)*C (e : ℚ))*hab

/-- A nonconstant rational-squarefree integer polynomial has nonsquare values
at arbitrarily large integer arguments. -/
theorem squarefree_nonsquare_value (F : ℤ[X]) (hdeg : 0 < F.natDegree)
    (hF : Squarefree (F.map (Int.castRingHom ℚ))) (N : ℤ) :
    ∃ n : ℤ, N ≤ n ∧ ¬ IsSquare ((F.eval n : ℤ) : ℚ) := by
  obtain ⟨A,B,D,hD,hbez⟩ := integral_bezout F hF
  obtain ⟨a,p,ha,hp,hval,hpD⟩ := fresh_prime_divisor F hdeg D N hD
  have hder : ¬ (p : ℤ) ∣ F.derivative.eval a := by
    intro hd
    have hh := congrArg (fun f : ℤ[X] => f.eval a) hbez
    simp only [eval_add,eval_mul,eval_C] at hh
    apply hpD
    rw [← hh]
    exact dvd_add (dvd_mul_of_dvd_right hval _) (dvd_mul_of_dvd_right hd _)
  obtain ⟨n,hn,hv,hn2⟩ := simple_prime_value F a p hp hval hder
  refine ⟨n,ha.trans hn,?_⟩
  intro hs
  exact not_square_of_simple_prime hp hv hn2 (Rat.isSquare_intCast_iff.mp hs)

@[simp] lemma eval_int_map (F : ℤ[X]) (n : ℤ) :
    (F.map (Int.castRingHom ℚ)).eval (n : ℚ)=((F.eval n : ℤ) : ℚ) := by
  rw [eval_map]
  exact eval₂_at_apply (Int.castRingHom ℚ) n

lemma squarefree_degree_zero (f : ℚ[X]) (hf : Squarefree f)
    (N : ℤ) (hs : ∀ n : ℤ, N ≤ n → IsSquare (f.eval (n : ℚ))) : f.natDegree=0 := by
  by_contra hdeg
  obtain ⟨d,F,hd,hF⟩ := clear_denominator f
  let G : ℤ[X] := C d*F
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hG : G.map (Int.castRingHom ℚ)=C ((d : ℚ)^2)*f := by
    simp [G,hF,pow_two,map_mul,mul_assoc]
  have hu : IsUnit (C ((d : ℚ)^2) : ℚ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hdQ))
  have hGs : Squarefree (G.map (Int.castRingHom ℚ)) := by
    rw [hG]
    exact squarefree_mul_iff.mpr ⟨hu.isRelPrime_left,hu.squarefree,hf⟩
  have hGdeg : 0 < G.natDegree := by
    have he := congrArg natDegree hG
    rw [natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)),
      natDegree_C_mul (pow_ne_zero _ hdQ)] at he
    omega
  obtain ⟨n,hn,hns⟩ := squarefree_nonsquare_value G hGdeg hGs N
  apply hns
  have he := congrArg (fun p : ℚ[X] => p.eval (n : ℚ)) hG
  simp only [eval_int_map,eval_mul,eval_C] at he
  rw [he]
  exact (IsSquare.sq (d : ℚ)).mul (hs n hn)

/-- A rational polynomial taking rational square values at every sufficiently
large integer is itself a square. Isolated or merely infinitely many square
values are deliberately not sufficient hypotheses here. -/
theorem isSquare_of_eventually_int_eval (f : ℚ[X])
    (hs : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare (f.eval (n : ℚ))) : IsSquare f := by
  suffices ∀ d : ℕ, ∀ f : ℚ[X], f.natDegree=d →
      (∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare (f.eval (n : ℚ))) → IsSquare f from
    this f.natDegree f rfl hs
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hdeg hs
    obtain ⟨N,hN⟩ := hs
    by_cases hf0 : f=0
    · exact hf0 ▸ ⟨0,by simp⟩
    by_cases hsf : Squarefree f
    · have hd0 := squarefree_degree_zero f hsf N hN
      have he := eq_C_of_natDegree_eq_zero hd0
      obtain ⟨r,hr⟩ := hN N le_rfl
      rw [he,eval_C] at hr
      refine ⟨C r,?_⟩
      rw [he,hr,map_mul]
    obtain ⟨g,hgf,hgu⟩ : ∃ g : ℚ[X], g*g ∣ f ∧ ¬ IsUnit g := by
      simpa only [Squarefree,not_forall,_root_.not_imp,exists_prop] using hsf
    obtain ⟨q,hfq⟩ := hgf
    have hg0 : g ≠ 0 := by intro h; exact hf0 (by simp [hfq,h])
    have hq0 : q ≠ 0 := by intro h; exact hf0 (by simp [hfq,h])
    have hgd : 0 < g.natDegree := by
      by_contra! hh
      have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hh)
      apply hgu
      rw [he]
      apply isUnit_C.mpr
      apply isUnit_iff_ne_zero.mpr
      intro hh
      exact hg0 (by rw [he,hh]; simp)
    have hqd : q.natDegree < d := by
      have he := congrArg natDegree hfq
      rw [natDegree_mul (mul_ne_zero hg0 hg0) hq0,natDegree_mul hg0 hg0,hdeg] at he
      omega
    obtain ⟨R,hR⟩ := exists_max_root g hg0
    obtain ⟨N₀,hN₀⟩ := exists_int_gt R
    have hqs : ∃ K : ℤ, ∀ n : ℤ, K ≤ n → IsSquare (q.eval (n : ℚ)) := by
      refine ⟨max N N₀,?_⟩
      intro n hn
      have hgn : g.eval (n : ℚ) ≠ 0 := by
        intro hz
        have hh := hR (n : ℚ) hz
        have hh' : (N₀ : ℚ) ≤ n := by exact_mod_cast (le_max_right N N₀).trans hn
        linarith
      have hfn := hN n ((le_max_left _ _).trans hn)
      have he : f.eval (n : ℚ)/(g.eval (n : ℚ))^2=q.eval (n : ℚ) := by
        rw [hfq,eval_mul,eval_mul,pow_two]
        field_simp
      rw [← he]
      exact hfn.div (IsSquare.sq _)
    obtain ⟨r,hr⟩ := ih q.natDegree hqd q rfl hqs
    exact ⟨g*r,by rw [hfq,hr]; ring⟩

#print axioms fresh_prime_divisor
#print axioms squarefree_nonsquare_value
#print axioms isSquare_of_eventually_int_eval
end
end Erdos213.PolynomialSquareValues
