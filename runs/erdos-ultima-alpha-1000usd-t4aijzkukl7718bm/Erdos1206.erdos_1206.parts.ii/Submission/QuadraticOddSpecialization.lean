import Submission.QuadraticTripleDichotomy
import Submission.CollinearTripleParity

/-!
An all-odd, six-distinct specialization of a rational quadratic triple family
forces that family to be a common polynomial dilation. This does not exclude
all-odd numerical triples, which can occur as constant configurations.
-/
namespace Erdos1206.QuadraticOddSpecialization
open Polynomial FermatCubicConics QuadraticResidualBridge QuadraticTripleClassification
open QuadraticTripleDichotomy CollinearTripleParity

private lemma eval_ne_of_values {p q : ℚ[X]} {t : ℚ} {a b : ℤ}
    (hp : p.eval t=(a:ℚ)) (hq : q.eval t=(b:ℚ)) (hab : a ≠ b) : p ≠ q := by
  intro he
  have hh : (a:ℚ)=(b:ℚ) := hp.symm.trans ((congrArg (fun p : ℚ[X] => p.eval t) he).trans hq)
  exact hab (by exact_mod_cast hh)

private lemma eval_nonzero_of_odd {p : ℚ[X]} {t : ℚ} {a : ℤ}
    (hp : p.eval t=(a:ℚ)) (ha : Odd a) : p ≠ 0 := by
  intro hz
  rw [hz,eval_zero] at hp
  have ha0 : a=0 := by exact_mod_cast hp.symm
  rw [ha0] at ha
  norm_num at ha

private lemma eval_cubes {p q : Pair} {t : ℚ} {a b c d : ℤ}
    (hc : quad p.1^3+quad p.2^3=quad q.1^3+quad q.2^3)
    (ha : (quad p.1).eval t=(a:ℚ)) (hb : (quad p.2).eval t=(b:ℚ))
    (hc' : (quad q.1).eval t=(c:ℚ)) (hd : (quad q.2).eval t=(d:ℚ)) :
    a^3+b^3=c^3+d^3 := by
  have hh := congrArg (fun p : ℚ[X] => p.eval t) hc
  simp only [eval_add,eval_pow,ha,hb,hc',hd] at hh
  exact_mod_cast hh

private lemma collinear_odd_false {p q r : Pair} {t : ℚ} {a b c d e f : ℤ}
    (hcol : Collinear p q r)
    (ha : (quad p.1).eval t=(a:ℚ)) (hb : (quad p.2).eval t=(b:ℚ))
    (hc : (quad q.1).eval t=(c:ℚ)) (hd : (quad q.2).eval t=(d:ℚ))
    (he : (quad r.1).eval t=(e:ℚ)) (hf : (quad r.2).eval t=(f:ℚ))
    (hn : a^3+b^3 ≠ 0) (hc₁ : a^3+b^3=c^3+d^3) (hc₂ : a^3+b^3=e^3+f^3)
    (hao : Odd a) (hbo : Odd b) (hco : Odd c) (hdo : Odd d) (heo : Odd e) (hfo : Odd f)
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f) : False := by
  have hh := hcol ![t^2,t,1]
  rw [← quad_eval,← quad_eval,← quad_eval,← quad_eval,← quad_eval,← quad_eval] at hh
  rw [ha,hb,hc,hd,he,hf] at hh
  have hcol' : (c-a)*(f-b)=(e-a)*(d-b) := by exact_mod_cast hh
  exact odd_collinear_triple_false a b c d e f (a^3+b^3) hn
    hao hbo hco hdo heo hfo hac hae hce hbd hbf hdf rfl hc₁.symm hc₂.symm hcol'

/-- Genuine projectively varying quadratic triples have no specialization
with six distinct odd integer coordinates and nonzero common cube sum. -/
theorem odd_specialization_common {p q r : Pair} {t : ℚ} {v : Fin 6 → ℤ}
    (hc₁ : quad p.1^3+quad p.2^3=quad q.1^3+quad q.2^3)
    (hc₂ : quad p.1^3+quad p.2^3=quad r.1^3+quad r.2^3)
    (ha : (quad p.1).eval t=(v 0:ℚ)) (hb : (quad p.2).eval t=(v 1:ℚ))
    (hc : (quad q.1).eval t=(v 2:ℚ)) (hd : (quad q.2).eval t=(v 3:ℚ))
    (he : (quad r.1).eval t=(v 4:ℚ)) (hf : (quad r.2).eval t=(v 5:ℚ))
    (hv : Function.Injective v) (ho : ∀ i, Odd (v i))
    (hn : (v 0)^3+(v 1)^3 ≠ 0) : CommonTriple p q r := by
  have hvn {i j : Fin 6} (hij : i ≠ j) : v i ≠ v j := fun hh => hij (hv hh)
  have hnp : quad p.1^3+quad p.2^3 ≠ 0 := by
    intro hz
    have hh := congrArg (fun p : ℚ[X] => p.eval t) hz
    simp only [eval_add,eval_pow,eval_zero,ha,hb] at hh
    exact hn (by exact_mod_cast hh)
  have hC₁ := eval_cubes hc₁ ha hb hc hd
  have hC₂ := eval_cubes hc₂ ha hb he hf
  rcases common_or_collinear_after_swaps hc₁ hc₂ hnp
    (eval_nonzero_of_odd ha (ho 0)) (eval_nonzero_of_odd hb (ho 1))
    (eval_nonzero_of_odd hc (ho 2)) (eval_nonzero_of_odd hd (ho 3))
    (eval_nonzero_of_odd he (ho 4)) (eval_nonzero_of_odd hf (ho 5))
    (eval_ne_of_values ha hb (hvn (by decide)))
    (eval_ne_of_values hc hd (hvn (by decide)))
    (eval_ne_of_values he hf (hvn (by decide)))
    (eval_ne_of_values ha hc (hvn (by decide)))
    (eval_ne_of_values ha hd (hvn (by decide)))
    (eval_ne_of_values ha he (hvn (by decide)))
    (eval_ne_of_values ha hf (hvn (by decide)))
    (eval_ne_of_values hc he (hvn (by decide)))
    (eval_ne_of_values hc hf (hvn (by decide))) with hQ | hcol | hcol | hcol | hcol
  · exact hQ
  · exact (collinear_odd_false hcol ha hb hc hd he hf hn hC₁ hC₂
      (ho 0) (ho 1) (ho 2) (ho 3) (ho 4) (ho 5)
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))).elim
  · exact (collinear_odd_false hcol ha hb hd hc he hf hn
      (by rw [add_comm ((v 3)^3)]; exact hC₁) hC₂
      (ho 0) (ho 1) (ho 3) (ho 2) (ho 4) (ho 5)
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))).elim
  · exact (collinear_odd_false hcol ha hb hc hd hf he hn hC₁
      (by rw [add_comm ((v 5)^3)]; exact hC₂)
      (ho 0) (ho 1) (ho 2) (ho 3) (ho 5) (ho 4)
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))).elim
  · exact (collinear_odd_false hcol ha hb hd hc hf he hn
      (by rw [add_comm ((v 3)^3)]; exact hC₁)
      (by rw [add_comm ((v 5)^3)]; exact hC₂)
      (ho 0) (ho 1) (ho 3) (ho 2) (ho 5) (ho 4)
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))
      (hvn (by decide)) (hvn (by decide)) (hvn (by decide))).elim

#print axioms odd_specialization_common
end Erdos1206.QuadraticOddSpecialization
