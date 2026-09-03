import Submission.UnitCubeNormalForm

/-! A uniform arithmetic progression of obstructed unit-cube fibers.
This excludes a rational-function section over the first parameter, not
arbitrary rational specializations, base changes, or point sets. -/
namespace Erdos213.UnitCubeNoSection
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

variable {R : Type*} [CommRing R]
def hx (a b : R) : R := b^4-6*a^2*b^2+a^4
def hy (a b : R) : R := 4*a*b*(b^2-a^2)
def hw (a b : R) : R := (a^2+b^2)^2
def sign (e : Bool) : R := if e then 1 else -1

def numerator (t a b : R) (e f : Bool) : R :=
  (hw t 1*hw a b+sign e*hx t 1*hw a b+sign f*hx a b*hw t 1)^2+
  (sign e*hy t 1*hw a b+sign f*hy a b*hw t 1)^2

lemma map_numerator {S : Type*} [CommRing S] (g : R →+* S)
    (t a b : R) (e f : Bool) :
    g (numerator t a b e f)=numerator (g t) (g a) (g b) e f := by
  cases e <;> cases f <;> simp [numerator,hx,hy,hw,sign,map_ofNat]

private lemma local_seven : ∀ a b : ZMod 7,
    (∀ e f : Bool, IsSquare (numerator (2 : ZMod 7) a b e f)) → a=0 ∧ b=0 := by
  decide

lemma cleared_body (t a b : ℚ) (hb : b ≠ 0) (e f : Bool) :
    (hw t 1*hw a b)^2*UnitCubeNormalForm.body t (a/b) (sign e) (sign f)=
      numerator t a b e f := by
  have h1 : (1 : ℚ)+t^2 ≠ 0 := ne_of_gt (by positivity)
  have h2 : a^2+b^2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg a,sq_pos_of_ne_zero hb])
  cases e <;> cases f <;>
    simp only [UnitCubeNormalForm.body,UnitCubeNormalForm.vx,UnitCubeNormalForm.vy,
      numerator,hx,hy,hw,sign,if_true,one_pow] <;>
    field_simp <;> ring

lemma clear_integer_square {t a b : ℤ} (hb : b ≠ 0) (e f : Bool)
    (h : IsSquare (UnitCubeNormalForm.body (t : ℚ) ((a : ℚ)/(b : ℚ)) (sign e) (sign f))) :
    IsSquare (numerator t a b e f) := by
  obtain ⟨r,hr⟩ := h
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨hw (t : ℚ) 1*hw (a : ℚ) (b : ℚ)*r,?_⟩
  have hn := cleared_body (t : ℚ) (a : ℚ) (b : ℚ) (by exact_mod_cast hb) e f
  rw [hr] at hn
  have hm := map_numerator (Int.castRingHom ℚ) t a b e f
  change ((numerator t a b e f : ℤ) : ℚ)=numerator (t : ℚ) (a : ℚ) (b : ℚ) e f at hm
  rw [hm]
  linear_combination -hn

lemma numerator_eval (t a b : ℚ[X]) (q : ℚ) (e f : Bool) :
    (numerator t a b e f).eval q=numerator (t.eval q) (a.eval q) (b.eval q) e f :=
  map_numerator (evalRingHom q) t a b e f

/-- No second rational parameter works at ANY integer first parameter
congruent to two modulo seven. Denominators of the second parameter are
handled using its primitive numerator and denominator. -/
theorem no_four_bodies_at_residue (k : ℤ) (s : ℚ) :
    ¬ (∀ e f : Bool, IsSquare
      (UnitCubeNormalForm.body ((2+7*k : ℤ) : ℚ) s (sign e) (sign f))) := by
  intro h
  have hN : ∀ e f : Bool, IsSquare (numerator (2+7*k) s.num (s.den : ℤ) e f) := by
    intro e f
    apply clear_integer_square (by exact_mod_cast s.den_ne_zero)
    simpa only [Int.cast_natCast,s.num_div_den] using h e f
  have hmod : ∀ e f : Bool,
      IsSquare (numerator (2 : ZMod 7) (s.num : ZMod 7) (s.den : ZMod 7) e f) := by
    intro e f
    obtain ⟨r,hr⟩ := hN e f
    refine ⟨(r : ZMod 7),?_⟩
    have hh := congrArg (Int.castRingHom (ZMod 7)) hr
    rw [map_numerator] at hh
    norm_num only [map_add,map_mul,map_ofNat] at hh
    rw [show (7 : ZMod 7)=0 by decide] at hh
    simpa using hh
  have hdiv := local_seven (s.num : ZMod 7) (s.den : ZMod 7) hmod
  have hn : (7 : ℤ) ∣ s.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdiv.1
  have hd : (7 : ℤ) ∣ (s.den : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using hdiv.2)
  obtain ⟨u,v,huv⟩ := s.isCoprime_num_den
  have hbad : (7 : ℤ) ∣ 1 := by
    rw [←huv]
    exact dvd_add (dvd_mul_of_dvd_right hn u) (dvd_mul_of_dvd_right hd v)
  norm_num at hbad

lemma body_square_of_numerator_square {t a b : ℚ} (hb : b ≠ 0) (e f : Bool)
    (h : IsSquare (numerator t a b e f)) :
    IsSquare (UnitCubeNormalForm.body t (a/b) (sign e) (sign f)) := by
  obtain ⟨r,hr⟩ := h
  have h1 : hw t (1 : ℚ) ≠ 0 := by unfold hw; positivity
  have h2 : hw a b ≠ 0 := by
    unfold hw
    exact pow_ne_zero 2 (ne_of_gt (by nlinarith [sq_nonneg a,sq_pos_of_ne_zero hb]))
  have hd : hw t 1*hw a b ≠ 0 := mul_ne_zero h1 h2
  have hc := cleared_body t a b hb e f
  rw [hr] at hc
  refine ⟨r/(hw t 1*hw a b),?_⟩
  field_simp
  linear_combination hc

lemma progression_eval_ne_zero (B : ℚ[X]) (hB : B ≠ 0) :
    ∃ k : ℤ, B.eval ((2+7*k : ℤ) : ℚ) ≠ 0 := by
  obtain ⟨M,hM⟩ := B.exists_max_root hB
  obtain ⟨k,hk⟩ := exists_int_gt ((M-2)/7)
  refine ⟨k,?_⟩
  intro he
  have hb := hM ((2+7*k : ℤ) : ℚ) he
  push_cast at hb
  linarith

/-- There are no polynomial numerator/denominator data for a section with
all four cleared body norms square. This has no degree cutoff. -/
theorem no_polynomial_section (A B : ℚ[X]) (hB : B ≠ 0) :
    ¬ (∀ e f : Bool, IsSquare (numerator X A B e f)) := by
  intro h
  obtain ⟨k,hk⟩ := progression_eval_ne_zero B hB
  let q : ℚ := ((2+7*k : ℤ) : ℚ)
  apply no_four_bodies_at_residue k (A.eval q/B.eval q)
  intro e f
  apply body_square_of_numerator_square hk e f
  obtain ⟨p,hp⟩ := h e f
  refine ⟨p.eval q,?_⟩
  have he := congrArg (fun p : ℚ[X] => p.eval q) hp
  dsimp only at he
  rw [numerator_eval] at he
  simpa only [eval_X,eval_one,eval_mul] using he

private lemma square_ratFunc_iff (p : ℚ[X]) :
    IsSquare (algebraMap ℚ[X] (RatFunc ℚ) p) ↔ IsSquare p := by
  constructor
  · rintro ⟨r,hr⟩
    have hint : IsIntegral ℚ[X] (r^2) := by
      rw [pow_two,←hr]
      exact isIntegral_algebraMap
    obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := ℚ[X]) (K := RatFunc ℚ) (by norm_num : 0 < (2 : ℕ)) hint
    refine ⟨q,?_⟩
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    simpa [map_mul,hq] using hr
  · rintro ⟨q,hq⟩
    exact ⟨algebraMap ℚ[X] (RatFunc ℚ) q,by simp [hq]⟩

/-- A rational second parameter A/B cannot make all four body norms square
in Q(X), even allowing arbitrary rational-function square roots. The first
parameter here is X itself, not an arbitrary rational base change. -/
theorem no_rational_function_section (A B : ℚ[X]) (hB : B ≠ 0) :
    ¬ (∀ e f : Bool, IsSquare
      (algebraMap ℚ[X] (RatFunc ℚ) (numerator X A B e f))) := by
  simpa only [square_ratFunc_iff] using no_polynomial_section A B hB

lemma inverse_coordinates (t : ℚ) :
    UnitCubeNormalForm.vx (1/t)=UnitCubeNormalForm.vx t ∧
    UnitCubeNormalForm.vy (1/t)= -UnitCubeNormalForm.vy t := by
  by_cases ht : t=0
  · simp [ht,UnitCubeNormalForm.vx,UnitCubeNormalForm.vy]
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  constructor <;> simp only [UnitCubeNormalForm.vx,UnitCubeNormalForm.vy] <;>
    field_simp <;> ring

lemma inverse_body (t s e f : ℚ) :
    UnitCubeNormalForm.body (1/t) (1/s) e f=UnitCubeNormalForm.body t s e f := by
  unfold UnitCubeNormalForm.body
  rw [(inverse_coordinates t).1,(inverse_coordinates t).2,
    (inverse_coordinates s).1,(inverse_coordinates s).2]
  ring

/-- The first parameter in the old t=1/2,s=2/3 geometric control in fact
cannot participate in ANY all-square unit cube, irrespective of s. -/
theorem no_four_bodies_half (s : ℚ) :
    ¬ (∀ e f : Bool, IsSquare (UnitCubeNormalForm.body (1/2) s (sign e) (sign f))) := by
  intro h
  have hn : ¬ (∀ e f : Bool, IsSquare
      (UnitCubeNormalForm.body 2 (1/s) (sign e) (sign f))) := by
    simpa using no_four_bodies_at_residue 0 (1/s)
  apply hn
  intro e f
  have he := inverse_body (1/2) s (sign e) (sign f)
  norm_num at he
  rw [one_div,he]
  exact h e f

#print axioms local_seven
#print axioms cleared_body
#print axioms no_four_bodies_at_residue
#print axioms no_polynomial_section
#print axioms no_rational_function_section
#print axioms no_four_bodies_half
end
end Erdos213.UnitCubeNoSection
