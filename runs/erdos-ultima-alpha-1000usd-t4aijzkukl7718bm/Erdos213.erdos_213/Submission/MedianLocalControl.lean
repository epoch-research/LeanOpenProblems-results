import Submission.MedianDiscriminant
import Submission.LocalParabolaPadic

/-!
An exact local control for the six-square median surface. For every finite set
of primes there are positive, nondegenerate integer side lengths satisfying
all the square conditions at those p-adic places. One doubled median is
nevertheless irrational. This is not a local-global principle or a witness
for Erdős 213.
-/

namespace Erdos213.MedianLocalControl

open Polynomial

set_option maxHeartbeats 1000000

def med₀ {R : Type*} [CommRing R] (a b c : R) : R := 2*a^2+2*b^2-c^2
def med₁ {R : Type*} [CommRing R] (a b c : R) : R := 2*a^2-b^2+2*c^2
def med₂ {R : Type*} [CommRing R] (a b c : R) : R := -a^2+2*b^2+2*c^2
def delta {R : Type*} [CommRing R] (a b c : R) : R :=
  a^4+b^4+c^4-a^2*b^2-a^2*c^2-b^2*c^2
def heron {R : Type*} [CommRing R] (a b c : R) : R :=
  2*a^2*b^2+2*a^2*c^2+2*b^2*c^2-a^4-b^4-c^4

def scale (K : ℤ) : ℤ := 25*K^2+1

def sideA (K : ℤ) : ℤ := 3*scale K
def sideB (K : ℤ) : ℤ := 4*scale K
def sideC (K : ℤ) : ℤ := 7*scale K-K

lemma error_identities (K L : ℤ) :
    med₀ (3*L) (4*L) (7*L-K)-L^2 = K*(14*L-K) ∧
    med₁ (3*L) (4*L) (7*L-K)-(10*L)^2 = 2*K*(K-14*L) ∧
    med₂ (3*L) (4*L) (7*L-K)-(11*L)^2 = 2*K*(K-14*L) ∧
    delta (3*L) (4*L) (7*L-K)-(37*L^2)^2 =
      K*(K-14*L)*(K^2-14*K*L+73*L^2) := by
  unfold med₀ med₁ med₂ delta
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma heron_factor (K L : ℤ) :
    heron (3*L) (4*L) (7*L-K) = K*(14*L-K)*(8*L-K)*(6*L-K) := by
  unfold heron
  ring

lemma scale_gt {K : ℤ} (hK : 0<K) : K<scale K := by
  have hK1 : 1≤K := by omega
  unfold scale
  nlinarith [sq_nonneg (K-1)]

lemma positive_triangle {K : ℤ} (hK : 0<K) :
    0<sideA K ∧ sideA K<sideB K ∧ sideB K<sideC K ∧
      0<heron (sideA K) (sideB K) (sideC K) := by
  have hL := scale_gt hK
  have hL0 : 0<scale K := hK.trans hL
  dsimp only [sideA, sideB, sideC]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [heron_factor]
  exact mul_pos (mul_pos (mul_pos hK (by omega)) (by omega)) (by omega)

lemma first_median_between {K : ℤ} (hK : 0<K) :
    (scale K+7*K-1)^2 < med₀ (sideA K) (sideB K) (sideC K) ∧
      med₀ (sideA K) (sideB K) (sideC K) < (scale K+7*K)^2 := by
  have he := (error_identities K (scale K)).1
  change med₀ (sideA K) (sideB K) (sideC K)-(scale K)^2 =
    K*(14*scale K-K) at he
  have hscale : scale K = 25*K^2+1 := rfl
  constructor <;> nlinarith [sq_pos_of_pos hK]

lemma first_median_not_rational_square {K : ℤ} (hK : 0<K) :
    ¬ IsSquare ((med₀ (sideA K) (sideB K) (sideC K) : ℤ) : ℚ) := by
  intro h
  obtain ⟨r,hr⟩ := Rat.isSquare_intCast_iff.mp h
  obtain ⟨hlo,hhi⟩ := first_median_between hK
  have he : |r|^2 = med₀ (sideA K) (sideB K) (sideC K) := by
    rw [sq_abs]
    simpa only [pow_two] using hr.symm
  have hbase : 0≤scale K+7*K-1 := by
    have := scale_gt hK
    omega
  rcases le_or_gt |r| (scale K+7*K-1) with hle | hgt
  · have hs := (sq_le_sq₀ (abs_nonneg r) hbase).mpr hle
    omega
  · have hge : scale K+7*K≤|r| := by omega
    have hs := (sq_le_sq₀ (by omega : 0≤scale K+7*K) (abs_nonneg r)).mpr hge
    omega

/-- The displayed integer triangles are primitive: no nonunit integer divides
all three sides. -/
lemma primitive (K d : ℤ) (ha : d ∣ sideA K) (hb : d ∣ sideB K)
    (hc : d ∣ sideC K) : IsUnit d := by
  have hL : d ∣ scale K := by
    convert dvd_sub hb ha using 1
    unfold sideA sideB
    ring
  have hK : d ∣ K := by
    convert dvd_sub (dvd_mul_of_dvd_right hL 7) hc using 1
    unfold sideC
    ring
  have h1 : d ∣ 1 := by
    convert dvd_sub hL (dvd_mul_of_dvd_right (dvd_pow hK (by decide : 2≠0)) 25) using 1
    unfold scale
    ring
  exact isUnit_of_dvd_one h1

/-- Hensel's lemma at a nonzero integer approximate square root. The congruence
includes an extra factor p and the entire square of the derivative, so it
also handles p=2 and primes dividing the approximate root. -/
lemma padic_square_of_congruence {p : ℕ} [hp : Fact p.Prime]
    {N r m : ℤ} (hm : m≠0)
    (hnorm : ‖(r : ℤ_[p])‖ = ‖(m : ℤ_[p])‖)
    (hdiv : (2*m)^2*(p : ℤ) ∣ N-r^2) : IsSquare (N : ℤ_[p]) := by
  obtain ⟨k,hk⟩ := hdiv
  let F : Polynomial ℤ_[p] := X^2-C (N : ℤ_[p])
  have hF (z : ℤ_[p]) : F.aeval z=z^2-(N : ℤ_[p]) := by simp [F]
  have hder : F.derivative.aeval (r : ℤ_[p])=2*(r : ℤ_[p]) := by
    dsimp [F]
    rw [derivative_sub, derivative_C, derivative_X_pow]
    simp
  have hval : F.aeval (r : ℤ_[p]) =
      -((2*(m : ℤ_[p]))^2*(p : ℤ_[p])*(k : ℤ_[p])) := by
    rw [hF]
    have hk' : (N : ℤ_[p])-(r : ℤ_[p])^2 =
      (2*(m : ℤ_[p]))^2*(p : ℤ_[p])*(k : ℤ_[p]) := by exact_mod_cast hk
    linear_combination -hk'
  have hpn : ‖(p : ℤ_[p])‖<1 := by
    rw [PadicInt.norm_p]
    exact (inv_lt_one₀ (by exact_mod_cast hp.out.pos)).mpr (by exact_mod_cast hp.out.one_lt)
  have hmn : 0<‖2*(m : ℤ_[p])‖^2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    apply mul_ne_zero (by norm_num)
    exact_mod_cast hm
  have hclose : ‖F.aeval (r : ℤ_[p])‖ < ‖F.derivative.aeval (r : ℤ_[p])‖^2 := by
    rw [hval, hder, norm_neg, norm_mul, norm_mul, norm_pow]
    have hright : ‖2*(r : ℤ_[p])‖=‖2*(m : ℤ_[p])‖ := by
      simp only [norm_mul, hnorm]
    rw [hright]
    calc
      ‖2*(m : ℤ_[p])‖^2*‖(p : ℤ_[p])‖*‖(k : ℤ_[p])‖ ≤
          ‖2*(m : ℤ_[p])‖^2*‖(p : ℤ_[p])‖*1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ < ‖2*(m : ℤ_[p])‖^2 := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hpn hmn
  obtain ⟨z,hz,-⟩ := hensels_lemma hclose
  refine ⟨z, ?_⟩
  rw [hF] at hz
  simpa only [pow_two] using (sub_eq_zero.mp hz).symm

lemma scale_padic_norm {p : ℕ} [Fact p.Prime] {K : ℤ} (hK : (p : ℤ) ∣ K) :
    ‖(scale K : ℤ_[p])‖=1 := by
  have hsmall : ‖(K : ℤ_[p])‖<1 := (PadicInt.norm_int_lt_one_iff_dvd K).mpr hK
  have hprod : ‖(25 : ℤ_[p])*(K : ℤ_[p])^2‖<1 := by
    rw [pow_two]
    exact PadicInt.norm_lt_one_mul (PadicInt.norm_lt_one_mul hsmall)
  have he : (scale K : ℤ_[p])=(25 : ℤ_[p])*(K : ℤ_[p])^2+1 := by
    simp [scale]
  rw [he, PadicInt.norm_add_eq_max_of_ne (by simpa using ne_of_lt hprod)]
  simpa using max_eq_right (le_of_lt hprod)

lemma local_squares {p : ℕ} [Fact p.Prime] {K : ℤ}
    (hK : (8140 : ℤ)^2*(p : ℤ) ∣ K) :
    IsSquare ((med₀ (sideA K) (sideB K) (sideC K) : ℤ) : ℤ_[p]) ∧
    IsSquare ((med₁ (sideA K) (sideB K) (sideC K) : ℤ) : ℤ_[p]) ∧
    IsSquare ((med₂ (sideA K) (sideB K) (sideC K) : ℤ) : ℤ_[p]) ∧
    IsSquare ((delta (sideA K) (sideB K) (sideC K) : ℤ) : ℤ_[p]) := by
  have hpK : (p : ℤ) ∣ K := (dvd_mul_left _ _).trans hK
  have hL := scale_padic_norm hpK
  have hnorm (m : ℤ) (e : ℕ) :
      ‖((m*(scale K)^e : ℤ) : ℤ_[p])‖=‖(m : ℤ_[p])‖ := by
    push_cast
    rw [norm_mul, norm_pow, hL, one_pow, mul_one]
  have hdiv (m : ℤ) (hm : (2*m)^2 ∣ (8140 : ℤ)^2) :
      (2*m)^2*(p : ℤ) ∣ K := (mul_dvd_mul_right hm _).trans hK
  obtain ⟨he₀,he₁,he₂,heD⟩ := error_identities K (scale K)
  have hd₀ : K ∣ med₀ (sideA K) (sideB K) (sideC K)-(scale K)^2 := by
    exact ⟨14*scale K-K, he₀⟩
  have hd₁ : K ∣ med₁ (sideA K) (sideB K) (sideC K)-(10*scale K)^2 := by
    refine ⟨2*(K-14*scale K), ?_⟩
    change med₁ (3*scale K) (4*scale K) (7*scale K-K)-(10*scale K)^2 = _
    rw [he₁]; ring
  have hd₂ : K ∣ med₂ (sideA K) (sideB K) (sideC K)-(11*scale K)^2 := by
    refine ⟨2*(K-14*scale K), ?_⟩
    change med₂ (3*scale K) (4*scale K) (7*scale K-K)-(11*scale K)^2 = _
    rw [he₂]; ring
  have hdD : K ∣ delta (sideA K) (sideB K) (sideC K)-(37*(scale K)^2)^2 := by
    refine ⟨(K-14*scale K)*(K^2-14*K*scale K+73*(scale K)^2), ?_⟩
    change delta (3*scale K) (4*scale K) (7*scale K-K)-(37*(scale K)^2)^2 = _
    rw [heD]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact padic_square_of_congruence (m := 1) (by norm_num)
      (by simpa using hnorm 1 1) ((hdiv 1 (by norm_num)).trans hd₀)
  · exact padic_square_of_congruence (m := 10) (by norm_num)
      (by simpa using hnorm 10 1) ((hdiv 10 (by norm_num)).trans hd₁)
  · exact padic_square_of_congruence (m := 11) (by norm_num)
      (by simpa using hnorm 11 1) ((hdiv 11 (by norm_num)).trans hd₂)
  · exact padic_square_of_congruence (m := 37) (by norm_num)
      (by simpa using hnorm 37 2) ((hdiv 37 (by norm_num)).trans hdD)

/-- A simultaneous local control, with a proved global failure. No rational
square root is inferred from the finitely many p-adic square roots. -/
theorem simultaneous_local_control (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ a b c : ℤ, 0<a ∧ a<b ∧ b<c ∧ 0<heron a b c ∧
      ¬IsSquare ((med₀ a b c : ℤ) : ℚ) ∧
      ∀ (p : ℕ) (hp : p∈P),
        letI : Fact p.Prime := ⟨hP p hp⟩
        IsSquare ((med₀ a b c : ℤ) : ℤ_[p]) ∧ IsSquare ((med₁ a b c : ℤ) : ℤ_[p]) ∧
        IsSquare ((med₂ a b c : ℤ) : ℤ_[p]) ∧ IsSquare ((delta a b c : ℤ) : ℤ_[p]) := by
  let K : ℤ := 8140^2*(∏ p ∈ P, (p : ℤ))
  have hK : 0<K := by
    dsimp [K]
    apply mul_pos (by norm_num)
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hP p hp).pos
  obtain ⟨ha,hab,hbc,hH⟩ := positive_triangle hK
  refine ⟨sideA K,sideB K,sideC K,ha,hab,hbc,hH,
    first_median_not_rational_square hK,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hP p hp⟩
  apply local_squares
  exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hp)

/-- The six arithmetic square conditions, over any commutative ring. -/
def SixSquares {R : Type*} [CommRing R] (A C : R) : Prop :=
  IsSquare A ∧ IsSquare C ∧ IsSquare (2*A+2-C) ∧
    IsSquare (2*A-1+2*C) ∧ IsSquare (-A+2+2*C) ∧
    IsSquare (A^2+1+C^2-A-A*C-C)

lemma normalized_squares {F : Type*} [Field F] {a b c : F} (hb : b≠0)
    (h₀ : IsSquare (med₀ a b c)) (h₁ : IsSquare (med₁ a b c))
    (h₂ : IsSquare (med₂ a b c)) (hD : IsSquare (delta a b c)) :
    SixSquares ((a/b)^2) ((c/b)^2) := by
  refine ⟨IsSquare.sq _, IsSquare.sq _, ?_, ?_, ?_, ?_⟩
  · convert h₀.div (IsSquare.sq b) using 1
    dsimp [med₀]
    field_simp
  · convert h₁.div (IsSquare.sq b) using 1
    dsimp [med₁]
    field_simp
  · convert h₂.div (IsSquare.sq b) using 1
    dsimp [med₂]
    field_simp
  · convert hD.div (IsSquare.sq (b^2)) using 1
    dsimp [delta]
    field_simp

lemma normalized_heron (a b c : ℚ) (hb : b≠0) :
    MedianDiscriminant.heron ((a/b)^2) ((c/b)^2) = heron a b c / b^4 := by
  unfold MedianDiscriminant.heron heron
  field_simp
  ring

/-- This corollary is expressed in precisely the normalized variables of the
conditional median construction. The finite collection of local tests cannot
exclude all positive-area parameters, even though these particular parameters
are proved not to be rational solutions. -/
theorem normalized_local_control (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) :
    ∃ A C : ℚ, 0<MedianDiscriminant.heron A C ∧
      ¬MedianDiscriminant.Admissible A C ∧
      ∀ (p : ℕ) (hp : p∈P),
        letI : Fact p.Prime := ⟨hP p hp⟩
        SixSquares (A : ℚ_[p]) (C : ℚ_[p]) := by
  obtain ⟨a,b,c,ha,hab,-,hH,hn,hloc⟩ := simultaneous_local_control P hP
  have hbZ : b≠0 := ne_of_gt (ha.trans hab)
  have hbQ : (b : ℚ)≠0 := by exact_mod_cast hbZ
  refine ⟨((a : ℚ)/b)^2,((c : ℚ)/b)^2,?_,?_,?_⟩
  · rw [normalized_heron _ _ _ hbQ]
    have hHQ : 0<heron (a : ℚ) (b : ℚ) (c : ℚ) := by
      unfold heron at hH ⊢
      exact_mod_cast hH
    exact div_pos hHQ (pow_pos (lt_of_le_of_ne (by exact_mod_cast (ha.trans hab).le)
      (Ne.symm hbQ)) 4)
  · intro h
    have hm := h.2.2.1.mul (IsSquare.sq (b : ℚ))
    apply hn
    convert hm using 1
    unfold med₀
    push_cast
    field_simp
  · intro p hp
    letI : Fact p.Prime := ⟨hP p hp⟩
    obtain ⟨h₀,h₁,h₂,hD⟩ := hloc p hp
    have lift (N : ℤ) (h : IsSquare (N : ℤ_[p])) : IsSquare (N : ℚ_[p]) := by
      simpa using h.map PadicInt.Coe.ringHom
    have h₀' : IsSquare (med₀ (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])) := by
      simpa [med₀] using lift _ h₀
    have h₁' : IsSquare (med₁ (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])) := by
      simpa [med₁] using lift _ h₁
    have h₂' : IsSquare (med₂ (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])) := by
      simpa [med₂] using lift _ h₂
    have hD' : IsSquare (delta (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])) := by
      simpa [delta] using lift _ hD
    simpa using normalized_squares (by exact_mod_cast hbZ : (b : ℚ_[p])≠0)
      h₀' h₁' h₂' hD'

#print axioms primitive
#print axioms normalized_local_control

#print axioms padic_square_of_congruence
#print axioms first_median_not_rational_square
#print axioms local_squares
#print axioms simultaneous_local_control

end Erdos213.MedianLocalControl
