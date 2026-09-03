import FormalConjecturesUtil

/-! A split-prime obstruction for six norm conditions after a cubic Hesse
base change. This is an arithmetic auxiliary result, not Erdos 213. -/
namespace Erdos213.HesseSplitSeven
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Homogeneous products of the two split embeddings. -/
def profile {R : Type*} [CommRing R] (r n d m e : R) : Fin 6 → R :=
  ![n*m,
    3*(2*n+(1-r)*d)*(2*m+(1+r)*e),
    3*(2*n+(1+r)*d)*(2*m+(1-r)*e),
    3*(n-(1-r)*d)*(m-(1+r)*e),
    3*(n+2*d)*(m+2*e),
    3*(n-(1+r)*d)*(m-(1-r)*e)]

def hNum {R : Type*} [CommRing R] (a b : R) : R := a^3+2*b^3
def hDen {R : Type*} [CommRing R] (a b : R) : R := 3*a*b^2

lemma profile_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r n d m e : R) (i : Fin 6) :
    f (profile r n d m e i)=profile (f r) (f n) (f d) (f m) (f e) i := by
  fin_cases i <;> simp [profile,map_ofNat]

lemma profile_scale {R : Type*} [CommRing R] (r n d m e u v : R) (i : Fin 6) :
    profile r (u*n) (u*d) (v*m) (v*e) i=u*v*profile r n d m e i := by
  fin_cases i <;> dsimp [profile] <;> ring

/-- Complete projective residue check. Each of the two components can be
finite or infinite independently. No zero norm residue is discarded. -/
lemma residue_obstruction : ∀ a b c d : ZMod 7,
    (a≠0 ∨ b≠0) → (c≠0 ∨ d≠0) →
    ¬(∀ i j : Fin 6, IsSquare
      (profile 2 (hNum a b) (hDen a b) (hNum c d) (hDen c d) i *
       profile 2 (hNum a b) (hDen a b) (hNum c d) (hDen c d) j)) := by
  decide

lemma square_reduces (a : ℤ_[7]) (h : IsSquare (a : ℚ_[7])) :
    IsSquare (PadicInt.toZMod a) := by
  obtain ⟨q,hq⟩ := h
  have hq1 : ‖q‖≤1 := by
    have hh : ‖q‖*‖q‖≤1 := by rw [← norm_mul,← hq]; exact a.property
    nlinarith [norm_nonneg q]
  let z : ℤ_[7] := ⟨q,hq1⟩
  have he : a=z*z := by apply Subtype.ext; exact hq
  refine ⟨PadicInt.toZMod z,?_⟩
  rw [he,map_mul]

/-- Projective normalization is performed separately in the two split
components. This avoids assuming that a rational common denominator is a unit. -/
lemma projective_normalize (s : ℚ_[7]) : ∃ a b : ℤ_[7],
    b≠0 ∧ s*(b : ℚ_[7])=(a : ℚ_[7]) ∧
    (PadicInt.toZMod a≠0 ∨ PadicInt.toZMod b≠0) := by
  by_cases h : ‖s‖≤1
  · refine ⟨⟨s,h⟩,1,one_ne_zero,by simp,Or.inr ?_⟩
    simp
  · have hs : 1<‖s‖ := lt_of_not_ge h
    have hs0 : s≠0 := by intro hz; norm_num [hz] at hs
    have hi : ‖s⁻¹‖≤1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hs.le
    refine ⟨1,⟨s⁻¹,hi⟩,?_,?_,Or.inl ?_⟩
    · intro hz
      have hh := congrArg (fun z : ℤ_[7] => (z : ℚ_[7])) hz
      exact inv_ne_zero hs0 hh
    · exact mul_inv_cancel₀ hs0
    · simp

/-- The residue obstruction lifts to all 7-adic parameters, including
independently nonintegral split components. -/
theorem padic_projective_obstruction (r a b c d : ℤ_[7])
    (hr : PadicInt.toZMod r=2)
    (hab : PadicInt.toZMod a≠0 ∨ PadicInt.toZMod b≠0)
    (hcd : PadicInt.toZMod c≠0 ∨ PadicInt.toZMod d≠0) :
    ¬(∀ i j : Fin 6, IsSquare
      (((profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) i : ℤ_[7]) : ℚ_[7]) *
       ((profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) j : ℤ_[7]) : ℚ_[7]))) := by
  intro h
  apply residue_obstruction (PadicInt.toZMod a) (PadicInt.toZMod b)
    (PadicInt.toZMod c) (PadicInt.toZMod d) hab hcd
  intro i j
  have hh := square_reduces
    (profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) i *
     profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) j) (h i j)
  simpa only [map_mul,profile_map,hNum,hDen,map_add,map_pow,map_mul,map_ofNat,hr] using hh

def hesse (s : ℚ_[7]) : ℚ_[7] := (s^3+2)/(3*s)

lemma hesse_homogeneous (s : ℚ_[7]) (a b : ℤ_[7])
    (hs : s≠0) (_hb : b≠0) (he : s*(b : ℚ_[7])=(a : ℚ_[7])) :
    hesse s*(hDen a b : ℚ_[7])=(hNum a b : ℚ_[7]) := by
  unfold hesse hDen hNum
  rw [← he]
  field_simp

lemma hDen_ne (s : ℚ_[7]) (a b : ℤ_[7])
    (hs : s≠0) (hb : b≠0) (he : s*(b : ℚ_[7])=(a : ℚ_[7])) : hDen a b≠0 := by
  have ha : a≠0 := by
    intro ha
    rw [ha] at he
    exact mul_ne_zero hs (PadicInt.coe_ne_zero.mpr hb) he
  unfold hDen
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 2 hb)

/-- Six affine products cannot even share a square class after this base
change. The theorem does not need a relation between the two 7-adic inputs. -/
theorem no_padic_profile (r : ℤ_[7]) (hr : PadicInt.toZMod r=2)
    (s t : ℚ_[7]) (hs : s≠0) (ht : t≠0) :
    ¬(∀ i j : Fin 6, IsSquare
      (profile (r : ℚ_[7]) (hesse s) 1 (hesse t) 1 i *
       profile (r : ℚ_[7]) (hesse s) 1 (hesse t) 1 j)) := by
  intro h
  obtain ⟨a,b,hb,hab,hab0⟩ := projective_normalize s
  obtain ⟨c,d,hd,hcd,hcd0⟩ := projective_normalize t
  apply padic_projective_obstruction r a b c d hr hab0 hcd0
  have he1 := hesse_homogeneous s a b hs hb hab
  have he2 := hesse_homogeneous t c d ht hd hcd
  have he (i : Fin 6) :
      ((profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) i : ℤ_[7]) : ℚ_[7]) =
      (hDen a b : ℚ_[7])*(hDen c d : ℚ_[7])*
        profile (r : ℚ_[7]) (hesse s) 1 (hesse t) 1 i := by
    have hm : ((profile r (hNum a b) (hDen a b) (hNum c d) (hDen c d) i : ℤ_[7]) : ℚ_[7]) =
        profile (r : ℚ_[7]) (hNum (a : ℚ_[7]) b) (hDen (a : ℚ_[7]) b)
          (hNum (c : ℚ_[7]) d) (hDen (c : ℚ_[7]) d) i := by
      fin_cases i <;> simp [profile,hNum,hDen] <;> rfl
    rw [hm,← he1,← he2]
    simpa only [mul_comm,mul_one,one_mul] using
      profile_scale (r : ℚ_[7]) (hesse s) 1 (hesse t) 1
        (hDen a b : ℚ_[7]) (hDen c d : ℚ_[7]) i
  intro i j
  rw [he i,he j]
  convert (IsSquare.sq ((hDen a b : ℚ_[7])*(hDen c d : ℚ_[7]))).mul (h i j) using 1
  ring

open Polynomial

lemma root_lift : ∃ r : ℤ_[7], r^2=-3 ∧ PadicInt.toZMod r=2 := by
  let F : ℤ[X] := X^2+3
  have hv : Polynomial.aeval (2 : ℤ_[7]) F=(7 : ℤ_[7]) := by norm_num [F,map_ofNat]
  have hd : Polynomial.aeval (2 : ℤ_[7]) F.derivative=(4 : ℤ_[7]) := by norm_num [F,map_ofNat]
  have hn4 : ‖(4 : ℤ_[7])‖=1 := by
    change ‖((4 : ℤ) : ℤ_[7])‖=1
    rw [PadicInt.norm_intCast_eq_one_iff]
    norm_num
  have hn7 : ‖(7 : ℤ_[7])‖<1 := by
    change ‖((7 : ℤ) : ℤ_[7])‖<1
    rw [PadicInt.norm_intCast_lt_one_iff]
    norm_num
  have hh : ‖Polynomial.aeval (2 : ℤ_[7]) F‖ <
      ‖Polynomial.aeval (2 : ℤ_[7]) F.derivative‖^2 := by rw [hv,hd,hn4,one_pow]; exact hn7
  obtain ⟨r,hr,hclose,_⟩ := hensels_lemma hh
  refine ⟨r,?_,?_⟩
  · have he : r^2+3=0 := by simpa [F,map_ofNat] using hr
    linear_combination he
  · rw [hd,hn4] at hclose
    have hz : PadicInt.toZMod (r-2)=0 := by
      rw [← RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
      exact (PadicInt.norm_lt_one_iff_dvd _).mp hclose
    simpa only [map_sub,map_ofNat,sub_eq_zero] using hz

#print axioms root_lift
#print axioms residue_obstruction
#print axioms no_padic_profile
end
end Erdos213.HesseSplitSeven
