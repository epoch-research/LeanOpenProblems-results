import Submission.FilteredFourthNorm

/-! Leading systems on quadratic algebras with a degree-two radicand.
This construction can be iterated, without irreducibility assumptions. -/
namespace Erdos322Research.FilteredFourthNorm
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0
open QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]
variable (F : LeadingSystem R S) (a : R) (a' : S)

private def quadBound (n : ℤ) (z : QuadraticAlgebra R a 0) : Prop :=
  F.bounded n z.re ∧ F.bounded (n-1) z.im

private def quadTop (n : ℤ) : QuadraticAlgebra R a 0 →+ QuadraticAlgebra S a' 0 where
  toFun z := ⟨F.top n z.re,F.top (n-1) z.im⟩
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

private lemma quadBound_mul (ha : F.bounded 2 a) {m n : ℤ}
    {z w : QuadraticAlgebra R a 0} (hz : quadBound F a m z) (hw : quadBound F a n w) :
    quadBound F a (m+n) (z*w) := by
  constructor
  · simp only [re_mul]
    apply F.add_bounded (F.mul_bounded hz.1 hw.1)
    have hi : 2+(m-1)+(n-1) = m+n := by ring
    exact hi ▸ F.mul_bounded (F.mul_bounded ha hz.2) hw.2
  · simp only [im_mul,zero_mul,add_zero]
    apply F.add_bounded
    · have hi : m+(n-1) = m+n-1 := by ring
      exact hi ▸ F.mul_bounded hz.1 hw.2
    · have hi : (m-1)+n = m+n-1 := by ring
      exact hi ▸ F.mul_bounded hz.2 hw.1

private lemma quadTop_mul (ha : F.bounded 2 a) (ha' : F.top 2 a = a') {m n : ℤ}
    {z w : QuadraticAlgebra R a 0} (hz : quadBound F a m z) (hw : quadBound F a n w) :
    quadTop F a a' (m+n) (z*w) = quadTop F a a' m z * quadTop F a a' n w := by
  have hre : F.top (m+n) (a*z.im*w.im) = a' * F.top (m-1) z.im * F.top (n-1) w.im := by
    have he := F.top_mul (F.mul_bounded ha hz.2) hw.2
    rw [F.top_mul ha hz.2,ha'] at he
    rw [show 2+(m-1)+(n-1) = m+n by ring] at he
    exact he
  have him₁ : F.top (m+n-1) (z.re*w.im) = F.top m z.re * F.top (n-1) w.im := by
    rw [show m+n-1 = m+(n-1) by ring]
    exact F.top_mul hz.1 hw.2
  have him₂ : F.top (m+n-1) (z.im*w.re) = F.top (m-1) z.im * F.top n w.re := by
    rw [show m+n-1 = (m-1)+n by ring]
    exact F.top_mul hz.2 hw.1
  apply QuadraticAlgebra.ext
  · change F.top (m+n) (z.re*w.re+a*z.im*w.im) =
      F.top m z.re * F.top n w.re + a' * F.top (m-1) z.im * F.top (n-1) w.im
    rw [map_add,F.top_mul hz.1 hw.1,hre]
  · change F.top (m+n-1) (z.re*w.im+z.im*w.re+0*z.im*w.im) =
      F.top m z.re * F.top (n-1) w.im + F.top (m-1) z.im * F.top n w.re +
        0*F.top (m-1) z.im*F.top (n-1) w.im
    simp only [zero_mul,add_zero,map_add,him₁,him₂]

/-- The leading radicand may be named separately from its computation. -/
def quadraticSystem (ha : F.bounded 2 a) (ha' : F.top 2 a = a') :
    LeadingSystem (QuadraticAlgebra R a 0) (QuadraticAlgebra S a' 0) where
  bounded := quadBound F a
  top := quadTop F a a'
  zero_bounded n := ⟨F.zero_bounded n,F.zero_bounded (n-1)⟩
  mono := by
    intro m n z h hz
    exact ⟨F.mono h hz.1,F.mono (by omega) hz.2⟩
  add_bounded hz hw := ⟨F.add_bounded hz.1 hw.1,F.add_bounded hz.2 hw.2⟩
  mul_bounded := quadBound_mul F a ha
  exists_bound := by
    intro z
    obtain ⟨m,hm⟩ := F.exists_bound z.re
    obtain ⟨n,hn⟩ := F.exists_bound z.im
    refine ⟨max m (n+1),F.mono ?_ hm,F.mono ?_ hn⟩
    · exact_mod_cast le_max_left m (n+1)
    · have hh : ((n+1:ℕ):ℤ) ≤ max m (n+1) := by exact_mod_cast le_max_right m (n+1)
      omega
  top_mul := quadTop_mul F a a' ha ha'
  top_above := by
    intro m n z hz hmn
    apply QuadraticAlgebra.ext
    · exact F.top_above hz.1 hmn
    · exact F.top_above hz.2 (by omega)
  lower := by
    intro n z hz ht
    exact ⟨F.lower hz.1 (congrArg QuadraticAlgebra.re ht),
      F.lower hz.2 (congrArg QuadraticAlgebra.im ht)⟩

lemma quadratic_bounded_iff (ha : F.bounded 2 a) (ha' : F.top 2 a = a')
    (n : ℤ) (z : QuadraticAlgebra R a 0) :
    (quadraticSystem F a a' ha ha').bounded n z ↔
      F.bounded n z.re ∧ F.bounded (n-1) z.im := Iff.rfl

lemma quadratic_top_re (ha : F.bounded 2 a) (ha' : F.top 2 a = a')
    (n : ℤ) (z : QuadraticAlgebra R a 0) :
    ((quadraticSystem F a a' ha ha').top n z).re = F.top n z.re := rfl

lemma quadratic_top_im (ha : F.bounded 2 a) (ha' : F.top 2 a = a')
    (n : ℤ) (z : QuadraticAlgebra R a 0) :
    ((quadraticSystem F a a' ha ha').top n z).im = F.top (n-1) z.im := rfl

lemma quadratic_bound_base (ha : F.bounded 2 a) (ha' : F.top 2 a = a')
    {n : ℤ} {r : R} (hr : F.bounded n r) :
    (quadraticSystem F a a' ha ha').bounded n (algebraMap R (QuadraticAlgebra R a 0) r) :=
  ⟨hr,F.zero_bounded _⟩

lemma quadratic_top_base (ha : F.bounded 2 a) (ha' : F.top 2 a = a')
    (n : ℤ) (r : R) :
    (quadraticSystem F a a' ha ha').top n (algebraMap R (QuadraticAlgebra R a 0) r) =
      algebraMap S (QuadraticAlgebra S a' 0) (F.top n r) := by
  apply QuadraticAlgebra.ext
  · rfl
  · exact map_zero _

end
end Erdos322Research.FilteredFourthNorm
