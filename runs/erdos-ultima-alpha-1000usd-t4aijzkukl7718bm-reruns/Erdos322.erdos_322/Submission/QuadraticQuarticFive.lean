import FormalConjecturesUtil

/-! A local obstruction for four fourth powers over quadratic algebras.
This file does not bound the unrestricted representation count. -/
namespace Erdos322Research.QuadraticQuarticFive

noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The quadratic extension at five is split or ramified, rather than inert. -/
def GoodFive (d : ℤ) : Prop :=
  (∃ r : ZMod 5, r ≠ 0 ∧ r^2 = -(d : ZMod 5)) ∨
  ∃ e : ℤ, d = 5*e ∧ ¬ (5 : ℤ) ∣ e

def reFourth {R : Type*} [CommRing R] (d a b : R) : R :=
  a^4-6*d*a^2*b^2+d^2*b^4

def imFourth {R : Type*} [CommRing R] (d a b : R) : R :=
  4*a*b*(a^2-d*b^2)

private lemma residue_zero (a : Fin 4 → ZMod 5) (h : ∑ i, a i^4 = 0) :
    ∀ i, a i = 0 := by
  have H : ∀ a : Fin 4 → ZMod 5, (∑ i, a i^4 = 0) → ∀ i, a i = 0 := by decide
  exact H a h

private lemma root_eval {R : Type*} [CommRing R] (d r a b : R) (hr : r^2 = -d) :
    (a+r*b)^4 = reFourth d a b + r*imFourth d a b := by
  dsimp [reFourth, imFourth]
  linear_combination (6*a^2*b^2+4*r*a*b^3+(r^2-d)*b^4)*hr

private lemma split_divisibility (d : ℤ) (r : ZMod 5) (hr : r ≠ 0)
    (hrd : r^2 = -(d : ZMod 5)) (a b : Fin 4 → ℤ)
    (hA : ∑ i, reFourth d (a i) (b i) = 0)
    (hB : ∑ i, imFourth d (a i) (b i) = 0) :
    ∀ i, (5 : ℤ) ∣ a i ∧ (5 : ℤ) ∣ b i := by
  have hA' : ∑ i, reFourth (d : ZMod 5) (a i) (b i) = 0 := by
    simpa [reFourth] using congrArg (fun z : ℤ ↦ (z : ZMod 5)) hA
  have hB' : ∑ i, imFourth (d : ZMod 5) (a i) (b i) = 0 := by
    simpa [imFourth] using congrArg (fun z : ℤ ↦ (z : ZMod 5)) hB
  have hs (s : ZMod 5) (hs : s^2 = -(d : ZMod 5)) :
      ∀ i, (a i : ZMod 5)+s*(b i : ZMod 5)=0 := by
    apply residue_zero
    simp_rw [root_eval _ s _ _ hs]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hA', hB']
    ring
  have hp := hs r hrd
  have hm := hs (-r) (by simpa using hrd)
  intro i
  have hb : (b i : ZMod 5) = 0 := by
    have he : (2*r)*(b i : ZMod 5)=0 := by linear_combination hp i - hm i
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by decide) hr)
  have ha : (a i : ZMod 5)=0 := by simpa [hb] using hp i
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hb⟩

private lemma ramified_divisibility (e : ℤ) (he : ¬ (5 : ℤ) ∣ e)
    (a b : Fin 4 → ℤ) (hA : ∑ i, reFourth (5*e) (a i) (b i) = 0) :
    ∀ i, (5 : ℤ) ∣ a i ∧ (5 : ℤ) ∣ b i := by
  have hA' : ∑ i, reFourth ((5*e : ℤ) : ZMod 5) (a i) (b i) = 0 := by
    simpa [reFourth] using congrArg (fun z : ℤ ↦ (z : ZMod 5)) hA
  have ha : ∀ i, (5 : ℤ) ∣ a i := by
    have hz : ∑ i, (a i : ZMod 5)^4=0 := by
      have h5 : (5 : ZMod 5)=0 := by decide
      simpa only [reFourth,Int.cast_mul,Int.cast_ofNat,h5,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,add_zero] using hA'
    exact fun i ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (residue_zero _ hz i)
  choose c hc using ha
  have hx : ∑ i, (25*(c i)^4-30*e*(c i)^2*(b i)^2+e^2*(b i)^4)=0 := by
    have hh : (25 : ℤ)*(∑ i, (25*(c i)^4-30*e*(c i)^2*(b i)^2+e^2*(b i)^4))=0 := by
      rw [Finset.mul_sum]
      convert hA using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i]
      dsimp [reFourth]
      ring
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hx' : ∑ i, ((25 : ZMod 5)*(c i : ZMod 5)^4-
      30*(e : ZMod 5)*(c i : ZMod 5)^2*(b i : ZMod 5)^2+
      (e : ZMod 5)^2*(b i : ZMod 5)^4)=0 := by
    simpa only [Int.cast_sum,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_zero] using
      congrArg (fun z : ℤ ↦ (z : ZMod 5)) hx
  have hb : ∀ i, (b i : ZMod 5)=0 := by
    apply residue_zero
    have hh : (e : ZMod 5)^2*(∑ i, (b i : ZMod 5)^4)=0 := by
      have h25 : (25 : ZMod 5)=0 := by decide
      have h30 : (30 : ZMod 5)=0 := by decide
      simpa only [h25,h30,zero_mul,zero_sub,neg_zero,zero_add,Finset.mul_sum] using hx'
    exact (mul_eq_zero.mp hh).resolve_left
      (pow_ne_zero _ (fun h ↦ he ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h)))
  exact fun i ↦ ⟨⟨c i,hc i⟩, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (hb i)⟩

private lemma coefficient_divisibility (d : ℤ) (hd : GoodFive d) (a b : Fin 4 → ℤ)
    (hA : ∑ i, reFourth d (a i) (b i) = 0)
    (hB : ∑ i, imFourth d (a i) (b i) = 0) :
    ∀ i, (5 : ℤ) ∣ a i ∧ (5 : ℤ) ∣ b i := by
  rcases hd with ⟨r,hr,hrd⟩ | ⟨e,rfl,he⟩
  · exact split_divisibility d r hr hrd a b hA hB
  · exact ramified_divisibility e he a b hA

/-- Integer coefficient version of quadratic-field anisotropy at five. -/
theorem integer_fourth_sum_zero (d : ℤ) (hd : GoodFive d) (a b : Fin 4 → ℤ)
    (hA : ∑ i, reFourth d (a i) (b i) = 0)
    (hB : ∑ i, imFourth d (a i) (b i) = 0) :
    ∀ i, a i=0 ∧ b i=0 := by
  let N := ∑ i, ((a i).natAbs+(b i).natAbs)
  suffices H : ∀ N : ℕ, ∀ a b : Fin 4 → ℤ,
      (∑ i, ((a i).natAbs+(b i).natAbs))=N →
      (∑ i, reFourth d (a i) (b i))=0 →
      (∑ i, imFourth d (a i) (b i))=0 → ∀ i, a i=0 ∧ b i=0 by
    exact H N a b rfl hA hB
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b hN hA hB
    by_cases hzero : N=0
    · intro i
      have hle := Finset.single_le_sum (f := fun i : Fin 4 ↦ (a i).natAbs+(b i).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      dsimp only at hle
      rw [hN,hzero] at hle
      have ha : (a i).natAbs=0 := by omega
      have hb : (b i).natAbs=0 := by omega
      exact ⟨Int.natAbs_eq_zero.mp ha,Int.natAbs_eq_zero.mp hb⟩
    · have hdv := coefficient_divisibility d hd a b hA hB
      choose c hc using fun i ↦ (hdv i).1
      choose e he using fun i ↦ (hdv i).2
      have hAc : ∑ i, reFourth d (c i) (e i)=0 := by
        have hh : (625 : ℤ)*(∑ i, reFourth d (c i) (e i))=0 := by
          rw [Finset.mul_sum]
          convert hA using 1
          apply Finset.sum_congr rfl
          intro i _
          rw [hc i,he i]
          dsimp [reFourth]
          ring
        exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      have hBc : ∑ i, imFourth d (c i) (e i)=0 := by
        have hh : (625 : ℤ)*(∑ i, imFourth d (c i) (e i))=0 := by
          rw [Finset.mul_sum]
          convert hB using 1
          apply Finset.sum_congr rfl
          intro i _
          rw [hc i,he i]
          dsimp [imFourth]
          ring
        exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      have hscale : 5*(∑ i, ((c i).natAbs+(e i).natAbs))=N := by
        rw [←hN,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i,he i,Int.natAbs_mul,Int.natAbs_mul]
        norm_num
        ring
      have hs : (∑ i, ((c i).natAbs+(e i).natAbs))<N := by omega
      have hz := ih _ hs c e rfl hAc hBc
      intro i
      simp [hc i,he i,(hz i).1,(hz i).2]


private lemma reFourth_scale {R : Type*} [CommRing R] (d t a b : R) :
    reFourth d (t*a) (t*b)=t^4*reFourth d a b := by
  dsimp [reFourth]; ring

private lemma imFourth_scale {R : Type*} [CommRing R] (d t a b : R) :
    imFourth d (t*a) (t*b)=t^4*imFourth d a b := by
  dsimp [imFourth]; ring

/-- Clearing a common denominator gives the rational coefficient version. -/
theorem rational_fourth_sum_zero (d : ℤ) (hd : GoodFive d) (a b : Fin 4 → ℚ)
    (hA : ∑ i, reFourth (d : ℚ) (a i) (b i)=0)
    (hB : ∑ i, imFourth (d : ℚ) (a i) (b i)=0) :
    ∀ i, a i=0 ∧ b i=0 := by
  let f : Fin 4 ⊕ Fin 4 → ℚ := Sum.elim a b
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose c hc using hD
  have hD0 : ((D : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero D.prop
  have hcA (i : Fin 4) : (c (Sum.inl i) : ℚ)=(D : ℤ)*a i := by
    simpa [f,Algebra.smul_def] using hc (Sum.inl i)
  have hcB (i : Fin 4) : (c (Sum.inr i) : ℚ)=(D : ℤ)*b i := by
    simpa [f,Algebra.smul_def] using hc (Sum.inr i)
  have hAc : ∑ i, reFourth d (c (Sum.inl i)) (c (Sum.inr i))=0 := by
    have he : ∑ i, reFourth (d : ℚ) (c (Sum.inl i)) (c (Sum.inr i))=0 := by
      simp_rw [hcA,hcB,reFourth_scale]
      rw [←Finset.mul_sum,hA,mul_zero]
    have he' : ((∑ i, reFourth d (c (Sum.inl i)) (c (Sum.inr i)) : ℤ) : ℚ)=0 := by
      simpa [reFourth] using he
    exact_mod_cast he'
  have hBc : ∑ i, imFourth d (c (Sum.inl i)) (c (Sum.inr i))=0 := by
    have he : ∑ i, imFourth (d : ℚ) (c (Sum.inl i)) (c (Sum.inr i))=0 := by
      simp_rw [hcA,hcB,imFourth_scale]
      rw [←Finset.mul_sum,hB,mul_zero]
    have he' : ((∑ i, imFourth d (c (Sum.inl i)) (c (Sum.inr i)) : ℤ) : ℚ)=0 := by
      simpa [imFourth] using he
    exact_mod_cast he'
  have hz := integer_fourth_sum_zero d hd (fun i ↦ c (Sum.inl i))
    (fun i ↦ c (Sum.inr i)) hAc hBc
  dsimp only at hz
  intro i
  have h1 := hcA i
  have h2 := hcB i
  rw [(hz i).1,Int.cast_zero] at h1
  rw [(hz i).2,Int.cast_zero] at h2
  exact ⟨(mul_eq_zero.mp h1.symm).resolve_left hD0,
    (mul_eq_zero.mp h2.symm).resolve_left hD0⟩

private lemma quadratic_fourth_re (d : ℚ) (z : QuadraticAlgebra ℚ (-d) 0) :
    (z^4).re = reFourth d z.re z.im := by
  simp only [pow_succ,pow_zero,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  dsimp [reFourth]
  ring

private lemma quadratic_fourth_im (d : ℚ) (z : QuadraticAlgebra ℚ (-d) 0) :
    (z^4).im = imFourth d z.re z.im := by
  simp only [pow_succ,pow_zero,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  dsimp [imFourth]
  ring

/-- Four fourth powers are anisotropic over these quadratic algebras. -/
theorem quadratic_algebra_fourth_sum_zero (d : ℤ) (hd : GoodFive d)
    (z : Fin 4 → QuadraticAlgebra ℚ (-(d : ℚ)) 0) (h : ∑ i, z i^4=0) :
    ∀ i, z i=0 := by
  have hA : ∑ i, reFourth (d : ℚ) (z i).re (z i).im=0 := by
    have hh := congrArg QuadraticAlgebra.re h
    simpa [Fin.sum_univ_four,quadratic_fourth_re] using hh
  have hB : ∑ i, imFourth (d : ℚ) (z i).re (z i).im=0 := by
    have hh := congrArg QuadraticAlgebra.im h
    simpa [Fin.sum_univ_four,quadratic_fourth_im] using hh
  have hz := rational_fourth_sum_zero d hd (fun i ↦ (z i).re) (fun i ↦ (z i).im) hA hB
  intro i
  exact QuadraticAlgebra.ext (hz i).1 (hz i).2

end
end Erdos322Research.QuadraticQuarticFive
