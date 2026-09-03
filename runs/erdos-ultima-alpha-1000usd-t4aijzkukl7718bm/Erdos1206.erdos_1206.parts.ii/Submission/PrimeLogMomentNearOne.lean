import Submission.QuadraticPrimeMassNearOne

/-! An upper logarithmic prime moment near s=1, obtained from the regularized
von Mangoldt L-series. No prime number theorem is invoked. -/
namespace Erdos1206.PrimeLogMomentNearOne
open RealQuadraticEulerMass Filter ArithmeticFunction
open scoped Topology

noncomputable def mangoldtPower (s : ℝ) (n : ℕ) : ℝ :=
  vonMangoldt n*(n:ℝ)^(-s)

lemma mangoldtPower_nonneg (s : ℝ) (n : ℕ) : 0 ≤ mangoldtPower s n :=
  mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma mangoldtPower_term (s : ℝ) (n : ℕ) :
    (mangoldtPower s n:ℂ)=LSeries.term (fun n => (vonMangoldt n:ℂ)) (s:ℂ) n := by
  rw [LSeries.term_def₀ (by simp)]
  simp only [mangoldtPower,Complex.ofReal_mul]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
  simp only [Complex.ofReal_natCast,Complex.ofReal_neg]

lemma summable_mangoldtPower {s : ℝ} (hs : 1 < s) : Summable (mangoldtPower s) := by
  apply Complex.summable_ofReal.mp
  simpa only [mangoldtPower_term] using LSeriesSummable_vonMangoldt (show 1 < (s:ℂ).re from hs)

lemma mangoldtPower_tsum_norm (s : ℝ) :
    ∑' n, mangoldtPower s n=‖LSeries (fun n => (vonMangoldt n:ℂ)) (s:ℂ)‖ := by
  have he : ((∑' n, mangoldtPower s n:ℝ):ℂ) =
      LSeries (fun n => (vonMangoldt n:ℂ)) (s:ℂ) := by
    rw [Complex.ofReal_tsum]
    simp only [mangoldtPower_term,LSeries]
  rw [←he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (mangoldtPower_nonneg s))]

noncomputable def primeMoment (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Real.log (p:ℝ)*primePower s p

lemma summable_primeMoment {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => Real.log (p:ℝ)*primePower s p) := by
  have hh := (summable_mangoldtPower hs).subtype (fun p => p.Prime)
  exact hh.congr (fun p => by simp only [Function.comp_apply,mangoldtPower,primePower,vonMangoldt_apply_prime p.prop])

lemma primeMoment_nonneg (s : ℝ) : 0 ≤ primeMoment s := by
  apply tsum_nonneg
  intro p
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (primePower_pos s p).le

lemma primeMoment_le_LSeries_norm {s : ℝ} (hs : 1 < s) :
    primeMoment s ≤ ‖LSeries (fun n => (vonMangoldt n:ℂ)) (s:ℂ)‖ := by
  rw [←mangoldtPower_tsum_norm]
  have hh := Summable.tsum_subtype_le (mangoldtPower s) {p | p.Prime}
    (mangoldtPower_nonneg s) (summable_mangoldtPower hs)
  have he (p : Nat.Primes) : mangoldtPower s p=Real.log (p:ℝ)*primePower s p := by
    simp only [mangoldtPower,primePower,vonMangoldt_apply_prime p.prop]
  simpa only [he,primeMoment] using hh

lemma ofReal_tendsto_closed_halfplane :
    Tendsto (fun s : ℝ => (s:ℂ)) (𝓝[>] 1) (𝓝[{z : ℂ | 1 ≤ z.re}] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (show 1 < s from hs).le

/-- The logarithmic prime moment has at most a simple pole at 1. -/
theorem eventually_primeMoment_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*primeMoment s ≤ B := by
  let aux := vonMangoldt.LFunctionResidueClassAux (1:ZMod 1)
  let C : ℝ := ‖aux 1‖+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have ht : Tendsto (fun s : ℝ => aux (s:ℂ)) (𝓝[>] 1) (𝓝 (aux 1)) := by
    have hc := vonMangoldt.continuousOn_LFunctionResidueClassAux (1:ZMod 1) 1
      (by simp : (1:ℂ) ∈ {z : ℂ | 1 ≤ z.re})
    exact Filter.Tendsto.comp (f := fun s : ℝ => (s:ℂ)) (g := aux) hc
      ofReal_tendsto_closed_halfplane
  have hbounded : ∀ᶠ s : ℝ in 𝓝[>] 1, ‖aux (s:ℂ)‖ < C :=
    ht.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨C+1,by positivity,?_⟩
  have htwo : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 :=
    (gt_mem_nhds (by norm_num : (1:ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hbounded,htwo,self_mem_nhdsWithin] with s hb hs2 hs1
  have hsp : 0 < s-1 := sub_pos.mpr hs1
  have he := vonMangoldt.eqOn_LFunctionResidueClassAux
    (isUnit_one : IsUnit (1:ZMod 1)) (show 1 < (s:ℂ).re from hs1)
  have hres : (fun n => (vonMangoldt.residueClass (1:ZMod 1) n:ℂ))=
      (fun n => (vonMangoldt n:ℂ)) := by
    funext n
    have hn : (n:ZMod 1)=1 := Subsingleton.elim _ _
    simp [vonMangoldt.residueClass,hn]
  rw [hres] at he
  simp only [Nat.totient_one,Nat.cast_one,inv_one] at he
  have he' : LSeries (fun n => (vonMangoldt n:ℂ)) (s:ℂ) = aux (s:ℂ)+1/((s:ℂ)-1) := by
    dsimp only [aux]
    linear_combination -he
  have hn : ‖(1:ℂ)/((s:ℂ)-1)‖=1/(s-1) := by
    rw [norm_div,norm_one,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsp]
  have hbound : primeMoment s ≤ C+1/(s-1) := calc
    _ ≤ ‖LSeries (fun n => (vonMangoldt n:ℂ)) (s:ℂ)‖ := primeMoment_le_LSeries_norm hs1
    _ = ‖aux (s:ℂ)+1/((s:ℂ)-1)‖ := by rw [he']
    _ ≤ ‖aux (s:ℂ)‖+‖(1:ℂ)/((s:ℂ)-1)‖ := norm_add_le _ _
    _ ≤ C+1/(s-1) := by rw [hn]; linarith
  have hh := mul_le_mul_of_nonneg_left hbound hsp.le
  have heq : (s-1)*(C+1/(s-1))=(s-1)*C+1 := by field_simp
  rw [heq] at hh
  have hmul := mul_le_mul_of_nonneg_right (show s-1 ≤ 1 by linarith) hC.le
  linarith

#print axioms summable_primeMoment
#print axioms primeMoment_le_LSeries_norm
#print axioms eventually_primeMoment_bound
end Erdos1206.PrimeLogMomentNearOne
