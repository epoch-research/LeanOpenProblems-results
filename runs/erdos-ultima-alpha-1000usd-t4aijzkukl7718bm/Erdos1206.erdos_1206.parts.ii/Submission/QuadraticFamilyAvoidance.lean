import Submission.CubeShapeCompactness
import Submission.RationalCubePairRelations

/-!
One positive-lower-density set simultaneously avoids every ordered integral
specialization of finitely many rational quadratic four-cube identities.
The finite collection must be fixed in advance; this is not a uniform theorem
over all families.
-/
namespace Erdos1206.QuadraticFamilyAvoidance
open Polynomial FermatCubicConics RationalCubePairRelations CubeShapeCompactness

/-- We allow arbitrary linearized coefficient vectors, but explicitly require
the numerical cubic identity. Polynomial parameter values are a special case. -/
def OrderedInstance (a b c d x : Vec) : Prop :=
  0 < linear a x ∧ linear a x < linear b x ∧ linear b x ≤ linear c x ∧
  linear c x < linear d x ∧
  (linear a x)^3+(linear d x)^3=(linear b x)^3+(linear c x)^3

private lemma instance_gap {a b c d x : Vec} (h : OrderedInstance a b c d x) :
    linear d x-linear c x < linear b x-linear a x := by
  have hh := gap_strict
    (show (0:ℝ) ≤ (linear a x:ℝ) by exact_mod_cast h.1.le)
    (show (linear a x:ℝ) < (linear b x:ℝ) by exact_mod_cast h.2.1)
    (show (linear b x:ℝ) ≤ (linear c x:ℝ) by exact_mod_cast h.2.2.1)
    (show (linear c x:ℝ) < (linear d x:ℝ) by exact_mod_cast h.2.2.2.1)
    (show (linear a x:ℝ)^3+(linear d x:ℝ)^3=
      (linear b x:ℝ)^3+(linear c x:ℝ)^3 by exact_mod_cast h.2.2.2.2)
  exact_mod_cast hh

private lemma sum_ratio_lt_one {a b c d x : Vec} {q : ℚ}
    (h : OrderedInstance a b c d x)
    (hr : linear a x+linear d x=q*(linear b x+linear c x)) : q < 1 := by
  have hg := instance_gap h
  have hp : 0 < linear b x+linear c x := by
    obtain ⟨ha,hab,hbc,hcd,he⟩ := h
    linarith
  nlinarith

private lemma adjacent_ratio_gt_one {a b c d x : Vec} {r : ℚ}
    (h : OrderedInstance a b c d x)
    (hr : linear a x-linear b x=r*(linear d x-linear c x)) : 1 < -r := by
  have hg := instance_gap h
  have hp : 0 < linear d x-linear c x := sub_pos.mpr h.2.2.2.1
  nlinarith

private lemma cross_ratio_gt_one {a b c d x : Vec} {r : ℚ}
    (h : OrderedInstance a b c d x)
    (hr : linear a x-linear c x=r*(linear d x-linear b x)) : 1 < -r := by
  have hg := instance_gap h
  have hp : 0 < linear d x-linear b x := sub_pos.mpr (h.2.2.1.trans_lt h.2.2.2.1)
  nlinarith

private lemma linearize_neg (p : ℚ[X]) (x : Vec) :
    linearize (-p) x = -linearize p x := by
  simp only [linearize,coeff_neg]
  ring

private lemma nontrivial_of_instance {a b c d x : Vec} (h : OrderedInstance a b c d x) :
    quad a^3+quad d^3 ≠ 0 ∧ quad a ≠ quad b ∧ quad a ≠ quad c := by
  have hn : quad a^3+quad d^3 ≠ 0 := by
    intro hz
    have he : quad a^3=(-quad d)^3 := by linear_combination hz
    have he' := congrArg (fun p => linearize p x) (cube_injective he)
    simp only [linearize_neg,linearize_quad] at he'
    obtain ⟨ha,hab,hbc,hcd,he⟩ := h
    linarith
  have hne {e : Vec} (he : linear a x < linear e x) : quad a ≠ quad e := by
    intro hz
    have hh := congrArg (fun p => linearize p x) hz
    simp only [linearize_quad] at hh
    exact he.ne hh
  exact ⟨hn,hne h.2.1,hne (h.2.1.trans_le h.2.2.1)⟩

/-- A fixed rational quadratic family has its ordered positive gap ratios
uniformly bounded away from both one and infinity. -/
theorem uniform_gap_bound {a b c d : Vec}
    (hc : quad a^3+quad d^3=quad b^3+quad c^3) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ x : Vec, OrderedInstance a b c d x →
      ((H:ℚ)+1)*(linear d x-linear c x) ≤ H*(linear b x-linear a x) ∧
      linear b x-linear a x ≤ H*(linear d x-linear c x) := by
  by_cases hex : ∃ x, OrderedInstance a b c d x
  swap
  · exact ⟨1,le_rfl,fun x hx => (hex ⟨x,hx⟩).elim⟩
  obtain ⟨x₀,hx₀⟩ := hex
  obtain ⟨hn,hab,hac⟩ := nontrivial_of_instance hx₀
  rcases normalized_pair_relation hc hn hab hac with
    ⟨q,hq,hq1,hr⟩ | ⟨r,hr0,hr1,hr⟩ | ⟨r,hr0,hr1,hr⟩
  · have hq' : (q:ℝ) < 1 := by exact_mod_cast sum_ratio_lt_one hx₀ (hr x₀)
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq
    obtain ⟨H,hH,hcompact⟩ := integer_compact_interval
      (U := 12*((q:ℝ)/(1-q))^2) (by linarith : (1:ℝ) < 1+(1-q)/2)
    refine ⟨H,hH,fun x hx => ?_⟩
    have hb := sum_ratio_bounds
      (show (0:ℝ) ≤ (linear a x:ℝ) by exact_mod_cast hx.1.le)
      (show (linear a x:ℝ) < (linear b x:ℝ) by exact_mod_cast hx.2.1)
      (show (linear b x:ℝ) ≤ (linear c x:ℝ) by exact_mod_cast hx.2.2.1)
      (show (linear c x:ℝ) < (linear d x:ℝ) by exact_mod_cast hx.2.2.2.1)
      (show (linear a x:ℝ)^3+(linear d x:ℝ)^3=
        (linear b x:ℝ)^3+(linear c x:ℝ)^3 by exact_mod_cast hx.2.2.2.2)
      hq0 hq' (by exact_mod_cast hr x)
    have hk : (0:ℝ) < (linear d x:ℝ)-(linear c x:ℝ) := by
      apply sub_pos.mpr
      exact_mod_cast hx.2.2.2.1
    have hh := hcompact _ _ hk hb.1 hb.2
    exact_mod_cast hh
  · have hs : (1:ℝ) < -(r:ℝ) := by exact_mod_cast adjacent_ratio_gt_one hx₀ (hr x₀)
    obtain ⟨H,hH,hcompact⟩ := integer_compact_interval (U := -(r:ℝ)) hs
    refine ⟨H,hH,fun x hx => ?_⟩
    have hk : (0:ℝ) < (linear d x:ℝ)-(linear c x:ℝ) := by
      apply sub_pos.mpr
      exact_mod_cast hx.2.2.2.1
    have he : (linear b x:ℝ)-(linear a x:ℝ)=
        -(r:ℝ)*((linear d x:ℝ)-(linear c x:ℝ)) := by
      have hh : (linear a x:ℝ)-(linear b x:ℝ)=
          (r:ℝ)*((linear d x:ℝ)-(linear c x:ℝ)) := by exact_mod_cast hr x
      nlinarith only [hh]
    have hh := hcompact _ _ hk he.ge he.le
    exact_mod_cast hh
  · have hs : (1:ℝ) < -(r:ℝ) := by exact_mod_cast cross_ratio_gt_one hx₀ (hr x₀)
    obtain ⟨H,hH,hcompact⟩ := integer_compact_interval
      (U := 12*((-(r:ℝ))/(-(r:ℝ)-1))^2) hs
    refine ⟨H,hH,fun x hx => ?_⟩
    have he : (linear c x:ℝ)-(linear a x:ℝ)=
        -(r:ℝ)*((linear d x:ℝ)-(linear b x:ℝ)) := by
      have hh : (linear a x:ℝ)-(linear c x:ℝ)=
          (r:ℝ)*((linear d x:ℝ)-(linear b x:ℝ)) := by exact_mod_cast hr x
      nlinarith only [hh]
    have hb := cross_ratio_bounds
      (show (0:ℝ) ≤ (linear a x:ℝ) by exact_mod_cast hx.1.le)
      (show (linear a x:ℝ) < (linear b x:ℝ) by exact_mod_cast hx.2.1)
      (show (linear b x:ℝ) ≤ (linear c x:ℝ) by exact_mod_cast hx.2.2.1)
      (show (linear c x:ℝ) < (linear d x:ℝ) by exact_mod_cast hx.2.2.2.1)
      (show (linear a x:ℝ)^3+(linear d x:ℝ)^3=
        (linear b x:ℝ)^3+(linear c x:ℝ)^3 by exact_mod_cast hx.2.2.2.2)
      hs he
    have hk : (0:ℝ) < (linear d x:ℝ)-(linear c x:ℝ) := by
      apply sub_pos.mpr
      exact_mod_cast hx.2.2.2.1
    have hh := hcompact _ _ hk hb.1 hb.2
    exact_mod_cast hh

private lemma widen_gap_bound {H K : ℕ} (hHK : H ≤ K) {h k : ℚ}
    (hh : ((H:ℚ)+1)*k ≤ H*h) (hu : h ≤ H*k) (hk : 0 < k) :
    ((K:ℚ)+1)*k ≤ K*h ∧ h ≤ K*k := by
  have hHK' : (H:ℚ) ≤ K := by exact_mod_cast hHK
  have hH : (0:ℚ) ≤ H := Nat.cast_nonneg H
  have hgap : k ≤ h := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hHK') (sub_nonneg.mpr hgap)
  constructor
  · nlinarith
  · exact hu.trans (mul_le_mul_of_nonneg_right hHK' hk.le)

/-- The bound is simultaneous over a finite collection. This does not take
intersections of independently constructed positive-density sets. -/
theorem finite_uniform_gap_bound {ι : Type*} [Finite ι] (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ i x, OrderedInstance (a i) (b i) (c i) (d i) x →
      ((H:ℚ)+1)*(linear (d i) x-linear (c i) x) ≤
        H*(linear (b i) x-linear (a i) x) ∧
      linear (b i) x-linear (a i) x ≤ H*(linear (d i) x-linear (c i) x) := by
  classical
  letI := Fintype.ofFinite ι
  choose K hK hbound using fun i => uniform_gap_bound (hc i)
  let H := 1+∑ i, K i
  have hHK (i : ι) : K i ≤ H := by
    have hh := Finset.single_le_sum (f := K) (fun j _ => Nat.zero_le (K j)) (Finset.mem_univ i)
    dsimp [H]
    omega
  refine ⟨H,by dsimp [H]; omega,fun i x hx => ?_⟩
  exact widen_gap_bound (hHK i) (hbound i x hx).1 (hbound i x hx).2
    (sub_pos.mpr hx.2.2.2.1)

/-- All integral ordered instances of finitely many quadratic families can be
excluded simultaneously at positive lower density, including every dilation. -/
theorem positive_density_avoids_finite_families {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ i x (u v w z : ℕ), OrderedInstance (a i) (b i) (c i) (d i) x →
        linear (a i) x=(u:ℚ) → linear (b i) x=(v:ℚ) →
        linear (c i) x=(w:ℚ) → linear (d i) x=(z:ℚ) →
        ¬ (v ∈ A ∧ z ∈ A) := by
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  obtain ⟨A,hA,hden,havoid⟩ :=
    CompactGapRatioColoring.positive_density_avoids_compact_gap_ratios H hH
  refine ⟨A,hA,hden,fun i x u v w z hx hu hv hw hz => ?_⟩
  have hb := hbound i x hx
  rcases hx with ⟨hpos,huv,hvw,hwz,he⟩
  simp only [hu,hv,hw,hz] at hb huv hvw hwz he
  have huv' : u < v := by exact_mod_cast huv
  have hvw' : v ≤ w := by exact_mod_cast hvw
  have hwz' : w < z := by exact_mod_cast hwz
  rw [← Nat.cast_sub hwz'.le,← Nat.cast_sub huv'.le] at hb
  exact havoid u v w z huv' hvw' hwz' (by exact_mod_cast he)
    (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)

lemma linear_specialization (a : Vec) (t ell : ℚ) :
    linear a (ell • ![t^2,t,1]) = ell*(quad a).eval t := by
  simp only [map_smul,smul_eq_mul,QuadraticResidualBridge.quad_eval]

/-- Direct polynomial-parameter interface, including arbitrary rational scales
and therefore all integral normalizations and dilations that are ordered. -/
theorem positive_density_avoids_finite_specializations {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ i (t ell : ℚ) (u v w z : ℕ), 0 < u → u < v → v ≤ w → w < z →
        ell*(quad (a i)).eval t=(u:ℚ) → ell*(quad (b i)).eval t=(v:ℚ) →
        ell*(quad (c i)).eval t=(w:ℚ) → ell*(quad (d i)).eval t=(z:ℚ) →
        ¬ (v ∈ A ∧ z ∈ A) := by
  obtain ⟨A,hA,hden,havoid⟩ := positive_density_avoids_finite_families a b c d hc
  refine ⟨A,hA,hden,fun i t ell u v w z hu huv hvw hwz ha hb hc' hd => ?_⟩
  let x : Vec := ell • ![t^2,t,1]
  have hval (p : Vec) : linear p x=ell*(quad p).eval t := linear_specialization p t ell
  have he : (linear (a i) x)^3+(linear (d i) x)^3=
      (linear (b i) x)^3+(linear (c i) x)^3 := by
    simp only [hval,mul_pow,← mul_add]
    congr 1
    simpa only [eval_add,eval_pow] using congrArg (fun p : ℚ[X] => p.eval t) (hc i)
  apply havoid i x u v w z
  · refine ⟨?_,?_,?_,?_,he⟩
    · rw [hval,ha]; exact_mod_cast hu
    · rw [hval,hval,ha,hb]; exact_mod_cast huv
    · rw [hval,hval,hb,hc']; exact_mod_cast hvw
    · rw [hval,hval,hc',hd]; exact_mod_cast hwz
  · exact (hval _).trans ha
  · exact (hval _).trans hb
  · exact (hval _).trans hc'
  · exact (hval _).trans hd

#print axioms uniform_gap_bound
#print axioms finite_uniform_gap_bound
#print axioms positive_density_avoids_finite_families
#print axioms positive_density_avoids_finite_specializations
end Erdos1206.QuadraticFamilyAvoidance
