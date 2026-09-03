import Submission.NaturalSidonExtractionExplore
import Submission.Explore

/-! A near-scale annular basis cannot be chosen independently of every old
prefix satisfying a logarithmic upper envelope. This does not rule out
prefix-dependent choices or a carefully compatible infinite construction. -/
namespace Erdos66NearScalePrefixObstruction
open Filter AdditiveCombinatorics Erdos66NaturalSidonExtraction Erdos66NatPairAlgebra Erdos66Explore
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma reflected_prefix_peak (D : Set ℕ) (E : Finset ℕ) (L t m : ℕ)
    (hL : 1≤L) (hD : ∀a∈D, 3*L≤a) (hED : (E : Set ℕ)⊆D)
    (hE : ∀a∈E, t-2*L≤a ∧ a<t-L) (htlo : 5*L≤t) (hthi : t≤6*L)
    (hm : m^4<E.card) (c : ℝ) (hc : 0<c)
    (hsmall : 2/Real.log ((2*L : ℕ) : ℝ)≤c)
    (hpeak : c*Real.log ((6*L : ℕ) : ℝ)<2*m) :
    ∃ A : Finset ℕ, (∀a∈A, a<3*L) ∧
      (∀n : ℕ, (sumRep (A : Set ℕ) n : ℝ)/Real.log n≤c) ∧
      c<(sumRep ((A : Set ℕ)∪D) t : ℝ)/Real.log t := by
  obtain ⟨F,hFE,hFcard,hFsidon⟩ := exists_natSidon_subset E m hm
  have hFt : ∀a∈F, a≤t := by
    intro a ha
    have hh := (hE a (hFE ha)).2
    omega
  let A := natReflect t F
  have hAbounds : ∀a∈A, L<a ∧ a≤2*L := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have hh := hE b (hFE hb)
    omega
  have hAsidon : NatSidon A := natReflect_sidon hFsidon t hFt
  have hlogL : 0<Real.log ((2*L : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<2*L by omega))
  have hlogt : 0<Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (show 1<t by omega))
  have hdis : Disjoint F A := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h₁ := hD a (hED (hFE ha))
    have h₂ := (hAbounds a hb).2
    omega
  have hbase : 2*m≤sumRep ((F∪A : Finset ℕ) : Set ℕ) t := by
    rw [sumRep_union_self _ _ _ hdis,natReflect_mixed F t hFt,hFcard]
    omega
  have hmono := sumRep_mono (show ((F∪A : Finset ℕ) : Set ℕ)⊆(A : Set ℕ)∪D from by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Or.inr (hED (hFE ha))
    · exact Or.inl ha) t
  refine ⟨A,fun a ha ↦ by have hh := hAbounds a ha; omega,?_,?_⟩
  · intro n
    by_cases hn : n≤2*L
    · have hz : sumRep (A : Set ℕ) n=0 := by
        rw [←pairs_self]
        exact pairs_zero_of_lower A A (L+1) (L+1) n
          (fun a ha ↦ by have hh := hAbounds a ha; omega)
          (fun a ha ↦ by have hh := hAbounds a ha; omega) (by omega)
      rw [hz,Nat.cast_zero,zero_div]
      exact hc.le
    have hlogcomp : Real.log ((2*L : ℕ) : ℝ)≤Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0<2*L by omega)) (by exact_mod_cast (show 2*L≤n by omega))
    have hlogn := hlogL.trans_le hlogcomp
    have hh : (sumRep (A : Set ℕ) n : ℝ)≤2 := by exact_mod_cast natSidon_rep_le_two hAsidon n
    exact (div_le_div_of_nonneg_right hh hlogn.le).trans
      ((div_le_div_of_nonneg_left (by norm_num) hlogL hlogcomp).trans hsmall)
  · apply (lt_div_iff₀ hlogt).mpr
    have hcomp : Real.log (t : ℝ)≤Real.log ((6*L : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0<t by omega)) (by exact_mod_cast hthi)
    have hm' : (2*m : ℝ)≤sumRep ((A : Set ℕ)∪D) t := by exact_mod_cast hbase.trans hmono
    exact (mul_le_mul_of_nonneg_left hcomp hc.le).trans_lt (hpeak.trans_le hm')

/-- Merely being a basis on the indicated interval forces enough new points
in one of its two lower half-intervals for the reflection construction. -/
lemma basis_forces_dense_half (D : Set ℕ) (L m : ℕ)
    (hD : ∀a∈D, 3*L≤a) (hbasis : ∀n : ℕ, 6*L≤n → n<8*L → 0<sumRep D n)
    (hL : 2*m^8<L) :
    ∃ E : Finset ℕ, (E : Set ℕ)⊆D ∧ m^4<E.card ∧
      ((∀a∈E, 3*L≤a ∧ a<4*L) ∨ (∀a∈E, 4*L≤a ∧ a<5*L)) := by
  let E := (Finset.Ico (3*L) (5*L)).filter (fun a ↦ a∈D)
  let E₁ := E.filter (fun a ↦ a<4*L)
  let E₂ := E.filter (fun a ↦ ¬a<4*L)
  have hrep (n : ℕ) (hn : 6*L≤n) (hn' : n<8*L) :
      sumRep D n=sumRep (E : Set ℕ) n := by
    rw [sumRep_def,sumRep_def]
    congr 1
    ext p
    simp only [Finset.mem_filter,Finset.mem_antidiagonal,Finset.mem_coe]
    constructor
    · rintro ⟨he,ha,hb⟩
      have ha' := hD p.1 ha
      have hb' := hD p.2 hb
      exact ⟨he,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha',by omega⟩,ha⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hb',by omega⟩,hb⟩⟩
    · rintro ⟨he,ha,hb⟩
      exact ⟨he,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
  have hmass : 2*L≤E.card^2 := by
    have hh := Finset.sum_le_sum (s := Finset.Ico (6*L) (8*L)) (f := fun _ ↦ (1 : ℕ))
      (g := fun n ↦ pairs E E n) (by
        intro n hn
        obtain ⟨hn,hn'⟩ := Finset.mem_Ico.mp hn
        change 1≤pairs E E n
        rw [pairs_self,←hrep n hn hn']
        exact hbasis n hn hn')
    have hm := pairs_sum_le E E (Finset.Ico (6*L) (8*L))
    have hc : (Finset.Ico (6*L) (8*L)).card=2*L := by rw [Nat.card_Ico]; omega
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hc] at hh
    nlinarith
  have hcards : E₁.card+E₂.card=E.card := Finset.card_filter_add_card_filter_not (s := E) (fun a ↦ a<4*L)
  have hbig : m^4<E₁.card ∨ m^4<E₂.card := by
    by_contra hh
    push_neg at hh
    have hc : E.card≤2*m^4 := by omega
    have hs : E.card^2≤(2*m^4)^2 := Nat.pow_le_pow_left hc 2
    nlinarith [show (2*m^4)^2=4*m^8 by ring]
  rcases hbig with hbig | hbig
  · refine ⟨E₁,?_,hbig,Or.inl ?_⟩
    · intro a ha
      change a∈E.filter _ at ha
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    · intro a ha
      obtain ⟨ha,ha'⟩ := Finset.mem_filter.mp ha
      exact ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1,ha'⟩
  · refine ⟨E₂,?_,hbig,Or.inr ?_⟩
    · intro a ha
      change a∈E.filter _ at ha
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    · intro a ha
      obtain ⟨ha,ha'⟩ := Finset.mem_filter.mp ha
      exact ⟨by omega,(Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2⟩

theorem near_scale_template_not_universal (c : ℝ) (hc : 0<c) (L m : ℕ)
    (hL : 2*m^8<L) (hsmall : 2/Real.log ((2*L : ℕ) : ℝ)≤c)
    (hpeak : c*Real.log ((6*L : ℕ) : ℝ)<2*m)
    (D : Set ℕ) (hD : ∀a∈D, 3*L≤a)
    (hbasis : ∀n : ℕ, 6*L≤n → n<8*L → 0<sumRep D n) :
    ∃ A : Finset ℕ, (∀a∈A, a<3*L) ∧
      (∀n : ℕ, (sumRep (A : Set ℕ) n : ℝ)/Real.log n≤c) ∧
      ∃ t : ℕ, 5*L≤t ∧ t≤6*L ∧ c<(sumRep ((A : Set ℕ)∪D) t : ℝ)/Real.log t := by
  obtain ⟨E,hED,hbig,hE⟩ := basis_forces_dense_half D L m hD hbasis hL
  rcases hE with hE | hE
  · obtain ⟨A,hA,hup,hpk⟩ := reflected_prefix_peak D E L (5*L) m (by omega) hD hED
      (fun a ha ↦ by have hh := hE a ha; omega) le_rfl (by omega) hbig c hc hsmall hpeak
    exact ⟨A,hA,hup,5*L,le_rfl,by omega,hpk⟩
  · obtain ⟨A,hA,hup,hpk⟩ := reflected_prefix_peak D E L (6*L) m (by omega) hD hED
      (fun a ha ↦ by have hh := hE a ha; omega) (by omega) le_rfl hbig c hc hsmall hpeak
    exact ⟨A,hA,hup,6*L,by omega,le_rfl,hpk⟩

lemma eventually_obstruction_parameters (c : ℝ) (hc : 0<c) :
    ∀ᶠ L : ℕ in atTop, ∃m : ℕ, 2*m^8<L ∧
      2/Real.log ((2*L : ℕ) : ℝ)≤c ∧ c*Real.log ((6*L : ℕ) : ℝ)<2*m := by
  have hlog : Tendsto (fun L : ℕ ↦ Real.log (L : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun L : ℕ ↦ (Real.log (L : ℝ))^8/(L : ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 8 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscaled := hdecay.const_mul (2*(c+2)^8)
  simp only [mul_zero] at hscaled
  filter_upwards [eventually_ge_atTop 2,
    hlog.eventually_ge_atTop (max 1 (max (2/c) (c*Real.log 6))),
    hscaled.eventually_lt_const (show (0 : ℝ)<1 by norm_num)] with L hL hl hs
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hl1 : 1≤Real.log (L : ℝ) := (le_max_left _ _).trans hl
  have hlc : 2/c≤Real.log (L : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hl
  have hl6 : c*Real.log 6≤Real.log (L : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hl
  let m : ℕ := ⌈(c+1)*Real.log (L : ℝ)⌉₊
  have hmlo : (c+1)*Real.log (L : ℝ)≤(m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ)≤(c+2)*Real.log (L : ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0≤(c+1)*Real.log (L : ℝ) by positivity)
    change (m : ℝ)<(c+1)*Real.log (L : ℝ)+1 at hh
    nlinarith
  have hmp : 0<(m : ℝ) := (mul_pos (by linarith) (by linarith)).trans_le hmlo
  refine ⟨m,?_,?_,?_⟩
  · have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hmhi 8
    have hh : 2*(c+2)^8*(Real.log (L : ℝ))^8<(L : ℝ) := by
      have hh : 2*(c+2)^8*(Real.log (L : ℝ))^8/(L : ℝ)<1 := by convert hs using 1 <;> ring
      exact (div_lt_one hLp).mp hh
    have hres : 2*(m : ℝ)^8<(L : ℝ) := by
      rw [mul_pow] at hpow
      linarith
    exact_mod_cast hres
  · have hcomp : Real.log (L : ℝ)≤Real.log ((2*L : ℕ) : ℝ) :=
      Real.log_le_log hLp (by exact_mod_cast (show L≤2*L by omega))
    apply (div_le_div_of_nonneg_left (by norm_num) (by linarith : 0<Real.log (L : ℝ)) hcomp).trans
    apply (div_le_iff₀ (by linarith : 0<Real.log (L : ℝ))).mpr
    have hh := (div_le_iff₀ hc).mp hlc
    nlinarith
  · have hlog6 : Real.log ((6*L : ℕ) : ℝ)=Real.log 6+Real.log (L : ℝ) := by
      push_cast
      exact Real.log_mul (by norm_num) hLp.ne'
    rw [hlog6]
    nlinarith

/-- At every sufficiently large scale, NO predetermined set supported above
3L and covering [6L,8L) works for every upper-bounded prefix below 3L.
The adverse prefix is itself Sidon, not merely globally upper-bounded. -/
theorem eventually_no_prefix_independent_near_scale_bridge (c : ℝ) (hc : 0<c) :
    ∀ᶠ L : ℕ in atTop, ∀D : Set ℕ,
      (∀a∈D, 3*L≤a) → (∀n : ℕ, 6*L≤n → n<8*L → 0<sumRep D n) →
      ∃ A : Finset ℕ, (∀a∈A, a<3*L) ∧
        (∀n : ℕ, (sumRep (A : Set ℕ) n : ℝ)/Real.log n≤c) ∧
        ∃ t : ℕ, 5*L≤t ∧ t≤6*L ∧ c<(sumRep ((A : Set ℕ)∪D) t : ℝ)/Real.log t := by
  filter_upwards [eventually_obstruction_parameters c hc] with L hL
  obtain ⟨m,hm,hs,hp⟩ := hL
  exact fun D hD hb ↦ near_scale_template_not_universal c hc L m hm hs hp D hD hb

end Erdos66NearScalePrefixObstruction
