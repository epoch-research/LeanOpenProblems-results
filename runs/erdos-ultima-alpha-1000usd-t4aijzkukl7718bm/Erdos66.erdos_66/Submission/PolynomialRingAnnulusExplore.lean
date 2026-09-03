import Submission.PolynomialRingCoverCapacityExplore
import Submission.SidonColorWitnessExplore

/-! A positive logarithmic counting profile requires at least a constant
multiple of sqrt(q) polynomial graph charts modulo q^2 in the annulus
[q^4,4q^4), when q ranges over powers of two. -/
namespace Erdos66PolynomialRingAnnulus
open Filter AdditiveCombinatorics Erdos66PolynomialRingGraphCapacity
  Erdos66PolynomialRingCoverCapacity Erdos66SidonColorWitness Erdos66Counting
  Erdos66TauberianProfile Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 3000000

noncomputable def annulus (A : Set ℕ) (q : ℕ) : Finset ℕ :=
  (Finset.Ico (q^4) (4*q^4)).filter (fun n ↦ n ∈ A)

lemma annulus_count (A : Set ℕ) (q : ℕ) :
    ((annulus A q).card : ℝ) = (count A (4*q^4) : ℝ)-count A (q^4) := by
  have hsub : cutoff A (q^4) ⊆ cutoff A (4*q^4) := cutoff_mono' A (by omega)
  have he : annulus A q = cutoff A (4*q^4) \ cutoff A (q^4) := by
    ext n
    simp only [annulus,Finset.mem_filter,Finset.mem_Ico,Finset.mem_sdiff,mem_cutoff]
    constructor
    · rintro ⟨⟨hl,hu⟩,ha⟩
      exact ⟨⟨hu,ha⟩,fun h ↦ by omega⟩
    · rintro ⟨⟨hu,ha⟩,hn⟩
      refine ⟨⟨?_,hu⟩,ha⟩
      by_contra hh
      exact hn ⟨by omega,ha⟩
  rw [he,Finset.card_sdiff_of_subset hsub,Nat.cast_sub (Finset.card_le_card hsub)]
  rfl

lemma scale_identities (J : ℕ) :
    (2^J)^4 = 4^(2*J) ∧ 4*(2^J)^4 = 4^(2*J+1) := by
  have he : (2^J)^4 = 4^(2*J) := by
    rw [show (4 : ℕ)=2^2 by decide,← pow_mul,← pow_mul]
    congr 1
    omega
  exact ⟨he,by rw [he,pow_succ]; omega⟩

lemma counting_profile_annulus_lower (A : Set ℕ) (L : ℝ) (hL : 0 < L)
    (hcount : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 L)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ J : ℕ in atTop,
      γ*((2^J : ℕ) : ℝ)^4*J ≤ ((annulus A (2^J)).card : ℝ)^2 := by
  let D := L*Real.sqrt (Real.log 4)
  have hD : 0 < D := mul_pos hL (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))
  have hg := geometric_count_limit hcount
  obtain ⟨K,hK,hbounds⟩ := geometric_count_bounds hD hg
  refine ⟨(D/4)^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1] with J hJ hJ1
  have hlo := (hbounds (2*J+1) (by omega)).1
  have hhi := (hbounds (2*J) (by omega)).2
  have hsqrt : Real.sqrt ((2*J : ℕ) : ℝ) ≤ Real.sqrt ((2*J+1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (2*J))
  have hlow : (D/4)*((2 : ℝ)^(2*J)*Real.sqrt ((2*J : ℕ) : ℝ)) ≤
      (count A (4^(2*J+1)) : ℝ)-count A (4^(2*J)) := by
    rw [pow_succ] at hlo
    have hh := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ (3*D/2)*(2 : ℝ)^(2*J))
    nlinarith
  rw [← (scale_identities J).2,← (scale_identities J).1,← annulus_count A (2^J)] at hlow
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (D/4)*((2 : ℝ)^(2*J)*Real.sqrt ((2*J : ℕ) : ℝ))) hlow 2
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  have he : ((2 : ℝ)^(2*J))^2 = ((2^J : ℕ) : ℝ)^4 := by
    push_cast
    rw [← pow_mul,← pow_mul]
    congr 1
    omega
  rw [he] at hsq
  push_cast at hsq
  have hnon : 0 ≤ (D/4)^2*((2^J : ℕ) : ℝ)^4*(J : ℝ) := by positivity
  push_cast at hnon ⊢
  nlinarith

lemma annular_log_cap (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (J : ℕ) (hJ : 1 ≤ J) :
    K+C*Real.log (2*((4*(2^J)^4 : ℕ) : ℝ)+2*((2^J : ℕ) : ℝ)^4+2) ≤
      2*(K+15*C+1)*(J : ℝ) := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^(4*J) := one_le_pow₀ (by norm_num)
  have he : 2*((4*(2^J)^4 : ℕ) : ℝ)+2*((2^J : ℕ) : ℝ)^4+2 ≤ 12*(2 : ℝ)^(4*J) := by
    push_cast
    have hh : ((2 : ℝ)^J)^4 = (2 : ℝ)^(4*J) := by rw [← pow_mul]; congr 1; omega
    rw [hh]
    linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2*((4*(2^J)^4 : ℕ) : ℝ)+2*((2^J : ℕ) : ℝ)^4+2) he
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  have h12 : Real.log (12 : ℝ) ≤ 11 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 12 by norm_num)]
  have h2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  push_cast at hl
  have hm := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 4*J by positivity)
  have hb : Real.log (2*((4*(2^J)^4 : ℕ) : ℝ)+2*((2^J : ℕ) : ℝ)^4+2) ≤ 15*(J : ℝ) := by
    push_cast
    linarith
  have hc := mul_le_mul_of_nonneg_left hb hC
  nlinarith

/-- No arbitrary-graph description is assumed of the set. The conclusion
is conditional on an actual cover by these polynomial charts. -/
theorem counting_profile_cover_lower (A : Set ℕ) (L K C : ℝ) (hL : 0 < L)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcount : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 L))
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ J : ℕ in atTop, ∀ h : ℕ,
      ∀ P : Fin h → Polynomial (ZMod ((2^J)^2)), ∀ a : Fin h → ℕ,
      (∀ i, a i ≤ 4*(2^J)^4) →
      (∀ n ∈ annulus A (2^J), ∃ i x, n = encodeGraph (2^J) (P i) (a i) x) →
      η*((2^J : ℕ) : ℝ) ≤ (h : ℝ)^2 := by
  obtain ⟨γ,hγ,hann⟩ := counting_profile_annulus_lower A L hL hcount
  let V₀ := K+15*C+1
  have hV₀ : 0 < V₀ := by dsimp [V₀]; positivity
  refine ⟨γ/(8*V₀),by positivity,?_⟩
  filter_upwards [hann,eventually_ge_atTop 1] with J hmass hJ
  intro h P a ha hcover
  have hq : 0 < (2^J : ℕ) := by positivity
  letI : NeZero (2^J : ℕ) := ⟨by omega⟩
  have hs : (annulus A (2^J) : Set ℕ) ⊆ A := by
    intro n hn
    change n ∈ (Finset.Ico ((2^J)^4) (4*(2^J)^4)).filter (fun n ↦ n ∈ A) at hn
    exact (Finset.mem_filter.mp hn).2
  have hc := polynomial_cover_log_capacity (2^J) h P a (4*(2^J)^4) ha
    (annulus A (2^J)) A hs hcover K C hK hC henv
  have hl := annular_log_cap K C hK hC J hJ
  have he : 2*((((4*(2^J)^4 : ℕ) : ℝ))+((2^J : ℕ) : ℝ)^4)+2 =
      2*((4*(2^J)^4 : ℕ) : ℝ)+2*((2^J : ℕ) : ℝ)^4+2 := by ring
  rw [he] at hc
  have hb := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ 4*(h : ℝ)^2*((2^J : ℕ) : ℝ)^3 by positivity)
  have htotal : γ*((2^J : ℕ) : ℝ)^4*(J : ℝ) ≤
      8*V₀*(h : ℝ)^2*((2^J : ℕ) : ℝ)^3*(J : ℝ) := by
    dsimp only [V₀]
    nlinarith only [hmass,hc,hb]
  have hp : 0 < ((2^J : ℕ) : ℝ)^3*(J : ℝ) := by positivity
  have hcancel : γ*((2^J : ℕ) : ℝ) ≤ 8*V₀*(h : ℝ)^2 := by
    apply le_of_mul_le_mul_right (a := ((2^J : ℕ) : ℝ)^3*(J : ℝ)) _ hp
    nlinarith only [htotal]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 8*V₀ by positivity)).mpr
  -- Put the constant denominator on the entire left-hand product.
  nlinarith

/-- Every hypothetical witness requires at least on the order of sqrt(q)
charts in these square-modulus annuli, even with arbitrary degrees and
arbitrary within-graph thinning. -/
theorem witness_cover_lower {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ J : ℕ in atTop, ∀ h : ℕ,
      ∀ P : Fin h → Polynomial (ZMod ((2^J)^2)), ∀ a : Fin h → ℕ,
      (∀ i, a i ≤ 4*(2^J)^4) →
      (∀ n ∈ annulus A (2^J), ∃ i x, n = encodeGraph (2^J) (P i) (a i) x) →
      η*((2^J : ℕ) : ℝ) ≤ (h : ℝ)^2 := by
  obtain ⟨K,C,hK,hC,henv⟩ := global_log_upper_bound h
  have hcpos := limit_pos hc h
  exact counting_profile_cover_lower A (2*Real.sqrt (c/Real.pi)) K C (by positivity) hK hC.le
    (witness_counting_profile hc h) henv


/-- An explicit restricted-class exclusion. This additional polynomial-cover
hypothesis is not present in the original conjecture. -/
theorem subcritical_chart_cover_excludes_witness (A : Set ℕ) (h : ℕ → ℕ)
    (P : (J : ℕ) → Fin (h J) → Polynomial (ZMod ((2^J)^2)))
    (a : (J : ℕ) → Fin (h J) → ℕ)
    (hsmall : Tendsto (fun J ↦ (h J : ℝ)^2/((2^J : ℕ) : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ J : ℕ in atTop, ∀ i, a J i ≤ 4*(2^J)^4)
    (hcover : ∀ᶠ J : ℕ in atTop, ∀ n ∈ annulus A (2^J),
      ∃ i x, n = encodeGraph (2^J) (P J i) (a J i) x)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro hlim
  obtain ⟨η,hη,hlower⟩ := witness_cover_lower hc hlim
  obtain ⟨J,hJ,hJb,hJc,hJs⟩ := (hlower.and (hbound.and (hcover.and
    (hsmall.eventually_lt_const hη)))).exists
  have hh := hJ (h J) (P J) (a J) hJb hJc
  have hp : (0 : ℝ) < ((2^J : ℕ) : ℝ) := by positivity
  have ht := (div_lt_iff₀ hp).mp hJs
  nlinarith

end Erdos66PolynomialRingAnnulus
