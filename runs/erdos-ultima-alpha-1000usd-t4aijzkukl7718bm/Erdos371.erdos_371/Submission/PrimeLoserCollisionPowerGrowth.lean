import Submission.PrimeLoserSignedCollisions

/-! Polynomial growth of the actual unsigned collision obstruction. A positive
incidence mass is already carried by a fixed power-sized set of loser labels. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

def primeLoserBandSet (B C N : ℕ) : Finset ℕ :=
  (bothAboveSet B N).filter fun n => primeLoser n ≤ C

lemma bothAboveSet_mono_cutoff (B C N : ℕ) (hBC : B≤C) :
    bothAboveSet C N ⊆ bothAboveSet B N := by
  intro n hn
  obtain ⟨hnN,hnC,hnC'⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnN, hBC.trans_lt hnC,hBC.trans_lt hnC'⟩

lemma primeLoserBandSet_card_add_top (B C N : ℕ) (hBC : B≤C) :
    (primeLoserBandSet B C N).card + (bothAboveSet C N).card =
      (bothAboveSet B N).card := by
  have he : (bothAboveSet B N).filter (fun n => ¬primeLoser n≤C) = bothAboveSet C N := by
    ext n
    simp only [mem_filter,not_le]
    constructor
    · rintro ⟨hn,hp⟩
      exact mem_filter.mpr ⟨(mem_filter.mp hn).1,lt_min_iff.mp hp⟩
    · intro hn
      exact ⟨bothAboveSet_mono_cutoff B C N hBC hn,
        lt_min (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2⟩
  have h := card_filter_add_card_filter_not (s := bothAboveSet B N)
    (fun n => primeLoser n≤C)
  rw [he] at h
  exact h

/-- Cauchy--Schwarz using only the labels in a bounded middle window, while
retaining all original collisions on the right. -/
lemma primeLoserBandSet_card_sq_bound (B C N : ℕ) :
    ((primeLoserBandSet B C N).card : ℝ)^2 ≤
      (C+1 : ℝ)*(N+(primeLoserCollisions B N).card) := by
  let S := primeLoserBandSet B C N
  let T := range (C+1)
  let d (p : ℕ) := (S.filter fun n => primeLoser n=p).card
  have hmap : (S : Set ℕ).MapsTo primeLoser T := by
    intro n hn
    change n ∈ (bothAboveSet B N).filter (fun n => primeLoser n≤C) at hn
    exact mem_range.mpr (by have := (mem_filter.mp hn).2; omega)
  have hsum : (∑ p ∈ T, (d p : ℝ))=S.card := by
    exact_mod_cast (card_eq_sum_card_fiberwise hmap).symm
  have hsub : S.offDiag.filter (fun nm => primeLoser nm.1=primeLoser nm.2) ⊆
      primeLoserCollisions B N := by
    intro nm hnm
    obtain ⟨hnm,he⟩ := mem_filter.mp hnm
    obtain ⟨hn,hm,hne⟩ := mem_offDiag.mp hnm
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨(mem_filter.mp hn).1,
      (mem_filter.mp hm).1,hne⟩,he⟩
  have hmass : S.card ≤ N := by
    apply (card_le_card ((filter_subset _ _).trans (filter_subset _ _))).trans_eq
      (card_range N)
  have hsq : (∑ p ∈ T, (d p : ℝ)^2) ≤ N+(primeLoserCollisions B N).card := by
    have hh := (sum_card_sq_fibers_le_same_pairs S T primeLoser).trans_eq
      (card_same_pairs_eq_diagonal_add_offDiag S primeLoser)
    exact_mod_cast hh.trans (Nat.add_le_add hmass (card_le_card hsub))
  have hcs := sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun p => (d p : ℝ))
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hsum, T, card_range,
    Nat.cast_add,Nat.cast_one] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- A positive mass in a sublinear power-sized label window forces a
polynomially superlinear collision count. -/
theorem primeLoserCollisions_power_growth_of_band_mass
    (B C : ℕ → ℕ) (c K u : ℝ) (hc : 0<c) (hK : 0<K) (hu : 0<u)
    (hmass : ∀ᶠ N : ℕ in atTop, c*(N : ℝ) ≤ (primeLoserBandSet (B N) (C N) N).card)
    (hlabels : ∀ᶠ N : ℕ in atTop, (C N+1 : ℝ) ≤ K*(N : ℝ)^(1-u)) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ)^(1+u/2) ≤ (primeLoserCollisions (B N) N).card := by
  have hgrow := ((tendsto_rpow_atTop (half_pos hu)).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*K/c^2)
  filter_upwards [hmass,hlabels,hgrow,eventually_ge_atTop (1 : ℕ)] with N hm hl hg hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)<N := by linarith
  have hpow0 := Real.rpow_pos_of_pos hN0 (u/2)
  have hpow : (N : ℝ) ≤ (N : ℝ)^(1+u/2) := by
    calc
      _ = (N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmasssq : c^2*(N : ℝ)^2 ≤ ((primeLoserBandSet (B N) (C N) N).card : ℝ)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hm 2
  have hraw := primeLoserBandSet_card_sq_bound (B N) (C N) N
  have hraw' := hmasssq.trans (hraw.trans
    (mul_le_mul_of_nonneg_right hl (by positivity)))
  by_contra hnot
  have hQ : ((primeLoserCollisions (B N) N).card : ℝ)<(N : ℝ)^(1+u/2) := lt_of_not_ge hnot
  have hsum : (N : ℝ)+(primeLoserCollisions (B N) N).card < 2*(N : ℝ)^(1+u/2) := by linarith
  have hh := mul_lt_mul_of_pos_left hsum (mul_pos hK (Real.rpow_pos_of_pos hN0 (1-u)))
  have hexp : K*(N : ℝ)^(1-u)*(2*(N : ℝ)^(1+u/2)) =
      2*K*(N : ℝ)^(2-u/2) := by
    rw [show K*(N : ℝ)^(1-u)*(2*(N : ℝ)^(1+u/2)) =
      2*K*((N : ℝ)^(1-u)*(N : ℝ)^(1+u/2)) by ring,
      ← Real.rpow_add hN0]
    congr 2
    ring
  rw [hexp] at hh
  have hg' : 2*K < c^2*(N : ℝ)^(u/2) := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hc)).mp hg
    simpa only [Function.comp_apply,mul_comm] using h
  have hg'' := mul_lt_mul_of_pos_right hg' (Real.rpow_pos_of_pos hN0 (2-u/2))
  have hid : c^2*(N : ℝ)^(u/2)*(N : ℝ)^(2-u/2) = c^2*(N : ℝ)^2 := by
    rw [mul_assoc,← Real.rpow_add hN0]
    norm_num
  rw [hid] at hg''
  linarith

/-- A fixed top power cutoff can be chosen to leave positive middle-window
incidence mass above N^(21/40). -/
theorem upperHalf_positive_band_mass_exists :
    ∃ u : ℝ, 0<u ∧ u≤1/8 ∧
      (∀ᶠ N : ℕ in atTop,
        (1/40 : ℝ)*(N : ℝ) ≤
          (primeLoserBandSet (ceilPowerCutoff (21/40) N)
            (ceilPowerCutoff (1-u) N) N).card) ∧
      (∀ᶠ N : ℕ in atTop,
        (ceilPowerCutoff (1-u) N+1 : ℝ) ≤ 3*(N : ℝ)^(1-u)) := by
  have hL : 0≤largePairConstant := by unfold largePairConstant; positivity
  let u : ℝ := min (1/8) (1/(160*(largePairConstant+1)))
  have hu0 : 0<u := lt_min (by norm_num) (by positivity)
  have hu : u≤1/8 := min_le_left _ _
  have hsmall : largePairConstant*u^2 ≤ 1/160 := by
    have hh : u*(160*(largePairConstant+1)) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hs : u^2≤u := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hs hL
    nlinarith
  refine ⟨u,hu0,hu,?_,?_⟩
  · have htop := bothLargePrimeSet_eventually_ratio_le u hu0.le hu (1/160) (by norm_num)
    filter_upwards [bothAbove_upperHalf_positive_proportion,htop,
      eventually_gt_atTop (1 : ℕ)] with N hmass htopN hN
    have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN.le
    have hBC : ceilPowerCutoff (21/40) N ≤ ceilPowerCutoff (1-u) N := by
      apply Nat.ceil_mono
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsub : bothAboveSet (ceilPowerCutoff (1-u) N) N ⊆ bothLargePrimeSet N u := by
      intro n hn
      obtain ⟨hnN,hp,hp'⟩ := mem_filter.mp hn
      have hceil := Nat.le_ceil ((N : ℝ)^(1-u))
      exact mem_filter.mpr ⟨hnN,hceil.trans_lt (by exact_mod_cast hp),
        hceil.trans_lt (by exact_mod_cast hp')⟩
    have htopbound : ((bothAboveSet (ceilPowerCutoff (1-u) N) N).card : ℝ)/N ≤ 1/80 := by
      have hh := div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub :
        ((bothAboveSet (ceilPowerCutoff (1-u) N) N).card : ℝ)≤(bothLargePrimeSet N u).card) hN0.le
      linarith
    have he : ((primeLoserBandSet (ceilPowerCutoff (21/40) N) (ceilPowerCutoff (1-u) N) N).card : ℝ) +
        (bothAboveSet (ceilPowerCutoff (1-u) N) N).card =
          (bothAboveSet (ceilPowerCutoff (21/40) N) N).card := by
      exact_mod_cast primeLoserBandSet_card_add_top _ _ N hBC
    have hm := (le_div_iff₀ hN0).mp hmass
    have ht := (div_le_iff₀ hN0).mp htopbound
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    have hpow1 : (1 : ℝ)≤(N : ℝ)^(1-u) := Real.one_le_rpow hN1 (by linarith)
    have hc := Nat.ceil_lt_add_one (show 0≤(N : ℝ)^(1-u) by positivity)
    change (ceilPowerCutoff (1-u) N : ℝ)<_ at hc
    linarith

/-- The actual upper-half unsigned collision count grows at least as a fixed
power N^(1+delta), for some delta>0. This does not negate a signed estimate. -/
theorem primeLoserCollisions_upperHalf_polynomial_growth :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ)^(1+δ) ≤ (primeLoserCollisions (ceilPowerCutoff (21/40) N) N).card := by
  obtain ⟨u,hu0,hu,hmass,hlabels⟩ := upperHalf_positive_band_mass_exists
  exact ⟨u/2,half_pos hu0,primeLoserCollisions_power_growth_of_band_mass
    _ _ (1/40) 3 u (by norm_num) (by norm_num) hu0 hmass hlabels⟩

#print axioms primeLoserBandSet_card_sq_bound
#print axioms upperHalf_positive_band_mass_exists
#print axioms primeLoserCollisions_upperHalf_polynomial_growth
end Erdos371
