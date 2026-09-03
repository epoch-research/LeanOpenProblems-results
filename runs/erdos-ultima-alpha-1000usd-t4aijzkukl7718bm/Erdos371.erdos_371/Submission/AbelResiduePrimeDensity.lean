import FormalConjecturesUtil

/-! Abel-weighted equidistribution of primes in fixed residue classes. The
weights are (s-1)*log(p)/p^s as s tends to 1 from the right. This is not a
natural prime-counting asymptotic or a uniform theorem in the modulus. -/
namespace Erdos371.AbelPrimes
open Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology

noncomputable def realDirichlet (c : ℕ → ℝ) (s : ℝ) : ℝ := ∑' n, c n/(n : ℝ)^s

lemma dirichlet_term_le_at_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (s : ℝ) (hs : 1 < s) (n : ℕ) : c n/(n : ℝ)^s ≤ c n/n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (by linarith : s ≠ 0)]
  · apply div_le_div_of_nonneg_left (hc n) (by exact_mod_cast hn)
    calc
      (n : ℝ) = (n : ℝ)^((1 : ℝ)) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hs.le

lemma summable_dirichlet_of_at_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsc : Summable (fun n => c n/n)) (s : ℝ) (hs : 1 < s) :
    Summable (fun n => c n/(n : ℝ)^s) :=
  hsc.of_nonneg_of_le (fun n => div_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    (dirichlet_term_le_at_one c hc s hs)

lemma realDirichlet_le_at_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsc : Summable (fun n => c n/n)) (s : ℝ) (hs : 1 < s) :
    0 ≤ realDirichlet c s ∧ realDirichlet c s ≤ ∑' n, c n/n := by
  refine ⟨tsum_nonneg (fun n => by exact div_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)),?_⟩
  exact (summable_dirichlet_of_at_one c hc hsc s hs).tsum_le_tsum
    (dirichlet_term_le_at_one c hc s hs) hsc

lemma abel_vanish_of_summable_at_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsc : Summable (fun n => c n/n)) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet c s) (𝓝[>] 1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ => (s-1)*(∑' n, c n/n)) (𝓝[>] 1) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds).sub_const 1).mul_const (∑' n, c n/n) using 1
    simp
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  have hb := realDirichlet_le_at_one c hc hsc s hs'
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sub_pos.mpr hs').le hb.1)]
  exact mul_le_mul_of_nonneg_left hb.2 (sub_pos.mpr hs').le

noncomputable def primeResidueCoeff {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime then residueClass a n else 0

noncomputable def nonprimeResidueCoeff {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime then 0 else residueClass a n

lemma primeResidueCoeff_nonneg {q : ℕ} (a : ZMod q) (n : ℕ) : 0 ≤ primeResidueCoeff a n := by
  unfold primeResidueCoeff
  split_ifs
  · exact residueClass_nonneg a n
  · rfl

lemma nonprimeResidueCoeff_nonneg {q : ℕ} (a : ZMod q) (n : ℕ) : 0 ≤ nonprimeResidueCoeff a n := by
  unfold nonprimeResidueCoeff
  split_ifs
  · rfl
  · exact residueClass_nonneg a n

lemma residue_realDirichlet_eq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (s : ℝ) (hs : 1 < s) :
    realDirichlet (residueClass a) s =
      (LFunctionResidueClassAux a (s : ℂ)).re + (q.totient : ℝ)⁻¹/(s-1) := by
  apply Complex.ofReal_injective
  simp only [realDirichlet,Complex.ofReal_tsum,Complex.ofReal_div,
    Complex.ofReal_cpow (Nat.cast_nonneg _),Complex.ofReal_natCast,
    Complex.ofReal_add,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hs,
    eqOn_LFunctionResidueClassAux ha (show (s : ℂ) ∈ {z | 1 < z.re} from hs), sub_add_cancel,
    LSeries,LSeries.term]
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp only [hn,residueClass_apply_zero,Complex.ofReal_zero,zero_div]
  · rfl

lemma residue_abel_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (residueClass a) s)
      (𝓝[>] 1) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hc : ContinuousOn (fun s : ℝ => (LFunctionResidueClassAux a (s : ℂ)).re) (Set.Ici 1) := by
    apply Complex.continuous_re.continuousOn.comp (t := Set.univ)
      ((continuousOn_LFunctionResidueClassAux a).comp Complex.continuous_ofReal.continuousOn ?_)
      (fun _ _ => Set.mem_univ _)
    intro s hs
    exact hs
  have haux : Tendsto (fun s : ℝ => (LFunctionResidueClassAux a (s : ℂ)).re)
      (𝓝[>] 1) (𝓝 (LFunctionResidueClassAux a (1 : ℂ)).re) :=
    (hc 1 (by simp)).mono_left (nhdsWithin_mono 1 Set.Ioi_subset_Ici_self)
  have ht := ((tendsto_id.mono_left nhdsWithin_le_nhds).sub_const 1).mul haux
  have ht' := ht.add_const ((q.totient : ℝ)⁻¹)
  simp only [sub_self,zero_mul,zero_add] at ht'
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  rw [residue_realDirichlet_eq ha s hs',mul_add]
  have hne : s-1 ≠ 0 := (sub_pos.mpr hs').ne'
  field_simp
  simp only [id_eq]
  ring

lemma residue_summable {q : ℕ} (a : ZMod q) (s : ℝ) (hs : 1 < s) :
    Summable (fun n => residueClass a n/(n : ℝ)^s) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hs))

lemma primeResidue_summable {q : ℕ} (a : ZMod q) (s : ℝ) (hs : 1 < s) :
    Summable (fun n => primeResidueCoeff a n/(n : ℝ)^s) := by
  apply (residue_summable a s hs).of_nonneg_of_le
  · intro n
    exact div_nonneg (primeResidueCoeff_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  · intro n
    unfold primeResidueCoeff
    split_ifs
    · rfl
    · simp only [zero_div]
      exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

lemma residue_split_prime_nonprime {q : ℕ} (a : ZMod q) (s : ℝ) (hs : 1 < s) :
    realDirichlet (residueClass a) s = realDirichlet (primeResidueCoeff a) s +
      realDirichlet (nonprimeResidueCoeff a) s := by
  have hnp := summable_dirichlet_of_at_one (nonprimeResidueCoeff a) (nonprimeResidueCoeff_nonneg a)
    (summable_residueClass_non_primes_div a) s hs
  rw [realDirichlet,realDirichlet,realDirichlet,← (primeResidue_summable a s hs).tsum_add hnp]
  apply tsum_congr
  intro n
  unfold primeResidueCoeff nonprimeResidueCoeff
  split_ifs <;> simp_all

/-- The pole residue is unchanged on discarding the higher prime powers. -/
theorem prime_residue_abel_limit_unit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (primeResidueCoeff a) s)
      (𝓝[>] 1) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hnp := abel_vanish_of_summable_at_one (nonprimeResidueCoeff a) (nonprimeResidueCoeff_nonneg a)
    (summable_residueClass_non_primes_div a)
  have ht := (residue_abel_limit ha).sub hnp
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [residue_split_prime_nonprime a s hs]
  ring

lemma primeResidueCoeff_eq_zero_of_gt {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : ¬IsUnit a) (n : ℕ) (hn : q < n) : primeResidueCoeff a n = 0 := by
  classical
  unfold primeResidueCoeff
  split_ifs with hp
  · by_cases he : (n : ZMod q) = a
    · have hd : n ∣ q := by
        by_contra hd
        exact ha (he ▸ (ZMod.isUnit_prime_iff_not_dvd hp).mpr hd)
      exact (hn.not_ge (Nat.le_of_dvd (NeZero.pos q) hd)).elim
    · simp [residueClass,Set.indicator_of_notMem,he]
  · rfl

/-- Nonunit prime residue classes contain only primes dividing the fixed
modulus, so their normalized Abel mass vanishes. -/
theorem prime_residue_abel_limit_nonunit {q : ℕ} [NeZero q] {a : ZMod q} (ha : ¬IsUnit a) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (primeResidueCoeff a) s) (𝓝[>] 1) (𝓝 0) := by
  apply abel_vanish_of_summable_at_one _ (primeResidueCoeff_nonneg a)
  apply summable_of_ne_finset_zero (s := range (q+1))
  intro n hn
  rw [primeResidueCoeff_eq_zero_of_gt ha n (by simp only [mem_range] at hn; omega),zero_div]

/-- Abel-weighted prime density in every residue class of a fixed modulus. -/
theorem prime_residue_abel_limit (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto (fun s : ℝ => (s-1)*realDirichlet (primeResidueCoeff a) s)
      (𝓝[>] 1) (𝓝 (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)) := by
  classical
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    exact prime_residue_abel_limit_unit ha
  · rw [if_neg ha]
    exact prime_residue_abel_limit_nonunit ha

#print axioms prime_residue_abel_limit
end Erdos371.AbelPrimes
