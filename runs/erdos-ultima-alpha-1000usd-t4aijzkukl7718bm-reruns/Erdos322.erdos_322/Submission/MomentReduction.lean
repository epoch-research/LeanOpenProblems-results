import Submission.Spec
import Submission.GrowthReduction
import Submission.QuarticFullUpperBound

/-!
A full-count moment reformulation of Erdős Problem 322.
These equivalences do not establish the required moment estimates.
-/

namespace Erdos322.MomentReduction

noncomputable section

/-- Positive-index integer moments of a counting sequence. -/
def countMoment (r : ℕ → ℕ) (q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (r n : ℝ)^q

/-- Uniform domination by every positive power. -/
def Subpolynomial (r : ℕ → ℕ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
    (r n : ℝ) ≤ C * (n : ℝ)^ε

/-- Every fixed positive integer moment has at most quadratic summatory growth.
The constant may depend on the moment order. -/
def QuadraticMoments (r : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
    countMoment r q N ≤ C * (N : ℝ)^2

theorem subpolynomial_iff_quadratic_moments (r : ℕ → ℕ) :
    Subpolynomial r ↔ QuadraticMoments r := by
  constructor
  · intro h q hq
    have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    obtain ⟨A, hA, hbound⟩ := h (1/(q : ℝ)) (by positivity)
    refine ⟨A^q, pow_pos hA _, ?_⟩
    intro N hN
    have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : (r n : ℝ)^q ≤ A^q * N := by
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r n) (hbound n hn1) q
      rw [mul_pow] at hp
      have hroot : ((n : ℝ)^(1/(q : ℝ)))^q = n := by
        simpa only [one_div] using Real.rpow_inv_natCast_pow
          (by positivity : (0 : ℝ) ≤ n) (by omega : q ≠ 0)
      rw [hroot] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (by positivity))
    calc
      countMoment r q N ≤ ∑ _n ∈ Finset.Icc 1 N, A^q * (N : ℝ) :=
        Finset.sum_le_sum hterm
      _ = A^q * (N : ℝ)^2 := by simp [Nat.card_Icc]; ring
  · intro h ε hε
    obtain ⟨q, hq⟩ := exists_nat_gt (2/ε)
    have hqr : (0 : ℝ) < q := (div_pos (by norm_num) hε).trans hq
    have hqnat : 1 ≤ q := by
      have hqpos : 0 < q := by exact_mod_cast hqr
      omega
    have hexp : (2 : ℝ) ≤ ε * q := by
      have ht := (div_lt_iff₀ hε).mp hq
      nlinarith
    obtain ⟨A, hA, hbound⟩ := h q hqnat
    let C := max 1 A
    have hC1 : 1 ≤ C := le_max_left _ _
    have hCA : A ≤ C := le_max_right _ _
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hsingle : (r n : ℝ)^q ≤ countMoment r q n :=
      Finset.single_le_sum (f := fun j : ℕ => (r j : ℝ)^q)
        (fun _ _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    have hCq : A ≤ C^q := hCA.trans (le_self_pow₀ hC1 (by omega))
    have hnpow : (n : ℝ)^2 ≤ ((n : ℝ)^ε)^q := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      exact (Real.rpow_natCast (n : ℝ) 2).symm.le.trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp)
    apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ r n)
      (by positivity : 0 ≤ C*(n : ℝ)^ε) (by omega : q ≠ 0)).mp
    calc
      (r n : ℝ)^q ≤ A * (n : ℝ)^2 := hsingle.trans (hbound n hn)
      _ ≤ C^q * ((n : ℝ)^ε)^q := mul_le_mul hCq hnpow (by positivity) (by positivity)
      _ = (C * (n : ℝ)^ε)^q := (mul_pow _ _ _).symm

/-- The exact negation of the original conjecture is equivalent to a bound on
all integer moments for one exponent at least four. No such bound is assumed. -/
theorem negation_iff_quadratic_moments :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite)) ↔
      ∃ k : ℕ, 4 ≤ k ∧ QuadraticMoments (representationCount k) := by
  classical
  constructor
  · intro h
    have hex : ∃ k : ℕ, 3 ≤ k ∧ ¬ ∃ c > (0 : ℝ),
        {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite := by
      simpa only [not_forall, exists_prop] using h
    obtain ⟨k, hk, hnot⟩ := hex
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have he : k = 3 := by omega
      subst k
      exact hnot cubic_case
    refine ⟨k, hk4, (subpolynomial_iff_quadratic_moments _).mp ?_⟩
    exact (Erdos322Research.no_polynomial_peaks_iff_uniform_bound _).mp hnot
  · rintro ⟨k, hk, hm⟩ h
    have hnot := (Erdos322Research.no_polynomial_peaks_iff_uniform_bound
      (representationCount k)).mpr ((subpolynomial_iff_quadratic_moments _).mpr hm)
    exact hnot (h k (by omega))


theorem single_le_countMoment (r : ℕ → ℕ) (q n : ℕ) (hn : 1 ≤ n) :
    (r n : ℝ)^q ≤ countMoment r q n := by
  exact Finset.single_le_sum (f := fun j : ℕ => (r j : ℝ)^q)
    (fun _ _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- The cubic construction necessarily violates the moment criterion. -/
theorem cubic_twenty_fifth_moment_not_quadratic :
    ¬ (∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 3) 25 N ≤ C*(N : ℝ)^2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 C)
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := lt_trans (by positivity : (0 : ℝ) < max 1 C) hm
    exact_mod_cast this
  have hC3 : C < 3*(m : ℝ) := by
    have hCm : C < m := (le_max_right _ _).trans_lt hm
    have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
    linarith
  have hn : 1 ≤ (3*m)^12 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcount : (3*(m : ℝ)) ≤ representationCount 3 ((3*m)^12) := by
    have hc := cubic_count_lower_strong m hmpos
    exact_mod_cast (show 3*m ≤ representationCount 3 ((3*m)^12) by omega)
  have hlow : (3*(m : ℝ))^25 ≤ countMoment (representationCount 3) 25 ((3*m)^12) :=
    (pow_le_pow_left₀ (by positivity) hcount 25).trans
      (single_le_countMoment _ 25 _ hn)
  have hup := hbound ((3*m)^12) hn
  have hnorm : (((3*m)^12 : ℕ) : ℝ)^2 = (3*(m : ℝ))^24 := by push_cast; ring
  rw [hnorm] at hup
  have hstrict : C*(3*(m : ℝ))^24 < (3*(m : ℝ))^25 := by
    calc
      C*(3*(m : ℝ))^24 < (3*(m : ℝ))*(3*(m : ℝ))^24 :=
        mul_lt_mul_of_pos_right hC3 (by positivity)
      _ = (3*(m : ℝ))^25 := by ring
  exact not_lt_of_ge (hlow.trans hup) hstrict

/-- A block of distinct cubic construction targets gives a lower bound for
all positive-index moments. -/
theorem cubic_moment_block_lower (q m : ℕ) (hm : 0 < m) :
    (m : ℝ) * (3 * (m : ℝ))^q ≤
      countMoment (representationCount 3) q ((6*m)^12) := by
  classical
  let f : ℕ → ℕ := fun i => (3*(m+i+1))^12
  have hf : Function.Injective f := by
    intro i j hij
    have he := Nat.pow_left_injective (by decide : 12 ≠ 0) hij
    omega
  have hsub : (Finset.range m).image f ⊆ Finset.Icc 1 ((6*m)^12) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have him : i < m := Finset.mem_range.mp hi
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by dsimp [f]; positivity)
    · exact Nat.pow_le_pow_left (by omega : 3*(m+i+1) ≤ 6*m) 12
  have hlower (i : ℕ) : 3*m ≤ representationCount 3 (f i) := by
    have hc := cubic_count_lower_strong (m+i+1) (by omega)
    dsimp [f]
    omega
  calc
    (m : ℝ) * (3*(m : ℝ))^q = ∑ _i ∈ Finset.range m, (3*(m : ℝ))^q := by simp
    _ ≤ ∑ i ∈ Finset.range m, (representationCount 3 (f i) : ℝ)^q := by
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hlower i
    _ = ∑ n ∈ (Finset.range m).image f, (representationCount 3 n : ℝ)^q := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => hf hij
    _ ≤ countMoment (representationCount 3) q ((6*m)^12) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

/-- Summing many cubic peaks strengthens the single-peak obstruction:
already the twenty-fourth moment cannot have quadratic summatory growth. -/
theorem cubic_twenty_fourth_moment_not_quadratic :
    ¬ (∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 3) 24 N ≤ C*(N : ℝ)^2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (C * 2^24))
  have hmpos : 0 < m := by
    have hmr : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one
      ((le_max_left _ _).trans hm.le)
    exact_mod_cast hmr
  have hCm : C * 2^24 < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hn : 1 ≤ (6*m)^12 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlow := cubic_moment_block_lower 24 m hmpos
  have hup := hbound ((6*m)^12) hn
  have hnorm : (((6*m)^12 : ℕ) : ℝ)^2 = (6*(m : ℝ))^24 := by
    push_cast
    ring
  rw [hnorm] at hup
  have hstrict : C*(6*(m : ℝ))^24 < (m : ℝ)*(3*(m : ℝ))^24 := by
    calc
      C*(6*(m : ℝ))^24 = (C*2^24)*(3*(m : ℝ))^24 := by ring
      _ < (m : ℝ)*(3*(m : ℝ))^24 :=
        mul_lt_mul_of_pos_right hCm (by positivity)
  exact not_lt_of_ge (hlow.trans hup) hstrict

private abbrev Rep (k n : ℕ) :=
  {a : Fin k → Fin (n+1) // ∑ i, (a i : ℕ)^k = n}

private theorem rep_card (k n : ℕ) :
    Fintype.card (Rep k n) = representationCount k n := by
  simp [Rep, Fintype.card_subtype, representationCount]

private def rootBoxMap (k N : ℕ) (hk : k ≠ 0)
    (v : (n : Fin (N+1)) × Rep k n) : Fin k → Fin (k.nthRoot N+1) :=
  fun i => ⟨v.2.1 i, by
    have hi : (v.2.1 i : ℕ)^k ≤ v.1 :=
      (Finset.single_le_sum (f := fun j : Fin k => (v.2.1 j : ℕ)^k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq v.2.2
    have hn : (v.1 : ℕ) ≤ N := Nat.le_of_lt_succ v.1.isLt
    exact Nat.lt_succ_of_le ((Nat.le_nthRoot_iff hk).mpr (hi.trans hn))⟩

private theorem rootBoxMap_injective (k N : ℕ) (hk : k ≠ 0) :
    Function.Injective (rootBoxMap k N hk) := by
  rintro ⟨n,a⟩ ⟨m,b⟩ he
  have hvals : ∀ i, (a.1 i : ℕ) = b.1 i := by
    intro i
    exact congrArg Fin.val (congrFun he i)
  have hnm : n = m := by
    apply Fin.ext
    calc
      (n : ℕ) = ∑ i, (a.1 i : ℕ)^k := a.2.symm
      _ = ∑ i, (b.1 i : ℕ)^k := by simp only [hvals]
      _ = m := b.2
  subst m
  congr 1
  apply Subtype.ext
  funext i
  exact Fin.ext (hvals i)

/-- The total number of representations up to `N` fits in the integer root box. -/
theorem summatory_count_le_root_box (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range (N+1), representationCount k n ≤ (k.nthRoot N+1)^k := by
  classical
  have hc := Fintype.card_le_of_injective (rootBoxMap k N hk.ne')
    (rootBoxMap_injective k N hk.ne')
  simpa only [Fintype.card_sigma, rep_card, Fintype.card_fun, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using hc

/-- A uniform linear first-moment estimate for the full count, at every exponent. -/
theorem first_moment_linear (k N : ℕ) (hk : 0 < k) (hN : 1 ≤ N) :
    countMoment (representationCount k) 1 N ≤ (2 : ℝ)^k*N := by
  have hroot : 1 ≤ k.nthRoot N := (Nat.le_nthRoot_iff hk.ne').mpr (by simpa using hN)
  have hbox : (k.nthRoot N+1)^k ≤ 2^k*N := by
    calc
      (k.nthRoot N+1)^k ≤ (2*k.nthRoot N)^k := Nat.pow_le_pow_left (by omega) k
      _ = 2^k*(k.nthRoot N)^k := Nat.mul_pow _ _ _
      _ ≤ 2^k*N := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (.inl hk.ne'))
  have hsub : ∑ n ∈ Finset.Icc 1 N, representationCount k n ≤
      ∑ n ∈ Finset.range (N+1), representationCount k n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intros; exact Nat.zero_le _
  have hb := hsub.trans ((summatory_count_le_root_box k N hk).trans hbox)
  simpa only [countMoment, pow_one, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using (show ((∑ n ∈ Finset.Icc 1 N, representationCount k n : ℕ) : ℝ) ≤
      ((2^k*N : ℕ) : ℝ) by exact_mod_cast hb)


/-- Combining the full quartic upper bound with its linear first moment gives
bounds on every fixed moment, but with an exponent growing with the order. -/
theorem quartic_moment_upper (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) (q+1) N ≤
        C*(N : ℝ)^(1+(q : ℝ)/2+ε) := by
  let δ : ℝ := ε/((q : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hbound⟩ := Erdos322Research.quartic_count_upper_half δ hδ
  have hδq : δ*(q : ℝ) ≤ ε := by
    have hpos : (0 : ℝ) < (q : ℝ)+1 := by positivity
    have hcancel : δ*((q : ℝ)+1) = ε := div_mul_cancel₀ ε hpos.ne'
    have : 0 ≤ δ := hδ.le
    nlinarith
  refine ⟨16*A^q, by positivity, ?_⟩
  intro N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  let K : ℝ := (A*(N : ℝ)^(1/2+δ))^q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (representationCount 4 n : ℝ)^(q+1) ≤ K*(representationCount 4 n : ℝ) := by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hb : (representationCount 4 n : ℝ) ≤ A*(N : ℝ)^(1/2+δ) := by
      exact (hbound n (by omega)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) (by positivity)) hA.le)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hb q) (by positivity)
  have hsum : countMoment (representationCount 4) (q+1) N ≤
      K*countMoment (representationCount 4) 1 N := by
    unfold countMoment
    simp only [pow_one]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum ht
  have hfirst : countMoment (representationCount 4) 1 N ≤ 16*(N : ℝ) := by
    have hf := first_moment_linear 4 N (by decide) hN
    norm_num at hf
    exact hf
  have halg : K*(16*(N : ℝ)) =
      (16*A^q)*(N : ℝ)^((1/2+δ)*(q : ℝ)+1) := by
    dsimp [K]
    rw [mul_pow, ← Real.rpow_mul_natCast hNpos.le, Real.rpow_add_one hNpos.ne']
    ring
  have hexp : (1/2+δ)*(q : ℝ)+1 ≤ 1+(q : ℝ)/2+ε := by nlinarith
  calc
    countMoment (representationCount 4) (q+1) N ≤ K*(16*(N : ℝ)) :=
      hsum.trans (mul_le_mul_of_nonneg_left hfirst hK)
    _ = (16*A^q)*(N : ℝ)^((1/2+δ)*(q : ℝ)+1) := halg
    _ ≤ (16*A^q)*(N : ℝ)^(1+(q : ℝ)/2+ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNr hexp) (by positivity)

/-- The second moment meets the quadratic criterion. The higher moments needed
for the full criterion are not supplied by this theorem. -/
theorem quartic_second_moment_quadratic :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 2 N ≤ C*(N : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := quartic_moment_upper 1 (1/2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hb := hbound N hN
  norm_num at hb
  exact hb

/-- At order three the available estimate is only `N^(2+ε)`. -/
theorem quartic_third_moment_near_quadratic (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 3 N ≤ C*(N : ℝ)^(2+ε) := by
  convert quartic_moment_upper 2 ε hε using 1
  norm_num

end

end Erdos322.MomentReduction
