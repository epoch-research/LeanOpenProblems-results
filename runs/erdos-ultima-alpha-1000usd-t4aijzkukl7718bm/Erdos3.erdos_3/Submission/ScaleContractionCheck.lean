import Submission.Reduction

/-! A precise scale-contraction route to the extremal-series criterion.
The contraction estimate is a hypothesis, not an established AP bound. -/

namespace Erdos3ScaleContractionCheck

open Filter
open scoped Topology
set_option maxHeartbeats 1000000

lemma geometric_scale_diff (N C j : ℕ) :
    N * C ^ (j + 1) - N * C ^ j = N * C ^ j * (C - 1) := by
  simp only [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_assoc]

/-- A multiplicative-scale contraction strong enough to overcome the number
of indices between consecutive scales implies summability. -/
theorem summable_of_scale_contraction {f : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ f n) (hmono : Antitone f)
    {C N : ℕ} (hC : 1 < C) (hN : 0 < N) {q : ℝ}
    (hq : 0 ≤ q) (hCq : (C : ℝ) * q < 1)
    (hstep : ∀ n ≥ N, f (C * n) ≤ q * f n) : Summable f := by
  let u : ℕ → ℕ := fun j ↦ N * C ^ j
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hu_pos (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hu_mono : StrictMono u := by
    apply strictMono_nat_of_lt_succ
    intro j
    dsimp [u]
    rw [pow_succ]
    have hp : 0 < C ^ j := by positivity
    have hpc : C ^ j < C ^ j * C := by nlinarith
    exact Nat.mul_lt_mul_of_pos_left hpc hN
  have hdiff : SuccDiffBounded C u := by
    intro j
    dsimp [u]
    rw [geometric_scale_diff, geometric_scale_diff, pow_succ]
    change N * (C ^ j * C) * (C - 1) ≤ C * (N * C ^ j * (C - 1))
    exact le_of_eq (by ring)
  have hNu (j : ℕ) : N ≤ u j := by
    dsimp [u]
    simpa using Nat.mul_le_mul_left N (one_le_pow₀ (by omega : 1 ≤ C) (n := j))
  have hbound (j : ℕ) : f (u j) ≤ q ^ j * f N := by
    induction j with
    | zero => simp [u]
    | succ j ih =>
      have he : u (j + 1) = C * u j := by dsimp [u]; rw [pow_succ]; ring
      rw [he]
      calc
        _ ≤ q * f (u j) := hstep _ (hNu j)
        _ ≤ q * (q ^ j * f N) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (j + 1) * f N := by rw [pow_succ']; ring
  have hgeom : Summable (fun j : ℕ ↦
      ((N : ℝ) * ((C : ℝ) - 1) * f N) * ((C : ℝ) * q) ^ j) :=
    (summable_geometric_of_lt_one (mul_nonneg hCpos.le hq) hCq).mul_left _
  have hcondensed : Summable (fun j : ℕ ↦
      ((u (j + 1) : ℝ) - (u j : ℝ)) * f (u j)) := by
    apply hgeom.of_nonneg_of_le
    · intro j
      apply mul_nonneg _ (hnonneg _)
      exact sub_nonneg.mpr (by exact_mod_cast (hu_mono (Nat.lt_succ_self j)).le)
    · intro j
      have hcoef : (u (j + 1) : ℝ) - (u j : ℝ) =
          (N : ℝ) * (C : ℝ) ^ j * ((C : ℝ) - 1) := by
        dsimp [u]
        push_cast
        rw [pow_succ]
        ring
      rw [hcoef]
      calc
        _ ≤ ((N : ℝ) * (C : ℝ) ^ j * ((C : ℝ) - 1)) * (q ^ j * f N) := by
          apply mul_le_mul_of_nonneg_left (hbound j)
          have : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (sub_nonneg.mpr this)
        _ = _ := by rw [mul_pow]; ring
  exact (summable_schlomilch_iff_of_nonneg hnonneg (fun {_ _} _ h ↦ hmono h)
    hu_pos hu_mono (by omega : C ≠ 0) hdiff).mp hcondensed

/-- Quadratic contraction is sufficient once the initial density is small enough.
No asymptotic density theorem is required for this version. -/
theorem summable_of_quadratic_scale_contraction {f : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ f n) (hmono : Antitone f)
    {C N : ℕ} (hC : 1 < C) (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K)
    (hsmall : (C : ℝ) * (K * f N) < 1)
    (hstep : ∀ n ≥ N, f (C * n) ≤ K * (f n) ^ 2) : Summable f := by
  apply summable_of_scale_contraction hnonneg hmono hC hN
    (mul_nonneg hK (hnonneg N)) hsmall
  intro n hn
  calc
    f (C * n) ≤ K * (f n) ^ 2 := hstep n hn
    _ ≤ (K * f N) * f n := by
      have := mul_le_mul_of_nonneg_left (hmono hn) hK
      have := mul_le_mul_of_nonneg_right this (hnonneg n)
      nlinarith

/-- In particular, qualitative decay to zero plus a fixed quadratic power-scale
contraction would suffice. The latter is the substantive extra hypothesis. -/
theorem summable_of_eventual_quadratic_scale_contraction {f : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ f n) (hmono : Antitone f)
    (hlim : Tendsto f atTop (nhds 0)) {C : ℕ} (hC : 1 < C)
    {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ᶠ n in atTop, f (C * n) ≤ K * (f n) ^ 2) : Summable f := by
  have hsmall : ∀ᶠ n in atTop, (C : ℝ) * (K * f n) < 1 := by
    have ht := (hlim.const_mul K).const_mul (C : ℝ)
    simp only [mul_zero] at ht
    exact ht.eventually_lt_const zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hstep.and hsmall)
  let M := max N 1
  have hNM : N ≤ M := le_max_left _ _
  apply summable_of_quadratic_scale_contraction hnonneg hmono hC
    (by dsimp [M]; omega : 0 < M) hK (hN M hNM).2
  intro n hn
  exact (hN n (hNM.trans hn)).1

noncomputable def extremalDensity (k j : ℕ) : ℝ :=
  (Set.IsAPOfLengthFree.maxCard k (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)

/-- A fully explicit sufficient estimate for the original conjecture.
This theorem does not assert that its contraction hypothesis holds. -/
theorem conjecture_of_quadratic_scale_contraction
    (h : ∀ k : ℕ, 3 ≤ k → ∃ C N : ℕ, ∃ K : ℝ,
      1 < C ∧ 0 < N ∧ 0 ≤ K ∧ (C : ℝ) * (K * extremalDensity k N) < 1 ∧
      ∀ n ≥ N, extremalDensity k (C * n) ≤ K * (extremalDensity k n) ^ 2) :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Erdos3Reduction.conjecture_iff_extremal_series.mpr
  intro k hk
  obtain ⟨C, N, K, hC, hN, hK, hsmall, hstep⟩ := h k hk
  exact summable_of_quadratic_scale_contraction (f := extremalDensity k)
    (fun _ ↦ by dsimp [extremalDensity]; positivity)
    (Erdos3Reduction.extremal_density_antitone (by omega)) hC hN hK hsmall hstep

#print axioms summable_of_scale_contraction
#print axioms summable_of_eventual_quadratic_scale_contraction
#print axioms conjecture_of_quadratic_scale_contraction

lemma threeAPFree_iff_free_three (A : Set ℕ) :
    ThreeAPFree A ↔ A.IsAPOfLengthFree (3 : ℕ) := by
  rw [Erdos3Reduction.free_iff_not_hasNatAP (by norm_num : 2 ≤ 3)]
  constructor
  · intro h
    rintro ⟨a, d, hd, hmem⟩
    have ha := hmem 0 (by norm_num)
    have hb := hmem 1 (by norm_num)
    have hc := hmem 2 (by norm_num)
    simp only [zero_mul, add_zero, one_mul] at ha hb
    have := h ha hb hc (by ring)
    omega
  · intro h a ha b hb c hc heq
    by_contra hne
    have hmake {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
        (hxy : x < y) (he : x + z = y + y) : Erdos3Reduction.HasNatAP A 3 := by
      refine ⟨x, y - x, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa using hx
      · have : x + 1 * (y - x) = y := by omega
        simpa only [this] using hy
      · have : x + 2 * (y - x) = z := by omega
        simpa only [this] using hz
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h (hmake ha hb hc hlt heq)
    · exact h (hmake hc hb ha (by omega) (by omega))

lemma maxCard_three_eq_roth (N : ℕ) : Set.IsAPOfLengthFree.maxCard 3 N = rothNumberNat N := by
  classical
  have he : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hroth : addRothNumber (Finset.Icc 1 N) = rothNumberNat N := by
    rw [he, addRothNumber_Ico]
    simp
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hf, hc⟩ := Erdos3Reduction.maxCard_spec (N := N) (by norm_num : 2 ≤ 3)
    rw [← hc, ← hroth]
    exact ((threeAPFree_iff_free_three _).mpr hf).le_addRothNumber hS
  · obtain ⟨S, hS, hc, hf⟩ := addRothNumber_spec (Finset.Icc 1 N)
    rw [← hroth, ← hc]
    exact Erdos3Reduction.card_le_maxCard hS ((threeAPFree_iff_free_three _).mp hf)

noncomputable def rothDensity (n : ℕ) : ℝ :=
  (rothNumberNat (4 ^ n) : ℝ) / ((4 ^ n : ℕ) : ℝ)

lemma rothDensity_lower_bound (n : ℕ) :
    Real.exp (-4 * Real.sqrt ((n : ℝ) * Real.log 4)) ≤ rothDensity n := by
  have hb := Behrend.roth_lower_bound (N := 4 ^ n)
  dsimp [rothDensity]
  apply (le_div_iff₀ (by positivity)).mpr
  have he : Real.log ((4 ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
    push_cast
    rw [Real.log_pow]
  simpa only [he, mul_comm] using hb

/-- Behrend's lower bound rules out quadratic contraction when the scale exponent
is strictly below 4, even allowing any fixed loss and discarding an initial segment. -/
theorem no_quadratic_roth_contraction_below_four {C : ℕ} (hC : 1 < C) (hC4 : C < 4) :
    ¬ (∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      rothDensity (C * n) ≤ K * (rothDensity n) ^ 2) := by
  rintro ⟨K, N, hstep⟩
  let q : ℝ := max K 1
  have hq1 : 1 ≤ q := le_max_right _ _
  have hq : 0 < q := zero_lt_one.trans_le hq1
  have hKq : K ≤ q := le_max_left _ _
  let F : ℕ → ℝ := fun n ↦ q * rothDensity n
  have hFnonneg (n : ℕ) : 0 ≤ F n := by dsimp [F, rothDensity]; positivity
  have hFstep (n : ℕ) (hn : N ≤ n) : F (C * n) ≤ (F n) ^ 2 := by
    calc
      F (C * n) ≤ q * (K * (rothDensity n) ^ 2) :=
        mul_le_mul_of_nonneg_left (hstep n hn) hq.le
      _ ≤ q * (q * (rothDensity n) ^ 2) := by gcongr
      _ = (F n) ^ 2 := by dsimp [F]; ring
  have hlower (n : ℕ) :
      Real.exp (-4 * Real.sqrt ((n : ℝ) * Real.log 4)) ≤ F n := by
    apply (rothDensity_lower_bound n).trans
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq1 (show 0 ≤ rothDensity n by dsimp [rothDensity]; positivity)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (rothNumberNat_isLittleO_id.bound (show (0 : ℝ) < 1 / (2 * q) by positivity))
  let m := max N (max M 1)
  have hmN : N ≤ m := le_max_left _ _
  have hmM : M ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm1 : 1 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm4 : m ≤ 4 ^ m :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) m)
  have hFmpos : 0 < F m := (Real.exp_pos _).trans_le (hlower m)
  have hFmhalf : F m ≤ 1 / 2 := by
    have hb := hM (4 ^ m) (hmM.trans hm4)
    simp only [Real.norm_natCast] at hb
    have hrho : rothDensity m ≤ 1 / (2 * q) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ))).mpr
      exact hb
    calc
      F m ≤ q * (1 / (2 * q)) := mul_le_mul_of_nonneg_left hrho hq.le
      _ = 1 / 2 := by field_simp
  have hFmlt : F m < 1 := hFmhalf.trans_lt (by norm_num)
  let d : ℝ := -Real.log (F m)
  have hd : 0 < d := neg_pos.mpr (Real.log_neg hFmpos hFmlt)
  have hbound (j : ℕ) : F (m * C ^ j) ≤ (F m) ^ (2 ^ j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hnm : N ≤ m * C ^ j := hmN.trans (by
        simpa using Nat.mul_le_mul_left m (one_le_pow₀ (by omega : 1 ≤ C) (n := j)))
      calc
        F (m * C ^ (j + 1)) = F (C * (m * C ^ j)) := by rw [pow_succ]; congr 1; ring
        _ ≤ (F (m * C ^ j)) ^ 2 := hFstep _ hnm
        _ ≤ ((F m) ^ (2 ^ j)) ^ 2 := pow_le_pow_left₀ (hFnonneg _) ih 2
        _ = (F m) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hratio : (1 : ℝ) < 4 / (C : ℝ) := by
    apply (lt_div_iff₀ hCpos).mpr
    have : (C : ℝ) < 4 := by exact_mod_cast hC4
    simpa using this
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (16 * (m : ℝ) * Real.log 4 / d ^ 2) hratio
  rw [div_pow] at hj
  have hj' : 16 * (m : ℝ) * Real.log 4 * (C : ℝ) ^ j < (4 : ℝ) ^ j * d ^ 2 :=
    (div_lt_div_iff₀ (sq_pos_of_pos hd) (by positivity)).mp hj
  have he := (hlower (m * C ^ j)).trans (hbound j)
  have hlog := Real.log_le_log (by positivity) he
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hineq : (2 : ℝ) ^ j * d ≤
      4 * Real.sqrt ((m : ℝ) * (C : ℝ) ^ j * Real.log 4) := by
    dsimp [d]
    linarith
  have hsqrt := Real.sq_sqrt
    (show 0 ≤ (m : ℝ) * (C : ℝ) ^ j * Real.log 4 by positivity)
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ) ^ j * d)
    (by positivity : 0 ≤ 4 * Real.sqrt ((m : ℝ) * (C : ℝ) ^ j * Real.log 4))).mpr hineq
  have htwo : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  rw [mul_pow, htwo] at hsq
  nlinarith

/-- The same obstruction applies to the precise extremal density used in the
conjecture reduction; interval translation identifies it with the Roth number. -/
theorem no_quadratic_extremal_contraction_below_four {C : ℕ} (hC : 1 < C) (hC4 : C < 4) :
    ¬ (∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      extremalDensity 3 (C * n) ≤ K * (extremalDensity 3 n) ^ 2) := by
  simpa only [extremalDensity, maxCard_three_eq_roth, rothDensity] using
    no_quadratic_roth_contraction_below_four hC hC4

#print axioms maxCard_three_eq_roth
#print axioms no_quadratic_roth_contraction_below_four
#print axioms no_quadratic_extremal_contraction_below_four

noncomputable def inverseSquare (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ) ^ 2

lemma inverseSquare_summable : Summable inverseSquare :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

lemma inverseSquare_antitone : Antitone inverseSquare := by
  intro m n hmn
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hmn 1) 2

lemma inverseSquare_no_quadratic_contraction (C : ℕ) :
    ¬ (∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      inverseSquare (C * n) ≤ K * (inverseSquare n) ^ 2) := by
  rintro ⟨K, N, h⟩
  let q : ℝ := max K 1
  have hq : 0 < q := zero_lt_one.trans_le (le_max_right _ _)
  have hKq : K ≤ q := le_max_left _ _
  obtain ⟨j, hj⟩ := exists_nat_gt (q * ((C : ℝ) + 1) ^ 2)
  let n := max N j
  have hnN : N ≤ n := le_max_left _ _
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast (le_max_right N j)
  have hlarge : q * ((C : ℝ) + 1) ^ 2 < n := hj.trans_le hjn
  let x : ℝ := (n : ℝ) + 1
  let y : ℝ := (C : ℝ) * n + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hh : 1 / y ^ 2 ≤ q * (1 / x ^ 2) ^ 2 := by
    have hh' := (h n hnN).trans (mul_le_mul_of_nonneg_right hKq (sq_nonneg (inverseSquare n)))
    simpa only [inverseSquare, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hh'
  rw [div_pow, one_pow, mul_one_div] at hh
  have hh' : (x ^ 2) ^ 2 ≤ q * y ^ 2 := by
    simpa only [one_mul] using (div_le_div_iff₀ (sq_pos_of_pos hy)
      (sq_pos_of_pos (sq_pos_of_pos hx))).mp hh
  have hxy : y ≤ ((C : ℝ) + 1) * x := by
    dsimp [x, y]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hb := pow_le_pow_left₀ hy.le hxy 2
  have hsmall : x ^ 2 ≤ q * ((C : ℝ) + 1) ^ 2 := by
    apply le_of_mul_le_mul_right (a := x ^ 2) _ (sq_pos_of_pos hx)
    calc
      x ^ 2 * x ^ 2 = (x ^ 2) ^ 2 := by ring
      _ ≤ q * y ^ 2 := hh'
      _ ≤ q * (((C : ℝ) + 1) * x) ^ 2 := mul_le_mul_of_nonneg_left hb hq.le
      _ = (q * ((C : ℝ) + 1) ^ 2) * x ^ 2 := by ring
  dsimp [x] at hsmall
  nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

/-- Quadratic power-scale contraction is genuinely stronger than summability,
even for positive decreasing sequences tending to zero. Consequently the
conditional route above cannot be inferred from summability by analysis alone. -/
theorem summability_does_not_imply_quadratic_contraction :
    ∃ f : ℕ → ℝ, (∀ n, 0 < f n) ∧ Antitone f ∧ Summable f ∧
      Tendsto f atTop (nhds 0) ∧
      ¬ (∃ C : ℕ, ∃ K : ℝ, ∃ N : ℕ, 1 < C ∧
        ∀ n ≥ N, f (C * n) ≤ K * (f n) ^ 2) := by
  refine ⟨inverseSquare, (fun n ↦ by dsimp [inverseSquare]; positivity),
    inverseSquare_antitone, inverseSquare_summable,
    inverseSquare_summable.tendsto_atTop_zero, ?_⟩
  rintro ⟨C, K, N, _, h⟩
  exact inverseSquare_no_quadratic_contraction C ⟨K, N, h⟩

#print axioms summability_does_not_imply_quadratic_contraction

end Erdos3ScaleContractionCheck
