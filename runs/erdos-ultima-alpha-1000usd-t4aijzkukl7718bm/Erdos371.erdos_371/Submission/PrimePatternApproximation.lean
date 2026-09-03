import Submission.PrimePatternReflection

/-! A polynomial-size error for moving prime configurations. The full CRT
period is absent from the bound; only finitely many inclusion degrees enter. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma prime_pattern_rounding_moment (P : Finset ℕ) (N L : ℕ) (Z : ℝ)
    (hZ : 1 ≤ Z) (hsum : (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) ≤ Z) :
    (∑ T ∈ (primeAtoms P).powersetCard L, (∏ a ∈ T, (a.1 : ℝ))/N) ≤ Z^L/N := by
  have hsum' : (∑ a ∈ primeAtoms P, (a.1 : ℝ)) ≤ Z := by
    have hnon : 0 ≤ ∑ a ∈ primeAtoms P, (a.1 : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
    rw [← mul_sum] at hsum
    linarith
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ (∑ a ∈ primeAtoms P, (a.1 : ℝ))^L/L.factorial :=
      elementarySum_le_pow_div_factorial _ _ (fun _ _ => Nat.cast_nonneg _) L
    _ ≤ (∑ a ∈ primeAtoms P, (a.1 : ℝ))^L := div_le_self (by positivity)
      (by exact_mod_cast Nat.factorial_pos L)
    _ ≤ Z^L := pow_le_pow_left₀ (by positivity) hsum' L

lemma prime_pattern_rounding_polynomial (P : Finset ℕ) (N L : ℕ) (Z : ℝ)
    (hZ : 1 ≤ Z) (hsum : (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) ≤ Z) :
    (∑ T ∈ (primeAtoms P).powerset, if T.card < L then
      (2 : ℝ)^T.card*((∏ a ∈ T, (a.1 : ℝ))/N) else 0) ≤ (L+1)*Z^L/N := by
  have he (T : Finset PrimeAtom) : (2 : ℝ)^T.card*(∏ a ∈ T, (a.1 : ℝ)) =
      ∏ a ∈ T, 2*(a.1 : ℝ) := by simp only [prod_mul_distrib,prod_const]
  calc
    _ = (∑ T ∈ (primeAtoms P).powerset, if T.card < L then ∏ a ∈ T, 2*(a.1 : ℝ) else 0)/N := by
      rw [sum_div]
      apply sum_congr rfl
      intro T _
      split_ifs
      · rw [← mul_div_assoc,he]
      · simp only [zero_div]
    _ ≤ (∑ T ∈ (primeAtoms P).powerset, if T.card ≤ L then ∏ a ∈ T, 2*(a.1 : ℝ) else 0)/N := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      apply sum_le_sum
      intro T _
      split_ifs <;> try omega
      · rfl
      · positivity
      · rfl
    _ ≤ _ := div_le_div_of_nonneg_right
      (truncated_subset_product_sum_le (primeAtoms P) (fun a => 2*(a.1 : ℝ)) L
        (fun _ _ => by positivity) Z hZ hsum) (Nat.cast_nonneg N)

/-- Uniform over every bounded observable odd under a prime-preserving
permutation. The error is controlled by a fixed-degree polynomial in Z. -/
theorem prime_pattern_odd_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (hN : 0 < N) (L : ℕ) (Z : ℝ) (hZ : 1 ≤ Z)
    (hsum : (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) ≤ Z)
    (e : PrimeAtom ≃ PrimeAtom) (he : ∀ a, (e a).1=a.1)
    (heP : (primeAtoms P).map e.toEmbedding = primeAtoms P)
    (F : Finset PrimeAtom → ℝ) (hF : ∀ T ⊆ primeAtoms P, |F T| ≤ 1)
    (hodd : ∀ T, F (T.map e.toEmbedding) = -F T) :
    |(∑ n ∈ range N, F (activePrimeAtoms P n))/N| ≤
      (1+3^L)*(2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial +
        (1+3^L+(L+1))*Z^L/N := by
  have h := prime_pattern_comparison P hP N hN L F hF
  rw [prime_pattern_model_odd_zero P L e he heP F hodd,sub_zero] at h
  have hm := prime_pattern_rounding_moment P N L Z hZ hsum
  have hp := prime_pattern_rounding_polynomial P N L Z hZ hsum
  calc
    _ ≤ _ := h
    _ ≤ (1+3^L)*((2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial+Z^L/N)+(L+1)*Z^L/N :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) (by positivity)) hp
    _ = _ := by ring

lemma pattern_factorial_tail_tendsto (M : ℝ) :
    Tendsto (fun L : ℕ => (1+3^L)*M^L/L.factorial) atTop (𝓝 0) := by
  have h := (Real.summable_pow_div_factorial M).tendsto_atTop_zero.add
    (Real.summable_pow_div_factorial (3*M)).tendsto_atTop_zero
  simp only [add_zero] at h
  convert h using 1
  funext L
  rw [mul_pow]
  ring

/-- Degree is chosen before the prime set, endpoint and observable. This
quantifier order permits moving prime bands with a sufficiently small fixed
power exponent, and arbitrary endpoint-dependent odd observables. -/
theorem exists_degree_for_prime_pattern_symmetry (M ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ (P : Finset ℕ) (N : ℕ) (Z : ℝ)
      (e : PrimeAtom ≃ PrimeAtom) (F : Finset PrimeAtom → ℝ),
      (∀ p ∈ P, p.Prime) → 0 < N → 1 ≤ Z →
      (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) ≤ Z →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ a, (e a).1=a.1) → (primeAtoms P).map e.toEmbedding = primeAtoms P →
      (∀ T ⊆ primeAtoms P, |F T| ≤ 1) →
      (∀ T, F (T.map e.toEmbedding) = -F T) →
      (1+3^L+(L+1))*Z^L/N < ε/2 →
      |(∑ n ∈ range N, F (activePrimeAtoms P n))/N| < ε := by
  obtain ⟨L,hL,htail⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((pattern_factorial_tail_tendsto M).eventually_lt_const (show (0 : ℝ)<ε/2 by positivity))).exists
  refine ⟨L,hL,?_⟩
  intro P N Z e F hP hN hZ hsum hmass he heP hF hodd hbudget
  have hb := prime_pattern_odd_bound P hP N hN L Z hZ hsum e he heP F hF hodd
  have hm : (1+3^L)*(2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial ≤
      (1+3^L)*M^L/L.factorial := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) hmass L
  linarith

lemma prime_atoms_modulus_budget (P : Finset ℕ) (X : ℕ)
    (hX : ∀ p ∈ P, p ≤ X) :
    (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) ≤ 4*(X+1 : ℝ)^2 := by
  have hcard : P.card ≤ X+1 := (card_le_card (fun p hp => mem_range.mpr
    (Nat.lt_succ_of_le (hX p hp)))).trans_eq (card_range (X+1))
  have hs : (∑ p ∈ P, (p : ℝ)) ≤ (X+1 : ℝ)^2 := by
    calc
      _ ≤ ∑ _ ∈ P, (X : ℝ) := sum_le_sum fun p hp => by exact_mod_cast hX p hp
      _ = (P.card : ℝ)*X := by simp
      _ ≤ (X+1 : ℝ)*X := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg X)
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) X]
  have he : (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ)) = 4*∑ p ∈ P, (p : ℝ) := by
    simp only [primeAtoms,sum_product,sum_const,card_univ,Fintype.card_bool,
      nsmul_eq_mul,← mul_sum]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Natural-prefix transfer for small-power prime bands of bounded reciprocal
mass, uniform in all bounded odd observables. The exponent depends on the
requested precision and reciprocal-mass bound. -/
theorem exists_small_power_for_pattern_symmetry (M ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (e : PrimeAtom ≃ PrimeAtom) (F : Finset PrimeAtom → ℝ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ a, (e a).1=a.1) → (primeAtoms P).map e.toEmbedding = primeAtoms P →
      (∀ T ⊆ primeAtoms P, |F T| ≤ 1) →
      (∀ T, F (T.map e.toEmbedding) = -F T) →
      |(∑ n ∈ range N, F (activePrimeAtoms P n))/N| < ε := by
  obtain ⟨L,hL,hdegree⟩ := exists_degree_for_prime_pattern_symmetry M ε hε
  let δ : ℝ := 1/(4*L)
  let C : ℝ := 1+3^L+(L+1)
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδeq : δ*(2*L)=1/2 := by dsimp [δ]; field_simp; ring
  have hC : 0≤C := by dsimp [C]; positivity
  have ht : Tendsto (fun N : ℕ => C*16^L*(N : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp
        tendsto_natCast_atTop_atTop).const_mul (C*16^L)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),ht.eventually_lt_const
    (show (0 : ℝ)<ε/2 by positivity)] with N hN hbudget
  intro P e F hP hmass he heP hF hodd
  let X : ℕ := ⌊(N : ℝ)^δ⌋₊
  let Z : ℝ := 4*(X+1 : ℝ)^2
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hpow1 : (1 : ℝ)≤(N : ℝ)^δ := Real.one_le_rpow hN1 hδ.le
  have hX : (X : ℝ)≤(N : ℝ)^δ := Nat.floor_le (Real.rpow_nonneg hN0.le δ)
  have hZ : 1≤Z := by dsimp [Z]; nlinarith [Nat.cast_nonneg (α := ℝ) X]
  have hZbound : Z ≤ 16*((N : ℝ)^δ)^2 := by
    dsimp [Z]
    have hx : (0 : ℝ)≤X := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((N : ℝ)^δ-X)]
  have hpower : (((N : ℝ)^δ)^2)^L=(N : ℝ)^(1/2 : ℝ) := by
    rw [← pow_mul,← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hδeq
  have hZbudget : C*Z^L/N ≤ C*16^L*(N : ℝ)^(-(1/2 : ℝ)) := by
    calc
      _ ≤ C*(16*((N : ℝ)^δ)^2)^L/N := by
        apply div_le_div_of_nonneg_right _ hN0.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hZbound L) hC
      _ = C*16^L*((N : ℝ)^(1/2 : ℝ)/N) := by rw [mul_pow,hpower]; ring
      _ = _ := by
        rw [show -(1/2 : ℝ) = 1/2-1 by ring,Real.rpow_sub hN0,Real.rpow_one]
  apply hdegree P N Z e F (fun p hp => (hP p hp).1) (by omega) hZ
    (prime_atoms_modulus_budget P X (fun p hp => (Nat.le_floor_iff (by positivity)).mpr (hP p hp).2))
    hmass he heP hF hodd
  exact hZbudget.trans_lt hbudget

#print axioms prime_pattern_odd_bound
#print axioms exists_degree_for_prime_pattern_symmetry
#print axioms exists_small_power_for_pattern_symmetry
end Erdos371.FiniteSieve
