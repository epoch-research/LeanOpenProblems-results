import Submission.LowerExponent

/-!
# Reciprocal mass at the unconditional fixed smoothness scale

These results do not establish the arbitrary-root smoothness needed for
Erdős 821. They retain reciprocal divergence at one fixed weak scale.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- Reciprocal summability controls the geometrically sampled counting
function. No monotonicity of the indicator itself is assumed. -/
lemma summable_dyadic_count_of_summable_reciprocal (S : Set ℕ)
    (hS : ∀ n ∈ S, 0 < n)
    (H : Summable (S.indicator (fun n : ℕ => 1 / (n : ℝ)))) :
    Summable (fun k : ℕ =>
      (((Finset.range (2 ^ k + 1)).filter (fun n => n ∈ S)).card : ℝ) / (2 : ℝ) ^ k) := by
  classical
  let F : ℕ × ℕ → ℝ := fun z => if z.1 ∈ S ∧ z.1 ≤ 2 ^ z.2 then (2 : ℝ)⁻¹ ^ z.2 else 0
  have hF : 0 ≤ F := by intro z; dsimp [F]; split_ifs <;> positivity
  have hrow (n : ℕ) : Summable (fun k => F (n, k)) := by
    apply summable_geometric_two.of_nonneg_of_le (fun k => hF (n, k))
    intro k
    dsimp [F]
    split_ifs
    · simp only [one_div, le_refl]
    · positivity
  have hbound (n : ℕ) : (∑' k, F (n, k)) ≤ 2 * S.indicator (fun n : ℕ => 1 / (n : ℝ)) n := by
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
      have hid : (∑' k, F (n, k)) = 2 * (2 : ℝ)⁻¹ ^ Nat.clog 2 n := by
        simp only [F, hn, true_and, ← Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))]
        exact tsum_geometric_inv_two_ge _
      rw [hid]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [inv_pow, ← one_div]
      exact one_div_le_one_div_of_le (by exact_mod_cast hS n hn)
        (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n)
    · simp [F, hn]
  have hrows : Summable (fun n => ∑' k, F (n, k)) :=
    (H.mul_left 2).of_nonneg_of_le (fun n => tsum_nonneg (fun k => hF (n, k))) hbound
  have hprod : Summable F := (summable_prod_of_nonneg hF).mpr ⟨hrow, hrows⟩
  have hswap : Summable (fun z : ℕ × ℕ => F (z.2, z.1)) :=
    hprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
  convert hswap.prod using 1
  ext k
  rw [tsum_eq_sum (s := Finset.range (2 ^ k + 1)) (by
    intro n hn
    have : ¬n ≤ 2 ^ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp [F, this])]
  simp only [F]
  have hid : (∑ n ∈ Finset.range (2 ^ k + 1),
      if n ∈ S ∧ n ≤ 2 ^ k then (2 : ℝ)⁻¹ ^ k else 0) =
      ∑ n ∈ (Finset.range (2 ^ k + 1)).filter (fun n => n ∈ S), (2 : ℝ)⁻¹ ^ k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have : n ≤ 2 ^ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp only [this, and_true]
  rw [hid]
  simp only [Finset.sum_const, nsmul_eq_mul, inv_pow, div_eq_mul_inv]

/-- A lower counting bound of prime-count size on every sufficiently large
geometric scale forces reciprocal divergence. -/
lemma not_summable_reciprocal_of_eventual_dyadic_count (S : Set ℕ)
    (hS : ∀ n ∈ S, 0 < n) (t : ℕ) (ht : 0 < t) (C : ℝ)
    (H : ∀ᶠ L : ℕ in atTop,
      (2 : ℝ) ^ (t * L) ≤ C * L *
        (((Finset.range (2 ^ (t * L) + 1)).filter (fun n => n ∈ S)).card : ℝ)) :
    ¬Summable (S.indicator (fun n : ℕ => 1 / (n : ℝ))) := by
  intro hsum
  have hd := summable_dyadic_count_of_summable_reciprocal S hS hsum
  have hinj : Function.Injective (fun L : ℕ => t * L) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left ht h
  have hsub := (hd.comp_injective hinj).mul_left C
  apply Real.not_summable_one_div_natCast
  apply hsub.of_norm_bounded_eventually_nat
  filter_upwards [H, eventually_ge_atTop 1] with L hL hL1
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (t * L) := by positivity
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (L : ℝ))]
  dsimp only [Function.comp_apply]
  apply (div_le_iff₀ hLp).mpr
  have hb := (le_div_iff₀ hpow).mpr
    (show (1 : ℝ) * (2 : ℝ) ^ (t * L) ≤ C * L *
      (((Finset.range (2 ^ (t * L) + 1)).filter (fun n => n ∈ S)).card : ℝ) by
      simpa only [one_mul] using hL)
  convert hb using 1; ring

/-- A rational relative smoothness condition, written without real roots. -/
def rationalSmoothShiftedPrimes (a b : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∀ q ∈ (p - 1).primeFactors, q ^ a ≤ (p - 1) ^ b}

lemma relative_smooth_prime_count_of_sieve (t L : ℕ) (ht : 6 ≤ t)
    (hL : 4 ≤ L) (hLt : 12 * t ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L)))
    (hcard : 2 ^ (t * L) ≤ 2 * (t * L) * (P.card + 1)) :
    2 ^ (t * L) ≤ 4 * (t * L) *
      ((Finset.range (2 ^ (t * L) + 1)).filter
        (fun p => p ∈ rationalSmoothShiftedPrimes (t - 1) (t - 5))).card := by
  classical
  let A := 2 ^ ((t - 1) * L)
  let Q := P.filter (fun p => A < p)
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
  have hQ : Q ⊆ (Finset.range (2 ^ (t * L) + 1)).filter
      (fun p => p ∈ rationalSmoothShiftedPrimes (t - 1) (t - 5)) := by
    intro p hp
    obtain ⟨hpP, hAp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpprime, hpbound, hpsmooth⟩ := hP p hpP
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpprime, ?_⟩
    intro q hq
    have hqbound : q < 2 ^ ((t - 5) * L) :=
      Nat.mem_smoothNumbers'.mp hpsmooth q (Nat.prime_of_mem_primeFactors hq)
        (Nat.dvd_of_mem_primeFactors hq)
    calc
      q ^ (t - 1) ≤ (2 ^ ((t - 5) * L)) ^ (t - 1) :=
        Nat.pow_le_pow_left hqbound.le _
      _ = A ^ (t - 5) := by
        dsimp [A]
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ ≤ (p - 1) ^ (t - 5) := Nat.pow_le_pow_left (by omega) _
  have hsmall : (P.filter (fun p => ¬A < p)).card ≤ A + 1 := by
    calc
      _ ≤ (Finset.range (A + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        have := (Finset.mem_filter.mp hp).2
        exact Finset.mem_range.mpr (by omega)
      _ = _ := Finset.card_range _
  have hsplit : P.card ≤ Q.card + A + 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := P) (fun p => A < p)
    dsimp [Q]
    omega
  have hX : 2 ^ (t * L) = 2 ^ L * A := by
    dsimp [A]
    rw [← pow_add]
    congr 1
    have : t = (t - 1) + 1 := by omega
    nlinarith
  have hbudget : 12 * (t * L) * A ≤ 2 ^ (t * L) := by
    rw [hX]
    apply Nat.mul_le_mul_right A
    exact (show 12 * (t * L) ≤ L ^ 2 by nlinarith).trans (Sieve.sq_le_two_pow L hL)
  have hQcard : 2 ^ (t * L) ≤ 4 * (t * L) * Q.card := by
    have hlarge : 2 ^ (t * L) ≤ 2 * (t * L) * (Q.card + A + 2) :=
      hcard.trans (Nat.mul_le_mul_left _ (by omega))
    have herr : 4 * (t * L) * (A + 2) ≤ 12 * (t * L) * A := by
      have hh := Nat.mul_le_mul_left (4 * (t * L)) (show A + 2 ≤ 3 * A by omega)
      nlinarith only [hh]
    nlinarith only [hlarge, hbudget, herr]
  exact hQcard.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hQ))

/-- The unconditional sieve supplies reciprocal divergence at one fixed
relative smoothness exponent strictly below one. This exponent is not
arbitrarily small. -/
theorem exists_fixed_smooth_reciprocal_divergence :
    ∃ a b : ℕ, 0 < b ∧ b < a ∧
      ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
        (fun p : ℕ => 1 / (p : ℝ))) := by
  obtain ⟨t, ht, L₀, H⟩ := Sieve.exists_eventual_full_smooth_shifted_prime_density
  refine ⟨t - 1, t - 5, by omega, by omega, ?_⟩
  apply not_summable_reciprocal_of_eventual_dyadic_count _
    (fun p hp => hp.1.pos) t (by omega) (4 * (t : ℝ))
  filter_upwards [eventually_ge_atTop (max L₀ (max 4 (12 * t)))] with L hL
  have hL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hL4 : 4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLt : 12 * t ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨P, hP, hcard⟩ := H L hL₀
  have h := relative_smooth_prime_count_of_sieve t L ht hL4 hLt P hP hcard
  exact_mod_cast (by simpa only [mul_assoc] using h :
    2 ^ (t * L) ≤ 4 * t * L *
      ((Finset.range (2 ^ (t * L) + 1)).filter
        (fun p => p ∈ rationalSmoothShiftedPrimes (t - 1) (t - 5))).card)

/-- Converting rational smoothness to the integer root parameter. -/
lemma predecessor_mem_smooth_of_rational {a b k p : ℕ}
    (hb : 0 < b) (hscale : k * b ≤ a)
    (hp : p ∈ rationalSmoothShiftedPrimes a b) :
    p - 1 ∈ smoothShiftedPredecessors k := by
  refine ⟨by simpa only [Nat.sub_add_cancel hp.1.one_lt.le] using hp.1, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := (Nat.prime_of_mem_primeFactors hq).one_lt.le
  apply (Nat.pow_le_pow_iff_left (by omega : b ≠ 0)).mp
  calc
    (q ^ k) ^ b = q ^ (k * b) := (pow_mul _ _ _).symm
    _ ≤ q ^ a := Nat.pow_le_pow_right hq1 hscale
    _ ≤ _ := hp.2 q hq

lemma summable_rational_reciprocal_of_summable_predecessors
    (a b k : ℕ) (hb : 0 < b) (hscale : k * b ≤ a)
    (s : ℝ) (hs : s ≤ 1)
    (H : Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-s)))) :
    Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => 1 / (p : ℝ))) := by
  classical
  apply (summable_nat_add_iff 1).mp
  refine H.of_nonneg_of_le (fun d => Set.indicator_nonneg (fun p _ => by positivity) _) ?_
  intro d
  by_cases hd : d + 1 ∈ rationalSmoothShiftedPrimes a b
  · have hdp : d ∈ smoothShiftedPredecessors k := by
      simpa only [Nat.add_sub_cancel] using predecessor_mem_smooth_of_rational hb hscale hd
    have hd0 : 0 < d := by have := hd.1.two_le; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    rw [Set.indicator_of_mem hd, Set.indicator_of_mem hdp]
    calc
      1 / ((d + 1 : ℕ) : ℝ) ≤ 1 / (d : ℝ) :=
        one_div_le_one_div_of_le hdR (by push_cast; linarith)
      _ = (d : ℝ) ^ (-(1 : ℝ)) := by simp only [Real.rpow_neg_one, one_div]
      _ ≤ (d : ℝ) ^ (-s) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  · rw [Set.indicator_of_notMem hd]
    exact Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d

/-- Reciprocal divergence at arbitrarily small relative smoothness scales
would settle the conjecture. The unconditional result above supplies only
one fixed scale, not this hypothesis. -/
theorem erdos_821_of_arbitrarily_smooth_reciprocal_divergence
    (H : ∀ k : ℕ, 1 ≤ k → ∃ a b : ℕ, 0 < b ∧ k * b ≤ a ∧
      ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
        (fun p : ℕ => 1 / (p : ℝ)))) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  apply erdos_821_iff_smooth_shifted_nonsummable.mpr
  intro k hk hsum
  obtain ⟨a, b, hb, hscale, hdiv⟩ := H k hk
  apply hdiv
  apply summable_rational_reciprocal_of_summable_predecessors a b k hb hscale _ _ hsum
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
  linarith

#print axioms predecessor_mem_smooth_of_rational
#print axioms summable_rational_reciprocal_of_summable_predecessors
#print axioms erdos_821_of_arbitrarily_smooth_reciprocal_divergence

#print axioms summable_dyadic_count_of_summable_reciprocal
#print axioms not_summable_reciprocal_of_eventual_dyadic_count
#print axioms relative_smooth_prime_count_of_sieve
#print axioms exists_fixed_smooth_reciprocal_divergence

end Erdos821
