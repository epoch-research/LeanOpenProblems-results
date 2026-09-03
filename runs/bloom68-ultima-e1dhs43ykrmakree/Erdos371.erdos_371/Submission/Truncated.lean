import FormalConjecturesUtil

/-!
# A finite-prime truncation of the Erdős 371 comparison

For a fixed cutoff `y ≥ 2`, the largest prime divisor at most `y` (with default
zero) rises on a set of natural density `1 / 2`. The factorial `y!` is a period.
Reflection on a complete period interchanges rises and falls, and the remaining
incomplete block has bounded size.

This is an auxiliary result only; it does not assert the corresponding density
statement for the untruncated largest prime factor.
-/

namespace Erdos371Truncated

open Filter
open scoped Topology

/-- The primes at most `y` dividing `n`, including all such primes when `n = 0`. -/
def primeDivisors (y n : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter fun p => p.Prime ∧ p ∣ n

@[simp]
theorem mem_primeDivisors (y n p : ℕ) :
    p ∈ primeDivisors y n ↔ p ≤ y ∧ p.Prime ∧ p ∣ n := by
  simp [primeDivisors]

/-- The largest prime divisor of `n` at most `y`, with default `0`. -/
def truncated (y n : ℕ) : ℕ := (primeDivisors y n).sup id

theorem le_truncated {y n p : ℕ} (hpy : p ≤ y) (hp : p.Prime) (hd : p ∣ n) :
    p ≤ truncated y n :=
  Finset.le_sup (f := id) ((mem_primeDivisors y n p).2 ⟨hpy, hp, hd⟩)

theorem truncated_mem {y n : ℕ} (h : truncated y n ≠ 0) :
    truncated y n ≤ y ∧ (truncated y n).Prime ∧ truncated y n ∣ n := by
  have hs : (primeDivisors y n).Nonempty := by
    by_contra hs
    have he : primeDivisors y n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [truncated, he] at h
  have hm : truncated y n ∈ primeDivisors y n := by
    simpa [truncated] using (Finset.sup_mem_of_nonempty (f := id) hs)
  exact (mem_primeDivisors y n _).1 hm

/-- Every relevant prime divides the factorial, so the truncation is periodic. -/
theorem truncated_periodic (y : ℕ) : Function.Periodic (truncated y) y.factorial := by
  intro n
  unfold truncated
  congr 1
  ext p
  simp only [mem_primeDivisors]
  constructor
  · rintro ⟨hpy, hp, hd⟩
    exact ⟨hpy, hp, (Nat.dvd_add_iff_left (Nat.dvd_factorial hp.pos hpy)).2 hd⟩
  · rintro ⟨hpy, hp, hd⟩
    exact ⟨hpy, hp, (Nat.dvd_add_iff_left (Nat.dvd_factorial hp.pos hpy)).1 hd⟩

/-- Reflection about a multiple of every relevant prime preserves the truncation. -/
theorem truncated_reflect (y n : ℕ) (hn : n ≤ y.factorial) :
    truncated y (y.factorial - n) = truncated y n := by
  unfold truncated
  congr 1
  ext p
  simp only [mem_primeDivisors]
  constructor
  · rintro ⟨hpy, hp, hd⟩
    exact ⟨hpy, hp, (Nat.dvd_sub_iff_right hn (Nat.dvd_factorial hp.pos hpy)).1 hd⟩
  · rintro ⟨hpy, hp, hd⟩
    exact ⟨hpy, hp, (Nat.dvd_sub_iff_right hn (Nat.dvd_factorial hp.pos hpy)).2 hd⟩

/-- Adjacent values cannot tie: one contains `2`, but no prime divides both. -/
theorem truncated_succ_ne {y : ℕ} (hy : 2 ≤ y) (n : ℕ) :
    truncated y (n + 1) ≠ truncated y n := by
  intro heq
  have ht : 2 ≤ truncated y n := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact le_truncated hy Nat.prime_two (Nat.dvd_iff_mod_eq_zero.2 h)
    · rw [← heq]
      exact le_truncated hy Nat.prime_two (Nat.dvd_iff_mod_eq_zero.2 (by omega))
  obtain ⟨_, hp, hd⟩ := truncated_mem (show truncated y n ≠ 0 by omega)
  have hd' : truncated y n ∣ n + 1 := by
    rw [← heq]
    exact (truncated_mem (show truncated y (n + 1) ≠ 0 by omega)).2.2
  exact hp.not_dvd_one (by simpa using Nat.dvd_sub hd' hd)

/-- The predicate that the truncated largest prime factor rises. -/
def Rises (y n : ℕ) : Prop := truncated y n < truncated y (n + 1)

instance (y : ℕ) : DecidablePred (Rises y) := fun _ => inferInstanceAs (Decidable (_ < _))

theorem rises_periodic (y : ℕ) : Function.Periodic (Rises y) y.factorial := by
  intro n
  apply propext
  simp only [Rises, show n + y.factorial + 1 = n + 1 + y.factorial by omega,
    truncated_periodic y n, truncated_periodic y (n + 1)]

/-- On a full period, `n ↦ y! - 1 - n` exchanges rises and non-rises. -/
theorem rises_reflect_iff {y : ℕ} (hy : 2 ≤ y) {n : ℕ} (hn : n < y.factorial) :
    Rises y (y.factorial - 1 - n) ↔ ¬ Rises y n := by
  have h₁ : y.factorial - 1 - n = y.factorial - (n + 1) := by omega
  have h₂ : y.factorial - 1 - n + 1 = y.factorial - n := by omega
  unfold Rises
  rw [h₂, h₁, truncated_reflect y (n + 1) (by omega),
    truncated_reflect y n (by omega)]
  have hne := truncated_succ_ne hy n
  omega

/-- Precisely half of the indices in one full factorial period are rises. -/
theorem twice_count_period {y : ℕ} (hy : 2 ≤ y) :
    2 * Nat.count (Rises y) y.factorial = y.factorial := by
  let s := (Finset.range y.factorial).filter (Rises y)
  let t := (Finset.range y.factorial).filter fun n => ¬ Rises y n
  have hM := Nat.factorial_pos y
  have hmaps : ∀ n < y.factorial,
      y.factorial - 1 - n < y.factorial := by omega
  have hinv : ∀ n < y.factorial,
      y.factorial - 1 - (y.factorial - 1 - n) = n := by omega
  have hcard : s.card = t.card := by
    apply Finset.card_nbij' (s := s) (t := t) (fun n => y.factorial - 1 - n)
      (fun n => y.factorial - 1 - n)
    · intro n hn
      change n ∈ s at hn
      obtain ⟨hn, hr⟩ := Finset.mem_filter.1 hn
      have hn' := Finset.mem_range.1 hn
      change y.factorial - 1 - n ∈ t
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_range.2 (hmaps n hn'), ?_⟩
      rw [rises_reflect_iff hy hn']
      exact not_not_intro hr
    · intro n hn
      change n ∈ t at hn
      obtain ⟨hn, hr⟩ := Finset.mem_filter.1 hn
      have hn' := Finset.mem_range.1 hn
      change y.factorial - 1 - n ∈ s
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hmaps n hn'),
        (rises_reflect_iff hy hn').2 hr⟩
    · intro n hn
      change n ∈ s at hn
      exact hinv n (Finset.mem_range.1 (Finset.mem_filter.1 hn).1)
    · intro n hn
      change n ∈ t at hn
      exact hinv n (Finset.mem_range.1 (Finset.mem_filter.1 hn).1)
  have hsum : s.card + t.card = y.factorial := by
    exact (Finset.card_filter_add_card_filter_not (s := Finset.range y.factorial)
      (Rises y)).trans (Finset.card_range _)
  rw [Nat.count_eq_card_filter_range]
  change 2 * s.card = y.factorial
  omega

/-- Complete periods contribute their full count; a final block contributes its own count. -/
theorem count_mul_add_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ}
    (hp : Function.Periodic p M) (q r : ℕ) :
    Nat.count p (q * M + r) = q * Nat.count p M + Nat.count p r := by
  have hshift : (fun k => p (M + k)) = p := by
    funext k
    simpa only [Nat.add_comm] using hp k
  induction q with
  | zero => simp
  | succ q ih =>
    simp only [Nat.succ_mul]
    rw [show q * M + M + r = M + (q * M + r) by omega,
      Nat.count_add]
    simp only [hshift, ih]
    omega

/-- The usual cutoff density expressed with `Nat.count`. -/
theorem partialDensity_eq_count (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    {n : ℕ | p n}.partialDensity Set.univ N = (Nat.count p N : ℝ) / N := by
  have hset : ((Finset.range N).filter p : Set ℕ) = {n : ℕ | p n} ∩ Set.Iio N := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  rw [← hset, Set.ncard_coe_finset, Nat.count_eq_card_filter_range]

/-- A periodic predicate has natural density equal to its proportion in one period. -/
theorem hasDensity_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ}
    (hM : 0 < M) (hp : Function.Periodic p M) :
    {n : ℕ | p n}.HasDensity ((Nat.count p M : ℝ) / M) := by
  change Tendsto (fun N => {n : ℕ | p n}.partialDensity Set.univ N) atTop _
  simp only [partialDensity_eq_count]
  have hrem : Tendsto (fun N : ℕ => (Nat.count p (N % M) : ℝ) / N) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := (0 : ℝ)) (B := (M : ℝ))
    · exact .of_forall fun _ => Nat.cast_nonneg _
    · exact .of_forall fun N =>
        Nat.cast_le.mpr ((Nat.count_le p).trans (Nat.mod_lt N hM).le)
    · exact tendsto_natCast_atTop_atTop
  have hmod := tendsto_mod_div_atTop_nhds_zero_nat hM
  have hlimit : Tendsto (fun N : ℕ =>
      ((Nat.count p M : ℝ) / M) * (1 - (N % M : ℕ) / (N : ℝ)) +
        (Nat.count p (N % M) : ℝ) / N) atTop (𝓝 ((Nat.count p M : ℝ) / M)) := by
    simpa using ((hmod.const_sub (1 : ℝ)).const_mul ((Nat.count p M : ℝ) / M)).add hrem
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hdec : (N / M) * M + N % M = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N M
  have hc := count_mul_add_of_periodic p hp (N / M) (N % M)
  rw [hdec] at hc
  have hc' : (Nat.count p N : ℝ) =
      (N / M : ℕ) * (Nat.count p M : ℝ) + Nat.count p (N % M) := by exact_mod_cast hc
  have hd' : ((N / M : ℕ) : ℝ) * M + (N % M : ℕ) = N := by exact_mod_cast hdec
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hprod := congrArg (fun x : ℝ => (Nat.count p M : ℝ) * x) hd'
  rw [hc']
  field_simp
  nlinarith only [hprod]

/-- For each fixed natural cutoff at least two, truncated rises have natural density one half. -/
theorem truncated_rises_hasDensity {y : ℕ} (hy : 2 ≤ y) :
    {n : ℕ | truncated y (n + 1) > truncated y n}.HasDensity (1 / 2 : ℝ) := by
  have hc : (Nat.count (Rises y) y.factorial : ℝ) / y.factorial = 1 / 2 := by
    have hden : (y.factorial : ℝ) ≠ 0 := by positivity
    apply (div_eq_iff hden).2
    have hcount : 2 * (Nat.count (Rises y) y.factorial : ℝ) = y.factorial := by
      exact_mod_cast twice_count_period hy
    linarith
  simpa only [hc, Rises] using
    hasDensity_of_periodic (Rises y) (Nat.factorial_pos y) (rises_periodic y)

/-- The same truncation with an integer cutoff, via its nonnegative part. -/
def truncatedInt (y : ℤ) (n : ℕ) : ℕ := truncated y.toNat n

/-- Integer-cutoff formulation of the finite-prime auxiliary density result. -/
theorem truncatedInt_rises_hasDensity {y : ℤ} (hy : 2 ≤ y) :
    {n : ℕ | truncatedInt y (n + 1) > truncatedInt y n}.HasDensity (1 / 2 : ℝ) := by
  exact truncated_rises_hasDensity (show 2 ≤ y.toNat by omega)

/-- Truncation does not change a nontrivial integer whose largest prime is below the cutoff. -/
theorem truncated_eq_maxPrimeFac {y n : ℕ} (hn : 1 < n)
    (hy : Nat.maxPrimeFac n ≤ y) : truncated y n = Nat.maxPrimeFac n := by
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    obtain ⟨_, hp, hd⟩ := (mem_primeDivisors y n p).1 hp
    exact Nat.le_maxPrimeFac (by omega) hp hd
  · exact le_truncated hy (Nat.prime_maxPrimeFac_of_one_lt n hn) Nat.maxPrimeFac_dvd

/-- A counting union bound, formulated so that no disjointness is necessary. -/
theorem count_le_add_count_of_imp (p q r : ℕ → Prop) [DecidablePred p]
    [DecidablePred q] [DecidablePred r] (h : ∀ n, p n → q n ∨ r n) (N : ℕ) :
    Nat.count p N ≤ Nat.count q N + Nat.count r N := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Nat.count_succ]
    have hN := h N
    by_cases hp : p N <;> by_cases hq : q N <;> by_cases hr : r N <;>
      simp_all <;> omega

/-- The difference of the two finite counts is controlled by integers beyond the prime cutoff. -/
theorem count_comparison_error (y N : ℕ) :
    |(Nat.count (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)) N : ℝ) -
      Nat.count (Rises y) N| ≤
      2 + 2 * (Nat.count (fun n => y < Nat.maxPrimeFac n) (N + 1) : ℝ) := by
  let p := fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)
  let bad := fun n => n < 2 ∨ y < Nat.maxPrimeFac n ∨ y < Nat.maxPrimeFac (n + 1)
  have heq (n : ℕ) (hn : ¬ bad n) : Rises y n ↔ p n := by
    have hn' : 1 < n := by dsimp [bad] at hn; omega
    have h₀ : Nat.maxPrimeFac n ≤ y := by dsimp [bad] at hn; omega
    have h₁ : Nat.maxPrimeFac (n + 1) ≤ y := by dsimp [bad] at hn; omega
    simp only [Rises, truncated_eq_maxPrimeFac hn' h₀,
      truncated_eq_maxPrimeFac (show 1 < n + 1 by omega) h₁, p]
  have hleft : Nat.count p N ≤ Nat.count (Rises y) N + Nat.count bad N :=
    count_le_add_count_of_imp p (Rises y) bad (fun n hn => by
      by_cases hb : bad n
      · exact Or.inr hb
      · exact Or.inl ((heq n hb).2 hn)) N
  have hright : Nat.count (Rises y) N ≤ Nat.count p N + Nat.count bad N :=
    count_le_add_count_of_imp (Rises y) p bad (fun n hn => by
      by_cases hb : bad n
      · exact Or.inr hb
      · exact Or.inl ((heq n hb).1 hn)) N
  have hsmall : Nat.count (fun n => n < 2) N ≤ 2 := by
    rw [Nat.count_eq_card_filter_range]
    calc
      _ ≤ (Finset.range 2).card := Finset.card_le_card (fun n hn =>
        Finset.mem_range.2 (Finset.mem_filter.1 hn).2)
      _ = 2 := Finset.card_range _
  have hcurrent : Nat.count (fun n => y < Nat.maxPrimeFac n) N ≤
      Nat.count (fun n => y < Nat.maxPrimeFac n) (N + 1) :=
    Nat.count_monotone _ (by omega)
  have hnext : Nat.count (fun n => y < Nat.maxPrimeFac (n + 1)) N ≤
      Nat.count (fun n => y < Nat.maxPrimeFac n) (N + 1) := by
    rw [Nat.count_succ']
    omega
  have hb₁ := count_le_add_count_of_imp bad (fun n => n < 2)
    (fun n => y < Nat.maxPrimeFac n ∨ y < Nat.maxPrimeFac (n + 1)) (fun _ h => h) N
  have hb₂ := count_le_add_count_of_imp
    (fun n => y < Nat.maxPrimeFac n ∨ y < Nat.maxPrimeFac (n + 1))
    (fun n => y < Nat.maxPrimeFac n) (fun n => y < Nat.maxPrimeFac (n + 1))
    (fun _ h => h) N
  have hb : Nat.count bad N ≤
      2 + 2 * Nat.count (fun n => y < Nat.maxPrimeFac n) (N + 1) := by omega
  have hlr : (Nat.count p N : ℝ) ≤ Nat.count (Rises y) N + Nat.count bad N := by
    exact_mod_cast hleft
  have hrr : (Nat.count (Rises y) N : ℝ) ≤ Nat.count p N + Nat.count bad N := by
    exact_mod_cast hright
  have hbr : (Nat.count bad N : ℝ) ≤
      2 + 2 * (Nat.count (fun n => y < Nat.maxPrimeFac n) (N + 1) : ℝ) := by
    exact_mod_cast hb
  change |(Nat.count p N : ℝ) - Nat.count (Rises y) N| ≤ _
  rw [abs_le]
  constructor <;> linarith


#print axioms truncated_rises_hasDensity
#print axioms truncatedInt_rises_hasDensity
#print axioms hasDensity_of_periodic

end Erdos371Truncated
