import FormalConjecturesUtil

/-!
An unconditional Dirichlet argument with a varying integer translate of the slope.
The translate is not fixed, so this does not settle Erdős 972.
-/

namespace Erdos972Translation

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ (⌊α * p⌋₊).Prime}

lemma floor_mul_translate {α : ℝ} (hα : 0 ≤ α) (p k : ℕ) :
    ⌊(α + k) * p⌋₊ = ⌊α * p⌋₊ + p * k := by
  have he : (α + k) * p = α * p + (p * k : ℕ) := by
    push_cast
    ring
  rw [he, Nat.floor_add_natCast (mul_nonneg hα (Nat.cast_nonneg p))]

/-- Dirichlet applies to the translate parameter when the input prime is fixed. -/
theorem infinite_translates_of_coprime {α : ℝ} (hα : 0 ≤ α) {p : ℕ}
    (hp : p.Prime) (hc : (⌊α * p⌋₊).Coprime p) :
    {k : ℕ | p ∈ primeSet (α + k)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro K
  obtain ⟨q, hq, hprime, hcon⟩ := Nat.forall_exists_prime_gt_and_modEq
    (⌊α * p⌋₊ + p * K) hp.ne_zero hc
  have hbase : ⌊α * p⌋₊ ≤ q := by omega
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hbase).mp hcon.symm
  have hK : K < k := by
    by_contra h
    have hle := Nat.mul_le_mul_left p (Nat.le_of_not_gt h)
    omega
  refine ⟨k, ⟨hp, ?_⟩, hK⟩
  rw [floor_mul_translate hα, ← hk]
  exact hprime

/-- At a noninteger irrational slope, a sufficiently large input prime cannot
itself divide the output. This is coprimality with the input, not primality. -/
theorem eventually_floor_coprime_input {α : ℝ} (hα : 0 ≤ α)
    (hI : Irrational α) :
    ∃ N : ℕ, ∀ p : ℕ, N < p → p.Prime → (⌊α * p⌋₊).Coprime p := by
  let δ : ℝ := α - ⌊α⌋₊
  have hδ0 : 0 < δ := by
    apply sub_pos.mpr
    exact lt_of_le_of_ne (Nat.floor_le hα) (hI.ne_nat _).symm
  have hδ1 : δ < 1 := by
    dsimp [δ]
    linarith [Nat.lt_floor_add_one α]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, ?_⟩
  intro p hNp hp
  have hplarge : 1 < δ * p := by
    have he := (div_lt_iff₀ hδ0).mp (hN.trans (Nat.cast_lt.mpr hNp))
    nlinarith
  have hr0 : 0 < ⌊δ * p⌋₊ := Nat.floor_pos.mpr hplarge.le
  have hrp : ⌊δ * p⌋₊ < p := by
    apply (Nat.floor_lt (mul_nonneg hδ0.le (Nat.cast_nonneg p))).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_right hδ1 (Nat.cast_pos.mpr hp.pos)
  have hc : (⌊δ * p⌋₊).Coprime p :=
    (Nat.coprime_of_lt_prime (by omega) hrp hp).symm
  have he : α * p = δ * p + (⌊α⌋₊ * p : ℕ) := by
    dsimp [δ]
    push_cast
    ring
  rw [he, Nat.floor_add_natCast (mul_nonneg hδ0.le (Nat.cast_nonneg p))]
  simpa using hc

/-- Every sufficiently large prime input succeeds at infinitely many integer
translates of the given irrational slope. The successful translate depends on the input. -/
theorem eventually_infinite_translates {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α) :
    ∃ N : ℕ, ∀ p : ℕ, N < p → p.Prime →
      {k : ℕ | p ∈ primeSet (α + k)}.Infinite := by
  obtain ⟨N, hN⟩ := eventually_floor_coprime_input hα hI
  exact ⟨N, fun p hp hprime => infinite_translates_of_coprime hα hprime (hN p hp hprime)⟩

/-- Both coordinates can be made large, but the slope still varies with the input. -/
theorem exists_large_input_and_translate {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (N K : ℕ) :
    ∃ p k : ℕ, N < p ∧ K < k ∧ 1 < α + k ∧ Irrational (α + k) ∧
      p ∈ primeSet (α + k) := by
  obtain ⟨B, hB⟩ := eventually_infinite_translates (by linarith) hI
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (max B N + 1)
  have hBp : B < p := by omega
  obtain ⟨k, hk, hK⟩ := Set.infinite_iff_exists_gt.mp (hB p hBp hp) K
  exact ⟨p, k, by omega, hK, by linarith [Nat.cast_nonneg (α := ℝ) k],
    hI.add_natCast k, hk⟩

/-- An explicit positive translate that kills the entire finite input window. -/
noncomputable def gapTranslate (α : ℝ) (N : ℕ) : ℕ :=
  (⌊α * N⌋₊).factorial

/-- Each original output is a proper divisor of the corresponding translated output.
This construction works for every slope at least one, not only irrational slopes. -/
theorem factorial_translate_gap {α : ℝ} (hα : 1 ≤ α) (N t : ℕ) (ht : 0 < t) :
    ∀ p : ℕ, p ≤ N → p.Prime →
      ¬ (⌊(α + (gapTranslate α N * t : ℕ)) * p⌋₊).Prime := by
  intro p hpN hp
  have hα0 : 0 ≤ α := by linarith
  have hpout : p ≤ ⌊α * p⌋₊ := by
    apply Nat.le_floor
    simpa using mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg p)
  have hbound : ⌊α * p⌋₊ ≤ ⌊α * N⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpN) hα0)
  have hdiv : ⌊α * p⌋₊ ∣ gapTranslate α N :=
    Nat.dvd_factorial (hp.pos.trans_le hpout) hbound
  have hk : 0 < gapTranslate α N * t :=
    Nat.mul_pos (Nat.factorial_pos _) ht
  rw [floor_mul_translate hα0]
  apply Nat.not_prime_of_dvd_of_lt
    (dvd_add (dvd_refl _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hdiv t) p))
    (hp.two_le.trans hpout)
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hp.pos hk)

/-- For each finite input bound there are infinitely many bad translates, with the
fractional part of the slope unchanged. This does not give one translate for all bounds. -/
theorem infinite_initial_gap_translates {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    {k : ℕ | ∀ p : ℕ, p ≤ N → p ∉ primeSet (α + k)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro K
  refine ⟨gapTranslate α N * (K + 1), ?_, ?_⟩
  · intro p hpN hp
    exact factorial_translate_gap hα N (K + 1) (by omega) p hpN hp.1 hp.2
  · have hg : 1 ≤ gapTranslate α N := Nat.factorial_pos _
    have hmul := Nat.mul_le_mul_right (K + 1) hg
    omega

/-- The explicit finite-gap translates necessarily escape every bounded interval. -/
theorem input_bound_le_gapTranslate {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    N ≤ gapTranslate α N := by
  apply le_trans _ (Nat.self_le_factorial _)
  apply Nat.le_floor
  simpa using mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg N)

open Filter in
/-- Consequently, their limit is not a real counterexample. -/
theorem factorial_gap_slopes_tendsto_atTop {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => α + (gapTranslate α N : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨M, hM⟩ := exists_nat_gt (b - α)
  filter_upwards [eventually_ge_atTop M] with N hN
  have hMN : (M : ℝ) ≤ gapTranslate α N :=
    Nat.cast_le.mpr (hN.trans (input_bound_le_gapTranslate hα N))
  linarith

/-- For a fixed finite collection of translates, the quantifiers can be exchanged.
Thus boundedness would close this route, but the factorial construction above does not
supply it. -/
theorem bounded_gap_translates_iff (α : ℝ) (K : ℕ) :
    (∀ N : ℕ, ∃ k : ℕ, k ≤ K ∧ ∀ p : ℕ, p ≤ N → p ∉ primeSet (α + k)) ↔
      ∃ k : ℕ, k ≤ K ∧ primeSet (α + k) = ∅ := by
  classical
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have hex : ∀ k : Fin (K + 1), ∃ p : ℕ, p ∈ primeSet (α + (k : ℕ)) := by
      intro k
      exact hn k (by have := k.isLt; omega)
    choose f hf using hex
    obtain ⟨k, hk, hgap⟩ := h (Finset.univ.sup f)
    let i : Fin (K + 1) := ⟨k, by omega⟩
    exact hgap (f i) (Finset.le_sup (Finset.mem_univ i)) (hf i)
  · rintro ⟨k, hk, he⟩ N
    refine ⟨k, hk, ?_⟩
    intro p _ hp
    rw [he] at hp
    exact hp

/-- A bounded-translate construction would be a genuine disproof. The boundedness
hypothesis here is not established by the preceding finite-window construction. -/
theorem disproof_of_bounded_gap_translates {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (K : ℕ)
    (hgap : ∀ N : ℕ, ∃ k : ℕ, k ≤ K ∧
      ∀ p : ℕ, p ≤ N → p ∉ primeSet (α + k)) :
    ¬ (∀ β > 1, Irrational β → (primeSet β).Infinite) := by
  intro hC
  obtain ⟨k, _, hk⟩ := (bounded_gap_translates_iff α K).mp hgap
  have hi := hC (α + k) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (hI.add_natCast k)
  rw [hk] at hi
  exact hi Set.finite_empty

#print axioms bounded_gap_translates_iff
#print axioms disproof_of_bounded_gap_translates

#print axioms factorial_translate_gap
#print axioms infinite_initial_gap_translates
#print axioms factorial_gap_slopes_tendsto_atTop

#print axioms eventually_infinite_translates
#print axioms exists_large_input_and_translate

end Erdos972Translation
