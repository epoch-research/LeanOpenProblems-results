import FormalConjectures.Util.ProblemImports

open Rat
open BigOperators

/--
A064169: Numerator - denominator in n-th harmonic number, $1 + 1/2 + 1/3 + \dots + 1/n$.
-/
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  -- The difference in ℤ is non-negative for n ≥ 1. Int.natAbs ensures the output is ℕ.
  Int.natAbs (hn.num - hn.den)

-- We will prove the negation of the conjecture.

-- Helper definitions for structural binary sums to avoid stack overflows in kernel reduction.
def nat_sum_depth (L : ℕ) : ℕ → ℕ × ℕ
  | 0 => if L < 16843 then (1, L) else (0, 1)
  | d + 1 =>
    let (n1, d1) := nat_sum_depth L d
    let (n2, d2) := nat_sum_depth (L + 2^d) d
    (n1 * d2 + n2 * d1, d1 * d2)

def mod_sum_depth (L : ℕ) (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => if L < 16843 then (1 % m, L % m) else (0, 1)
  | d + 1 =>
    let (n1, d1) := mod_sum_depth L m d
    let (n2, d2) := mod_sum_depth (L + 2^d) m d
    ((n1 * d2 + n2 * d1) % m, (d1 * d2) % m)

theorem nat_sum_depth_den_pos (L d : ℕ) (hL : L > 0) : (nat_sum_depth L d).2 > 0 := by
  induction' d with d ih generalizing L
  · simp only [nat_sum_depth]
    by_cases h : L < 16843
    · simp only [h, ↓reduceIte]
      omega
    · simp only [h, ↓reduceIte]
      omega
  · simp only [nat_sum_depth]
    have h_pow : 2^d > 0 := by positivity
    have h1 := ih L hL
    have h2 := ih (L + 2^d) (by omega)
    exact Nat.mul_pos h1 h2

theorem nat_sum_depth_eq (L d : ℕ) (hL : L > 0) :
  ((nat_sum_depth L d).1 : ℚ) / ((nat_sum_depth L d).2 : ℚ) =
    ∑ i ∈ (Finset.Ico L (L + 2^d)).filter (fun i => i < 16843), (i : ℚ)⁻¹ := by
  induction' d with d ih generalizing L
  · simp only [pow_zero]
    by_cases h : L < 16843
    · have h_eq : (Finset.filter (fun i => i < 16843) (Finset.Ico L (L + 1))) = {L} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
        omega
      simp only [nat_sum_depth, h, ↓reduceIte]
      rw [h_eq]
      simp only [Finset.sum_singleton, Nat.cast_one]
      rw [one_div]
    · have h_eq : (Finset.filter (fun i => i < 16843) (Finset.Ico L (L + 1))) = ∅ := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor <;> intro hc
        · omega
        · contradiction
      simp only [nat_sum_depth, h, ↓reduceIte]
      rw [h_eq]
      simp only [Finset.sum_empty, Nat.cast_zero, Nat.cast_one, div_one]
  · simp only [nat_sum_depth]
    have h_pow : 2^d > 0 := by positivity
    have h1 := ih L hL
    have h2 := ih (L + 2^d) (by omega)
    have h_div : (((nat_sum_depth L d).1 * (nat_sum_depth (L + 2^d) d).2 + (nat_sum_depth (L + 2^d) d).1 * (nat_sum_depth L d).2 : ℕ) : ℚ) / (((nat_sum_depth L d).2 * (nat_sum_depth (L + 2^d) d).2 : ℕ) : ℚ) =
      ((nat_sum_depth L d).1 : ℚ) / ((nat_sum_depth L d).2 : ℚ) + ((nat_sum_depth (L + 2^d) d).1 : ℚ) / ((nat_sum_depth (L + 2^d) d).2 : ℚ) := by
      have hd1_pos := nat_sum_depth_den_pos L d hL
      have hd2_pos := nat_sum_depth_den_pos (L + 2^d) d (by omega)
      have hd1 : ((nat_sum_depth L d).2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd1_pos)
      have hd2 : ((nat_sum_depth (L + 2^d) d).2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd2_pos)
      push_cast
      field_simp
    rw [h_div, h1, h2]
    have h_split_eq : L + 2^(d+1) = L + 2^d + 2^d := by
      calc L + 2^(d+1) = L + (2^d * 2) := by rw [pow_succ]
      _ = L + (2^d + 2^d) := by ring
      _ = L + 2^d + 2^d := by omega
    have h_split : (Finset.Ico L (L + 2^(d+1))) = Finset.Ico L (L + 2^d) ∪ Finset.Ico (L + 2^d) (L + 2^(d+1)) := by
      rw [h_split_eq]
      rw [Finset.Ico_union_Ico (by omega) (by omega)]
      rw [min_eq_left (by omega), max_eq_right (by omega)]
    have h_disj : Disjoint (Finset.Ico L (L + 2^d)) (Finset.Ico (L + 2^d) (L + 2^(d+1))) := by
      apply Finset.disjoint_iff_ne.mpr
      intro a ha b hb hc
      simp only [Finset.mem_Ico] at ha hb
      omega
    rw [h_split, Finset.filter_union, Finset.sum_union]
    · rw [← h_split_eq]
    · apply Finset.disjoint_filter_filter h_disj

theorem mod_sum_eq_nat_sum (L d m : ℕ) (hm : m ≥ 2) :
  mod_sum_depth L m d = ((nat_sum_depth L d).1 % m, (nat_sum_depth L d).2 % m) := by
  induction' d with d ih generalizing L
  · simp [nat_sum_depth, mod_sum_depth]
    by_cases h : L < 16843
    · simp [h]
    · simp [h, Nat.zero_mod, Nat.mod_eq_of_lt hm]
  · simp [nat_sum_depth, mod_sum_depth]
    rw [ih L, ih (L + 2^d)]
    constructor
    · rw [Nat.add_mod]
      simp only
      have h1_eq : (nat_sum_depth L d).1 % m * ((nat_sum_depth (L + 2^d) d).2 % m) % m = ((nat_sum_depth L d).1 * (nat_sum_depth (L + 2^d) d).2) % m := by
        simp only [Nat.mod_mod, Nat.mul_mod]
      have h2_eq : (nat_sum_depth (L + 2^d) d).1 % m * ((nat_sum_depth L d).2 % m) % m = ((nat_sum_depth (L + 2^d) d).1 * (nat_sum_depth L d).2) % m := by
        simp only [Nat.mod_mod, Nat.mul_mod]
      rw [h1_eq, h2_eq]
      rw [← Nat.add_mod]
    · simp only
      rw [← Nat.mul_mod]

theorem mod_sum_16842_zero : (mod_sum_depth 1 (16843^3) 15).1 = 0 := by
  decide

theorem mod_sum_16842_den_ne_zero : (mod_sum_depth 1 16843 15).2 ≠ 0 := by
  decide

-- Coprime denominator lemmas for Finset sums.
theorem den_sum_coprime (p : ℕ) (hp : p.Prime) (s : Finset ι) (f : ι → ℚ) (h : ∀ x ∈ s, ¬ p ∣ (f x).den) :
  ¬ p ∣ (∑ x ∈ s, f x).den := by
  classical
  induction' s using Finset.induction_on with x s hx ih
  · simp only [Finset.sum_empty, Rat.zero_den]
    intro hc
    have : p = 1 := Nat.eq_one_of_dvd_one hc
    have : p ≥ 2 := hp.two_le
    omega
  · rw [Finset.sum_insert hx]
    have h_dvd := Rat.add_den_dvd (f x) (∑ x ∈ s, f x)
    intro hc
    have h_prime := hp
    have h_dvd_mul : p ∣ (f x).den * (∑ x ∈ s, f x).den := dvd_trans hc h_dvd
    rcases h_prime.dvd_mul.1 h_dvd_mul with h1 | h2
    · have : x ∈ insert x s := Finset.mem_insert_self x s
      have := h x this
      contradiction
    · have ih_h : ∀ y ∈ s, ¬ p ∣ (f y).den := by
        intro y hy
        exact h y (Finset.mem_insert_of_mem hy)
      have := ih ih_h
      contradiction

-- Verification of composite numbers primality negation.
theorem test_not_prime : ¬ (16843^2).Prime := by
  intro h
  have hdvd : 16843 ∣ 16843^2 := ⟨16843, by ring⟩
  have h_cases := (Nat.prime_def.1 h).2 16843 hdvd
  rcases h_cases with h1 | h2
  · revert h1; decide
  · have h2' : 16843 = 16843 * 16843 := by
      calc 16843 = 16843^2 := h2
      _ = 16843 * 16843 := by ring
    have h3 : 16843 * 1 = 16843 * 16843 := by
      rw [mul_one, ← h2']
    have h4 : 1 = 16843 := Nat.eq_of_mul_eq_mul_left (by decide) h3
    revert h4; decide

-- Algebraic identities for the disproof.
theorem sum_bij_test (p : ℕ) (hp : p ≥ 3) (hp_odd : p % 2 = 1) :
  let M := p^2
  let t := (Finset.Ico 1 M).filter (fun i => ¬ p ∣ i)
  let t1 := t.filter (fun x => x < M/2 + 1)
  let t2 := t.filter (fun x => ¬ x < M/2 + 1)
  ∑ x ∈ t2, (x : ℚ)⁻¹ = ∑ y ∈ t1, (M - y : ℚ)⁻¹ := by
  intro M t t1 t2
  dsimp only [M, t, t1, t2] at *
  symm
  apply Finset.sum_bij (fun y _ => p^2 - y)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy
    rcases hy with ⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩
    have hp2 : p^2 ≥ 9 := by
      calc p^2 ≥ 3^2 := Nat.pow_le_pow_left hp 2
      _ = 9 := by decide
    have h_odd : p^2 % 2 = 1 := by
      rw [Nat.pow_two, Nat.mul_mod, hp_odd]
    have h_ico : 1 ≤ p^2 - y ∧ p^2 - y < p^2 := by omega
    have h_ndvd : ¬ p ∣ p^2 - y := by
      intro hc
      rcases hc with ⟨c, hc⟩
      have : p ∣ y := by
        have hc_le : c ≤ p := by
          by_contra hc_gt
          have : p * p < p * c := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
          have : p^2 < p^2 - y := by
            calc p^2 = p * p := by ring
            _ < p * c := this
            _ = p^2 - y := hc.symm
          omega
        have h_eq : y = p * (p - c) := by
          calc y = p^2 - (p^2 - y) := by omega
          _ = p * p - p * c := by rw [hc, Nat.pow_two]
          _ = p * (p - c) := by rw [← Nat.mul_sub_left_distrib]
        use p - c
      contradiction
    have h_nlt : ¬ p^2 - y < p^2 / 2 + 1 := by omega
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨h_ico, h_ndvd⟩, h_nlt⟩
  · intro y1 hy1 y2 hy2 hseq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy1 hy2
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    rcases hx with ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩
    use p^2 - x
    have hp2 : p^2 ≥ 9 := by
      calc p^2 ≥ 3^2 := Nat.pow_le_pow_left hp 2
      _ = 9 := by decide
    have h_odd : p^2 % 2 = 1 := by
      rw [Nat.pow_two, Nat.mul_mod, hp_odd]
    have h_ico : 1 ≤ p^2 - x ∧ p^2 - x < p^2 := by omega
    have h_ndvd : ¬ p ∣ p^2 - x := by
      intro hc
      rcases hc with ⟨c, hc⟩
      have : p ∣ x := by
        have hc_le : c ≤ p := by
          by_contra hc_gt
          have : p * p < p * c := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
          have : p^2 < p^2 - x := by
            calc p^2 = p * p := by ring
            _ < p * c := this
            _ = p^2 - x := hc.symm
          omega
        have h_eq : x = p^2 - (p^2 - x) := by omega
        have h_eq2 : x = p * (p - c) := by
          calc x = p^2 - (p^2 - x) := h_eq
          _ = p * p - p * c := by rw [hc, Nat.pow_two]
          _ = p * (p - c) := by rw [← Nat.mul_sub_left_distrib]
        use p - c
      contradiction
    have h_lt : p^2 - x < p^2 / 2 + 1 := by omega
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨h_ico, h_ndvd⟩, h_lt⟩
    · omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy
    have : y ≤ p^2 := by omega
    rw [Nat.cast_sub this]

theorem sum_coprime_eq_p2_mul_T (p : ℕ) (hp : p ≥ 3) (hp_odd : p % 2 = 1) :
  let M := p^2
  let t := (Finset.Ico 1 M).filter (fun i => ¬ p ∣ i)
  let t1 := t.filter (fun x => x < M/2 + 1)
  ∑ x ∈ t, (x : ℚ)⁻¹ = (p^2 : ℚ) * ∑ x ∈ t1, (x * (p^2 - x) : ℚ)⁻¹ := by
  intro M t t1
  dsimp only [M, t, t1] at *
  have h_split : ∑ x ∈ (Finset.Ico 1 (p^2)).filter (fun i => ¬p ∣ i), (x : ℚ)⁻¹ =
    (∑ x ∈ ((Finset.Ico 1 (p^2)).filter (fun i => ¬p ∣ i)).filter (fun x => x < p^2 / 2 + 1), (x : ℚ)⁻¹) +
    (∑ x ∈ ((Finset.Ico 1 (p^2)).filter (fun i => ¬p ∣ i)).filter (fun x => ¬ x < p^2 / 2 + 1), (x : ℚ)⁻¹) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [h_split]
  have h_bij := sum_bij_test p hp hp_odd
  dsimp only at h_bij
  rw [h_bij]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Ico] at hx
  rcases hx with ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩
  have hx_pos : (x : ℚ) ≠ 0 := by
    have : x ≥ 1 := hx1
    positivity
  have h_sub_pos : (p^2 : ℚ) - (x : ℚ) ≠ 0 := by
    have h_sub_eq : ((p^2 - x : ℕ) : ℚ) = (p^2 : ℚ) - (x : ℚ) := Nat.cast_sub (by omega)
    rw [← h_sub_eq]
    have : (0 : ℚ) < ((p^2 - x : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
    exact ne_of_gt this
  have h_id : (x : ℚ)⁻¹ + ((p^2 : ℚ) - (x : ℚ))⁻¹ = (p^2 : ℚ) * (x * ((p^2 : ℚ) - (x : ℚ)))⁻¹ := by
    field_simp
    ring
  exact h_id

-- Helper definitions for custom prime factor checker to avoid kernel stack overflow
def no_factors (p : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | d + 2 => (! decide (d + 2 ∣ p)) && no_factors p (d + 1)

theorem no_factors_imp (p : ℕ) (K : ℕ) (h : no_factors p K = true) : ∀ m, 2 ≤ m → m ≤ K → ¬ m ∣ p := by
  induction' K with d ih
  · intro m hm hle
    omega
  · by_cases hd : d = 0
    · subst hd
      intro m hm hle
      omega
    · have : d + 1 ≥ 2 := by omega
      rcases d with _ | d
      · contradiction
      · simp only [no_factors, Bool.and_eq_true] at h
        have h1 : ¬ d + 2 ∣ p := by
          have h_not := h.1
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h_not
          exact h_not
        intro m hm hle
        if h_eq : m = d + 2 then
          subst h_eq
          exact h1
        else
          have : m ≤ d + 1 := by omega
          exact ih h.2 m hm this

theorem prime_of_no_factors (p : ℕ) (h : p ≥ 2) (h_sqrt : Nat.sqrt p = K) (hf : no_factors p K = true) : p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h, fun m hm hle => ?_⟩
  rw [h_sqrt] at hle
  exact no_factors_imp p K hf m hm hle

theorem prime_16843 : (16843).Prime := by
  apply prime_of_no_factors (K := 129)
  · decide
  · have h1 : 129 ≤ Nat.sqrt 16843 := Nat.le_sqrt.mpr (by decide)
    have h2 : Nat.sqrt 16843 < 130 := Nat.sqrt_lt.mpr (by decide)
    omega
  · decide

def spec_p : ℕ := 16843

def spec_M : ℕ := spec_p^2

def spec_t : Finset ℕ := (Finset.Ico 1 spec_M).filter (fun i => ¬ spec_p ∣ i)

def spec_t1 : Finset ℕ := spec_t.filter (fun x => x < spec_M / 2 + 1)

def spec_T : ℚ := ∑ x ∈ spec_t1, (x * (spec_M - x) : ℚ)⁻¹

/-- Conjecture: for n > 2, n divides a(n-2) if and only if n is a prime. Checked up to 20000. -/
theorem oeis_64169_conjecture_0.disproof : ¬ (∀ (n : ℕ) (hn : n > 2), (n ∣ A064169 (n - 2)) ↔ n.Prime) := by
  intro h
  have h_spec := h (16843^2) (by decide)
  have h_not_prime := test_not_prime
  rw [eq_false h_not_prime] at h_spec
  rw [iff_false] at h_spec
  have h_dvd : 16843^2 ∣ A064169 (16843^2 - 2) := by
    -- We want to prove 16843^2 ∣ A064169 (16843^2 - 2).
    -- By definition, A064169 (n - 2) is the absolute difference of num and den of harmonic (n - 2).
    -- Let p = 16843.
    let p := 16843
    have hp : p.Prime := prime_16843
    have hp_ge3 : p ≥ 3 := by decide
    have hp_odd : p % 2 = 1 := by decide
    have h_mod3 : (mod_sum_depth 1 (p^3) 15).1 = 0 := mod_sum_16842_zero
    have h_mod_eq := mod_sum_eq_nat_sum 1 15 (p^3) (by decide)
    rw [h_mod_eq] at h_mod3
    have h_dvd_nat : p^3 ∣ (nat_sum_depth 1 15).1 := by
      exact Nat.dvd_of_mod_eq_zero h_mod3
    
    -- Now we connect (nat_sum_depth 1 15) to harmonic 16842 in ℚ.
    have h_sum_eq : ((nat_sum_depth 1 15).1 : ℚ) / ((nat_sum_depth 1 15).2 : ℚ) = ∑ i ∈ (Finset.Ico 1 (1 + 2^15)).filter (fun i => i < p), (i : ℚ)⁻¹ := by
      exact nat_sum_depth_eq 1 15 (by decide)
    
    have h_filter_eq : (Finset.filter (fun i => i < p) (Finset.Ico 1 (1 + 2^15))) = Finset.Ico 1 p := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    
    rw [h_filter_eq] at h_sum_eq
    
    have h_harmonic_eq : harmonic (p - 1) = ∑ i ∈ Finset.Ico 1 p, (i : ℚ)⁻¹ := by
      -- harmonic (p-1) = ∑ i ∈ range (p-1), 1/(i+1)
      -- By changing variables, this is ∑ i ∈ Ico 1 p, 1/i.
      have : harmonic (p - 1) = ∑ i ∈ Finset.range (p - 1), (↑(i + 1) : ℚ)⁻¹ := rfl
      rw [this]
      apply Finset.sum_bij (fun i _ => i + 1)
      · intro a ha
        simp only [Finset.mem_range] at ha
        simp only [Finset.mem_Ico]
        omega
      · intro a1 ha1 a2 ha2 hseq
        omega
      · intro b hb
        simp only [Finset.mem_Ico] at hb
        use b - 1
        simp only [Finset.mem_range]
        refine ⟨by omega, by omega⟩
      · intro a ha
        rfl

    have h_rat_eq : (harmonic (p - 1)) = ((nat_sum_depth 1 15).1 : ℚ) / ((nat_sum_depth 1 15).2 : ℚ) := by
      rw [h_harmonic_eq, ← h_sum_eq]
    
    -- Under h_rat_eq, since p^3 divides (nat_sum_depth 1 15).1, we have p^3 divides (harmonic (p-1)).num!
    -- Specifically, let H = harmonic (p-1). H = U / V in lowest terms.
    -- (nat_sum_depth 1 15).1 = p^3 * K for some K.
    rcases h_dvd_nat with ⟨K, hK_eq⟩
    have h_num_dvd : (p^3 : ℚ) * (K : ℚ) / ((nat_sum_depth 1 15).2 : ℚ) = (harmonic (p - 1)) := by
      rw [h_rat_eq, hK_eq]
      push_cast
      rfl
    
    -- Now we have: (harmonic (p-1)).num * (nat_sum_depth 1 15).2 = p^3 * K * (harmonic (p-1)).den.
    -- Since p^3 is coprime to (nat_sum_depth 1 15).2, p^3 must divide (harmonic (p-1)).num.
    have h_mod_eq_all := mod_sum_eq_nat_sum 1 15 p (by decide)
    have h_mod_den : (mod_sum_depth 1 p 15).2 = (nat_sum_depth 1 15).2 % p := by
      rw [h_mod_eq_all]
    have h_den_ne_zero : (mod_sum_depth 1 p 15).2 ≠ 0 := mod_sum_16842_den_ne_zero
    have h_den_coprime : ¬ p ∣ (nat_sum_depth 1 15).2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [← h_mod_den]
      exact h_den_ne_zero
    
    -- Let's prove: harmonic (p - 1) = p^3 * (some rational whose denominator is coprime to p).
    let K_rat : ℚ := (K : ℚ) / ((nat_sum_depth 1 15).2 : ℚ)
    have h_harmonic_p3 : harmonic (p - 1) = (p^3 : ℚ) * K_rat := by
      rw [← h_num_dvd]
      ring
    have h_K_den_coprime : ¬ p ∣ K_rat.den := by
      have h_div : K_rat.den ∣ (nat_sum_depth 1 15).2 := by
        have h_eq : K_rat = (K : ℚ) * ((nat_sum_depth 1 15).2 : ℚ)⁻¹ := div_eq_mul_inv (K : ℚ) ((nat_sum_depth 1 15).2 : ℚ)
        have hdvd : K_rat.den ∣ (K : ℚ).den * ((nat_sum_depth 1 15).2 : ℚ)⁻¹.den := by
          rw [h_eq]
          exact mul_den_dvd (K : ℚ) ((nat_sum_depth 1 15).2 : ℚ)⁻¹
        have hK_den : (K : ℚ).den = 1 := Rat.den_natCast K
        have hden_pos : (nat_sum_depth 1 15).2 > 0 := nat_sum_depth_den_pos 1 15 (by decide)
        have h_inv_den : ((nat_sum_depth 1 15).2 : ℚ)⁻¹.den = (nat_sum_depth 1 15).2 := inv_natCast_den_of_pos hden_pos
        rw [hK_den, one_mul, h_inv_den] at hdvd
        exact hdvd
      intro hc
      exact h_den_coprime (dvd_trans hc h_div)

    -- Now we apply sum_coprime_eq_p2_mul_T:
    -- harmonic (p^2 - 1) = p⁻¹ * harmonic (p-1) + p^2 * T
    -- = p^2 * K_rat + p^2 * T = p^2 * (K_rat + T).
    have h_coprime_T : ∑ x ∈ spec_t, (x : ℚ)⁻¹ = (p^2 : ℚ) * spec_T := by
      exact sum_coprime_eq_p2_mul_T p hp_ge3 hp_odd
    
    -- Prove harmonic (p^2 - 1) = p⁻¹ * harmonic (p-1) + sum_coprime.
    have h_split_harmonic : harmonic (p^2 - 1) = (p : ℚ)⁻¹ * harmonic (p - 1) + ∑ x ∈ spec_t, (x : ℚ)⁻¹ := by
      -- harmonic (p^2 - 1) = sum divisible by p + sum coprime to p.
      -- Sum divisible by p = p⁻¹ * harmonic (p-1).
      have h_partition : ∑ i ∈ Finset.Ico 1 (p^2), (i : ℚ)⁻¹ =
        (∑ i ∈ (Finset.Ico 1 (p^2)).filter (fun i => p ∣ i), (i : ℚ)⁻¹) +
        ∑ x ∈ spec_t, (x : ℚ)⁻¹ := by
        change ∑ i ∈ Finset.Ico 1 (p^2), (i : ℚ)⁻¹ =
          (∑ i ∈ (Finset.Ico 1 (p^2)).filter (fun i => p ∣ i), (i : ℚ)⁻¹) +
          ∑ x ∈ (Finset.Ico 1 (p^2)).filter (fun i => ¬ p ∣ i), (x : ℚ)⁻¹
        rw [Finset.sum_filter_add_sum_filter_not]
      have h_div_p : ∑ i ∈ (Finset.Ico 1 (p^2)).filter (fun i => p ∣ i), (i : ℚ)⁻¹ = ∑ j ∈ Finset.Ico 1 p, (p * j : ℚ)⁻¹ := by
        symm
        apply Finset.sum_bij (fun j _ => p * j)
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          simp only [Finset.mem_filter, Finset.mem_Ico]
          constructor
          · constructor
            · exact Nat.mul_pos (by omega) (by omega)
            · calc p * j < p * p := Nat.mul_lt_mul_of_pos_left hj.2 (by omega)
                  _ = p^2 := by ring
          · use j
        · intro j1 hj1 j2 hj2 hseq
          simp only [Finset.mem_Ico] at hj1 hj2
          exact Nat.eq_of_mul_eq_mul_left (by omega) hseq
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_Ico] at hi
          rcases hi with ⟨⟨h1, h2⟩, j, hj_eq⟩
          use j
          have hj_eq_symm : i = p * j := hj_eq
          rw [hj_eq_symm] at h1 h2
          have hj1 : 1 ≤ j := by
            by_contra hc
            have : j = 0 := by omega
            subst this
            simp only [mul_zero] at h1
            omega
          have hj2 : j < p := by
            by_contra hc
            have : p ≤ j := by omega
            have : p * p ≤ p * j := Nat.mul_le_mul_left p this
            have : p^2 ≤ p * j := by
              rwa [← Nat.pow_two] at this
            omega
          refine ⟨?_, hj_eq.symm⟩
          simp only [Finset.mem_Ico]
          exact ⟨hj1, hj2⟩
        · intro j hj
          push_cast
          rfl
      
      have h_div_p_inv : ∑ j ∈ Finset.Ico 1 p, (p * j : ℚ)⁻¹ = (p : ℚ)⁻¹ * harmonic (p - 1) := by
        rw [h_harmonic_eq]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_Ico] at hj
        push_cast
        ring
      
      have h_harmonic_def : harmonic (p^2 - 1) = ∑ i ∈ Finset.Ico 1 (p^2), (i : ℚ)⁻¹ := by
        have : harmonic (p^2 - 1) = ∑ i ∈ Finset.range (p^2 - 1), (↑(i + 1) : ℚ)⁻¹ := rfl
        rw [this]
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro a ha
          simp only [Finset.mem_range] at ha
          simp only [Finset.mem_Ico]
          omega
        · intro a1 ha1 a2 ha2 hseq
          omega
        · intro b hb
          simp only [Finset.mem_Ico] at hb
          use b - 1
          simp only [Finset.mem_range]
          refine ⟨by omega, by omega⟩
        · intro a ha
          rfl

      rw [h_harmonic_def, h_partition, h_div_p, h_div_p_inv]
    
    -- Combine h_split_harmonic with h_harmonic_p3:
    -- harmonic (p^2 - 1) = p⁻¹ * p^3 * K_rat + p^2 * T = p^2 * K_rat + p^2 * T = p^2 * (K_rat + T).
    have h_harmonic_p2 : harmonic (p^2 - 1) = (p^2 : ℚ) * (K_rat + spec_T) := by
      rw [h_split_harmonic, h_harmonic_p3, h_coprime_T]
      have : (p : ℚ)⁻¹ * ((p^3 : ℚ) * K_rat) = (p^2 : ℚ) * K_rat := by
        have hp_ne : (p : ℚ) ≠ 0 := by positivity
        field_simp
      rw [this]
      ring

    -- Now we have: harmonic (p^2 - 2) - 1 = harmonic (p^2 - 1) - (p^2 - 1)⁻¹ - 1
    -- = p^2 * (K_rat + T) - (p^2 - 1)⁻¹ - 1
    -- = p^2 * (K_rat + T - (p^2 - 1)⁻¹ * p⁻² - p⁻²).
    have h_sub_eq : harmonic (p^2 - 2) - 1 = (p^2 : ℚ) * (K_rat + spec_T - ((p^2 - 1 : ℕ) : ℚ)⁻¹) := by
      have hp2 : p^2 ≥ 2 := by decide
      have h_harmonic_succ : harmonic (p^2 - 1) = harmonic (p^2 - 2) + ((p^2 - 1 : ℕ) : ℚ)⁻¹ := by
        have : p^2 - 1 = p^2 - 2 + 1 := by omega
        rw [this]
        exact harmonic_succ (p^2 - 2)
      have h_ne : ((p^2 - 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have : harmonic (p^2 - 2) = harmonic (p^2 - 1) - ((p^2 - 1 : ℕ) : ℚ)⁻¹ := by
        rw [h_harmonic_succ]
        ring
      rw [this, h_harmonic_p2]
      field_simp
      ring

    -- Let Y_rat = K_rat + spec_T - (p^2 - 1)⁻¹ * p⁻² - p⁻².
    let Y_rat : ℚ := K_rat + spec_T - ((p^2 - 1 : ℕ) : ℚ)⁻¹
    have h_Y_coprime : ¬ p ∣ Y_rat.den := by
      -- Y_rat is a sum/diff of coprime rationals.
      -- Let's apply den_sum_coprime and add_den_dvd.
      have h_coprime_K : ¬ p ∣ K_rat.den := h_K_den_coprime
      have h_coprime_T_den : ¬ p ∣ spec_T.den := by
        apply den_sum_coprime p hp
        intro x hx
        have hx_mem : x ∈ ((Finset.Ico 1 (p^2)).filter (fun i => ¬ p ∣ i)).filter (fun x => x < p^2 / 2 + 1) := hx
        clear hx
        simp only [Finset.mem_filter, Finset.mem_Ico] at hx_mem
        rcases hx_mem with ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩
        have h_spec_M : spec_M = p^2 := rfl
        have h_pow_pos : x * (spec_M - x) > 0 := Nat.mul_pos hx1 (by omega)
        have h_eq : ((x * (spec_M - x) : ℕ) : ℚ) = ↑x * (↑spec_M - ↑x) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        rw [← h_eq]
        rw [inv_natCast_den_of_pos h_pow_pos]
        intro hc
        rcases hp.dvd_mul.1 hc with h_c1 | h_c2
        · exact hx3 h_c1
        · have : p ∣ spec_M - x := h_c2
          have hp2_dvd : p ∣ spec_M := by
            have : spec_M = p^2 := rfl
            rw [this]
            use p
            rw [Nat.pow_two]
          have : p ∣ x := by
            have hx_eq : x = spec_M - (spec_M - x) := by omega
            rw [hx_eq]
            exact Nat.dvd_sub hp2_dvd h_c2
          exact hx3 this
      have h_coprime_inv1 : ¬ p ∣ ((p^2 - 1 : ℕ) : ℚ)⁻¹.den := by
        have hp2 : p^2 ≥ 2 := by decide
        have : p^2 - 1 > 0 := by omega
        rw [inv_natCast_den_of_pos this]
        intro hc
        have h_div_prod : p ∣ (p - 1)*(p + 1) := by
          have h_eq : p^2 - 1 = (p - 1)*(p + 1) := by ring
          rwa [h_eq] at hc
        rcases hp.dvd_mul.1 h_div_prod with h_c1 | h_c2
        · have : p ≤ p - 1 := Nat.le_of_dvd (by omega) h_c1
          omega
        · rcases h_c2 with ⟨k, hk⟩
          rcases k with _ | k
          · omega
          · rcases k with _ | k
            · omega
            · have h1 : p * (k + 1) ≥ p := by
                have : p * (k + 1) ≥ p * 1 := Nat.mul_le_mul_left p (by omega)
                rwa [Nat.mul_one] at this
              have : p * (k + 1) ≥ 3 := by omega
              omega

      have h_sum1_dvd := Rat.add_den_dvd K_rat spec_T
      have h_sum2_dvd := Rat.sub_den_dvd (K_rat + spec_T) ((p^2 - 1 : ℕ) : ℚ)⁻¹
      intro hc
      have h_prime := hp
      rcases h_prime.dvd_mul.1 (dvd_trans hc h_sum2_dvd) with h1 | h2
      · rcases h_prime.dvd_mul.1 (dvd_trans h1 h_sum1_dvd) with h11 | h12
        · exact h_coprime_K h11
        · exact h_coprime_T_den h12
      · exact h_coprime_inv1 h2

    -- We have harmonic (p^2 - 2) - 1 = p^2 * Y_rat.
    -- Let q = harmonic (p^2 - 2). q - 1 = p^2 * Y_rat.
    -- q.num - q.den = p^2 * Y_rat.num * q.den / Y_rat.den.
    -- So Y_rat.den * (q.num - q.den) = p^2 * Y_rat.num * q.den.
    -- Since p^2 is coprime to Y_rat.den, p^2 must divide (q.num - q.den).
    let q := harmonic (p^2 - 2)
    have h_q_eq : q - 1 = (p^2 : ℚ) * Y_rat := h_sub_eq
    have h_q_num_den : q - 1 = ((q.num - q.den : ℤ) : ℚ) / (q.den : ℚ) := by
      have : q = (q.num : ℚ) / (q.den : ℚ) := by rw [num_div_den]
      nth_rw 1 [this]
      push_cast
      field_simp
    have h_eq_mul : (Y_rat.den : ℚ) * (q - 1) = (Y_rat.den : ℚ) * ((p^2 : ℚ) * Y_rat) := by rw [h_q_eq]
    rw [h_q_num_den] at h_eq_mul
    have h_Y_rat_num_den : Y_rat = (Y_rat.num : ℚ) / (Y_rat.den : ℚ) := by rw [num_div_den]
    have h_eq_mul2 : (Y_rat.den : ℚ) * (((q.num - q.den : ℤ) : ℚ) / (q.den : ℚ)) = (p^2 : ℚ) * (Y_rat.num : ℚ) := by
      rw [h_eq_mul]
      nth_rw 2 [h_Y_rat_num_den]
      have hY_den_ne : (Y_rat.den : ℚ) ≠ 0 := by positivity
      field_simp
    have h_eq_mul3 : (Y_rat.den : ℚ) * ((q.num - q.den : ℤ) : ℚ) = (p^2 : ℚ) * (Y_rat.num : ℚ) * (q.den : ℚ) := by
      have hq_den_ne : (q.den : ℚ) ≠ 0 := by positivity
      calc (Y_rat.den : ℚ) * ((q.num - q.den : ℤ) : ℚ) = ((Y_rat.den : ℚ) * (((q.num - q.den : ℤ) : ℚ) / (q.den : ℚ))) * (q.den : ℚ) := by field_simp
      _ = ((p^2 : ℚ) * (Y_rat.num : ℚ)) * (q.den : ℚ) := by rw [h_eq_mul2]
      _ = (p^2 : ℚ) * (Y_rat.num : ℚ) * (q.den : ℚ) := by ring
    have h_eq_int : (Y_rat.den : ℤ) * (q.num - q.den) = (p^2 : ℤ) * Y_rat.num * q.den := by
      exact_mod_cast h_eq_mul3
    
    -- Since p^2 ∣ (p^2 : ℤ) * Y_rat.num * q.den, we have p^2 ∣ (Y_rat.den : ℤ) * (q.num - q.den).
    have h_dvd_int_prod : (p^2 : ℤ) ∣ (Y_rat.den : ℤ) * (q.num - q.den) := by
      rw [h_eq_int]
      use Y_rat.num * (q.den : ℤ)
      ring
    
    -- Since p^2 is coprime to Y_rat.den, p^2 ∣ q.num - q.den!
    have h_coprime : Nat.Coprime (p^2) Y_rat.den := by
      -- since p is prime and ¬ p ∣ Y_rat.den
      have : Nat.Coprime p Y_rat.den := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_Y_coprime
      exact Nat.Coprime.pow_left 2 this
    
    have h_dvd_int : (p^2 : ℤ) ∣ (q.num - q.den) := by
      have h_cop_int : IsCoprime (p^2 : ℤ) (Y_rat.den : ℤ) := by
        exact_mod_cast h_coprime
      exact h_cop_int.dvd_of_dvd_mul_left h_dvd_int_prod
    
    -- Now we convert to Nat: 16843^2 ∣ Int.natAbs (q.num - q.den).
    have h_dvd_nat_abs : (p^2 : ℕ) ∣ Int.natAbs (q.num - q.den) := by
      exact Int.natAbs_dvd_natAbs.mpr h_dvd_int
    exact h_dvd_nat_abs
  
  exact h_spec h_dvd
