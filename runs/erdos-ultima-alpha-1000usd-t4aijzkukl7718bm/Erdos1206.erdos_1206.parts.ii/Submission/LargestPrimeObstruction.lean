import FormalConjecturesUtil

/-! Largest-prime-factor selection cannot settle the conjecture.
These are auxiliary obstructions, not a proof or disproof of `Spec.lean`. -/

namespace Erdos1206
open Filter
open scoped Topology

/-- The largest prime divisor, with value zero at zero and one. -/
def greatestPrimeDivisor (n : ℕ) : ℕ := n.primeFactors.sup id

lemma greatestPrimeDivisor_le (n : ℕ) : greatestPrimeDivisor n ≤ n :=
  Finset.sup_le fun _ h => Nat.le_of_mem_primeFactors h

lemma greatestPrimeDivisor_prime {p : ℕ} (hp : p.Prime) :
    greatestPrimeDivisor p = p := by
  simp [greatestPrimeDivisor, hp.primeFactors]

lemma greatestPrimeDivisor_mul_prime {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hkp : k ≤ p) : greatestPrimeDivisor (k * p) = p := by
  rw [greatestPrimeDivisor, Nat.primeFactors_mul (by omega) hp.ne_zero,
    Finset.sup_union, hp.primeFactors, Finset.sup_singleton]
  exact max_eq_right ((greatestPrimeDivisor_le k).trans hkp)

/-- Sets depending only on the largest prime divisor cannot contain a prime
larger than twelve and have Sidon cubes. -/
lemma largest_prime_selection_bounded {A : Set ℕ}
    (hselect : ∀ m n : ℕ, greatestPrimeDivisor m = greatestPrimeDivisor n →
      (m ∈ A ↔ n ∈ A))
    (hs : IsSidon ((fun a : ℕ => a ^ 3) '' A)) :
    ∀ n ∈ A, greatestPrimeDivisor n ≤ 12 := by
  intro n hn
  by_contra! hlarge
  have hn₂ : 1 < n := by
    have := greatestPrimeDivisor_le n
    omega
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup n.primeFactors
    (Nat.nonempty_primeFactors.mpr hn₂) id
  change greatestPrimeDivisor n = p at heq
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpbig : 12 < p := by omega
  have hpA : p ∈ A := (hselect n p (heq.trans (greatestPrimeDivisor_prime hpprime).symm)).mp hn
  have hmul (k : ℕ) (hk : 0 < k) (hk12 : k ≤ 12) : k * p ∈ A := by
    apply (hselect (k * p) p _).mpr hpA
    exact (greatestPrimeDivisor_mul_prime hpprime hk (by omega)).trans
      (greatestPrimeDivisor_prime hpprime).symm
  have h₁ : p ^ 3 ∈ (fun a : ℕ => a ^ 3) '' A := ⟨p, hpA, rfl⟩
  have h₉ : (9 * p) ^ 3 ∈ (fun a : ℕ => a ^ 3) '' A := ⟨_, hmul 9 (by omega) (by omega), rfl⟩
  have h₁₀ : (10 * p) ^ 3 ∈ (fun a : ℕ => a ^ 3) '' A := ⟨_, hmul 10 (by omega) (by omega), rfl⟩
  have h₁₂ : (12 * p) ^ 3 ∈ (fun a : ℕ => a ^ 3) '' A := ⟨_, hmul 12 (by omega) (by omega), rfl⟩
  have hident : p ^ 3 + (12 * p) ^ 3 = (9 * p) ^ 3 + (10 * p) ^ 3 := by ring
  have h := hs _ h₁ _ h₉ _ h₁₂ _ h₁₀ hident
  have hp3 : 0 < p ^ 3 := pow_pos hpprime.pos _
  rcases h with h | h <;> simp only [mul_pow] at h <;> nlinarith [h.1]

/-- A set supported on finitely many prime factors has lower density zero.
Zero may also be included. -/
lemma lowerDensity_zero_of_smooth_support {A : Set ℕ} (K : ℕ)
    (hA : A ⊆ {0} ∪ Nat.smoothNumbers K) : A.lowerDensity = 0 := by
  classical
  apply le_antisymm _ (Set.lowerDensity_nonneg A)
  by_contra! hpos
  let δ := A.lowerDensity / 2
  have hδ : 0 < δ := half_pos hpos
  have hδA : δ < A.lowerDensity := half_lt_self hpos
  have hev : ∀ᶠ N : ℕ in atTop, δ < A.partialDensity Set.univ N :=
    eventually_lt_of_lt_liminf hδA (isBoundedUnder_of ⟨0, fun _ => by positivity⟩)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  let C := 2 ^ K.primesBelow.card
  have hcount (N : ℕ) : (A ∩ Set.Iio N).ncard ≤ 1 + C * N.sqrt := by
    have hsub : A ∩ Set.Iio N ⊆ ({0} : Set ℕ) ∪ (Nat.smoothNumbersUpTo N K : Set ℕ) := by
      intro n hn
      rcases hA hn.1 with hz | hs
      · exact Or.inl hz
      · exact Or.inr (Nat.mem_smoothNumbersUpTo.mpr ⟨Nat.le_of_lt hn.2, hs⟩)
    have hcard := Set.ncard_le_ncard hsub
      ((Set.finite_singleton 0).union (Nat.smoothNumbersUpTo N K).finite_toSet)
    have hu := Set.ncard_union_le ({0} : Set ℕ) (Nat.smoothNumbersUpTo N K : Set ℕ)
    simp only [Set.ncard_singleton, Set.ncard_coe_finset] at hu
    have hc := Nat.smoothNumbersUpTo_card_le N K
    change _ ≤ C * N.sqrt at hc
    omega
  obtain ⟨t, ht⟩ := exists_nat_gt (((C : ℝ) + 1) / δ)
  let m := max (M + 1) (t + 1)
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmM : M ≤ m * m := by
    have hm : M < m := by dsimp [m]; omega
    nlinarith
  have htm : (t : ℝ) < m := by exact_mod_cast (show t < m by dsimp [m]; omega)
  have hbig : (C : ℝ) + 1 < δ * m := by
    have := (div_lt_iff₀ hδ).mp (ht.trans htm)
    nlinarith
  have hden : (0 : ℝ) < (m * m : ℕ) := by positivity
  have hd := hM (m * m) hmM
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio] at hd
  have hlow := (lt_div_iff₀ hden).mp hd
  have hc := hcount (m * m)
  rw [Nat.sqrt_eq] at hc
  have hcR : ((A ∩ Set.Iio (m * m)).ncard : ℝ) ≤ 1 + C * (m : ℝ) := by exact_mod_cast hc
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  push_cast at hlow
  nlinarith [mul_lt_mul_of_pos_right hbig (show (0 : ℝ) < m by positivity)]

lemma largest_prime_selection_lowerDensity_zero {A : Set ℕ}
    (hselect : ∀ m n : ℕ, greatestPrimeDivisor m = greatestPrimeDivisor n →
      (m ∈ A ↔ n ∈ A))
    (hs : IsSidon ((fun a : ℕ => a ^ 3) '' A)) : A.lowerDensity = 0 := by
  apply lowerDensity_zero_of_smooth_support 13
  intro n hn
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  · apply Or.inr
    rw [Nat.mem_smoothNumbers]
    refine ⟨hn0, fun p hp => ?_⟩
    have hp' : p ∈ n.primeFactors := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp
    have hle : p ≤ greatestPrimeDivisor n := Finset.le_sup (f := id) hp'
    have := largest_prime_selection_bounded hselect hs n hn
    omega

end Erdos1206
