import FormalConjectures.Util.ProblemImports
open PNat

/--
A078680: Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime, or $0$ if no such $m$ exists.
We search for the smallest element in the set of positive natural numbers ($\mathbb{N}^+$ or PNat) satisfying the primality condition.
-/
noncomputable def A078680 (n : ℕ) : ℕ :=
  -- Predicate P on PNat: n * 2^m + 1 is prime.
  let P (m : PNat) : Prop := Nat.Prime (n * 2 ^ (m : ℕ) + 1)

  -- Use classical logic to determine if a solution exists.
  match Classical.dec (∃ m : PNat, P m) with
  | isTrue h_exist => (PNat.find h_exist).val -- Find the smallest PNat m, and convert to Nat.
  | isFalse _      => 0                       -- Return 0 if no such PNat exists.

open Nat

lemma A078680_ne_zero_of_exists (n : ℕ)
    (h : ∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1)) : A078680 n ≠ 0 := by
  unfold A078680
  dsimp
  cases Classical.dec (∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1)) with
  | isFalse hfalse => exact (hfalse h).elim
  | isTrue hex => exact PNat.ne_zero (PNat.find hex)

lemma A078680_eq_zero_iff_not_exists (n : ℕ) :
    A078680 n = 0 ↔ ¬ ∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1) := by
  constructor
  · intro hz h
    exact A078680_ne_zero_of_exists n h hz
  · intro h
    unfold A078680
    dsimp
    cases Classical.dec (∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1)) with
    | isFalse _ => rfl
    | isTrue hex => exact (h hex).elim


lemma A078680_ne_zero_iff_exists (n : ℕ) :
    A078680 n ≠ 0 ↔ ∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1) := by
  constructor
  · intro hn
    by_contra h
    exact hn ((A078680_eq_zero_iff_not_exists n).mpr h)
  · exact A078680_ne_zero_of_exists n


lemma A078680_ne_zero_iff_not_all_composite (n : ℕ) :
    A078680 n ≠ 0 ↔ ¬ ∀ m : PNat, ¬ Nat.Prime (n * 2 ^ (m : ℕ) + 1) := by
  rw [A078680_ne_zero_iff_exists]
  push_neg
  rfl


lemma proth_prime_mul_two_pow_of_sub {a t m : ℕ} (ht : t < m)
    (hp : Nat.Prime (a * 2 ^ m + 1)) :
    Nat.Prime ((a * 2 ^ t) * 2 ^ (m - t) + 1) := by
  have hpow : 2 ^ t * 2 ^ (m - t) = 2 ^ m := by
    rw [← pow_add]
    rw [Nat.add_sub_of_le ht.le]
  have hcalc : (a * 2 ^ t) * 2 ^ (m - t) + 1 = a * 2 ^ m + 1 := by
    calc
      (a * 2 ^ t) * 2 ^ (m - t) + 1 = a * (2 ^ t * 2 ^ (m - t)) + 1 := by ring
      _ = a * 2 ^ m + 1 := by rw [hpow]
  rwa [hcalc]

lemma A078680_ne_zero_of_shifted_witness {a t m : ℕ} (ht : t < m)
    (hp : Nat.Prime (a * 2 ^ m + 1)) : A078680 (a * 2 ^ t) ≠ 0 := by
  let r : PNat := ⟨m - t, by omega⟩
  apply A078680_ne_zero_of_exists
  exact ⟨r, by simpa [r] using proth_prime_mul_two_pow_of_sub (a := a) ht hp⟩

lemma A078680_ne_zero_of_eq_mul_two_pow_of_witness {n a t m : ℕ}
    (hn : n = a * 2 ^ t) (ht : t < m)
    (hp : Nat.Prime (a * 2 ^ m + 1)) : A078680 n ≠ 0 := by
  subst n
  let r : PNat := ⟨m - t, by omega⟩
  apply A078680_ne_zero_of_exists
  exact ⟨r, by simpa [r] using proth_prime_mul_two_pow_of_sub (a := a) ht hp⟩


lemma A078680_mul_two_pow_ne_zero_iff_exists_gt (a t : ℕ) :
    A078680 (a * 2 ^ t) ≠ 0 ↔ ∃ m : ℕ, t < m ∧ Nat.Prime (a * 2 ^ m + 1) := by
  rw [A078680_ne_zero_iff_exists]
  constructor
  · rintro ⟨r, hp⟩
    refine ⟨t + (r : ℕ), Nat.lt_add_of_pos_right r.pos, ?_⟩
    have hcalc : (a * 2 ^ t) * 2 ^ (r : ℕ) + 1 = a * 2 ^ (t + (r : ℕ)) + 1 := by
      calc
        (a * 2 ^ t) * 2 ^ (r : ℕ) + 1 = a * (2 ^ t * 2 ^ (r : ℕ)) + 1 := by ring
        _ = a * 2 ^ (t + (r : ℕ)) + 1 := by rw [pow_add]
    rwa [← hcalc]
  · rintro ⟨m, htm, hp⟩
    let r : PNat := ⟨m - t, by omega⟩
    refine ⟨r, ?_⟩
    have hsum : t + (r : ℕ) = m := by dsimp [r]; omega
    have hcalc : (a * 2 ^ t) * 2 ^ (r : ℕ) + 1 = a * 2 ^ m + 1 := by
      calc
        (a * 2 ^ t) * 2 ^ (r : ℕ) + 1 = a * (2 ^ t * 2 ^ (r : ℕ)) + 1 := by ring
        _ = a * 2 ^ (t + (r : ℕ)) + 1 := by rw [pow_add]
        _ = a * 2 ^ m + 1 := by rw [hsum]
    rwa [hcalc]



lemma isSierpinski_of_A078680_eq_zero_of_odd {n : ℕ} (hn1 : 1 < n) (hnodd : ¬ 2 ∣ n)
    (hz : A078680 n = 0) : Nat.IsSierpinskiNumber n := by
  constructor
  · exact hnodd
  · intro m
    constructor
    · have hnpos : 0 < n := by omega
      nlinarith [pow_pos (by norm_num : 0 < (2:ℕ)) m]
    · by_cases hm : m = 0
      · subst m
        intro hp
        have hoddn : Odd n := by
          apply Nat.not_even_iff_odd.mp
          rwa [even_iff_two_dvd]
        have heven : Even (n + 1) := hoddn.add_one
        have hoddprime : Odd (n + 1) := by
          simpa using hp.odd_of_ne_two (by omega)
        exact (Nat.not_odd_iff_even.mpr heven) hoddprime
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        let pm : PNat := ⟨m, hmpos⟩
        have hnot := (A078680_eq_zero_iff_not_exists n).mp hz
        exact fun hp => hnot ⟨pm, by simpa [pm] using hp⟩

lemma A078680_ne_zero_of_odd_of_not_sierpinski {n : ℕ}
    (hn1 : 1 < n) (hnodd : ¬ 2 ∣ n) (hns : ¬ Nat.IsSierpinskiNumber n) :
    A078680 n ≠ 0 := by
  intro hz
  exact hns (isSierpinski_of_A078680_eq_zero_of_odd hn1 hnodd hz)


lemma A078680_two_pow_ne_zero {r : ℕ} (hr : r < 16) : A078680 (2 ^ r) ≠ 0 := by
  let m : PNat := ⟨16 - r, by omega⟩
  apply A078680_ne_zero_of_exists
  refine ⟨m, ?_⟩
  have hsum : r + (m : ℕ) = 16 := by dsimp [m]; omega
  have hcalc : 2 ^ r * 2 ^ (m : ℕ) + 1 = 65537 := by
    rw [← pow_add, hsum]
    norm_num
  rw [hcalc]
  norm_num


lemma four_lt_of_sixteen_lt_two_pow {k : ℕ} (h : 16 < 2 ^ k) : 4 < k := by
  by_contra hk
  have hk' : k ≤ 4 := by omega
  have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk'
  omega


lemma A078680_small_of_odd_part_witnesses
    (hoddparts : ∀ a t : ℕ, Odd a → 1 ≤ a * 2 ^ t ∧ a * 2 ^ t < 2^16 →
      ∃ m : ℕ, t < m ∧ Nat.Prime (a * 2 ^ m + 1)) :
    ∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨t, a, haodd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hn_eq' : n = a * 2 ^ t := by rw [hn_eq, mul_comm]
  rw [hn_eq']
  exact (A078680_mul_two_pow_ne_zero_iff_exists_gt a t).mpr
    (hoddparts a t haodd (by simpa [← hn_eq'] using hn))

lemma fermat_rhs_iff_A078680_2pow16_zero :
    A078680 (2^16) = 0 ↔ (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  rw [A078680_eq_zero_iff_not_exists]
  constructor
  · intro hzero k hk hp
    apply hzero
    let mnat := 2 ^ k - 16
    have hmpos : 0 < mnat := by
      dsimp [mnat]
      have : 16 < 2 ^ k := by
        have h4 : 2 ^ 4 < 2 ^ k := Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) hk
        norm_num at h4 ⊢
        exact h4
      omega
    let m : PNat := ⟨mnat, hmpos⟩
    refine ⟨m, ?_⟩
    have hmn : 16 + (m : ℕ) = 2 ^ k := by
      dsimp [m, mnat]
      omega
    have hcalc : (2 ^ 16) * 2 ^ (m : ℕ) + 1 = fermatNumber k := by
      rw [fermatNumber]
      rw [← pow_add]
      rw [hmn]
    change Nat.Prime ((2 ^ 16) * 2 ^ (m : ℕ) + 1)
    rw [hcalc]
    exact hp
  · intro hferm hEx
    rcases hEx with ⟨m, hp⟩
    have hp' : Nat.Prime (2 ^ (16 + (m : ℕ)) + 1) := by
      have hcalc : (2 ^ 16) * 2 ^ (m : ℕ) + 1 = 2 ^ (16 + (m : ℕ)) + 1 := by
        rw [pow_add]
      change Nat.Prime (2 ^ 16 * 2 ^ (m : ℕ) + 1) at hp
      rwa [hcalc] at hp
    have hnonzero : 16 + (m : ℕ) ≠ 0 := by omega
    obtain ⟨k, hkpow⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := 16 + (m : ℕ))
      (by norm_num) hnonzero hp'
    have hkgt : 4 < k := by
      apply four_lt_of_sixteen_lt_two_pow
      rw [← hkpow]
      have hmpos : 0 < (m : ℕ) := m.pos
      omega
    have hpfermat : Nat.Prime (fermatNumber k) := by
      rw [fermatNumber, ← hkpow]
      exact hp'
    exact hferm k hkgt hpfermat


lemma oeis_equivalence_iff_small_witnesses :
    (((A078680 (2^16) = 0 ∧
        (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0)) ↔
        (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k))) ↔
      ((∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) →
        (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))) := by
  rw [← fermat_rhs_iff_A078680_2pow16_zero]
  tauto

lemma not_oeis_equivalence_iff_fermat_rhs_and_not_small_witnesses :
    (¬ (((A078680 (2^16) = 0 ∧
        (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0)) ↔
        (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)))) ↔
      ((∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) ∧
        ¬ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))) := by
  rw [← fermat_rhs_iff_A078680_2pow16_zero]
  tauto


lemma oeis_equivalence_of_small_witnesses
    (hsmall : ∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0) :
    ((A078680 (2^16) = 0 ∧
        (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0)) ↔
      (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k))) := by
  constructor
  · intro h
    exact fermat_rhs_iff_A078680_2pow16_zero.mp h.1
  · intro h
    exact ⟨fermat_rhs_iff_A078680_2pow16_zero.mpr h, hsmall⟩

/--
Conjecture from OEIS A078680:
The claim that the first $n > 0$ for which $A078680(n)=0$ is $n=65536$ is equivalent to
the statement that all Fermat numbers $F_k = 2^{2^k} + 1$ for $k > 4$ are composite.

Here, $65536 = 2^{16}$.
-/
theorem oeis_A078680_conjecture_equivalence :
  (A078680 (2^16) = 0 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))
  ↔
  (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  apply oeis_equivalence_of_small_witnesses
  -- This is the finite computational theorem that every `1 ≤ n < 2^16`
  -- has a Proth-prime witness `n * 2^m + 1`.
  sorry
