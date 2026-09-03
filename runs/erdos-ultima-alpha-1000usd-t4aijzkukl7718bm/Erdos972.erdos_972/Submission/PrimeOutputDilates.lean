import FormalConjecturesUtil

/-!
Exact arithmetic of the two output dilates 2x and 3x. These identities do
not assert the existence or an asymptotic count of simultaneous primes.
In particular, they do not settle Erdos 972.
-/
namespace Erdos972PrimeOutputDilates

lemma floor_nat_mul_decompose {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ⌊(k : ℝ) * x⌋₊ = k * ⌊x⌋₊ + ⌊(k : ℝ) * (x - (⌊x⌋₊ : ℝ))⌋₊ := by
  have ht : 0 ≤ x - (⌊x⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have he : (k : ℝ) * x =
      (k : ℝ) * (x - (⌊x⌋₊ : ℝ)) + ((k * ⌊x⌋₊ : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg k) ht)]
  omega

/-- Both outputs being large primes forces one of two affine prime patterns. -/
theorem prime_dilates_patterns {x : ℝ} (hx : 0 ≤ x)
    (hp : Nat.Prime ⌊2 * x⌋₊) (hq : Nat.Prime ⌊3 * x⌋₊)
    (hp2 : 2 < ⌊2 * x⌋₊) (hq3 : 3 < ⌊3 * x⌋₊) :
    ∃ m : ℕ, ⌊2 * x⌋₊ = 2 * m + 1 ∧
      ((⌊3 * x⌋₊ = 3 * m + 1 ∧ (m : ℝ) + 1 / 2 ≤ x ∧ x < m + 2 / 3) ∨
       (⌊3 * x⌋₊ = 3 * m + 2 ∧ (m : ℝ) + 2 / 3 ≤ x ∧ x < m + 1)) := by
  let m := ⌊x⌋₊
  let t : ℝ := x - m
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Nat.floor_le hx)
  have ht1 : t < 1 := by
    have hh := Nat.lt_floor_add_one x
    change x < (m : ℝ) + 1 at hh
    dsimp [t]
    linarith
  have hpde : ⌊2 * x⌋₊ = 2 * m + ⌊2 * t⌋₊ := by
    simpa only [Nat.cast_ofNat] using floor_nat_mul_decompose hx 2
  have hqde : ⌊3 * x⌋₊ = 3 * m + ⌊3 * t⌋₊ := by
    simpa only [Nat.cast_ofNat] using floor_nat_mul_decompose hx 3
  have hk : ⌊2 * t⌋₊ < 2 := (Nat.floor_lt (by linarith)).mpr (by norm_num; linarith)
  have hl : ⌊3 * t⌋₊ < 3 := (Nat.floor_lt (by linarith)).mpr (by norm_num; linarith)
  have hk0 : ⌊2 * t⌋₊ ≠ 0 := by
    intro he
    have hd : 2 ∣ ⌊2 * x⌋₊ := by rw [hpde, he, add_zero]; exact dvd_mul_right _ _
    have hh := hp.eq_one_or_self_of_dvd 2 hd
    omega
  have hl0 : ⌊3 * t⌋₊ ≠ 0 := by
    intro he
    have hd : 3 ∣ ⌊3 * x⌋₊ := by rw [hqde, he, add_zero]; exact dvd_mul_right _ _
    have hh := hq.eq_one_or_self_of_dvd 3 hd
    omega
  have hk1 : ⌊2 * t⌋₊ = 1 := by omega
  have hkt := (Nat.floor_eq_iff (show 0 ≤ 2 * t by linarith)).mp hk1
  norm_num only [Nat.cast_one] at hkt
  refine ⟨m, by omega, ?_⟩
  rcases (show ⌊3 * t⌋₊ = 1 ∨ ⌊3 * t⌋₊ = 2 by omega) with hl1 | hl2
  · have hlt := (Nat.floor_eq_iff (show 0 ≤ 3 * t by linarith)).mp hl1
    norm_num only [Nat.cast_one] at hlt
    left
    refine ⟨by omega, ?_, ?_⟩ <;> dsimp [t] at * <;> linarith
  · have hlt := (Nat.floor_eq_iff (show 0 ≤ 3 * t by linarith)).mp hl2
    norm_num only [Nat.cast_ofNat] at hlt
    right
    refine ⟨by omega, ?_, ?_⟩ <;> dsimp [t] at * <;> linarith

/-- The two prime outputs satisfy an integer determinant of exactly plus or minus one. -/
theorem prime_dilates_determinant {x : ℝ} (hx : 0 ≤ x)
    (hp : Nat.Prime ⌊2 * x⌋₊) (hq : Nat.Prime ⌊3 * x⌋₊)
    (hp2 : 2 < ⌊2 * x⌋₊) (hq3 : 3 < ⌊3 * x⌋₊) :
    3 * (⌊2 * x⌋₊ : ℤ) - 2 * (⌊3 * x⌋₊ : ℤ) = 1 ∨
      3 * (⌊2 * x⌋₊ : ℤ) - 2 * (⌊3 * x⌋₊ : ℤ) = -1 := by
  obtain ⟨m, hp', hq'⟩ := prime_dilates_patterns hx hp hq hp2 hq3
  rcases hq' with ⟨hq', _, _⟩ | ⟨hq', _, _⟩
  · left
    rw [hp', hq']
    push_cast
    ring
  · right
    rw [hp', hq']
    push_cast
    ring

/-- Conversely, each affine prime pattern gives precisely its indicated floor window. -/
theorem prime_dilates_iff {m : ℕ} (hm : 2 ≤ m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (Nat.Prime ⌊2 * ((m : ℝ) + t)⌋₊ ∧ Nat.Prime ⌊3 * ((m : ℝ) + t)⌋₊) ↔
      Nat.Prime (2 * m + 1) ∧
        ((1 / 2 ≤ t ∧ t < 2 / 3 ∧ Nat.Prime (3 * m + 1)) ∨
         (2 / 3 ≤ t ∧ t < 1 ∧ Nat.Prime (3 * m + 2))) := by
  have hx : 0 ≤ (m : ℝ) + t := add_nonneg (Nat.cast_nonneg m) ht0
  have hfm : ⌊(m : ℝ) + t⌋₊ = m := (Nat.floor_eq_iff hx).mpr (by constructor <;> linarith)
  constructor
  · rintro ⟨hp, hq⟩
    have hmR : (2 : ℝ) ≤ m := Nat.cast_le.mpr hm
    have hp2 : 2 < ⌊2 * ((m : ℝ) + t)⌋₊ := by
      have hh := Nat.lt_floor_add_one (2 * ((m : ℝ) + t))
      have h4 : (4 : ℝ) ≤ 2 * ((m : ℝ) + t) := by linarith
      have hh' : (3 : ℝ) < (⌊2 * ((m : ℝ) + t)⌋₊ : ℝ) + 1 := by linarith
      exact_mod_cast (show (2 : ℝ) < (⌊2 * ((m : ℝ) + t)⌋₊ : ℝ) by linarith)
    have hq3 : 3 < ⌊3 * ((m : ℝ) + t)⌋₊ := by
      have hh := Nat.lt_floor_add_one (3 * ((m : ℝ) + t))
      exact_mod_cast (show (3 : ℝ) < (⌊3 * ((m : ℝ) + t)⌋₊ : ℝ) by linarith)
    obtain ⟨k, hk, hcases⟩ := prime_dilates_patterns hx hp hq hp2 hq3
    have hkm : k = m := by
      rcases hcases with ⟨_, hlo, hhi⟩ | ⟨_, hlo, hhi⟩
      all_goals
        have hf : ⌊(m : ℝ) + t⌋₊ = k :=
          (Nat.floor_eq_iff hx).mpr ⟨by linarith, by linarith⟩
        omega
    subst k
    refine ⟨by simpa only [hk] using hp, ?_⟩
    rcases hcases with ⟨hq', hlo, hhi⟩ | ⟨hq', hlo, hhi⟩
    · exact Or.inl ⟨by linarith, by linarith, by simpa only [hq'] using hq⟩
    · exact Or.inr ⟨by linarith, ht1, by simpa only [hq'] using hq⟩
  · rintro ⟨hp, hcases⟩
    have htlow : 1 / 2 ≤ t := by rcases hcases with h | h <;> linarith [h.1]
    have hp' : ⌊2 * ((m : ℝ) + t)⌋₊ = 2 * m + 1 := by
      apply (Nat.floor_eq_iff (show 0 ≤ 2 * ((m : ℝ) + t) by positivity)).mpr
      push_cast
      constructor <;> linarith
    refine ⟨by simpa only [hp'] using hp, ?_⟩
    rcases hcases with ⟨hlo, hhi, hq⟩ | ⟨hlo, hhi, hq⟩
    · have hq' : ⌊3 * ((m : ℝ) + t)⌋₊ = 3 * m + 1 := by
        apply (Nat.floor_eq_iff (show 0 ≤ 3 * ((m : ℝ) + t) by positivity)).mpr
        push_cast
        constructor <;> linarith
      simpa only [hq'] using hq
    · have hq' : ⌊3 * ((m : ℝ) + t)⌋₊ = 3 * m + 2 := by
        apply (Nat.floor_eq_iff (show 0 ≤ 3 * ((m : ℝ) + t) by positivity)).mpr
        push_cast
        constructor <;> linarith
      simpa only [hq'] using hq

/-- Infinitely many simultaneous prime outputs for these two dilates would
already give infinitely many prime pairs in the corresponding affine forms.
No such infinitude is asserted by this conditional statement. -/
theorem infinite_affine_pairs_of_infinite_dilates {α : ℝ} (hα : 1 ≤ α)
    (h : {n : ℕ | Nat.Prime ⌊2 * (α * n)⌋₊ ∧
      Nat.Prime ⌊3 * (α * n)⌋₊}.Infinite) :
    {m : ℕ | Nat.Prime (2 * m + 1) ∧
      (Nat.Prime (3 * m + 1) ∨ Nat.Prime (3 * m + 2))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, ⟨hp, hq⟩, hn⟩ := h.exists_gt (max B 3)
  have hBn : B < n := (le_max_left B 3).trans_lt hn
  have hn3 : 3 < n := (le_max_right B 3).trans_lt hn
  have hxn : (n : ℝ) ≤ α * n := le_mul_of_one_le_left (Nat.cast_nonneg n) hα
  have hx0 : 0 ≤ α * n := (Nat.cast_nonneg n).trans hxn
  have hpN : n ≤ ⌊2 * (α * n)⌋₊ := Nat.le_floor (by linarith)
  have hqN : n ≤ ⌊3 * (α * n)⌋₊ := Nat.le_floor (by linarith)
  obtain ⟨m, hp', hcases⟩ := prime_dilates_patterns hx0 hp hq (by omega) (by omega)
  have hmwin : α * n < (m : ℝ) + 1 := by
    rcases hcases with ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ <;> linarith
  have hnm : n ≤ m := by
    have hh : (n : ℝ) < (m : ℝ) + 1 := hxn.trans_lt hmwin
    have hh' : n < m + 1 := by exact_mod_cast hh
    omega
  refine ⟨m, ⟨by simpa only [hp'] using hp, ?_⟩, hBn.trans_le hnm⟩
  rcases hcases with ⟨hq', _, _⟩ | ⟨hq', _, _⟩
  · exact Or.inl (by simpa only [hq'] using hq)
  · exact Or.inr (by simpa only [hq'] using hq)

#print axioms prime_dilates_patterns
#print axioms prime_dilates_determinant
#print axioms prime_dilates_iff
#print axioms infinite_affine_pairs_of_infinite_dilates

end Erdos972PrimeOutputDilates
