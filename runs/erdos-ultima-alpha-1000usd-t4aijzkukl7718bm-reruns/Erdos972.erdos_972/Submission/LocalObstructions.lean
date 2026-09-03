import FormalConjecturesUtil

/-!
# Local obstructions for rational slopes

Auxiliary work for Erdős 972. These results do not assert simultaneous primality.
-/

namespace Explore972

open Polynomial

lemma exists_affine_pair_ne_zero {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) (a b r s : K)
    (ha : a ≠ 0 ∨ r ≠ 0) (hb : b ≠ 0 ∨ s ≠ 0) :
    ∃ t : K, a * t + r ≠ 0 ∧ b * t + s ≠ 0 := by
  classical
  have linear_ne (a r : K) (h : a ≠ 0 ∨ r ≠ 0) :
      C a * X + C r ≠ (0 : K[X]) := by
    intro heq
    have h₁ := congrArg (fun f : K[X] => f.coeff 1) heq
    have h₀ := congrArg (fun f : K[X] => f.coeff 0) heq
    simp only [coeff_add, coeff_C_mul_X, coeff_C, zero_add, add_zero,
      coeff_zero, ite_true, ite_false, one_ne_zero, zero_ne_one] at h₁ h₀
    rcases h with h | h
    · exact h h₁
    · exact h h₀
  let f : K[X] := (C a * X + C r) * (C b * X + C s)
  have hf : f ≠ 0 := mul_ne_zero (linear_ne a r ha) (linear_ne b s hb)
  have hdeg : f.natDegree ≤ 2 := by
    exact (natDegree_mul_le).trans (by
      have h₁ := natDegree_linear_le (a := a) (b := r)
      have h₂ := natDegree_linear_le (a := b) (b := s)
      omega)
  by_contra h
  push_neg at h
  apply hf
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id
    (hcard := hdeg.trans_lt hcard)
  intro t
  by_cases ht : a * t + r = 0
  · simp [f, ht]
  · simp [f, h t ht]

lemma affine_pair_mod_two :
    ∀ a b r s : ZMod 2, a * r - b * s = 1 → (a = 0 ∨ b = 0) →
      ∃ t : ZMod 2, b * t + r ≠ 0 ∧ a * t + s ≠ 0 := by
  decide

lemma linear_pair_no_fixed_prime (a b r s : ℤ)
    (hdet : a * r - b * s = 1 ∨ a * r - b * s = 2)
    (hpar : ∃ t : ZMod 2, (b : ZMod 2) * t + r ≠ 0 ∧
      (a : ZMod 2) * t + s ≠ 0) :
    ∀ l : ℕ, l.Prime → ∃ t : ℤ,
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  intro l hl
  letI : Fact l.Prime := ⟨hl⟩
  have hx : ∃ t : ZMod l, (b : ZMod l) * t + r ≠ 0 ∧
      (a : ZMod l) * t + s ≠ 0 := by
    by_cases hl2 : l = 2
    · subst l
      exact hpar
    have hlarge : 2 < l := lt_of_le_of_ne hl.two_le (Ne.symm hl2)
    have hd : (a : ZMod l) * r - b * s ≠ 0 := by
      rcases hdet with hd | hd
      · have he := congrArg (fun z : ℤ => (z : ZMod l)) hd
        push_cast at he
        rw [he]
        exact one_ne_zero
      · have he := congrArg (fun z : ℤ => (z : ZMod l)) hd
        push_cast at he
        rw [he]
        intro hzero
        have hdiv : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp hzero
        have := Nat.le_of_dvd (by omega : 0 < 2) hdiv
        omega
    apply exists_affine_pair_ne_zero (by simpa only [ZMod.card] using hlarge)
    · by_contra! hz
      simp [hz.1, hz.2] at hd
    · by_contra! hz
      simp [hz.1, hz.2] at hd
  obtain ⟨t, ht₁, ht₂⟩ := hx
  refine ⟨(t.val : ℤ), ?_, ?_⟩
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (b * t.val + r) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₁ he
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * t.val + s) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₂ he

lemma zmod_two_not_both_one :
    ∀ a b : ZMod 2, ¬ (a = 1 ∧ b = 1) → a = 0 ∨ b = 0 := by
  decide

lemma rational_affine_model (a b : ℕ) (hb : 1 < b) (hab : a.Coprime b) :
    ∃ r s k : ℤ, 0 < k ∧ k < b ∧ (a : ℤ) * r - b * s = k ∧
      ∀ l : ℕ, l.Prime → ∃ t : ℤ,
        ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  let r₀ : ℤ := Nat.gcdA a b
  let s₀ : ℤ := -Nat.gcdB a b
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one] at hbez
  have hd₀ : (a : ℤ) * r₀ - b * s₀ = 1 := by
    dsimp [r₀, s₀]
    push_cast at hbez
    linarith
  have ht : (2 : ZMod 2) = 0 := by decide
  by_cases hodd : (a : ZMod 2) = 1 ∧ (b : ZMod 2) = 1
  · have hb3 : 2 < b := by
      have hb2 : b ≠ 2 := by
        intro heq
        have he := hodd.2
        simp [heq, ht] at he
      omega
    have hd : (a : ℤ) * (2 * r₀) - b * (2 * s₀) = 2 := by nlinarith [hd₀]
    have hpar : ∃ t : ZMod 2, (b : ZMod 2) * t + (2 * r₀ : ℤ) ≠ 0 ∧
        (a : ZMod 2) * t + (2 * s₀ : ℤ) ≠ 0 := by
      refine ⟨1, ?_, ?_⟩ <;> simp [hodd.1, hodd.2, ht]
    refine ⟨2 * r₀, 2 * s₀, 2, by norm_num, by exact_mod_cast hb3, hd, ?_⟩
    exact linear_pair_no_fixed_prime a b (2 * r₀) (2 * s₀) (Or.inr hd)
      (by simpa using hpar)
  · have hd₂ := congrArg (fun z : ℤ => (z : ZMod 2)) hd₀
    push_cast at hd₂
    have hpar := affine_pair_mod_two a b r₀ s₀ hd₂ (zmod_two_not_both_one a b hodd)
    refine ⟨r₀, s₀, 1, by norm_num, by exact_mod_cast hb, hd₀, ?_⟩
    exact linear_pair_no_fixed_prime a b r₀ s₀ (Or.inl hd₀) (by simpa using hpar)

lemma floor_rational_affine (a b r s k : ℤ) (hb : 0 < b)
    (hk : 0 ≤ k) (hkb : k < b) (hdet : a * r - b * s = k) (t : ℤ) :
    ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ)⌋ = a * t + s := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hkbr : (k : ℝ) < b := by exact_mod_cast hkb
  have hdr : (a : ℝ) * r - b * s = k := by exact_mod_cast hdet
  apply Int.floor_eq_iff.mpr
  push_cast
  rw [div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hbr).mpr
    nlinarith [hdr]
  · apply (div_lt_iff₀ hbr).mpr
    nlinarith [hdr]

/-- Every reduced rational noninteger slope has a floor-compatible pair of
linear forms with no fixed prime obstruction. This is not a prime-pair theorem. -/
theorem rational_slope_locally_admissible (a b : ℕ) (hb : 1 < b) (hab : a.Coprime b) :
    ∃ r s : ℤ,
      (∀ t : ℤ, ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ)⌋ = a * t + s) ∧
      ∀ l : ℕ, l.Prime → ∃ t : ℤ,
        ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  obtain ⟨r, s, k, hk, hkb, hd, hlocal⟩ := rational_affine_model a b hb hab
  refine ⟨r, s, ?_, hlocal⟩
  intro t
  simpa only [Int.cast_natCast] using
    floor_rational_affine a b r s k (by exact_mod_cast (by omega : 0 < b)) hk.le hkb hd t

/-- Local admissibility rules out finite congruence covers, also arbitrarily far
along the linear forms. No primality is asserted. -/
lemma locally_admissible_avoids_finite_primes (a b r s : ℤ)
    (hlocal : ∀ l : ℕ, l.Prime → ∃ t : ℤ,
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s)
    (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (N : ℕ) :
    ∃ t : ℕ, N < t ∧ ∀ l ∈ S,
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  classical
  have hnat : ∀ l : ℕ, ∃ t : ℕ, l.Prime →
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
    intro l
    by_cases hl : l.Prime
    · letI : NeZero l := ⟨hl.ne_zero⟩
      obtain ⟨t, ht₁, ht₂⟩ := hlocal l hl
      have hm : ((t : ZMod l).val : ℤ) ≡ t [ZMOD (l : ℤ)] := by
        apply (ZMod.intCast_eq_intCast_iff _ _ l).mp
        simp
      refine ⟨(t : ZMod l).val, fun _ => ⟨?_, ?_⟩⟩
      · exact fun hd => ht₁ (((hm.mul_left b).add_right r).dvd_iff.mp hd)
      · exact fun hd => ht₂ (((hm.mul_left a).add_right s).dvd_iff.mp hd)
    · exact ⟨0, fun h => (hl h).elim⟩
  choose f hf using hnat
  have hs : ∀ l ∈ S, (id l : ℕ) ≠ 0 := fun l hl => (hS l hl).ne_zero
  have hpair : Set.Pairwise (S : Set ℕ) (fun l m => (id l).Coprime (id m)) := by
    intro l hl m hm hne
    exact (Nat.coprime_primes (hS l hl) (hS m hm)).mpr hne
  let c := Nat.chineseRemainderOfFinset f id S hs hpair
  let M : ℕ := ∏ l ∈ S, l
  have hMpos : 0 < M := Finset.prod_pos (fun l hl => (hS l hl).pos)
  let t : ℕ := c.val + M * (N + 1)
  have hlarge : N < t := by
    have := Nat.le_mul_of_pos_left (N + 1) hMpos
    dsimp [t]
    omega
  refine ⟨t, hlarge, ?_⟩
  intro l hl
  have hlM : l ∣ M := Finset.dvd_prod_of_mem (fun l : ℕ => l) hl
  have hmod : t ≡ f l [MOD l] := by
    have hz : M ≡ 0 [MOD l] := Nat.modEq_zero_iff_dvd.mpr hlM
    have ht : t ≡ c.val [MOD l] := by
      simpa [t] using (hz.mul_right (N + 1)).add_left c.val
    exact ht.trans (c.property l hl)
  have hm : (t : ℤ) ≡ (f l : ℤ) [ZMOD (l : ℤ)] := Int.natCast_modEq_iff.mpr hmod
  refine ⟨?_, ?_⟩
  · exact fun hd => (hf l (hS l hl)).1 (((hm.mul_left b).add_right r).dvd_iff.mp hd)
  · exact fun hd => (hf l (hS l hl)).2 (((hm.mul_left a).add_right s).dvd_iff.mp hd)

/-- For a reduced noninteger rational slope, prime indices can be found whose
outputs avoid every prime divisor of a prescribed modulus. The output is not
proved prime. -/
theorem rational_slope_prime_indices_coprime (a b : ℕ) (hb : 1 < b) (hab : a.Coprime b) (M : ℕ) (hM : 0 < M) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ (⌊((a : ℝ) / b * p)⌋₊).Coprime M := by
  obtain ⟨r, s, hfloor, hlocal⟩ := rational_slope_locally_admissible a b hb hab
  let Q : ℕ := b * M
  have hQ : Q ≠ 0 := mul_ne_zero (by omega) hM.ne'
  obtain ⟨t₀, _, ht₀⟩ := locally_admissible_avoids_finite_primes a b r s hlocal
    Q.primeFactors (fun l hl => Nat.prime_of_mem_primeFactors hl) 0
  let v : ℤ := b * t₀ + r
  have hcop : IsCoprime v (Q : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simp only [Int.natAbs_natCast]
    by_contra h
    obtain ⟨l, hl, hlv, hlQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact (ht₀ l (Nat.mem_primeFactors.mpr ⟨hl, hlQ, hQ⟩)).1
      (Int.natCast_dvd.mpr hlv)
  obtain ⟨p, hNp, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq N hQ hcop
  obtain ⟨k, hk⟩ := hmod.symm.dvd
  let t : ℤ := t₀ + M * k
  have hpeq : (p : ℤ) = b * t + r := by
    dsimp [v, Q] at hk
    dsimp [t]
    push_cast at hk
    nlinarith [hk]
  have hfl : ⌊((a : ℝ) / b * p)⌋ = (a : ℤ) * t + s := by
    convert hfloor t using 1
    rw [← hpeq]
    simp only [Int.cast_natCast]
  have hflnat : (⌊((a : ℝ) / b * p)⌋₊ : ℤ) = (a : ℤ) * t + s := by
    rw [Int.natCast_floor_eq_floor (by positivity), hfl]
  refine ⟨p, hNp, hp, ?_⟩
  by_contra h
  obtain ⟨l, hl, hlq, hlM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hlQ : l ∈ Q.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, hlM.trans (dvd_mul_left M b), hQ⟩
  have hMm : (M : ℤ) ≡ 0 [ZMOD (l : ℤ)] :=
    (Int.natCast_dvd_natCast.mpr hlM).modEq_zero_int
  have htm : t ≡ (t₀ : ℤ) [ZMOD (l : ℤ)] := by
    simpa [t] using (hMm.mul_right k).add_left (t₀ : ℤ)
  apply (ht₀ l hlQ).2
  apply ((htm.mul_left (a : ℤ)).add_right s).dvd_iff.mp
  rw [← hflnat]
  exact Int.natCast_dvd_natCast.mpr hlq

#print axioms rational_slope_prime_indices_coprime

#print axioms locally_admissible_avoids_finite_primes

#print axioms rational_slope_locally_admissible

#print axioms linear_pair_no_fixed_prime

#print axioms exists_affine_pair_ne_zero

end Explore972
