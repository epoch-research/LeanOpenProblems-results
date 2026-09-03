import FormalConjecturesUtil

/-! Local admissibility checks for rational slopes. These do not assert simultaneous primality. -/
namespace Erdos972Local
set_option maxHeartbeats 1000000

lemma coprime_of_determinant {a b r c t : ℕ}
    (he : a * r = b * c + t) (hat : a.Coprime t) (hbt : b.Coprime t) :
    b.Coprime r ∧ a.Coprime c := by
  constructor
  · change Nat.gcd b r = 1
    apply Nat.eq_one_of_dvd_coprimes hbt (Nat.gcd_dvd_left b r)
    apply (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_left b r) c)).mpr
    rw [← he]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right b r) a
  · change Nat.gcd a c = 1
    apply Nat.eq_one_of_dvd_coprimes hat (Nat.gcd_dvd_left a c)
    apply (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_right a c) b)).mpr
    rw [← he]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a c) r

/-- A suitable residue has determinant either one, or two to remove the parity obstruction. -/
lemma exists_primitive_residue {a b : ℕ} (hab : a.Coprime b) (hb : 1 < b) :
    ∃ r c t : ℕ, 0 < r ∧ r < b ∧ 0 < t ∧ t < b ∧
      a * r = b * c + t ∧ b.Coprime r ∧ a.Coprime c ∧
      ((Odd a ∧ Odd b) → Even t) := by
  have ht : ∃ t : ℕ, 0 < t ∧ t < b ∧ a.Coprime t ∧ b.Coprime t ∧
      ((Odd a ∧ Odd b) → Even t) := by
    by_cases ho : Odd a ∧ Odd b
    · refine ⟨2, by omega, ?_, ho.1.coprime_two_right, ho.2.coprime_two_right, ?_⟩
      · have hodd := Nat.odd_iff.mp ho.2
        omega
      · intro _
        decide
    · exact ⟨1, by omega, hb, Nat.coprime_one_right a, Nat.coprime_one_right b,
        fun h => (ho h).elim⟩
  obtain ⟨t, ht0, htb, hat, hbt, hte⟩ := ht
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab hb
  let r := t * u % b
  have hrb : r < b := Nat.mod_lt _ (by omega)
  have hrmod : a * r % b = t := by
    dsimp [r]
    rw [Nat.mul_mod_mod]
    calc
      a * (t * u) % b = t * (a * u) % b := by congr 1; ring
      _ = t * (a * u % b) % b := (Nat.mul_mod_mod _ _ _).symm
      _ = t := by rw [hu, mul_one, Nat.mod_eq_of_lt htb]
  have hr0 : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    rw [hz] at hrmod
    simp at hrmod
    omega
  have he : a * r = b * (a * r / b) + t := by
    have h := Nat.div_add_mod (a * r) b
    rw [hrmod] at h
    omega
  have hc := coprime_of_determinant he hat hbt
  exact ⟨r, a * r / b, t, hr0, hrb, ht0, htb, he, hc.1, hc.2, hte⟩

/-- Two nonzero affine forms cannot vanish between them at all three points 0, 1, 2
in a field of characteristic different from two. -/
lemma three_trials {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (a b c d : F) (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ k : ℕ, k ≤ 2 ∧ a * k + b ≠ 0 ∧ c * k + d ≠ 0 := by
  have hpair (x y : F) (hxy : x ≠ 0 ∨ y ≠ 0) :
      ¬ (y = 0 ∧ x + y = 0) ∧
      ¬ (y = 0 ∧ x * 2 + y = 0) ∧
      ¬ (x + y = 0 ∧ x * 2 + y = 0) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hy, he⟩
      have hx : x = 0 := by linear_combination he - hy
      exact hxy.elim (fun h => h hx) (fun h => h hy)
    · rintro ⟨hy, he⟩
      have hx2 : x * 2 = 0 := by linear_combination he - hy
      have hx := (mul_eq_zero.mp hx2).resolve_right h2
      exact hxy.elim (fun h => h hx) (fun h => h hy)
    · rintro ⟨he₁, he₂⟩
      have hx : x = 0 := by linear_combination he₂ - he₁
      have hy : y = 0 := by linear_combination 2 * he₁ - he₂
      exact hxy.elim (fun h => h hx) (fun h => h hy)
  by_contra h
  push_neg at h
  have hbad (k : ℕ) (hk : k ≤ 2) : a * k + b = 0 ∨ c * k + d = 0 := by
    by_cases ha : a * k + b = 0
    · exact Or.inl ha
    · exact Or.inr (h k hk ha)
  have h0 := hbad 0 (by omega)
  have h1 := hbad 1 (by omega)
  have htwo := hbad 2 (by omega)
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_add, mul_one] at h0 h1 htwo
  have ha := hpair a b hab
  have hc := hpair c d hcd
  tauto

lemma coprime_cast_nonzero {a b ℓ : ℕ} (hab : a.Coprime b) (hℓ : ℓ.Prime) :
    (a : ZMod ℓ) ≠ 0 ∨ (b : ZMod ℓ) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hℓ.ne_one (Nat.eq_one_of_dvd_coprimes hab
    ((ZMod.natCast_eq_zero_iff a ℓ).mp h.1)
    ((ZMod.natCast_eq_zero_iff b ℓ).mp h.2))

/-- Primitive affine forms have a common locally allowed residue at every odd prime. -/
lemma odd_prime_local_residue {a b r c ℓ : ℕ}
    (hbr : b.Coprime r) (hac : a.Coprime c) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ∃ k : ℕ, k ≤ 2 ∧ ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  have ht : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have hd : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp h
    exact hℓ2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hℓ.ne_one)
  obtain ⟨k, hk, hb, ha⟩ := three_trials ht
    (b : ZMod ℓ) r a c (coprime_cast_nonzero hbr hℓ) (coprime_cast_nonzero hac hℓ)
  refine ⟨k, hk, ?_, ?_⟩
  · intro hd
    apply hb
    exact_mod_cast (ZMod.natCast_eq_zero_iff (b * k + r) ℓ).mpr hd
  · intro hd
    apply ha
    exact_mod_cast (ZMod.natCast_eq_zero_iff (a * k + c) ℓ).mpr hd

lemma coprime_not_both_even {a b : ℕ} (hab : a.Coprime b) :
    ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
  rintro ⟨ha, hb⟩
  have h2 := Nat.eq_one_of_dvd_coprimes hab
    (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
  omega

/-- The determinant choice also removes the only possible two-root obstruction, at two. -/
lemma two_local_residue {a b r c t : ℕ}
    (he : a * r = b * c + t) (hbr : b.Coprime r) (hac : a.Coprime c)
    (hte : (Odd a ∧ Odd b) → Even t) :
    ∃ k : ℕ, k ≤ 1 ∧ ¬ 2 ∣ b * k + r ∧ ¬ 2 ∣ a * k + c := by
  have hcompat : a % 2 = 1 → b % 2 = 1 → r % 2 = c % 2 := by
    intro ha hb
    have ht := Nat.even_iff.mp (hte ⟨Nat.odd_iff.mpr ha, Nat.odd_iff.mpr hb⟩)
    have hm := congrArg (fun n : ℕ => n % 2) he
    simp only [Nat.add_mod, Nat.mul_mod, ha, hb, ht, one_mul, add_zero, Nat.mod_mod] at hm
    exact hm
  have hbr2 := coprime_not_both_even hbr
  have hac2 := coprime_not_both_even hac
  by_cases h0 : ¬ 2 ∣ r ∧ ¬ 2 ∣ c
  · exact ⟨0, by omega, by simpa using h0.1, by simpa using h0.2⟩
  · refine ⟨1, le_rfl, ?_, ?_⟩ <;>
      simp only [mul_one, Nat.dvd_iff_mod_eq_zero] at * <;> omega

/-- Every reduced noninteger positive rational slope has a residue class for which
no prime is a fixed obstruction to simultaneous primality of the two affine forms. -/
theorem rational_slope_locally_admissible {a b : ℕ} (hab : a.Coprime b) (hb : 1 < b) :
    ∃ r c : ℕ, 0 < r ∧ r < b ∧ c = a * r / b ∧
      (∀ k : ℕ, ⌊((a : ℝ) / b) * (b * k + r)⌋₊ = a * k + c) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, k ≤ 2 ∧
        ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c := by
  obtain ⟨r, c, t, hr0, hrb, ht0, htb, he, hbr, hac, hte⟩ :=
    exists_primitive_residue hab hb
  have hb0 : 0 < b := by omega
  have hc : c = a * r / b := by
    rw [he, Nat.mul_add_div hb0, Nat.div_eq_of_lt htb, add_zero]
  refine ⟨r, c, hr0, hrb, hc, ?_, ?_⟩
  · intro k
    have hbr : (0 : ℝ) < b := Nat.cast_pos.mpr hb0
    have htr : (t : ℝ) < b := Nat.cast_lt.mpr htb
    have her : (a : ℝ) * r = b * c + t := by exact_mod_cast he
    apply (Nat.floor_eq_iff (by positivity)).mpr
    push_cast
    rw [div_mul_eq_mul_div]
    constructor
    · apply (le_div_iff₀ hbr).mpr
      nlinarith
    · apply (div_lt_iff₀ hbr).mpr
      nlinarith
  · intro ℓ hℓ
    by_cases h2 : ℓ = 2
    · subst ℓ
      obtain ⟨k, hk, hkr, hkc⟩ := two_local_residue he hbr hac hte
      exact ⟨k, hk.trans (by omega), hkr, hkc⟩
    · exact odd_prime_local_residue hbr hac hℓ h2

/-- Local admissibility can be combined for every prime divisor of a fixed modulus. -/
lemma admissible_crt {a b r c : ℕ}
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ k : ℕ, (b * k + r).Coprime M ∧ (a * k + c).Coprime M := by
  classical
  have hchoose : ∀ ℓ : ℕ, ∃ k : ℕ,
      ℓ.Prime → ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c := by
    intro ℓ
    by_cases hp : ℓ.Prime
    · obtain ⟨k, hk⟩ := hloc ℓ hp
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose f hf using hchoose
  have hs : ∀ ℓ ∈ M.primeFactors, id ℓ ≠ 0 :=
    fun ℓ hℓ => (Nat.prime_of_mem_primeFactors hℓ).ne_zero
  have hpair : (M.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro ℓ hℓ m hm hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hℓ)
      (Nat.prime_of_mem_primeFactors hm)).mpr hne
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset f id M.primeFactors hs hpair
  refine ⟨k, ?_, ?_⟩
  · apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro ℓ hℓ hℓM hdiv
    have hcon := hk ℓ (hℓ.mem_primeFactors hℓM hM)
    exact (hf ℓ hℓ).1 ((((hcon.mul_left b).add_right r).dvd_iff (dvd_refl ℓ)).mp hdiv)
  · apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro ℓ hℓ hℓM hdiv
    have hcon := hk ℓ (hℓ.mem_primeFactors hℓM hM)
    exact (hf ℓ hℓ).2 ((((hcon.mul_left a).add_right c).dvd_iff (dvd_refl ℓ)).mp hdiv)

lemma primitive_of_admissible {a b r c : ℕ}
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c) :
    b.Coprime r := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓb hℓr
  obtain ⟨k, hk, _⟩ := hloc ℓ hℓ
  exact hk (dvd_add (dvd_mul_of_dvd_left hℓb k) hℓr)

/-- Dirichlet's theorem provides prime values of the first form while the second
avoids all prime divisors of a fixed modulus. This does not make the second form prime. -/
lemma admissible_prime_input {a b r c : ℕ} (hb : b ≠ 0)
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c)
    (M : ℕ) (hM : M ≠ 0) (N : ℕ) :
    ∃ k : ℕ, N < b * k + r ∧ (b * k + r).Prime ∧ (a * k + c).Coprime M := by
  obtain ⟨k₀, hk₀, hc₀⟩ := admissible_crt hloc M hM
  have hbr := primitive_of_admissible hloc
  have hbase : (b * k₀ + r).Coprime (b * M) := by
    apply Nat.coprime_mul_iff_right.mpr
    exact ⟨by simpa using hbr.symm, hk₀⟩
  obtain ⟨p, hp, hprime, hcon⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max N (b * k₀ + r)) (mul_ne_zero hb hM) hbase
  have hbp : b * k₀ + r ≤ p := (le_max_right _ _).trans hp.le
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hbp).mp hcon.symm
  have he : b * (k₀ + M * t) + r = p := by rw [ht]; ring
  refine ⟨k₀ + M * t, ?_, ?_, ?_⟩
  · rw [he]
    exact (le_max_left _ _).trans_lt hp
  · rwa [he]
  · have hform : a * (k₀ + M * t) + c = (a * k₀ + c) + M * (a * t) := by ring
    rw [hform]
    simpa using hc₀

/-- No finite set of possible prime divisors can obstruct all prime inputs at a
reduced noninteger rational slope. -/
theorem rational_prime_inputs_coprime_outputs {a b : ℕ}
    (hab : a.Coprime b) (hb : 1 < b) (M : ℕ) (hM : M ≠ 0) :
    {p : ℕ | p.Prime ∧ (⌊((a : ℝ) / b) * p⌋₊).Coprime M}.Infinite := by
  obtain ⟨r, c, _, _, _, hfloor, hlocal⟩ := rational_slope_locally_admissible hab hb
  have hloc : ∀ ℓ : ℕ, ℓ.Prime → ∃ k : ℕ, ¬ ℓ ∣ b * k + r ∧ ¬ ℓ ∣ a * k + c := by
    intro ℓ hℓ
    obtain ⟨k, _, hk⟩ := hlocal ℓ hℓ
    exact ⟨k, hk⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hNk, hprime, hcoprime⟩ := admissible_prime_input (by omega) hloc M hM N
  refine ⟨b * k + r, ⟨hprime, ?_⟩, hNk⟩
  simpa only [Nat.cast_add, Nat.cast_mul, hfloor k] using hcoprime

#print axioms exists_primitive_residue
#print axioms odd_prime_local_residue
#print axioms rational_slope_locally_admissible
#print axioms rational_prime_inputs_coprime_outputs
end Erdos972Local
