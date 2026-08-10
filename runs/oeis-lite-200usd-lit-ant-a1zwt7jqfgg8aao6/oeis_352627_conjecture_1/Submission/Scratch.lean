import FormalConjectures.Util.ProblemImports

open Nat

lemma dvd_of_dvd_sq_add_two_sq {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7)
    (a b : ℕ) (hdvd : p ∣ a ^ 2 + 2 * b ^ 2) : p ∣ a ∧ p ∣ b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; simp at hp8
  have hnsq : ¬ IsSquare (-2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_two_iff hp2]
    rcases hp8 with h | h <;> omega
  have key : (a : ZMod p) ^ 2 + 2 * (b : ZMod p) ^ 2 = 0 := by
    have : ((a ^ 2 + 2 * b ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hdvd
    push_cast at this; linear_combination this
  have hb : (b : ZMod p) = 0 := by
    by_contra hbne
    apply hnsq
    refine ⟨(a : ZMod p) * (b : ZMod p)⁻¹, ?_⟩
    have hbinv : (b : ZMod p) * (b:ZMod p)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ ((isUnit_iff_ne_zero).mpr hbne)
    have hval : (a:ZMod p)^2 = -2 * (b:ZMod p)^2 := by linear_combination key
    have : (a:ZMod p) * (b:ZMod p)⁻¹ * ((a:ZMod p) * (b:ZMod p)⁻¹)
        = (a:ZMod p)^2 * ((b:ZMod p)⁻¹ * (b:ZMod p)⁻¹) := by ring
    rw [this, hval]
    have : (-2 * (b:ZMod p)^2) * ((b:ZMod p)⁻¹ * (b:ZMod p)⁻¹)
        = -2 * ((b:ZMod p) * (b:ZMod p)⁻¹) * ((b:ZMod p) * (b:ZMod p)⁻¹) := by ring
    rw [this, hbinv]; ring
  have hbdvd : p ∣ b := by rwa [← ZMod.natCast_eq_zero_iff]
  refine ⟨?_, hbdvd⟩
  have hz : (a : ZMod p) ^ 2 = 0 := by rw [hb] at key; simpa using key
  have : (a : ZMod p) = 0 := pow_eq_zero_iff (by norm_num) |>.mp hz
  rwa [← ZMod.natCast_eq_zero_iff]

-- Lemma B: representable numbers have even p-adic valuation (p ≡ 5,7 mod 8).
lemma even_padicValNat_of_repr {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) :
    ∀ m : ℕ, (∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = m) → Even (padicValNat p m) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    rintro ⟨a, b, hab⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp [padicValNat.zero]
    · by_cases hdvd : p ∣ m
      · -- descent
        obtain ⟨ha, hb⟩ := dvd_of_dvd_sq_add_two_sq hp hp8 a b (hab ▸ hdvd)
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        set m' := a' ^ 2 + 2 * b' ^ 2 with hm'
        have hfac : m = p ^ 2 * m' := by rw [← hab]; ring
        have hm'pos : 0 < m' := by
          rcases Nat.eq_zero_or_pos m' with h | h
          · rw [h, mul_zero] at hfac; omega
          · exact h
        have hm'lt : m' < m := by
          rw [hfac]
          have : 1 < p ^ 2 := by nlinarith [hp1]
          calc m' = 1 * m' := (one_mul m').symm
            _ < p ^ 2 * m' := (Nat.mul_lt_mul_right hm'pos).mpr this
        have hev' : Even (padicValNat p m') := IH m' hm'lt ⟨a', b', rfl⟩
        have hval : padicValNat p m = 2 + padicValNat p m' := by
          rw [hfac, padicValNat.mul (pow_ne_zero 2 hp.pos.ne') hm'pos.ne',
            padicValNat.prime_pow]
        rw [hval]; exact (Nat.even_add).mpr (by simp [hev'])
      · rw [padicValNat.eq_zero_of_not_dvd hdvd]; exact ⟨0, rfl⟩

-- Final: numbers with an odd-power prime ≡ 5,7 mod 8 are not of the form a²+2b².
lemma not_repr_of_odd_val {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7)
    (m k u : ℕ) (hk : Odd k) (hu : ¬ p ∣ u) (hm : m = p ^ k * u) :
    ¬ ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = m := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hrepr
  have hev := even_padicValNat_of_repr hp hp8 m hrepr
  have hupos : 0 < u := Nat.pos_of_ne_zero (fun h => hu (h ▸ dvd_zero p))
  have hval : padicValNat p m = k := by
    rw [hm, padicValNat.mul (pow_ne_zero k hp.pos.ne') hupos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu, add_zero]
  rw [hval] at hev
  exact (Nat.not_even_iff_odd.mpr hk) hev


example : ¬ ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = 5 :=
  not_repr_of_odd_val (p := 5) (by norm_num) (by decide) 5 1 1
    (by decide) (by decide) (by norm_num)

example : ¬ ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = 350 :=
  not_repr_of_odd_val (p := 7) (by norm_num) (by decide) 350 1 50
    (by decide) (by decide) (by norm_num)
