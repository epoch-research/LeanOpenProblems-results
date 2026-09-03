import Submission.CubicIntegralCertificates

/-! Kernel-checked bounds at the two exceptional cancellation primes.
These are local arithmetic facts, not a global density estimate. -/

namespace Erdos1206.CubicBaseLocus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma common_zero_mod_sixteen :
    ∀ a b t : ZMod 16,
      A a b t = 0 → B a b t = 0 → C a b t = 0 → D a b t = 0 →
      a.val % 2 = 0 ∧ b.val % 2 = 0 ∧ t.val % 2 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma common_zero_mod_twentyseven :
    ∀ a b t : ZMod 27,
      A a b t = 0 → B a b t = 0 → C a b t = 0 → D a b t = 0 →
      a.val % 3 = 0 ∧ b.val % 3 = 0 ∧ t.val % 3 = 0 := by
  decide +kernel

#print axioms common_zero_mod_sixteen
#print axioms common_zero_mod_twentyseven


private lemma dvd_of_val_mod_eq_zero {p m : ℕ} [NeZero m]
    (hpm : p ∣ m) (a : ℤ) (h : (a : ZMod m).val % p = 0) : (p : ℤ) ∣ a := by
  have hZ : ((a : ZMod m).val : ℤ) % (p : ℤ) = 0 := by exact_mod_cast h
  rw [ZMod.val_intCast,Int.emod_emod_of_dvd a (by exact_mod_cast hpm)] at hZ
  exact Int.dvd_of_emod_eq_zero hZ

private lemma no_common_divisor_of_mod_table {p m : ℕ} [NeZero m]
    (hp : p.Prime) (hpm : p ∣ m)
    (htable : ∀ a b t : ZMod m,
      A a b t = 0 → B a b t = 0 → C a b t = 0 → D a b t = 0 →
      a.val % p = 0 ∧ b.val % p = 0 ∧ t.val % p = 0)
    {a b t : ℤ} (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1) :
    ¬ ((m : ℤ) ∣ A a b t ∧ (m : ℤ) ∣ B a b t ∧
      (m : ℤ) ∣ C a b t ∧ (m : ℤ) ∣ D a b t) := by
  rintro ⟨hA,hB,hC,hD⟩
  have hA' : A (a : ZMod m) b t = 0 := by
    simpa [A,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (A a b t) m).mpr hA
  have hB' : B (a : ZMod m) b t = 0 := by
    simpa [B,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (B a b t) m).mpr hB
  have hC' : C (a : ZMod m) b t = 0 := by
    simpa [C,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (C a b t) m).mpr hC
  have hD' : D (a : ZMod m) b t = 0 := by
    simpa [D,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (D a b t) m).mpr hD
  obtain ⟨ha,hb,ht⟩ := htable a b t hA' hB' hC' hD'
  exact triple_primitive_at_prime hprim hp
    ⟨dvd_of_val_mod_eq_zero hpm a ha,dvd_of_val_mod_eq_zero hpm b hb,
      dvd_of_val_mod_eq_zero hpm t ht⟩

/-- The 2-adic valuation of a primitive raw coordinate gcd is at most three. -/
lemma not_sixteen_dvd_common {a b t : ℤ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1) :
    ¬ ((16 : ℤ) ∣ A a b t ∧ (16 : ℤ) ∣ B a b t ∧
      (16 : ℤ) ∣ C a b t ∧ (16 : ℤ) ∣ D a b t) :=
  no_common_divisor_of_mod_table (by norm_num : Nat.Prime 2) (by norm_num)
    common_zero_mod_sixteen hprim

/-- The 3-adic valuation of a primitive raw coordinate gcd is at most two. -/
lemma not_twentyseven_dvd_common {a b t : ℤ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1) :
    ¬ ((27 : ℤ) ∣ A a b t ∧ (27 : ℤ) ∣ B a b t ∧
      (27 : ℤ) ∣ C a b t ∧ (27 : ℤ) ∣ D a b t) :=
  no_common_divisor_of_mod_table (by norm_num : Nat.Prime 3) (by norm_num)
    common_zero_mod_twentyseven hprim

lemma certificate_small_prime_bounds {a b t g : ℤ} {x y z w : ℕ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    ¬ (16 : ℤ) ∣ g ∧ ¬ (27 : ℤ) ∣ g := by
  constructor
  · intro h
    apply not_sixteen_dvd_common hprim
    rw [hA,hB,hC,hD]
    exact ⟨h.mul_right _,h.mul_right _,h.mul_right _,h.mul_right _⟩
  · intro h
    apply not_twentyseven_dvd_common hprim
    rw [hA,hB,hC,hD]
    exact ⟨h.mul_right _,h.mul_right _,h.mul_right _,h.mul_right _⟩

#print axioms not_sixteen_dvd_common
#print axioms not_twentyseven_dvd_common
#print axioms certificate_small_prime_bounds

end Erdos1206.CubicBaseLocus
