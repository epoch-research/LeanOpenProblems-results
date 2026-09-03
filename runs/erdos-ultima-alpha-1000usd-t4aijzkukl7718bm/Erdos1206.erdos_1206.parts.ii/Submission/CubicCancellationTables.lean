import Submission.CubicLocusProduct

/-! Kernel-checked local tables and transfer lemmas for an exact cancellation formula.
This file concerns arithmetic normalization, not positive density. -/

namespace Erdos1206.CubicBaseLocus

def locusLcm (a b t : ℤ) : ℕ :=
  Nat.lcm (locusDivisor0 a b t) (Nat.lcm (locusDivisor1 a b t) (locusDivisor2 a b t))

def extraTwo (a b t : ℤ) : ℕ :=
  if a % 2 = 1 ∧ b % 2 = 0 ∧ t % 2 = 1 then 1 else 0

def extraThree (_a b t : ℤ) : ℕ :=
  if t % 3 = 0 ∧ b % 3 ≠ 0 then 1 else 0

lemma locusLcm_pos {a b t : ℤ} (ht : 0 < t) : 0 < locusLcm a b t := by
  obtain ⟨h0,h1,h2⟩ := locus_divisors_pos (a := a) (b := b) ht
  exact Nat.lcm_pos h0 (Nat.lcm_pos h1 h2)

lemma pow_dvd_locusLcm_iff {a b t : ℤ} (ht : 0 < t) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    p^k ∣ locusLcm a b t ↔
      (((p : ℤ)^k ∣ t ∧ (p : ℤ)^k ∣ Q a b) ∨
        ((p : ℤ)^k ∣ b ∧ (p : ℤ)^k ∣ t^2+3*a^2) ∨
        ((p : ℤ)^k ∣ 2*a-b ∧ (p : ℤ)^k ∣ t^2+3*a^2)) := by
  obtain ⟨h0,h1,h2⟩ := locus_divisors_pos (a := a) (b := b) ht
  have hL : locusLcm a b t ≠ 0 := (locusLcm_pos ht).ne'
  rw [hp.pow_dvd_iff_le_factorization hL,locusLcm,
    Nat.factorization_lcm h0.ne' (Nat.lcm_pos h1 h2).ne',Nat.factorization_lcm h1.ne' h2.ne']
  simp only [Finsupp.sup_apply,le_max_iff]
  rw [← hp.pow_dvd_iff_le_factorization h0.ne',← hp.pow_dvd_iff_le_factorization h1.ne',
    ← hp.pow_dvd_iff_le_factorization h2.ne']
  simp only [locusDivisor0,locusDivisor1,locusDivisor2,Int.dvd_gcd_iff,Nat.cast_pow]

lemma val_mod_iff_dvd {m d : ℕ} [NeZero m] (hd : d ∣ m) (a : ℤ) :
    (a : ZMod m).val % d = 0 ↔ (d : ℤ) ∣ a := by
  have he : ((a : ZMod m).val : ℤ) % (d : ℤ) = a % (d : ℤ) := by
    rw [ZMod.val_intCast,Int.emod_emod_of_dvd a (by exact_mod_cast hd)]
  constructor
  · intro h
    have hZ : ((a : ZMod m).val : ℤ) % (d : ℤ) = 0 := by exact_mod_cast h
    rw [he] at hZ
    exact Int.dvd_of_emod_eq_zero hZ
  · intro h
    have hZ : ((a : ZMod m).val : ℤ) % (d : ℤ) = 0 := by
      rw [he,Int.emod_eq_zero_of_dvd h]
    exact_mod_cast hZ

lemma val_mod_eq_int_mod {m d : ℕ} [NeZero m] (hd : d ∣ m) (a : ℤ) :
    (((a : ZMod m).val % d : ℕ) : ℤ) = a % (d : ℤ) := by
  rw [Int.natCast_emod,ZMod.val_intCast,Int.emod_emod_of_dvd a (by exact_mod_cast hd)]

def commonResidueDivisibility {m : ℕ} (a b t : ZMod m) (d : ℕ) : Prop :=
  (A a b t).val % d = 0 ∧ (B a b t).val % d = 0 ∧
    (C a b t).val % d = 0 ∧ (D a b t).val % d = 0

def locusResidueDivisibility {m : ℕ} (a b t : ZMod m) (d : ℕ) : Prop :=
  (t.val % d = 0 ∧ (Q a b).val % d = 0) ∨
    (b.val % d = 0 ∧ (t^2+3*a^2).val % d = 0) ∨
    ((2*a-b).val % d = 0 ∧ (t^2+3*a^2).val % d = 0)

instance {m : ℕ} (a b t : ZMod m) (d : ℕ) :
    Decidable (commonResidueDivisibility a b t d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance {m : ℕ} (a b t : ZMod m) (d : ℕ) :
    Decidable (locusResidueDivisibility a b t d) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_table : ∀ a b t : ZMod 16,
    ¬ (a.val % 2 = 0 ∧ b.val % 2 = 0 ∧ t.val % 2 = 0) →
    ∀ k : Fin 5,
      commonResidueDivisibility a b t (2^k.val) ↔
        locusResidueDivisibility a b t
          (2^(k.val - if a.val % 2 = 1 ∧ b.val % 2 = 0 ∧ t.val % 2 = 1 then 1 else 0)) := by
  intro a
  unfold commonResidueDivisibility locusResidueDivisibility
  fin_cases a <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma three_table : ∀ a b t : ZMod 27,
    ¬ (a.val % 3 = 0 ∧ b.val % 3 = 0 ∧ t.val % 3 = 0) →
    ∀ k : Fin 4,
      commonResidueDivisibility a b t (3^k.val) ↔
        locusResidueDivisibility a b t
          (3^(k.val - if t.val % 3 = 0 ∧ b.val % 3 ≠ 0 then 1 else 0)) := by
  intro a
  unfold commonResidueDivisibility locusResidueDivisibility
  fin_cases a <;> decide +kernel

lemma commonResidueDivisibility_iff {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (a b t : ℤ) :
    commonResidueDivisibility (a : ZMod m) b t d ↔
      (d : ℤ) ∣ A a b t ∧ (d : ℤ) ∣ B a b t ∧
        (d : ℤ) ∣ C a b t ∧ (d : ℤ) ∣ D a b t := by
  have hA := val_mod_iff_dvd hd (A a b t)
  have hB := val_mod_iff_dvd hd (B a b t)
  have hC := val_mod_iff_dvd hd (C a b t)
  have hD := val_mod_iff_dvd hd (D a b t)
  simpa [commonResidueDivisibility,A,B,C,D,Q] using and_congr hA (and_congr hB (and_congr hC hD))

lemma locusResidueDivisibility_iff {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (a b t : ℤ) :
    locusResidueDivisibility (a : ZMod m) b t d ↔
      ((d : ℤ) ∣ t ∧ (d : ℤ) ∣ Q a b) ∨
        ((d : ℤ) ∣ b ∧ (d : ℤ) ∣ t^2+3*a^2) ∨
        ((d : ℤ) ∣ 2*a-b ∧ (d : ℤ) ∣ t^2+3*a^2) := by
  have ht := val_mod_iff_dvd hd t
  have hb := val_mod_iff_dvd hd b
  have hQ := val_mod_iff_dvd hd (Q a b)
  have hN := val_mod_iff_dvd hd (t^2+3*a^2)
  have hB := val_mod_iff_dvd hd (2*a-b)
  simpa [locusResidueDivisibility,Q] using
    or_congr (and_congr ht hQ) (or_congr (and_congr hb hN) (and_congr hB hN))

lemma certificate_common_divisibility {a b t g : ℤ} {x y z w : ℕ}
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) (d : ℕ) :
    (d : ℤ) ∣ A a b t ∧ (d : ℤ) ∣ B a b t ∧
        (d : ℤ) ∣ C a b t ∧ (d : ℤ) ∣ D a b t ↔ d ∣ g.natAbs := by
  rw [← certificate_gcd_exact hpRoots hA hB hC hD,Nat.dvd_gcd_iff,
    Int.dvd_gcd_iff,Int.dvd_gcd_iff]
  tauto

#print axioms two_table
#print axioms three_table

end Erdos1206.CubicBaseLocus
