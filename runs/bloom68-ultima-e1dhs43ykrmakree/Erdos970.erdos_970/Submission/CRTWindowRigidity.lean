import Submission.CRTWindowArithmetic

/-!
# Complete finite CRT counts and rigidity of subinterval counts

The theorems here strengthen the earlier remainder-one pair implication to
all intersections. They also show that exact length-`p` singleton window counts
already recover a residue column, rather than merely improving its density.
This file is independent of `Submission.Spec`.
-/

namespace IntegerSieve.CRTWindow

open Finset

lemma modEq_modulus_iff {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p) (n r : ℕ) :
    n ≡ r [MOD modulus S] ↔ ∀ p ∈ S, n ≡ r [MOD p] := by
  induction S using Finset.induction_on with
  | empty => simp [modulus, Nat.modEq_one]
  | @insert p S hp ih =>
    have hp' := hprime p (Finset.mem_insert_self _ _)
    have hS : ∀ q ∈ S, Nat.Prime q := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hcp : p.Coprime (modulus S) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hp' (hS q hq)).mpr
      exact fun heq => hp (heq ▸ hq)
    rw [show modulus (insert p S) = p * modulus S by simp [modulus, hp],
      ← Nat.modEq_and_modEq_iff_modEq_mul hcp, ih hS]
    simp

/-- Exact counts for EVERY intersection, with one coherent CRT root per subset. -/
theorem intersection_count_exact {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) (L : ℕ) (a : ℕ → ℕ)
    (r : ℕ) (hr : r < modulus S) (ha : ∀ p ∈ S, r ≡ a p [MOD p]) :
    Nat.count (fun n => ∀ p ∈ S, n ≡ a p [MOD p]) L =
      L / modulus S + if r < L % modulus S then 1 else 0 := by
  have heq : (fun n => ∀ p ∈ S, n ≡ a p [MOD p]) =
      (fun n => n ≡ r [MOD modulus S]) := by
    funext n
    apply propext
    rw [modEq_modulus_iff hprime]
    constructor
    · intro h p hp
      exact (h p hp).trans (ha p hp).symm
    · intro h p hp
      exact (h p hp).trans (ha p hp)
  simpa only [heq, Nat.mod_eq_of_lt hr] using
    (Nat.count_modEq_card L (modulus_pos hprime) r)

lemma exists_crt_root {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p) (a : ℕ → ℕ) :
    ∃ r : ℕ, r < modulus S ∧ ∀ p ∈ S, r ≡ a p [MOD p] := by
  have hn : ∀ p ∈ S, p ≠ 0 := fun p hp => (hprime p hp).ne_zero
  have hc : Set.Pairwise (↑S : Set ℕ) Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  let r := Nat.chineseRemainderOfFinset a (fun p : ℕ => p) S hn hc
  exact ⟨r, Nat.chineseRemainderOfFinset_lt_prod a (fun p : ℕ => p) hn hc, r.property⟩

/-- At remainder one the entire intersection rounding bit, not just one
implication, is determined: it is the AND of the zero-residue singleton bits. -/
theorem remainder_one_intersection {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) (L : ℕ) (hL : L % modulus S = 1)
    (a : ℕ → ℕ) :
    Nat.count (fun n => ∀ p ∈ S, n ≡ a p [MOD p]) L =
      L / modulus S + if ∀ p ∈ S, a p % p = 0 then 1 else 0 := by
  classical
  obtain ⟨r, hr, ha⟩ := exists_crt_root hprime a
  have hz : r < 1 ↔ ∀ p ∈ S, a p % p = 0 := by
    constructor
    · intro h p hp
      have hr0 : r = 0 := by omega
      simpa only [hr0, Nat.ModEq, Nat.zero_mod] using (ha p hp).symm
    · intro h
      have hd : modulus S ∣ r := (modulus_dvd_iff hprime r).mpr fun p hp =>
        Nat.dvd_of_mod_eq_zero ((show r % p = a p % p from ha p hp).trans (h p hp))
      have hm := Nat.mod_eq_zero_of_dvd hd
      rw [Nat.mod_eq_of_lt hr] at hm
      omega
  rw [intersection_count_exact hprime L a r hr ha, hL]
  simp only [hz]

lemma modulus_one_lt {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) : 1 < modulus S := by
  obtain ⟨p, hp⟩ := hne
  exact (hprime p hp).one_lt.trans_le
    (Nat.le_of_dvd (modulus_pos hprime) (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp))

/-- A common favorable length gives the complete Boolean formula on every
nonempty subintersection of the selected primes. -/
theorem common_remainder_one {P : Finset ℕ} (hprime : ∀ p ∈ P, Nat.Prime p)
    (L : ℕ) (hL : L % modulus P = 1) (a : ℕ → ℕ)
    {S : Finset ℕ} (hSP : S ⊆ P) (hne : S.Nonempty) :
    Nat.count (fun n => ∀ p ∈ S, n ≡ a p [MOD p]) L =
      L / modulus S + if ∀ p ∈ S, a p % p = 0 then 1 else 0 := by
  have hS : ∀ p ∈ S, Nat.Prime p := fun p hp => hprime p (hSP hp)
  have hd : modulus S ∣ modulus P := (modulus_dvd_iff hS _).mpr fun p hp =>
    Finset.dvd_prod_of_mem (fun q : ℕ => q) (hSP hp)
  have hm := Nat.mod_mod_of_dvd L hd
  rw [hL, Nat.mod_eq_of_lt (modulus_one_lt hS hne)] at hm
  exact remainder_one_intersection hS L hm.symm a

/-- The sum of all nonempty rounding contributions in a favorable block
collapses to `-1` or `0`, regardless of how many singleton bits are maximal. -/
theorem alternating_rounding_collapse (P G : Finset ℕ) (hGP : G ⊆ P) :
    (∑ S ∈ P.powerset,
      if S.Nonempty ∧ S ⊆ G then (-1 : ℤ) ^ S.card else 0) =
      if G.Nonempty then -1 else 0 := by
  have hfull : (∑ S ∈ P.powerset, if S ⊆ G then (-1 : ℤ) ^ S.card else 0) =
      if G = ∅ then 1 else 0 := by
    have hreduce : (∑ S ∈ P.powerset, if S ⊆ G then (-1 : ℤ) ^ S.card else 0) =
        ∑ S ∈ G.powerset, (-1 : ℤ) ^ S.card := by
      calc
        _ = ∑ S ∈ G.powerset, if S ⊆ G then (-1 : ℤ) ^ S.card else 0 := by
          symm
          apply Finset.sum_subset (Finset.powerset_mono.mpr hGP)
          intro S _ hSG
          simp only [Finset.mem_powerset] at hSG
          simp [hSG]
        _ = _ := Finset.sum_congr rfl fun S hS => by simp [Finset.mem_powerset.mp hS]
    rw [hreduce]
    have ht := alternating_upper_sum G ∅
    by_cases hG : G = ∅
    · simp [hG]
    · simpa [hG, Ne.symm hG] using ht
  have hsplit : (∑ S ∈ P.powerset, if S ⊆ G then (-1 : ℤ) ^ S.card else 0) =
      (∑ S ∈ P.powerset,
        if S.Nonempty ∧ S ⊆ G then (-1 : ℤ) ^ S.card else 0) + 1 := by
    calc
      _ = ∑ S ∈ P.powerset,
          ((if S.Nonempty ∧ S ⊆ G then (-1 : ℤ) ^ S.card else 0) +
            if S = ∅ then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S = ∅
        · simp [hS]
        · simp [Finset.nonempty_iff_ne_empty, hS]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit] at hfull
  by_cases hG : G = ∅
  · simp [hG] at hfull ⊢
    exact hfull
  · simp [hG, Finset.nonempty_iff_ne_empty] at hfull ⊢
    omega

/-- Count of a Boolean column on the subinterval `[a,a+len)`. -/
def windowCount (b : ℕ → Prop) [DecidablePred b] (a len : ℕ) : ℕ :=
  Nat.count (fun j => b (a + j)) len

/-- Equal counts on consecutive length-`p` windows force equality of the
entering and leaving bits. -/
lemma one_windows_force_period {b : ℕ → Prop} [DecidablePred b] {L p : ℕ}
    (h : ∀ a : ℕ, a + p ≤ L → windowCount b a p = 1)
    (a : ℕ) (ha : a + p < L) : b (a + p) ↔ b a := by
  have h₁ := Nat.count_add (p := b) a p
  have h₂ := Nat.count_add (p := b) (a + 1) p
  have h₃ := Nat.count_succ (p := b) a
  have h₄ := Nat.count_succ (p := b) (a + p)
  change Nat.count b (a + p) = Nat.count b a + windowCount b a p at h₁
  change Nat.count b (a + 1 + p) = Nat.count b (a + 1) + windowCount b (a + 1) p at h₂
  rw [h a (by omega)] at h₁
  rw [h (a + 1) (by omega)] at h₂
  have heq : a + 1 + p = a + p + 1 := by omega
  rw [heq] at h₂
  by_cases hb : b a <;> by_cases hc : b (a + p) <;> simp_all

/-- Exact counts at just one scale suffice to recover the full residue column.
No intersection bounds, covering assumption, or primality assumption is used. -/
theorem one_windows_iff_residue {b : ℕ → Prop} [DecidablePred b] {L p : ℕ}
    (hp : 0 < p) (hpL : p ≤ L) :
    (∀ a : ℕ, a + p ≤ L → windowCount b a p = 1) ↔
      ∃ r : ℕ, r < p ∧ ∀ i : ℕ, i < L → (b i ↔ i % p = r) := by
  constructor
  · intro h
    have hred : ∀ i : ℕ, i < L → (b i ↔ b (i % p)) := by
      intro i
      induction i using Nat.strong_induction_on with
      | h i ih =>
        intro hi
        by_cases hip : i < p
        · rw [Nat.mod_eq_of_lt hip]
        · have hpi : p ≤ i := by omega
          have hlt : i - p < i := by omega
          have heq : i - p + p = i := by omega
          have hperiod := one_windows_force_period h (i - p) (by omega)
          rw [heq] at hperiod
          have hm : (i - p) % p = i % p := by
            simpa only [heq] using (Nat.add_mod_right (i - p) p).symm
          exact hperiod.trans ((ih (i - p) hlt (by omega)).trans (by rw [hm]))
    have hc : Nat.count b p = 1 := by simpa [windowCount] using h 0 (by simpa using hpL)
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_one] at hc
    obtain ⟨r, hr⟩ := hc
    have hrmem : r ∈ (Finset.range p).filter b := by rw [hr]; simp
    obtain ⟨hrp, hbr⟩ := Finset.mem_filter.mp hrmem
    have hrlt : r < p := Finset.mem_range.mp hrp
    refine ⟨r, hrlt, ?_⟩
    intro i hi
    rw [hred i hi]
    constructor
    · intro hb
      have hm : i % p ∈ (Finset.range p).filter b :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp), hb⟩
      rwa [hr, Finset.mem_singleton] at hm
    · intro hm
      simpa [hm] using hbr
  · rintro ⟨r, hr, hb⟩ a ha
    have hc : windowCount b a p = Nat.count (fun j => a + j ≡ r [MOD p]) p := by
      simp only [windowCount, Nat.count_eq_card_filter_range]
      congr 1
      apply Finset.filter_congr
      intro j hj
      have hjp := Finset.mem_range.mp hj
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hb (a + j) (by omega)
    rw [hc]
    have hadd := Nat.count_add (p := fun n => n ≡ r [MOD p]) a p
    have hbig := Nat.count_modEq_card (a + p) hp r
    have hsmall := Nat.count_modEq_card a hp r
    rw [Nat.add_div_right a hp, Nat.add_mod_right] at hbig
    omega

end IntegerSieve.CRTWindow

#print axioms IntegerSieve.CRTWindow.intersection_count_exact
#print axioms IntegerSieve.CRTWindow.common_remainder_one
#print axioms IntegerSieve.CRTWindow.alternating_rounding_collapse
#print axioms IntegerSieve.CRTWindow.one_windows_iff_residue
