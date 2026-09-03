import Submission.PresentCylinderArithmetic

/-! Pure-avoiding lifts in each prescribed first-digit branch. All cardinality
bounds are finite and exact. This is preparation for random restrictions, not
an unrestricted odd-covering obstruction. -/
namespace Erdos7IndependentPureLifts
open scoped BigOperators
open Erdos7PresentCylinderArithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000

def higherLevels (E : ℕ) : Finset ℕ := (Finset.range (E+1)).filter (2 ≤ ·)

def higherBad (p E : ℕ) [NeZero p] (a : ℕ → ℤ) : Finset (ZMod (p^E)) :=
  (higherLevels E).biUnion (fun e => cylinder p E e (a e))

def branchGood (p E : ℕ) [NeZero p] (a : ℕ → ℤ) (b : ℤ) :
    Finset (ZMod (p^E)) := cylinder p E 1 b \ higherBad p E a

/-- The sum of all higher pure-cylinder sizes, without any disjointness
assumption, is at most N/(p*(p-1)). -/
lemma higherBad_card_le (p E : ℕ) [NeZero p] (hp : 1 < p) (a : ℕ → ℤ) :
    ((higherBad p E a).card : ℚ) ≤
      (Fintype.card (ZMod (p^E)) : ℚ)/(p*(p-1)) := by
  have hcard : (higherBad p E a).card ≤
      ∑ e ∈ higherLevels E, (cylinder p E e (a e)).card := Finset.card_biUnion_le
  have hq : ((higherBad p E a).card : ℚ) ≤
      ∑ e ∈ higherLevels E, ((cylinder p E e (a e)).card : ℚ) := by
    exact_mod_cast hcard
  have hsum : (∑ e ∈ higherLevels E, ((cylinder p E e (a e)).card : ℚ)) =
      (Fintype.card (ZMod (p^E)) : ℚ)*∑ e ∈ higherLevels E, ((p : ℚ)⁻¹)^e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have heE : e ≤ E := by have := Finset.mem_range.mp (Finset.mem_filter.mp he).1; omega
    exact cylinder_card p E e heE (a e)
  have htail := Erdos7StarSieve.geometric_tail_le p 2 hp (higherLevels E)
    (fun e he => (Finset.mem_filter.mp he).2)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp
  have heq : ((p : ℚ)⁻¹)^2*((p : ℚ)/(p-1)) = 1/(p*(p-1)) := by
    field_simp
  rw [hsum] at hq
  rw [heq] at htail
  simpa only [mul_one_div] using hq.trans
    (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _))

/-- Every first-digit branch retains a p-dependent positive proportion of the
ambient space. The bound permits all higher pure residues to lie in this same
branch, so it holds separately for every prescribed branch. -/
theorem branchGood_card_le (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (a : ℕ → ℤ) (b : ℤ) :
    (Fintype.card (ZMod (p^E)) : ℚ)*(p-2)/(p*(p-1)) ≤
      (branchGood p E a b).card := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
  have hb := higherBad_card_le p E (by omega) a
  have hc := Finset.card_sdiff_add_card_inter (cylinder p E 1 b) (higherBad p E a)
  have hi : ((cylinder p E 1 b ∩ higherBad p E a).card : ℚ) ≤
      (higherBad p E a).card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hcq : ((branchGood p E a b).card : ℚ)+
      (cylinder p E 1 b ∩ higherBad p E a).card = (cylinder p E 1 b).card := by
    exact_mod_cast hc
  have hs := cylinder_card p E 1 hE b
  simp only [pow_one] at hs
  have heq : (Fintype.card (ZMod (p^E)) : ℚ)*(p-2)/(p*(p-1)) =
      (Fintype.card (ZMod (p^E)) : ℚ)*(p : ℚ)⁻¹-
      (Fintype.card (ZMod (p^E)) : ℚ)/(p*(p-1)) := by
    field_simp [show (p : ℚ)-1 ≠ 0 by linarith]
    <;> ring
  rw [heq]
  linarith

lemma branchGood_nonempty (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (a : ℕ → ℤ) (b : ℤ) : (branchGood p E a b).Nonempty := by
  have hb := branchGood_card_le p E hp hE a b
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hN : (0 : ℚ) < Fintype.card (ZMod (p^E)) := by exact_mod_cast Fintype.card_pos
  have hh : (0 : ℚ) < Fintype.card (ZMod (p^E))*(p-2)/(p*(p-1)) := by
    apply div_pos
    · exact mul_pos hN (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  exact Finset.card_pos.mp (by exact_mod_cast hh.trans_le hb)

lemma mem_branchGood (p E : ℕ) [NeZero p] (a : ℕ → ℤ) (b : ℤ)
    (x : ZMod (p^E)) : x ∈ branchGood p E a b ↔
    (p : ℤ) ∣ (x.val : ℤ)-b ∧ ∀ e, 2 ≤ e → e ≤ E →
      ¬ ((p^e : ℕ) : ℤ) ∣ (x.val : ℤ)-a e := by
  simp only [branchGood, Finset.mem_sdiff, mem_cylinder, pow_one]
  simp only [higherBad, Finset.mem_biUnion, higherLevels, Finset.mem_filter,
    Finset.mem_range, mem_cylinder]
  grind

/-- The branch residue may be prescribed in advance, independently of all the
higher pure residues. If b is nonzero modulo p, the resulting lift is a unit
modulo p when p is prime. -/
theorem exists_avoiding_lift (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (a : ℕ → ℤ) (b : ℤ) :
    ∃ u : ℤ, (p : ℤ) ∣ u-b ∧ ∀ e, 2 ≤ e → e ≤ E →
      ¬ ((p^e : ℕ) : ℤ) ∣ u-a e := by
  obtain ⟨x, hx⟩ := branchGood_nonempty p E hp hE a b
  exact ⟨x.val, (mem_branchGood p E a b x).mp hx⟩

/-- No positive-exponent cylinder meets two lifts whose first digits differ.
Primality and oddness are not needed for this elementary thinness property. -/
lemma lifts_thin (p e : ℕ) (he : 0 < e) (u v b c a : ℤ)
    (hu : (p : ℤ) ∣ u-b) (hv : (p : ℤ) ∣ v-c)
    (hbc : ¬ (p : ℤ) ∣ b-c) :
    ¬ (((p^e : ℕ) : ℤ) ∣ u-a ∧ ((p^e : ℕ) : ℤ) ∣ v-a) := by
  rintro ⟨h₁, h₂⟩
  have hd : (p : ℤ) ∣ ((p^e : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p (Nat.ne_of_gt he)
  apply hbc
  convert dvd_sub (dvd_sub (dvd_sub (hd.trans h₁) (hd.trans h₂)) hu) (dvd_neg.mpr hv) using 1
  ring

#print axioms branchGood_card_le
#print axioms exists_avoiding_lift
#print axioms lifts_thin
end Erdos7IndependentPureLifts
