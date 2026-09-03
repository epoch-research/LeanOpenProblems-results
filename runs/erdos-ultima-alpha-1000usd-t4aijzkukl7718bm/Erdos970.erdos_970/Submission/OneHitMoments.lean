import FormalConjecturesUtil

/-! Exact moment updates for adding a residue class which can hit at most one
survivor. The hypothesis p>=m is essential to applying this to an interval.
No moment bound for small-prime insertions is asserted. -/
namespace Erdos970.OneHitMoments
open Finset

lemma sum_erase_card (S : Finset ℕ) (p : ℕ) (hS : S ⊆ range p) (f : ℕ → ℝ) :
    (∑ a ∈ range p, f (S.erase a).card) =
      (p - (S.card : ℝ)) * f S.card + (S.card : ℝ) * f (S.card - 1) := by
  classical
  have hs := sum_sdiff (f := fun a => f (S.erase a).card) hS
  have hyes : (∑ a ∈ S, f (S.erase a).card) = (S.card : ℝ) * f (S.card - 1) := by
    rw [sum_congr rfl (fun a ha => congrArg f (card_erase_of_mem ha))]
    simp
  have hno : (∑ a ∈ range p \ S, f (S.erase a).card) =
      ((range p \ S).card : ℝ) * f S.card := by
    calc
      _ = ∑ _a ∈ range p \ S, f S.card := sum_congr rfl (fun a ha => by
        rw [erase_eq_of_notMem (mem_sdiff.mp ha).2])
      _ = _ := by simp
  have hc : (S.card : ℝ) ≤ p := by exact_mod_cast (card_le_card hS).trans_eq (card_range p)
  have hd : ((range p \ S).card : ℝ) = p - S.card := by
    rw [card_sdiff_of_subset hS, card_range, Nat.cast_sub (by exact_mod_cast hc)]
  rw [hyes, hno, hd] at hs
  exact hs.symm

lemma choose_identity (n t : ℕ) :
    ((n : ℝ) - t) * (n.choose t : ℝ) = (t + 1 : ℝ) * n.choose (t + 1) := by
  by_cases ht : t ≤ n
  · have hh := Nat.choose_succ_right_eq n t
    have hh' := congrArg (fun z : ℕ => (z : ℝ)) hh
    push_cast at hh'
    rw [Nat.cast_sub ht] at hh'
    nlinarith only [hh']
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < t),
      Nat.choose_eq_zero_of_lt (by omega : n < t + 1)]
    norm_num

/-- Exact unnormalized factorial-moment update for one fixed survivor set. -/
lemma oneHit_choose_sum (S : Finset ℕ) (m p t : ℕ)
    (hS : S ⊆ range m) (hmp : m ≤ p) :
    (∑ a ∈ range p, ((m - (S.erase a).card).choose (t + 1) : ℝ)) =
      ((p : ℝ) - (t + 1)) * (m - S.card).choose (t + 1) +
      ((m : ℝ) - t) * (m - S.card).choose t := by
  have hsm : S.card ≤ m := (card_le_card hS).trans_eq (card_range m)
  rw [sum_erase_card S p (hS.trans (range_mono hmp)) (fun n => ((m - n).choose (t + 1) : ℝ))]
  have hstep : (S.card : ℝ) * ((m - (S.card - 1)).choose (t + 1) : ℝ) =
      (S.card : ℝ) * ((m - S.card).choose t + (m - S.card).choose (t + 1)) := by
    by_cases hs : S.card = 0
    · simp [hs]
    · rw [show m - (S.card - 1) = (m - S.card) + 1 by omega,
        Nat.choose_succ_succ]
      push_cast
      rfl
  rw [hstep]
  have hh := choose_identity (m - S.card) t
  rw [Nat.cast_sub hsm] at hh
  nlinarith only [hh]

variable {Ω : Type*} [Fintype Ω]

noncomputable def moment (m : ℕ) (S : Ω → Finset ℕ) (t : ℕ) : ℝ :=
  (∑ w, ((m - (S w).card).choose t : ℝ)) / Fintype.card Ω

noncomputable def updatedMoment (m p : ℕ) (S : Ω → Finset ℕ) (t : ℕ) : ℝ :=
  (∑ w, ∑ a ∈ range p, ((m - ((S w).erase a).card).choose t : ℝ)) /
    ((Fintype.card Ω : ℝ) * p)

/-- The update averages independently over the old phase and the new residue. -/
theorem moment_update (m p t : ℕ) (hp : 0 < p) (hmp : m ≤ p)
    (S : Ω → Finset ℕ) (hS : ∀ w, S w ⊆ range m) :
    updatedMoment m p S (t + 1) =
      (1 - (t + 1 : ℝ) / p) * moment m S (t + 1) +
      ((m : ℝ) - t) / p * moment m S t := by
  unfold updatedMoment moment
  simp_rw [oneHit_choose_sum _ m p t (hS _) hmp]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [hpR]

/-- In an interval shorter than the modulus, avoidance really is a one-point
 deletion, not an independent thinning of all positions. -/
lemma avoidance_filter_eq_erase (S : Finset ℕ) (m p a : ℕ)
    (hS : S ⊆ range m) (hmp : m ≤ p) (ha : a < p) :
    S.filter (fun x => ¬x ≡ a [MOD p]) = S.erase a := by
  classical
  ext x
  by_cases hx : x ∈ S
  · have hxp : x < p := (mem_range.mp (hS hx)).trans_le hmp
    simp [mem_filter, mem_erase, hx, Nat.ModEq, Nat.mod_eq_of_lt hxp,
      Nat.mod_eq_of_lt ha]
  · simp [hx]

/-- The normalized moment has a convex two-term update, provided t+1<=p. -/
theorem normalized_moment_update (m p t : ℕ) (ht : t < m) (hmp : m ≤ p)
    (S : Ω → Finset ℕ) (hS : ∀ w, S w ⊆ range m) :
    updatedMoment m p S (t + 1) / (m.choose (t + 1) : ℝ) =
      (1 - (t + 1 : ℝ) / p) * (moment m S (t + 1) / (m.choose (t + 1) : ℝ)) +
      (t + 1 : ℝ) / p * (moment m S t / (m.choose t : ℝ)) := by
  have hp : 0 < p := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hct : (m.choose t : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht.le).ne'
  have hcs : (m.choose (t + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show t + 1 ≤ m by omega)).ne'
  have hc : ((m : ℝ) - t) / p / (m.choose (t + 1) : ℝ) =
      (t + 1 : ℝ) / p / (m.choose t : ℝ) := by
    field_simp [hpR, hct, hcs]
    have hh := choose_identity m t
    nlinarith only [hh]
  rw [moment_update m p t hp hmp S hS]
  calc
    _ = (1 - (t + 1 : ℝ) / p) * (moment m S (t + 1) / (m.choose (t + 1) : ℝ)) +
        (((m : ℝ) - t) / p / (m.choose (t + 1) : ℝ)) * moment m S t := by ring
    _ = _ := by rw [hc]; ring

/-- The scalar inequality needed for preservation of a binomial moment bound. -/
lemma binomial_update_bound (m p t : ℕ) (ht : t < m) (hmp : m ≤ p)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - (t + 1 : ℝ) / p) * ((m.choose (t + 1) : ℝ) * q ^ (t + 1)) +
      ((m : ℝ) - t) / p * ((m.choose t : ℝ) * q ^ t) ≤
    (m.choose (t + 1) : ℝ) * (q + (1 - q) / p) ^ (t + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hd : 0 ≤ (1 - q) / p := div_nonneg (by linarith) hp.le
  have hb := pow_add_mul_le_add_pow hq (show 0 ≤ 2 * q + (1 - q) / p by positivity) (t + 1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (m.choose (t + 1)))
  have hc := choose_identity m t
  have hc' := congrArg (fun z : ℝ => z * q ^ t / p) hc
  calc
    _ = (m.choose (t + 1) : ℝ) *
        (q ^ (t + 1) + (t + 1 : ℝ) * q ^ t * ((1 - q) / p)) := by
      rw [pow_succ]
      field_simp [hp.ne'] at hc' ⊢
      nlinarith only [hc']
    _ ≤ _ := hh

/-- If the two required old moments obey binomial bounds, so does the updated
moment. For arbitrary prime insertions p<m the positivity argument is unavailable. -/
theorem preserves_binomial_moment (m p t : ℕ) (ht : t < m) (hmp : m ≤ p)
    (S : Ω → Finset ℕ) (hS : ∀ w, S w ⊆ range m)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hprev : moment m S t ≤ (m.choose t : ℝ) * q ^ t)
    (hcur : moment m S (t + 1) ≤ (m.choose (t + 1) : ℝ) * q ^ (t + 1)) :
    updatedMoment m p S (t + 1) ≤
      (m.choose (t + 1) : ℝ) * (q + (1 - q) / p) ^ (t + 1) := by
  have hp : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcoef : 0 ≤ 1 - (t + 1 : ℝ) / p := by
    have hle : (t + 1 : ℝ) ≤ p := by exact_mod_cast (show t + 1 ≤ p by omega)
    have hh := (div_le_one hpR).mpr hle
    linarith
  have hcoef' : 0 ≤ ((m : ℝ) - t) / p := by
    apply div_nonneg _ hpR.le
    have hh : (t : ℝ) ≤ m := by exact_mod_cast ht.le
    linarith
  rw [moment_update m p t hp hmp S hS]
  exact (add_le_add (mul_le_mul_of_nonneg_left hcur hcoef)
    (mul_le_mul_of_nonneg_left hprev hcoef')).trans
      (binomial_update_bound m p t ht hmp q hq hq1)

#print axioms oneHit_choose_sum
#print axioms moment_update
#print axioms normalized_moment_update
#print axioms avoidance_filter_eq_erase
#print axioms preserves_binomial_moment
end Erdos970.OneHitMoments
