import Mathlib

/-!
Auxiliary structural facts for factorial residues modulo primes (Erdős problem 478).
This file does not prove or disprove the conjectured asymptotic. It formalizes Wilson
reflection, midpoint restrictions, constant-defect upper bounds, and quotient-set
lower bounds. No statements from Submission/Spec.lean are used.
-/

namespace FactorialPairing

open Finset

lemma factorial_ne_zero {p k : ℕ} [Fact p.Prime] (hk : k < p) :
    (k.factorial : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
  exact not_le.mpr hk

lemma factorial_mul_reflection {p k : ℕ} [Fact p.Prime] (hk : k < p) :
    (k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p) = (-1) ^ (k + 1) := by
  have h := congrArg (fun n : ℕ => (n : ZMod p))
    (Nat.factorial_mul_descFactorial (show k ≤ p - 1 by omega))
  dsimp only at h
  rw [Nat.cast_mul, ZMod.cast_descFactorial (Nat.le_of_lt hk), ZMod.wilsons_lemma p] at h
  have hs : (-1 : ZMod p) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    (k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p)
        = ((-1 : ZMod p) ^ k * (-1) ^ k) *
            ((k.factorial : ZMod p) * ((p - 1 - k).factorial : ZMod p)) := by rw [hs, one_mul]
    _ = (-1 : ZMod p) ^ k *
        (((p - 1 - k).factorial : ZMod p) * ((-1) ^ k * (k.factorial : ZMod p))) := by ring
    _ = (-1 : ZMod p) ^ k * (-1) := by rw [h]
    _ = (-1 : ZMod p) ^ (k + 1) := (pow_succ _ _).symm

lemma factorial_reflection {p k : ℕ} [Fact p.Prime] (hk : k < p) :
    ((p - 1 - k).factorial : ZMod p) =
      (-1) ^ (k + 1) * (k.factorial : ZMod p)⁻¹ := by
  have h := factorial_mul_reflection hk
  apply (mul_right_cancel₀ (factorial_ne_zero hk))
  calc
    ((p - 1 - k).factorial : ZMod p) * (k.factorial : ZMod p) = (-1) ^ (k + 1) := by
      simpa [mul_comm] using h
    _ = ((-1) ^ (k + 1) * (k.factorial : ZMod p)⁻¹) * (k.factorial : ZMod p) := by
      rw [mul_assoc, inv_mul_cancel₀ (factorial_ne_zero hk), mul_one]

lemma factorial_reflection_even {p k : ℕ} [Fact p.Prime] (hk : k < p) (hke : Even k) :
    ((p - 1 - k).factorial : ZMod p) = -(k.factorial : ZMod p)⁻¹ := by
  rw [factorial_reflection hk, pow_succ, hke.neg_one_pow]
  simp

lemma factorial_reflection_odd {p k : ℕ} [Fact p.Prime] (hk : k < p) (hko : Odd k) :
    ((p - 1 - k).factorial : ZMod p) = (k.factorial : ZMod p)⁻¹ := by
  rw [factorial_reflection hk, pow_succ, hko.neg_one_pow]
  simp

lemma factorial_penultimate {p : ℕ} [Fact p.Prime] :
    ((p - 2).factorial : ZMod p) = 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have h := factorial_mul_reflection (show 1 < p by omega)
  simpa [Nat.sub_sub] using h

lemma factorial_midpoint_sq {p n : ℕ} [Fact p.Prime] (hp : p = 2 * n + 1) :
    (n.factorial : ZMod p) ^ 2 = (-1) ^ (n + 1) := by
  have h := factorial_mul_reflection (show n < p by omega)
  simpa [show p - 1 - n = n by omega, sq] using h

lemma factorial_midpoint_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ((p / 2).factorial : ZMod p) = 1 ∨ ((p / 2).factorial : ZMod p) = -1 := by
  apply sq_eq_one_iff.mp
  have he : Even (p / 2 + 1) := by
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  rw [factorial_midpoint_sq (show p = 2 * (p / 2) + 1 by omega), he.neg_one_pow]

lemma factorial_midpoint_one_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ((p / 2).factorial : ZMod p) ^ 2 = -1 := by
  have ho : Odd (p / 2 + 1) := by
    rw [Nat.odd_iff]
    omega
  rw [factorial_midpoint_sq (show p = 2 * (p / 2) + 1 by omega), ho.neg_one_pow]


noncomputable def residues (p : ℕ) : Finset (ZMod p) :=
  (Ico 1 p).image (fun k => (k.factorial : ZMod p))

lemma card_residues {p : ℕ} [Fact p.Prime] :
    (residues p).card = ((Ico 1 p).image (fun k => k.factorial % p)).card := by
  classical
  have h := card_image_of_injective (residues p) (ZMod.val_injective p)
  simpa [residues, image_image, Function.comp_def, ZMod.val_natCast] using h.symm

lemma factorial_mem_residues {p k : ℕ} [Fact p.Prime] (hk : k < p) :
    (k.factorial : ZMod p) ∈ residues p := by
  classical
  by_cases hk0 : k = 0
  · have hp := (Fact.out : p.Prime).two_le
    apply mem_image.mpr
    exact ⟨1, mem_Ico.mpr ⟨by omega, by omega⟩, by simp [hk0]⟩
  · exact mem_image.mpr ⟨k, mem_Ico.mpr ⟨by omega, hk⟩, rfl⟩

lemma residue_ne_zero {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ∈ residues p) :
    a ≠ 0 := by
  classical
  obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
  exact factorial_ne_zero (mem_Ico.mp hk).2

lemma image_erase_eq_of_duplicate {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) {a b : α} (hb : b ∈ s) (hba : b ≠ a)
    (hf : f a = f b) : (s.erase a).image f = s.image f := by
  apply Subset.antisymm (image_subset_image (erase_subset _ _))
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  by_cases hxa : x = a
  · subst x
    exact mem_image.mpr ⟨b, mem_erase.mpr ⟨hba, hb⟩, hf.symm⟩
  · exact mem_image.mpr ⟨x, mem_erase.mpr ⟨hxa, hx⟩, rfl⟩

lemma residues_eq_image_Ico_two {p : ℕ} [Fact p.Prime] (hp : 4 ≤ p) :
    residues p = (Ico 2 p).image (fun k => (k.factorial : ZMod p)) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    have hk' := mem_Ico.mp hk
    by_cases hk1 : k = 1
    · subst k
      exact mem_image.mpr ⟨p - 2, mem_Ico.mpr ⟨by omega, by omega⟩,
        by simpa using (factorial_penultimate (p := p))⟩
    · exact mem_image.mpr ⟨k, mem_Ico.mpr ⟨by omega, hk'.2⟩, rfl⟩
  · intro ha
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    exact factorial_mem_residues (mem_Ico.mp hk).2

lemma card_residues_le_sub_two {p : ℕ} [Fact p.Prime] (hp : 4 ≤ p) :
    (residues p).card ≤ p - 2 := by
  classical
  rw [residues_eq_image_Ico_two hp]
  exact (card_image_le).trans_eq (Nat.card_Ico _ _)

lemma card_residues_le_sub_three_of_three_mod_four {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hp4 : p % 4 = 3) :
    (residues p).card ≤ p - 3 := by
  classical
  have hmid : p / 2 ∈ Ico 2 p := mem_Ico.mpr ⟨by omega, by omega⟩
  have himage : ((Ico 2 p).erase (p / 2)).image (fun k => (k.factorial : ZMod p)) =
      (Ico 2 p).image (fun k => (k.factorial : ZMod p)) := by
    rcases factorial_midpoint_three_mod_four hp4 with h | h
    · exact image_erase_eq_of_duplicate _ _
        (b := p - 2) (mem_Ico.mpr ⟨by omega, by omega⟩) (by omega)
        (h.trans factorial_penultimate.symm)
    · exact image_erase_eq_of_duplicate _ _
        (b := p - 1) (mem_Ico.mpr ⟨by omega, by omega⟩) (by omega)
        (h.trans (ZMod.wilsons_lemma p).symm)
  rw [residues_eq_image_Ico_two (by omega), ← himage]
  calc
    _ ≤ ((Ico 2 p).erase (p / 2)).card := card_image_le
    _ = p - 3 := by rw [card_erase_of_mem hmid, Nat.card_Ico, Nat.sub_sub]

open scoped Pointwise

lemma quotient_residues {p : ℕ} [Fact p.Prime] :
    residues p / residues p = (univ : Finset (ZMod p)).erase 0 := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_div.mp hx
    exact mem_erase.mpr ⟨div_ne_zero (residue_ne_zero ha) (residue_ne_zero hb), mem_univ _⟩
  · intro hx
    have hx0 : x ≠ 0 := (mem_erase.mp hx).1
    have hxp : x.val < p := ZMod.val_lt x
    have hxv : x.val ≠ 0 := by simpa using hx0
    have hpred : x.val - 1 < p := by omega
    apply mem_div.mpr
    refine ⟨(x.val.factorial : ZMod p), factorial_mem_residues hxp,
      ((x.val - 1).factorial : ZMod p), factorial_mem_residues hpred, ?_⟩
    rw [← Nat.mul_factorial_pred hxv, Nat.cast_mul,
      mul_div_cancel_right₀ _ (factorial_ne_zero hpred), ZMod.natCast_zmod_val]

lemma card_residues_sq_lower_bound {p : ℕ} [Fact p.Prime] :
    p - 1 ≤ (residues p).card ^ 2 := by
  classical
  have h := card_div_le (s := residues p) (t := residues p)
  rw [quotient_residues, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card] at h
  simpa [sq] using h

lemma offdiag_quotient_residues {p : ℕ} [Fact p.Prime] :
    ((residues p).offDiag.image (fun ab => ab.1 / ab.2)) =
      ((univ : Finset (ZMod p)).erase 0).erase 1 := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hx
    obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp hab
    exact mem_erase.mpr ⟨fun h => hab ((div_eq_one_iff_eq (residue_ne_zero hb)).mp h),
      mem_erase.mpr ⟨div_ne_zero (residue_ne_zero ha) (residue_ne_zero hb), mem_univ _⟩⟩
  · intro hx
    have hx1 : x ≠ 1 := (mem_erase.mp hx).1
    have hxq : x ∈ residues p / residues p := by
      rw [quotient_residues]
      exact (mem_erase.mp hx).2
    obtain ⟨a, ha, b, hb, hab⟩ := mem_div.mp hxq
    refine mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, ?_⟩, hab⟩
    intro heq
    dsimp only at heq
    apply hx1
    rw [← hab, heq, div_self (residue_ne_zero hb)]

lemma card_residues_strong_lower_bound {p : ℕ} [Fact p.Prime] :
    p - 2 ≤ (residues p).card * ((residues p).card - 1) := by
  classical
  have h := card_image_le (s := (residues p).offDiag) (f := fun ab => ab.1 / ab.2)
  rw [offdiag_quotient_residues, card_erase_of_mem (by simp : (1 : ZMod p) ∈ univ.erase 0),
    card_erase_of_mem (mem_univ 0), card_univ, ZMod.card, offDiag_card,
    Nat.sub_sub] at h
  simpa [Nat.mul_sub_left_distrib] using h


lemma prod_range_pairing {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∏ k ∈ range (2 * n + 1), f k) =
      f n * ∏ k ∈ range n, f k * f (2 * n - k) := by
  have htop : (∏ k ∈ Ico (n + 1) (2 * n + 1), f k) =
      ∏ k ∈ range n, f (2 * n - k) := by
    have h := prod_Ico_reflect f 0 (m := n) (n := 2 * n) (by omega)
    simpa [Nat.Ico_zero_eq_range, show 2 * n + 1 - n = n + 1 by omega] using h.symm
  rw [← prod_range_mul_prod_Ico f (show n + 1 ≤ 2 * n + 1 by omega),
    prod_range_succ, htop, prod_mul_distrib]
  ac_rfl

lemma prod_factorials {p n : ℕ} [Fact p.Prime] (hp : p = 2 * n + 1) :
    (∏ k ∈ range p, (k.factorial : ZMod p)) =
      (n.factorial : ZMod p) * (-1) ^ (n * (n + 1) / 2) := by
  have hsum : (∑ k ∈ range n, (k + 1)) = n * (n + 1) / 2 := by
    calc
      _ = ∑ k ∈ range (n + 1), k := by rw [sum_range_succ']; simp
      _ = n * (n + 1) / 2 := by rw [sum_range_id]; simp [mul_comm]
  calc
    _ = (n.factorial : ZMod p) *
        ∏ k ∈ range n, (k.factorial : ZMod p) * ((2 * n - k).factorial : ZMod p) := by
      rw [show range p = range (2 * n + 1) by rw [hp]]
      exact prod_range_pairing (fun k => (k.factorial : ZMod p)) n
    _ = (n.factorial : ZMod p) * ∏ k ∈ range n, (-1 : ZMod p) ^ (k + 1) := by
      congr 1
      apply prod_congr rfl
      intro k hk
      have h := factorial_mul_reflection (show k < p by have := mem_range.mp hk; omega)
      simpa only [show p - 1 = 2 * n by omega] using h
    _ = _ := by rw [prod_pow_eq_pow_sum, hsum]

lemma prod_factorials_Ico_two {p : ℕ} [Fact p.Prime] (hp : 2 ≤ p) :
    (∏ k ∈ Ico 2 p, (k.factorial : ZMod p)) =
      ∏ k ∈ range p, (k.factorial : ZMod p) := by
  have h := prod_range_mul_prod_Ico (fun k => (k.factorial : ZMod p)) hp
  simpa [prod_range_succ] using h

lemma prod_factorials_one_mod_eight {p : ℕ} [Fact p.Prime] (hp : p % 8 = 1) :
    (∏ k ∈ Ico 2 p, (k.factorial : ZMod p)) = ((p / 2).factorial : ZMod p) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hmid : p / 2 = 4 * (p / 8) := by omega
  have hexp : (p / 2) * (p / 2 + 1) / 2 =
      2 * ((p / 8) * (4 * (p / 8) + 1)) := by
    rw [hmid, show 4 * (p / 8) * (4 * (p / 8) + 1) =
      (2 * ((p / 8) * (4 * (p / 8) + 1))) * 2 by ring]
    omega
  rw [prod_factorials_Ico_two hp2,
    prod_factorials (show p = 2 * (p / 2) + 1 by omega), hexp, pow_mul]
  simp

lemma nonzero_residues_product {p : ℕ} [Fact p.Prime] :
    (∏ a ∈ (univ : Finset (ZMod p)).erase 0, a) = -1 := by
  classical
  have himage : (Ico 1 p).image (fun k : ℕ => (k : ZMod p)) = univ.erase 0 := by
    ext a
    constructor
    · intro ha
      obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
      obtain ⟨hk1, hkp⟩ := mem_Ico.mp hk
      have hk0 : (k : ZMod p) ≠ 0 := by
        intro hz
        have := congrArg ZMod.val hz
        simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hkp] at this
        omega
      exact mem_erase.mpr ⟨hk0, mem_univ _⟩
    · intro ha
      have ha0 : a ≠ 0 := (mem_erase.mp ha).1
      have hav : a.val ≠ 0 := by simpa using ha0
      exact mem_image.mpr ⟨a.val, mem_Ico.mpr ⟨by omega, ZMod.val_lt a⟩, by simp⟩
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Ico 1 p) := by
    intro k hk l hl hkl
    have := congrArg ZMod.val hkl
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.mp hk).2,
      Nat.mod_eq_of_lt (mem_Ico.mp hl).2] using this
  rw [← himage, prod_image hinj]
  exact ZMod.prod_Ico_one_prime p

lemma card_residues_le_sub_three_of_one_mod_eight {p : ℕ} [Fact p.Prime]
    (hp : 4 ≤ p) (hp8 : p % 8 = 1) :
    (residues p).card ≤ p - 3 := by
  classical
  have hbound := card_residues_le_sub_two hp
  by_contra hnot
  have hcard : (residues p).card = p - 2 := by omega
  have hinj : Set.InjOn (fun k : ℕ => (k.factorial : ZMod p)) (Ico 2 p) := by
    apply injOn_of_card_image_eq
    rw [← residues_eq_image_Ico_two hp, hcard, Nat.card_Ico]
  have hprod : (∏ a ∈ residues p, a) = ((p / 2).factorial : ZMod p) := by
    rw [residues_eq_image_Ico_two hp, prod_image hinj, prod_factorials_one_mod_eight hp8]
  have hsubset : residues p ⊆ (univ : Finset (ZMod p)).erase 0 := by
    intro a ha
    exact mem_erase.mpr ⟨residue_ne_zero ha, mem_univ _⟩
  have hcard_missing : (((univ : Finset (ZMod p)).erase 0) \ residues p).card = 1 := by
    rw [card_sdiff_of_subset hsubset, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card, hcard]
    omega
  obtain ⟨r, hr⟩ := card_eq_one.mp hcard_missing
  have hmissing : r ∉ residues p := by
    have : r ∈ ((univ : Finset (ZMod p)).erase 0) \ residues p := by rw [hr]; simp
    exact (mem_sdiff.mp this).2
  have hmul : r * ((p / 2).factorial : ZMod p) = -1 := by
    have h := prod_sdiff (f := fun a : ZMod p => a) hsubset
    simpa [hr, hprod, nonzero_residues_product] using h
  have hsq := factorial_midpoint_one_mod_four (p := p) (show p % 4 = 1 by omega)
  have heq : r = ((p / 2).factorial : ZMod p) := by
    apply mul_right_cancel₀ (factorial_ne_zero (show p / 2 < p by omega))
    simpa [sq] using hmul.trans hsq.symm
  apply hmissing
  rw [heq]
  exact factorial_mem_residues (show p / 2 < p by omega)


lemma card_residues_eq_sub_two_imp_five_mod_eight {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hc : (residues p).card = p - 2) : p % 8 = 5 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hnot4 : p % 4 ≠ 3 := by
    intro h4
    have h := card_residues_le_sub_three_of_three_mod_four (by omega) h4
    omega
  have hnot8 : p % 8 ≠ 1 := by
    intro h8
    have h := card_residues_le_sub_three_of_one_mod_eight (by omega) h8
    omega
  omega

lemma nat_card_bound_three_mod_four {p : ℕ} (hprime : p.Prime)
    (hp : 7 ≤ p) (hp4 : p % 4 = 3) :
    ((Ico 1 p).image (fun k => k.factorial % p)).card ≤ p - 3 := by
  letI : Fact p.Prime := ⟨hprime⟩
  rw [← card_residues]
  exact card_residues_le_sub_three_of_three_mod_four hp hp4

lemma nat_card_bound_one_mod_eight {p : ℕ} (hprime : p.Prime)
    (hp : 4 ≤ p) (hp8 : p % 8 = 1) :
    ((Ico 1 p).image (fun k => k.factorial % p)).card ≤ p - 3 := by
  letI : Fact p.Prime := ⟨hprime⟩
  rw [← card_residues]
  exact card_residues_le_sub_three_of_one_mod_eight hp hp8

end FactorialPairing
