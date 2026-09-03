import FormalConjecturesUtil

/-!
# Exact integer lifting and its carry terms

These identities describe a boundary of the finite-group approach to Erdős 66.
They do not establish the natural-number conjecture.
-/

namespace Erdos66Carry
open AdditiveCombinatorics

lemma sumRep_image_eq {X : Type*} [DecidableEq X] (B : Finset X)
    (e : X → ℕ) (he : Function.Injective e) (n : ℕ) :
    sumRep ((B.image e : Finset ℕ) : Set ℕ) n =
      ((B ×ˢ B).filter (fun ab ↦ e ab.1 + e ab.2 = n)).card := by
  classical
  rw [sumRep_def]
  symm
  apply Finset.card_bij (fun ab _ ↦ (e ab.1, e ab.2))
  · intro ab hab
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hs⟩ := hab
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe]
    exact ⟨hs, Finset.mem_image.mpr ⟨ab.1, ha, rfl⟩,
      Finset.mem_image.mpr ⟨ab.2, hb, rfl⟩⟩
  · intro ab hab cd hcd heq
    exact Prod.ext (he (congrArg Prod.fst heq)) (he (congrArg Prod.snd heq))
  · intro xy hxy
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe] at hxy
    obtain ⟨hs, hx, hy⟩ := hxy
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hy
    refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩,
      Prod.ext hax hby⟩
    simpa only [hax, hby] using hs

variable (p : ℕ) [NeZero p]

def digitEncode (z : ZMod p × ZMod p) : ℕ := z.1.val + p * z.2.val

def topDigit : ZMod p × ZMod p := ((p - 1 : ℕ), (p - 1 : ℕ))

lemma digitEncode_mod (z : ZMod p × ZMod p) : digitEncode p z % p = z.1.val := by
  rw [digitEncode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)]

lemma digitEncode_div (z : ZMod p × ZMod p) : digitEncode p z / p = z.2.val := by
  rw [digitEncode, Nat.add_mul_div_left _ _ (NeZero.pos p),
    Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]

lemma digitEncode_injective : Function.Injective (digitEncode p) := by
  intro a b h
  have hx := congrArg (· % p) h
  have hy := congrArg (· / p) h
  dsimp only at hx hy
  rw [digitEncode_mod, digitEncode_mod] at hx
  rw [digitEncode_div, digitEncode_div] at hy
  exact Prod.ext (ZMod.val_injective p hx) (ZMod.val_injective p hy)

lemma digitEncode_lt (z : ZMod p × ZMod p) : digitEncode p z < p ^ 2 := by
  have hx := ZMod.val_lt z.1
  have hy := ZMod.val_lt z.2
  dsimp [digitEncode]
  nlinarith [NeZero.pos p]

lemma digitEncode_complement (z : ZMod p × ZMod p) :
    digitEncode p z + digitEncode p (topDigit p - z) = p ^ 2 - 1 := by
  have hp := NeZero.pos p
  have hx := ZMod.val_lt z.1
  have hy := ZMod.val_lt z.2
  have ht : ((p - 1 : ℕ) : ZMod p).val = p - 1 :=
    ZMod.val_natCast_of_lt (by omega)
  have hx' : z.1.val ≤ ((p - 1 : ℕ) : ZMod p).val := by rw [ht]; omega
  have hy' : z.2.val ≤ ((p - 1 : ℕ) : ZMod p).val := by rw [ht]; omega
  simp only [digitEncode, topDigit, Prod.fst_sub, Prod.snd_sub,
    ZMod.val_sub hx', ZMod.val_sub hy', ht]
  have hx'' : p - 1 - z.1.val + z.1.val = p - 1 := Nat.sub_add_cancel (by omega)
  have hy'' : p - 1 - z.2.val + z.2.val = p - 1 := Nat.sub_add_cancel (by omega)
  calc
    _ = (p - 1 - z.1.val + z.1.val) + p * (p - 1 - z.2.val + z.2.val) := by ring
    _ = (p - 1) + p * (p - 1) := by rw [hx'', hy'']
    _ = p ^ 2 - 1 := by
      have hp' : p - 1 + 1 = p := by omega
      have hm : p * (p - 1) + p = p ^ 2 := by
        calc
          _ = p * (p - 1 + 1) := by ring
          _ = _ := by rw [hp']; ring
      omega

lemma digitEncode_sum_center_iff (a b : ZMod p × ZMod p) :
    digitEncode p a + digitEncode p b = p ^ 2 - 1 ↔ b = topDigit p - a := by
  constructor
  · intro h
    apply digitEncode_injective p
    have hh := digitEncode_complement p a
    omega
  · rintro rfl
    exact digitEncode_complement p a

/-- At the central target the lift has exactly the finite-group representation count. -/
lemma integer_lift_center (B : Finset (ZMod p × ZMod p)) :
    sumRep ((B.image (digitEncode p) : Finset ℕ) : Set ℕ) (p ^ 2 - 1) =
      (B.filter (fun a ↦ topDigit p - a ∈ B)).card := by
  rw [sumRep_image_eq B _ (digitEncode_injective p), Finset.card_filter, Finset.sum_product]
  simp only [digitEncode_sum_center_iff, Finset.sum_ite_eq', Finset.card_filter]

/-- Away from the central target there are two distinct low-digit carry cases. -/
lemma digitEncode_sum_iff (a b : ZMod p × ZMod p) (t s : ℕ) (ht : t < p) :
    digitEncode p a + digitEncode p b = t + p * s ↔
      (a.1.val + b.1.val = t ∧ a.2.val + b.2.val = s) ∨
      (a.1.val + b.1.val = t + p ∧ a.2.val + b.2.val + 1 = s) := by
  have hp := NeZero.pos p
  have ha := ZMod.val_lt a.1
  have hb := ZMod.val_lt b.1
  constructor
  · intro h
    have hmod := congrArg (· % p) h
    have hx : (a.1.val + b.1.val) % p = t := by
      have he : digitEncode p a + digitEncode p b =
          (a.1.val + b.1.val) + p * (a.2.val + b.2.val) := by dsimp [digitEncode]; ring
      simpa only [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht] using hmod
    have hd := Nat.mod_add_div (a.1.val + b.1.val) p
    rw [hx] at hd
    have hdiv : (a.1.val + b.1.val) / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    interval_cases hh : (a.1.val + b.1.val) / p
    · left
      simp only [mul_zero, add_zero] at hd
      refine ⟨hd.symm, ?_⟩
      dsimp [digitEncode] at h
      nlinarith
    · right
      simp only [mul_one] at hd
      refine ⟨hd.symm, ?_⟩
      dsimp [digitEncode] at h
      nlinarith
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> dsimp [digitEncode] <;> nlinarith

lemma integer_lift_carry_formula (B : Finset (ZMod p × ZMod p)) (t s : ℕ) (ht : t < p) :
    sumRep ((B.image (digitEncode p) : Finset ℕ) : Set ℕ) (t + p * s) =
      ((B ×ˢ B).filter (fun ab ↦ ab.1.1.val + ab.2.1.val = t ∧
        ab.1.2.val + ab.2.2.val = s)).card +
      ((B ×ˢ B).filter (fun ab ↦ ab.1.1.val + ab.2.1.val = t + p ∧
        ab.1.2.val + ab.2.2.val + 1 = s)).card := by
  rw [sumRep_image_eq B _ (digitEncode_injective p)]
  simp only [digitEncode_sum_iff p _ _ t s ht]
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  apply Finset.disjoint_filter.mpr
  intro ab hab h0 h1
  have hp := NeZero.pos p
  omega

lemma small_mod_eq_iff (x n : ℕ) (hx : x < 2 * p) (hn : n < p) :
    x % p = n ↔ x = n ∨ x = n + p := by
  have hp := NeZero.pos p
  constructor
  · intro h
    have hd := Nat.mod_add_div x p
    rw [h] at hd
    have hdiv : x / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr hx
    interval_cases hh : x / p <;> simp_all
  · rintro (rfl | rfl)
    · exact Nat.mod_eq_of_lt hn
    · simpa only [Nat.add_mod_right] using Nat.mod_eq_of_lt hn

lemma residue_sum_iff (a b : ZMod p) (n : ℕ) (hn : n < p) :
    a + b = (n : ZMod p) ↔ a.val + b.val = n ∨ a.val + b.val = n + p := by
  rw [← (ZMod.val_injective p).eq_iff, ZMod.val_add, ZMod.val_natCast_of_lt hn]
  exact small_mod_eq_iff p _ n (by have ha := ZMod.val_lt a; have hb := ZMod.val_lt b; omega) hn

lemma pair_filter_card (B : Finset (ZMod p)) (z : ZMod p) :
    ((B ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = z)).card =
      (B.filter (fun a ↦ z - a ∈ B)).card := by
  have he (a b : ZMod p) : a + b = z ↔ b = z - a := by
    constructor <;> intro h <;> linear_combination h
  simp only [Finset.card_filter, Finset.sum_product, he, Finset.sum_ite_eq']

/-- A cyclic representation count is the sum of two different integer counts.
Controlling their sum does not by itself control how the representations split. -/
lemma cyclic_periodization (B : Finset (ZMod p)) (n : ℕ) (hn : n < p) :
    (B.filter (fun a ↦ (n : ZMod p) - a ∈ B)).card =
      sumRep ((B.image ZMod.val : Finset ℕ) : Set ℕ) n +
      sumRep ((B.image ZMod.val : Finset ℕ) : Set ℕ) (n + p) := by
  rw [← pair_filter_card, sumRep_image_eq B _ (ZMod.val_injective p),
    sumRep_image_eq B _ (ZMod.val_injective p)]
  simp only [residue_sum_iff p _ _ n hn]
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  apply Finset.disjoint_filter.mpr
  intro ab hab h0 h1
  have hp := NeZero.pos p
  omega

end Erdos66Carry
