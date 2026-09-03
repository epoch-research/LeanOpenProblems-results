import Submission.CarryExplore
import Submission.CarryAveragingExplore

/-! Exact finite cyclic realization of coordinate thickening. This is not an
infinite integer construction. -/
namespace Erdos66CyclicThickening
open Erdos66Carry Erdos66CarryAveraging

variable (b : ℕ) [NeZero b]

def cyclicEncode (z : ZMod b × ZMod b) : ZMod (b ^ 2) := (digitEncode b z : ℕ)

lemma cyclicEncode_injective : Function.Injective (cyclicEncode b) := by
  intro x y h
  apply digitEncode_injective b
  have hval := congrArg ZMod.val h
  simpa only [cyclicEncode, ZMod.val_natCast_of_lt (digitEncode_lt b x),
    ZMod.val_natCast_of_lt (digitEncode_lt b y)] using hval

noncomputable def cyclicDigitEquiv : (ZMod b × ZMod b) ≃ ZMod (b ^ 2) :=
  Equiv.ofBijective (cyclicEncode b)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cyclicEncode_injective b, by simp [pow_two]⟩)

/-- The borrow in subtracting the low base-`b` digit. -/
def borrow (t x : ZMod b) : ℕ := if t.val < x.val then 1 else 0

lemma low_sub_val (t x : ZMod b) :
    (t - x).val + x.val = t.val + b * borrow b t x := by
  by_cases h : t.val < x.val
  · simp only [borrow, if_pos h, mul_one]
    have hsum : (t - x) + x = (t.val : ZMod b) := by simp
    have hh := (residue_sum_iff b (t - x) x t.val (ZMod.val_lt t)).mp hsum
    omega
  · simp only [borrow, if_neg h, mul_zero, add_zero]
    rw [ZMod.val_sub (by omega)]
    omega

lemma mul_cast_eq (x y : ℕ) (h : (x : ZMod b) = (y : ZMod b)) :
    (b : ZMod (b ^ 2)) * x = b * y := by
  rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  have hh := (ZMod.natCast_eq_natCast_iff x y b).mp h
  simpa only [pow_two] using hh.mul_left' b

lemma cyclicEncode_sub (t s x y : ZMod b) :
    cyclicEncode b (t, s) - cyclicEncode b (x, y) =
      cyclicEncode b (t - x, s - y - (borrow b t x : ZMod b)) := by
  apply sub_eq_iff_eq_add.mpr
  let c := borrow b t x
  let v := s - y - (c : ZMod b)
  have hl := low_sub_val b t x
  have hh : ((v.val + y.val + c : ℕ) : ZMod b) = (s.val : ZMod b) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, v]
    ring
  have hm := mul_cast_eq b _ _ hh
  have hl' : (((t - x).val + x.val : ℕ) : ZMod (b ^ 2)) =
      ((t.val + b * c : ℕ) : ZMod (b ^ 2)) := by rw [hl]
  dsimp only [cyclicEncode, digitEncode, Prod.fst, Prod.snd]
  push_cast
  change (t.val + b * s.val : ZMod (b ^ 2)) =
    ((t - x).val + b * v.val) + (x.val + b * y.val)
  push_cast at hm hl'
  linear_combination -hl' - hm

section Blocks
variable (p K : ℕ) [NeZero p] [NeZero K]

def blockDigit (a : ZMod p) (i : Fin K) : ZMod (p * K) :=
  ((a.val + p * i.val : ℕ) : ZMod (p * K))

lemma blockDigit_val (a : ZMod p) (i : Fin K) :
    (blockDigit p K a i).val = a.val + p * i.val := by
  apply ZMod.val_natCast_of_lt
  have ha := ZMod.val_lt a
  have hi := i.isLt
  have hp := NeZero.pos p
  nlinarith

lemma blockDigit_injective :
    Function.Injective (fun z : ZMod p × Fin K ↦ blockDigit p K z.1 z.2) := by
  intro a b h
  have hv := congrArg ZMod.val h
  dsimp only at hv
  rw [blockDigit_val, blockDigit_val] at hv
  have hm := congrArg (· % p) hv
  have hd := congrArg (· / p) hv
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)] at hm
  simp only [Nat.add_mul_div_left _ _ (NeZero.pos p),
    Nat.div_eq_of_lt (ZMod.val_lt _), zero_add] at hd
  exact Prod.ext (ZMod.val_injective p hm) (Fin.ext hd)

noncomputable def blockEquiv : (ZMod p × Fin K) ≃ ZMod (p * K) :=
  Equiv.ofBijective (fun z ↦ blockDigit p K z.1 z.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨blockDigit_injective p K, by simp⟩)

def reduceDigit : ZMod (p * K) →+* ZMod p := ZMod.castHom (dvd_mul_right p K) _

lemma reduce_block (a : ZMod p) (i : Fin K) :
    reduceDigit p K (blockDigit p K a i) = a := by
  unfold blockDigit
  rw [map_natCast]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val]

/-- Number of block indices not requiring a borrow. -/
def lowCutoff (q : Fin K) (t a : ZMod p) : ℕ :=
  q.val + if a.val ≤ t.val then 1 else 0

lemma lowCutoff_le (q : Fin K) (t a : ZMod p) : lowCutoff p K q t a ≤ K := by
  unfold lowCutoff
  split_ifs <;> have hq := q.isLt <;> omega

lemma borrow_block (t a : ZMod p) (q i : Fin K) :
    borrow (p * K) (blockDigit p K t q) (blockDigit p K a i) =
      if i.val < lowCutoff p K q t a then 0 else 1 := by
  have hp := NeZero.pos p
  have ht := ZMod.val_lt t
  have ha := ZMod.val_lt a
  simp only [borrow, blockDigit_val, lowCutoff]
  by_cases h : a.val ≤ t.val
  · simp only [if_pos h]
    split_ifs with h₁ h₂ h₂
    · have hi : i.val ≤ q.val := by omega
      nlinarith
    · rfl
    · rfl
    · have hi : q.val + 1 ≤ i.val := by omega
      nlinarith
  · simp only [if_neg h, Nat.add_zero]
    split_ifs with h₁ h₂ h₂
    · have hi : i.val + 1 ≤ q.val := by omega
      nlinarith
    · rfl
    · rfl
    · have hi : q.val ≤ i.val := by omega
      nlinarith


noncomputable def liftWeight (w : ZMod p × ZMod p → ℝ)
    (z : ZMod ((p * K) ^ 2)) : ℝ :=
  let xy := (cyclicDigitEquiv (p * K)).symm z
  w (reduceDigit p K xy.1, reduceDigit p K xy.2)

lemma liftWeight_encode (w : ZMod p × ZMod p → ℝ) (x y : ZMod (p * K)) :
    liftWeight p K w (cyclicEncode (p * K) (x, y)) =
      w (reduceDigit p K x, reduceDigit p K y) := by
  change w (reduceDigit p K (((cyclicDigitEquiv (p * K)).symm
    ((cyclicDigitEquiv (p * K)) (x, y))).1),
    reduceDigit p K (((cyclicDigitEquiv (p * K)).symm
    ((cyclicDigitEquiv (p * K)) (x, y))).2)) = _
  rw [Equiv.symm_apply_apply]

noncomputable def cyclicConv {m : ℕ} [NeZero m] (w : ZMod m → ℝ) (z : ZMod m) : ℝ :=
  ∑ x, w x * w (z - x)

lemma lift_convolution_digits (w : ZMod p × ZMod p → ℝ) (t s : ZMod (p * K)) :
    cyclicConv (liftWeight p K w) (cyclicEncode (p * K) (t, s)) =
      ∑ x : ZMod (p * K), ∑ y : ZMod (p * K),
        w (reduceDigit p K x, reduceDigit p K y) *
          w (reduceDigit p K t - reduceDigit p K x,
            reduceDigit p K s - reduceDigit p K y - (borrow (p * K) t x : ZMod p)) := by
  unfold cyclicConv
  rw [← Equiv.sum_comp (cyclicDigitEquiv (p * K)), Fintype.sum_prod_type]
  simp only [cyclicDigitEquiv, Equiv.ofBijective_apply, cyclicEncode_sub,
    liftWeight_encode, map_sub, map_natCast]

lemma card_fin_below (K d : ℕ) (hd : d ≤ K) :
    ((Finset.univ : Finset (Fin K)).filter (fun i ↦ i.val < d)).card = d := by
  calc
    _ = (Finset.range d).card := by
      apply Finset.card_bij (fun i _ ↦ i.val)
      · intro i hi
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] using hi
      · intro i hi j hj hij
        exact Fin.ext hij
      · intro i hi
        have hi' := Finset.mem_range.mp hi
        exact ⟨⟨i, lt_of_lt_of_le hi' hd⟩, by simp [hi'], rfl⟩
    _ = d := Finset.card_range d

lemma sum_fin_cutoff (K d : ℕ) (hd : d ≤ K) (u v : ℝ) :
    (∑ i : Fin K, if i.val < d then u else v) = (d : ℝ) * u + ((K : ℝ) - d) * v := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_fin_below K d hd]
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ (α := Fin K)) (fun i ↦ i.val < d)
  rw [card_fin_below K d hd, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : ((((Finset.univ : Finset (Fin K)).filter
      (fun i ↦ ¬i.val < d)).card : ℕ) : ℝ) = (K : ℝ) - d := by
    have hh : (d : ℝ) + ((((Finset.univ : Finset (Fin K)).filter
      (fun i ↦ ¬i.val < d)).card : ℕ) : ℝ) = K := by exact_mod_cast hc
    linarith
  rw [hc']


lemma lift_convolution_formula (w : ZMod p × ZMod p → ℝ)
    (t : ZMod p) (q : Fin K) (s : ZMod (p * K)) :
    cyclicConv (liftWeight p K w)
        (cyclicEncode (p * K) (blockDigit p K t q, s)) =
      (K : ℝ) * ∑ a : ZMod p, ∑ u : ZMod p,
        w (a, u) * ((lowCutoff p K q t a : ℝ) *
          w (t - a, reduceDigit p K s - u) +
          ((K : ℝ) - lowCutoff p K q t a) *
          w (t - a, reduceDigit p K s - u - 1)) := by
  rw [lift_convolution_digits, reduce_block]
  rw [← Equiv.sum_comp (blockEquiv p K), Fintype.sum_prod_type]
  simp only [blockEquiv, Equiv.ofBijective_apply, reduce_block, borrow_block]
  calc
    _ = ∑ a : ZMod p, ∑ i : Fin K, ∑ u : ZMod p,
        (K : ℝ) * (w (a, u) * w (t - a, reduceDigit p K s - u -
          ((if i.val < lowCutoff p K q t a then 0 else 1 : ℕ) : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Equiv.sum_comp (blockEquiv p K), Fintype.sum_prod_type]
      simp only [blockEquiv, Equiv.ofBijective_apply, reduce_block,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ a : ZMod p, ∑ u : ZMod p, ∑ i : Fin K,
        (K : ℝ) * (w (a, u) * w (t - a, reduceDigit p K s - u -
          ((if i.val < lowCutoff p K q t a then 0 else 1 : ℕ) : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      congr 2
      simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
      simp_rw [sub_ite, sub_zero, apply_ite (fun z ↦ w (t - a, z))]
      exact sum_fin_cutoff K (lowCutoff p K q t a) (lowCutoff_le p K q t a) _ _


def setWeight {α : Type*} [DecidableEq α] (B : Finset α) (a : α) : ℝ :=
  if a ∈ B then 1 else 0

noncomputable def sumFiber (B : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    Finset (ZMod p × ZMod p) := B.filter (fun a ↦ (t - a.1, s - a.2) ∈ B)

lemma set_weight_fibers (B : Finset (ZMod p × ZMod p)) (t s : ZMod p)
    (g h : ZMod p × ZMod p → ℝ) :
    (∑ a : ZMod p, ∑ u : ZMod p, setWeight B (a, u) *
      (g (a, u) * setWeight B (t - a, s - u) +
        h (a, u) * setWeight B (t - a, s - u - 1))) =
      (∑ z ∈ sumFiber p B t s, g z) + ∑ z ∈ sumFiber p B t (s - 1), h z := by
  classical
  rw [← Fintype.sum_prod_type (fun z : ZMod p × ZMod p ↦ setWeight B z *
    (g z * setWeight B (t - z.1, s - z.2) +
      h z * setWeight B (t - z.1, s - z.2 - 1)))]
  simp only [sumFiber, Finset.sum_filter, setWeight]
  have he : ∀ z : ZMod p × ZMod p,
      (if z ∈ B then (1 : ℝ) else 0) *
        (g z * (if (t - z.1, s - z.2) ∈ B then 1 else 0) +
          h z * (if (t - z.1, s - z.2 - 1) ∈ B then 1 else 0)) =
      (if z ∈ B then (if (t - z.1, s - z.2) ∈ B then g z else 0) else 0) +
        (if z ∈ B then (if (t - z.1, s - 1 - z.2) ∈ B then h z else 0) else 0) := by
    intro z
    rw [show s - 1 - z.2 = s - z.2 - 1 by ring]
    split_ifs <;> ring
  simp only [he, Finset.sum_add_distrib]
  simp

/-- The small carry before adding the block digits. -/
def smallBorrow (t a : ZMod p) : ℤ := if t.val < a.val then 1 else 0

lemma smallBorrow_cases (t a : ZMod p) : smallBorrow p t a = 0 ∨ smallBorrow p t a = 1 := by
  unfold smallBorrow
  split_ifs <;> simp

lemma cutoff_triangle (t a : ZMod p) (q : Fin K) :
    (lowCutoff p K q t a : ℝ) = (triangle K ((q.val : ℤ) - smallBorrow p t a) : ℝ) := by
  have hq := q.isLt
  suffices h : (lowCutoff p K q t a : ℤ) = triangle K ((q.val : ℤ) - smallBorrow p t a) by
    exact_mod_cast h
  unfold lowCutoff triangle smallBorrow
  split_ifs <;> omega

lemma cutoff_complement_triangle (t a : ZMod p) (q : Fin K) :
    (K : ℝ) - lowCutoff p K q t a =
      (triangle K ((q.val : ℤ) + K - smallBorrow p t a) : ℝ) := by
  have hq := q.isLt
  suffices h : (K : ℤ) - lowCutoff p K q t a =
      triangle K ((q.val : ℤ) + K - smallBorrow p t a) by exact_mod_cast h
  unfold lowCutoff triangle smallBorrow
  split_ifs <;> omega

lemma lift_set_convolution_formula (B : Finset (ZMod p × ZMod p))
    (t : ZMod p) (q : Fin K) (s : ZMod (p * K)) :
    cyclicConv (liftWeight p K (setWeight B))
        (cyclicEncode (p * K) (blockDigit p K t q, s)) =
      (K : ℝ) * ((∑ z ∈ sumFiber p B t (reduceDigit p K s),
        (triangle K ((q.val : ℤ) - smallBorrow p t z.1) : ℝ)) +
        ∑ z ∈ sumFiber p B t (reduceDigit p K s - 1),
          (triangle K ((q.val : ℤ) + K - smallBorrow p t z.1) : ℝ)) := by
  rw [lift_convolution_formula]
  simp_rw [cutoff_complement_triangle, cutoff_triangle]
  congr 1
  exact set_weight_fibers p B t (reduceDigit p K s)
    (fun z ↦ (triangle K ((q.val : ℤ) - smallBorrow p t z.1) : ℝ))
    (fun z ↦ (triangle K ((q.val : ℤ) + K - smallBorrow p t z.1) : ℝ))

noncomputable def thickenedSet (B : Finset (ZMod p × ZMod p)) :
    Finset (ZMod ((p * K) ^ 2)) :=
  Finset.univ.filter (fun z ↦
    let xy := (cyclicDigitEquiv (p * K)).symm z
    (reduceDigit p K xy.1, reduceDigit p K xy.2) ∈ B)

lemma thickenedSet_weight (B : Finset (ZMod p × ZMod p)) :
    setWeight (thickenedSet p K B) = liftWeight p K (setWeight B) := by
  classical
  funext z
  simp [setWeight, thickenedSet, liftWeight]

lemma cyclicConv_setWeight {m : ℕ} [NeZero m] (C : Finset (ZMod m)) (z : ZMod m) :
    cyclicConv (setWeight C) z = ((C.filter (fun a ↦ z - a ∈ C)).card : ℝ) := by
  classical
  simp only [cyclicConv, setWeight, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

/-- Coordinate thickening converts flat two-coordinate counts into flat counts
in an actual cyclic group, with an explicit carry error. -/
theorem thickenedSet_error (B : Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hB : ∀ t s : ZMod p, |((sumFiber p B t s).card : ℝ) - μ| ≤ E)
    (z : ZMod ((p * K) ^ 2)) :
    |(((thickenedSet p K B).filter (fun a ↦ z - a ∈ thickenedSet p K B)).card : ℝ) -
      (K : ℝ) ^ 2 * μ| ≤ (K : ℝ) ^ 2 * E + 2 * K * (μ + E) := by
  obtain ⟨⟨x, s⟩, rfl⟩ := (cyclicDigitEquiv (p * K)).surjective z
  obtain ⟨⟨t, q⟩, rfl⟩ := (blockEquiv p K).surjective x
  change |(((thickenedSet p K B).filter (fun a ↦
    cyclicEncode (p * K) (blockDigit p K t q, s) - a ∈ thickenedSet p K B)).card : ℝ) -
      (K : ℝ) ^ 2 * μ| ≤ _
  rw [← cyclicConv_setWeight, thickenedSet_weight, lift_set_convolution_formula]
  exact two_fiber_error (sumFiber p B t (reduceDigit p K s))
    (sumFiber p B t (reduceDigit p K s - 1)) (fun a ↦ smallBorrow p t a.1)
    (fun a _ ↦ smallBorrow_cases p t a.1) (fun a _ ↦ smallBorrow_cases p t a.1)
    K q.val q.isLt μ E (hB _ _) (hB _ _)

end Blocks
end Erdos66CyclicThickening
