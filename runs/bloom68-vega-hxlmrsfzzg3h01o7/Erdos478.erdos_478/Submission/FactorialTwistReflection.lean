import Submission.FactorialPairing
import Submission.OccupancyBounds

/-!
# Reflection of twisted factorials and finite occupancy identities

For a nonzero `c : ZMod p`, with `p` prime, reflection of the full index set
`range p` intertwines `twist (-c)` and `twist c` by the output involution
`a ↦ -a⁻¹`. Thus their full fiber histograms and all full binomial moments
agree. The positive index set is `Ico 1 p`; `N c a` always denotes its fiber,
not the full fiber. Removing index zero gives exact second-moment corrections
and changes the support cardinality by at most one.

These are finite auxiliary theorems only. No factorial support limit or
asymptotic assertion, including Erdős problem 478, is proved here.
-/

open Finset
open scoped BigOperators

namespace FactorialTwistReflection

section FiniteMap

variable {α β : Type*} [DecidableEq β]

/-- Source and output involutions identify the corresponding finite fibers. -/
theorem fiberCard_involution (s : Finset α) (f g : α → β)
    (r : α → α) (t : β → β)
    (hr_mem : ∀ x ∈ s, r x ∈ s) (hr : ∀ x ∈ s, r (r x) = x)
    (ht : Function.Involutive t) (hfg : ∀ x ∈ s, g x = t (f (r x))) (b : β) :
    OccupancyBounds.fiberCard s g (t b) = OccupancyBounds.fiberCard s f b := by
  classical
  unfold OccupancyBounds.fiberCard
  apply card_bij' (fun x _ => r x) (fun x _ => r x)
  · intro x hx
    obtain ⟨hxs, hxb⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hr_mem x hxs, ht.injective ((hfg x hxs).symm.trans hxb)⟩
  · intro x hx
    obtain ⟨hxs, hxb⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hr_mem x hxs, ?_⟩
    rw [hfg _ (hr_mem x hxs), hr x hxs, hxb]
  · intro x hx
    exact hr x (mem_filter.mp hx).1
  · intro x hx
    exact hr x (mem_filter.mp hx).1

/-- Adding one source point changes exactly its output fiber. -/
theorem fiberCard_insert [DecidableEq α] (s : Finset α) (f : α → β)
    {x : α} (hx : x ∉ s) (b : β) :
    OccupancyBounds.fiberCard (insert x s) f b =
      OccupancyBounds.fiberCard s f b + if b = f x then 1 else 0 := by
  classical
  by_cases hb : f x = b
  · simp [OccupancyBounds.fiberCard, filter_insert, hb, hx]
  · simp [OccupancyBounds.fiberCard, filter_insert, hb, Ne.symm hb]

/-- Pascal's identity gives the exact change of every positive-order binomial moment. -/
theorem binomialMoment_fiber_insert [DecidableEq α]
    (s : Finset α) (f : α → β) (t : Finset β) {x : α}
    (hx : x ∉ s) (hxt : f x ∈ t) (r : ℕ) :
    OccupancyBounds.binomialMoment t (OccupancyBounds.fiberCard (insert x s) f) (r + 1) =
      OccupancyBounds.binomialMoment t (OccupancyBounds.fiberCard s f) (r + 1) +
        (OccupancyBounds.fiberCard s f (f x)).choose r := by
  classical
  unfold OccupancyBounds.binomialMoment
  calc
    (∑ b ∈ t, (OccupancyBounds.fiberCard (insert x s) f b).choose (r + 1)) =
        ∑ b ∈ t, ((OccupancyBounds.fiberCard s f b).choose (r + 1) +
          if b = f x then (OccupancyBounds.fiberCard s f b).choose r else 0) := by
      apply sum_congr rfl
      intro b _
      rw [fiberCard_insert s f hx b]
      by_cases hb : b = f x
      · simp [hb, Nat.choose_succ_succ, Nat.add_comm]
      · simp [hb]
    _ = _ := by simp [sum_add_distrib, hxt]

end FiniteMap

variable {p : ℕ}

/-- The factorial sequence twisted by a geometric progression. -/
def twist (c : ZMod p) (n : ℕ) : ZMod p := c ^ n * (n.factorial : ZMod p)

@[simp] theorem twist_zero (c : ZMod p) : twist c 0 = 1 := by simp [twist]

lemma reflection_lt {n : ℕ} (hn : n < p) : p - 1 - n < p := by omega

lemma reflection_reflection {n : ℕ} (hn : n < p) :
    p - 1 - (p - 1 - n) = n := by omega

/-- The full index domain adds just zero to the positive domain. -/
lemma range_eq_insert_Ico (hp : 0 < p) : range p = insert 0 (Ico 1 p) := by
  ext n
  simp only [mem_range, mem_insert, mem_Ico]
  omega

/-- Negated inversion is an involution, including at zero. -/
lemma negInv_involutive {K : Type*} [DivisionRing K] :
    Function.Involutive (fun a : K => -a⁻¹) := by
  intro a
  simp

noncomputable section

/-- Fiber over the full domain `0 ≤ n < p`. -/
def fullN (c : ZMod p) (a : ZMod p) : ℕ :=
  OccupancyBounds.fiberCard (range p) (twist c) a

/-- Fiber over the positive domain `1 ≤ n < p`. -/
def N (c : ZMod p) (a : ZMod p) : ℕ :=
  OccupancyBounds.fiberCard (Ico 1 p) (twist c) a

/-- Full support, including the contribution of index zero. -/
def fullSupport (c : ZMod p) : Finset (ZMod p) := (range p).image (twist c)

/-- Positive-index support. -/
def positiveSupport (c : ZMod p) : Finset (ZMod p) := (Ico 1 p).image (twist c)

@[simp] theorem fullN_pos_iff (c a : ZMod p) :
    0 < fullN c a ↔ a ∈ fullSupport c :=
  OccupancyBounds.fiberCard_pos_iff _ _ _

@[simp] theorem N_pos_iff (c a : ZMod p) :
    0 < N c a ↔ a ∈ positiveSupport c :=
  OccupancyBounds.fiberCard_pos_iff _ _ _

variable [Fact p.Prime]

/-- All binomial moments here sum over the entire target `ZMod p`. -/
def fullMoment (c : ZMod p) (r : ℕ) : ℕ :=
  OccupancyBounds.binomialMoment univ (fullN c) r

/-- Binomial moments of the positive-index fibers. -/
def positiveMoment (c : ZMod p) (r : ℕ) : ℕ :=
  OccupancyBounds.binomialMoment univ (N c) r

/-- `S₂(c)` without a `full` prefix is the positive-index second binomial moment. -/
def S2 (c : ZMod p) : ℕ := positiveMoment c 2

/-- Number of target values having a given full fiber cardinality (also for `k = 0`). -/
def fullHistogram (c : ZMod p) (k : ℕ) : ℕ :=
  (univ.filter fun a => fullN c a = k).card

lemma twist_ne_zero {c : ZMod p} (hc : c ≠ 0) {n : ℕ} (hn : n < p) :
    twist c n ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hc) (FactorialPairing.factorial_ne_zero hn)

/-- Wilson reflection and Fermat cancel all powers of `c`. -/
theorem twist_mul_reflection {c : ZMod p} (hc : c ≠ 0) {n : ℕ} (hn : n < p) :
    twist (-c) n * twist c (p - 1 - n) = -1 := by
  have he : n + (p - 1 - n) = p - 1 := by omega
  calc
    twist (-c) n * twist c (p - 1 - n) =
        (-1 : ZMod p) ^ n * (c ^ n * c ^ (p - 1 - n)) *
          ((n.factorial : ZMod p) * ((p - 1 - n).factorial : ZMod p)) := by
      simp only [twist]
      rw [neg_pow c n]
      ring
    _ = (-1 : ZMod p) ^ n * (-1) ^ (n + 1) := by
      rw [← pow_add, he, ZMod.pow_card_sub_one_eq_one hc,
        FactorialPairing.factorial_mul_reflection hn, mul_one]
    _ = -1 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      simp

/-- Exact reflection identity on `range p`; the hypothesis includes `n = 0`. -/
theorem twist_reflection {c : ZMod p} (hc : c ≠ 0) {n : ℕ} (hn : n < p) :
    twist (-c) n = -(twist c (p - 1 - n))⁻¹ := by
  have hr := twist_ne_zero hc (reflection_lt hn)
  apply mul_right_cancel₀ hr
  rw [twist_mul_reflection hc hn, neg_mul, inv_mul_cancel₀ hr]

/-- Pointwise full-fiber equality under `c ↦ -c` and `a ↦ -a⁻¹`. -/
theorem fullN_neg {c : ZMod p} (hc : c ≠ 0) (a : ZMod p) :
    fullN (-c) (-a⁻¹) = fullN c a := by
  exact fiberCard_involution (range p) (twist c) (twist (-c))
    (fun n => p - 1 - n) (fun a => -a⁻¹)
    (fun n hn => mem_range.mpr (reflection_lt (mem_range.mp hn)))
    (fun n hn => reflection_reflection (mem_range.mp hn))
    negInv_involutive (fun n hn => twist_reflection hc (mem_range.mp hn)) a

/-- The same fiber identity with the output involution on the right. -/
theorem fullN_neg_at {c : ZMod p} (hc : c ≠ 0) (a : ZMod p) :
    fullN (-c) a = fullN c (-a⁻¹) := by
  simpa using fullN_neg hc (-a⁻¹)

/-- Equality of full histograms, including the empty fibers. -/
theorem fullHistogram_neg {c : ZMod p} (hc : c ≠ 0) (k : ℕ) :
    fullHistogram (-c) k = fullHistogram c k := by
  classical
  unfold fullHistogram
  apply card_bijective (fun a : ZMod p => -a⁻¹) negInv_involutive.bijective
  intro a
  simp only [mem_filter, mem_univ, true_and, fullN_neg_at hc]

/-- Every additive statistic of the full fiber cardinalities is preserved. -/
theorem sum_fullN_neg {M : Type*} [AddCommMonoid M]
    {c : ZMod p} (hc : c ≠ 0) (F : ℕ → M) :
    (∑ a : ZMod p, F (fullN (-c) a)) = ∑ a : ZMod p, F (fullN c a) := by
  exact Fintype.sum_bijective (fun a : ZMod p => -a⁻¹) negInv_involutive.bijective
    _ _ (fun a => congrArg F (fullN_neg_at hc a))

/-- Full binomial moments are invariant in every order, including order zero. -/
theorem fullMoment_neg {c : ZMod p} (hc : c ≠ 0) (r : ℕ) :
    fullMoment (-c) r = fullMoment c r :=
  sum_fullN_neg hc (fun k => k.choose r)

/-- The value at the added index is `1`, independent of `c`. -/
theorem fullN_eq_N_add (c a : ZMod p) :
    fullN c a = N c a + if a = 1 then 1 else 0 := by
  classical
  unfold fullN N
  rw [range_eq_insert_Ico (Fact.out : p.Prime).pos]
  simpa only [twist_zero] using
    fiberCard_insert (Ico 1 p) (twist c) (x := 0) (by simp) a

/-- Exact index-zero correction for every positive-order binomial moment. -/
theorem fullMoment_succ_eq_positive (c : ZMod p) (r : ℕ) :
    fullMoment c (r + 1) = positiveMoment c (r + 1) + (N c 1).choose r := by
  classical
  unfold fullMoment positiveMoment fullN N
  rw [range_eq_insert_Ico (Fact.out : p.Prime).pos]
  simpa only [twist_zero] using
    binomialMoment_fiber_insert (Ico 1 p) (twist c) univ
      (x := 0) (by simp) (mem_univ _) r

/-- In particular, the second binomial moment gains precisely `N c 1`. -/
theorem fullMoment_two_eq_S2_add (c : ZMod p) :
    fullMoment c 2 = S2 c + N c 1 := by
  simpa [S2] using fullMoment_succ_eq_positive c 1

/-- Corrected positive-index moments retain the reflection symmetry. -/
theorem positiveMoment_succ_corrected_neg {c : ZMod p} (hc : c ≠ 0) (r : ℕ) :
    positiveMoment c (r + 1) + (N c 1).choose r =
      positiveMoment (-c) (r + 1) + (N (-c) 1).choose r := by
  rw [← fullMoment_succ_eq_positive c, ← fullMoment_succ_eq_positive (-c),
    fullMoment_neg hc]

/-- The requested second-moment identity, with `N` and `S2` both on `Ico 1 p`. -/
theorem S2_add_N_one_neg {c : ZMod p} (hc : c ≠ 0) :
    S2 c + N c 1 = S2 (-c) + N (-c) 1 := by
  rw [← fullMoment_two_eq_S2_add c, ← fullMoment_two_eq_S2_add (-c),
    fullMoment_neg hc]

/-- Reflection permutes the entire full support by negated inversion. -/
theorem fullSupport_neg {c : ZMod p} (hc : c ≠ 0) :
    fullSupport (-c) = (fullSupport c).image (fun a => -a⁻¹) := by
  classical
  ext a
  constructor
  · intro ha
    refine mem_image.mpr ⟨-a⁻¹, ?_, by simp⟩
    apply (fullN_pos_iff c (-a⁻¹)).mp
    rw [← fullN_neg_at hc a]
    exact (fullN_pos_iff (-c) a).mpr ha
  · intro ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    apply (fullN_pos_iff (-c) (-b⁻¹)).mp
    rw [fullN_neg hc b]
    exact (fullN_pos_iff c b).mpr hb

/-- Full-support cardinalities are exactly equal. -/
theorem card_fullSupport_neg {c : ZMod p} (hc : c ≠ 0) :
    (fullSupport (-c)).card = (fullSupport c).card := by
  classical
  rw [fullSupport_neg hc]
  exact card_image_of_injective _ negInv_involutive.injective

/-- Adding the zero index adds only the target value `1`. -/
theorem fullSupport_eq_insert_positiveSupport (c : ZMod p) :
    fullSupport c = insert 1 (positiveSupport c) := by
  classical
  unfold fullSupport positiveSupport
  rw [range_eq_insert_Ico (Fact.out : p.Prime).pos, image_insert, twist_zero]

/-- The precise support correction is one if and only if `1` was absent. -/
theorem card_fullSupport_eq (c : ZMod p) :
    (fullSupport c).card = (positiveSupport c).card + if N c 1 = 0 then 1 else 0 := by
  classical
  rw [fullSupport_eq_insert_positiveSupport]
  by_cases h : N c 1 = 0
  · have hm : (1 : ZMod p) ∉ positiveSupport c := by
      intro hm
      have hpos := (N_pos_iff c 1).mpr hm
      omega
    simp [card_insert_of_notMem hm, h]
  · have hm : (1 : ZMod p) ∈ positiveSupport c :=
      (N_pos_iff c 1).mp (Nat.pos_of_ne_zero h)
    simp [card_insert_of_mem hm, h]

/-- Each positive-support size is within one of its reflected partner. -/
theorem positiveSupport_card_bounds {c : ZMod p} (hc : c ≠ 0) :
    (positiveSupport c).card ≤ (positiveSupport (-c)).card + 1 ∧
      (positiveSupport (-c)).card ≤ (positiveSupport c).card + 1 := by
  have heq := card_fullSupport_neg hc
  rw [card_fullSupport_eq, card_fullSupport_eq] at heq
  split_ifs at heq <;> omega

/-- Absolute difference of the two positive-support cardinalities is at most one. -/
theorem positiveSupport_card_dist_le_one {c : ZMod p} (hc : c ≠ 0) :
    Nat.dist (positiveSupport c).card (positiveSupport (-c)).card ≤ 1 := by
  have h := positiveSupport_card_bounds hc
  unfold Nat.dist
  omega

end

end FactorialTwistReflection
