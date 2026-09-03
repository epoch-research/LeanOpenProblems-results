import Submission.FactorialGapBound

/-!
# A finite global collision-energy bound for twisted factorials

The energy uses the full domain `range p`, including index zero. Partitioning
that domain into the `p / H + 1` buckets indexed by `n / H` gives

`energy c ≤ (p / H + 1) * (p + H * (H - 1))`.

Cauchy--Schwarz reduces this to counting equal-output ordered pairs in the
same bucket. Apart from the diagonal, their gaps are positive and less than
`H`. The all-positive-gap theorem of `FactorialGapBound` bounds their number
by `2 * ∑ d ∈ Ico 1 H, d = H * (H - 1)`.

Taking `H = Nat.sqrt p + 1` gives the unconditional finite bound
`energy c ≤ 3 * p * (Nat.sqrt p + 1)` for prime `p` and nonzero `c`.
This is a block-partition bound, not the sharper box-smoothing inequality.
It does not give energy asymptotic to `2 * p` and does not settle Erdős 478;
even that energy asymptotic alone would not settle the problem.
-/

open Finset FactorialTwistReflection FactorialGapBound OccupancyBounds
open scoped BigOperators

noncomputable section

namespace FactorialCollisionEnergy

section FiniteMap

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-- Squared fiber sizes count ordered equal-output pairs. The finite target
set need only contain the image of the finite source. -/
theorem sum_fiberCard_sq_eq_card (s : Finset α) (f : α → β) (t : Finset β)
    (hf : ∀ x ∈ s, f x ∈ t) :
    (∑ a ∈ t, (fiberCard s f a) ^ 2) =
      ((s ×ˢ s).filter fun ij => f ij.1 = f ij.2).card := by
  classical
  let P := (s ×ˢ s).filter fun ij => f ij.1 = f ij.2
  have hmaps : ∀ ij ∈ P, f ij.1 ∈ t := by
    intro ij hij
    exact hf ij.1 (mem_product.mp (mem_filter.mp hij).1).1
  calc
    (∑ a ∈ t, (fiberCard s f a) ^ 2) =
        ∑ a ∈ t, (P.filter fun ij => f ij.1 = a).card := by
      apply sum_congr rfl
      intro a _
      simp only [fiberCard, pow_two, ← card_product]
      congr 1
      ext ij
      simp only [P, mem_product, mem_filter]
      aesop
    _ = P.card := (card_eq_sum_card_fiberwise hmaps).symm

/-- Finite Cauchy--Schwarz for a fiber partitioned by a second map. -/
theorem fiberCard_sq_le_card_mul_sum (s : Finset α) (f : α → β) (g : α → γ)
    (u : Finset γ) (hg : ∀ x ∈ s, g x ∈ u) (a : β) :
    (fiberCard s f a) ^ 2 ≤
      u.card * ∑ b ∈ u, (fiberCard s (fun x => (f x, g x)) (a, b)) ^ 2 := by
  classical
  have hsplit : fiberCard s f a =
      ∑ b ∈ u, fiberCard s (fun x => (f x, g x)) (a, b) := by
    calc
      fiberCard s f a =
          ∑ b ∈ u, ((s.filter fun x => f x = a).filter fun x => g x = b).card :=
        card_eq_sum_card_fiberwise (fun x hx => hg x (mem_filter.mp hx).1)
      _ = _ := by simp only [fiberCard, filter_filter, Prod.mk.injEq]
  rw [hsplit]
  exact sq_sum_le_card_mul_sum_sq

/-- Summed fiber Cauchy--Schwarz, with the refined energy written as a pair count. -/
theorem sum_fiberCard_sq_le_card_mul_pairs (s : Finset α) (f : α → β) (g : α → γ)
    (t : Finset β) (u : Finset γ)
    (hf : ∀ x ∈ s, f x ∈ t) (hg : ∀ x ∈ s, g x ∈ u) :
    (∑ a ∈ t, (fiberCard s f a) ^ 2) ≤
      u.card * ((s ×ˢ s).filter fun ij =>
        f ij.1 = f ij.2 ∧ g ij.1 = g ij.2).card := by
  classical
  calc
    (∑ a ∈ t, (fiberCard s f a) ^ 2) ≤
        ∑ a ∈ t, u.card * ∑ b ∈ u,
          (fiberCard s (fun x => (f x, g x)) (a, b)) ^ 2 :=
      sum_le_sum fun a _ => fiberCard_sq_le_card_mul_sum s f g u hg a
    _ = u.card * ∑ ab ∈ t ×ˢ u,
          (fiberCard s (fun x => (f x, g x)) ab) ^ 2 := by
      rw [← mul_sum, sum_product]
    _ = _ := by
      rw [sum_fiberCard_sq_eq_card s (fun x => (f x, g x)) (t ×ˢ u)
        (fun x hx => mem_product.mpr ⟨hf x hx, hg x hx⟩)]
      simp only [Prod.mk.injEq]

end FiniteMap

section NatBlocks

variable {β : Type*} [DecidableEq β]

/-- Increasing equal-output pairs with gap strictly less than `H`. -/
def shortPairs (f : ℕ → β) (L H : ℕ) : Finset (ℕ × ℕ) :=
  ((range L) ×ˢ (range L)).filter fun ij =>
    ij.1 < ij.2 ∧ ij.2 - ij.1 < H ∧ f ij.2 = f ij.1

@[simp] theorem mem_shortPairs {f : ℕ → β} {L H : ℕ} {ij : ℕ × ℕ} :
    ij ∈ shortPairs f L H ↔ ij.1 < L ∧ ij.2 < L ∧
      ij.1 < ij.2 ∧ ij.2 - ij.1 < H ∧ f ij.2 = f ij.1 := by
  simp only [shortPairs, mem_filter, mem_product, mem_range, and_assoc]

/-- Ordered equal-output pairs in the same division bucket. -/
def blockPairs (f : ℕ → β) (L H : ℕ) : Finset (ℕ × ℕ) :=
  ((range L) ×ˢ (range L)).filter fun ij =>
    f ij.1 = f ij.2 ∧ ij.1 / H = ij.2 / H

@[simp] theorem mem_blockPairs {f : ℕ → β} {L H : ℕ} {ij : ℕ × ℕ} :
    ij ∈ blockPairs f L H ↔ ij.1 < L ∧ ij.2 < L ∧
      f ij.1 = f ij.2 ∧ ij.1 / H = ij.2 / H := by
  simp only [blockPairs, mem_filter, mem_product, mem_range, and_assoc]

/-- Two indices in one bucket have gap less than its positive width. -/
theorem sub_lt_of_div_eq_div {i j H : ℕ} (hH : 0 < H) (h : i / H = j / H) :
    j - i < H := by
  have hi := Nat.mod_add_div i H
  have hj := Nat.mod_add_div j H
  have hjm := Nat.mod_lt j hH
  rw [h] at hi
  omega

/-- The diagonal contributes at most `L`; both off-diagonal orientations
are bounded by the increasing short-gap pair set. -/
theorem blockPairs_card_le (f : ℕ → β) (L : ℕ) {H : ℕ} (hH : 0 < H) :
    (blockPairs f L H).card ≤ L + 2 * (shortPairs f L H).card := by
  classical
  let U := shortPairs f L H
  have hsub : blockPairs f L H ⊆
      (range L).diag ∪ U ∪ U.image Prod.swap := by
    intro ij hij
    obtain ⟨hi, hj, heq, hdiv⟩ := mem_blockPairs.mp hij
    rcases lt_trichotomy ij.1 ij.2 with hlt | he | hgt
    · apply mem_union.mpr
      left
      apply mem_union.mpr
      right
      exact mem_shortPairs.mpr
        ⟨hi, hj, hlt, sub_lt_of_div_eq_div hH hdiv, heq.symm⟩
    · exact mem_union.mpr (Or.inl (mem_union.mpr
        (Or.inl (mem_diag.mpr ⟨mem_range.mpr hi, he⟩))))
    · apply mem_union.mpr
      right
      refine mem_image.mpr ⟨ij.swap, ?_, Prod.swap_swap ij⟩
      exact mem_shortPairs.mpr
        ⟨hj, hi, hgt, sub_lt_of_div_eq_div hH hdiv.symm, heq⟩
  calc
    (blockPairs f L H).card ≤ ((range L).diag ∪ U ∪ U.image Prod.swap).card :=
      card_le_card hsub
    _ ≤ ((range L).diag.card + U.card) + (U.image Prod.swap).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ L + 2 * U.card := by
      have himage : (U.image Prod.swap).card ≤ U.card := card_image_le
      simp only [diag_card, card_range]
      omega

/-- The elementary triangular-number identity with the zero summand omitted. -/
theorem two_mul_sum_Ico_id {H : ℕ} (hH : 0 < H) :
    2 * (∑ d ∈ Ico 1 H, d) = H * (H - 1) := by
  have hs : (∑ d ∈ Ico 1 H, d) = ∑ d ∈ range H, d := by
    simpa using sum_range_add_sum_Ico (fun d : ℕ => d) (show 1 ≤ H by omega)
  rw [hs, Nat.mul_comm, sum_range_id_mul_two]

end NatBlocks

variable {p : ℕ} [Fact p.Prime]

/-- Global collision energy over the full index domain `range p`. -/
def energy (c : ZMod p) : ℕ := ∑ a : ZMod p, (fullN c a) ^ 2

omit [Fact p.Prime] in
/-- Sending an increasing pair to `(gap, starting index)` is injective. -/
theorem shortPairs_card_le_sum_gapSet (c : ZMod p) (H : ℕ) :
    (shortPairs (twist c) p H).card ≤ ∑ d ∈ Ico 1 H, (gapSet c d).card := by
  classical
  calc
    (shortPairs (twist c) p H).card ≤ ((Ico 1 H).sigma (gapSet c)).card := by
      apply card_le_card_of_injOn
        (fun ij : ℕ × ℕ => (⟨ij.2 - ij.1, ij.1⟩ : Σ _ : ℕ, ℕ))
      · intro ij hij
        obtain ⟨hi, hj, hlt, hd, heq⟩ := mem_shortPairs.mp hij
        apply mem_sigma.mpr
        dsimp only
        refine ⟨mem_Ico.mpr ⟨by omega, hd⟩, mem_gapSet.mpr ⟨by omega, ?_⟩⟩
        simpa only [Nat.add_sub_of_le hlt.le] using heq
      · intro ij hij kl hkl he
        obtain ⟨_, _, hijlt, _, _⟩ := mem_shortPairs.mp hij
        obtain ⟨_, _, hkllt, _, _⟩ := mem_shortPairs.mp hkl
        have hd := congrArg Sigma.fst he
        have hi := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
        apply Prod.ext <;> dsimp at hd hi ⊢ <;> omega
    _ = _ := card_sigma _ _

/-- All short-gap collisions are bounded at once, without a hypothesis `H ≤ p`. -/
theorem two_mul_shortPairs_card_le {c : ZMod p} (hc : c ≠ 0)
    {H : ℕ} (hH : 0 < H) :
    2 * (shortPairs (twist c) p H).card ≤ H * (H - 1) := by
  calc
    2 * (shortPairs (twist c) p H).card ≤
        2 * ∑ d ∈ Ico 1 H, (gapSet c d).card :=
      Nat.mul_le_mul_left _ (shortPairs_card_le_sum_gapSet c H)
    _ ≤ 2 * ∑ d ∈ Ico 1 H, d := by
      apply Nat.mul_le_mul_left
      exact sum_le_sum fun d hd => gapSet_card_le hc (by
        have := (mem_Ico.mp hd).1
        omega)
    _ = _ := two_mul_sum_Ico_id hH

/-- Total energy inside the division buckets is at most the diagonal plus
the all-positive-gap bound. -/
theorem blockPairs_twist_card_le {c : ZMod p} (hc : c ≠ 0)
    {H : ℕ} (hH : 0 < H) :
    (blockPairs (twist c) p H).card ≤ p + H * (H - 1) :=
  (blockPairs_card_le (twist c) p hH).trans
    (Nat.add_le_add_left (two_mul_shortPairs_card_le hc hH) p)

/-- Finite global block-partition energy bound, valid for every positive width. -/
theorem energy_le_block {c : ZMod p} (hc : c ≠ 0) {H : ℕ} (hH : 0 < H) :
    energy c ≤ (p / H + 1) * (p + H * (H - 1)) := by
  have hbucket : ∀ n ∈ range p, n / H ∈ range (p / H + 1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hn).le))
  calc
    energy c ≤ (p / H + 1) * (blockPairs (twist c) p H).card := by
      simpa only [energy, fullN, card_range, blockPairs] using
        sum_fiberCard_sq_le_card_mul_pairs (range p) (twist c) (fun n => n / H)
          univ (range (p / H + 1)) (fun _ _ => mem_univ _) hbucket
    _ ≤ _ := Nat.mul_le_mul_left _ (blockPairs_twist_card_le hc hH)

/-- Choosing one more than the integer square root gives a finite `O(p^(3/2))`
energy bound. It includes the prime `2` and every nonzero twist parameter. -/
theorem energy_le_three_mul_sqrt {c : ZMod p} (hc : c ≠ 0) :
    energy c ≤ 3 * p * (Nat.sqrt p + 1) := by
  have hH : 0 < Nat.sqrt p + 1 := Nat.succ_pos _
  have hB : p / (Nat.sqrt p + 1) + 1 ≤ Nat.sqrt p + 1 := by
    apply Nat.succ_le_of_lt
    exact (Nat.div_lt_iff_lt_mul hH).mpr (Nat.lt_succ_sqrt p)
  have hD : p + (Nat.sqrt p + 1) * (Nat.sqrt p + 1 - 1) ≤ 3 * p := by
    have hs := Nat.sqrt_le p
    have hs' := Nat.sqrt_le_self p
    simp only [Nat.add_sub_cancel]
    nlinarith
  calc
    energy c ≤ (p / (Nat.sqrt p + 1) + 1) *
        (p + (Nat.sqrt p + 1) * (Nat.sqrt p + 1 - 1)) := energy_le_block hc hH
    _ ≤ (Nat.sqrt p + 1) * (3 * p) := Nat.mul_le_mul hB hD
    _ = _ := Nat.mul_comm _ _

/-- Pointwise conversion from ordinary to binomial second moments. -/
theorem sq_eq_self_add_two_choose (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    ring

/-- Exact full-domain relation to the second binomial moment. No nonzero
hypothesis on `c` is needed for this counting identity. -/
theorem energy_eq_p_add_two_fullMoment (c : ZMod p) :
    energy c = p + 2 * fullMoment c 2 := by
  have htotal : (∑ a : ZMod p, fullN c a) = p := by
    simpa only [fullN, card_range] using
      sum_fiberCard_eq_card_of_subset (range p) (twist c) univ (subset_univ _)
  simp only [energy, fullMoment, binomialMoment, sq_eq_self_add_two_choose,
    sum_add_distrib, ← mul_sum, htotal]

/-- The energy is the full-domain count of ordered collision pairs. -/
theorem energy_eq_card_pairs (c : ZMod p) :
    energy c = (((range p) ×ˢ (range p)).filter fun ij =>
      twist c ij.1 = twist c ij.2).card := by
  simpa only [energy, fullN] using
    sum_fiberCard_sq_eq_card (range p) (twist c) univ (fun _ _ => mem_univ _)

/-- The global bound stated with the natural-number remainders used in `Spec`.
The domain includes zero, so it also bounds every positive-index subdomain. -/
theorem factorial_mod_collision_count_le :
    (((range p) ×ˢ (range p)).filter fun ij =>
      ij.1.factorial % p = ij.2.factorial % p).card ≤
        3 * p * (Nat.sqrt p + 1) := by
  have h := energy_le_three_mul_sqrt (c := (1 : ZMod p)) one_ne_zero
  rw [energy_eq_card_pairs] at h
  simpa only [twist, one_pow, one_mul, ZMod.natCast_eq_natCast_iff'] using h

/-- Exact endpoint bookkeeping in the positive-index notation. -/
theorem positive_secondMoment_bound {c : ZMod p} (hc : c ≠ 0) :
    p + 2 * (S2 c + N c 1) ≤ 3 * p * (Nat.sqrt p + 1) := by
  rw [← fullMoment_two_eq_S2_add, ← energy_eq_p_add_two_fullMoment]
  exact energy_le_three_mul_sqrt hc

end FactorialCollisionEnergy
