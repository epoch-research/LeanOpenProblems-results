import Submission.IntervalRescaling

/-! An interval-aware recursive sieve. The floor/ceiling lengths occur inside the
recursive bounds, rather than being replaced by independent unit moment errors.
The soundness theorem does not assert uniform quadratic positivity. -/
namespace Erdos970.IntervalRescaling
open BlockSieve.SievePolynomial

theorem count_succ_partition (p r : ℕ → ℕ) (k m : ℕ) :
    firstHitCount p r k m + count p r (k + 1) m = count p r k m := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.range m).filter (fun x => ∀ j < k, ¬x ≡ r j [MOD p j]))
    (fun x => x ≡ r k [MOD p k])
  simpa only [Finset.filter_filter, Nat.forall_lt_succ_right, count, firstHitCount,
    and_comm] using h

theorem count_firstHit_tail (p r : ℕ → ℕ) (b k m : ℕ) (hbk : b ≤ k) :
    count p r k m + ∑ i : Fin k, (if b ≤ i.val then firstHitCount p r i.val m else 0) =
      count p r b m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if b ≤ i then firstHitCount p r i m else 0) k]
  induction k, hbk using Nat.le_induction with
  | base =>
    have hz : (∑ i ∈ Finset.range b, if b ≤ i then firstHitCount p r i m else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (Nat.not_le_of_lt (Finset.mem_range.mp hi))
    rw [hz, Nat.add_zero]
  | succ k hk ih =>
    rw [Finset.sum_range_succ, if_pos hk]
    have hh := count_succ_partition p r k m
    omega

/-- Base functions may use any verified wheel counts. The `keep` flag permits
pruning lower branches, without asserting that any omitted branch was zero. -/
def intervalEnvelope (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℕ)
    (keep : ℕ → ℕ → Bool) (k m : ℕ) : ℕ × ℕ :=
  if k ≤ b then (lo m, hi m) else
    (if keep k m then lo m - ∑ i : Fin k, if b ≤ i.val then
        (intervalEnvelope p b lo hi keep i.val (ceilQuotient m (p i.val))).2 else 0
      else 0,
     hi m - ∑ i : Fin k, if b ≤ i.val then
        (intervalEnvelope p b lo hi keep i.val (m / p i.val)).1 else 0)
termination_by k

/-- Exact interval rescaling proves both recursive bounds for any pairwise
coprime positive indexed moduli. No comparison with the first primes is needed. -/
theorem intervalEnvelope_sound (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℕ)
    (keep : ℕ → ℕ → Bool)
    (hlo : ∀ m r, lo m ≤ count p r b m)
    (hhi : ∀ m r, count p r b m ≤ hi m)
    (k : ℕ) (hbk : b ≤ k)
    (hp : ∀ i < k, 0 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j)) (m : ℕ) (r : ℕ → ℕ) :
    (intervalEnvelope p b lo hi keep k m).1 ≤ count p r k m ∧
      count p r k m ≤ (intervalEnvelope p b lo hi keep k m).2 := by
  induction k using Nat.strong_induction_on generalizing m r with
  | h k ih =>
    by_cases hk : k ≤ b
    · have heq : k = b := by omega
      subst k
      simpa only [intervalEnvelope, le_refl, ↓reduceIte] using ⟨hlo m r, hhi m r⟩
    · have hrescale (i : Fin k) (hbi : b ≤ i.val) :
          (intervalEnvelope p b lo hi keep i.val (m / p i.val)).1 ≤
            firstHitCount p r i.val m ∧
          firstHitCount p r i.val m ≤
            (intervalEnvelope p b lo hi keep i.val (ceilQuotient m (p i.val))).2 := by
        obtain ⟨c, s, hcl, hcu, he⟩ := firstHitCount_rescale p r i.val m (hp i i.isLt)
          (fun j hj => hp j (hj.trans i.isLt)) (hcop i i.isLt)
        have hli := ih i.val i.isLt hbi
          (fun j hj => hp j (hj.trans i.isLt))
          (fun j hj => hcop j (hj.trans i.isLt)) (m / p i.val) s
        have hui := ih i.val i.isLt hbi
          (fun j hj => hp j (hj.trans i.isLt))
          (fun j hj => hcop j (hj.trans i.isLt)) (ceilQuotient m (p i.val)) s
        rw [he]
        exact ⟨hli.1.trans (count_mono_length p s i.val hcl),
          (count_mono_length p s i.val hcu).trans hui.2⟩
      have hsumlo : (∑ i : Fin k, if b ≤ i.val then
          (intervalEnvelope p b lo hi keep i.val (m / p i.val)).1 else 0) ≤
          ∑ i : Fin k, if b ≤ i.val then firstHitCount p r i.val m else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with hbi
        · exact (hrescale i hbi).1
        · rfl
      have hsumhi : (∑ i : Fin k, if b ≤ i.val then firstHitCount p r i.val m else 0) ≤
          ∑ i : Fin k, if b ≤ i.val then
            (intervalEnvelope p b lo hi keep i.val (ceilQuotient m (p i.val))).2 else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with hbi
        · exact (hrescale i hbi).2
        · rfl
      have hpart := count_firstHit_tail p r b k m hbk
      have hl := hlo m r
      have hu := hhi m r
      rw [intervalEnvelope, if_neg hk]
      dsimp only
      constructor
      · split_ifs <;> omega
      · omega

/-- Positivity of the actual interval envelope gives a survivor for the given
moduli. This is not a transfer from smaller reference primes. -/
theorem survivor_of_positive_intervalEnvelope (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℕ)
    (keep : ℕ → ℕ → Bool)
    (hlo : ∀ m r, lo m ≤ count p r b m)
    (hhi : ∀ m r, count p r b m ≤ hi m)
    (k : ℕ) (hbk : b ≤ k)
    (hp : ∀ i < k, 0 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j)) (m : ℕ)
    (hpos : 0 < (intervalEnvelope p b lo hi keep k m).1) (r : ℕ → ℕ) :
    ∃ x < m, ∀ j < k, ¬x ≡ r j [MOD p j] := by
  have h := hpos.trans_le (intervalEnvelope_sound p b lo hi keep hlo hhi k hbk hp hcop m r).1
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

#print axioms intervalEnvelope_sound
#print axioms survivor_of_positive_intervalEnvelope
end Erdos970.IntervalRescaling
