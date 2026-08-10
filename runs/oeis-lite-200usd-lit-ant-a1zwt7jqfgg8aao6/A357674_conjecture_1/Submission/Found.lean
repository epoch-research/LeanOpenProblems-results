import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Wolst

/-- Extract a factor of `p` from a `ZMod N` element whose `val` is divisible by `p`. -/
lemma exists_p_mul {N : ℕ} [NeZero N] {p : ℕ} (x : ZMod N) (hx : p ∣ x.val) :
    ∃ w : ZMod N, x = p * w := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod N), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hm]
  push_cast
  ring

variable {p : ℕ} [Fact p.Prime]

/-- For `0 < i < p`, the cast of `i` is a unit in `ZMod (p^k)`. -/
lemma isUnit_cast {k : ℕ} (i : ℕ) (hi : 0 < i) (hip : i < p) :
    IsUnit ((i : ZMod (p ^ k))) := by
  rw [ZMod.isUnit_iff_coprime]
  have hpp : p.Prime := Fact.out
  have h1 : Nat.Coprime p i := (hpp.coprime_iff_not_dvd).mpr (fun h => by
    have := Nat.le_of_dvd hi h; omega)
  exact (h1.symm).pow_right k

/-- Bridge: a sum over `range p` of a function of casts equals the sum over all of `ZMod p`. -/
theorem sum_range_eq_univ {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  have : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  apply Finset.sum_nbij' (fun i => ((i : ℕ) : ZMod p)) ZMod.val
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

/-- Sum of positive powers over `1..p-1` vanishes mod `p` (Fermat). -/
theorem sum_pow_Ico_eq_zero (m : ℕ) (hm1 : 1 ≤ m) (hm : m < p - 1) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p))^m = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have key : ∑ x : ZMod p, x ^ m = 0 := by
    rw [FiniteField.sum_pow_lt_card_sub_one]; rw [hcard]; omega
  have h0 : ∑ i ∈ Finset.range p, ((i : ZMod p))^m = ∑ x : ZMod p, x ^ m :=
    sum_range_eq_univ (fun x => x ^ m)
  have hsplit : ∑ i ∈ Finset.range p, ((i : ZMod p))^m
      = ((0 : ZMod p))^m + ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p))^m := by
    have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : (1:ℕ) ≤ p)]
    simp
  rw [h0] at hsplit
  rw [key] at hsplit
  have : ((0 : ZMod p))^m = 0 := by
    rw [zero_pow]; omega
  rw [this, zero_add] at hsplit
  exact hsplit.symm

end Wolst
