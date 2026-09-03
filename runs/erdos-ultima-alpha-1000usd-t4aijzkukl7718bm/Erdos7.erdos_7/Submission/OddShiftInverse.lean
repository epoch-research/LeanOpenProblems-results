import FormalConjecturesUtil

/-! Exact inversion of adding an odd-order cyclic shift. This is an auxiliary
algebraic lemma, not a solution of the odd covering conjecture. -/
namespace Erdos7OddShift
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Alternating adjacent sums telescope, including the endpoint sign. -/
theorem alternating_adjacent_sum (f : ℕ → ℚ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (-1 : ℚ)^j * (f j + f (j + 1))) =
      f 0 - (-1 : ℚ)^n * f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- If the shift has an odd period, its sum with the identity has this explicit
inverse over the rationals. No finiteness of the ambient additive group is
needed, only the displayed period for this shift. -/
theorem odd_period_inverse {G : Type*} [AddMonoid G]
    (k : G) (n : ℕ) (hn : Odd n) (hperiod : n • k = 0)
    (C D : G → ℚ) (hC : ∀ x, C x = D x + D (x + k)) (x : G) :
    (∑ j ∈ Finset.range n, (-1 : ℚ)^j * C (x + j • k)) = 2 * D x := by
  have hh := alternating_adjacent_sum (fun j => D (x + j • k)) n
  have he (j : ℕ) : C (x + j • k) =
      D (x + j • k) + D (x + (j + 1) • k) := by
    rw [hC, add_nsmul, one_nsmul, add_assoc]
  simp_rw [he]
  rw [hh, hn.neg_one_pow, hperiod]
  simp
  ring

/-- Adding a fixed odd-period shift is injective on rational-valued functions. -/
theorem odd_period_shift_injective {G : Type*} [AddMonoid G]
    (k : G) (n : ℕ) (hn : Odd n) (hperiod : n • k = 0) :
    Function.Injective (fun D : G → ℚ => fun x => D x + D (x + k)) := by
  intro D E h
  funext x
  have hD := odd_period_inverse k n hn hperiod
    (fun y => D y + D (y + k)) D (fun _ => rfl) x
  have hE := odd_period_inverse k n hn hperiod
    (fun y => E y + E (y + k)) E (fun _ => rfl) x
  have hs : (∑ j ∈ Finset.range n,
      (-1 : ℚ)^j * (D (x + j • k) + D ((x + j • k) + k))) =
      ∑ j ∈ Finset.range n,
        (-1 : ℚ)^j * (E (x + j • k) + E ((x + j • k) + k)) := by
    apply Finset.sum_congr rfl
    intro j _
    have he : D (x + j • k) + D ((x + j • k) + k) =
        E (x + j • k) + E ((x + j • k) + k) := congrFun h (x + j • k)
    rw [he]
  linarith

/-- Cyclic specialization used by exact subset-count coordinate updates. -/
theorem zmod_shift_injective {N : ℕ} (hN : Odd N) (k : ZMod N) :
    Function.Injective (fun D : ZMod N → ℚ => fun x => D x + D (x + k)) := by
  apply odd_period_shift_injective k N hN
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

#print axioms alternating_adjacent_sum
#print axioms odd_period_inverse
#print axioms odd_period_shift_injective
#print axioms zmod_shift_injective
end Erdos7OddShift
