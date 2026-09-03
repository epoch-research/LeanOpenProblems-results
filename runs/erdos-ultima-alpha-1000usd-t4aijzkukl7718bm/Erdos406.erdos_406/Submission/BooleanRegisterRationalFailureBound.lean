import Submission.BooleanRegisterFailureBound

/-! Rational potentials can be rounded down. These are conditional criteria;
no automaton satisfying them is asserted to exist. -/
namespace Erdos406BooleanRegister

lemma floor_failure_step (q r : ℚ) (hq : 0 ≤ q) (hr : 0 ≤ r) (d k : ℕ)
    (h : (d : ℚ) + k * r ≤ q) : d + k * ⌊r⌋₊ ≤ ⌊q⌋₊ := by
  apply (Nat.le_floor_iff hq).mpr
  push_cast
  have hm := mul_le_mul_of_nonneg_left (Nat.floor_le hr) (Nat.cast_nonneg k)
  linarith

lemma positive_of_positive_floor (r : ℚ) (hr : 0 ≤ r) (h : 0 < ⌊r⌋₊) : 0 < r := by
  have hh : (0 : ℚ) < (⌊r⌋₊ : ℚ) := by exact_mod_cast h
  exact hh.trans_le (Nat.floor_le hr)

/-- The floor operation preserves every local bound needed by the natural-valued
certificate. In particular, allowing rational potentials does not weaken the
subsequent finite check. -/
theorem finite_of_rational_failure_checks {N : ℕ} (F : FiniteData N) (E : ℕ)
    (W : Fin N → Fin N → Fin 4 → ℚ)
    (hnonneg : ∀ s t c, 0 ≤ W s t c)
    (hstart : F.relation F.start F.start 0 = true)
    (hstep : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      F.relation (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) = true)
    (hbound : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      0 < W (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) →
      (d.val : ℚ) + 3 * W (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) ≤ W s t c)
    (hend : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 2),
      F.relation s t c = true →
      F.test (F.step s (digit (d.val + 1))) = false →
      F.test (F.toData.dfa.evalFrom
        (F.step t (digit (4 * (d.val + 1) + c.val)))
        (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
      (d.val : ℚ) + 1 ≤ W s t c)
    (hroot : W F.start F.start 0 < ((4 ^ E : ℕ) : ℚ))
    (hseed : F.test (F.toData.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (hgoodStart : F.good F.start = true)
    (hgoodStep : ∀ (s : Fin N) (d : Fin 2), F.good s = true →
      F.good (F.step s (digit d.val)) = true)
    (hgoodEnd : ∀ s : Fin N, F.good s = true →
      F.test (F.step s (digit 1)) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine finite_of_finite_failure_checks F E (fun s t c => ⌊W s t c⌋₊)
    hstart hstep ?_ ?_ ?_ hseed hgoodStart hgoodStep hgoodEnd
  · intro s t c d hr hp
    have hpos := positive_of_positive_floor _ (hnonneg _ _ _) hp
    exact floor_failure_step _ _ (hnonneg _ _ _) (hnonneg _ _ _) d.val 3
      (hbound s t c d hr hpos)
  · intro s t c d hr hi ho
    apply (Nat.le_floor_iff (hnonneg _ _ _)).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hend s t c d hr hi ho
  · exact (Nat.floor_lt (hnonneg _ _ _)).mpr hroot

#print axioms floor_failure_step
#print axioms positive_of_positive_floor
#print axioms finite_of_rational_failure_checks
end Erdos406BooleanRegister
