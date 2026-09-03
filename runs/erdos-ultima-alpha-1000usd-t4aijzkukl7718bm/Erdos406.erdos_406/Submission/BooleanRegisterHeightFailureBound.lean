import Submission.BooleanRegisterFailureBound

/-! A conditional certificate criterion using bounds on failure-word length.
No register system satisfying these hypotheses is asserted to exist. -/
namespace Erdos406BooleanRegister

lemma height_failure_step (a b d : ℕ) (hab : b < a) (hd : d < 3) :
    d + 3 * (3 ^ b - 1) ≤ 3 ^ a - 1 := by
  have hp : 0 < (3 : ℕ) ^ b := pow_pos (by decide) _
  have hq : 0 < (3 : ℕ) ^ a := pow_pos (by decide) _
  have hle : 3 ^ b * 3 ≤ (3 : ℕ) ^ a := by
    simpa only [pow_succ] using
      (Nat.pow_le_pow_right (by decide : 0 < 3) (show b + 1 ≤ a by omega))
  omega

/-- Strict descent of a positive failure-height supplies an ordinary natural
potential via `3^height-1`. This is only an implication from explicit checks. -/
theorem finite_of_height_failure_checks {N : ℕ} (F : FiniteData N) (E : ℕ)
    (H : Fin N → Fin N → Fin 4 → ℕ)
    (hstart : F.relation F.start F.start 0 = true)
    (hstep : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      F.relation (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) = true)
    (hbound : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      0 < H (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) →
      H (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) < H s t c)
    (hend : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 2),
      F.relation s t c = true →
      F.test (F.step s (digit (d.val + 1))) = false →
      F.test (F.toData.dfa.evalFrom
        (F.step t (digit (4 * (d.val + 1) + c.val)))
        (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
      0 < H s t c)
    (hroot : 3 ^ H F.start F.start 0 ≤ 4 ^ E)
    (hseed : F.test (F.toData.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (hgoodStart : F.good F.start = true)
    (hgoodStep : ∀ (s : Fin N) (d : Fin 2), F.good s = true →
      F.good (F.step s (digit d.val)) = true)
    (hgoodEnd : ∀ s : Fin N, F.good s = true →
      F.test (F.step s (digit 1)) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine finite_of_finite_failure_checks F E (fun s t c => 3 ^ H s t c - 1)
    hstart hstep ?_ ?_ ?_ hseed hgoodStart hgoodStep hgoodEnd
  · intro s t c d hr hp
    have hpos : 0 < H (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) := by
      by_contra hn
      have hz : H (F.step s d) (F.step t (digit (4 * d.val + c.val)))
          (carry ((4 * d.val + c.val) / 3)) = 0 := by omega
      simp only [hz, pow_zero, Nat.sub_self, lt_self_iff_false] at hp
    exact height_failure_step _ _ d.val (hbound s t c d hr hpos) d.isLt
  · intro s t c d hr hi ho
    have hh := height_failure_step (H s t c) 0 (d.val + 1)
      (hend s t c d hr hi ho) (by omega)
    simpa only [pow_zero, Nat.sub_self, mul_zero, add_zero] using hh
  · change 3 ^ H F.start F.start 0 - 1 < 4 ^ E
    have hp : 0 < (3 : ℕ) ^ H F.start F.start 0 := pow_pos (by decide) _
    omega

#print axioms height_failure_step
#print axioms finite_of_height_failure_checks
end Erdos406BooleanRegister
