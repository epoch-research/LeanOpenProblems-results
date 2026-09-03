import Submission.BooleanRegisterCertificates

/-! Finite, decidable obligations for the Boolean-register search.
This supplies no certificate witness and does not settle the conjecture. -/
namespace Erdos406BooleanRegister

structure FiniteData (N : ℕ) where
  step : Fin N → Fin 3 → Fin N
  start : Fin N
  test : Fin N → Bool
  good : Fin N → Bool
  relation : Fin N → Fin N → Fin 4 → Bool

def digit (d : ℕ) : Fin 3 := ⟨d % 3, Nat.mod_lt _ (by decide)⟩
def carry (c : ℕ) : Fin 4 := ⟨c % 4, Nat.mod_lt _ (by decide)⟩

def FiniteData.toData {N : ℕ} (F : FiniteData N) : Data (Fin N) where
  step s d := F.step s (digit d)
  start := F.start
  test := F.test

lemma digit_val (d : Fin 3) : digit d.val = d := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt d.isLt

lemma carry_val (c : Fin 4) : carry c.val = c := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt c.isLt

/-- All the non-seed obligations quantify over fixed finite types. In a
concrete certificate they can be checked by ordinary kernel reduction. -/
theorem finite_of_finite_checks {N : ℕ} (F : FiniteData N) (E : ℕ)
    (hstart : F.relation F.start F.start 0 = true)
    (hstep : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      F.relation (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) = true)
    (hend : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 2),
      F.relation s t c = true →
      F.test (F.toData.dfa.evalFrom
        (F.step t (digit (4 * (d.val + 1) + c.val)))
        (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
      F.test (F.step s (digit (d.val + 1))) = true)
    (hseed : F.test (F.toData.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (hgoodStart : F.good F.start = true)
    (hgoodStep : ∀ (s : Fin N) (d : Fin 2), F.good s = true →
      F.good (F.step s (digit d.val)) = true)
    (hgoodEnd : ∀ s : Fin N, F.good s = true →
      F.test (F.step s (digit 1)) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine finite_of_checks F.toData E (fun s t c => F.relation s t (carry c) = true)
    hstart ?_ ?_ hseed (fun s => F.good s = true) hgoodStart ?_ hgoodEnd
  · intro s t c d hc hd hr
    have hh := hstep s t ⟨c, hc⟩ ⟨d, hd⟩ (by simpa only [carry, Nat.mod_eq_of_lt hc] using hr)
    simpa only [FiniteData.toData, digit, Nat.mod_mod, Nat.mod_eq_of_lt hd] using hh
  · intro s t c d hc hd hd3 hr ha
    let i : Fin 2 := ⟨d - 1, by omega⟩
    have hi : i.val + 1 = d := by dsimp [i]; omega
    have hh := hend s t ⟨c, hc⟩ i (by simpa only [carry, Nat.mod_eq_of_lt hc] using hr)
    simp only [hi, FiniteData.toData, digit, Nat.mod_mod] at hh ha ⊢
    exact hh ha
  · intro s d hd hs
    exact hgoodStep s ⟨d, hd⟩ hs

#print axioms finite_of_finite_checks
end Erdos406BooleanRegister
