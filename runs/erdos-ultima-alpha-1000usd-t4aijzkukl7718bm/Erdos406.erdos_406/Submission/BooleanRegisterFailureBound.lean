import Submission.BooleanRegisterFiniteCheck

/-! A conditional bound on all canonical multiplication-closure failures.
No bounded-failure register system is asserted to exist. -/
namespace Erdos406BooleanRegister

/-- A local natural-valued bound on continuations bounds every failed input. -/
theorem failure_le_potential {σ : Type*} (D : Data σ)
    (R : σ → σ → ℕ → Prop) (V : σ → σ → ℕ → ℕ)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hbound : ∀ s t c d, c < 4 → d < 3 → R s t c →
      0 < V (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3) →
      d + 3 * V (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3) ≤
        V s t c)
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c →
      D.test (D.step s d) = false →
      D.test (D.dfa.evalFrom (D.step t ((4 * d + c) % 3))
        (Nat.digits 3 ((4 * d + c) / 3))) = true → d ≤ V s t c) :
    ∀ n : ℕ, 0 < n → ∀ s t c, c < 4 → R s t c →
      D.test (D.dfa.evalFrom s (Nat.digits 3 n)) = false →
      D.test (D.dfa.evalFrom t (Nat.digits 3 (4 * n + c))) = true → n ≤ V s t c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s t c hc hr hi ho
    have hd : n % 3 < 3 := Nat.mod_lt _ (by decide)
    have hp : 0 < 4 * n + c := by omega
    have hm : (4 * n + c) % 3 = (4 * (n % 3) + c) % 3 := by omega
    have hq : (4 * n + c) / 3 = 4 * (n / 3) + (4 * (n % 3) + c) / 3 := by omega
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hn] at hi
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp, hm, hq] at ho
    simp only [DFA.evalFrom_cons, Data.dfa] at hi ho
    by_cases hz : n / 3 = 0
    · have hdp : 0 < n % 3 := by omega
      simp only [hz, Nat.digits_zero, DFA.evalFrom_nil, mul_zero, zero_add] at hi ho
      have hh := hend s t c (n % 3) hc hdp hd hr hi ho
      omega
    · have hnp : 0 < n / 3 := by omega
      have hcp : (4 * (n % 3) + c) / 3 < 4 := by omega
      have hrel := hstep s t c (n % 3) hc hd hr
      have hb := ih (n / 3) (Nat.div_lt_self hn (by decide)) hnp
        (D.step s (n % 3)) (D.step t ((4 * (n % 3) + c) % 3))
        ((4 * (n % 3) + c) / 3) hcp hrel hi ho
      have hvp : 0 < V (D.step s (n % 3)) (D.step t ((4 * (n % 3) + c) % 3))
          ((4 * (n % 3) + c) / 3) := by omega
      have hh := hbound s t c (n % 3) hc hd hr hvp
      omega

/-- Above the root potential, a failed backward implication is impossible. -/
theorem backward_above_potential {σ : Type*} (D : Data σ)
    (R : σ → σ → ℕ → Prop) (V : σ → σ → ℕ → ℕ)
    (hstart : R D.start D.start 0)
    (hfail : ∀ n : ℕ, 0 < n → ∀ s t c, c < 4 → R s t c →
      D.test (D.dfa.evalFrom s (Nat.digits 3 n)) = false →
      D.test (D.dfa.evalFrom t (Nat.digits 3 (4 * n + c))) = true → n ≤ V s t c)
    (n : ℕ) (hn : V D.start D.start 0 < n)
    (ho : D.test (D.dfa.eval (Nat.digits 3 (4 * n))) = true) :
    D.test (D.dfa.eval (Nat.digits 3 n)) = true := by
  cases hi : D.test (D.dfa.eval (Nat.digits 3 n)) with
  | true => rfl
  | false =>
    have hh := hfail n (by omega) D.start D.start 0 (by decide) hstart hi
      (by simpa only [Nat.add_zero, DFA.eval] using ho)
    omega

/-- A rejected power above a checked bound for all closure failures suffices.
The existence of a suitable potential and register system remains unproved. -/
theorem finite_of_failure_bound {σ : Type*} (D : Data σ) (E : ℕ)
    (R : σ → σ → ℕ → Prop) (V : σ → σ → ℕ → ℕ)
    (hstart : R D.start D.start 0)
    (hstep : ∀ s t c d, c < 4 → d < 3 → R s t c →
      R (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3))
    (hbound : ∀ s t c d, c < 4 → d < 3 → R s t c →
      0 < V (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3) →
      d + 3 * V (D.step s d) (D.step t ((4 * d + c) % 3)) ((4 * d + c) / 3) ≤
        V s t c)
    (hend : ∀ s t c d, c < 4 → 0 < d → d < 3 → R s t c →
      D.test (D.step s d) = false →
      D.test (D.dfa.evalFrom (D.step t ((4 * d + c) % 3))
        (Nat.digits 3 ((4 * d + c) / 3))) = true → d ≤ V s t c)
    (hroot : V D.start D.start 0 < 4 ^ E)
    (hseed : D.test (D.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (G : σ → Prop) (hgoodStart : G D.start)
    (hgoodStep : ∀ s d, d < 2 → G s → G (D.step s d))
    (hgoodEnd : ∀ s, G s → D.test (D.step s 1) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hfail := failure_le_potential D R V hstep hbound hend
  have htail : ∀ j : ℕ, D.test (D.dfa.eval (Nat.digits 3 (4 ^ (E + j)))) = false := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero] using hseed
    | succ j ih =>
      cases ho : D.test (D.dfa.eval (Nat.digits 3 (4 ^ (E + (j + 1))))) with
      | false => rfl
      | true =>
        have hpow : 4 ^ E ≤ 4 ^ (E + j) := Nat.pow_le_pow_right (by decide) (by omega)
        have hh := backward_above_potential D R V hstart hfail (4 ^ (E + j))
          (hroot.trans_le hpow) (by simpa only [Nat.add_succ, pow_succ'] using ho)
        cases (ih.symm.trans hh)
  apply (Set.finite_Iic (4 ^ E)).subset
  rintro n ⟨⟨k, rfl⟩, hd⟩
  obtain ⟨m, hm⟩ := Erdos406Certificate.even_exponent hd
  have hp : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [hp] at hd ⊢
  by_cases hEm : E ≤ m
  · have ht := htail (m - E)
    rw [Nat.add_sub_of_le hEm] at ht
    have hgood := Erdos406Certificate.dfa_good_reject D.dfa G hgoodStart hgoodStep
      (fun s hs hh => by
        have hh' := hgoodEnd s hs
        change D.test (D.step s 1) = false at hh
        simp [hh] at hh') (by positivity : 0 < 4 ^ m) hd
    exact False.elim (hgood ht)
  · exact Nat.pow_le_pow_right (by decide) (by omega)

#print axioms failure_le_potential

/-- Explicitly finite obligations for a bounded-failure certificate. -/
theorem finite_of_finite_failure_checks {N : ℕ} (F : FiniteData N) (E : ℕ)
    (V : Fin N → Fin N → Fin 4 → ℕ)
    (hstart : F.relation F.start F.start 0 = true)
    (hstep : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      F.relation (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) = true)
    (hbound : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 3),
      F.relation s t c = true →
      0 < V (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) →
      d.val + 3 * V (F.step s d) (F.step t (digit (4 * d.val + c.val)))
        (carry ((4 * d.val + c.val) / 3)) ≤ V s t c)
    (hend : ∀ (s t : Fin N) (c : Fin 4) (d : Fin 2),
      F.relation s t c = true → F.test (F.step s (digit (d.val + 1))) = false →
      F.test (F.toData.dfa.evalFrom
        (F.step t (digit (4 * (d.val + 1) + c.val)))
        (Nat.digits 3 ((4 * (d.val + 1) + c.val) / 3))) = true →
      d.val + 1 ≤ V s t c)
    (hroot : V F.start F.start 0 < 4 ^ E)
    (hseed : F.test (F.toData.dfa.eval (Nat.digits 3 (4 ^ E))) = false)
    (hgoodStart : F.good F.start = true)
    (hgoodStep : ∀ (s : Fin N) (d : Fin 2), F.good s = true →
      F.good (F.step s (digit d.val)) = true)
    (hgoodEnd : ∀ s : Fin N, F.good s = true →
      F.test (F.step s (digit 1)) = true) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine finite_of_failure_bound F.toData E
    (fun s t c => F.relation s t (carry c) = true) (fun s t c => V s t (carry c))
    hstart ?_ ?_ ?_ hroot hseed (fun s => F.good s = true) hgoodStart ?_ hgoodEnd
  · intro s t c d hc hd hr
    have hh := hstep s t ⟨c, hc⟩ ⟨d, hd⟩
      (by simpa only [carry, Nat.mod_eq_of_lt hc] using hr)
    simpa only [FiniteData.toData, digit, Nat.mod_mod, Nat.mod_eq_of_lt hd] using hh
  · intro s t c d hc hd hr hv
    have hh := hbound s t ⟨c, hc⟩ ⟨d, hd⟩
      (by simpa only [carry, Nat.mod_eq_of_lt hc] using hr)
    have hv' : 0 < V (F.step s ⟨d, hd⟩) (F.step t (digit (4 * d + c)))
        (carry ((4 * d + c) / 3)) := by
      simpa only [FiniteData.toData, digit, Nat.mod_mod, Nat.mod_eq_of_lt hd] using hv
    have hout := hh hv'
    simpa only [FiniteData.toData, digit, carry, Nat.mod_mod,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hc] using hout
  · intro s t c d hc hd hd3 hr hi ho
    let i : Fin 2 := ⟨d - 1, by omega⟩
    have hdi : i.val + 1 = d := by dsimp [i]; omega
    have hh := hend s t ⟨c, hc⟩ i
      (by simpa only [carry, Nat.mod_eq_of_lt hc] using hr)
    simp only [hdi, FiniteData.toData, digit, Nat.mod_mod] at hh hi ho
    have hout := hh hi ho
    simpa only [carry, Nat.mod_eq_of_lt hc] using hout
  · intro s d hd hs
    exact hgoodStep s ⟨d, hd⟩ hs

#print axioms finite_of_finite_failure_checks

#print axioms finite_of_failure_bound
end Erdos406BooleanRegister
