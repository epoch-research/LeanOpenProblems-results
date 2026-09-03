import Submission.BackwardNFASelfContained

/-! Strided backward NFA simulations. The covering automaton may be different
for each exponent residue class. No rejected-seed certificate is supplied. -/
namespace Erdos406BackwardStrided
open Erdos406BackwardStandalone

theorem finite_of_backward_family (s E : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → Prop)
    (hseed : ∀ r, r < s → ¬ Q r (4 ^ (E + r)))
    (hback : ∀ r, r < s → ∀ n, Q r (4 ^ s * n) → Q r n)
    (hcover : ∀ r, r < s → ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q r n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have htail : ∀ r, r < s → ∀ j : ℕ, ¬ Q r (4 ^ (E + r + s * j)) := by
    intro r hr j
    induction j with
    | zero => simpa using hseed r hr
    | succ j ih =>
      intro hq
      apply ih
      apply hback r hr
      have he : E + r + s * (j + 1) = s + (E + r + s * j) := by ring
      simpa only [he, pow_add] using hq
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨4 ^ E, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := even_exponent hg
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hg ⊢
  by_cases hEm : E ≤ m
  · have hr : (m - E) % s < s := Nat.mod_lt _ hs
    have heq : E + (m - E) % s + s * ((m - E) / s) = m := by
      have hdiv := Nat.mod_add_div (m - E) s
      omega
    apply False.elim
    apply htail ((m - E) % s) hr ((m - E) / s)
    rw [heq]
    exact hcover _ hr _ (by positivity) hg
  · exact Nat.pow_le_pow_right (by decide) (by omega)

theorem finite_of_backward_pair (E : ℕ) (Q₀ Q₁ : ℕ → Prop)
    (hseed₀ : ¬ Q₀ (4 ^ E)) (hseed₁ : ¬ Q₁ (4 ^ (E + 1)))
    (hback₀ : ∀ n, Q₀ (16 * n) → Q₀ n)
    (hback₁ : ∀ n, Q₁ (16 * n) → Q₁ n)
    (hcover₀ : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q₀ n)
    (hcover₁ : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q₁ n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply finite_of_backward_family 2 E (by decide) (fun r => if r = 0 then Q₀ else Q₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hseed₀ | exact hseed₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hback₀ | exact hback₁)
  · intro r hr
    interval_cases r <;> simpa using (by first | exact hcover₀ | exact hcover₁)

structure Simulation (σ : Type*) (K : ℕ) where
  factor_pos : 0 < K
  M : NFA ℕ σ
  R : σ → σ → ℕ → Prop
  initial : ∀ c, c < K → ∀ p ∈ evalNat M.toDFA c, ∃ q ∈ M.start, R p q c
  step : ∀ p q c d e c' r,
    c < K → d < 3 → e < 3 → c' < K → K * d + c' = 3 * c + e →
    R p q c → r ∈ M.step p e → ∃ t ∈ M.step q d, R r t c'
  finish : ∀ p q, R p q 0 → p ∈ M.accept → q ∈ M.accept

namespace Simulation
variable {σ : Type*} {K : ℕ} (C : Simulation σ K)

theorem match_output : ∀ n c, c < K → ∀ p ∈ evalNat C.M.toDFA (K * n + c),
    ∃ q ∈ evalNat C.M.toDFA n, C.R p q c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc p hp
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hp
      obtain ⟨q, hq, hr⟩ := C.initial c hc p hp
      exact ⟨q, by simpa only [evalNat_zero, NFA.toDFA] using hq, hr⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hK := C.factor_pos
      let d := n % 3
      let a := (K * d + c) / 3
      let e := (K * d + c) % 3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have ha : a < K := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
        nlinarith
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcarry : K * d + c = 3 * a + e := by dsimp [a, e]; omega
      have hdiv : (K * n + c) / 3 = K * (n / 3) + a := (affine_div_mod K n c).1
      have hmod : (K * n + c) % 3 = e := (affine_div_mod K n c).2
      rw [evalNat_pos C.M.toDFA (by positivity : 0 < K * n + c), hdiv, hmod] at hp
      obtain ⟨r, hr, hrp⟩ := NFA.mem_stepSet.mp hp
      obtain ⟨q, hq, hrq⟩ := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) a ha r hr
      obtain ⟨t, hqt, hpt⟩ := C.step r q a d e c p ha hd he hc hcarry hrq hrp
      refine ⟨t, ?_, hpt⟩
      rw [evalNat_pos C.M.toDFA hnpos]
      exact NFA.mem_stepSet.mpr ⟨q, hq, hqt⟩

theorem backward (n : ℕ) : acceptsNat C.M (K * n) → acceptsNat C.M n := by
  rintro ⟨p, hp, hpa⟩
  obtain ⟨q, hq, hpq⟩ := C.match_output n 0 C.factor_pos p (by simpa using hp)
  exact ⟨q, hq, C.finish p q hpq hpa⟩

theorem rejects_mul_orbit (x : ℕ) (hseed : ¬ acceptsNat C.M x) (j : ℕ) :
    ¬ acceptsNat C.M (K ^ j * x) := by
  induction j with
  | zero => simpa using hseed
  | succ j ih =>
    intro hq
    apply ih
    apply C.backward
    simpa only [pow_succ', mul_assoc] using hq

end Simulation

variable {σ : Type*} [DecidableEq σ]
/-- Finite data use the same evaluation interface as one-step simulations. -/
def checkedSimulation (D : Data σ) (K : ℕ) (hK : 0 < K)
    (hinit : ∀ c, c < K → ∀ p ∈ D.evalStates c,
      (D.start ∩ D.relation p c).Nonempty)
    (hstep : ∀ p d, d < 3 → ∀ c', c' < K →
      ∀ r ∈ D.step p ((K * d + c') % 3),
      ∀ q ∈ D.relation p ((K * d + c') / 3),
      (D.step q d ∩ D.relation r c').Nonempty)
    (hfinish : ∀ p ∈ D.accept, D.relation p 0 ⊆ D.accept) : Simulation σ K where
  factor_pos := hK
  M := D.toNFA
  R p q c := q ∈ D.relation p c
  initial := by
    intro c hc p hp
    rw [← D.evalStates_coe] at hp
    obtain ⟨q, hq⟩ := hinit c hc p hp
    exact ⟨q, (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  step := by
    intro p q c d e c' r hc hd he hc' hcarry hpq hr
    have hv : (K * d + c') / 3 = c := by omega
    have hm : (K * d + c') % 3 = e := by omega
    obtain ⟨t, ht⟩ := hstep p d hd c' hc' r (by simpa only [hm] using hr)
      q (by simpa only [hv] using hpq)
    exact ⟨t, (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩
  finish := by
    intro p q hpq hp
    exact hfinish p hp hpq

#print axioms finite_of_backward_family
#print axioms finite_of_backward_pair
#print axioms Simulation.match_output
#print axioms checkedSimulation
end Erdos406BackwardStrided
