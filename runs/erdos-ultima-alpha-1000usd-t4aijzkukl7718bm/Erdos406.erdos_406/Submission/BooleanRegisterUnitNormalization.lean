import Submission.BooleanRegisterCertificates

/-! A two-state normalization of a putative regular certificate. It does not
construct a certificate or prove the missing-digit conjecture. -/
namespace Erdos406BooleanRegister

/-- New initial state, accepting sink, and copies of the original states. -/
def normalizeUnit {σ : Type*} (D : Data σ) : Data (Option (Option σ)) where
  start := none
  step
    | none, d => if d = 1 then some (some (D.step D.start 1)) else some none
    | some none, _ => some none
    | some (some s), d => some (some (D.step s d))
  test
    | none => true
    | some none => true
    | some (some s) => D.test s

lemma normalizeUnit_evalFrom_lift {σ : Type*} (D : Data σ) (s : σ) (w : List ℕ) :
    (normalizeUnit D).dfa.evalFrom (some (some s)) w =
      some (some (D.dfa.evalFrom s w)) := by
  induction w generalizing s with
  | nil => rfl
  | cons d w ih =>
    change (normalizeUnit D).dfa.evalFrom (some (some (D.step s d))) w =
      some (some (D.dfa.evalFrom (D.step s d) w))
    exact ih (D.step s d)

lemma normalizeUnit_evalFrom_sink {σ : Type*} (D : Data σ) (w : List ℕ) :
    (normalizeUnit D).dfa.evalFrom (some none) w = some none := by
  induction w with
  | nil => rfl
  | cons d w ih => exact ih

/-- Only the unit residue class is tested by the old automaton. -/
lemma normalizeUnit_eval {σ : Type*} (D : Data σ) (n : ℕ) :
    (normalizeUnit D).test ((normalizeUnit D).dfa.eval (Nat.digits 3 n)) =
      if n % 3 = 1 then D.test (D.dfa.eval (Nat.digits 3 n)) else true := by
  by_cases hn : n = 0
  · subst n
    simp [normalizeUnit, Data.dfa, DFA.eval]
  · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) (by omega : 0 < n)]
    simp only [DFA.eval, DFA.evalFrom_cons]
    change (normalizeUnit D).test ((normalizeUnit D).dfa.evalFrom
      (if n % 3 = 1 then some (some (D.step D.start 1)) else some none)
      (Nat.digits 3 (n / 3))) =
      if n % 3 = 1 then D.test (D.dfa.evalFrom (D.step D.start (n % 3))
        (Nat.digits 3 (n / 3))) else true
    by_cases hu : n % 3 = 1
    · rw [if_pos hu, if_pos hu, normalizeUnit_evalFrom_lift]
      change D.test (D.dfa.evalFrom (D.step D.start 1) (Nat.digits 3 (n / 3))) = _
      rw [hu]
    · rw [if_neg hu, if_neg hu, normalizeUnit_evalFrom_sink]
      rfl

lemma normalizeUnit_accept_iff {σ : Type*} (D : Data σ) (n : ℕ) :
    (normalizeUnit D).test ((normalizeUnit D).dfa.eval (Nat.digits 3 n)) = true ↔
      n % 3 ≠ 1 ∨ D.test (D.dfa.eval (Nat.digits 3 n)) = true := by
  rw [normalizeUnit_eval]
  by_cases hu : n % 3 = 1 <;> simp [hu]

lemma normalizeUnit_good {σ : Type*} (D : Data σ)
    (hgood : ∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      D.test (D.dfa.eval (Nat.digits 3 n)) = true)
    (n : ℕ) (hn : Nat.digits 3 n ⊆ [0, 1]) :
    (normalizeUnit D).test ((normalizeUnit D).dfa.eval (Nat.digits 3 n)) = true := by
  apply (normalizeUnit_accept_iff D n).mpr
  by_cases hz : n = 0
  · left
    simp [hz]
  · exact Or.inr (hgood n (by omega) hn)

/-- Above any given threshold, backward closure is preserved. -/
lemma normalizeUnit_backward {σ : Type*} (D : Data σ) (B : ℕ)
    (hback : ∀ n : ℕ, B < n → D.test (D.dfa.eval (Nat.digits 3 (4 * n))) = true →
      D.test (D.dfa.eval (Nat.digits 3 n)) = true)
    (n : ℕ) (hn : B < n)
    (ho : (normalizeUnit D).test
      ((normalizeUnit D).dfa.eval (Nat.digits 3 (4 * n))) = true) :
    (normalizeUnit D).test ((normalizeUnit D).dfa.eval (Nat.digits 3 n)) = true := by
  rw [normalizeUnit_accept_iff] at ho ⊢
  by_cases hu : n % 3 = 1
  · right
    apply hback n hn
    rcases ho with hnot | hold
    · exact False.elim (hnot (by omega))
    · exact hold
  · exact Or.inl hu

lemma normalizeUnit_power_seed {σ : Type*} (D : Data σ) (E : ℕ) :
    (normalizeUnit D).test ((normalizeUnit D).dfa.eval (Nat.digits 3 (4 ^ E))) =
      D.test (D.dfa.eval (Nat.digits 3 (4 ^ E))) := by
  rw [normalizeUnit_eval]
  have hm : (4 : ℕ) ^ E % 3 = 1 := by simp [Nat.pow_mod]
  rw [if_pos hm]

lemma normalizeUnit_card (σ : Type*) [Fintype σ] :
    Fintype.card (Option (Option σ)) = Fintype.card σ + 2 := by
  simp only [Fintype.card_option]

#print axioms normalizeUnit_eval
#print axioms normalizeUnit_good
#print axioms normalizeUnit_backward
#print axioms normalizeUnit_power_seed
#print axioms normalizeUnit_card
end Erdos406BooleanRegister
