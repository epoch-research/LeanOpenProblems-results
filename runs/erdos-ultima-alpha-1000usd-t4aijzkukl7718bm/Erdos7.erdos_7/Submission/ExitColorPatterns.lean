import Submission.PrimePowerBoxRealization

/-! Distinct moduli for a finite exit-color lifting construction. -/
namespace Erdos7ExitColorPatterns
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 3000000

section
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Old (q : ℕ) := {e : I → Fin (q+1) // ∃ i, e i ≠ 0}
abbrev Index (q : ℕ) := Old (I := I) q ⊕ (I × Fin q)

def exponent (q : ℕ) : Index (I := I) q → Option I → ℕ
  | .inl e, none => 0
  | .inl e, some i => (e.val i).val
  | .inr (i,t), none => 1
  | .inr (i,t), some k => if k=i then t.val+1 else 0

def base (p : I → ℕ) (q : ℕ) : Option I → ℕ
  | none => q
  | some i => p i

lemma exponent_injective (q : ℕ) : Function.Injective (exponent (I := I) q) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrFun he (some i)
    | inr b =>
      have h := congrFun he none
      simp [exponent] at h
  | inr a =>
    cases b with
    | inl b =>
      have h := congrFun he none
      simp [exponent] at h
    | inr b =>
      rcases a with ⟨i,t⟩
      rcases b with ⟨k,u⟩
      have hi := congrFun he (some i)
      simp only [exponent, ite_true] at hi
      have hik : i=k := by by_contra h; simp [h] at hi
      subst k
      simp only [ite_true, Nat.add_right_cancel_iff] at hi
      have htu : t=u := Fin.ext hi
      subst u
      rfl

lemma exponent_nonzero (q : ℕ) (j : Index (I := I) q) : ∃ i, exponent q j i ≠ 0 := by
  cases j with
  | inl e =>
    obtain ⟨i,hi⟩ := e.property
    exact ⟨some i, fun h => hi (Fin.ext h)⟩
  | inr j => exact ⟨none, by simp [exponent]⟩

lemma base_injective (p : I → ℕ) (q : ℕ) (hpi : Function.Injective p)
    (hq : ∀ i, p i ≠ q) : Function.Injective (base p q) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i => exact (hq i h.symm).elim
  | some i =>
    cases b with
    | none => exact (hq i h).elim
    | some j => exact congrArg some (hpi h)

lemma base_prime (p : I → ℕ) (q : ℕ) (hp : ∀ i, (p i).Prime) (hq : q.Prime) :
    ∀ i, (base p q i).Prime := by intro i; cases i <;> simp_all [base]

noncomputable def m (p : I → ℕ) (q : ℕ) (j : Index (I := I) q) : ℕ :=
  Erdos7PrimePowerBoxRealization.modulus (base p q) (exponent q j)

lemma m_injective (p : I → ℕ) (q : ℕ) (hp : ∀ i, (p i).Prime)
    (hpi : Function.Injective p) (hq : q.Prime) (hqp : ∀ i, p i ≠ q) :
    Function.Injective (m p q) := by
  intro a b h
  apply exponent_injective q
  exact Erdos7PrimePowerBoxRealization.modulus_injective (base p q)
    (base_prime p q hp hq) (base_injective p q hpi hqp) h

lemma m_gt_one (p : I → ℕ) (q : ℕ) (hp : ∀ i, (p i).Prime)
    (hpi : Function.Injective p) (hq : q.Prime) (hqp : ∀ i, p i ≠ q)
    (j : Index (I := I) q) : 1 < m p q j := by
  have hpos := Erdos7PrimePowerBoxRealization.modulus_pos (base p q) (base_prime p q hp hq)
    (exponent q j)
  change 0 < m p q j at hpos
  have hn : m p q j ≠ 1 := by
    intro he
    obtain ⟨i,hi⟩ := exponent_nonzero q j
    have hf := Erdos7PrimePowerBoxRealization.factorization_at (base p q)
      (base_prime p q hp hq) (base_injective p q hpi hqp) (exponent q j) i
    change (m p q j).factorization (base p q i) = exponent q j i at hf
    rw [he] at hf
    apply hi
    simpa using hf.symm
  omega

lemma m_odd (p : I → ℕ) (q : ℕ) (hp : ∀ i, Odd (p i)) (hq : Odd q)
    (j : Index (I := I) q) : Odd (m p q j) := by
  have hb : ∀ i, Odd (base p q i) := by intro i; cases i <;> simp_all [base]
  have hall (s : Finset (Option I)) : Odd (∏ i ∈ s, (base p q i) ^ exponent q j i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [prod_insert ha]
      exact (hb a).pow.mul ih
  exact hall univ

def cap (q : ℕ) : Option I → ℕ | none => 1 | some _ => q

lemma exponent_le_cap (q : ℕ) (j : Index (I := I) q) : exponent q j ≤ cap q := by
  intro i
  cases j with
  | inl e =>
    cases i with
    | none => simp [exponent,cap]
    | some i => have := (e.val i).isLt; simp [exponent,cap]; omega
  | inr j =>
    rcases j with ⟨k,t⟩
    cases i with
    | none => simp [exponent,cap]
    | some i => have := t.isLt; simp [exponent,cap]; split_ifs <;> omega

noncomputable def support (q : ℕ) (e : Old (I := I) q) : Finset I :=
  Erdos7PrimePowerCombFamily.support (fun i => (e.val i).val)

lemma mem_support (q : ℕ) (e : Old (I := I) q) (i : I) :
    i ∈ support q e ↔ (e.val i).val ≠ 0 := Erdos7PrimePowerCombFamily.mem_support _ _

end
#print axioms m_injective
#print axioms m_gt_one
#print axioms m_odd
end Erdos7ExitColorPatterns
