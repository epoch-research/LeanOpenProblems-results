import FormalConjectures.Util.ProblemImports
open Nat
open Classical

-- let's copy the definition of a
def a (n : ℕ) : ℕ :=
  (Nat.factorization n).support.sum fun p =>
    2 ^ (Nat.primeCounting p - 1)

def T (x : ℕ) : Prop := ∃ k, (a^[k]) x = 0

-- We can define steps x as the minimum k such that (a^[k]) x = 0, using Classical.choose if T x holds.
noncomputable def steps (x : ℕ) : ℕ :=
  if h : T x then
    Nat.find h
  else
    0

noncomputable def R (x y : ℕ) : Prop :=
  (T x ∧ ¬ T y) ∨ (T x ∧ T y ∧ steps x < steps y) ∨ (¬ T x ∧ ¬ T y ∧ x < y)

open PSum

def S : PSum ℕ ℕ → PSum ℕ ℕ → Prop
  | inl a, inl b => a < b
  | inl _, inr _ => True
  | inr _, inl _ => False
  | inr a, inr b => a < b

theorem S_wf : WellFounded S := by
  constructor
  intro x
  rcases x with a | b
  · -- Case inl a
    induction' a using Nat.strong_induction_on with a ih
    constructor
    intro y hy
    rcases y with c | d
    · exact ih c hy
    · contradiction
  · -- Case inr b
    induction' b using Nat.strong_induction_on with b ih
    constructor
    intro y hy
    rcases y with c | d
    · -- y is inl c, which is always accessible because inl is well-founded
      have h_inl_acc : ∀ w, Acc S (inl w) := by
        intro w
        induction' w using Nat.strong_induction_on with w ih_inl
        constructor
        intro z hz
        rcases z with zc | zd
        · exact ih_inl zc hz
        · contradiction
      exact h_inl_acc c
    · -- y is inr d
      exact ih d hy

noncomputable def f (x : ℕ) : PSum ℕ ℕ :=
  if T x then
    inl (steps x)
  else
    inr x

theorem R_impl_S (x y : ℕ) (h : R x y) : S (f x) (f y) := by
  unfold R at h
  unfold f
  by_cases hx : T x <;> by_cases hy : T y
  · -- T x, T y
    simp [hx, hy]
    unfold S
    rcases h with (h1 | h2 | h3)
    · exact False.elim (h1.2 hy)
    · exact h2.2.2
    · exact False.elim (h3.2.1 hy)
  · -- T x, ¬ T y
    simp [hx, hy]
    unfold S
    trivial
  · -- ¬ T x, T y
    simp [hx, hy]
    rcases h with (h1 | h2 | h3)
    · exact False.elim (hx h1.1)
    · exact False.elim (hx h2.1)
    · exact False.elim (h3.2.1 hy)
  · -- ¬ T x, ¬ T y
    simp [hx, hy]
    unfold S
    rcases h with (h1 | h2 | h3)
    · exact False.elim (hx h1.1)
    · exact False.elim (hx h2.1)
    · exact h3.2.2


theorem R_wf : WellFounded R := by
  constructor
  intro x
  have h_acc : ∀ (s : PSum ℕ ℕ), ∀ (x : ℕ), f x = s → Acc R x := by
    intro s
    induction' s using S_wf.induction with s ih
    intro x hx
    constructor
    intro y hy
    have hs := R_impl_S y x hy
    rw [hx] at hs
    exact ih (f y) hs y rfl
  exact h_acc (f x) x rfl

theorem T_zero : T 0 := by
  use 0
  rfl

theorem T_one : T 1 := by
  use 1
  -- we need to show a 1 = 0
  unfold a
  simp

theorem T_two : T 2 := by
  use 2
  have ha2 : a 2 = 1 := by
    unfold a
    have h2 : Nat.Prime 2 := Nat.prime_two
    rw [Nat.Prime.factorization h2]
    -- Finsupp.single 2 1 has support {2}
    have h_supp : (Finsupp.single 2 1).support = {2} := Finsupp.support_single_ne_zero 2 (by decide)
    rw [h_supp]
    -- now we sum over {2}
    simp
    -- Nat.primeCounting 2 = 1
    -- 2^(1-1) = 1
    -- In Mathlib, primeCounting is primeCounting. But wait, what is primeCounting 2?
    -- let's see if we can simplify it or let simp/decide do it
    rfl
  have ha1 : a 1 = 0 := by
    unfold a
    simp
  simp [ha2, ha1]

theorem T_pow_two (k : ℕ) : T (2 ^ k) := by
  by_cases hk : k = 0
  · rw [hk]
    simp
    exact T_one
  · use 2
    -- we want to show (a^[2]) (2 ^ k) = 0, which is a (a (2 ^ k)) = 0
    have ha2k : a (2 ^ k) = 1 := by
      unfold a
      have h2 : Nat.Prime 2 := Nat.prime_two
      rw [Nat.Prime.factorization_pow h2]
      have h_supp : (Finsupp.single 2 k).support = {2} := Finsupp.support_single_ne_zero 2 hk
      rw [h_supp]
      simp
      rfl
    have ha1 : a 1 = 0 := by
      unfold a
      simp
    simp [ha2k, ha1]

theorem T_prime (p : ℕ) (hp : p.Prime) : T p := by
  have hap : a p = 2 ^ (Nat.primeCounting p - 1) := by
    unfold a
    rw [Nat.Prime.factorization hp]
    have h_supp : (Finsupp.single p 1).support = {p} := Finsupp.support_single_ne_zero p (by decide)
    rw [h_supp]
    simp
  -- Now we want to show T p
  -- Since a p is a power of 2, and we have T_pow_two
  have h_ap_term : T (a p) := by
    rw [hap]
    exact T_pow_two _
  -- since T (a p) holds, let's show T p
  rcases h_ap_term with ⟨k, hk⟩
  use k + 1
  -- we want to show (a^[k+1]) p = 0
  -- which is (a^[k]) (a p) = 0
  have h_eq : (a^[k+1]) p = (a^[k]) (a p) := congr_fun (Function.iterate_succ a k) p
  rw [h_eq]
  exact hk










