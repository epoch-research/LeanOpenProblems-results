import FormalConjecturesUtil

/-! Exact rectangular Hall obstructions for divisor reassignment. These are
conditional finite matching facts, not covering-system nonexistence claims. -/
namespace Erdos7JointDivisorCapacity
set_option autoImplicit false

lemma divisor_rectangle {p q a b d : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hd : d ∣ p^a*q^b) :
    ∃ u ≤ a, ∃ v ≤ b, d=p^u*q^v := by
  obtain ⟨d₁,d₂,h₁,h₂,he⟩ := Nat.dvd_mul.mp hd
  obtain ⟨u,hu,rfl⟩ := (Nat.dvd_prime_pow hp).mp h₁
  obtain ⟨v,hv,rfl⟩ := (Nat.dvd_prime_pow hq).mp h₂
  exact ⟨u,hu,v,hv,he.symm⟩

lemma card_divisors_rectangle {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p.Coprime q) (a b : ℕ) :
    (p^a*q^b).divisors.card = (a+1)*(b+1) := by
  rw [(hpq.pow a b).card_divisors_mul]
  simp only [Nat.divisors_prime_pow hp,Nat.divisors_prime_pow hq,
    Finset.card_map,Finset.card_range]

/-- An injective assignment to nontrivial divisors has strictly fewer sources
than the full divisor-rectangle cardinality, because the unit is unavailable. -/
theorem assignment_card_lt {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p.Coprime q) (a b : ℕ)
    (hf : ∀ i ∈ S, 1 < f i ∧ f i ∣ p^a*q^b)
    (hi : Set.InjOn f S) :
    S.card < (a+1)*(b+1) := by
  let R := (p^a*q^b).divisors.erase 1
  have hn : p^a*q^b ≠ 0 := mul_ne_zero (pow_ne_zero a hp.ne_zero)
    (pow_ne_zero b hq.ne_zero)
  have hcard : S.card ≤ R.card := Finset.card_le_card_of_injOn f (by
    intro i his
    exact Finset.mem_erase.mpr ⟨by have := (hf i his).1; omega,
      Nat.mem_divisors.mpr ⟨(hf i his).2,hn⟩⟩) hi
  have hr : R.card = (a+1)*(b+1)-1 := by
    rw [Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr hn),
      card_divisors_rectangle hp hq hpq]
  rw [hr] at hcard
  have hpos : 0 < (a+1)*(b+1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- A rectangular Hall deficit rules out every injective divisor assignment,
not merely an assignment keeping each source's original modulus. -/
theorem no_assignment {I : Type*} [DecidableEq I]
    (S : Finset I) (P : I → Prop) (n : I → ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p.Coprime q) (a b : ℕ)
    (hS : ∀ i ∈ S, P i ∧ n i ∣ p^a*q^b)
    (hlarge : (a+1)*(b+1) ≤ S.card) :
    ¬ ∃ f : I → ℕ,
      (∀ i, P i → 1 < f i ∧ f i ∣ n i) ∧
      (∀ i j, P i → P j → f i=f j → i=j) := by
  rintro ⟨f,hf,hi⟩
  have hlt := assignment_card_lt S f hp hq hpq a b (by
    intro i his
    exact ⟨(hf i (hS i his).1).1,((hf i (hS i his).1).2).trans (hS i his).2⟩)
    (by intro i his j hjs hij; exact hi i j (hS i his).1 (hS j hjs).1 hij)
  omega

#print axioms divisor_rectangle
#print axioms card_divisors_rectangle
#print axioms assignment_card_lt
#print axioms no_assignment
end Erdos7JointDivisorCapacity
