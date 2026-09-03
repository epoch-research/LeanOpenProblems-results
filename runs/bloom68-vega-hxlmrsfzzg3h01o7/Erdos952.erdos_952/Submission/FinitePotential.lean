import FormalConjecturesUtil

/-!
# Finite-potential obstructions to bounded-step Gaussian-prime sequences

A finite-potential certificate makes `x n - f (r (x n))` constant after an
injective sequence leaves a finite exceptional set. A finite residue type then
forces a repeated value, contradicting injectivity.

The main Gaussian-integer theorem is conditional on such a certificate. This
file does not construct a certificate or settle the Gaussian moat problem, and
does not import `Submission.Spec`.
-/

namespace Erdos952
namespace FinitePotential

/-- An injective sequence eventually avoids any given finite exceptional set. -/
theorem exists_tail_avoiding {G : Type*} {x : ℕ → G}
    (hx : Function.Injective x) {E : Set G} (hE : E.Finite) :
    ∃ N : ℕ, ∀ n : ℕ, x (N + n) ∉ E := by
  obtain ⟨M, hM⟩ := (hE.preimage hx.injOn).bddAbove
  refine ⟨M + 1, ?_⟩
  intro n hn
  have hle : M + 1 + n ≤ M := hM hn
  omega

/-- When each step equals the corresponding potential difference, subtracting
that potential gives a constant sequence. No finiteness assumption is needed. -/
theorem sub_potential_constant {G α : Type*} [AddCommGroup G]
    (r : G → α) (f : α → G) (x : ℕ → G)
    (hstep : ∀ n, x (n + 1) - x n = f (r (x (n + 1))) - f (r (x n))) :
    ∀ n, x n - f (r (x n)) = x 0 - f (r (x 0)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (sub_eq_sub_iff_sub_eq_sub.mp (hstep n)).trans ih

/-- A sequence whose steps are differences of a potential on a finite residue
type cannot be injective. -/
theorem not_injective_of_step_eq {G α : Type*} [AddCommGroup G] [Finite α]
    (r : G → α) (f : α → G) (x : ℕ → G)
    (hstep : ∀ n, x (n + 1) - x n = f (r (x (n + 1))) - f (r (x n))) :
    ¬ Function.Injective x := by
  intro hx
  have hconstant := sub_potential_constant r f x hstep
  apply not_injective_infinite_finite (fun n : ℕ => r (x n))
  intro m n hmn
  change r (x m) = r (x n) at hmn
  have heq := (hconstant m).trans (hconstant n).symm
  rw [hmn] at heq
  exact hx (sub_left_inj.mp heq)

/-- General finite-potential obstruction in an additive commutative group.
The certificate need only hold for admissible steps between points satisfying
`P` outside a finite exceptional set. -/
theorem not_exists_injective_sequence {G α : Type*} [AddCommGroup G] [Finite α]
    (P : G → Prop) (R : G → G → Prop) (r : G → α) (f : α → G)
    (E : Set G) (hE : E.Finite)
    (hcert : ∀ p q, P p → P q → p ∉ E → q ∉ E → R p q →
      q - p = f (r q) - f (r p)) :
    ¬ ∃ x : ℕ → G, Function.Injective x ∧ ∀ n, P (x n) ∧ R (x n) (x (n + 1)) := by
  rintro ⟨x, hx, hstep⟩
  obtain ⟨N, hN⟩ := exists_tail_avoiding hx hE
  have htail : ∀ n, x (N + (n + 1)) - x (N + n) =
      f (r (x (N + (n + 1)))) - f (r (x (N + n))) := by
    intro n
    apply hcert (x (N + n)) (x (N + (n + 1)))
    · exact (hstep (N + n)).1
    · exact (hstep (N + (n + 1))).1
    · exact hN n
    · exact hN (n + 1)
    · simpa only [Nat.add_assoc] using (hstep (N + n)).2
  exact not_injective_of_step_eq r f (fun n => x (N + n)) htail
    (fun _ _ h => Nat.add_left_cancel (hx h))

end FinitePotential

/-- A finite-potential certificate outside a finite exceptional set excludes
an injective Gaussian-prime sequence all of whose squared step norms are `< C`. -/
theorem no_bounded_step_sequence_of_finite_potential {α : Type*} [Finite α]
    (r : GaussianInt → α) (f : α → GaussianInt)
    (E : Set GaussianInt) (hE : E.Finite) (C : ℤ)
    (hcert : ∀ p q : GaussianInt, Prime p → Prime q → p ∉ E → q ∉ E →
      (q - p).norm < C → q - p = f (r q) - f (r p)) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  exact FinitePotential.not_exists_injective_sequence
    (G := GaussianInt) Prime (fun p q => (q - p).norm < C) r f E hE hcert

/-- The finite-potential obstruction with the exceptional set supplied as a
`Finset`, so that its finiteness need not be passed separately. -/
theorem no_bounded_step_sequence_of_finset_potential {α : Type*} [Finite α]
    (r : GaussianInt → α) (f : α → GaussianInt) (E : Finset GaussianInt) (C : ℤ)
    (hcert : ∀ p q : GaussianInt, Prime p → Prime q → p ∉ E → q ∉ E →
      (q - p).norm < C → q - p = f (r q) - f (r p)) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  exact no_bounded_step_sequence_of_finite_potential r f
    (E : Set GaussianInt) E.finite_toSet C hcert

/-- Distinct consecutive Gaussian integers have positive integral squared norm,
so a strict integral upper bound on all step norms is at least `2`.
Primality is not needed for this necessary condition. -/
theorem two_le_bound_of_injective_steps {x : ℕ → GaussianInt} {C : ℤ}
    (hx : Function.Injective x) (hstep : ∀ n, (x (n + 1) - x n).norm < C) :
    2 ≤ C := by
  have hne : x 1 ≠ x 0 := fun h => Nat.one_ne_zero (hx h)
  have hpos := GaussianInt.norm_pos.mpr (sub_ne_zero.mpr hne)
  have hlt : (x 1 - x 0).norm < C := hstep 0
  omega

/-- Any witness to an injective bounded-step Gaussian-prime sequence has
integral squared-norm bound at least `2`. -/
theorem two_le_bound_of_witness {C : ℤ}
    (h : ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    2 ≤ C := by
  rcases h with ⟨x, hx, hstep⟩
  exact two_le_bound_of_injective_steps hx (fun n => (hstep n).2)

end Erdos952
