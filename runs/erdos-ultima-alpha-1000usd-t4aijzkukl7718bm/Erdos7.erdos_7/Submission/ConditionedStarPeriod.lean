import Submission.ConditionedStarMeasure

/-! Exact finite-period uniform measure for the conditioned star example. -/
namespace Erdos7ConditionedStarPeriod
open scoped BigOperators
open Erdos7ConditionedStarPolynomial Erdos7ConditionedStarArithmetic Erdos7ConditionedStarMeasure
set_option maxHeartbeats 2000000

def period (s : Finset Nat.Primes) : ℕ := 15 * ∏ p ∈ s, (p : ℕ)
lemma period_pos (s : Finset Nat.Primes) : 0 < period s := by
  unfold period
  exact Nat.mul_pos (by decide) (Finset.prod_pos (fun p _ => p.property.pos))
lemma three_dvd_period (s : Finset Nat.Primes) : 3 ∣ period s :=
  (by decide : 3 ∣ 15).trans (dvd_mul_right _ _)
lemma five_dvd_period (s : Finset Nat.Primes) : 5 ∣ period s :=
  (by decide : 5 ∣ 15).trans (dvd_mul_right _ _)
lemma prime_dvd_period (s : Finset Nat.Primes) (p : s) : (p.val : ℕ) ∣ period s :=
  (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) p.property).trans (dvd_mul_left _ _)

def project (s : Finset Nat.Primes) (x : Fin (period s)) : Full s :=
  (⟨x.val % 3, Nat.mod_lt _ (by decide)⟩, ⟨x.val % 5, Nat.mod_lt _ (by decide)⟩,
    fun p => ⟨x.val % (p.val : ℕ), Nat.mod_lt _ p.val.property.pos⟩)

lemma project_surjective (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    Function.Surjective (project s) := by
  intro y
  obtain ⟨x,h₃,h₅,hp⟩ := exists_coordinates s hs y.1.val y.2.1.val (coordinates y)
  refine ⟨⟨x % period s, Nat.mod_lt _ (period_pos s)⟩, ?_⟩
  apply Prod.ext
  · apply Fin.ext
    change (x % period s) % 3 = y.1.val
    rw [Nat.mod_mod_of_dvd _ (three_dvd_period s), h₃, Nat.mod_eq_of_lt y.1.isLt]
  · apply Prod.ext
    · apply Fin.ext
      change (x % period s) % 5 = y.2.1.val
      rw [Nat.mod_mod_of_dvd _ (five_dvd_period s), h₅, Nat.mod_eq_of_lt y.2.1.isLt]
    · funext p
      apply Fin.ext
      change (x % period s) % (p.val : ℕ) = (y.2.2 p).val
      rw [Nat.mod_mod_of_dvd _ (prime_dvd_period s p), hp p.val p.property,
        coordinates_eval, Nat.mod_eq_of_lt (y.2.2 p).isLt]

lemma full_card (s : Finset Nat.Primes) : Fintype.card (Full s) = period s := by
  simp only [Full, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
  rw [Finset.prod_coe_sort]
  unfold period
  ring

noncomputable def periodEquiv (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    Fin (period s) ≃ Full s :=
  Equiv.ofBijective (project s) ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨project_surjective s hs, by rw [Fintype.card_fin, full_card]⟩)

lemma project_hit (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (x : Fin (period s)) (i : Index s) :
    Nat.ModEq (modulus s i) x.val (residue s hs i) ↔ hit i (project s x) := by
  have h₃ : Nat.ModEq 3 x.val (project s x).1.val := (Nat.mod_mod _ _).symm
  have h₅ : Nat.ModEq 5 x.val (project s x).2.1.val := (Nat.mod_mod _ _).symm
  have hp : ∀ p ∈ s, Nat.ModEq (p : ℕ) x.val (coordinates (project s x) p) := by
    intro p hp
    rw [show coordinates (project s x) p = ((project s x).2.2 ⟨p,hp⟩).val from
      coordinates_eval (project s x) ⟨p,hp⟩]
    exact (Nat.mod_mod _ _).symm
  rw [membership_coordinates s hs x.val (project s x).1.val (project s x).2.1.val
    (coordinates (project s x)) h₃ h₅ hp i]
  exact (hit_coordinate hs i (project s x)).symm

def Avoided (s : Finset Nat.Primes) (x : Fin (period s)) : Prop :=
  ¬ Nat.ModEq 3 x.val 0 ∧ ¬ Nat.ModEq 5 x.val 0 ∧ ∀ p : s, ¬ Nat.ModEq (p.val : ℕ) x.val 0
instance (s : Finset Nat.Primes) (x : Fin (period s)) : Decidable (Avoided s x) := by
  unfold Avoided; infer_instance

lemma avoided_iff_allowed (s : Finset Nat.Primes) (x : Fin (period s)) :
    Avoided s x ↔ Allowed (project s x) := by
  simp [Avoided, Allowed, project, Nat.ModEq]

noncomputable def avoidedEquiv (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    {x : Fin (period s) // Avoided s x} ≃ {y : Full s // Allowed y} :=
  (periodEquiv s hs).subtypeEquiv (avoided_iff_allowed s)

lemma avoided_iff_all_prime_classes (s : Finset Nat.Primes)
    (hs : ∀ p ∈ s, 15 < (p : ℕ)) (x : Fin (period s)) :
    Avoided s x ↔ ∀ i : Index s, (modulus s i).Prime →
      ¬ Nat.ModEq (modulus s i) x.val (residue s hs i) := by
  rw [avoided_iff_allowed, allowed_iff_avoids_prime_moduli]
  simp_rw [project_hit s hs]

lemma avoided_nonempty (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    Nonempty {x : Fin (period s) // Avoided s x} := by
  obtain ⟨f⟩ := fibers_nonempty s
  exact ⟨(avoidedEquiv s hs).symm (allowedEquiv s (0,0,f))⟩

/-- Uniform probability in one integer period after deleting all pure classes. -/
noncomputable def arithmeticProbability (s : Finset Nat.Primes)
    (hs : ∀ p ∈ s, 15 < (p : ℕ)) (i : Index s) : ℝ :=
  ((Finset.univ.filter (fun x : {x : Fin (period s) // Avoided s x} =>
    Nat.ModEq (modulus s i) x.val.val (residue s hs i))).card : ℝ) /
      Fintype.card {x : Fin (period s) // Avoided s x}

lemma arithmeticProbability_eq (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (i : Index s) : arithmeticProbability s hs i = conditionalProbability i := by
  have hn : (Finset.univ.filter (fun x : {x : Fin (period s) // Avoided s x} =>
      Nat.ModEq (modulus s i) x.val.val (residue s hs i))).card =
      (Finset.univ.filter (fun y : {y : Full s // Allowed y} => hit i y.val)).card := by
    apply Finset.card_equiv (avoidedEquiv s hs)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact project_hit s hs x.val i
  unfold arithmeticProbability conditionalProbability
  rw [hn, Fintype.card_congr (avoidedEquiv s hs)]

lemma center_probability (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    arithmeticProbability s hs (starEmbedding s none) = 1/8 := by
  rw [arithmeticProbability_eq, Erdos7ConditionedStarMeasure.center_probability]

lemma leaf_probability (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) (p : s) :
    arithmeticProbability s hs (starEmbedding s (some p)) = 1/(8*((p.val : ℝ)-1)) := by
  rw [arithmeticProbability_eq, Erdos7ConditionedStarMeasure.leaf_probability]

lemma period_incompatibility_star (s : Finset Nat.Primes)
    (hs : ∀ p ∈ s, 15 < (p : ℕ)) (i j : Option s) :
    (¬ ∃ x : {x : Fin (period s) // Avoided s x},
      Nat.ModEq (modulus s (starEmbedding s i)) x.val.val (residue s hs (starEmbedding s i)) ∧
      Nat.ModEq (modulus s (starEmbedding s j)) x.val.val (residue s hs (starEmbedding s j))) ↔
      (i=none ∧ j≠none) ∨ (j=none ∧ i≠none) := by
  have he : (∃ x : {x : Fin (period s) // Avoided s x},
      Nat.ModEq (modulus s (starEmbedding s i)) x.val.val (residue s hs (starEmbedding s i)) ∧
      Nat.ModEq (modulus s (starEmbedding s j)) x.val.val (residue s hs (starEmbedding s j))) ↔
      ∃ y : {y : Full s // Allowed y}, hit (starEmbedding s i) y.val ∧ hit (starEmbedding s j) y.val := by
    simp_rw [project_hit s hs]
    constructor
    · rintro ⟨x,hx⟩; exact ⟨avoidedEquiv s hs x,hx⟩
    · rintro ⟨y,hy⟩
      obtain ⟨x,rfl⟩ := (avoidedEquiv s hs).surjective y
      exact ⟨x,hy⟩
  rw [he]
  exact conditioned_incompatibility_star s i j

/-- The negative polynomial uses the exact arithmetic conditional probabilities,
not raw reciprocal moduli or an independently chosen probability vector. -/
theorem exists_negative_arithmetic_polynomial :
    ∃ s : Finset Nat.Primes, ∃ hs : ∀ p ∈ s, 15 < (p : ℕ),
      Function.Injective (modulus s) ∧
      (∀ i, Odd (modulus s i) ∧ 1 < modulus s i) ∧
      (∀ i, ∃ x : ℤ, ∀ j, (modulus s j : ℤ) ∣ x-(residue s hs j : ℤ) ↔ i=j) ∧
      (∀ i d, 1 < d → d ∣ modulus s i → ∃ j, modulus s j=d) ∧
      (∃ z : ℤ, ∀ i, ¬ (modulus s i : ℤ) ∣ z-(residue s hs i : ℤ)) ∧
      (∑ t ∈ (Finset.univ : Finset s).powerset,
        ∏ p ∈ t, -(arithmeticProbability s hs (starEmbedding s (some p)))) -
          arithmeticProbability s hs (starEmbedding s none) < 0 := by
  obtain ⟨s,hs,hi,ho,hp,hd,hn,hpoly⟩ := exists_conditioned_barrier
  refine ⟨s,hs,hi,ho,hp,hd,hn,?_⟩
  simpa only [arithmeticProbability_eq] using hpoly

#print axioms avoided_iff_all_prime_classes
#print axioms avoided_nonempty
#print axioms period_incompatibility_star
#print axioms exists_negative_arithmetic_polynomial
#print axioms periodEquiv
#print axioms avoidedEquiv
#print axioms arithmeticProbability_eq
#print axioms center_probability
#print axioms leaf_probability
end Erdos7ConditionedStarPeriod
