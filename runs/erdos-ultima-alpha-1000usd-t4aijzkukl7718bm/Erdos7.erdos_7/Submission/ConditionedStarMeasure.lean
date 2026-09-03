import Submission.ConditionedStarArithmetic

/-!
Exact uniform-conditioning link for the arithmetic star limitation.
This family is not a cover and does not settle Erdős Problem 7.
-/
namespace Erdos7ConditionedStarMeasure
open scoped BigOperators
open Erdos7ConditionedStarPolynomial Erdos7ConditionedStarArithmetic
set_option maxHeartbeats 2000000

abbrev Full (s : Finset Nat.Primes) := Fin 3 × Fin 5 × ((p : s) → Fin (p.val : ℕ))

def Allowed {s : Finset Nat.Primes} (y : Full s) : Prop :=
  y.1.val ≠ 0 ∧ y.2.1.val ≠ 0 ∧ ∀ p, (y.2.2 p).val ≠ 0
instance {s : Finset Nat.Primes} (y : Full s) : Decidable (Allowed y) := by
  unfold Allowed; infer_instance

def allowedEquiv (s : Finset Nat.Primes) : Space s ≃ {y : Full s // Allowed y} where
  toFun x := ⟨(⟨x.1.val+1, by have := x.1.isLt; omega⟩,
      ⟨x.2.1.val+1, by have := x.2.1.isLt; omega⟩,
      fun p => ⟨(x.2.2 p).val+1, by have := (x.2.2 p).isLt; omega⟩),
    by dsimp [Allowed]; exact ⟨by omega, by omega, fun p => by omega⟩⟩
  invFun y := (⟨y.val.1.val-1, by have := y.val.1.isLt; have := y.property.1; omega⟩,
      ⟨y.val.2.1.val-1, by have := y.val.2.1.isLt; have := y.property.2.1; omega⟩,
      fun p => ⟨(y.val.2.2 p).val-1, by
        have := (y.val.2.2 p).isLt; have := y.property.2.2 p; omega⟩)
  left_inv x := by
    apply Prod.ext
    · apply Fin.ext; simp
    · apply Prod.ext
      · apply Fin.ext; simp
      · funext p; apply Fin.ext; simp
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; dsimp; have := y.property.1; omega
    · apply Prod.ext
      · apply Fin.ext; dsimp; have := y.property.2.1; omega
      · funext p; apply Fin.ext; dsimp; have := y.property.2.2 p; omega

def hit {s : Finset Nat.Primes} (i : Index s) (y : Full s) : Prop :=
  match i with
  | Sum.inl j => (![y.1.val=0, y.2.1.val=0,
      y.1.val=1 ∧ y.2.1.val=1] : Fin 3 → Prop) j
  | Sum.inr (j,p) => (![(y.2.2 p).val=0,
      y.1.val=1 ∧ (y.2.2 p).val=2,
      y.2.1.val=1 ∧ (y.2.2 p).val=3,
      y.1.val=2 ∧ y.2.1.val=2 ∧ (y.2.2 p).val=1] : Fin 4 → Prop) j

noncomputable instance {s : Finset Nat.Primes} (i : Index s) (y : Full s) :
    Decidable (hit i y) := Classical.propDecidable _

lemma allowed_iff_avoids_pure {s : Finset Nat.Primes} (y : Full s) :
    Allowed y ↔ ¬ hit (Sum.inl 0) y ∧ ¬ hit (Sum.inl 1) y ∧
      ∀ p : s, ¬ hit (Sum.inr (0,p)) y := Iff.rfl

lemma allowed_iff_avoids_prime_moduli {s : Finset Nat.Primes} (y : Full s) :
    Allowed y ↔ ∀ i : Index s, (modulus s i).Prime → ¬ hit i y := by
  rw [allowed_iff_avoids_pure]
  constructor
  · rintro ⟨h₃,h₅,hp⟩ i hi
    rcases (modulus_prime_iff s i).mp hi with rfl | rfl | ⟨p,rfl⟩
    · exact h₃
    · exact h₅
    · exact hp p
  · intro h
    exact ⟨h _ Nat.prime_three, h _ (by change Nat.Prime 5; decide), fun p => h _ (by simpa [modulus,baseDiv] using p.val.property)⟩

lemma modEq_iff_eq {n a b : ℕ} (ha : a<n) (hb : b<n) :
    Nat.ModEq n a b ↔ a=b := by rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

noncomputable def coordinates {s : Finset Nat.Primes} (y : Full s) : Nat.Primes → ℕ :=
  fun p => if h : p ∈ s then (y.2.2 ⟨p,h⟩).val else 0

lemma coordinates_eval {s : Finset Nat.Primes} (y : Full s) (p : s) :
    coordinates y p.val = (y.2.2 p).val := by simp [coordinates]

lemma hit_coordinate {s : Finset Nat.Primes} (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (i : Index s) (y : Full s) :
    hit i y ↔ coordinateHit s i y.1.val y.2.1.val (coordinates y) := by
  cases i with
  | inl j =>
      fin_cases j <;>
        simp [hit, coordinateHit, modEq_iff_eq y.1.isLt, modEq_iff_eq y.2.1.isLt]
  | inr jp =>
      rcases jp with ⟨j,p⟩
      have h0 : 0 < (p.val : ℕ) := p.val.property.pos
      have h1 : 1 < (p.val : ℕ) := p.val.property.one_lt
      have h2 : 2 < (p.val : ℕ) := by have := hs p.val p.property; omega
      have h3 : 3 < (p.val : ℕ) := by have := hs p.val p.property; omega
      fin_cases j <;>
        simp [hit, coordinateHit, coordinates_eval,
          modEq_iff_eq y.1.isLt, modEq_iff_eq y.2.1.isLt,
          modEq_iff_eq (y.2.2 p).isLt h0, modEq_iff_eq (y.2.2 p).isLt h1,
          modEq_iff_eq (y.2.2 p).isLt h2, modEq_iff_eq (y.2.2 p).isLt h3]

/-- Every full coordinate point is realized by one integer, for all classes at once. -/
lemma realization (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (y : Full s) : ∃ x : ℤ, ∀ i : Index s,
      (modulus s i : ℤ) ∣ x-(residue s hs i : ℤ) ↔ hit i y := by
  obtain ⟨x,h₃,h₅,hp⟩ := exists_coordinates s hs y.1.val y.2.1.val (coordinates y)
  refine ⟨(x : ℤ), ?_⟩
  intro i
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd,
    membership_coordinates s hs x y.1.val y.2.1.val (coordinates y) h₃ h₅ hp i]
  exact (hit_coordinate hs i y).symm

def starEmbedding (s : Finset Nat.Primes) : Option s → Index s
  | none => Sum.inl 2
  | some p => Sum.inr (3,p)

lemma star_injective (s : Finset Nat.Primes) : Function.Injective (starEmbedding s) := by
  intro i j h
  cases i <;> cases j <;> simp_all [starEmbedding]

lemma conditioned_center (s : Finset Nat.Primes) (x : Space s) :
    hit (starEmbedding s none) (allowedEquiv s x).val ↔ center x := by
  change (x.1.val+1=1 ∧ x.2.1.val+1=1) ↔ x.1=0 ∧ x.2.1=0
  simp only [Fin.ext_iff]
  norm_num only [Fin.val_zero]
  omega

lemma conditioned_leaf (s : Finset Nat.Primes) (p : s) (x : Space s) :
    hit (starEmbedding s (some p)) (allowedEquiv s x).val ↔ leaf p x := by
  change (x.1.val+1=2 ∧ x.2.1.val+1=2 ∧ (x.2.2 p).val+1=1) ↔
    x.1=1 ∧ x.2.1=1 ∧ (x.2.2 p).val=0
  simp only [Fin.ext_iff]
  norm_num only [Fin.val_one]
  omega

noncomputable def conditionalProbability {s : Finset Nat.Primes} (i : Index s) : ℝ :=
  ((Finset.univ.filter (fun y : {y : Full s // Allowed y} => hit i y.val)).card : ℝ) /
    Fintype.card {y : Full s // Allowed y}

lemma probability_transfer (s : Finset Nat.Primes) (i : Index s)
    (P : Space s → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ hit i (allowedEquiv s x).val) :
    probability P = conditionalProbability i := by
  have hn : (Finset.univ.filter P).card =
      (Finset.univ.filter (fun y : {y : Full s // Allowed y} => hit i y.val)).card := by
    apply Finset.card_equiv (allowedEquiv s)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hP x
  unfold probability conditionalProbability
  rw [hn, Fintype.card_congr (allowedEquiv s)]

lemma center_probability (s : Finset Nat.Primes) :
    conditionalProbability (starEmbedding s none) = 1/8 := by
  rw [← probability_transfer s (starEmbedding s none) (@center s)
    (fun x => (conditioned_center s x).symm)]
  exact Erdos7ConditionedStarPolynomial.center_probability s

lemma leaf_probability (s : Finset Nat.Primes) (p : s) :
    conditionalProbability (starEmbedding s (some p)) = 1/(8*((p.val : ℝ)-1)) := by
  rw [← probability_transfer s (starEmbedding s (some p)) (leaf p)
    (fun x => (conditioned_leaf s p x).symm)]
  exact Erdos7ConditionedStarPolynomial.leaf_probability s p

lemma conditioned_incompatibility_star (s : Finset Nat.Primes) (i j : Option s) :
    (¬ ∃ y : {y : Full s // Allowed y},
      hit (starEmbedding s i) y.val ∧ hit (starEmbedding s j) y.val) ↔
      (i=none ∧ j≠none) ∨ (j=none ∧ i≠none) := by
  have hh : (∃ y : {y : Full s // Allowed y},
      hit (starEmbedding s i) y.val ∧ hit (starEmbedding s j) y.val) ↔
      ∃ x : Space s, (match i with | none => center x | some p => leaf p x) ∧
        (match j with | none => center x | some p => leaf p x) := by
    have ht (x : Space s) :
        (hit (starEmbedding s i) (allowedEquiv s x).val ∧
          hit (starEmbedding s j) (allowedEquiv s x).val) ↔
          (match i with | none => center x | some p => leaf p x) ∧
          (match j with | none => center x | some p => leaf p x) := by
      cases i <;> cases j <;> simp only [conditioned_center, conditioned_leaf]
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨(allowedEquiv s).symm y, (ht _).mp ?_⟩
      simpa using hy
    · rintro ⟨x,hx⟩
      exact ⟨allowedEquiv s x, (ht x).mpr hx⟩
  rw [hh]
  exact Erdos7ConditionedStarPolynomial.incompatibility_star s i j

/-- The signed independent-subset sum of this actual conditioned star. -/
noncomputable def actualPolynomial (s : Finset Nat.Primes) : ℝ :=
  (∑ t ∈ (Finset.univ : Finset s).powerset,
    ∏ p ∈ t, -(conditionalProbability (starEmbedding s (some p)))) -
      conditionalProbability (starEmbedding s none)

lemma actualPolynomial_eq (s : Finset Nat.Primes) : actualPolynomial s = polynomial s := by
  unfold actualPolynomial
  simp_rw [leaf_probability, center_probability]
  rw [← Finset.prod_one_add, polynomial_eq]
  congr 1
  simp only [← sub_eq_add_neg]
  exact Finset.prod_attach s (fun p : Nat.Primes => (1-1/(8*((p : ℝ)-1))))

/-- Pure-prime conditioning does not make static star positivity universal,
even with distinct odd divisor-closed moduli and literal private integers. -/
theorem exists_conditioned_barrier :
    ∃ s : Finset Nat.Primes, ∃ hs : ∀ p ∈ s, 15 < (p : ℕ),
      Function.Injective (modulus s) ∧
      (∀ i, Odd (modulus s i) ∧ 1 < modulus s i) ∧
      (∀ i, ∃ x : ℤ, ∀ j, (modulus s j : ℤ) ∣ x-(residue s hs j : ℤ) ↔ i=j) ∧
      (∀ i d, 1 < d → d ∣ modulus s i → ∃ j, modulus s j=d) ∧
      (∃ z : ℤ, ∀ i, ¬ (modulus s i : ℤ) ∣ z-(residue s hs i : ℤ)) ∧
      actualPolynomial s < 0 := by
  obtain ⟨s,hs,hn⟩ := exists_negative
  refine ⟨s,hs,modulus_injective s hs,odd_nontrivial s hs,private_points s hs,
    divisor_closed s,exists_uncovered s hs,?_⟩
  rwa [actualPolynomial_eq]

#print axioms allowedEquiv
#print axioms realization
#print axioms center_probability
#print axioms leaf_probability
#print axioms conditioned_incompatibility_star
#print axioms exists_conditioned_barrier
end Erdos7ConditionedStarMeasure
