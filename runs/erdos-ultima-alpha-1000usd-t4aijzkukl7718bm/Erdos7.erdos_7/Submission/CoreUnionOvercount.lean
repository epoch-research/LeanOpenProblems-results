import Submission.ManyBooleanCores

/-! An exact obstruction to summing probabilities over all minimal covering
cores under uniform independent nonzero-branch-pair selection. This is NOT a
covering system of integers and is NOT a disproof of Erdos7. -/
namespace Erdos7CoreUnionOvercount
open scoped BigOperators
open Erdos7ManyBooleanCores
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000

abbrev Clause := Erdos7ManyBooleanCores.Class
attribute [local irreducible] allCores

def prime (i : Coord) : ℕ := match i with
  | .inl (b,c) => (![![11,13,17,19], ![23,29,31,37], ![41,43,47,53]] : Fin 3 → Fin 4 → ℕ) b c
  | .inr (b,c) => (![![59,61,67,71], ![73,79,83,89]] : Fin 2 → Fin 4 → ℕ) b c

lemma prime_properties : Function.Injective prime ∧ ∀ i, (prime i).Prime ∧ 11 ≤ prime i := by
  decide +kernel

/-- Tags zero through p-2 represent the p-1 nonzero first-digit branches. -/
abbrev Branch (i : Coord) := Fin (prime i-1)
abbrev PairChoice (i : Coord) := ↥((Finset.univ : Finset (Branch i)).powersetCard 2)
abbrev Sample := (i : Coord) → PairChoice i

def encode (i : Coord) (b : Fin 2) : Branch i :=
  ⟨prime i-3+b.val, by have := (prime_properties.2 i).2; have := b.isLt; omega⟩

lemma encode_injective (i : Coord) : Function.Injective (encode i) := by
  intro b c h
  have hh := congrArg Fin.val h
  exact Fin.ext (by simpa only [encode, Nat.add_right_inj] using hh)

noncomputable def special (i : Coord) : PairChoice i :=
  ⟨{encode i 0, encode i 1}, by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    have hn : encode i 0 ≠ encode i 1 := fun h => by
      have hh := encode_injective i h
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    simp [hn]⟩

lemma special_lifts (i : Coord) (x : Branch i) (hx : x ∈ (special i).val) :
    ∃ b : Fin 2, x = encode i b := by
  have hx' : x = encode i 0 ∨ x = encode i 1 := by simpa [special] using hx
  rcases hx' with h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩

/-- This is coverage of the ENTIRE selected product, not just the activity of
one clause or a pair of conflicting clauses. -/
def CoreEvent (s : Finset Clause) (z : Sample) : Prop :=
  ∀ x : (i : Coord) → Branch i, (∀ i, x i ∈ (z i).val) →
    ∃ k ∈ s, ∀ i ∈ support k, x i = encode i (bit k i)

lemma core_event_special (s : Finset Clause) (hs : s ∈ allCores) : CoreEvent s special := by
  intro x hx
  choose b hb using fun i => special_lifts i (x i) (hx i)
  have hc := many_minimal_cores.2.2.2 s hs
  obtain ⟨k,hk,hmatch⟩ := hc.1 b
  refine ⟨k,hk,fun i hi => ?_⟩
  rw [hb i, hmatch i hi]

/-- The event also records minimality on the selected product: every class
has its own private point within that product. -/
def MinimalCoreEvent (s : Finset Clause) (z : Sample) : Prop :=
  CoreEvent s z ∧ ∀ k ∈ s, ∃ x : (i : Coord) → Branch i,
    (∀ i, x i ∈ (z i).val) ∧ ∀ l ∈ s,
      (∀ i ∈ support l, x i = encode i (bit l i)) ↔ l=k

lemma encode_mem_special (i : Coord) (v : Fin 2) : encode i v ∈ (special i).val := by
  fin_cases v <;> simp [special]

lemma minimal_core_event_special (s : Finset Clause) (hs : s ∈ allCores) :
    MinimalCoreEvent s special := by
  refine ⟨core_event_special s hs, ?_⟩
  intro k hk
  obtain ⟨x,hx⟩ := (many_minimal_cores.2.2.2 s hs).2 k hk
  refine ⟨fun i => encode i (x i), fun i => encode_mem_special i (x i), ?_⟩
  intro l hl
  have he : (∀ i ∈ support l, encode i (x i) = encode i (bit l i)) ↔ Matches l x := by
    constructor
    · exact fun h i hi => encode_injective i (h i hi)
    · exact fun h i hi => congrArg (encode i) (h i hi)
  exact he.trans (hx l hl)

lemma sample_card : Fintype.card Sample = ∏ i : Coord, (prime i-1).choose 2 := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Only a twenty-term integer product is evaluated; the enormous sample
space itself is never enumerated. -/
lemma sample_card_lt : Fintype.card Sample < 2^216 := by
  rw [sample_card]
  decide +kernel

noncomputable def coreProbability (s : Finset Clause) : ℚ := by
  classical
  exact ((Finset.univ.filter (MinimalCoreEvent s)).card : ℚ)/Fintype.card Sample

lemma card_filter_one_le {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P]
    (x : X) (hx : P x) : 1 ≤ (Finset.univ.filter P).card := by
  exact Finset.one_le_card.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩

lemma coreProbability_lower (s : Finset Clause) (hs : s ∈ allCores) :
    1/(Fintype.card Sample : ℚ) ≤ coreProbability s := by
  classical
  have hcard := card_filter_one_le (X := Sample) (MinimalCoreEvent s) special (minimal_core_event_special s hs)
  unfold coreProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

/-- Summing the probabilities of these DISTINCT MINIMAL cores exceeds one.
They all occur together on one small event, so their overlap cannot be ignored.
This rules out a universal raw-core union bound for this sampling law. -/
theorem sum_core_probabilities_gt_one :
    1 < ∑ s ∈ allCores, coreProbability s := by
  classical
  letI : Nonempty Sample := ⟨special⟩
  have hN : (0 : ℚ) < Fintype.card Sample := by exact_mod_cast Fintype.card_pos
  have hlt : (Fintype.card Sample : ℚ) < allCores.card := by
    rw [allCores_card]
    exact_mod_cast sample_card_lt
  have hsum : (∑ s ∈ allCores, 1/(Fintype.card Sample : ℚ)) ≤
      ∑ s ∈ allCores, coreProbability s := by
    apply Finset.sum_le_sum (s := allCores) (f := fun _ => 1/(Fintype.card Sample : ℚ)) (g := coreProbability)
    intro s hs
    exact coreProbability_lower s hs
  have he : (∑ _s ∈ allCores, 1/(Fintype.card Sample : ℚ)) =
      (allCores.card : ℚ)/Fintype.card Sample := by
    rw [Finset.sum_const (s := allCores), nsmul_eq_mul, mul_one_div]
  rw [he] at hsum
  exact (one_lt_div hN).mpr hlt |>.trans_le hsum

#print axioms sample_card_lt
#print axioms minimal_core_event_special
#print axioms sum_core_probabilities_gt_one
end Erdos7CoreUnionOvercount
