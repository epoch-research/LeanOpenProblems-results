import Submission.SumsetIncidence

/-!
A finite cardinality bound for codes that force coordinatewise unordered
pair matchings to agree globally. This is a limitation on that construction
criterion, not an upper bound for arbitrary Sidon subsets of squares.
-/
namespace Erdos773.MatchingCoherenceBound
open Finset SumsetIncidence
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Matching the two entries of a pair, without specifying their order. -/
def PairMatch {γ : Type*} (a b c d : γ) : Prop :=
  (a=c ∧ b=d) ∨ (a=d ∧ b=c)

/-- Unordered matchings in the two blocks must come from one global matching. -/
def Coherent (C : Finset (α × β)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
    PairMatch a.1 b.1 c.1 d.1 → PairMatch a.2 b.2 c.2 d.2 → PairMatch a b c d

omit [DecidableEq α] [DecidableEq β] in
lemma rectangle (C : Finset (α × β)) (hC : Coherent C)
    {x w : α} {y z : β} (hxy : (x,y) ∈ C) (hxz : (x,z) ∈ C)
    (hwy : (w,y) ∈ C) (hwz : (w,z) ∈ C) : x=w ∨ y=z := by
  have h := hC (x,y) hxy (w,z) hwz (x,z) hxz (w,y) hwy
    (Or.inl ⟨rfl,rfl⟩) (Or.inr ⟨rfl,rfl⟩)
  rcases h with h | h
  · exact Or.inr (congrArg Prod.snd h.1)
  · exact Or.inl (congrArg Prod.fst h.1)

lemma common_neighbors (C : Finset (α × β)) (hC : Coherent C)
    (X : Finset α) {y z : β} (hyz : y ≠ z) :
    (X.filter (fun x => (x,y) ∈ C ∧ (x,z) ∈ C)).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx w hw
  obtain ⟨_,hxy,hxz⟩ := mem_filter.mp hx
  obtain ⟨_,hwy,hwz⟩ := mem_filter.mp hw
  exact (rectangle C hC hxy hxz hwy hwz).resolve_right hyz

lemma card_eq_incidence (C : Finset (α × β)) :
    C.card = incidenceCount (C.image Prod.fst) (C.image Prod.snd)
      (fun x y => (x,y) ∈ C) := by
  classical
  have he : C = ((C.image Prod.fst) ×ˢ (C.image Prod.snd)).filter (fun p => p ∈ C) := by
    ext p
    simp only [mem_filter, mem_product]
    constructor
    · intro hp
      exact ⟨⟨mem_image.mpr ⟨p,hp,rfl⟩, mem_image.mpr ⟨p,hp,rfl⟩⟩,hp⟩
    · intro hp
      exact hp.2
  calc
    C.card = (((C.image Prod.fst) ×ˢ (C.image Prod.snd)).filter (fun p => p ∈ C)).card :=
      congrArg card he
    _ = _ := by simp only [incidenceCount, card_eq_sum_ones, sum_filter, sum_product]

/-- A coherence code has at most |Y| sqrt(|X|)+|X| words, where X and Y
are its actual block projections. -/
theorem projection_bound (C : Finset (α × β)) (hC : Coherent C) :
    (C.card : ℝ) ≤ (C.image Prod.snd).card * Real.sqrt (C.image Prod.fst).card +
      (C.image Prod.fst).card := by
  rw [card_eq_incidence C]
  simpa using incidence_le (C.image Prod.fst) (C.image Prod.snd)
    (fun x y => (x,y) ∈ C) 1 (by norm_num)
    (fun y hy z hz hyz => by exact_mod_cast common_neighbors C hC _ hyz)

/-- The same bound in terms of the available block alphabets. -/
theorem alphabet_bound [Fintype α] [Fintype β]
    (C : Finset (α × β)) (hC : Coherent C) :
    (C.card : ℝ) ≤ Fintype.card β * Real.sqrt (Fintype.card α) + Fintype.card α := by
  have hx : ((C.image Prod.fst).card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast card_le_univ (C.image Prod.fst)
  have hy : ((C.image Prod.snd).card : ℝ) ≤ Fintype.card β := by
    exact_mod_cast card_le_univ (C.image Prod.snd)
  exact (projection_bound C hC).trans (add_le_add
    (mul_le_mul hy (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) hx)

/-- In a balanced R-by-R box, the criterion has a three-quarters power ceiling.
The conclusion is an integer inequality and includes R=0. -/
theorem balanced_fourth_bound (R : ℕ) (C : Finset (Fin R × Fin R))
    (hC : Coherent C) : C.card^4 ≤ 16*(R^2)^3 := by
  by_cases hR : R=0
  · subst R
    have hc : C.card=0 := by have := card_le_univ C; simp at this; simp [this]
    simp [hc]
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hroot : 1 ≤ Real.sqrt (R : ℝ) := by simpa using Real.sqrt_le_sqrt hR1
  have hroot0 := Real.sqrt_nonneg (R : ℝ)
  have hroot2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) R)
  have hc := alphabet_bound C hC
  simp only [Fintype.card_fin] at hc
  have hmult : (R : ℝ) ≤ R*Real.sqrt R := by
    have := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg (α := ℝ) R)
    simpa using this
  have hbound : (C.card : ℝ) ≤ 2*R*Real.sqrt R := by linarith
  have hsq : (C.card : ℝ)^2 ≤ 4*(R : ℝ)^3 := by
    calc
      _ ≤ (2*(R : ℝ)*Real.sqrt R)^2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hbound 2
      _ = _ := by rw [mul_pow, hroot2]; ring
  have hfour : (C.card : ℝ)^4 ≤ 16*((R : ℝ)^2)^3 := by
    have hh := pow_le_pow_left₀ (sq_nonneg (C.card : ℝ)) hsq 2
    nlinarith only [hh]
  exact_mod_cast hfour

/-- Coordinatewise coherence for a code whose coordinates are split into two blocks. -/
def CoordinateCoherent {ι κ A : Type*} [DecidableEq ι] [DecidableEq κ]
    [Fintype ι] [Fintype κ] [DecidableEq A]
    (C : Finset ((ι → A) × (κ → A))) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
    (∀ i, PairMatch (a.1 i) (b.1 i) (c.1 i) (d.1 i)) →
    (∀ j, PairMatch (a.2 j) (b.2 j) (c.2 j) (d.2 j)) → PairMatch a b c d

lemma coordinate_implies_block {ι κ A : Type*} [DecidableEq ι] [DecidableEq κ]
    [Fintype ι] [Fintype κ] [DecidableEq A]
    (C : Finset ((ι → A) × (κ → A))) (hC : CoordinateCoherent C) : Coherent C := by
  intro a ha b hb c hc d hd hleft hright
  apply hC a ha b hb c hc d hd
  · intro i
    rcases hleft with h | h
    · exact Or.inl ⟨congrFun h.1 i, congrFun h.2 i⟩
    · exact Or.inr ⟨congrFun h.1 i, congrFun h.2 i⟩
  · intro j
    rcases hright with h | h
    · exact Or.inl ⟨congrFun h.1 j, congrFun h.2 j⟩
    · exact Or.inr ⟨congrFun h.1 j, congrFun h.2 j⟩

/-- A 2d-coordinate code over an m-letter alphabet, with global pair coherence. -/
theorem uniform_coordinate_bound (m d : ℕ)
    (C : Finset ((Fin d → Fin m) × (Fin d → Fin m))) (hC : CoordinateCoherent C) :
    (C.card : ℝ) ≤ (m^d : ℕ)*Real.sqrt (m^d : ℕ) + (m^d : ℕ) := by
  simpa using alphabet_bound C (coordinate_implies_block C hC)

#print axioms projection_bound
#print axioms alphabet_bound
#print axioms balanced_fourth_bound
#print axioms coordinate_implies_block
#print axioms uniform_coordinate_bound
end
end Erdos773.MatchingCoherenceBound
