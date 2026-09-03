import Submission.GreedyTwoDegreeEnergy
import Submission.BipartiteDegreeEnergy

/-!
Complete bipartite two-graphs occur as genuine residual graphs after legal
choices in linear four-uniform hypergraphs. Thus the centered-degree
signless-gap obstruction is not limited to unrelated symmetric matrices.
This file does not claim exact initial regularity or any square-specific
realization, and it is not a disproof of Erdős 773.
-/
namespace Erdos773.BipartiteGreedyResidual
open Finset GreedyHypergraphState
set_option maxHeartbeats 2000000
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev Vertex (α β : Type*) := (α ⊕ β) ⊕ ((α × β) × Bool)

abbrev left (a : α) : Vertex α β := .inl (.inl a)
abbrev right (b : β) : Vertex α β := .inl (.inr b)
abbrev label (p : α × β) (c : Bool) : Vertex α β := .inr (p,c)

def edge (p : α × β) : Finset (Vertex α β) :=
  {left p.1, right p.2, label p false, label p true}

def H (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (Finset (Vertex α β)) := univ.image edge

def I (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (Vertex α β) := univ.image Sum.inr

def cores (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (Vertex α β) := univ.image Sum.inl

omit [Fintype α] [Fintype β] in
@[simp] lemma left_mem_edge (a : α) (p : α × β) : left a ∈ edge p ↔ a = p.1 := by
  simp [edge]

omit [Fintype α] [Fintype β] in
@[simp] lemma right_mem_edge (b : β) (p : α × β) : right b ∈ edge p ↔ b = p.2 := by
  simp [edge]

omit [Fintype α] [Fintype β] in
@[simp] lemma label_mem_edge (p q : α × β) (c : Bool) : label p c ∈ edge q ↔ p = q := by
  cases c <;> simp [edge]

@[simp] lemma label_mem_I (p : α × β) (c : Bool) : label p c ∈ I α β := by
  simp [I]

@[simp] lemma core_notMem_I (u : α ⊕ β) : (Sum.inl u : Vertex α β) ∉ I α β := by
  simp [I]

omit [Fintype α] [Fintype β] in
lemma edge_injective : Function.Injective (edge (α := α) (β := β)) := by
  intro p q h
  have hl : p.1 = q.1 := left_mem_edge _ _ |>.mp (h ▸ (left_mem_edge p.1 p).mpr rfl)
  have hr : p.2 = q.2 := right_mem_edge _ _ |>.mp (h ▸ (right_mem_edge p.2 p).mpr rfl)
  exact Prod.ext hl hr

lemma edge_mem (p : α × β) : edge p ∈ H α β := mem_image.mpr ⟨p, mem_univ _, rfl⟩

omit [Fintype α] [Fintype β] in
@[simp] lemma edge_card (p : α × β) : (edge p).card = 4 := by
  simp [edge]

theorem four_uniform : ∀ e ∈ H α β, e.card = 4 := by
  intro e he
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  exact edge_card p

lemma edge_residual (p : α × β) : edge p \ I α β = {left p.1, right p.2} := by
  ext u
  rcases u with (a | b) | ⟨q,c⟩ <;> simp [mem_sdiff]

theorem independent : Independent (H α β) (I α β) := by
  intro e he hs
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  exact core_notMem_I _ (hs ((left_mem_edge p.1 p).mpr rfl))

/-- Every order of selecting the labels is legal. -/
theorem label_available {J : Finset (Vertex α β)} (hJ : J ⊆ I α β)
    {p : α × β} {c : Bool} (hnot : label p c ∉ J) :
    label p c ∈ available (H α β) J := by
  apply mem_available.mpr
  exact ⟨hnot, independent.mono (insert_subset (label_mem_I p c) hJ)⟩

theorem available_eq : available (H α β) (I α β) = cores α β := by
  ext u
  rcases u with (a | b) | ⟨p,c⟩
  · simp only [mem_available, core_notMem_I, not_false_eq_true, true_and]
    have hcore : (left a : Vertex α β) ∈ cores α β := by simp [cores]
    rw [iff_true_intro hcore, iff_true]
    intro e he hs
    obtain ⟨p, _, rfl⟩ := mem_image.mp he
    have hh := hs ((right_mem_edge p.2 p).mpr rfl)
    simp at hh
  · simp only [mem_available, core_notMem_I, not_false_eq_true, true_and]
    have hcore : (right b : Vertex α β) ∈ cores α β := by simp [cores]
    rw [iff_true_intro hcore, iff_true]
    intro e he hs
    obtain ⟨p, _, rfl⟩ := mem_image.mp he
    have hh := hs ((left_mem_edge p.1 p).mpr rfl)
    simp at hh
  · simp [mem_available, I, cores]

omit [Fintype α] [Fintype β] in
lemma edge_inter_card_le {p q : α × β} (hpq : p ≠ q) :
    (edge p ∩ edge q).card ≤ 1 := by
  by_cases hp : p.1 = q.1
  · have hq : p.2 ≠ q.2 := fun h => hpq (Prod.ext hp h)
    have hs : edge p ∩ edge q ⊆ {left p.1} := by
      intro u hu
      rcases u with (a | b) | ⟨r,c⟩
      · simpa using (left_mem_edge a p).mp (mem_inter.mp hu).1
      · have h₁ := (right_mem_edge b p).mp (mem_inter.mp hu).1
        have h₂ := (right_mem_edge b q).mp (mem_inter.mp hu).2
        exact (hq (h₁.symm.trans h₂)).elim
      · have h₁ := (label_mem_edge r p c).mp (mem_inter.mp hu).1
        have h₂ := (label_mem_edge r q c).mp (mem_inter.mp hu).2
        exact (hpq (h₁.symm.trans h₂)).elim
    simpa using card_le_card hs
  · have hs : edge p ∩ edge q ⊆ {right p.2} := by
      intro u hu
      rcases u with (a | b) | ⟨r,c⟩
      · have h₁ := (left_mem_edge a p).mp (mem_inter.mp hu).1
        have h₂ := (left_mem_edge a q).mp (mem_inter.mp hu).2
        exact (hp (h₁.symm.trans h₂)).elim
      · simpa using (right_mem_edge b p).mp (mem_inter.mp hu).1
      · have h₁ := (label_mem_edge r p c).mp (mem_inter.mp hu).1
        have h₂ := (label_mem_edge r q c).mp (mem_inter.mp hu).2
        exact (hpq (h₁.symm.trans h₂)).elim
    simpa using card_le_card hs

/-- Distinct original edges have at most one vertex in common. -/
theorem linear : ∀ e ∈ H α β, ∀ f ∈ H α β, e ≠ f → (e ∩ f).card ≤ 1 := by
  intro e he f hf hne
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  obtain ⟨q, _, rfl⟩ := mem_image.mp hf
  exact edge_inter_card_le (fun h => hne (congrArg edge h))

lemma active_two : active (H α β) (I α β) 2 = H α β := by
  apply filter_eq_self.mpr
  intro e he
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  rw [edge_residual, available_eq]
  simp [cores, insert_subset_iff, singleton_subset_iff]

lemma pairReps_left_right (a : α) (b : β) :
    pairReps (H α β) (I α β) (left a) (right b) = {edge (a,b)} := by
  ext e
  simp only [pairReps, mem_filter, mem_singleton]
  constructor
  · rintro ⟨he, hne, hr⟩
    obtain ⟨p, _, rfl⟩ := mem_image.mp he
    rw [edge_residual] at hr
    have ha : p.1 = a := by
      have hh : left p.1 ∈ ({left a, right b} : Finset (Vertex α β)) := hr ▸ (by simp)
      simpa using hh
    have hb : p.2 = b := by
      have hh : right p.2 ∈ ({left a, right b} : Finset (Vertex α β)) := hr ▸ (by simp)
      simpa using hh
    have hp : p = (a,b) := Prod.ext ha hb
    rw [hp]
  · rintro rfl
    exact ⟨edge_mem _, by simp, edge_residual _⟩

lemma pairReps_left_left (a a' : α) :
    pairReps (H α β) (I α β) (left a) (left a') = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, _, hr⟩ := mem_filter.mp he
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  rw [edge_residual] at hr
  have hh : right p.2 ∈ ({left a, left a'} : Finset (Vertex α β)) := hr ▸ (by simp)
  simp at hh

lemma pairReps_right_right (b b' : β) :
    pairReps (H α β) (I α β) (right b) (right b') = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, _, hr⟩ := mem_filter.mp he
  obtain ⟨p, _, rfl⟩ := mem_image.mp he
  rw [edge_residual] at hr
  have hh : left p.1 ∈ ({right b, right b'} : Finset (Vertex α β)) := hr ▸ (by simp)
  simp at hh

/-- Exact matching, with original-edge multiplicities retained. -/
theorem weight_eq {m n : ℕ} (u v : BipartiteDegreeEnergy.Vertex m n) :
    GreedyTwoDegreeEnergy.weight (H (Fin m) (Fin n)) (I (Fin m) (Fin n))
      (Sum.inl u) (Sum.inl v) = BipartiteDegreeEnergy.weight u v := by
  rcases u with a | b <;> rcases v with a' | b'
  · simp [GreedyTwoDegreeEnergy.weight, pairReps_left_left, BipartiteDegreeEnergy.weight]
  · simp [GreedyTwoDegreeEnergy.weight, pairReps_left_right, BipartiteDegreeEnergy.weight]
  · rw [GreedyTwoDegreeEnergy.weight_symm]
    simp [GreedyTwoDegreeEnergy.weight, pairReps_left_right, BipartiteDegreeEnergy.weight]
  · simp [GreedyTwoDegreeEnergy.weight, pairReps_right_right, BipartiteDegreeEnergy.weight]

theorem degree_eq {m n : ℕ} (u : BipartiteDegreeEnergy.Vertex m n) :
    ((incident (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) 2 (Sum.inl u)).card : ℝ) =
      BipartiteDegreeEnergy.degree u := by
  have hu : Sum.inl u ∈ available (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) := by
    rw [available_eq]
    simp [cores]
  rw [← GreedyTwoDegreeEnergy.weighted_degree hu, available_eq, cores,
    sum_image (fun _ _ _ _ h => Sum.inl.inj h)]
  simp only [weight_eq]
  rfl

theorem actual_mean (m n : ℕ) :
    (∑ u ∈ available (H (Fin m) (Fin n)) (I (Fin m) (Fin n)),
      ((incident (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) 2 u).card : ℝ))/
      (available (H (Fin m) (Fin n)) (I (Fin m) (Fin n))).card =
      BipartiteDegreeEnergy.mean m n := by
  simp only [available_eq, cores, sum_image (fun _ _ _ _ h => Sum.inl.inj h),
    card_image_of_injective _ Sum.inl_injective, card_univ, degree_eq]
  exact (BipartiteDegreeEnergy.mean_eq m n).symm

/-- The exact available-vertex degree variance of the legal residual state. -/
theorem energy_eq (m n : ℕ) :
    (∑ u ∈ available (H (Fin m) (Fin n)) (I (Fin m) (Fin n)),
      (((incident (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) 2 u).card : ℝ)-
        BipartiteDegreeEnergy.mean m n)^2) = BipartiteDegreeEnergy.energy m n := by
  rw [available_eq, cores, sum_image (fun _ _ _ _ h => Sum.inl.inj h)]
  simp only [degree_eq]
  rfl

/-- The signless energy from the actual greedy two-degree operator. -/
theorem dissipation_eq (m n : ℕ) :
    (1/2:ℝ)*(∑ u ∈ available (H (Fin m) (Fin n)) (I (Fin m) (Fin n)),
      ∑ v ∈ available (H (Fin m) (Fin n)) (I (Fin m) (Fin n)),
        GreedyTwoDegreeEnergy.weight (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) u v*
          ((((incident (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) 2 u).card : ℝ)-
            BipartiteDegreeEnergy.mean m n)+
           (((incident (H (Fin m) (Fin n)) (I (Fin m) (Fin n)) 2 v).card : ℝ)-
            BipartiteDegreeEnergy.mean m n))^2) = BipartiteDegreeEnergy.dissipation m n := by
  simp only [available_eq, cores, sum_image (fun _ _ _ _ h => Sum.inl.inj h),
    degree_eq, weight_eq]
  rfl

#print axioms four_uniform
#print axioms linear
#print axioms independent
#print axioms label_available
#print axioms available_eq
#print axioms weight_eq
#print axioms degree_eq
#print axioms actual_mean
#print axioms energy_eq
#print axioms dissipation_eq
end
end Erdos773.BipartiteGreedyResidual
