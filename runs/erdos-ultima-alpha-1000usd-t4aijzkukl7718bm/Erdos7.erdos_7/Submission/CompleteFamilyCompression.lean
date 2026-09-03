import Submission.CompleteFamilyModel

/-! Actual kernel compression for normalized complete exponent families. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7KernelFamilyCompression Erdos7CappedRetentionRows
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

lemma sum_filter_level_le {κ : Type*} (K : Finset κ) (e : κ → ℕ) (a : ℕ)
    (w : κ → ℝ) :
    (∑ k ∈ K.filter (fun k => e k ≤ a), w k) =
      (∑ k ∈ K.filter (fun k => e k=0), w k) +
      ∑ g ∈ Finset.range a, ∑ k ∈ K.filter (fun k => e k=g+1), w k := by
  classical
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have h1 : (K.filter (fun k => e k ≤ a+1)).filter (fun k => e k ≤ a) =
        K.filter (fun k => e k ≤ a) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk,h1⟩,h2⟩
        exact ⟨hk, by omega⟩
      · rintro ⟨hk,h⟩
        exact ⟨⟨hk, by omega⟩, by omega⟩
    have h2 : (K.filter (fun k => e k ≤ a+1)).filter (fun k => ¬ e k ≤ a) =
        K.filter (fun k => e k=a+1) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk,h1⟩,h2⟩
        exact ⟨hk, by omega⟩
      · rintro ⟨hk,h⟩
        exact ⟨⟨hk, by omega⟩, by omega⟩
    have hh := Finset.sum_filter_add_sum_filter_not (K.filter (fun k => e k ≤ a+1)) (fun k => e k ≤ a) w
    rw [h1,h2] at hh
    exact hh.symm

variable {n : ℕ} {κ : Type} [DecidableEq κ]
variable {E : Fin n → ℕ} {e : κ → Fin n → ℕ} {t : ℕ}

noncomputable def oldFamily (b : Family E e (t+1)) (ht : t < n) :
    Option (Fin (E ⟨t,ht⟩)) → Family E e t
  | none => b.truncate ht 0 (Nat.zero_le _)
  | some j => b.truncate ht (j.val+1) (by omega)

lemma oldFamily_scaled (A : Fin n → Type) [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (X : κ → ∀ i, Finset (A i)) (b : Family E e (t+1)) (ht : t < n)
    (d : Option (Fin (E ⟨t,ht⟩))) (x : ∀ i,A i) :
    multiplier d * count A X (oldFamily b ht d) x =
      (∑ k ∈ b.labels.filter (fun k => e k ⟨t,ht⟩ ≤
        (match d with | none => 0 | some j => j.val+1)),
        indicator A t (e k) (X k) x)/(b.multiplicity:ℝ) := by
  have hm : (b.multiplicity:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt b.positive
  cases d with
  | none => simp [oldFamily,multiplier,count,Family.truncate]
  | some j =>
    dsimp only [oldFamily,multiplier,count,Family.truncate]
    have hj : ((j.val:ℝ)+2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

section Compression
variable (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, DecidableEq (A i)]
variable (X : κ → ∀ i, Finset (A i))

/-- Geometric marginals may be substituted for r. No extremizer common to
the different projected families is postulated. -/
theorem complete_family_compression (he : ∀ k i, e k i ≤ E i)
    (b : Family E e (t+1)) (ht : t < n)
    (μ : (∀ i,A i) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (ν : (∀ i,A i) → A ⟨t,ht⟩ → ℝ) (hν : ∀ x y, 0 ≤ ν x y)
    (h : (∀ i,A i) → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hmass : ∀ x, (∑ y,ν x y) = μ x*h x)
    (ρ : A ⟨t,ht⟩ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ x y, ν x y ≤ c*μ x*ρ y)
    (r : ℕ → ℝ) (hr : ∀ j < E ⟨t,ht⟩, 0 ≤ r j) (hrE : r (E ⟨t,ht⟩) = 0)
    (hdensity : ∀ k ∈ b.labels, ∀ j < E ⟨t,ht⟩, e k ⟨t,ht⟩ = j+1 →
      (∑ y, if y ∈ X k ⟨t,ht⟩ then ρ y else 0) ≤ r j)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, ∑ y, ν x y * φ (count A X b (Function.update x ⟨t,ht⟩ y))) ≤
      ∑ x, μ x * (∑ d : Option (Fin (E ⟨t,ht⟩)),
        coefficient (h x) (fun j => c*r j) (E ⟨t,ht⟩) d *
          φ (multiplier d * count A X (oldFamily b ht d) x)) := by
  classical
  let i : Fin n := ⟨t,ht⟩
  let w (g : ℕ) (k : b.labels) (x : ∀ i,A i) : ℝ :=
    if e k.val i = g+1 then indicator A t (e k.val) (X k.val) x/(b.multiplicity:ℝ) else 0
  let hit (g : ℕ) (k : b.labels) (y : A i) : Prop :=
    e k.val i = g+1 ∧ y ∈ X k.val i
  have hm : (b.multiplicity:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt b.positive
  have hms (a : ℕ) (x : ∀ i,A i) :
      (∑ k∈b.labels.filter (fun k => e k i ≤ a), indicator A t (e k) (X k) x)/(b.multiplicity:ℝ) =
      count A X (oldFamily b ht none) x +
        ∑ g∈Finset.range a, ∑ k : b.labels, w g k x := by
    rw [sum_filter_level_le,add_div]
    have hz : count A X (oldFamily b ht none) x =
        (∑ k∈b.labels.filter (fun k => e k i = 0),indicator A t (e k) (X k) x)/(b.multiplicity:ℝ) := by
      simpa only [multiplier,one_mul,Nat.le_zero_eq] using oldFamily_scaled A X b ht none x
    rw [hz]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [w]
    rw [Finset.sum_div,Finset.sum_filter]
    exact (Finset.sum_coe_sort b.labels (fun k => if e k i = g+1 then
      indicator A t (e k) (X k) x/(b.multiplicity:ℝ) else 0)).symm
  apply normalized_family_compression μ hμ ν hν h hh hmass ρ c hc hcap
    (E i) r hrE w ?_ hit ?_
    (fun d => count A X (oldFamily b ht d))
    (fun x y => count A X b (Function.update x i y)) ?_ ?_ φ hφ hmφ
  · intro g hg k x
    dsimp only [w]
    split_ifs
    · exact div_nonneg (indicator_nonneg A t (e k.val) (X k.val) x) (Nat.cast_nonneg _)
    · exact le_rfl
  · intro g hg k
    by_cases hk : e k.val i = g+1
    · simpa only [hit,hk,true_and] using hdensity k.val k.property g hg hk
    · simpa only [hit,hk,false_and,if_false,Finset.sum_const_zero] using hr g hg
  · intro x y
    have hfilter : b.labels.filter (fun k => e k i ≤ E i) = b.labels :=
      Finset.filter_true_of_mem (fun k _ => he k i)
    have hp := sum_filter_level_le b.labels (fun k => e k i) (E i)
      (fun k => indicator A (t+1) (e k) (X k) (Function.update x i y))
    rw [hfilter] at hp
    dsimp only
    rw [count,hp,add_div]
    congr 1
    · simp only [oldFamily,Family.truncate,count,Nat.zero_add,one_mul,Nat.le_zero_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [indicator_step,if_pos (Or.inl (show e k ⟨t,ht⟩ = 0 from (Finset.mem_filter.mp hk).2))]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g hg
      dsimp only [hit,w]
      rw [Finset.sum_div,Finset.sum_filter,Finset.sum_coe_sort b.labels (fun k =>
        if e k i = g+1 ∧ y ∈ X k i then
          (if e k i = g+1 then indicator A t (e k) (X k) x/(b.multiplicity:ℝ) else 0) else 0)]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkg : e k i = g+1
      · rw [if_pos hkg,indicator_step]
        simp only [show ¬e k ⟨t,ht⟩ = 0 by change ¬e k i=0; omega,false_or,hkg,true_and,if_true]
        split_ifs <;> simp
      · simp only [hkg,false_and,if_false]
  · intro j x
    rw [oldFamily_scaled]
    exact (hms (j.val+1) x).symm

end Compression
#print axioms complete_family_compression
end Erdos7CompleteFamilyModel
