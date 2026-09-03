import Submission.TriangleHit

/-!
The Hilbert triangle-hitting criterion is not necessary for countable
triangle-free edge covering in general. Complete graphs on binary sequences
are countably coverable, but have no such representation. They are NOT
K4-free, so this does not settle Erdős 595 or exclude the criterion on that
restricted class.
-/

open SimpleGraph Set
open scoped BigOperators
namespace Erdos595HilbertStrictness

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_sum_le_diagonal (v : I → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) ≤ 0)) (s : Finset I) :
    inner ℝ (∑ i ∈ s, v i) (∑ i ∈ s, v i) ≤ ∑ i ∈ s, inner ℝ (v i) (v i) := by
  classical
  rw [sum_inner]
  apply Finset.sum_le_sum
  intro i hi
  rw [inner_sum]
  calc
    ∑ j ∈ s, inner ℝ (v i) (v j) ≤
        ∑ j ∈ s, if j = i then inner ℝ (v i) (v i) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · subst j; exact le_rfl
      · exact hv (Ne.symm h)
    _ = inner ℝ (v i) (v i) := by simp [hi]

/-- A Bessel-type inequality for a family of unit vectors with nonpositive
mutual inner products, all strictly negative against a fixed anchor. -/
lemma sum_sq_anchor_le (u : E) (v : I → E)
    (hu : ∀ i, inner ℝ u (v i) < 0)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) ≤ 0))
    (hunit : ∀ i, inner ℝ (v i) (v i) = 1) (s : Finset I) :
    (∑ i ∈ s, (inner ℝ u (v i)) ^ 2) ≤ inner ℝ u u := by
  let a : I → ℝ := fun i => -inner ℝ u (v i)
  let w : I → E := fun i => a i • v i
  have ha : ∀ i, 0 ≤ a i := fun i => neg_nonneg.mpr (hu i).le
  have hw : Pairwise (fun i j => inner ℝ (w i) (w j) ≤ 0) := by
    intro i j hij
    simp only [w,real_inner_smul_left,real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (ha j)
      (mul_nonpos_of_nonneg_of_nonpos (ha i) (hv hij))
  have hdiag := inner_sum_le_diagonal w hw s
  have hsq : ∑ i ∈ s, inner ℝ (w i) (w i) =
      ∑ i ∈ s, (inner ℝ u (v i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [w,real_inner_smul_left,real_inner_smul_right,hunit,mul_one,a]
    ring
  have hlin : inner ℝ u (∑ i ∈ s, w i) =
      -(∑ i ∈ s, (inner ℝ u (v i)) ^ 2) := by
    rw [inner_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [w,real_inner_smul_right,a]
    ring
  have hp := real_inner_self_nonneg (x := u + ∑ i ∈ s, w i)
  rw [inner_add_left,inner_add_right,inner_add_right,
    real_inner_comm u (∑ i ∈ s, w i),hlin] at hp
  rw [hsq] at hdiag
  linarith

lemma countable_of_negative_anchor_unit (u : E) (v : I → E)
    (hu : ∀ i, inner ℝ u (v i) < 0)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) ≤ 0))
    (hunit : ∀ i, inner ℝ (v i) (v i) = 1) : Countable I := by
  have hs : Summable (fun i => (inner ℝ u (v i)) ^ 2) :=
    summable_of_sum_le (fun i => sq_nonneg _) (sum_sq_anchor_le u v hu hv hunit)
  have hc := hs.countable_support
  have he : Function.support (fun i => (inner ℝ u (v i)) ^ 2) = Set.univ := by
    ext i
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact pow_ne_zero _ (ne_of_lt (hu i))
  rw [he] at hc
  exact Set.countable_univ_iff.mp hc

lemma countable_of_negative_anchor (u : E) (v : I → E)
    (hu : ∀ i, inner ℝ u (v i) < 0)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) ≤ 0)) : Countable I := by
  have hne : ∀ i, v i ≠ 0 := by
    intro i h
    have hi := hu i
    rw [h,inner_zero_right] at hi
    exact (lt_irrefl _ hi)
  let w : I → E := fun i => (‖v i‖⁻¹ : ℝ) • v i
  have hpos : ∀ i, 0 < (‖v i‖⁻¹ : ℝ) := fun i => inv_pos.mpr (norm_pos_iff.mpr (hne i))
  apply countable_of_negative_anchor_unit u w
  · intro i
    simp only [w,real_inner_smul_right]
    exact mul_neg_of_pos_of_neg (hpos i) (hu i)
  · intro i j hij
    simp only [w,real_inner_smul_left,real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (hpos j).le
      (mul_nonpos_of_nonneg_of_nonpos (hpos i).le (hv hij))
  · intro i
    exact inner_self_eq_one_of_norm_eq_one (𝕜 := ℝ) (norm_smul_inv_norm (hne i))

/-- A pairwise strictly obtuse family in a real inner-product space is countable. -/
theorem countable_of_pairwise_negative (v : I → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) < 0)) : Countable I := by
  classical
  by_cases hI : Nonempty I
  · obtain ⟨i⟩ := hI
    have hct : Countable {j : I | j ≠ i} :=
      countable_of_negative_anchor (v i) (fun j : {j : I | j ≠ i} => v j)
        (fun j => hv (Ne.symm j.property))
        (fun j k h => (hv (fun he => h (Subtype.ext he))).le)
    have hc : ({j : I | j ≠ i} : Set I).Countable := hct
    apply Set.countable_univ_iff.mp
    apply (hc.union (Set.countable_singleton i)).mono
    intro j _
    by_cases h : j = i
    · exact Or.inr h
    · exact Or.inl h
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    infer_instance

/-- If every triple of distinct indices has a strictly negative pair,
there can only be countably many indices. -/
theorem countable_of_triangle_hit_complete (v : I → E)
    (hv : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      inner ℝ (v a) (v b) < 0 ∨ inner ℝ (v a) (v c) < 0 ∨
        inner ℝ (v b) (v c) < 0) : Countable I := by
  classical
  let G : SimpleGraph I :=
    { Adj := fun a b => a ≠ b ∧ 0 ≤ inner ℝ (v a) (v b)
      symm := fun _ _ h => ⟨Ne.symm h.1,by simpa only [real_inner_comm] using h.2⟩
      loopless := fun _ h => h.1 rfl }
  have hdeg : ∀ a, (G.neighborSet a).Countable := by
    intro a
    apply countable_of_pairwise_negative (fun b : G.neighborSet a => v b)
    intro b c hbc
    have hne : b.val ≠ c.val := fun h => hbc (Subtype.ext h)
    rcases hv a b c b.property.1 c.property.1 hne with h | h | h
    · exact ((not_lt_of_ge b.property.2) h).elim
    · exact ((not_lt_of_ge c.property.2) h).elim
    · exact h
  obtain ⟨f⟩ := Erdos595Work.coloring_nat_of_countable_neighbors G hdeg
  have hf : ∀ n, {a | f a = n}.Countable := by
    intro n
    apply countable_of_pairwise_negative (fun a : {a | f a = n} => v a)
    intro a b hab
    by_contra hn
    have hadj : G.Adj a b := ⟨fun h => hab (Subtype.ext h),le_of_not_gt hn⟩
    exact f.valid hadj (a.property.trans b.property.symm)
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion hf).mono
  intro a _
  exact Set.mem_iUnion.mpr ⟨f a,rfl⟩

/-- Binary sequences are uncountable, by Cantor's theorem. -/
lemma binary_not_countable : ¬Countable (ℕ → Fin 2) := by
  classical
  intro h
  letI := h
  let f : Set ℕ → ℕ → Fin 2 := fun S n => if n ∈ S then 1 else 0
  have hf : Function.Injective f := by
    intro S T he
    ext n
    have hn := congrFun he n
    by_cases hs : n ∈ S <;> by_cases ht : n ∈ T <;> simp_all [f]
  obtain ⟨g,hg⟩ := exists_injective_nat (ℕ → Fin 2)
  exact Function.cantor_injective (g ∘ f) (hg.comp hf)

/-- This separation example is countably coverable, but is not K4-free. -/
theorem coverable_without_hilbert_hit :
    Erdos595Work.IsCountableUnionOfTriangleFree (⊤ : SimpleGraph (ℕ → Fin 2)) ∧
      ∀ (v : (ℕ → Fin 2) → E), ¬(∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        inner ℝ (v a) (v b) < 0 ∨ inner ℝ (v a) (v c) < 0 ∨
          inner ℝ (v b) (v c) < 0) := by
  refine ⟨Erdos595Work.countable_union_of_binary_encoding _ id Function.injective_id,?_⟩
  intro v hv
  exact binary_not_countable (countable_of_triangle_hit_complete v hv)

#print axioms countable_of_pairwise_negative
#print axioms countable_of_triangle_hit_complete
#print axioms coverable_without_hilbert_hit
end Erdos595HilbertStrictness
