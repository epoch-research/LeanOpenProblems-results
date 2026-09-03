import Submission.MultiPacketExplore

/-! Finite joint selection of several symmetric packets. Collision costs are
charged to a chosen coordinate in each event, allowing the largest scale to
pay for that event. -/
namespace Erdos66MultiPacketSelection
open Erdos66MultiPacket Erdos66HeterogeneousSelection
open scoped Classical
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

abbrev Label (ι : Type*) := ι × Bool
abbrev Quad (ι : Type*) := Label ι × Label ι × Label ι × Label ι

noncomputable def pointEvents : Finset (Label ι × Label ι) :=
  Finset.univ.filter (fun p ↦ p.1 ≠ p.2)

noncomputable def pairEvents : Finset (Quad ι) :=
  Finset.univ.filter (fun p ↦
    ¬ Designated p.1 p.2.1 ∧ ¬ Designated p.2.2.1 p.2.2.2 ∧
    p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2)

def chosen (x : ∀ i, α i → ℤ) (ω : ∀ i, α i) : ι → ℤ := fun i ↦ x i (ω i)

lemma chosen_update (x : ∀ i, α i → ℤ) (ω : ∀ i, α i) (i : ι) (a : α i) :
    chosen x (Function.update ω i a) = Function.update (chosen x ω) i (x i a) := by
  funext j
  by_cases h : j = i
  · subst j; simp [chosen]
  · simp [chosen, Function.update_of_ne h]

/-- The finite potential bound gives simultaneously distinct points, Sidon
non-designated sums, avoidance of old points, and all mixed-hit tests. -/
theorem exists_joint_packets {ζ : Type*} (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (hx : ∀ i, Function.Injective (x i)) (B : ∀ i, Finset (α i))
    (v₂ : Label ι × Label ι → ι) (v₄ : Quad ι → ι)
    (hv₂ : ∀ p ∈ (pointEvents : Finset (Label ι × Label ι)), v₂ p = p.1.1 ∨ v₂ p = p.2.1)
    (hv₄ : ∀ p ∈ (pairEvents : Finset (Quad ι)),
      v₄ p = p.1.1 ∨ v₄ p = p.2.1.1 ∨ v₄ p = p.2.2.1.1 ∨ v₄ p = p.2.2.2.1)
    (T : Finset ζ) (S : ζ → ∀ i, Finset (α i)) (R t : ζ → ℝ)
    (ht : ∀ z ∈ T, 0 < t z)
    (hsmall : (∑ p ∈ (pointEvents : Finset (Label ι × Label ι)), 1 / (Fintype.card (α (v₂ p)) : ℝ)) +
      (∑ p ∈ (pairEvents : Finset (Quad ι)), 1 / (Fintype.card (α (v₄ p)) : ℝ)) + hitMass B +
      (∑ z ∈ T, Real.exp (Real.exp (t z) * hitMass (S z) - t z * R z)) < 1) :
    ∃ ω : ∀ i, α i,
      Function.Injective (point n (chosen x ω)) ∧ (∀ i, ω i ∉ B i) ∧
      (∀ u v w t : Label ι, ¬ Designated u v → ¬ Designated w t →
        point n (chosen x ω) u + point n (chosen x ω) v =
          point n (chosen x ω) w + point n (chosen x ω) t →
          (u = w ∧ v = t) ∨ (u = t ∧ v = w)) ∧
      ∀ z ∈ T, hits (S z) ω < R z := by
  let D : Finset (Sigma α) := Finset.univ.filter (fun e ↦ e.2 ∈ B e.1)
  let E := ((pointEvents : Finset (Label ι × Label ι)).disjSum (pairEvents : Finset (Quad ι))).disjSum D
  let v : ((Label ι × Label ι) ⊕ Quad ι) ⊕ Sigma α → ι
    | .inl (.inl p) => v₂ p
    | .inl (.inr p) => v₄ p
    | .inr e => e.1
  let P : (((Label ι × Label ι) ⊕ Quad ι) ⊕ Sigma α) → (∀ i, α i) → Prop
    | .inl (.inl p), ω => point n (chosen x ω) p.1 = point n (chosen x ω) p.2
    | .inl (.inr p), ω => point n (chosen x ω) p.1 + point n (chosen x ω) p.2.1 =
        point n (chosen x ω) p.2.2.1 + point n (chosen x ω) p.2.2.2
    | .inr e, ω => ω e.1 = e.2
  have hP : ∀ e ∈ E, ∀ f : ∀ i, α i, ∀ a b : α (v e),
      P e (Function.update f (v e) a) → P e (Function.update f (v e) b) → a = b := by
    intro e he
    cases e with
    | inl e =>
      have he' := Finset.inl_mem_disjSum.mp he
      cases e with
      | inl p =>
        have hp := Finset.inl_mem_disjSum.mp he'
        intro f a b ha hb
        have hh := point_collision_fiber n p.1 p.2 (Finset.mem_filter.mp hp).2
          (v₂ p) (hv₂ p hp) (chosen x f) (x (v₂ p) a) (x (v₂ p) b)
        dsimp only [P, v] at ha hb
        rw [chosen_update] at ha hb
        exact hx (v₂ p) (hh ha hb)
      | inr p =>
        have hp := Finset.inr_mem_disjSum.mp he'
        obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := (Finset.mem_filter.mp hp).2
        intro f a b ha hb
        have hh := pair_collision_fiber n p.1 p.2.1 p.2.2.1 p.2.2.2 h₁ h₂ h₃ h₄ h₅ h₆
          (v₄ p) (hv₄ p hp) (chosen x f) (x (v₄ p) a) (x (v₄ p) b)
        dsimp only [P, v] at ha hb
        rw [chosen_update] at ha hb
        exact hx (v₄ p) (hh ha hb)
    | inr e =>
      intro f a b ha hb
      dsimp only [P, v] at ha hb
      simp only [Function.update_self] at ha hb
      exact ha.trans hb.symm
  have hD : (∑ e ∈ D, 1 / (Fintype.card (α e.1) : ℝ)) = hitMass B := by
    simp only [D, Finset.sum_filter, Fintype.sum_sigma, hitMass]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hevent : (∑ e ∈ E, 1 / (Fintype.card (α (v e)) : ℝ)) =
      (∑ p ∈ (pointEvents : Finset (Label ι × Label ι)), 1 / (Fintype.card (α (v₂ p)) : ℝ)) +
      (∑ p ∈ (pairEvents : Finset (Quad ι)), 1 / (Fintype.card (α (v₄ p)) : ℝ)) + hitMass B := by
    simp only [E, Finset.sum_disjSum, v]
    rw [hD]
  have hsmall' : (∑ e ∈ E, 1 / (Fintype.card (α (v e)) : ℝ)) +
      ∑ z ∈ T, Real.exp (Real.exp (t z) * hitMass (S z) - t z * R z) < 1 := by
    rw [hevent]
    exact hsmall
  obtain ⟨ω, havoid, hhits⟩ := exists_avoid_and_small_hits E P v hP T S R t ht hsmall'
  have hinj : Function.Injective (point n (chosen x ω)) := by
    intro u v he
    by_contra hne
    have hp : (u,v) ∈ (pointEvents : Finset (Label ι × Label ι)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact havoid (.inl (.inl (u,v)))
      (Finset.inl_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr hp)) he
  refine ⟨ω, hinj, ?_, ?_, hhits⟩
  · intro i hi
    have hd : (⟨i, ω i⟩ : Sigma α) ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    exact havoid (.inr ⟨i,ω i⟩) (Finset.inr_mem_disjSum.mpr hd) rfl
  · apply non_designated_unique n (chosen x ω) hinj
    intro u v w t h₁ h₂ huw hut hvw hvt he
    have hp : (u,v,w,t) ∈ (pairEvents : Finset (Quad ι)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁,h₂,huw,hut,hvw,hvt⟩
    exact havoid (.inl (.inr (u,v,w,t)))
      (Finset.inl_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr hp)) he

end Erdos66MultiPacketSelection
