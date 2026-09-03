import Submission.RationalLinearFeasibility

/-! Closedness of the feasible right-hand sides of a finite system of real
linear inequalities, by Fourier--Motzkin elimination. No rounding assertion. -/
open scoped Classical BigOperators
namespace Erdos184.RealLinearFeasibility
open RationalLinearFeasibility
set_option maxHeartbeats 1000000

lemma between_finite_bounds {I J : Type*} [Fintype I] [Fintype J]
    (l : I → ℝ) (u : J → ℝ) (h : ∀ i j, l i ≤ u j) :
    ∃ q : ℝ, (∀ i, l i ≤ q) ∧ ∀ j, q ≤ u j := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    haveI := hI
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      haveI := hJ
      exact ⟨0,fun i => isEmptyElim i,fun j => isEmptyElim j⟩
    | inr hJ =>
      haveI := hJ
      obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
      exact ⟨u j,fun i => isEmptyElim i,fun k => hj k (Finset.mem_univ _)⟩
  | inr hI =>
    haveI := hI
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
    exact ⟨l i,fun k => hi k (Finset.mem_univ _),h i⟩

/-- Projecting away finitely many unrestricted real variables preserves
closedness for a fixed finite system of linear inequalities. -/
theorem isClosed_rhs_feasible (n : ℕ) {I : Type*} [Fintype I]
    (A : I → Fin n → ℝ) :
    IsClosed {b : I → ℝ | ∃ x : Fin n → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i} := by
  induction n generalizing I with
  | zero =>
    have heq : {b : I → ℝ | ∃ x : Fin 0 → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i} =
        {b | ∀ i, 0 ≤ b i} := by
      ext b
      simp
    rw [heq]
    simpa only [Set.setOf_forall] using isClosed_iInter
      (fun i : I => isClosed_le continuous_const (continuous_apply i))
  | succ n ih =>
    let Z := {i : I // A i 0 = 0}
    let N := {i : I // A i 0 < 0}
    let P := {i : I // 0 < A i 0}
    let J := Z ⊕ (N × P)
    let B : J → Fin n → ℝ := fun i j => match i with
      | .inl i => A i.val j.succ
      | .inr i => A i.2.val j.succ / A i.2.val 0 - A i.1.val j.succ / A i.1.val 0
    let proj : (I → ℝ) → J → ℝ := fun b i => match i with
      | .inl i => b i.val
      | .inr i => b i.2.val / A i.2.val 0 - b i.1.val / A i.1.val 0
    have heq (b : I → ℝ) :
        (∃ x : Fin (n+1) → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i) ↔
        (∃ y : Fin n → ℝ, ∀ i, (∑ j, B i j*y j) ≤ proj b i) := by
      constructor
      · rintro ⟨x,hx⟩
        have hnorm (i : I) : A i 0*x 0 + (∑ j : Fin n, A i j.succ*x j.succ) ≤ b i := by
          simpa only [Fin.sum_univ_succ] using hx i
        refine ⟨fun j => x j.succ,?_⟩
        intro i
        cases i with
        | inl i =>
          simpa only [i.property,zero_mul,zero_add,B,proj] using hnorm i.val
        | inr i =>
          obtain ⟨lo,up⟩ := i
          have hl := (normalized_neg lo.property).mp (hnorm lo.val)
          have hu := (normalized_pos up.property).mp (hnorm up.val)
          simp only [B,proj,sub_mul,Finset.sum_sub_distrib,div_mul_eq_mul_div]
          simp only [Finset.sum_div] at hl hu
          linarith
      · rintro ⟨x,hx⟩
        let r (i : I) := b i/A i 0 - (∑ j : Fin n, A i j.succ*x j)/A i 0
        have hr : ∀ lo : N, ∀ up : P, r lo.val ≤ r up.val := by
          intro lo up
          have hh := hx (.inr (lo,up))
          simp only [B,proj,sub_mul,Finset.sum_sub_distrib,div_mul_eq_mul_div] at hh
          dsimp only [r]
          simp only [Finset.sum_div]
          linarith
        obtain ⟨y,hylo,hyup⟩ := between_finite_bounds
          (fun lo : N => r lo.val) (fun up : P => r up.val) hr
        refine ⟨Fin.cons y x,?_⟩
        intro i
        simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
        rcases lt_trichotomy (A i 0) 0 with hi | hi | hi
        · exact (normalized_neg hi).mpr (hylo ⟨i,hi⟩)
        · simpa only [B,proj,hi,zero_mul,zero_add] using hx (.inl ⟨i,hi⟩)
        · exact (normalized_pos hi).mpr (hyup ⟨i,hi⟩)
    have hcont : Continuous proj := by
      apply continuous_pi
      intro i
      cases i with
      | inl i => exact continuous_apply i.val
      | inr i =>
        exact ((continuous_apply i.2.val).div_const _).sub
          ((continuous_apply i.1.val).div_const _)
    have hset : {b : I → ℝ | ∃ x : Fin (n+1) → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i} =
        proj ⁻¹' {c : J → ℝ | ∃ x : Fin n → ℝ, ∀ i, (∑ j, B i j*x j) ≤ c i} := by
      ext b
      exact heq b
    rw [hset]
    exact (ih B).preimage hcont

lemma isClosed_rhs_feasible_fintype {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) :
    IsClosed {b : I → ℝ | ∃ x : J → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i} := by
  let e := Fintype.equivFin J
  have heq : {b : I → ℝ | ∃ x : J → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i} =
      {b : I → ℝ | ∃ x : Fin (Fintype.card J) → ℝ,
        ∀ i, (∑ j, A i (e.symm j)*x j) ≤ b i} := by
    ext b
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨fun j => x (e.symm j),?_⟩
      intro i
      simpa only [e.symm.sum_comp (fun j => A i j*x j)] using hx i
    · rintro ⟨x,hx⟩
      refine ⟨fun j => x (e j),?_⟩
      intro i
      have he : (∑ j, A i j*x (e j)) = ∑ j, A i (e.symm j)*x j := by
        exact Fintype.sum_equiv e _ _ (by intro j; simp)
      rw [he]
      exact hx i
  rw [heq]
  exact isClosed_rhs_feasible _ _

/-- A finite linear objective attains its supremum whenever its feasible
superlevel set is nonempty and bounded above. -/
theorem objective_attained {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ)
    (hne : ∃ x : J → ℝ, ∀ i, (∑ j, A i j*x j) ≤ b i)
    (hbd : BddAbove {z : ℝ | ∃ x : J → ℝ,
      (∀ i, (∑ j, A i j*x j) ≤ b i) ∧ z ≤ ∑ j, c j*x j}) :
    ∃ x : J → ℝ, (∀ i, (∑ j, A i j*x j) ≤ b i) ∧
      ∀ y : J → ℝ, (∀ i, (∑ j, A i j*y j) ≤ b i) →
        (∑ j, c j*y j) ≤ ∑ j, c j*x j := by
  let S : Set ℝ := {z | ∃ x : J → ℝ,
      (∀ i, (∑ j, A i j*x j) ≤ b i) ∧ z ≤ ∑ j, c j*x j}
  let A' : Option I → J → ℝ := fun i j => i.elim (-c j) (fun i => A i j)
  let rhs : ℝ → Option I → ℝ := fun z i => i.elim (-z) b
  have hs : IsClosed S := by
    have hcont : Continuous rhs := by
      apply continuous_pi
      intro i
      cases i <;> dsimp [rhs] <;> fun_prop
    have heq : S = rhs ⁻¹' {d : Option I → ℝ |
        ∃ x : J → ℝ, ∀ i, (∑ j, A' i j*x j) ≤ d i} := by
      ext z
      constructor
      · rintro ⟨x,hx,hz⟩
        refine ⟨x,?_⟩
        intro i
        cases i with
        | none => simpa [A',rhs,neg_mul,Finset.sum_neg_distrib] using neg_le_neg hz
        | some i => exact hx i
      · rintro ⟨x,hx⟩
        refine ⟨x,fun i => hx (some i),?_⟩
        have hh := hx none
        simpa [A',rhs,neg_mul,Finset.sum_neg_distrib] using hh
    rw [heq]
    exact (isClosed_rhs_feasible_fintype A').preimage hcont
  have hn : S.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨_,x,hx,le_rfl⟩
  obtain ⟨x,hx,hval⟩ := hs.csSup_mem hn hbd
  refine ⟨x,hx,?_⟩
  intro y hy
  exact (le_csSup hbd (show (∑ j, c j*y j) ∈ S from ⟨y,hy,le_rfl⟩)).trans hval

end Erdos184.RealLinearFeasibility
