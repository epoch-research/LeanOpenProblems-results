import Submission.FiniteAdaptedExtension

/-!
A countable increasing union of induced subgraphs can lose the existence of
an adapted labeling, even when every stage has a bounded adapted labeling for
one fixed edge coloring and the entire graph is triangle-free. This is an
obstruction to one proposed transfinite strategy, not a settlement of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595AdaptedLimit
open Erdos595Work Erdos595FiniteAdapted

abbrev X := ℕ → Fin 2

def zero : X := fun _ => 0
noncomputable def d (x y : X) : ℕ := firstDifference id Function.injective_id x y

lemma d_find {x y : X} (h : x ≠ y) (hex : ∃ n, x n ≠ y n) :
    d x y = Nat.find hex := by
  classical
  simp only [d,firstDifference,dif_neg h]

lemma d_symm (x y : X) : d x y = d y x := by
  classical
  by_cases h : x = y
  · subst y; rfl
  · have hex : ∃ n, x n ≠ y n := Function.ne_iff.mp h
    have hey : ∃ n, y n ≠ x n := Function.ne_iff.mp (Ne.symm h)
    rw [d_find h hex,d_find (Ne.symm h) hey]
    apply le_antisymm
    · exact Nat.find_min' hex (Ne.symm (Nat.find_spec hey))
    · exact Nat.find_min' hey (Ne.symm (Nat.find_spec hex))

lemma d_spec {x y : X} (h : x ≠ y) : x (d x y) ≠ y (d x y) := by
  classical
  have hex : ∃ n, x n ≠ y n := Function.ne_iff.mp h
  rw [d_find h hex]
  exact Nat.find_spec hex

noncomputable def label (x y : X) : ℕ := by
  classical
  exact if x = y then 0 else d x y + 1

lemma label_symm (x y : X) : label x y = label y x := by
  classical
  by_cases h : x = y
  · subst y; rfl
  · simp only [label,if_neg h,if_neg (Ne.symm h),d_symm x y]

/-- Allowing the equal-input case with label zero repairs the diagonal
argument after all unequal-input labels are shifted up by one. -/
theorem label_no_adapted (g : X → ℕ) :
    ∃ x y, g x = label x y ∧ g y = label x y := by
  classical
  by_cases hzero : ∃ x, g x = 0
  · obtain ⟨x,hx⟩ := hzero
    exact ⟨x,x,by simp [label,hx],by simp [label,hx]⟩
  · have hpos : ∀ x, 0 < g x := by intro x; exact Nat.pos_of_ne_zero (fun h => hzero ⟨x,h⟩)
    obtain ⟨x,y,hxy,hx,hy⟩ := firstDifference_no_adapted (fun x => g x - 1)
    change g x - 1 = d x y at hx
    change g y - 1 = d x y at hy
    refine ⟨x,y,?_,?_⟩ <;> simp only [label,if_neg hxy] <;>
      have hpx := hpos x <;> have hpy := hpos y <;> omega

noncomputable def stage (n : ℕ) : Set X := {x | x = zero ∨ d x zero < n}

lemma stage_mono : Monotone stage := by
  intro n m hnm x hx
  exact hx.imp_right (fun h => h.trans_le hnm)

lemma stages_cover (x : X) : ∃ n, x ∈ stage n := by
  exact ⟨d x zero + 1,Or.inr (Nat.lt_succ_self _)⟩

noncomputable def stageLabel (n : ℕ) (x : X) : ℕ := by
  classical
  exact if x = zero then n + 1 else d x zero + 1

lemma stageLabel_pos (n : ℕ) (x : X) : 0 < stageLabel n x := by
  classical
  unfold stageLabel
  split_ifs <;> omega

lemma stageLabel_bound {n : ℕ} {x : X} (hx : x ∈ stage n) :
    stageLabel n x < n + 2 := by
  classical
  unfold stageLabel
  split_ifs with he
  · omega
  · have hd : d x zero < n := hx.resolve_left he
    omega

/-- On each stage these labels adapt to the fixed edge-label function,
without using any information about the base graph. -/
lemma stageLabel_adapted {n : ℕ} {x y : X} (hx : x ∈ stage n) (hy : y ∈ stage n) :
    ¬(stageLabel n x = label x y ∧ stageLabel n y = label x y) := by
  classical
  rintro ⟨he₁,he₂⟩
  by_cases hxy : x = y
  · have hp := stageLabel_pos n x
    simp only [label,if_pos hxy] at he₁
    omega
  have hd₁ : stageLabel n x = d x y + 1 := by simpa only [label,if_neg hxy] using he₁
  have hd₂ : stageLabel n y = d x y + 1 := by simpa only [label,if_neg hxy] using he₂
  by_cases hxz : x = zero
  · have hyz : y ≠ zero := fun h => hxy (hxz.trans h.symm)
    have hr : d y zero < n := hy.resolve_left hyz
    simp only [stageLabel,if_pos hxz] at hd₁
    simp only [stageLabel,if_neg hyz] at hd₂
    omega
  by_cases hyz : y = zero
  · have hr : d x zero < n := hx.resolve_left hxz
    simp only [stageLabel,if_neg hxz] at hd₁
    simp only [stageLabel,if_pos hyz] at hd₂
    omega
  simp only [stageLabel,if_neg hxz,Nat.add_right_cancel_iff] at hd₁
  simp only [stageLabel,if_neg hyz,Nat.add_right_cancel_iff] at hd₂
  have hxn := d_spec hxz
  have hyn := d_spec hyz
  have hdn := d_spec hxy
  rw [hd₁] at hxn
  rw [hd₂] at hyn
  change x (d x y) ≠ 0 at hxn
  change y (d x y) ≠ 0 at hyn
  have hxe : x (d x y) = 1 := by have := (x (d x y)).isLt; omega
  have hye : y (d x y) = 1 := by have := (y (d x y)).isLt; omega
  exact hdn (hxe.trans hye.symm)

/-- A single triangle-free graph with a coherent fixed edge coloring and a
countable exhaustion by stages with bounded adapted labelings, but with NO
adapted labeling on the union. -/
theorem exists_adapted_limit_failure :
    ∃ (V : Type) (G : SimpleGraph V) (c : Sym2 V → ℕ) (S : ℕ → Set V),
      G.CliqueFree 3 ∧ Valid G c ∧ Monotone S ∧ (∀ v, ∃ n, v ∈ S n) ∧
      (∀ n, ∃ f : S n → ℕ,
        Adapted (G.induce (S n)) (fun e => c (e.map Subtype.val)) f ∧ ∀ v, f v < n + 2) ∧
      ¬∃ f : V → ℕ, Adapted G c f := by
  classical
  obtain ⟨B,G,hG,hχ⟩ := exists_triangleFree_not_colorable (X → ℕ)
  let F := G.comap (Prod.fst : B × X → B)
  let c : Sym2 (B × X) → ℕ := Sym2.lift ⟨fun a b => label a.2 b.2,
    fun a b => label_symm a.2 b.2⟩
  let S : ℕ → Set (B × X) := fun n => {v | v.2 ∈ stage n}
  have hF : F.CliqueFree 3 := by
    intro s hs
    obtain ⟨a,b,t,hab,hat,hbt,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show G.Adj a.1 b.1 ∧ G.Adj a.1 t.1 ∧ G.Adj b.1 t.1 from ⟨hab,hat,hbt⟩))
  refine ⟨B × X,F,c,S,hF,?_,?_,?_,?_,?_⟩
  · intro a b t hab hat hbt _
    exact hF _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hat,hbt⟩)
  · intro n m hnm v hv
    exact stage_mono hnm hv
  · intro v
    exact stages_cover v.2
  · intro n
    refine ⟨fun v => stageLabel n v.val.2,?_,?_⟩
    · intro a b _
      exact stageLabel_adapted a.property b.property
    · intro v
      exact stageLabel_bound v.property
  · rintro ⟨f,hf⟩
    apply hχ.false
    refine SimpleGraph.Coloring.mk (fun v (x : X) => f (v,x)) ?_
    intro v w hvw he
    obtain ⟨x,y,hx,hy⟩ := label_no_adapted (fun x => f (v,x))
    apply hf (v,x) (w,y) hvw
    exact ⟨hx,(congrFun he y).symm.trans hy⟩

#print axioms label_no_adapted
#print axioms stageLabel_adapted
#print axioms exists_adapted_limit_failure
end Erdos595AdaptedLimit
