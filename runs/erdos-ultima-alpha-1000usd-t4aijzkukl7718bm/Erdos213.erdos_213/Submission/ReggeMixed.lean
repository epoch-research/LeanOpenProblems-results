import Mathlib.Tactic

/-! Mixed local Regge moves cannot change a consistently labelled complete
edge array on six or more vertices. This is a compatibility theorem, not an
upper bound for integral-distance configurations. Independent rescaling of
four-point subsets is not included. -/
namespace Erdos213.ReggeMixed

/-- The six-edge perimeter of a labelled quadruple. -/
def quadSum {ι : Type*} (w : ι → ι → ℝ) (a b c d : ι) : ℝ :=
  w a b + w a c + w a d + w b c + w b d + w c d

/-- Reconstruction of one edge from the fifteen four-vertex perimeters
on six labelled vertices. Symmetry of the edge function is not needed
because all edges in this identity use the same ordering of vertices. -/
lemma reconstruct {ι : Type*} (w : ι → ι → ℝ) (i j a b c d : ι) :
    6 * w i j =
      quadSum w i j a b + quadSum w i j a c + quadSum w i j a d +
      quadSum w i j b c + quadSum w i j b d + quadSum w i j c d -
      (quadSum w i a b c + quadSum w i a b d + quadSum w i a c d +
       quadSum w i b c d + quadSum w j a b c + quadSum w j a b d +
       quadSum w j a c d + quadSum w j b c d) + 3 * quadSum w a b c d := by
  dsimp [quadSum]
  ring

set_option maxHeartbeats 2000000 in
/-- On any finite set of at least six vertices, agreement of all four-vertex
perimeters implies agreement of every off-diagonal edge. -/
theorem rigidity {ι : Type*} (s : Finset ι) (hs : 6 ≤ s.card)
    (u v : ι → ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      quadSum u i j k l = quadSum v i j k l)
    (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) (hij : i ≠ j) :
    u i j = v i j := by
  classical
  have hcard : 4 ≤ (s \ {i,j}).card := by
    have hle := Finset.le_card_sdiff ({i,j} : Finset ι) s
    have htwo : ({i,j} : Finset ι).card = 2 := by simp [hij]
    rw [htwo] at hle
    omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp htc
  have hmem (x : ι) (hx : x ∈ ({a,b,c,d} : Finset ι)) :
      x ∈ s ∧ x ≠ i ∧ x ≠ j := by
    simpa only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      using ht hx
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hc := hmem c (by simp)
  have hd := hmem d (by simp)
  have hia := ha.2.1.symm
  have hja := ha.2.2.symm
  have hib := hb.2.1.symm
  have hjb := hb.2.2.symm
  have hic := hc.2.1.symm
  have hjc := hc.2.2.symm
  have hid := hd.2.1.symm
  have hjd := hd.2.2.symm
  have h1 : quadSum u i j a b = quadSum v i j a b := by apply h <;> tauto
  have h2 : quadSum u i j a c = quadSum v i j a c := by apply h <;> tauto
  have h3 : quadSum u i j a d = quadSum v i j a d := by apply h <;> tauto
  have h4 : quadSum u i j b c = quadSum v i j b c := by apply h <;> tauto
  have h5 : quadSum u i j b d = quadSum v i j b d := by apply h <;> tauto
  have h6 : quadSum u i j c d = quadSum v i j c d := by apply h <;> tauto
  have h7 : quadSum u i a b c = quadSum v i a b c := by apply h <;> tauto
  have h8 : quadSum u i a b d = quadSum v i a b d := by apply h <;> tauto
  have h9 : quadSum u i a c d = quadSum v i a c d := by apply h <;> tauto
  have h10 : quadSum u i b c d = quadSum v i b c d := by apply h <;> tauto
  have h11 : quadSum u j a b c = quadSum v j a b c := by apply h <;> tauto
  have h12 : quadSum u j a b d = quadSum v j a b d := by apply h <;> tauto
  have h13 : quadSum u j a c d = quadSum v j a c d := by apply h <;> tauto
  have h14 : quadSum u j b c d = quadSum v j b c d := by apply h <;> tauto
  have h15 : quadSum u a b c d = quadSum v a b c d := by apply h <;> tauto
  have hu := reconstruct u i j a b c d
  have hv := reconstruct v i j a b c d
  rw [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15] at hu
  linarith

abbrev Edges := Fin 6 → ℝ

def edgeSum (e : Edges) : ℝ := ∑ i, e i

/-- Edge order AB, AC, AD, BC, BD, CD. -/
def edges {ι : Type*} (w : ι → ι → ℝ) (a b c d : ι) : Edges :=
  ![w a b,w a c,w a d,w b c,w b d,w c d]

lemma edges_sum {ι : Type*} (w : ι → ι → ℝ) (a b c d : ι) :
    edgeSum (edges w a b c d) = quadSum w a b c d := by
  simp [edgeSum,edges,quadSum,Fin.sum_univ_succ]
  ring

/-- The three choices of a fixed pair of opposite edges in Regge's move. -/
noncomputable def move (k : Fin 3) (e : Edges) : Edges :=
  let s₀ := (e 1 + e 2 + e 3 + e 4)/2
  let s₁ := (e 0 + e 2 + e 3 + e 5)/2
  let s₂ := (e 0 + e 1 + e 4 + e 5)/2
  ![ ![e 0,s₀-e 1,s₀-e 2,s₀-e 3,s₀-e 4,e 5],
     ![s₁-e 0,e 1,s₁-e 2,s₁-e 3,e 4,s₁-e 5],
     ![s₂-e 0,s₂-e 1,e 2,e 3,s₂-e 4,s₂-e 5] ] k

lemma move_sum (k : Fin 3) (e : Edges) : edgeSum (move k e) = edgeSum e := by
  fin_cases k <;> simp [edgeSum,move,Fin.sum_univ_succ] <;> ring

/-- We allow all edge permutations, a larger relation than just the vertex
permutations. This makes the resulting impossibility theorem stronger. -/
inductive Orbit : Edges → Edges → Prop
  | refl (e) : Orbit e e
  | perm (e) (p : Equiv.Perm (Fin 6)) : Orbit e (e ∘ p)
  | regge (e) (k) : Orbit e (move k e)
  | trans {e f g} : Orbit e f → Orbit f g → Orbit e g

lemma orbit_sum {e f : Edges} (h : Orbit e f) : edgeSum e = edgeSum f := by
  induction h with
  | refl => rfl
  | perm e p => exact (Equiv.sum_comp p e).symm
  | regge e k => exact (move_sum k e).symm
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- Each quadruple may use its own sequence of moves and permutations.
Consistency on shared edges still forces the whole edge array to be fixed.
No triangle inequalities or planarity assumptions are needed. -/
theorem mixed_regge_rigid {ι : Type*} (s : Finset ι) (hs : 6 ≤ s.card)
    (u v : ι → ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      Orbit (edges u i j k l) (edges v i j k l))
    (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) (hij : i ≠ j) :
    u i j = v i j := by
  apply rigidity s hs u v _ i hi j hj hij
  intro a ha b hb c hc d hd hab hac had hbc hbd hcd
  simpa only [edges_sum] using orbit_sum (h a ha b hb c hc d hd hab hac had hbc hbd hcd)

#print axioms reconstruct
#print axioms rigidity
#print axioms move_sum
#print axioms orbit_sum
#print axioms mixed_regge_rigid
end Erdos213.ReggeMixed
