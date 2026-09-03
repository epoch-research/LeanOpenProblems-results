import FormalConjecturesUtil

/-! Components of a restricted local/radial/conjugate Clifford analysis.
The full pairing-to-geometry wrapper is not asserted here, and none of these
statements bounds arbitrary rational-distance configurations. -/
namespace Erdos213.CliffordPairedRules
open EuclideanGeometry
noncomputable section

/-- A clique in the Cartesian rook relation has one coordinate constant. -/
theorem rook_clique {α β : Type*} (S : Set (α × β))
    (h : ∀ p ∈ S, ∀ q ∈ S, p.1=q.1 ∨ p.2=q.2) :
    (∀ p ∈ S, ∀ q ∈ S, p.1=q.1) ∨
    (∀ p ∈ S, ∀ q ∈ S, p.2=q.2) := by
  classical
  by_cases ha : ∀ p ∈ S, ∀ q ∈ S, p.1=q.1
  · exact Or.inl ha
  push_neg at ha
  obtain ⟨p,hp,q,hq,hpq⟩ := ha
  have hpq' : p.2=q.2 := (h p hp q hq).resolve_left hpq
  have hall : ∀ r ∈ S, r.2=p.2 := by
    intro r hr
    by_contra hn
    have hrp := (h r hr p hp).resolve_right hn
    have hrq := (h r hr q hq).resolve_right (by simpa [← hpq'] using hn)
    exact hpq (hrp.symm.trans hrq)
  exact Or.inr (fun r hr s hs => (hall r hr).trans (hall s hs).symm)

/-- In a polar product grid, one rook coordinate gives a radial line and the
other a concentric circle. Thus a whole rook clique is generalized-circular. -/
theorem polar_rook_clique_line_or_circle {α β : Type*}
    (S : Set (α × β)) (z : α → ℂ) (r : β → ℝ) (T : ℂ) (R : ℝ)
    (hn : ∀ a, ‖z a‖=R)
    (h : ∀ p ∈ S, ∀ q ∈ S, p.1=q.1 ∨ p.2=q.2) :
    Collinear ℝ ((fun p : α × β => T+(r p.2 : ℂ)*z p.1) '' S) ∨
    Cospherical ((fun p : α × β => T+(r p.2 : ℂ)*z p.1) '' S) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨p,hp⟩
  · left
    simpa using collinear_empty ℝ ℂ
  rcases rook_clique S h with ha | hb
  · left
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨T,z p.1,?_⟩
    rintro x ⟨q,hq,rfl⟩
    refine ⟨r q.2,?_⟩
    dsimp only
    rw [Complex.real_smul,vadd_eq_add,ha q hq p hp]
    ring
  · right
    refine ⟨T,|r p.2| * R,?_⟩
    rintro x ⟨q,hq,rfl⟩
    dsimp only
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,hn]
    rw [Complex.norm_real,Real.norm_eq_abs,hb q hq p hp]

open scoped symmDiff

/-- The opposite branch in the local triangle normal form cannot have the
same paired-support parity when the three mate-pair labels are distinct. -/
theorem distinct_labels_parity {ι : Type*} [DecidableEq ι] {p q r s : ι}
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    ({p} ∆ {r} : Finset ι) ≠ ({q} ∆ {s} : Finset ι) := by
  intro he
  by_cases hsq : s=q
  · subst s
    have hp : p ∈ ({p} ∆ {r} : Finset ι) := by simp [Finset.mem_symmDiff,hpr]
    rw [he] at hp
    simp at hp
  · have hq : q ∈ ({q} ∆ {s} : Finset ι) := by simp [Finset.mem_symmDiff,Ne.symm hsq]
    rw [← he] at hq
    simp [Finset.mem_symmDiff,Ne.symm hpq,hqr] at hq

/-- The eight even vertices of a four-bit cell are indexed by masks
0,3,5,6,9,10,12,15. The first eight blocks are the neighbors of its odd
vertices 1,2,4,7,8,11,13,14; the last two are radial and concentric blocks. -/
def cellBlock : Fin 10 → Finset (Fin 8) :=
  ![{0,1,2,4},{0,1,3,5},{0,2,3,6},{1,2,3,7},
    {0,4,5,6},{1,4,5,7},{2,4,6,7},{3,5,6,7},
    {0,1,6,7},{2,3,4,5}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every six vertices of this cell contain a complete four-point block.
The geometric incidence of the blocks is separate from this certificate. -/
theorem six_contains_cellBlock : ∀ S : Finset (Fin 8), 6≤S.card →
    ∃ i : Fin 10, cellBlock i ⊆ S := by
  decide

lemma cellBlock_card (i : Fin 10) : (cellBlock i).card=4 := by
  fin_cases i <;> decide

#print axioms rook_clique
#print axioms polar_rook_clique_line_or_circle
#print axioms distinct_labels_parity
#print axioms six_contains_cellBlock
end
end Erdos213.CliffordPairedRules
