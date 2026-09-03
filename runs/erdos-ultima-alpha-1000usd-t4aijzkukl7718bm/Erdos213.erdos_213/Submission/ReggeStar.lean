import Submission.ReggeCircle

/-! The equal-radius-star locus has a 24-plane Regge orbit. This is a
construction-specific invariant, not a restriction on arbitrary integral sets. -/
namespace Erdos213.ReggeStar
open ReggeMixed ReggeCircle
noncomputable section
set_option maxHeartbeats 4000000

def form (e : Edges) : Fin 24 → Fin 2 → ℝ :=
  ![![(1)*(e 0) + (-1)*(e 2),(1)*(e 1) + (-1)*(e 2)],
    ![(2)*(e 0) + (-1)*(e 3) + (-1)*(e 4),(1)*(e 1) + (-1)*(e 2)],
    ![(1)*(e 0) + (-1)*(e 2),(2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)],
    ![(1)*(e 0) + (-1)*(e 1),(2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)],
    ![(1)*(e 0) + (-1)*(e 4),(1)*(e 3) + (-1)*(e 4)],
    ![(3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5),(3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5),(1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)],
    ![(2)*(e 0) + (-1)*(e 1) + (-1)*(e 2),(1)*(e 3) + (-1)*(e 4)],
    ![(3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5),(3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)],
    ![(1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5),(1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (-1)*(e 4),(1)*(e 1) + (-2)*(e 3) + (1)*(e 5)],
    ![(1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5),(1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5),(1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (-1)*(e 3),(1)*(e 2) + (-2)*(e 4) + (1)*(e 5)],
    ![(1)*(e 1) + (-1)*(e 5),(1)*(e 3) + (-1)*(e 5)],
    ![(1)*(e 0) + (-2)*(e 1) + (1)*(e 2),(1)*(e 3) + (-1)*(e 5)],
    ![(1)*(e 0) + (1)*(e 1) + (-2)*(e 2),(1)*(e 4) + (-1)*(e 5)],
    ![(1)*(e 0) + (-2)*(e 3) + (1)*(e 4),(1)*(e 1) + (-1)*(e 5)],
    ![(1)*(e 1) + (-1)*(e 3),(1)*(e 2) + (1)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5),(1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)],
    ![(1)*(e 0) + (1)*(e 3) + (-2)*(e 4),(1)*(e 2) + (-1)*(e 5)],
    ![(1)*(e 1) + (1)*(e 3) + (-2)*(e 5),(1)*(e 2) + (-1)*(e 4)],
    ![(1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5),(1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)],
    ![(1)*(e 2) + (-1)*(e 5),(1)*(e 4) + (-1)*(e 5)]]

def OnPlane (i : Fin 24) (e : Edges) : Prop := form e i 0=0 ∧ form e i 1=0

def StarLocus (e : Edges) : Prop := ∃ i, OnPlane i e

private def moveIndex : Fin 3 → Fin 24 → Fin 24 :=
  !![1,0,8,11,7,10,13,4,2,16,5,3,15,6,18,12,9,22,14,20,19,23,17,21;
    2,5,0,12,13,1,16,11,17,18,19,7,3,4,15,14,6,8,9,10,23,22,21,20;
    3,6,9,0,10,15,1,8,7,2,4,20,21,22,17,5,23,14,19,18,11,12,13,16]
lemma onPlane_move (e : Edges) (k : Fin 3) (i : Fin 24) (h : OnPlane i e) :
    OnPlane (moveIndex k i) (move k e) := by
  fin_cases k <;> fin_cases i
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0
    constructor
    · linear_combination (2)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0
    constructor
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (1)*(e 5)=0 ∧ (3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (2)*(e 5)=0
    constructor
    · linear_combination (3)*(h0) + (-1)*(h1)
    · linear_combination (-2)*(h1)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (2)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0
    constructor
    · linear_combination (2)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (1)*(e 5)=0
    constructor
    · linear_combination ((1/3 : ℝ))*(h0) + ((-1/6 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h1)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0
    constructor
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination (-1)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0 ∧ (2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(e 5)=0
    constructor
    · linear_combination ((1/3 : ℝ))*(h0) + ((-1/6 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((-3/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0 ∧ (3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (3)*(h0) + (-1)*(h1)
    · linear_combination (-2)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1))=0 ∧ (2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((3/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-2)*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (-1)*(h0) + (1)*(h1)
    · linear_combination (1)*(h0) + (1)*(h1)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (3)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-3)*(h1)
    · linear_combination (2)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (3)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-3)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (3)*(h1)
    · linear_combination (2)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-2)*(h1)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-1)*(e 5)=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (2)*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4)) + (-1)*(e 5)=0
    constructor
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h1)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 1)) + (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 3)) + (-2)*(e 5)=0 ∧ (1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 2)) + (-1)*(((e 1 + e 2 + e 3 + e 4)/2 - e 4))=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h0) + (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0 ∧ (2)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (-1)*(h0) + (2)*(h1)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (2)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (3)*(e 1) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (1)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h0)
    · linear_combination (-1)*(h0) + (3)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0 ∧ (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (1)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (2)*(h1)
    · linear_combination (-1)*(h0) + (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-2)*(e 4) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (1)*(h1)
    · linear_combination (1)*(h0) + (1)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0)
    · linear_combination ((-1/6 : ℝ))*(h0) + ((1/3 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (1)*(e 1) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0 ∧ (1)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-3/2 : ℝ))*(h0) + (1)*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (3)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (2)*(h1)
    · linear_combination (-1)*(h0) + (-3)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0)
    · linear_combination ((-1/6 : ℝ))*(h0) + ((1/3 : ℝ))*(h1)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + (1)*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (2)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (1)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h0)
    · linear_combination (-1)*(h0) + (1)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4)=0
    constructor
    · linear_combination ((-3/2 : ℝ))*(h0) + (-1)*(h1)
    · linear_combination ((1/2 : ℝ))*(h0)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(e 1)=0 ∧ (2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + (-1)*(h1)
    · linear_combination ((1/2 : ℝ))*(h0)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(e 4)=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4)=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-2)*(e 1) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-3)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h1)
    · linear_combination (1)*(h0) + (-3)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (3)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4) + (2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h0)
    · linear_combination (-1)*(h0) + (3)*(h1)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (-3)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h1)
    · linear_combination (1)*(h0) + (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0)
    · linear_combination ((-1/2 : ℝ))*(h0) + (1)*(h1)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 4) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(e 1) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-1)*(e 4) + (2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (2)*(h1)
    · linear_combination (1)*(h0) + (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(e 4)=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + (1)*(h1)
    · linear_combination ((1/2 : ℝ))*(h0)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 0)) + (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 3)) + (-2)*(e 4)=0 ∧ (1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 2)) + (-1)*(((e 0 + e 2 + e 3 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (1)*(h0) + (-2)*(h1)
    · linear_combination (-1)*(h0)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1))=0 ∧ (2)*(e 2) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h0) + (-1)*(h1)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (1)*(e 2) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (3)*(e 2) + (1)*(e 3) + (-3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h0) + (-3)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (3)*(e 2) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (1)*(e 2) + (1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-3)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h0) + (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 2)=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2)=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-2)*(e 3) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (1)*(h0) + (-2)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((-1/6 : ℝ))*(h0) + ((-1/6 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2)=0
    constructor
    · linear_combination ((-3/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (1)*(e 2) + (-3)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (-3)*(h1)
    · linear_combination (1)*(h0) + (-3)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((-1/6 : ℝ))*(h0) + ((-1/6 : ℝ))*(h1)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 2)=0 ∧ (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((1/2 : ℝ))*(h0) + ((-3/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0 ∧ (1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0 ∧ (1)*(e 2) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-3/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(e 2) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-3/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 2) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (-1)*(h1)
    · linear_combination (1)*(h0) + (-1)*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-2)*(e 3) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (1)*(h0) + (-2)*(h1)
    · linear_combination (-1)*(h0)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 2) + (-3)*(e 3) + (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (1)*(e 2) + (-3)*(e 3) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (-3)*(h1)
    · linear_combination (1)*(h0) + (-3)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 2) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(e 3) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 2) + (-1)*(e 3) + (2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 2) + (1)*(e 3) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h0) + (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (1)*(e 2) + (-1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-3)*(e 2) + (1)*(e 3) + (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-1)*(h0) + (1)*(h1)
    · linear_combination (1)*(h0) + (-3)*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-3)*(e 2) + (1)*(e 3) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (3)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (1)*(e 2) + (-1)*(e 3) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (1)*(h0) + (-3)*(h1)
    · linear_combination (-1)*(h0) + (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination ((-1/2 : ℝ))*(h0) + ((1/2 : ℝ))*(h1)
    · linear_combination ((-1/2 : ℝ))*(h0) + ((-1/2 : ℝ))*(h1)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 0)) + (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 1)) + (-2)*(e 2)=0 ∧ (1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 4)) + (-1)*(((e 0 + e 1 + e 4 + e 5)/2 - e 5))=0
    constructor
    · linear_combination (-2)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h1)

private def labelIndex : Fin 3 → Fin 24 → Fin 24 :=
  !![4,7,10,13,0,8,11,1,5,19,2,6,22,3,14,17,20,15,18,9,16,21,12,23;
    0,2,1,3,14,8,9,15,5,6,17,12,11,18,4,7,16,10,13,22,21,20,19,23;
    0,1,3,2,4,6,5,7,11,12,13,8,9,10,23,16,15,20,21,22,17,18,19,14]
lemma onPlane_label (e : Edges) (k : Fin 3) (i : Fin 24) (h : OnPlane i e) :
    OnPlane (labelIndex k i) (relabel k e) := by
  fin_cases k <;> fin_cases i
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-2)*(e 1) + (1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 1)=0 ∧ (1)*(e 4) + (-2)*(e 2) + (1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (1)*(e 4) + (-3)*(e 1) + (-2)*(e 2) + (1)*(e 5)=0 ∧ (3)*(e 3) + (-1)*(e 4) + (-3)*(e 1) + (-1)*(e 2) + (2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 4) + (-1)*(e 1) + (-2)*(e 2) + (1)*(e 5)=0 ∧ (1)*(e 3) + (-3)*(e 4) + (1)*(e 1) + (3)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (1)*(h1)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (-1)*(e 4) + (-3)*(e 1) + (2)*(e 2) + (-1)*(e 5)=0 ∧ (3)*(e 3) + (1)*(e 4) + (-3)*(e 1) + (1)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4) + (-1)*(e 1) + (2)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 4) + (1)*(e 1) + (1)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4)=0 ∧ (2)*(e 3) + (-1)*(e 1) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 4) + (1)*(e 1) + (-2)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (3)*(e 4) + (1)*(e 1) + (-3)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4) + (1)*(e 1) + (-2)*(e 2) + (1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 4) + (-1)*(e 1) + (-1)*(e 2) + (2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 3)=0 ∧ (2)*(e 4) + (-1)*(e 2) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 3) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 3) + (-1)*(e 1)=0 ∧ (1)*(e 4) + (1)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (3)*(e 4) + (1)*(e 1) + (-2)*(e 2) + (-3)*(e 5)=0 ∧ (1)*(e 3) + (1)*(e 4) + (1)*(e 1) + (-1)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 3) + (1)*(e 1) + (-2)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 2)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-3)*(e 4) + (1)*(e 1) + (-2)*(e 2) + (3)*(e 5)=0 ∧ (1)*(e 3) + (1)*(e 4) + (-1)*(e 1) + (1)*(e 2) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 0) + (-1)*(e 2)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 2)=0 ∧ (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 ∧ (1)*(e 0) + (-1)*(e 2)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 0)=0 ∧ (2)*(e 2) + (-1)*(e 5) + (-1)*(e 4)=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 5) + (1)*(e 4)=0 ∧ (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 5) + (2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 5) + (-3)*(e 4)=0 ∧ (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-2)*(e 0) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (1)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 5) + (-1)*(e 4)=0 ∧ (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 5) + (-1)*(e 4)=0 ∧ (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 ∧ (1)*(e 0) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 5) + (3)*(e 4)=0 ∧ (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 5) + (1)*(e 4)=0 ∧ (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 1) + (-1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (-1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (1)*(e 0) + (-2)*(e 2)=0 ∧ (1)*(e 5) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 5) + (1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 5) + (1)*(e 4)=0 ∧ (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 5) + (2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 5) + (-1)*(e 4)=0 ∧ (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 5) + (-2)*(e 4)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 2) + (-1)*(e 4)=0 ∧ (1)*(e 5) + (-1)*(e 4)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 1)=0 ∧ (1)*(e 2) + (-1)*(e 1)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (2)*(e 0) + (-1)*(e 3) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 2)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(e 4) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-1)*(e 1)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 2)=0 ∧ (2)*(e 1) + (-1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 1)=0 ∧ (2)*(e 2) + (-1)*(e 4) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 4) + (-1)*(e 3)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 1) + (1)*(e 4) + (-2)*(e 3) + (-1)*(e 5)=0 ∧ (1)*(e 2) + (3)*(e 1) + (1)*(e 4) + (-3)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination ((1/3 : ℝ))*(h0) + ((1/3 : ℝ))*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (-1)*(e 1) + (-3)*(e 4) + (2)*(e 3) + (-1)*(e 5)=0 ∧ (3)*(e 2) + (1)*(e 1) + (-3)*(e 4) + (1)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination (3)*(h0) + (-1)*(h1)
    · linear_combination (1)*(h1)
  · change (2)*(e 0) + (-1)*(e 1) + (-1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (2)*(e 0) + (-1)*(e 2) + (-1)*(e 1)=0 ∧ (1)*(e 4) + (-1)*(e 3)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (-1)*(h1)
  · change (3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 1) + (-1)*(e 4) + (-2)*(e 3) + (1)*(e 5)=0 ∧ (1)*(e 2) + (-3)*(e 1) + (1)*(e 4) + (3)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination ((1/3 : ℝ))*(h0) + ((1/3 : ℝ))*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-3)*(e 1) + (1)*(e 4) + (-2)*(e 3) + (3)*(e 5)=0 ∧ (1)*(e 2) + (1)*(e 1) + (-1)*(e 4) + (1)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-3)*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (-2)*(e 3) + (1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (3)*(e 0) + (1)*(e 1) + (-3)*(e 4) + (-2)*(e 3) + (1)*(e 5)=0 ∧ (3)*(e 2) + (-1)*(e 1) + (-3)*(e 4) + (-1)*(e 3) + (2)*(e 5)=0
    constructor
    · linear_combination (3)*(h0) + (1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5)=0 ∧ (1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (3)*(e 1) + (1)*(e 4) + (-2)*(e 3) + (-3)*(e 5)=0 ∧ (1)*(e 2) + (1)*(e 1) + (1)*(e 4) + (-1)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (3)*(h1)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (-2)*(e 4) + (1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 1) + (-1)*(e 5)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-2)*(e 1) + (1)*(e 2)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 2) + (-2)*(e 1)=0 ∧ (1)*(e 3) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (1)*(e 1) + (-2)*(e 2)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(e 2) + (1)*(e 1)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 0) + (-2)*(e 3) + (1)*(e 4)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (1)*(e 4) + (-2)*(e 3)=0 ∧ (1)*(e 1) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (-1)*(e 3)=0 ∧ (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 2) + (1)*(e 4) + (-2)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 3)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 1) + (1)*(e 4) + (-2)*(e 3) + (1)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 1) + (-1)*(e 4) + (-1)*(e 3) + (2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 0) + (1)*(e 3) + (-2)*(e 4)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-2)*(e 4) + (1)*(e 3)=0 ∧ (1)*(e 2) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)
  · change (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 4)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 2) + (-1)*(e 4)=0 ∧ (1)*(e 1) + (1)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h1)
    · linear_combination (1)*(h0)
  · change (1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5)=0 ∧ (1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 0) + (-1)*(e 1) + (-1)*(e 4) + (2)*(e 3) + (-1)*(e 5)=0 ∧ (1)*(e 2) + (-1)*(e 1) + (1)*(e 4) + (1)*(e 3) + (-2)*(e 5)=0
    constructor
    · linear_combination (1)*(h0) + (-1)*(h1)
    · linear_combination (-1)*(h1)
  · change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0 at h
    obtain ⟨h0,h1⟩ := h
    change (1)*(e 2) + (-1)*(e 5)=0 ∧ (1)*(e 4) + (-1)*(e 5)=0
    constructor
    · linear_combination (1)*(h0)
    · linear_combination (1)*(h1)

lemma form_scale (e : Edges) (c : ℝ) (i : Fin 24) (j : Fin 2) :
    form (fun k => c*e k) i j=c*form e i j := by
  fin_cases i <;> fin_cases j
  · change (1)*(c*e 0) + (-1)*(c*e 2)=c*((1)*(e 0) + (-1)*(e 2))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 2)=c*((1)*(e 1) + (-1)*(e 2))
    ring
  · change (2)*(c*e 0) + (-1)*(c*e 3) + (-1)*(c*e 4)=c*((2)*(e 0) + (-1)*(e 3) + (-1)*(e 4))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 2)=c*((1)*(e 1) + (-1)*(e 2))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 2)=c*((1)*(e 0) + (-1)*(e 2))
    ring
  · change (2)*(c*e 1) + (-1)*(c*e 3) + (-1)*(c*e 5)=c*((2)*(e 1) + (-1)*(e 3) + (-1)*(e 5))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 1)=c*((1)*(e 0) + (-1)*(e 1))
    ring
  · change (2)*(c*e 2) + (-1)*(c*e 4) + (-1)*(c*e 5)=c*((2)*(e 2) + (-1)*(e 4) + (-1)*(e 5))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 4)=c*((1)*(e 0) + (-1)*(e 4))
    ring
  · change (1)*(c*e 3) + (-1)*(c*e 4)=c*((1)*(e 3) + (-1)*(e 4))
    ring
  · change (3)*(c*e 0) + (-1)*(c*e 2) + (-3)*(c*e 3) + (2)*(c*e 4) + (-1)*(c*e 5)=c*((3)*(e 0) + (-1)*(e 2) + (-3)*(e 3) + (2)*(e 4) + (-1)*(e 5))
    ring
  · change (3)*(c*e 1) + (1)*(c*e 2) + (-3)*(c*e 3) + (1)*(c*e 4) + (-2)*(c*e 5)=c*((3)*(e 1) + (1)*(e 2) + (-3)*(e 3) + (1)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (1)*(c*e 2) + (1)*(c*e 3) + (-2)*(c*e 4) + (-1)*(c*e 5)=c*((1)*(e 0) + (1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-1)*(e 5))
    ring
  · change (1)*(c*e 1) + (3)*(c*e 2) + (1)*(c*e 3) + (-3)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 1) + (3)*(e 2) + (1)*(e 3) + (-3)*(e 4) + (-2)*(e 5))
    ring
  · change (2)*(c*e 0) + (-1)*(c*e 1) + (-1)*(c*e 2)=c*((2)*(e 0) + (-1)*(e 1) + (-1)*(e 2))
    ring
  · change (1)*(c*e 3) + (-1)*(c*e 4)=c*((1)*(e 3) + (-1)*(e 4))
    ring
  · change (3)*(c*e 0) + (1)*(c*e 2) + (-3)*(c*e 3) + (-2)*(c*e 4) + (1)*(c*e 5)=c*((3)*(e 0) + (1)*(e 2) + (-3)*(e 3) + (-2)*(e 4) + (1)*(e 5))
    ring
  · change (3)*(c*e 1) + (-1)*(c*e 2) + (-3)*(c*e 3) + (-1)*(c*e 4) + (2)*(c*e 5)=c*((3)*(e 1) + (-1)*(e 2) + (-3)*(e 3) + (-1)*(e 4) + (2)*(e 5))
    ring
  · change (1)*(c*e 0) + (3)*(c*e 2) + (1)*(c*e 3) + (-2)*(c*e 4) + (-3)*(c*e 5)=c*((1)*(e 0) + (3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (-3)*(e 5))
    ring
  · change (1)*(c*e 1) + (1)*(c*e 2) + (1)*(c*e 3) + (-1)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 1) + (1)*(e 2) + (1)*(e 3) + (-1)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 4)=c*((1)*(e 0) + (-1)*(e 4))
    ring
  · change (1)*(c*e 1) + (-2)*(c*e 3) + (1)*(c*e 5)=c*((1)*(e 1) + (-2)*(e 3) + (1)*(e 5))
    ring
  · change (1)*(c*e 0) + (1)*(c*e 2) + (-1)*(c*e 3) + (-2)*(c*e 4) + (1)*(c*e 5)=c*((1)*(e 0) + (1)*(e 2) + (-1)*(e 3) + (-2)*(e 4) + (1)*(e 5))
    ring
  · change (1)*(c*e 1) + (-3)*(c*e 2) + (1)*(c*e 3) + (3)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 1) + (-3)*(e 2) + (1)*(e 3) + (3)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (-3)*(c*e 2) + (1)*(c*e 3) + (-2)*(c*e 4) + (3)*(c*e 5)=c*((1)*(e 0) + (-3)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (3)*(e 5))
    ring
  · change (1)*(c*e 1) + (1)*(c*e 2) + (-1)*(c*e 3) + (1)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 1) + (1)*(e 2) + (-1)*(e 3) + (1)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 3)=c*((1)*(e 0) + (-1)*(e 3))
    ring
  · change (1)*(c*e 2) + (-2)*(c*e 4) + (1)*(c*e 5)=c*((1)*(e 2) + (-2)*(e 4) + (1)*(e 5))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 5)=c*((1)*(e 1) + (-1)*(e 5))
    ring
  · change (1)*(c*e 3) + (-1)*(c*e 5)=c*((1)*(e 3) + (-1)*(e 5))
    ring
  · change (1)*(c*e 0) + (-2)*(c*e 1) + (1)*(c*e 2)=c*((1)*(e 0) + (-2)*(e 1) + (1)*(e 2))
    ring
  · change (1)*(c*e 3) + (-1)*(c*e 5)=c*((1)*(e 3) + (-1)*(e 5))
    ring
  · change (1)*(c*e 0) + (1)*(c*e 1) + (-2)*(c*e 2)=c*((1)*(e 0) + (1)*(e 1) + (-2)*(e 2))
    ring
  · change (1)*(c*e 4) + (-1)*(c*e 5)=c*((1)*(e 4) + (-1)*(e 5))
    ring
  · change (1)*(c*e 0) + (-2)*(c*e 3) + (1)*(c*e 4)=c*((1)*(e 0) + (-2)*(e 3) + (1)*(e 4))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 5)=c*((1)*(e 1) + (-1)*(e 5))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 3)=c*((1)*(e 1) + (-1)*(e 3))
    ring
  · change (1)*(c*e 2) + (1)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 2) + (1)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 2) + (-1)*(c*e 3) + (2)*(c*e 4) + (-1)*(c*e 5)=c*((1)*(e 0) + (-1)*(e 2) + (-1)*(e 3) + (2)*(e 4) + (-1)*(e 5))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 2) + (1)*(c*e 3) + (1)*(c*e 4) + (-2)*(c*e 5)=c*((1)*(e 1) + (-1)*(e 2) + (1)*(e 3) + (1)*(e 4) + (-2)*(e 5))
    ring
  · change (1)*(c*e 0) + (1)*(c*e 3) + (-2)*(c*e 4)=c*((1)*(e 0) + (1)*(e 3) + (-2)*(e 4))
    ring
  · change (1)*(c*e 2) + (-1)*(c*e 5)=c*((1)*(e 2) + (-1)*(e 5))
    ring
  · change (1)*(c*e 1) + (1)*(c*e 3) + (-2)*(c*e 5)=c*((1)*(e 1) + (1)*(e 3) + (-2)*(e 5))
    ring
  · change (1)*(c*e 2) + (-1)*(c*e 4)=c*((1)*(e 2) + (-1)*(e 4))
    ring
  · change (1)*(c*e 0) + (-1)*(c*e 2) + (1)*(c*e 3) + (-2)*(c*e 4) + (1)*(c*e 5)=c*((1)*(e 0) + (-1)*(e 2) + (1)*(e 3) + (-2)*(e 4) + (1)*(e 5))
    ring
  · change (1)*(c*e 1) + (-1)*(c*e 2) + (-1)*(c*e 3) + (-1)*(c*e 4) + (2)*(c*e 5)=c*((1)*(e 1) + (-1)*(e 2) + (-1)*(e 3) + (-1)*(e 4) + (2)*(e 5))
    ring
  · change (1)*(c*e 2) + (-1)*(c*e 5)=c*((1)*(e 2) + (-1)*(e 5))
    ring
  · change (1)*(c*e 4) + (-1)*(c*e 5)=c*((1)*(e 4) + (-1)*(e 5))
    ring

lemma star_scale {e : Edges} (h : StarLocus e) (c : ℝ) :
    StarLocus (fun k => c*e k) := by
  obtain ⟨i,h0,h1⟩ := h
  exact ⟨i,by rw [form_scale,h0,mul_zero],by rw [form_scale,h1,mul_zero]⟩

lemma star_move {e : Edges} (h : StarLocus e) (k : Fin 3) : StarLocus (move k e) := by
  obtain ⟨i,hi⟩ := h
  exact ⟨_,onPlane_move e k i hi⟩

lemma star_relabel {e : Edges} (h : StarLocus e) (k : Fin 3) : StarLocus (relabel k e) := by
  obtain ⟨i,hi⟩ := h
  exact ⟨_,onPlane_label e k i hi⟩

lemma star_orbit {e f : Edges} (h : ReggeCircle.Orbit e f) (he : StarLocus e) : StarLocus f := by
  induction h with
  | refl => exact he
  | relabel e k => exact star_relabel he k
  | regge e k => exact star_move he k
  | scale e c => exact star_scale he c
  | trans _ _ h₁ h₂ => exact h₂ (h₁ he)

lemma star_of_equal_radii {e : Edges} (h1 : e 0=e 1) (h2 : e 0=e 2) : StarLocus e := by
  refine ⟨0,?_⟩
  change 1*e 0 + (-1)*e 2=0 ∧ 1*e 1+(-1)*e 2=0
  constructor <;> linarith

theorem heptad_edge_control_not_star :
    ¬StarLocus ![22270,8636,16637,13746,11397,11049] := by
  rintro ⟨i,hi⟩
  fin_cases i
  · change (1)*(22270) + (-1)*(16637)=0 ∧ (1)*(8636) + (-1)*(16637)=0 at hi
    norm_num at hi
  · change (2)*(22270) + (-1)*(13746) + (-1)*(11397)=0 ∧ (1)*(8636) + (-1)*(16637)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(16637)=0 ∧ (2)*(8636) + (-1)*(13746) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(8636)=0 ∧ (2)*(16637) + (-1)*(11397) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(11397)=0 ∧ (1)*(13746) + (-1)*(11397)=0 at hi
    norm_num at hi
  · change (3)*(22270) + (-1)*(16637) + (-3)*(13746) + (2)*(11397) + (-1)*(11049)=0 ∧ (3)*(8636) + (1)*(16637) + (-3)*(13746) + (1)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (1)*(16637) + (1)*(13746) + (-2)*(11397) + (-1)*(11049)=0 ∧ (1)*(8636) + (3)*(16637) + (1)*(13746) + (-3)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (2)*(22270) + (-1)*(8636) + (-1)*(16637)=0 ∧ (1)*(13746) + (-1)*(11397)=0 at hi
    norm_num at hi
  · change (3)*(22270) + (1)*(16637) + (-3)*(13746) + (-2)*(11397) + (1)*(11049)=0 ∧ (3)*(8636) + (-1)*(16637) + (-3)*(13746) + (-1)*(11397) + (2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (3)*(16637) + (1)*(13746) + (-2)*(11397) + (-3)*(11049)=0 ∧ (1)*(8636) + (1)*(16637) + (1)*(13746) + (-1)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(11397)=0 ∧ (1)*(8636) + (-2)*(13746) + (1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (1)*(16637) + (-1)*(13746) + (-2)*(11397) + (1)*(11049)=0 ∧ (1)*(8636) + (-3)*(16637) + (1)*(13746) + (3)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-3)*(16637) + (1)*(13746) + (-2)*(11397) + (3)*(11049)=0 ∧ (1)*(8636) + (1)*(16637) + (-1)*(13746) + (1)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(13746)=0 ∧ (1)*(16637) + (-2)*(11397) + (1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(8636) + (-1)*(11049)=0 ∧ (1)*(13746) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-2)*(8636) + (1)*(16637)=0 ∧ (1)*(13746) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (1)*(8636) + (-2)*(16637)=0 ∧ (1)*(11397) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-2)*(13746) + (1)*(11397)=0 ∧ (1)*(8636) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(8636) + (-1)*(13746)=0 ∧ (1)*(16637) + (1)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(16637) + (-1)*(13746) + (2)*(11397) + (-1)*(11049)=0 ∧ (1)*(8636) + (-1)*(16637) + (1)*(13746) + (1)*(11397) + (-2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (1)*(13746) + (-2)*(11397)=0 ∧ (1)*(16637) + (-1)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(8636) + (1)*(13746) + (-2)*(11049)=0 ∧ (1)*(16637) + (-1)*(11397)=0 at hi
    norm_num at hi
  · change (1)*(22270) + (-1)*(16637) + (1)*(13746) + (-2)*(11397) + (1)*(11049)=0 ∧ (1)*(8636) + (-1)*(16637) + (-1)*(13746) + (-1)*(11397) + (2)*(11049)=0 at hi
    norm_num at hi
  · change (1)*(16637) + (-1)*(11049)=0 ∧ (1)*(11397) + (-1)*(11049)=0 at hi
    norm_num at hi

#print axioms onPlane_move
#print axioms onPlane_label
#print axioms star_orbit
#print axioms star_of_equal_radii
#print axioms heptad_edge_control_not_star
end
end Erdos213.ReggeStar
