import Submission.IntervalTwoSidedWord

/-! Exact propagation of one additional uniform lower window bound. These results
concern integer cumulative functions, not realizability by prime residue classes.
Consistency is explicit: an admissible cumulative function supplies lower bounds
for each integer infimum. -/
namespace Erdos970.WindowConstraintClosure

/-- Translation-invariant upper increment constraints. -/
def Admissible (d F : ℤ → ℤ) : Prop :=
  ∀ a z, F (a + z) - F a ≤ d z

def LowerBlock (F : ℤ → ℤ) (g b : ℤ) : Prop :=
  ∀ a, b ≤ F (a + g) - F a

/-- A normalized subadditive signed distance. Negative distances encode lower
bounds on positively oriented windows. -/
structure IsDistance (d : ℤ → ℤ) : Prop where
  zero : d 0 = 0
  subadd : ∀ x y, d (x + y) ≤ d x + d y

lemma IsDistance.admissible {d : ℤ → ℤ} (hd : IsDistance d) : Admissible d d := by
  intro a z
  have := hd.subadd a z
  omega

lemma LowerBlock.iterate {F : ℤ → ℤ} {g b : ℤ}
    (h : LowerBlock F g b) (a : ℤ) (t : ℕ) :
    (t : ℤ) * b ≤ F (a + (t : ℤ) * g) - F a := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hh := h (a + (t : ℤ) * g)
    push_cast
    have he : a + ((t : ℤ) + 1) * g = a + (t : ℤ) * g + g := by ring
    rw [he]
    nlinarith

noncomputable def addLower (d : ℤ → ℤ) (g b z : ℤ) : ℤ :=
  sInf (Set.range fun t : ℕ => d (z + (t : ℤ) * g) - (t : ℤ) * b)

lemma candidates_nonempty (d : ℤ → ℤ) (g b z : ℤ) :
    (Set.range fun t : ℕ => d (z + (t : ℤ) * g) - (t : ℤ) * b).Nonempty :=
  Set.range_nonempty _

lemma candidate_lower {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) (a z : ℤ) (t : ℕ) :
    F (a + z) - F a ≤ d (z + (t : ℤ) * g) - (t : ℤ) * b := by
  have h₁ := hF a (z + (t : ℤ) * g)
  have h₂ := hB.iterate (a + z) t
  rw [add_assoc] at h₂
  omega

lemma candidates_bddBelow {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) (z : ℤ) :
    BddBelow (Set.range fun t : ℕ => d (z + (t : ℤ) * g) - (t : ℤ) * b) := by
  refine ⟨F z - F 0, ?_⟩
  rintro _ ⟨t, rfl⟩
  simpa using candidate_lower hF hB 0 z t

lemma addLower_attained {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) (z : ℤ) :
    ∃ t : ℕ, addLower d g b z = d (z + (t : ℤ) * g) - (t : ℤ) * b := by
  have hh := Int.csInf_mem (candidates_nonempty d g b z) (candidates_bddBelow hF hB z)
  obtain ⟨t, ht⟩ := hh
  exact ⟨t, ht.symm⟩

lemma addLower_le_candidate {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) (z : ℤ) (t : ℕ) :
    addLower d g b z ≤ d (z + (t : ℤ) * g) - (t : ℤ) * b :=
  csInf_le (candidates_bddBelow hF hB z) (Set.mem_range_self t)

lemma admissible_addLower {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) : Admissible (addLower d g b) F := by
  intro a z
  obtain ⟨t, ht⟩ := addLower_attained hF hB z
  rw [ht]
  exact candidate_lower hF hB a z t

lemma addLower_le {d F : ℤ → ℤ} {g b : ℤ}
    (hF : Admissible d F) (hB : LowerBlock F g b) (z : ℤ) :
    addLower d g b z ≤ d z := by
  simpa using addLower_le_candidate hF hB z 0

lemma addLower_neg_block {d F : ℤ → ℤ} {g b : ℤ}
    (hd : IsDistance d) (hF : Admissible d F) (hB : LowerBlock F g b) :
    addLower d g b (-g) ≤ -b := by
  simpa [hd.zero] using addLower_le_candidate hF hB (-g) 1

theorem IsDistance.addLower {d F : ℤ → ℤ} {g b : ℤ}
    (hd : IsDistance d) (hF : Admissible d F) (hB : LowerBlock F g b) :
    IsDistance (addLower d g b) := by
  constructor
  · have h₁ := admissible_addLower hF hB 0 0
    have h₂ := addLower_le hF hB 0
    rw [hd.zero] at h₂
    simp only [add_zero, sub_self] at h₁
    omega
  · intro x y
    obtain ⟨s, hs⟩ := addLower_attained hF hB x
    obtain ⟨t, ht⟩ := addLower_attained hF hB y
    have h₁ := addLower_le_candidate hF hB (x + y) (s + t)
    have h₂ := hd.subadd (x + (s : ℤ) * g) (y + (t : ℤ) * g)
    have he : x + y + ((s + t : ℕ) : ℤ) * g =
        (x + (s : ℤ) * g) + (y + (t : ℤ) * g) := by push_cast; ring
    rw [he] at h₁
    rw [hs, ht]
    push_cast at h₁
    nlinarith

lemma IsDistance.lowerBlock {d : ℤ → ℤ} {g b : ℤ}
    (hd : IsDistance d) (h : d (-g) ≤ -b) : LowerBlock d g b := by
  intro a
  have hh := hd.subadd (a + g) (-g)
  simp only [add_neg_cancel_right] at hh
  omega

/-- The closure is the greatest normalized subadditive minorant satisfying the
new lower bound. No finite-domain truncation is implicit in this statement. -/
theorem addLower_greatest {d e : ℤ → ℤ} {g b : ℤ}
    (he : IsDistance e) (hle : ∀ z, e z ≤ d z) (hB : e (-g) ≤ -b) (z : ℤ) :
    e z ≤ addLower d g b z := by
  have hE : Admissible d e := fun a z => (he.admissible a z).trans (hle z)
  have hh := admissible_addLower hE (he.lowerBlock hB) 0 z
  simpa only [zero_add, he.zero, sub_zero] using hh

/-- An already implied lower bound leaves the exact closure unchanged. -/
theorem addLower_eq_self {d : ℤ → ℤ} {g b : ℤ}
    (hd : IsDistance d) (hB : d (-g) ≤ -b) : addLower d g b = d := by
  funext z
  exact le_antisymm (addLower_le hd.admissible (hd.lowerBlock hB) z)
    (addLower_greatest hd (fun _ => le_rfl) hB z)

/-- Exact closures commute, provided one cumulative function satisfies both new
bounds. This does not assert order-independence of a finite truncated update. -/
theorem addLower_comm {d F : ℤ → ℤ} {g b h c : ℤ}
    (hd : IsDistance d) (hF : Admissible d F)
    (hB : LowerBlock F g b) (hC : LowerBlock F h c) :
    addLower (addLower d g b) h c = addLower (addLower d h c) g b := by
  have hFB := admissible_addLower hF hB
  have hFC := admissible_addLower hF hC
  have hDB := hd.addLower hF hB
  have hDC := hd.addLower hF hC
  have hDBC := hDB.addLower hFB hC
  have hDCB := hDC.addLower hFC hB
  have hleBC (z : ℤ) : addLower (addLower d g b) h c z ≤ d z :=
    (addLower_le hFB hC z).trans (addLower_le hF hB z)
  have hleCB (z : ℤ) : addLower (addLower d h c) g b z ≤ d z :=
    (addLower_le hFC hB z).trans (addLower_le hF hC z)
  have hBCB : addLower (addLower d g b) h c (-g) ≤ -b :=
    (addLower_le hFB hC (-g)).trans (addLower_neg_block hd hF hB)
  have hCBC : addLower (addLower d h c) g b (-h) ≤ -c :=
    (addLower_le hFC hB (-h)).trans (addLower_neg_block hd hF hC)
  funext z
  apply le_antisymm
  · apply addLower_greatest hDBC ?_ hBCB z
    intro x
    exact addLower_greatest hDBC hleBC (addLower_neg_block hDB hFB hC) x
  · apply addLower_greatest hDCB ?_ hCBC z
    intro x
    exact addLower_greatest hDCB hleCB (addLower_neg_block hDC hFC hB) x

#print axioms IsDistance.addLower
#print axioms addLower_greatest
#print axioms addLower_comm
end Erdos970.WindowConstraintClosure
