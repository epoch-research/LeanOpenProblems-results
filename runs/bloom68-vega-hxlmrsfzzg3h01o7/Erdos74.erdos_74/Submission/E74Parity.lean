import Submission.E74Basic

/-!
# Walk parity and short supports

Parity is computed on the complete edge list, with multiplicities.  All support
constraints concern closed walks, not just cycles.  In particular, no cycle
decomposition is needed for cut telescoping or for the certificate lemmas.
-/

open SimpleGraph
open scoped symmDiff

namespace E74

universe u
variable {V : Type u} [DecidableEq V]
variable {G H : SimpleGraph V} {u v x y : V}

/-! ## Total edge labels -/

section TotalLabels
omit [DecidableEq V]

/-- The recursive sum is a fold over the edge list, retaining multiplicities. -/
theorem walkXor_eq_foldr (a : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor a w = w.edges.foldr (fun e b => a e ^^ b) false := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [ih]

/-- Equal edge lists give equal sums, even in different graphs. -/
theorem walkXor_eq_of_edges_eq (a : Sym2 V → Bool)
    (w : G.Walk u v) (q : H.Walk x y) (h : w.edges = q.edges) :
    walkXor a w = walkXor a q := by
  simp only [walkXor_eq_foldr, h]

/-- Only pointwise agreement on the edges actually traversed is needed. -/
theorem walkXor_congr {a b : Sym2 V → Bool} (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, a e = b e) : walkXor a w = walkXor b w := by
  induction w with
  | nil => rfl
  | @cons u v x huv w ih =>
    simp only [walkXor_cons]
    rw [h s(u, v) (by simp), ih (fun e he => h e (by simp [he]))]

@[simp] theorem walkXor_append (a : Sym2 V → Bool)
    (w : G.Walk u v) (q : G.Walk v x) :
    walkXor a (w.append q) = (walkXor a w ^^ walkXor a q) := by
  induction w with
  | nil => simp
  | cons h w ih => simp [ih]

@[simp] theorem walkXor_reverse (a : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor a w.reverse = walkXor a w := by
  induction w with
  | nil => simp
  | @cons u v x huv w ih =>
    simp [ih, Sym2.eq_swap, Bool.xor_comm]

@[simp] theorem walkXor_copy (a : Sym2 V → Bool) (w : G.Walk u v)
    (hu : u = x) (hv : v = y) : walkXor a (w.copy hu hv) = walkXor a w := by
  subst x y
  rfl

@[simp] theorem walkXor_mapLe (a : Sym2 V → Bool) (hGH : G ≤ H)
    (w : G.Walk u v) : walkXor a (w.mapLe hGH) = walkXor a w :=
  walkXor_eq_of_edges_eq a _ _ (w.edges_mapLe_eq_edges hGH)

@[simp] theorem walkXor_transfer (a : Sym2 V → Bool) (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, e ∈ H.edgeSet) :
    walkXor a (w.transfer H h) = walkXor a w :=
  walkXor_eq_of_edges_eq a _ _ (w.edges_transfer h)

@[simp] theorem walkXor_false (w : G.Walk u v) :
    walkXor (fun _ => false) w = false := by
  induction w <;> simp_all

/-- XOR is linear in the total edge label. -/
theorem walkXor_xor (a b : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor (fun e => a e ^^ b e) w = (walkXor a w ^^ walkXor b w) := by
  induction w with
  | nil => rfl
  | @cons u v x huv w ih =>
    simp only [walkXor_cons, ih]
    cases a s(u, v) <;> cases b s(u, v) <;>
      cases walkXor a w <;> cases walkXor b w <;> rfl

/-- Unequal sums have an edge on which the labels differ. -/
theorem exists_edge_of_walkXor_ne {a b : Sym2 V → Bool} (w : G.Walk u v)
    (h : walkXor a w ≠ walkXor b w) : ∃ e ∈ w.edges, a e ≠ b e := by
  by_contra hn
  apply h
  apply walkXor_congr w
  intro e he
  by_contra hab
  exact hn ⟨e, he, hab⟩

end TotalLabels

/-! ## Membership labels and their differences -/

@[simp] theorem twist_of_mem {S : Finset (Sym2 V)} {e : Sym2 V} (h : e ∈ S) :
    twist S e = false := by
  classical
  simp [twist, h]

@[simp] theorem twist_of_not_mem {S : Finset (Sym2 V)} {e : Sym2 V} (h : e ∉ S) :
    twist S e = true := by
  classical
  simp [twist, h]

@[simp] theorem twist_eq_false_iff {S : Finset (Sym2 V)} {e : Sym2 V} :
    twist S e = false ↔ e ∈ S := by
  classical
  simp [twist]

@[simp] theorem twist_eq_true_iff {S : Finset (Sym2 V)} {e : Sym2 V} :
    twist S e = true ↔ e ∉ S := by
  classical
  simp [twist]

/-- This also applies directly to an unordered pair `s(u, v)`. -/
theorem twist_congr {S T : Finset (Sym2 V)} {e : Sym2 V}
    (h : e ∈ S ↔ e ∈ T) : twist S e = twist T e := by
  classical
  simp only [twist, h]

theorem walkXor_twist_congr {S T : Finset (Sym2 V)} (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, e ∈ S ↔ e ∈ T) :
    walkXor (twist S) w = walkXor (twist T) w :=
  walkXor_congr w (fun e he => twist_congr (h e he))

/-- Complementing both membership labels cancels under XOR. -/
theorem twist_xor_twist (S T : Finset (Sym2 V)) (e : Sym2 V) :
    (twist S e ^^ twist T e) = decide (e ∈ S ∆ T) := by
  classical
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;>
    simp [twist, Finset.mem_symmDiff, hS, hT]

/-- The difference of two twisted sums is the indicator sum of their symmetric difference. -/
theorem walkXor_twist_xor_twist (S T : Finset (Sym2 V)) (w : G.Walk u v) :
    (walkXor (twist S) w ^^ walkXor (twist T) w) =
      walkXor (fun e => decide (e ∈ S ∆ T)) w := by
  rw [← walkXor_xor]
  exact walkXor_congr w (fun e _ => twist_xor_twist S T e)

/-- If nested supports have different sums, a traversed edge lies in the difference. -/
theorem exists_edge_mem_sdiff_of_walkXor_twist_ne {S T : Finset (Sym2 V)}
    (hST : S ⊆ T) (w : G.Walk u v)
    (h : walkXor (twist S) w ≠ walkXor (twist T) w) :
    ∃ e ∈ w.edges, e ∈ T ∧ e ∉ S := by
  obtain ⟨e, he, hne⟩ := exists_edge_of_walkXor_ne w h
  have hnS : e ∉ S := by
    intro hS
    exact hne (by simp [hS, hST hS])
  have hT : e ∈ T := by
    by_contra hnT
    exact hne (by simp [hnS, hnT])
  exact ⟨e, he, hT, hnS⟩

/-! ## Cut telescoping -/

/-- On an actual graph edge, the twisted bad-edge label is the endpoint XOR. -/
theorem twist_badEdges [Fintype V] (p : V → Bool) (huv : G.Adj u v) :
    twist (badEdges G p) s(u, v) = (p u ^^ p v) := by
  classical
  simp only [twist, mem_badEdges, huv, true_and]
  cases p u <;> cases p v <;> rfl

/-- The XOR of an exact endpoint-difference label telescopes along every walk. -/
theorem walkXor_eq_endpoints {a : Sym2 V → Bool} (p : V → Bool)
    (w : G.Walk u v)
    (ha : ∀ x y, G.Adj x y → a s(x, y) = (p x ^^ p y)) :
    walkXor a w = (p u ^^ p v) := by
  induction w with
  | nil => simp
  | @cons u v x huv w ih =>
    rw [walkXor_cons, ha u v huv, ih]
    cases p u <;> cases p v <;> cases p x <;> rfl

theorem walkXor_twist_badEdges [Fintype V] (p : V → Bool) (w : G.Walk u v) :
    walkXor (twist (badEdges G p)) w = (p u ^^ p v) :=
  walkXor_eq_endpoints p w (fun _ _ h => twist_badEdges p h)

@[simp] theorem walkXor_twist_badEdges_closed [Fintype V]
    (p : V → Bool) (w : G.Walk v v) :
    walkXor (twist (badEdges G p)) w = false := by
  simp [walkXor_twist_badEdges]

/-- Every true cut is a short support, at every length scale. -/
theorem shortSupport_badEdges [Fintype V] (G : SimpleGraph V) (L : ℕ) (p : V → Bool) :
    ShortSupport G L (badEdges G p) := by
  constructor
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v => exact ((mem_badEdges G p u v).mp he).1
  · intro v w _
    exact walkXor_twist_badEdges_closed p w

/-! ## Transporting and pruning short supports -/

variable {L M : ℕ} {S T D A : Finset (Sym2 V)}

theorem ShortSupport.mono_length (hS : ShortSupport G L S) (hML : M ≤ L) :
    ShortSupport G M S :=
  ⟨hS.1, fun v w hw => hS.2 v w (hw.trans hML)⟩

/-- Restrict to a smaller graph when all edges of the support survive. -/
theorem ShortSupport.of_le (hS : ShortSupport G L S) (hHG : H ≤ G)
    (hSH : (S : Set (Sym2 V)) ⊆ H.edgeSet) : ShortSupport H L S := by
  refine ⟨hSH, ?_⟩
  intro v w hw
  simpa using hS.2 v (w.mapLe hHG) (by simpa using hw)

theorem ShortSupport.mask (hS : ShortSupport G L S) (Z : Set V)
    (hSZ : (S : Set (Sym2 V)) ⊆ (mask G Z).edgeSet) :
    ShortSupport (mask G Z) L S :=
  hS.of_le (mask_le G Z) hSZ

/-- In particular, deleting vertices away from the support endpoints preserves it. -/
theorem ShortSupport.mask_of_disjoint_ends (hS : ShortSupport G L S) {Z : Set V}
    (hSZ : Disjoint (ends S : Set V) Z) : ShortSupport (E74.mask G Z) L S := by
  apply hS.mask Z
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    change G.Adj u v ∧ u ∉ Z ∧ v ∉ Z
    refine ⟨hS.1 he, ?_, ?_⟩
    · exact fun hu => Set.disjoint_left.mp hSZ
        (mem_ends.mpr ⟨s(u, v), he, Sym2.mem_mk_left u v⟩) hu
    · exact fun hv => Set.disjoint_left.mp hSZ
        (mem_ends.mpr ⟨s(u, v), he, Sym2.mem_mk_right u v⟩) hv

/-- A replacement support is valid when all short closed-walk sums are unchanged. -/
theorem ShortSupport.congr (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hxor : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (twist T) w = walkXor (twist S) w) : ShortSupport G L T :=
  ⟨hT, fun v w hw => (hxor v w hw).trans (hS.2 v w hw)⟩

/-- Pointwise agreement is required only on the edges of short closed walks. -/
theorem ShortSupport.congr_edges (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hmem : ∀ v (w : G.Walk v v), w.length ≤ L →
      ∀ e ∈ w.edges, e ∈ T ↔ e ∈ S) : ShortSupport G L T :=
  hS.congr hT (fun v w hw => walkXor_twist_congr w (hmem v w hw))

/-- Pruning any set is allowed if it leaves every short closed-walk sum unchanged. -/
theorem ShortSupport.sdiff (hS : ShortSupport G L S) (A : Finset (Sym2 V))
    (hxor : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (twist (S \ A)) w = walkXor (twist S) w) :
    ShortSupport G L (S \ A) :=
  hS.congr (fun _ he => hS.1 (Finset.sdiff_subset he)) hxor

/-- A parity formulation of replacement: the symmetric-difference indicator sums to zero. -/
theorem ShortSupport.of_symmDiff (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hzero : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (fun e => decide (e ∈ T ∆ S)) w = false) : ShortSupport G L T := by
  apply hS.congr hT
  intro v w hw
  have h := (walkXor_twist_xor_twist T S w).trans (hzero v w hw)
  cases hT' : walkXor (twist T) w <;> cases hS' : walkXor (twist S) w <;>
    simp_all

/-! ## Minimal cardinality -/

theorem exists_shortSupport [Finite V] (G : SimpleGraph V) (L : ℕ) :
    ∃ S, ShortSupport G L S := by
  letI := Fintype.ofFinite V
  exact ⟨badEdges G (fun _ => false), shortSupport_badEdges G L (fun _ => false)⟩

/-- A minimum-cardinality support exists, by minimizing its natural-number cardinality. -/
theorem exists_minimalSupport [Finite V] (G : SimpleGraph V) (L : ℕ) :
    ∃ S, MinimalSupport G L S := by
  classical
  have hex : ∃ n : ℕ, ∃ S : Finset (Sym2 V), ShortSupport G L S ∧ S.card = n := by
    obtain ⟨S, hS⟩ := exists_shortSupport G L
    exact ⟨S.card, S, hS, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  rw [hcard]
  exact Nat.find_min' hex ⟨T, hT, rfl⟩

theorem MinimalSupport.card_le (hS : MinimalSupport G L S) (hT : ShortSupport G L T) :
    S.card ≤ T.card := hS.2 T hT

/-- A minimum short support is no larger than the bad-edge support of any cut. -/
theorem MinimalSupport.card_le_badEdges [Fintype V] (hS : MinimalSupport G L S)
    (p : V → Bool) : S.card ≤ (badEdges G p).card :=
  hS.card_le (shortSupport_badEdges G L p)

/-! ## Certificate-facing witnesses -/

/-- Any violated short constraint for a subset exposes a missing support edge. -/
theorem ShortSupport.exists_edge_not_mem (hS : ShortSupport G L S) (hD : D ⊆ S)
    (w : G.Walk v v) (hw : w.length ≤ L) (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ S ∧ e ∉ D := by
  apply exists_edge_mem_sdiff_of_walkXor_twist_ne hD w
  simpa only [hS.2 v w hw] using hxor

/-- For a true cut the witness theorem needs no length bound at all. -/
theorem exists_badEdge_not_mem_of_walkXor_ne_false [Fintype V]
    (p : V → Bool) (hD : D ⊆ badEdges G p) (w : G.Walk v v)
    (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ badEdges G p ∧ e ∉ D := by
  apply exists_edge_mem_sdiff_of_walkXor_twist_ne hD w
  simpa only [walkXor_twist_badEdges_closed] using hxor

/-- The bounded form used by short-walk certificates. -/
theorem exists_badEdge_not_mem_of_short_walkXor_ne_false [Fintype V]
    (p : V → Bool) (hD : D ⊆ badEdges G p) (w : G.Walk v v)
    (hw : w.length ≤ L) (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ badEdges G p ∧ e ∉ D :=
  (shortSupport_badEdges G L p).exists_edge_not_mem hD w hw hxor

end E74
