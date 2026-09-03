import Submission.SignatureGridFamily

/-! An obstruction to UNWEIGHTED injective counting of maximal minimal-core
 events. The underlying arithmetic family is partial, not a covering witness. -/
namespace Erdos7SignatureGridCores
open scoped BigOperators
open Finset Erdos7SignatureGridPatterns Erdos7SignatureGridFamily
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

abbrev Vertex := Coord → Fin 2
abbrev Sample := Coord → Fin 2 → ℤ

def pairIndex (r : Fin 2) (v : Fin 7) : Fin 14 := ⟨7 * r.val + v.val, by omega⟩

lemma pairIndex_injective (r s : Fin 2) (v w : Fin 7) :
    pairIndex r v = pairIndex s w ↔ r = s ∧ v = w := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    dsimp [pairIndex] at hval
    have hr := r.isLt
    have hs := s.isLt
    have hv := v.isLt
    have hw := w.isLt
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

def corner (h : Choice) (u : Vertex) : Grid := fun i => pairIndex (u i) (h i (u i))
def sample (h : Choice) : Sample := fun i r => value i (pairIndex r (h i r))

lemma corner_injective (h : Choice) : Function.Injective (corner h) := by
  intro u v hv
  funext i
  exact ((pairIndex_injective _ _ _ _).mp (congrFun hv i)).1

noncomputable def core (h : Choice) : Finset Pattern :=
  univ.image (fun u => gridPattern (corner h u))

lemma core_card (h : Choice) : (core h).card = 8 := by
  classical
  rw [core, card_image_of_injective _
    (show Function.Injective (fun u => gridPattern (corner h u)) from
      gridPattern_injective.comp (corner_injective h))]
  simp [Vertex, Fintype.card_fun]

/-- An actual event, including both coverage and private vertices. -/
def CoreEvent (s : Finset Pattern) (z : Sample) : Prop :=
  (∀ u : Vertex, ∃ d ∈ s, Hits (fun i => z i (u i)) d) ∧
  ∀ d ∈ s, ∃ u : Vertex, ∀ k ∈ s, Hits (fun i => z i (u i)) k ↔ k = d

lemma isolated_hits (h : Choice) (u : Vertex) (d : Pattern) :
    Hits (fun i => sample h i (u i)) d ↔ d = gridPattern (corner h u) :=
  grid_hits_iff (corner h u) d

/-- At the designated sample, exactly the eight corner boxes are active. -/
theorem isolated_event (h : Choice) (s : Finset Pattern) :
    CoreEvent s (sample h) ↔ s = core h := by
  classical
  constructor
  · intro he
    apply subset_antisymm
    · intro d hd
      obtain ⟨u, hu⟩ := he.2 d hd
      have hh := (isolated_hits h u d).mp ((hu d hd).mpr rfl)
      exact mem_image.mpr ⟨u, mem_univ _, hh.symm⟩
    · intro d hd
      obtain ⟨u, _, rfl⟩ := mem_image.mp hd
      obtain ⟨k, hk, hu⟩ := he.1 u
      exact ((isolated_hits h u k).mp hu) ▸ hk
  · rintro rfl
    constructor
    · intro u
      refine ⟨gridPattern (corner h u), mem_image.mpr ⟨u, mem_univ _, rfl⟩, ?_⟩
      exact (isolated_hits h u _).mpr rfl
    · intro d hd
      obtain ⟨u, _, rfl⟩ := mem_image.mp hd
      exact ⟨u, fun k _ => isolated_hits h u k⟩

lemma core_injective : Function.Injective core := by
  classical
  intro h k he
  funext i r
  let u : Vertex := fun _ => r
  have hu : gridPattern (corner h u) ∈ core k := by
    rw [← he]
    exact mem_image.mpr ⟨u, mem_univ _, rfl⟩
  obtain ⟨v, _, hv⟩ := mem_image.mp hu
  have hi := congrFun (gridPattern_injective hv) i
  obtain ⟨hr, hh⟩ := (pairIndex_injective _ _ _ _).mp hi
  change v i = r at hr
  change k i (v i) = h i r at hh
  rw [hr] at hh
  exact hh.symm

noncomputable def event (s : Finset Pattern) : Set Sample := {z | CoreEvent s z}

lemma event_core_injective : Function.Injective (fun h => event (core h)) := by
  intro h k he
  change event (core h) = event (core k) at he
  apply core_injective
  have hh : sample h ∈ event (core k) := by
    rw [← he]
    exact (isolated_event h _).mpr rfl
  exact ((isolated_event h _).mp hh).symm

/-- Maximality is among all actual minimal-core events in this family. -/
theorem core_event_maximal (h : Choice) (s : Finset Pattern)
    (hs : event (core h) ⊆ event s) : s = core h := by
  apply (isolated_event h s).mp
  exact hs ((isolated_event h _).mpr rfl)

/-- These maximal events cannot be charged injectively to original patterns. -/
theorem no_injective_core_charge : ¬ ∃ f : Choice → Pattern, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hb := Fintype.card_le_of_injective f hf
  exact (not_le_of_gt choice_count_gt_patterns) hb

/-- The witnesses lie in different nonzero first-digit branches and avoid all
pure comb constraints. Thus restriction to that natural sampling domain does
not remove the counting obstruction. -/
def Admissible (z : Sample) : Prop :=
  (∀ i r, ¬ (prime i : ℤ) ∣ z i r) ∧
  (∀ i r t, (prime i : ℤ) ∣ z i r - z i t → r = t) ∧
  ∀ i r e, 0 < e → ¬ (prime i : ℤ) ^ e ∣
    z i r - Erdos7PrimePowerCombFamily.exitValue (prime i) e 1

lemma branch_checks :
    (∀ i : Coord, ∀ r : Fin 2, ∀ v : Fin 7,
      ¬ (prime i : ℤ) ∣ value i (pairIndex r v)) ∧
    (∀ i : Coord, ∀ r t : Fin 2, ∀ v w : Fin 7,
      (prime i : ℤ) ∣ value i (pairIndex r v) - value i (pairIndex t w) → r = t) := by
  decide +kernel

lemma sample_admissible (h : Choice) : Admissible (sample h) := by
  refine ⟨fun i r => branch_checks.1 i r _, ?_, ?_⟩
  · intro i r t ht
    exact branch_checks.2 i r t _ _ ht
  · intro i r e he
    exact value_avoids_pure i _ e he

noncomputable def admissibleEvent (s : Finset Pattern) : Set {z : Sample // Admissible z} :=
  {z | CoreEvent s z.val}

lemma admissible_event_core_injective :
    Function.Injective (fun h => admissibleEvent (core h)) := by
  intro h k he
  change admissibleEvent (core h) = admissibleEvent (core k) at he
  apply core_injective
  have hh : (⟨sample h, sample_admissible h⟩ : {z : Sample // Admissible z}) ∈
      admissibleEvent (core k) := by
    rw [← he]
    exact (isolated_event h _).mpr rfl
  exact ((isolated_event h _).mp hh).symm

lemma admissible_core_event_maximal (h : Choice) (s : Finset Pattern)
    (hs : admissibleEvent (core h) ⊆ admissibleEvent s) : s = core h := by
  apply (isolated_event h s).mp
  exact hs (show (⟨sample h, sample_admissible h⟩ : {z : Sample // Admissible z}) ∈
    admissibleEvent (core h) from (isolated_event h _).mpr rfl)

#print axioms sample_admissible
#print axioms admissible_event_core_injective
#print axioms admissible_core_event_maximal
#print axioms isolated_event
#print axioms event_core_injective
#print axioms core_event_maximal
#print axioms no_injective_core_charge
end Erdos7SignatureGridCores
