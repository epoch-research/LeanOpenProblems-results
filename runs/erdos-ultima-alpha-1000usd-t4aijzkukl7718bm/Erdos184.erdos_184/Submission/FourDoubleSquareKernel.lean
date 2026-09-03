import Submission.FourDoubleSquareData

/-! Local endpoint lookup and rejection for the four-color double square. -/

namespace Erdos184Work.FourDoubleSquareKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option Elab.async false

def rowPlace : Fin 4 → Fin 4 → W :=
  ![![4,5,6,7],![12,13,14,15],![4,5,12,13],![6,7,14,15]]

def rowWord (k : ℕ) : Fin 4 → Fin 4 :=
  if k = 0 then ![0,1,2,3] else if k = 1 then ![0,1,3,2] else ![0,2,1,3]

def localKey (i : Fin 4) (q : Marked.Order (arity counts i)) : ℕ :=
  let v := (SmallOrderNormalization.normalized (arity counts i) q).vertex
  if (v 1).val = 2 then 2 else if (v 2).val = 2 then 0 else 1

def localWord (i : Fin 4) (q : Marked.Order (arity counts i))
    (j : Fin (arity counts i+2)) : W :=
  fastPlace counts marker_bound i ((SmallOrderNormalization.normalized (arity counts i) q).vertex j)

lemma local_word : ∀ (i : Fin 4) (q : Marked.Order (arity counts i))
    (j : Fin (arity counts i+2)), localWord i q j =
    rowPlace i (rowWord (localKey i q) ⟨j.val,by have h := j.isLt; have ha := arity_two i; omega⟩) := by
  decide +kernel


def pos (e : E) : Fin 4 := ⟨e.val % 4, Nat.mod_lt _ (by decide)⟩

lemma flat_source (o : Orders) (e : E) :
    FlatCanonicalKernel.src counts marker_bound o e =
    rowPlace (color e) (rowWord (localIndex (color e) o) (pos e)) := by
  fin_cases e <;> exact local_word _ (o _) _

lemma flat_target (o : Orders) (e : E) :
    FlatCanonicalKernel.dst counts marker_bound o e =
    rowPlace (color e) (rowWord (localIndex (color e) o) (pos e+1)) := by
  fin_cases e <;> exact local_word _ (o _) _

def digit (k : ℕ) (i : Fin 4) : ℕ :=
  if i = 0 then k / 27 else if i = 1 then k / 9 % 3 else if i = 2 then k / 3 % 3 else k % 3

lemma source_table_row : ∀ (k : Fin 81) (e : E), srcTable k.val e =
    rowPlace (color e) (rowWord (digit k.val (color e)) (pos e)) := by decide +kernel

lemma target_table_row : ∀ (k : Fin 81) (e : E), dstTable k.val e =
    rowPlace (color e) (rowWord (digit k.val (color e)) (pos e+1)) := by decide +kernel

lemma digit_key (o : Orders) (i : Fin 4) : digit (key o) i = localIndex i o := by
  have h (i : Fin 4) : localIndex i o ≤ 2 := by
    dsimp only [localIndex]
    split_ifs <;> omega
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  fin_cases i
  · change key o / 27 = localIndex 0 o
    unfold key
    omega
  · change key o / 9 % 3 = localIndex 1 o
    unfold key
    omega
  · change key o / 3 % 3 = localIndex 2 o
    unfold key
    omega
  · change key o % 3 = localIndex 3 o
    unfold key
    omega

lemma source_table (o : Orders) (e : E) :
    FlatCanonicalKernel.src counts marker_bound o e = srcTable (key o) e := by
  rw [source_table_row ⟨key o,key_lt o⟩, digit_key, flat_source]

lemma target_table (o : Orders) (e : E) :
    FlatCanonicalKernel.dst counts marker_bound o e = dstTable (key o) e := by
  rw [target_table_row ⟨key o,key_lt o⟩, digit_key, flat_target]

lemma color_table : ∀ e : E, FlatCanonicalKernel.color counts e = color e := by decide +kernel

def witness (o : Orders) : RejectionData E W (Fin 4) := lookup (key o)
lemma witness_valid (o : Orders) :
    (witness o).Valid (FlatCanonicalKernel.src counts marker_bound o)
      (FlatCanonicalKernel.dst counts marker_bound o) (FlatCanonicalKernel.color counts) := by
  have h := table_valid ⟨key o,key_lt o⟩
  have hs := funext (source_table o)
  have ht := funext (target_table o)
  have hc := funext color_table
  rw [← hs,← ht,← hc] at h
  exact h

lemma not_restrictions (o : Orders) :
    ¬ CanonicalThreeReduction.Restrictions counts marker_bound o :=
  FlatCanonicalKernel.rejects counts marker_bound o (witness_valid o)

#print axioms witness_valid
#print axioms not_restrictions
end Erdos184Work.FourDoubleSquareKernel
