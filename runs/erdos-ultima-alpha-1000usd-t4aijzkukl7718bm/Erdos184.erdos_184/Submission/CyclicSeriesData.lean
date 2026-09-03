import Submission.SeriesCertificateAssembly

/-! Computable series contraction of an indexed cycle to a selected set of
markers. The bounded validity checks cover every marker subset on cycles of
length two through six, not just a list of chosen word layouts. -/
namespace Erdos184Work.LabelKernel.CyclicSeries
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {n : ℕ}

def kept (s : Finset (Fin (n+2))) : List (Fin (n+2)) :=
  (List.finRange (n+2)).filter (fun j => decide (j ∈ s))

lemma kept_sorted (s : Finset (Fin (n+2))) : (kept s).SortedLT := by
  apply List.sortedLT_iff_pairwise.mpr
  exact List.Pairwise.filter _ (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange _))

lemma kept_toFinset (s : Finset (Fin (n+2))) : (kept s).toFinset = s := by
  ext j
  simp [kept]

lemma kept_length (s : Finset (Fin (n+2))) : (kept s).length = s.card := by
  rw [← List.toFinset_card_of_nodup (kept_sorted s).nodup,kept_toFinset]

def arity (s : Finset (Fin (n+2))) : ℕ := s.card - 2

lemma arity_add (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) : arity s + 2 = s.card :=
  Nat.sub_add_cancel hs

def vertex (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) (j : Fin (arity s+2)) : Fin (n+2) :=
  (kept s).get ⟨j.val,by rw [kept_length]; have h := j.isLt; have ha := arity_add s hs; omega⟩

lemma vertex_mem (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) (j : Fin (arity s+2)) :
    vertex s hs j ∈ s := by
  have h := (kept s).get_mem ⟨j.val,by rw [kept_length]; have h := j.isLt; have ha := arity_add s hs; omega⟩
  exact of_decide_eq_true (List.mem_filter.mp h).2

lemma vertex_injective (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) :
    Function.Injective (vertex s hs) := by
  apply StrictMono.injective
  intro i j hij
  exact (kept_sorted s).strictMono_get hij

lemma vertex_surjective_on (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card)
    (j : Fin (n+2)) (hj : j ∈ s) : ∃ e, vertex s hs e = j := by
  have hm : j ∈ kept s := by simp [kept,hj]
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  refine ⟨⟨i.val,?_⟩,hi⟩
  have h := i.isLt
  have hl := kept_length s
  have ha := arity_add s hs
  omega

def prefixCount (s : Finset (Fin (n+2))) (j : Fin (n+2)) : ℕ :=
  (s.filter (fun k => k ≤ j)).card

def fiber (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) (j : Fin (n+2)) : Fin (arity s+2) :=
  ⟨if prefixCount s j = 0 then s.card-1 else prefixCount s j-1, by
    have ha := arity_add s hs
    have hb : prefixCount s j ≤ s.card := Finset.card_filter_le _ _
    split_ifs <;> omega⟩

def data (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) :
    SeriesData (Fin (arity s+2)) (Fin (n+2)) (Fin (arity s+2)) (Fin (n+2)) where
  fiber := fiber s hs
  representative := vertex s hs
  vertex := vertex s hs
  rank j := (j - vertex s hs (fiber s hs j)).val
  parent j := j-1
  link := id

def Valid (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) : Prop :=
  (data s hs).Valid id (fun j => j+1) id (fun j => j+1)

instance (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) : Decidable (Valid s hs) := by
  unfold Valid
  infer_instance

lemma valid0 : ∀ (s : Finset (Fin 2)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel
lemma valid1 : ∀ (s : Finset (Fin 3)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel
lemma valid2 : ∀ (s : Finset (Fin 4)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel
lemma valid3 : ∀ (s : Finset (Fin 5)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel
lemma valid4 : ∀ (s : Finset (Fin 6)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel

lemma valid {n : ℕ} (hn : n ≤ 4) (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card) : Valid s hs := by
  interval_cases n
  · exact valid0 s hs
  · exact valid1 s hs
  · exact valid2 s hs
  · exact valid3 s hs
  · exact valid4 s hs

lemma representative_of_mem (s : Finset (Fin (n+2))) (hs : 2 ≤ s.card)
    (hv : Valid s hs) (j : Fin (n+2)) (hj : j ∈ s) :
    j = (data s hs).representative ((data s hs).fiber j) := by
  obtain ⟨e,rfl⟩ := vertex_surjective_on s hs j hj
  have h := hv.1 e
  exact (congrArg (vertex s hs) h).symm

#print axioms valid
end Erdos184Work.LabelKernel.CyclicSeries
