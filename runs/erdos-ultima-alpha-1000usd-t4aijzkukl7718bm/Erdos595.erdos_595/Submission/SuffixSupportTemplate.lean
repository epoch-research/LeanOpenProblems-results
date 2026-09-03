import Submission.Work

/-!
A finite graph can be encoded by suffix-row ultrafilters. Every finite
family of rows has a common INDEPENDENT original support, but every set
supporting ALL rows contains an induced copy of the finite graph. This
is an auxiliary support construction, not a settlement of Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work
set_option maxHeartbeats 1500000

namespace Erdos595SuffixSupportTemplate

noncomputable def U : Ultrafilter ℕ := Filter.hyperfilter ℕ

lemma tail (n : ℕ) : {m : ℕ | n < m} ∈ U :=
  Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)

def snocVec {n : ℕ} (x : Fin n → ℕ) (a : ℕ) : Fin (n+1) → ℕ := Fin.snoc x a

@[simp] lemma snocVec_last {n : ℕ} (x : Fin n → ℕ) (a : ℕ) :
    snocVec x a (Fin.last n) = a := by simp [snocVec]

@[simp] lemma snocVec_castSucc {n : ℕ} (x : Fin n → ℕ) (a : ℕ) (i : Fin n) :
    snocVec x a i.castSucc = x i := by simp [snocVec]

noncomputable def productU : (n : ℕ) → Ultrafilter (Fin n → ℕ)
  | 0 => pure (Fin.elim0)
  | n+1 => U.bind (fun a => Ultrafilter.map (fun x : Fin n → ℕ => snocVec x a) (productU n))

lemma mem_productU (n : ℕ) (S : Set (Fin (n+1) → ℕ)) :
    S ∈ productU (n+1) ↔ {a | {x | snocVec x a ∈ S} ∈ productU n} ∈ U := by
  change S ∈ Filter.bind (U : Filter ℕ)
    (fun a => (Ultrafilter.map (fun x : Fin n → ℕ => snocVec x a) (productU n)).toFilter) ↔ _
  rw [Filter.mem_bind']
  rfl

def restrictVec {k n : ℕ} (h : k ≤ n) (x : Fin n → ℕ) : Fin k → ℕ :=
  fun i => x (i.castLE h)

lemma prefix_snoc {k n : ℕ} (h : k ≤ n) (x : Fin n → ℕ) (a : ℕ) :
    restrictVec (h.trans (Nat.le_succ n)) (snocVec x a) = restrictVec h x := by
  funext i
  change snocVec x a (i.castLE (h.trans (Nat.le_succ n))) = x (i.castLE h)
  have he : i.castLE (h.trans (Nat.le_succ n)) = (i.castLE h).castSucc := rfl
  rw [he,snocVec_castSucc]

lemma prefix_mem {k n : ℕ} (h : k ≤ n) (S : Set (Fin k → ℕ)) :
    (restrictVec h) ⁻¹' S ∈ productU n ↔ S ∈ productU k := by
  induction n,h using Nat.le_induction with
  | base =>
    have he : restrictVec (le_refl k) = (id : (Fin k → ℕ) → (Fin k → ℕ)) := rfl
    rw [he,Set.preimage_id]
  | succ n h ih =>
    rw [mem_productU]
    have he : {a : ℕ | {x : Fin n → ℕ | snocVec x a ∈ restrictVec (h.trans (Nat.le_succ n)) ⁻¹' S}
        ∈ productU n} = {a : ℕ | (restrictVec h) ⁻¹' S ∈ productU n} := by
      ext a
      change ({x : Fin n → ℕ | snocVec x a ∈ restrictVec (h.trans (Nat.le_succ n)) ⁻¹' S}
        ∈ productU n) ↔ _
      have hx : {x : Fin n → ℕ | snocVec x a ∈ restrictVec (h.trans (Nat.le_succ n)) ⁻¹' S} =
          restrictVec h ⁻¹' S := by
        ext x
        change restrictVec (h.trans (Nat.le_succ n)) (snocVec x a) ∈ S ↔ restrictVec h x ∈ S
        rw [prefix_snoc]
      rw [hx]
      rfl
    rw [he]
    change (∀ᶠ a in (U : Filter ℕ), restrictVec h ⁻¹' S ∈ productU n) ↔ S ∈ productU k
    simpa only [Filter.eventually_const] using ih

lemma all_coords_gt (n M : ℕ) : {x : Fin n → ℕ | ∀ i, M < x i} ∈ productU n := by
  induction n with
  | zero =>
    rw [productU,Ultrafilter.mem_pure]
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    rw [mem_productU]
    apply Filter.mem_of_superset (tail M)
    intro a ha
    apply Filter.mem_of_superset ih
    intro x hx i
    induction i using Fin.lastCases with
    | last => simpa using ha
    | cast i => simpa using hx i

abbrev Vertex (k : ℕ) := (i : Fin k) × (Fin (i.val+1) → ℕ)

instance (k : ℕ) : Countable (Vertex k) := inferInstanceAs (Countable ((i : Fin k) × (Fin (i.val+1) → ℕ)))

def row {k : ℕ} (x : Vertex k) : ℕ := x.2 (Fin.last x.1.val)

def Align {k : ℕ} (x y : Vertex k) : Prop :=
  ∃ h : x.1.val < y.1.val, y.2 ⟨x.1.val,by omega⟩ = row x

def graph {k : ℕ} (B : SimpleGraph (Fin k)) : SimpleGraph (Vertex k) where
  Adj x y := B.Adj x.1 y.1 ∧ (Align x y ∨ Align y x)
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := fun x h => B.loopless x.1 h.1

lemma graph_cliqueFree {k : ℕ} (B : SimpleGraph (Fin k)) (hB : B.CliqueFree 4) :
    (graph B).CliqueFree 4 := by
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j → B.Adj (f i).1 (f j).1 :=
    fun i j h => (f.map_rel_iff.mpr h).1
  exact no_adj_common_neighbors hB (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

noncomputable def point {k : ℕ} (i : Fin k) (a : ℕ) : Ultrafilter (Vertex k) :=
  Ultrafilter.map (fun x : Fin i.val → ℕ => ⟨i,snocVec x a⟩) (productU i.val)

def cutoff {k : ℕ} (M : ℕ) : Set (Vertex k) :=
  {x | row x ≤ M ∧ ∀ j : Fin x.1.val, M < x.2 j.castSucc}

lemma cutoff_independent {k : ℕ} (B : SimpleGraph (Fin k)) (M : ℕ)
    {x y : Vertex k} (hx : x ∈ cutoff M) (hy : y ∈ cutoff M) :
    ¬(graph B).Adj x y := by
  rintro ⟨_,h | h⟩
  · obtain ⟨h,he⟩ := h
    have hh := hy.2 ⟨x.1.val,h⟩
    change M < y.2 ⟨x.1.val,by omega⟩ at hh
    rw [he] at hh
    exact (not_lt_of_ge hx.1) hh
  · obtain ⟨h,he⟩ := h
    have hh := hx.2 ⟨y.1.val,h⟩
    change M < x.2 ⟨y.1.val,by omega⟩ at hh
    rw [he] at hh
    exact (not_lt_of_ge hy.1) hh

lemma cutoff_mem_point {k : ℕ} (i : Fin k) (a M : ℕ) (ha : a ≤ M) :
    cutoff M ∈ point i a := by
  rw [point,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (all_coords_gt i.val M)
  intro x hx
  exact ⟨by simpa [row] using ha,by intro j; simpa using hx j⟩

/-- Any finitely many rows have a common independent support. -/
theorem finite_common_independent {k : ℕ} (B : SimpleGraph (Fin k))
    (F : Finset (Fin k × ℕ)) :
    ∃ S : Set (Vertex k), (∀ x ∈ S, ∀ y ∈ S, ¬(graph B).Adj x y) ∧
      ∀ z ∈ F, S ∈ point z.1 z.2 := by
  refine ⟨cutoff (F.sup Prod.snd),?_,?_⟩
  · intro x hx y hy
    exact cutoff_independent B _ hx hy
  · intro z hz
    exact cutoff_mem_point z.1 z.2 _ (Finset.le_sup hz)

def copyVertex {k : ℕ} (x : Fin k → ℕ) (i : Fin k) : Vertex k :=
  ⟨i,restrictVec i.isLt x⟩

lemma copy_align {k : ℕ} (x : Fin k → ℕ) {i j : Fin k} (h : i < j) :
    Align (copyVertex x i) (copyVertex x j) := by
  refine ⟨h,?_⟩
  rfl

lemma copy_rel {k : ℕ} (B : SimpleGraph (Fin k)) (x : Fin k → ℕ) (i j : Fin k) :
    (graph B).Adj (copyVertex x i) (copyVertex x j) ↔ B.Adj i j := by
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    rcases lt_or_gt_of_ne h.ne with hij | hji
    · exact Or.inl (copy_align x hij)
    · exact Or.inr (copy_align x hji)

/-- Common support of all rows forces the entire finite graph, not just a triangle. -/
theorem common_support_contains_copy {k : ℕ} (B : SimpleGraph (Fin k))
    (S : Set (Vertex k)) (hS : ∀ i a, S ∈ point i a) :
    Nonempty (B ↪g (graph B).induce S) := by
  have hi : ∀ i : Fin k, {x : Fin k → ℕ | copyVertex x i ∈ S} ∈ productU k := by
    intro i
    have hs : {y : Fin (i.val+1) → ℕ | (⟨i,y⟩ : Vertex k) ∈ S} ∈ productU (i.val+1) := by
      rw [mem_productU]
      exact Filter.Eventually.of_forall (fun a => hS i a)
    exact (prefix_mem i.isLt _).mpr hs
  have hall : {x : Fin k → ℕ | ∀ i, copyVertex x i ∈ S} ∈ productU k :=
    Filter.eventually_all.mpr hi
  obtain ⟨x,hx⟩ := Ultrafilter.nonempty_of_mem hall
  refine ⟨{
    toFun := fun i => ⟨copyVertex x i,hx i⟩
    inj' := ?_
    map_rel_iff' := ?_ }⟩
  · intro i j he
    exact congrArg (fun z : S => z.val.1) he
  · intro i j
    exact copy_rel B x i j

#print axioms graph_cliqueFree
#print axioms finite_common_independent
#print axioms common_support_contains_copy
end Erdos595SuffixSupportTemplate
