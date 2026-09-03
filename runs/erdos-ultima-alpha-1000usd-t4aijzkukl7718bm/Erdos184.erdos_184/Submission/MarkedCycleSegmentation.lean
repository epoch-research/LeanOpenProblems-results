import Submission.FourPointSegmentation

/-! Segmentation at an arbitrary finite set of cycle junctions, with a finite
recursive encoding of all possible cyclic orders. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 2000000
variable {V W : Type*} {G : SimpleGraph V}

/-- Insert a new junction immediately after one old junction. -/
def insertNext [DecidableEq W] (next : W → W) (j : W) : W ⊕ Unit → W ⊕ Unit
  | .inl i => if i = j then .inr () else .inl (next i)
  | .inr _ => .inl (next j)

lemma insertNext_ne [DecidableEq W] (next : W → W) (hne : ∀ i, i ≠ next i) (j : W) :
    ∀ i, i ≠ insertNext next j i := by
  intro i
  cases i with
  | inl i =>
    dsimp only [insertNext]
    split_ifs with hi
    · simp
    · exact fun h => hne i (Sum.inl.inj h)
  | inr u => simp [insertNext]

namespace Segmentation
variable [DecidableEq W] {a : V} {c : G.Walk a a} {vertex : W → V} {next : W → W}

noncomputable def splice (S : Segmentation c vertex id next) (j : W) (x : V)
    (P : PathParts (S.path j) x) :
    Segmentation c (Sum.elim vertex (fun _ : Unit => x)) id (insertNext next j) := by
  let path : ∀ i : W ⊕ Unit,
      G.Walk ((Sum.elim vertex (fun _ : Unit => x)) i)
        ((Sum.elim vertex (fun _ : Unit => x)) (insertNext next j i)) :=
    fun i => match i with
    | .inl i => if hi : i = j then
        P.first.copy (congrArg vertex hi.symm) (by simp [insertNext,hi])
      else (S.path i).copy rfl (by simp [insertNext,hi])
    | .inr _ => P.last
  have heleft : (path (.inl j)).edges = P.first.edges := by
    simp only [path,dif_pos rfl,Walk.edges_copy]
  have heother (i : W) (hi : i ≠ j) : (path (.inl i)).edges = (S.path i).edges := by
    simp only [path,dif_neg hi,Walk.edges_copy]
  have henew (u : Unit) : (path (.inr u)).edges = P.last.edges := rfl
  refine ⟨path,?_,?_,?_⟩
  · intro i
    cases i with
    | inl i =>
      by_cases hi : i = j
      · subst i
        simpa only [path,dif_pos rfl,Walk.isPath_copy] using P.first_path
      · simpa only [path,dif_neg hi,Walk.isPath_copy] using S.isPath i
    | inr u => cases u; exact P.last_path
  · intro i k hik
    cases i with
    | inl i =>
      cases k with
      | inl k =>
        have hik' : i ≠ k := fun h => hik (congrArg Sum.inl h)
        by_cases hi : i = j
        · subst i
          have hk : k ≠ j := Ne.symm hik'
          rw [heleft,heother k hk]
          exact disjoint_mono (S.disjoint j k hik') P.first_edges_subset (List.Subset.refl _)
        · by_cases hk : k = j
          · subst k
            rw [heother i hi,heleft]
            exact disjoint_mono (S.disjoint i j hi) (List.Subset.refl _) P.first_edges_subset
          · rw [heother i hi,heother k hk]
            exact S.disjoint i k hik'
      | inr u =>
        rw [henew u]
        by_cases hi : i = j
        · subst i
          rw [heleft]
          exact P.edges_disjoint
        · rw [heother i hi]
          exact disjoint_mono (S.disjoint i j hi) (List.Subset.refl _) P.last_edges_subset
    | inr u =>
      cases k with
      | inl k =>
        rw [henew u]
        by_cases hk : k = j
        · subst k
          rw [heleft]
          exact P.edges_disjoint.symm
        · rw [heother k hk]
          exact disjoint_mono (S.disjoint j k (Ne.symm hk)) P.last_edges_subset (List.Subset.refl _)
      | inr v => exact (hik (congrArg Sum.inr (Subsingleton.elim u v))).elim
  · intro e
    constructor
    · intro he
      obtain ⟨i,hi⟩ := (S.cover e).mp he
      by_cases hij : i = j
      · subst i
        rcases (P.edges_cover e).mpr hi with he | he
        · exact ⟨.inl j,heleft ▸ he⟩
        · exact ⟨.inr (),henew () ▸ he⟩
      · exact ⟨.inl i,heother i hij ▸ hi⟩
    · rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        by_cases hij : i = j
        · subst i
          rw [heleft] at hi
          exact (S.cover e).mpr ⟨j,P.first_edges_subset hi⟩
        · rw [heother i hij] at hi
          exact (S.cover e).mpr ⟨i,hi⟩
      | inr u =>
        rw [henew u] at hi
        exact (S.cover e).mpr ⟨j,P.last_edges_subset hi⟩

lemma exists_segment_through (S : Segmentation c vertex id next) (hc : c.IsCycle)
    {x : V} (hx : x ∈ c.support) : ∃ i, x ∈ (S.path i).support := by
  obtain ⟨e,he,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
  obtain ⟨i,hi⟩ := (S.cover e).mp he
  exact ⟨i,Walk.mem_support_of_mem_edges hi hxe⟩
end Segmentation

namespace Marked
/-- `Marker n` has `n+2` junctions. -/
def Marker : ℕ → Type
  | 0 => Fin 2
  | n+1 => Marker n ⊕ Unit

instance markerDecidableEq : (n : ℕ) → DecidableEq (Marker n)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | n+1 => by letI := markerDecidableEq n; exact inferInstanceAs (DecidableEq (Marker n ⊕ Unit))
instance markerFintype : (n : ℕ) → Fintype (Marker n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n+1 => by letI := markerFintype n; exact inferInstanceAs (Fintype (Marker n ⊕ Unit))

/-- There are `(n+1)!` recursively encoded directed cyclic orders. -/
def Order : ℕ → Type
  | 0 => Unit
  | n+1 => Order n × Marker n

instance orderDecidableEq : (n : ℕ) → DecidableEq (Order n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => by letI := orderDecidableEq n; exact inferInstanceAs (DecidableEq (Order n × Marker n))
instance orderFintype : (n : ℕ) → Fintype (Order n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by letI := orderFintype n; exact inferInstanceAs (Fintype (Order n × Marker n))

def next : (n : ℕ) → Order n → Marker n → Marker n
  | 0, _ => (![1,0] : Fin 2 → Fin 2)
  | n+1, (o,j) => insertNext (next n o) j

lemma next_ne : ∀ n (o : Order n) (i : Marker n), i ≠ next n o i := by
  intro n
  induction n with
  | zero =>
    intro o
    change ∀ i : Fin 2, i ≠ (![1,0] : Fin 2 → Fin 2) i
    decide
  | succ n ih => intro o; exact insertNext_ne (next n o.1) (ih o.1) o.2

lemma marker_card : ∀ n, Fintype.card (Marker n) = n+2 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (Marker n ⊕ Unit) = n+1+2; simp [ih]

lemma order_card : ∀ n, Fintype.card (Order n) = (n+1).factorial := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Order n × Marker n) = (n+1+1).factorial
    rw [Fintype.card_prod,ih,marker_card,Nat.factorial_succ (n+1)]
    exact Nat.mul_comm _ _

lemma exists_segmentation {a : V} (c : G.Walk a a) (hc : c.IsCycle) :
    ∀ n (vertex : Marker n → V), Function.Injective vertex → (∀ i, vertex i ∈ c.support) →
      ∃ o : Order n, Nonempty (Segmentation c vertex id (next n o)) := by
  intro n
  induction n with
  | zero =>
    intro vertex hinj hmem
    obtain ⟨S⟩ := two_segments_any c hc (hmem (0 : Fin 2)) (hmem (1 : Fin 2))
      (fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj h))
    have hv : vertex = ![vertex (0 : Fin 2),vertex (1 : Fin 2)] := by funext i; fin_cases i <;> rfl
    have hs : (id : Marker 0 → Marker 0) = src2 := by funext i; fin_cases i <;> rfl
    refine ⟨(),?_⟩
    rw [hv,hs]
    exact ⟨S⟩
  | succ n ih =>
    intro vertex hinj hmem
    let old : Marker n → V := vertex ∘ Sum.inl
    obtain ⟨o,⟨S⟩⟩ := ih old (hinj.comp Sum.inl_injective) (fun i => hmem (.inl i))
    obtain ⟨j,hj⟩ := S.exists_segment_through hc (hmem (.inr ()))
    obtain ⟨P⟩ := exists_pathParts (S.path j) (S.isPath j) hj
    have hv : Sum.elim old (fun _ : Unit => vertex (.inr ())) = vertex := by
      funext i
      cases i with
      | inl i => rfl
      | inr u => cases u; rfl
    refine ⟨(o,j),?_⟩
    have hS := S.splice j (vertex (.inr ())) P
    rw [hv] at hS
    exact ⟨hS⟩

#print axioms exists_segmentation
#print axioms order_card
end Marked
end Erdos184Work.CycleSegments
