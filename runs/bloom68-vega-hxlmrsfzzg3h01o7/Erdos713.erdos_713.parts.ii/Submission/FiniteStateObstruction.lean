import FormalConjecturesUtil

/-!
# An ordinary-subgraph obstruction to finite-state coding constructions

A synchronous automaton reads one letter of each of two vertex words at a
step. Two repeatable choices in the left word, followed (possibly at a
different state) by two repeatable choices in the right word, produce
arbitrarily large **ordinary injective** complete bipartite subgraphs.

This is a no-go lemma for a proposed construction mechanism, not a
counterexample to Erdős 713. In particular this file neither imports nor
uses `Submission.Spec`. The component-skeleton counting consequence is
proved in the accompanying `FiniteStateProgress.md`; it is not silently
assumed or advertised as formalized here.
-/

open SimpleGraph

namespace Erdos713FiniteState

universe u v w

variable {A : Type u} {B : Type v} {Q : Type w}

/-- The ordinary bipartite graph of accepted pairs of words of length `n`.
The sum tags keep the two vertex classes disjoint. -/
def wordGraph (M : DFA (A × B) Q) (n : ℕ) :
    SimpleGraph (List.Vector A n ⊕ List.Vector B n) where
  Adj
    | .inl x, .inr y => M.eval (x.val.zip y.val) ∈ M.accept
    | .inr y, .inl x => M.eval (x.val.zip y.val) ∈ M.accept
    | _, _ => False
  symm := by rintro (x | y) (x' | y') <;> simp
  loopless := by rintro (x | y) <;> simp

/-- These graphs really are bipartite ordinary simple graphs. -/
theorem wordGraph_isBipartite (M : DFA (A × B) Q) (n : ℕ) :
    (wordGraph M n).IsBipartite := by
  apply IsBipartiteWith.isBipartite (s := Set.range Sum.inl) (t := Set.range Sum.inr)
  constructor
  · rw [Set.disjoint_left]
    rintro z ⟨x, rfl⟩ ⟨y, h⟩
    cases h
  · rintro (x | y) (x' | y') h <;> simp_all [wordGraph, Set.mem_range]

/-- Reading the two projections of a paired word recovers that word. -/
lemma zip_projections (z : List (A × B)) :
    (z.map Prod.fst).zip (z.map Prod.snd) = z := by
  induction z with
  | nil => rfl
  | cons a z ih => simp [ih]

/-- Equal-length block codes are injective on words of a prescribed length.
This is the injectivity ingredient in the ordinary-copy construction. -/
lemma flatMap_injective_fixed_length {I X : Type*} (f : I → List X)
    (hf : Function.Injective f) {m : ℕ} (hm : ∀ i, (f i).length = m)
    {s t : List I} (hst : s.length = t.length)
    (heq : s.flatMap f = t.flatMap f) : s = t := by
  induction s generalizing t with
  | nil => simpa using hst.symm
  | cons a s ih =>
    cases t with
    | nil => simp at hst
    | cons b t =>
      have hh := List.append_inj heq ((hm a).trans (hm b).symm)
      have hab : a = b := hf hh.1
      have htail : s = t := ih (by simpa using hst) hh.2
      simp [hab, htail]

/-- A constant block map depends only on the length of the source word. -/
lemma flatMap_const_of_length {I J X : Type*} (z : List X)
    {s : List I} {t : List J} (h : s.length = t.length) :
    s.flatMap (fun _ => z) = t.flatMap (fun _ => z) := by
  induction s generalizing t with
  | nil =>
    have ht : t = [] := by simpa using h.symm
    simp [ht]
  | cons a s ih =>
    cases t with
    | nil => simp at h
    | cons b t => simp only [List.flatMap_cons]; rw [ih (by simpa using h)]

lemma length_flatMap_const {I X : Type*} (f : I → List X) {m : ℕ}
    (hm : ∀ i, (f i).length = m) (s : List I) :
    (s.flatMap f).length = s.length * m := by
  induction s with
  | nil => simp
  | cons a s ih => simp [hm, ih, Nat.add_mul, Nat.add_comm]

/-- Concatenating arbitrarily chosen loops still returns to the same state. -/
lemma evalFrom_flatMap_loops {X I S : Type*} (M : DFA X S) (q : S)
    (f : I → List X) (hf : ∀ i, M.evalFrom q (f i) = q) (s : List I) :
    M.evalFrom q (s.flatMap f) = q := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.flatMap_cons, DFA.evalFrom_of_append, hf, ih]

/-- A finite, directly checkable biclique-pumping certificate. The two
horizontal loops have the same right projection and distinct left
projections; the vertical loops have the opposite property. -/
structure LoopRectangle (M : DFA (A × B) Q) where
  leftState : Q
  rightState : Q
  entryWord : List (A × B)
  connector : List (A × B)
  exitWord : List (A × B)
  horizontal : Bool → List (A × B)
  vertical : Bool → List (A × B)
  entry_run : M.eval entryWord = leftState
  connector_run : M.evalFrom leftState connector = rightState
  exit_accept : M.evalFrom rightState exitWord ∈ M.accept
  horizontal_loop : ∀ b, M.evalFrom leftState (horizontal b) = leftState
  vertical_loop : ∀ b, M.evalFrom rightState (vertical b) = rightState
  horizontal_right : ∀ b, (horizontal b).map Prod.snd = (horizontal false).map Prod.snd
  vertical_left : ∀ b, (vertical b).map Prod.fst = (vertical false).map Prod.fst
  horizontal_left_injective : Function.Injective (fun b => (horizontal b).map Prod.fst)
  vertical_right_injective : Function.Injective (fun b => (vertical b).map Prod.snd)

namespace LoopRectangle

variable {M : DFA (A × B) Q} (C : LoopRectangle M)

lemma horizontal_length (b : Bool) :
    (C.horizontal b).length = (C.horizontal false).length := by
  simpa using congrArg List.length (C.horizontal_right b)

lemma vertical_length (b : Bool) :
    (C.vertical b).length = (C.vertical false).length := by
  simpa using congrArg List.length (C.vertical_left b)

/-- The full accepted word; the two Boolean words are independent choices. -/
def pumped (x y : List Bool) : List (A × B) :=
  C.entryWord ++ x.flatMap C.horizontal ++ C.connector ++ y.flatMap C.vertical ++ C.exitWord

lemma pumped_accept (x y : List Bool) : M.eval (C.pumped x y) ∈ M.accept := by
  simp only [pumped, DFA.eval, DFA.evalFrom_of_append]
  rw [show M.evalFrom M.start C.entryWord = C.leftState from C.entry_run,
    evalFrom_flatMap_loops _ _ _ C.horizontal_loop,
    C.connector_run, evalFrom_flatMap_loops _ _ _ C.vertical_loop]
  exact C.exit_accept

/-- The precise common length of all pumped pairs. -/
def size (n : ℕ) : ℕ := C.entryWord.length + n * (C.horizontal false).length +
  C.connector.length + n * (C.vertical false).length + C.exitWord.length

lemma pumped_length {x y : List Bool} {n : ℕ}
    (hx : x.length = n) (hy : y.length = n) :
    (C.pumped x y).length = C.size n := by
  simp only [pumped, List.length_append,
    length_flatMap_const C.horizontal C.horizontal_length,
    length_flatMap_const C.vertical C.vertical_length, hx, hy, size]

lemma pumped_fst {x y z : List Bool} (hyz : y.length = z.length) :
    (C.pumped x y).map Prod.fst = (C.pumped x z).map Prod.fst := by
  simp only [pumped, List.map_append, List.map_flatMap, C.vertical_left]
  rw [flatMap_const_of_length _ hyz]

lemma pumped_snd {x y z : List Bool} (hxy : x.length = y.length) :
    (C.pumped x z).map Prod.snd = (C.pumped y z).map Prod.snd := by
  simp only [pumped, List.map_append, List.map_flatMap, C.horizontal_right]
  rw [flatMap_const_of_length _ hxy]

/-- Left vertices encode arbitrary Boolean words of length `n`. -/
def leftWord {n : ℕ} (x : List.Vector Bool n) : List.Vector A (C.size n) :=
  ⟨(C.pumped x.val (List.replicate n false)).map Prod.fst,
    by simpa using C.pumped_length x.property (List.length_replicate ..)⟩

/-- Right vertices encode arbitrary Boolean words of length `n`. -/
def rightWord {n : ℕ} (y : List.Vector Bool n) : List.Vector B (C.size n) :=
  ⟨(C.pumped (List.replicate n false) y.val).map Prod.snd,
    by simpa using C.pumped_length (List.length_replicate ..) y.property⟩

lemma leftWord_injective (n : ℕ) :
    Function.Injective (C.leftWord (n := n)) := by
  intro x y h
  have heq := congrArg Subtype.val h
  simp only [leftWord, pumped, List.map_append, List.map_flatMap] at heq
  have hb : x.val.flatMap (fun b => (C.horizontal b).map Prod.fst) =
      y.val.flatMap (fun b => (C.horizontal b).map Prod.fst) := by
    simpa only [List.append_left_inj, List.append_right_inj] using heq
  apply Subtype.ext
  exact flatMap_injective_fixed_length _ C.horizontal_left_injective
    (fun b => by simpa using C.horizontal_length b)
    (x.property.trans y.property.symm) hb

lemma rightWord_injective (n : ℕ) :
    Function.Injective (C.rightWord (n := n)) := by
  intro x y h
  have heq := congrArg Subtype.val h
  simp only [rightWord, pumped, List.map_append, List.map_flatMap] at heq
  have hb : x.val.flatMap (fun b => (C.vertical b).map Prod.snd) =
      y.val.flatMap (fun b => (C.vertical b).map Prod.snd) := by
    simpa only [List.append_left_inj, List.append_right_inj] using heq
  apply Subtype.ext
  exact flatMap_injective_fixed_length _ C.vertical_right_injective
    (fun b => by simpa using C.vertical_length b)
    (x.property.trans y.property.symm) hb

lemma words_adj {n : ℕ} (x y : List.Vector Bool n) :
    (wordGraph M (C.size n)).Adj (.inl (C.leftWord x)) (.inr (C.rightWord y)) := by
  change M.eval (((C.pumped x.val (List.replicate n false)).map Prod.fst).zip
    ((C.pumped (List.replicate n false) y.val).map Prod.snd)) ∈ M.accept
  rw [C.pumped_fst (x := x.val) (z := y.val) (by simp [y.property]),
    C.pumped_snd (y := x.val) (by simp [x.property]), zip_projections]
  exact C.pumped_accept _ _

/-- An actual injective ordinary copy, not just a homomorphism or an
induced/coloured copy. Each side has `2 ^ n` distinct vertices. -/
def completeBipartiteCopy (n : ℕ) :
    (completeBipartiteGraph (List.Vector Bool n) (List.Vector Bool n)).Copy
      (wordGraph M (C.size n)) where
  toHom := {
    toFun := Sum.map C.leftWord C.rightWord
    map_rel' := by
      rintro (x | y) (x' | y') h
      · simp [completeBipartiteGraph] at h
      · exact C.words_adj x y'
      · exact (C.words_adj x' y).symm
      · simp [completeBipartiteGraph] at h }
  injective' := Sum.map_injective.mpr ⟨C.leftWord_injective n, C.rightWord_injective n⟩

/-- Ordinary `K_(t,t)` already occurs after any number of repetitions with
`t ≤ 2 ^ n`. This keeps the quantitative word length in the conclusion. -/
theorem completeBipartite_isContained {t n : ℕ} (ht : t ≤ 2 ^ n) :
    completeBipartiteGraph (Fin t) (Fin t) ⊑ wordGraph M (C.size n) := by
  classical
  have hcard : Fintype.card (Fin t) ≤ Fintype.card (List.Vector Bool n) := by
    simpa only [Fintype.card_fin, card_vector, Fintype.card_bool] using ht
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let f : (completeBipartiteGraph (Fin t) (Fin t)).Copy
      (completeBipartiteGraph (List.Vector Bool n) (List.Vector Bool n)) := {
    toHom := {
      toFun := Sum.map e e
      map_rel' := by
        rintro (x | y) (x' | y') h <;> simp_all [completeBipartiteGraph] }
    injective' := Sum.map_injective.mpr ⟨e.injective, e.injective⟩ }
  exact ⟨(C.completeBipartiteCopy n).comp f⟩

include C in
/-- No family with this certificate can remain free of any one prescribed
complete bipartite graph. -/
theorem not_all_completeBipartite_free (t : ℕ) :
    ¬ ∀ n, (completeBipartiteGraph (Fin t) (Fin t)).Free (wordGraph M n) := by
  intro h
  exact h (C.size t) (C.completeBipartite_isContained (Nat.lt_two_pow_self.le))

end LoopRectangle

/-- Any ordinary bipartite graph on `t` vertices injects into `K_(t,t)`.
This also accounts for isolated vertices and disconnected forbidden graphs. -/
theorem bipartite_isContained_completeBipartite {t : ℕ}
    (H : SimpleGraph (Fin t)) (hH : H.IsBipartite) :
    H ⊑ completeBipartiteGraph (Fin t) (Fin t) := by
  classical
  obtain ⟨col⟩ := hH
  let f : Fin t → Fin t ⊕ Fin t := fun v =>
    if col v = 0 then .inl v else .inr v
  have hinj : Function.Injective f := by
    have hleft : Function.LeftInverse (Sum.elim id id) f := by
      intro v
      dsimp [f]
      split_ifs <;> rfl
    exact hleft.injective
  refine ⟨⟨{ toFun := f, map_rel' := ?_ }, hinj⟩⟩
  intro v w hvw
  have hne := col.valid hvw
  by_cases hv : col v = 0
  · have hw : col w ≠ 0 := fun hw => hne (hv.trans hw.symm)
    simp [f, hv, hw, completeBipartiteGraph]
  · by_cases hw : col w = 0
    · simp [f, hv, hw, completeBipartiteGraph]
    · have heq : col v = col w := by omega
      exact (hne heq).elim

/-- The pumping certificate contradicts avoidance of *any fixed finite
ordinary bipartite graph*, not just avoidance of a biclique chosen afterwards. -/
theorem LoopRectangle.not_all_bipartite_free {M : DFA (A × B) Q}
    (C : LoopRectangle M) {t : ℕ} (H : SimpleGraph (Fin t)) (hH : H.IsBipartite) :
    ¬ ∀ n, H.Free (wordGraph M n) := by
  intro hall
  exact hall (C.size t) ((bipartite_isContained_completeBipartite H hH).trans
    (C.completeBipartite_isContained Nat.lt_two_pow_self.le))

/-- A repeatable ambiguity in the left coordinate at a state. -/
def LeftCollision (M : DFA (A × B) Q) (p : Q) : Prop :=
  ∃ u v : List (A × B), M.evalFrom p u = p ∧ M.evalFrom p v = p ∧
    u.map Prod.snd = v.map Prod.snd ∧ u.map Prod.fst ≠ v.map Prod.fst

/-- A repeatable ambiguity in the right coordinate at a state. -/
def RightCollision (M : DFA (A × B) Q) (p : Q) : Prop :=
  ∃ u v : List (A × B), M.evalFrom p u = p ∧ M.evalFrom p v = p ∧
    u.map Prod.fst = v.map Prod.fst ∧ u.map Prod.snd ≠ v.map Prod.snd

/-- Inside a strongly connected component with no left collision, a right
word and the two endpoint states determine at most one left word. Here the
return path is explicit, so no separate SCC datatype is needed. -/
theorem left_projection_unique_of_return {M : DFA (A × B) Q} {p q : Q}
    (hno : ¬ LeftCollision M p) {u v z : List (A × B)}
    (hu : M.evalFrom p u = q) (hv : M.evalFrom p v = q)
    (hz : M.evalFrom q z = p) (hsame : u.map Prod.snd = v.map Prod.snd) :
    u.map Prod.fst = v.map Prod.fst := by
  by_contra hne
  apply hno
  refine ⟨u ++ z, v ++ z, ?_, ?_, ?_, ?_⟩
  · simpa only [DFA.evalFrom_of_append, hu] using hz
  · simpa only [DFA.evalFrom_of_append, hv] using hz
  · simpa only [List.map_append] using congrArg (· ++ z.map Prod.snd) hsame
  · intro heq
    apply hne
    exact (List.append_left_inj _).mp (by simpa only [List.map_append] using heq)

/-- The symmetric endpoint-uniqueness statement for the other coordinate. -/
theorem right_projection_unique_of_return {M : DFA (A × B) Q} {p q : Q}
    (hno : ¬ RightCollision M p) {u v z : List (A × B)}
    (hu : M.evalFrom p u = q) (hv : M.evalFrom p v = q)
    (hz : M.evalFrom q z = p) (hsame : u.map Prod.fst = v.map Prod.fst) :
    u.map Prod.snd = v.map Prod.snd := by
  by_contra hne
  apply hno
  refine ⟨u ++ z, v ++ z, ?_, ?_, ?_, ?_⟩
  · simpa only [DFA.evalFrom_of_append, hu] using hz
  · simpa only [DFA.evalFrom_of_append, hv] using hz
  · simpa only [List.map_append] using congrArg (· ++ z.map Prod.fst) hsame
  · intro heq
    apply hne
    exact (List.append_left_inj _).mp (by simpa only [List.map_append] using heq)

/-- Two opposite collisions joined on an accepting path give a concrete
loop-rectangle certificate. All hypotheses are finite-word checks. -/
theorem exists_loopRectangle_of_collisions {M : DFA (A × B) Q} {p q : Q}
    (hp : LeftCollision M p) (hq : RightCollision M q)
    {a b c : List (A × B)} (ha : M.eval a = p)
    (hb : M.evalFrom p b = q) (hc : M.evalFrom q c ∈ M.accept) :
    Nonempty (LoopRectangle M) := by
  obtain ⟨u₀, u₁, hu₀, hu₁, hur, hul⟩ := hp
  obtain ⟨v₀, v₁, hv₀, hv₁, hvl, hvr⟩ := hq
  refine ⟨{
    leftState := p, rightState := q,
    entryWord := a, connector := b, exitWord := c,
    horizontal := fun b => if b then u₁ else u₀,
    vertical := fun b => if b then v₁ else v₀,
    entry_run := ha, connector_run := hb, exit_accept := hc,
    horizontal_loop := ?_, vertical_loop := ?_,
    horizontal_right := ?_, vertical_left := ?_,
    horizontal_left_injective := ?_, vertical_right_injective := ?_ }⟩
  · intro b; cases b <;> assumption
  · intro b; cases b <;> assumption
  · intro b; cases b
    · rfl
    · exact hur.symm
  · intro b; cases b
    · rfl
    · exact hvl.symm
  · intro b c h; cases b <;> cases c <;> simp_all
  · intro b c h; cases b <;> cases c <;> simp_all

/-- A usable rejection test for a putative ordinary `H`-free automaton
construction, for a fixed input forbidden graph `H`. -/
theorem not_all_free_of_collisions {M : DFA (A × B) Q} {p q : Q}
    {t : ℕ} (H : SimpleGraph (Fin t)) (hH : H.IsBipartite)
    (hp : LeftCollision M p) (hq : RightCollision M q)
    {a b c : List (A × B)} (ha : M.eval a = p)
    (hb : M.evalFrom p b = q) (hc : M.evalFrom q c ∈ M.accept) :
    ¬ ∀ n, H.Free (wordGraph M n) := by
  obtain ⟨C⟩ := exists_loopRectangle_of_collisions hp hq ha hb hc
  exact C.not_all_bipartite_free H hH

/-- Swapping the input tapes only swaps the two ordinary vertex classes. -/
def wordGraph_swap_iso (M : DFA (A × B) Q) (n : ℕ) :
    wordGraph (M.comap Prod.swap) n ≃g wordGraph M n :=
  ⟨Equiv.sumComm _ _, by
    rintro (x | y) (x' | y') <;>
      simp [wordGraph, DFA.eval_comap, List.zip_swap]⟩

/-- Coordinate swapping interchanges the two kinds of repeatable ambiguity. -/
lemma rightCollision_swap_iff (M : DFA (A × B) Q) (p : Q) :
    RightCollision (M.comap Prod.swap) p ↔ LeftCollision M p := by
  constructor
  · rintro ⟨u, v, hu, hv, heq, hne⟩
    refine ⟨u.map Prod.swap, v.map Prod.swap, ?_, ?_, ?_, ?_⟩
    · simpa only [DFA.evalFrom_comap] using hu
    · simpa only [DFA.evalFrom_comap] using hv
    · simpa [List.map_map, Function.comp_def] using heq
    · simpa [List.map_map, Function.comp_def] using hne
  · rintro ⟨u, v, hu, hv, heq, hne⟩
    refine ⟨u.map Prod.swap, v.map Prod.swap, ?_, ?_, ?_, ?_⟩
    · simpa [DFA.evalFrom_comap, List.map_map, Function.comp_def] using hu
    · simpa [DFA.evalFrom_comap, List.map_map, Function.comp_def] using hv
    · simpa [List.map_map, Function.comp_def] using heq
    · simpa [List.map_map, Function.comp_def] using hne

/-- Right neighbours of a left vertex are precisely the accepted right words. -/
def rightNeighborsEquiv (M : DFA (A × B) Q) {n : ℕ} (x : List.Vector A n) :
    (wordGraph M n).neighborSet (.inl x) ≃
      {y : List.Vector B n // M.eval (x.val.zip y.val) ∈ M.accept} where
  toFun z := match z with
    | ⟨.inl _, h⟩ => False.elim h
    | ⟨.inr y, h⟩ => ⟨y, h⟩
  invFun y := ⟨.inr y.val, y.property⟩
  left_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl y => exact False.elim hz
    | inr y => rfl
  right_inv _ := rfl

open scoped Classical in
/-- In a recurrent accepting automaton with no right collision, a fixed left
word has at most as many neighbours as there are states. -/
theorem degree_left_le_states [Fintype A] [Fintype B] [Fintype Q]
    (M : DFA (A × B) Q) (hno : ¬ RightCollision M M.start)
    (hreturn : ∀ q ∈ M.accept, ∃ z, M.evalFrom q z = M.start)
    {n : ℕ} (x : List.Vector A n) :
    (wordGraph M n).degree (.inl x) ≤ Fintype.card Q := by
  classical
  let Y := {y : List.Vector B n // M.eval (x.val.zip y.val) ∈ M.accept}
  let f : Y → Q := fun y => M.eval (x.val.zip y.val.val)
  have hinj : Function.Injective f := by
    intro y y' hyy
    obtain ⟨z, hz⟩ := hreturn _ y.property
    have hsame : (x.val.zip y.val.val).map Prod.fst =
        (x.val.zip y'.val.val).map Prod.fst := by
      rw [List.map_fst_zip (by simp [x.property, y.val.property]),
        List.map_fst_zip (by simp [x.property, y'.val.property])]
    have hright := right_projection_unique_of_return hno rfl hyy.symm hz hsame
    rw [List.map_snd_zip (by simp [x.property, y.val.property]),
      List.map_snd_zip (by simp [x.property, y'.val.property])] at hright
    exact Subtype.ext (Subtype.ext hright)
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (rightNeighborsEquiv M x)]
  exact Fintype.card_le_of_injective f hinj

open scoped Classical in
/-- A complete edge bound for the recurrent, one-sided-unambiguous case.
This is an ordinary simple-graph edge count, not just a bound on accepted runs. -/
theorem card_edges_le_of_no_right_collision [Fintype A] [Fintype B] [Fintype Q]
    (M : DFA (A × B) Q) (hno : ¬ RightCollision M M.start)
    (hreturn : ∀ q ∈ M.accept, ∃ z, M.evalFrom q z = M.start) (n : ℕ) :
    (wordGraph M n).edgeFinset.card ≤ Fintype.card Q * Fintype.card A ^ n := by
  classical
  let S : Finset (List.Vector A n ⊕ List.Vector B n) := Finset.univ.image Sum.inl
  let T : Finset (List.Vector A n ⊕ List.Vector B n) := Finset.univ.image Sum.inr
  have hpart : (wordGraph M n).IsBipartiteWith (S : Set _) (T : Set _) := by
    constructor
    · rw [Set.disjoint_left]
      rintro z hzS hzT
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hzS
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hzT
      have hxy := hx.trans hy.symm
      cases hxy
    · rintro (x | y) (x' | y') h <;> simp_all [S, T, wordGraph]
  calc
    (wordGraph M n).edgeFinset.card = ∑ v ∈ S, (wordGraph M n).degree v :=
      (isBipartiteWith_sum_degrees_eq_card_edges hpart).symm
    _ ≤ ∑ _v ∈ S, Fintype.card Q := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      exact degree_left_le_states M hno hreturn x
    _ = Fintype.card Q * Fintype.card A ^ n := by
      rw [Finset.sum_const, smul_eq_mul]
      dsimp [S]
      rw [Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_univ, card_vector, Nat.mul_comm]

open scoped Classical in
/-- The symmetric recurrent edge bound. -/
theorem card_edges_le_of_no_left_collision [Fintype A] [Fintype B] [Fintype Q]
    (M : DFA (A × B) Q) (hno : ¬ LeftCollision M M.start)
    (hreturn : ∀ q ∈ M.accept, ∃ z, M.evalFrom q z = M.start) (n : ℕ) :
    (wordGraph M n).edgeFinset.card ≤ Fintype.card Q * Fintype.card B ^ n := by
  classical
  have hno' : ¬ RightCollision (M.comap Prod.swap) M.start := by
    rwa [rightCollision_swap_iff]
  have hreturn' : ∀ q ∈ (M.comap Prod.swap).accept,
      ∃ z, (M.comap Prod.swap).evalFrom q z = (M.comap Prod.swap).start := by
    intro q hq
    obtain ⟨z, hz⟩ := hreturn q hq
    refine ⟨z.map Prod.swap, ?_⟩
    simpa [DFA.evalFrom_comap, List.map_map, Function.comp_def] using hz
  have h := card_edges_le_of_no_right_collision (M.comap Prod.swap) hno' hreturn' n
  rwa [(wordGraph_swap_iso M n).card_edgeFinset_eq] at h

open scoped Classical in
/-- If accepting states can return to the initial state, avoiding any one
fixed bipartite graph at every length forces a linear edge bound at every
length. This formally verified special case is stronger than the general
polynomial-in-length bound in the accompanying written argument. -/
theorem recurrent_free_linear_bound [Fintype A] [Fintype B] [Fintype Q]
    (M : DFA (A × B) Q) {t : ℕ} (H : SimpleGraph (Fin t))
    (hH : H.IsBipartite) (hfree : ∀ n, H.Free (wordGraph M n))
    (hreturn : ∀ q ∈ M.accept, ∃ z, M.evalFrom q z = M.start) :
    (∀ n, (wordGraph M n).edgeFinset.card ≤ Fintype.card Q * Fintype.card A ^ n) ∨
    (∀ n, (wordGraph M n).edgeFinset.card ≤ Fintype.card Q * Fintype.card B ^ n) := by
  classical
  by_cases haccept : ∃ w, M.eval w ∈ M.accept
  swap
  · push_neg at haccept
    left
    intro n
    have hempty : wordGraph M n = ⊥ := by
      ext x y
      cases x <;> cases y <;> simp [wordGraph, haccept]
    rw [edgeFinset_eq_empty.mpr hempty, Finset.card_empty]
    exact Nat.zero_le _
  by_cases hr : RightCollision M M.start
  · have hl : ¬ LeftCollision M M.start := by
      intro hl
      obtain ⟨w, hw⟩ := haccept
      exact not_all_free_of_collisions H hH hl hr (a := []) (b := [])
        (c := w) rfl rfl hw hfree
    exact Or.inr (card_edges_le_of_no_left_collision M hl hreturn)
  · exact Or.inl (card_edges_le_of_no_right_collision M hr hreturn)


lemma leftCollision_swap_iff (M : DFA (A × B) Q) (p : Q) :
    LeftCollision (M.comap Prod.swap) p ↔ RightCollision M p := by
  simpa [DFA.comap] using (rightCollision_swap_iff (M.comap Prod.swap) p).symm

/-- The same rejection test when the right-coordinate collision occurs first
along the accepting path. -/
theorem not_all_free_of_reverse_collisions {M : DFA (A × B) Q} {p q : Q}
    {t : ℕ} (H : SimpleGraph (Fin t)) (hH : H.IsBipartite)
    (hp : RightCollision M p) (hq : LeftCollision M q)
    {a b c : List (A × B)} (ha : M.eval a = p)
    (hb : M.evalFrom p b = q) (hc : M.evalFrom q c ∈ M.accept) :
    ¬ ∀ n, H.Free (wordGraph M n) := by
  intro hall
  have hall' : ∀ n, H.Free (wordGraph (M.comap Prod.swap) n) := by
    intro n h
    exact hall n (h.trans (wordGraph_swap_iso M n).isContained)
  have ha' : (M.comap Prod.swap).eval (a.map Prod.swap) = p := by
    simpa [DFA.eval_comap, List.map_map, Function.comp_def] using ha
  have hb' : (M.comap Prod.swap).evalFrom p (b.map Prod.swap) = q := by
    simpa [DFA.evalFrom_comap, List.map_map, Function.comp_def] using hb
  have hc' : (M.comap Prod.swap).evalFrom q (c.map Prod.swap) ∈
      (M.comap Prod.swap).accept := by
    simpa [DFA.evalFrom_comap, List.map_map, Function.comp_def] using hc
  exact not_all_free_of_collisions H hH ((leftCollision_swap_iff M p).mpr hp)
    ((rightCollision_swap_iff M q).mpr hq) ha' hb' hc' hall'

open scoped Classical in
/-- The preceding disjunction implies `e(G) ≤ s * v(G)` with the actual
ordinary vertex count. No asymptotic qualification is needed. -/
theorem recurrent_free_edges_le_states_mul_vertices
    [Fintype A] [Fintype B] [Fintype Q]
    (M : DFA (A × B) Q) {t : ℕ} (H : SimpleGraph (Fin t))
    (hH : H.IsBipartite) (hfree : ∀ n, H.Free (wordGraph M n))
    (hreturn : ∀ q ∈ M.accept, ∃ z, M.evalFrom q z = M.start) (n : ℕ) :
    (wordGraph M n).edgeFinset.card ≤
      Fintype.card Q * Fintype.card (List.Vector A n ⊕ List.Vector B n) := by
  classical
  rw [Fintype.card_sum, card_vector, card_vector]
  rcases recurrent_free_linear_bound M H hH hfree hreturn with h | h
  · exact (h n).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  · exact (h n).trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))


namespace Examples

/-- A genuinely state-dependent paired-letter relation with three allowed
transitions from each live state. State 2 is a rejecting sink. It is used
only as a regression test, never as a claimed H-free construction. -/
def contextMachine : DFA (Bool × Bool) (Fin 3) where
  step q z := if q = 2 then 2 else
    if q = 0 then
      if z.1 && z.2 then 2 else if z.1 then 1 else 0
    else
      if (!z.1) && z.2 then 2 else if z.1 then 0 else 1
  start := 0
  accept := {0, 1}

/-- The two distinct coordinate choices close after two and one steps,
respectively, giving an explicit finite certificate for the regression test. -/
def contextCertificate : LoopRectangle contextMachine where
  leftState := 0
  rightState := 0
  entryWord := []
  connector := []
  exitWord := []
  horizontal b := if b then [(true, false), (true, false)]
    else [(false, false), (false, false)]
  vertical b := if b then [(false, true)] else [(false, false)]
  entry_run := by decide
  connector_run := by decide
  exit_accept := by simp [contextMachine]
  horizontal_loop := by decide
  vertical_loop := by decide
  horizontal_right := by decide
  vertical_left := by decide
  horizontal_left_injective := by decide
  vertical_right_injective := by decide

lemma contextCertificate_size (n : ℕ) : contextCertificate.size n = 3 * n := by
  change 0 + n * 2 + 0 + n * 1 + 0 = 3 * n
  omega

/-- In particular, the apparently promising state-dependent growth example
contains `K_(t,t)` as an ordinary injective subgraph at length `3*n`. -/
theorem context_contains_completeBipartite {t n : ℕ} (ht : t ≤ 2 ^ n) :
    completeBipartiteGraph (Fin t) (Fin t) ⊑ wordGraph contextMachine (3 * n) := by
  rw [← contextCertificate_size n]
  exact contextCertificate.completeBipartite_isContained ht

/-- A small, fully checked ordinary-copy regression test. -/
theorem context_contains_K33 :
    completeBipartiteGraph (Fin 3) (Fin 3) ⊑ wordGraph contextMachine 6 :=
  context_contains_completeBipartite (n := 2) (by decide)

end Examples

end Erdos713FiniteState

#print axioms Erdos713FiniteState.wordGraph_isBipartite
#print axioms Erdos713FiniteState.LoopRectangle.completeBipartiteCopy
#print axioms Erdos713FiniteState.LoopRectangle.completeBipartite_isContained
#print axioms Erdos713FiniteState.LoopRectangle.not_all_completeBipartite_free

#print axioms Erdos713FiniteState.LoopRectangle.not_all_bipartite_free
#print axioms Erdos713FiniteState.left_projection_unique_of_return
#print axioms Erdos713FiniteState.right_projection_unique_of_return
#print axioms Erdos713FiniteState.not_all_free_of_collisions

#print axioms Erdos713FiniteState.wordGraph_swap_iso
#print axioms Erdos713FiniteState.card_edges_le_of_no_right_collision
#print axioms Erdos713FiniteState.recurrent_free_linear_bound

#print axioms Erdos713FiniteState.not_all_free_of_reverse_collisions
#print axioms Erdos713FiniteState.recurrent_free_edges_le_states_mul_vertices

#print axioms Erdos713FiniteState.Examples.contextCertificate
#print axioms Erdos713FiniteState.Examples.context_contains_K33
