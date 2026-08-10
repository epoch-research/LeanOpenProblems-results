import FormalConjectures.Util.ProblemImports

open Finset List

namespace A052709dev

/-- Avoids a weakly-increasing subsequence of length 3, phrased with `Sublist`. -/
def AvoidsWI3 (l : List ℕ) : Prop :=
  ∀ a b c, a ≤ b → b ≤ c → ¬ ([a, b, c] <+ l)

/-- strictly decreasing prefix length -/
def sdp : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: t => if b < a then 1 + sdp (b :: t) else 1

@[simp] theorem sdp_nil : sdp [] = 0 := rfl
@[simp] theorem sdp_single (a : ℕ) : sdp [a] = 1 := rfl

theorem sdp_cons_cons (a b : ℕ) (t : List ℕ) :
    sdp (a :: b :: t) = if b < a then 1 + sdp (b :: t) else 1 := rfl

theorem sdp_pos {l : List ℕ} (h : l ≠ []) : 0 < sdp l := by
  match l with
  | [] => simp at h
  | [_] => simp
  | a :: b :: t =>
    rw [sdp_cons_cons]; split <;> omega

theorem sdp_le_length (l : List ℕ) : sdp l ≤ l.length := by
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: t =>
    rw [sdp_cons_cons]
    have := sdp_le_length (b :: t)
    simp only [List.length_cons] at *
    split
    · omega
    · omega

/-- The maximal strictly-decreasing prefix (of length `sdp l`) is a chain. -/
theorem take_sdp_chain (l : List ℕ) : (l.take (sdp l)).IsChain (· > ·) := by
  match l with
  | [] => simp [List.isChain_nil]
  | [a] => exact List.isChain_singleton _
  | a :: b :: t =>
    rw [sdp_cons_cons]
    split
    · rename_i hba
      have ih := take_sdp_chain (b :: t)
      have : (a :: b :: t).take (1 + sdp (b :: t)) = a :: ((b :: t).take (sdp (b::t))) := by
        rw [Nat.add_comm]; simp [List.take_cons]
      rw [this]
      rw [List.isChain_cons]
      refine ⟨?_, ih⟩
      intro y hy
      have hsdp : 0 < sdp (b :: t) := sdp_pos (by simp)
      rw [List.take_cons (by omega : 0 < sdp (b::t))] at hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      omega
    · simp [List.isChain_singleton]

/-- Any prefix of length `i ≤ sdp l` is a chain. -/
theorem take_chain_of_le {l : List ℕ} {i : ℕ} (h : i ≤ sdp l) :
    (l.take i).IsChain (· > ·) := by
  have := take_sdp_chain l
  have heq : (l.take i) = (l.take (sdp l)).take i := by
    rw [List.take_take]; congr 1; omega
  rw [heq]
  exact this.take i

/-- Inserting the (strict) maximum `M` at a position `i ≤ sdp l` preserves avoidance. -/
theorem avoids_insert {l : List ℕ} {M i : ℕ} (hlt : ∀ x ∈ l, x < M)
    (hi : i ≤ sdp l) (hav : AvoidsWI3 l) :
    AvoidsWI3 (l.take i ++ M :: l.drop i) := by
  -- strictly decreasing prefix
  have hpair : (l.take i).Pairwise (· > ·) :=
    (List.isChain_iff_pairwise).1 (take_chain_of_le hi)
  have hdec : ∀ {x y}, [x, y] <+ l.take i → y < x := by
    intro x y hs
    exact (List.pairwise_iff_forall_sublist.1 hpair) hs
  intro a b c hab hbc hsub
  rw [List.sublist_append_iff] at hsub
  obtain ⟨p, q, hpq, hp, hq⟩ := hsub
  rw [List.sublist_cons_iff] at hq
  rcases hq with hq | ⟨r, hr, hrsub⟩
  · -- M not used: combine to sublist of l
    have : [a, b, c] <+ l := by
      have : p ++ q <+ l.take i ++ l.drop i := List.Sublist.append hp hq
      rw [List.take_append_drop] at this
      rwa [← hpq] at this
    exact hav a b c hab hbc this
  · -- q = M :: r, so M is at index p.length in [a,b,c]
    have hr_in : ∀ x ∈ r, x < M := by
      intro x hx
      exact hlt x (List.mem_of_mem_drop (hrsub.subset hx))
    rw [hr] at hpq
    -- hpq : [a, b, c] = p ++ M :: r
    rcases p with _ | ⟨x, _ | ⟨y, _ | ⟨z, p⟩⟩⟩
    · -- p = [], a = M, r = [b,c]
      simp only [List.nil_append, List.cons.injEq] at hpq
      obtain ⟨ha, hrbc⟩ := hpq
      have : b < M := hr_in b (by rw [← hrbc]; simp)
      omega
    · -- p = [x], a = x, b = M, r = [c]
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpq
      obtain ⟨_, hb, hrc⟩ := hpq
      have : c < M := hr_in c (by rw [← hrc]; simp)
      omega
    · -- p = [x,y] = [a,b], c = M, use strictly decreasing
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpq
      obtain ⟨hxa, hyb, _, _⟩ := hpq
      subst hxa; subst hyb
      have : b < a := hdec hp
      omega
    · -- p length ≥ 3: impossible
      simp only [List.cons_append, List.cons.injEq] at hpq
      obtain ⟨_, _, _, hnil⟩ := hpq
      exact absurd hnil (by simp)

/-- All lists of length `L` with entries `< B`. -/
def boundedLists : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | (L+1), B => (Finset.range B).biUnion (fun x => (boundedLists L B).image (x :: ·))

theorem mem_boundedLists {L B : ℕ} {l : List ℕ} :
    l ∈ boundedLists L B ↔ l.length = L ∧ ∀ x ∈ l, x < B := by
  induction L generalizing l with
  | zero =>
    simp only [boundedLists, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · intro ⟨h, _⟩; exact List.length_eq_zero_iff.1 h
  | succ L ih =>
    simp only [boundedLists, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, l', hl', rfl⟩
      rw [ih] at hl'
      refine ⟨by simp [hl'.1], ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hl'.2 y hy
    · rintro ⟨hlen, hmem⟩
      match l with
      | [] => simp at hlen
      | y :: t =>
        refine ⟨y, hmem y (by simp), t, ?_, rfl⟩
        rw [ih]
        refine ⟨by simpa using hlen, ?_⟩
        intro z hz; exact hmem z (by simp [hz])

open scoped Classical in
/-- Valid sequence: length `L`, entries in `[1,M]`, covering all of `{1,…,M}`, avoiding. -/
def IsValidML (M L : ℕ) (l : List ℕ) : Prop :=
  l.length = L ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ M) ∧ (∀ v, 1 ≤ v → v ≤ M → v ∈ l) ∧ AvoidsWI3 l

open scoped Classical in
/-- Finset of valid sequences with max `M` and length `L`. -/
noncomputable def Dfs (M L : ℕ) : Finset (List ℕ) :=
  (boundedLists L (M+1)).filter (IsValidML M L)

open scoped Classical in
theorem mem_Dfs {M L : ℕ} {l : List ℕ} : l ∈ Dfs M L ↔ IsValidML M L l := by
  unfold Dfs
  rw [Finset.mem_filter, mem_boundedLists]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨⟨h.1, ?_⟩, h⟩
    intro x hx
    have := (h.2.1 x hx).2
    omega

/-- Sublist of an avoider is an avoider. -/
theorem AvoidsWI3.sublist {l l' : List ℕ} (h : AvoidsWI3 l) (hs : l' <+ l) :
    AvoidsWI3 l' := by
  intro a b c hab hbc hsub
  exact h a b c hab hbc (hsub.trans hs)

/-- Remove all copies of the maximum `M`. -/
def removeMax (M : ℕ) (l : List ℕ) : List ℕ := l.filter (fun x => decide (x ≠ M))

theorem mem_removeMax {M : ℕ} {l : List ℕ} {x : ℕ} :
    x ∈ removeMax M l ↔ x ∈ l ∧ x ≠ M := by
  simp [removeMax, List.mem_filter]

theorem removeMax_sublist {M : ℕ} {l : List ℕ} : removeMax M l <+ l := List.filter_sublist

open scoped Classical in
/-- In a valid sequence (M ≥ 1) the max appears once or twice. -/
theorem count_le_two {M L : ℕ} {l : List ℕ} (h : l ∈ Dfs M L) : l.count M ≤ 2 := by
  by_contra hc
  push_neg at hc
  have : List.replicate 3 M <+ l := List.replicate_sublist_iff.2 (by omega)
  rw [mem_Dfs] at h
  exact h.2.2.2 M M M (le_refl _) (le_refl _) (by simpa using this)

open scoped Classical in
theorem count_pos {M L : ℕ} (hM : 1 ≤ M) {l : List ℕ} (h : l ∈ Dfs M L) : 1 ≤ l.count M := by
  rw [mem_Dfs] at h
  rw [List.one_le_count_iff]
  exact h.2.2.1 M hM (le_refl _)

theorem removeMax_length (M : ℕ) (l : List ℕ) :
    (removeMax M l).length + l.count M = l.length := by
  induction l with
  | nil => simp [removeMax]
  | cons x t ih =>
    simp only [removeMax, List.filter_cons, List.count_cons] at *
    by_cases hx : x = M <;> simp only [hx] at * <;>
      simp only [decide_not, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
        if_false, if_true, List.length_cons, decide_true, beq_iff_eq] at * <;>
      by_cases hx2 : x == M <;> simp_all <;> omega

open scoped Classical in
theorem removeMax_valid {M L : ℕ} (hM : 1 ≤ M) {l : List ℕ} (h : l ∈ Dfs M L) :
    removeMax M l ∈ Dfs (M-1) (l.length - l.count M) := by
  rw [mem_Dfs] at h ⊢
  obtain ⟨hlen, hbd, hcov, hav⟩ := h
  refine ⟨?_, ?_, ?_, hav.sublist removeMax_sublist⟩
  · have := removeMax_length M l; omega
  · intro x hx
    rw [mem_removeMax] at hx
    have := hbd x hx.1
    omega
  · intro v hv1 hv2
    rw [mem_removeMax]
    exact ⟨hcov v hv1 (by omega), by omega⟩

theorem sdp_cons_lt {a b : ℕ} {t : List ℕ} (h : b < a) :
    sdp (a :: b :: t) = 1 + sdp (b :: t) := by rw [sdp_cons_cons, if_pos h]

theorem sdp_cons_ge {a b : ℕ} {t : List ℕ} (h : ¬ b < a) :
    sdp (a :: b :: t) = 1 := by rw [sdp_cons_cons, if_neg h]

/-- Prepending the strict maximum to a list of smaller values: `sdp (M :: u) = 1 + sdp u`. -/
theorem sdp_cons_max {M : ℕ} {u : List ℕ} (h : ∀ x ∈ u, x < M) :
    sdp (M :: u) = 1 + sdp u := by
  match u with
  | [] => simp
  | x :: t =>
    rw [sdp_cons_lt (h x (by simp))]

/-- `sdp` of a strictly-decreasing (chain) nonempty prefix followed by the max. -/
theorem sdp_append_max {M : ℕ} {p rest : List ℕ} (hp : p ≠ [])
    (hchain : p.IsChain (· > ·)) (hlt : ∀ x ∈ p, x < M) :
    sdp (p ++ M :: rest) = p.length := by
  match p, hp with
  | [a], _ =>
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [sdp_cons_ge (by have := hlt a (by simp); omega)]
  | a :: b :: p', _ =>
    have hab : a > b := hchain.rel_head
    simp only [List.cons_append]
    rw [sdp_cons_lt hab]
    have ih := sdp_append_max (M := M) (p := b :: p') (rest := rest) (by simp)
      (hchain.of_cons) (fun x hx => hlt x (by simp [hx]))
    simp only [List.cons_append] at ih
    rw [ih]
    simp only [List.length_cons]; omega

def insert1 (M : ℕ) (u : List ℕ) (i : ℕ) : List ℕ := u.take i ++ M :: u.drop i
def insert2 (M : ℕ) (u : List ℕ) (i : ℕ) : List ℕ := M :: (u.take i ++ M :: u.drop i)

@[simp] theorem insert1_length (M : ℕ) (u : List ℕ) (i : ℕ) :
    (insert1 M u i).length = u.length + 1 := by
  simp only [insert1, List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

@[simp] theorem insert2_length (M : ℕ) (u : List ℕ) (i : ℕ) :
    (insert2 M u i).length = u.length + 2 := by
  simp only [insert2, List.length_cons, insert1_length]
  have := insert1_length M u i
  simp only [insert1, List.length_append, List.length_cons, List.length_take,
    List.length_drop] at *
  omega

theorem removeMax_eq_self {M : ℕ} {l : List ℕ} (h : ∀ x ∈ l, x < M) : removeMax M l = l := by
  rw [removeMax, List.filter_eq_self]
  intro a ha
  have := h a ha
  simp; omega

theorem removeMax_append (M : ℕ) (a b : List ℕ) :
    removeMax M (a ++ b) = removeMax M a ++ removeMax M b := List.filter_append _ _

theorem removeMax_cons_self (M : ℕ) (l : List ℕ) :
    removeMax M (M :: l) = removeMax M l := by
  rw [removeMax, List.filter_cons_of_neg (by simp), ← removeMax]

theorem removeMax_insert1 {M : ℕ} {u : List ℕ} {i : ℕ} (h : ∀ x ∈ u, x < M) :
    removeMax M (insert1 M u i) = u := by
  have hlt_take : ∀ x ∈ u.take i, x < M := fun x hx => h x (List.mem_of_mem_take hx)
  have hlt_drop : ∀ x ∈ u.drop i, x < M := fun x hx => h x (List.mem_of_mem_drop hx)
  rw [insert1, removeMax_append, removeMax_cons_self,
    removeMax_eq_self hlt_take, removeMax_eq_self hlt_drop, List.take_append_drop]

theorem removeMax_insert2 {M : ℕ} {u : List ℕ} {i : ℕ} (h : ∀ x ∈ u, x < M) :
    removeMax M (insert2 M u i) = u := by
  rw [insert2, removeMax_cons_self]
  exact removeMax_insert1 h

theorem sdp_cons_of_lt_head {M : ℕ} {w : List ℕ} (hne : w ≠ [])
    (hh : ∀ y ∈ w.head?, y < M) : sdp (M :: w) = 1 + sdp w := by
  match w with
  | b :: w' =>
    have : b < M := hh b (by simp)
    rw [sdp_cons_lt this]

theorem take_length_eq {i : ℕ} {u : List ℕ} (hiu : i ≤ u.length) : (u.take i).length = i := by
  rw [List.length_take]; omega

theorem sdp_insert1 {M : ℕ} {u : List ℕ} {i : ℕ} (hlt : ∀ x ∈ u, x < M) (hi : i ≤ sdp u) :
    sdp (insert1 M u i) = if i = 0 then 1 + sdp u else i := by
  have hiu : i ≤ u.length := le_trans hi (sdp_le_length u)
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp only [insert1, List.take_zero, List.nil_append, List.drop_zero, if_true]
    exact sdp_cons_max hlt
  · rw [if_neg (by omega)]
    have hne : u.take i ≠ [] := by
      intro hc; have := take_length_eq hiu; rw [hc] at this; simp at this; omega
    have hchain : (u.take i).IsChain (· > ·) := take_chain_of_le hi
    have hlt' : ∀ x ∈ u.take i, x < M := fun x hx => hlt x (List.mem_of_mem_take hx)
    rw [insert1, sdp_append_max hne hchain hlt', take_length_eq hiu]

theorem sdp_insert2 {M : ℕ} {u : List ℕ} {i : ℕ} (hlt : ∀ x ∈ u, x < M) (hi : i ≤ sdp u) :
    sdp (insert2 M u i) = i + 1 := by
  have hiu : i ≤ u.length := le_trans hi (sdp_le_length u)
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp only [insert2, List.take_zero, List.nil_append, List.drop_zero]
    rw [sdp_cons_ge (by omega)]
  · have hne : u.take i ≠ [] := by
      intro hc; have := take_length_eq hiu; rw [hc] at this; simp at this; omega
    have hchain : (u.take i).IsChain (· > ·) := take_chain_of_le hi
    have hlt' : ∀ x ∈ u.take i, x < M := fun x hx => hlt x (List.mem_of_mem_take hx)
    have hw : (insert1 M u i) ≠ [] := by
      intro hc; have := insert1_length M u i; rw [hc] at this; simp at this
    have hhead : ∀ y ∈ (insert1 M u i).head?, y < M := by
      intro y hy
      -- head of insert1 = head of u.take i (nonempty)
      match hh : u.take i, hne with
      | c :: rest, _ =>
        rw [insert1, hh] at hy
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact hlt' c (by rw [hh]; simp)
    rw [insert2, ← insert1, sdp_cons_of_lt_head hw hhead,
      sdp_insert1 hlt hi, if_neg (by omega)]
    omega

/-- Prepending the maximum `M` (appearing at most once in `w`) preserves avoidance. -/
theorem avoids_cons_max {M : ℕ} {w : List ℕ} (hav : AvoidsWI3 w) (hle : ∀ x ∈ w, x ≤ M)
    (hc : w.count M ≤ 1) : AvoidsWI3 (M :: w) := by
  intro a b c hab hbc hsub
  rw [List.sublist_cons_iff] at hsub
  rcases hsub with hs | ⟨r, hr, hrsub⟩
  · exact hav a b c hab hbc hs
  · -- hr : [a,b,c] = M :: r
    simp only [List.cons.injEq] at hr
    obtain ⟨ha, hrbc⟩ := hr
    have hbc_sub : [b, c] <+ w := by rw [hrbc]; exact hrsub
    have hbmem : b ∈ w := hbc_sub.subset (by simp)
    have hcmem : c ∈ w := hbc_sub.subset (by simp)
    have hbM : b = M := le_antisymm (hle b hbmem) (ha ▸ hab)
    have hcM : c = M := le_antisymm (hle c hcmem) (hbM ▸ hbc)
    have : List.replicate 2 M <+ w := by
      have : [b, c] = List.replicate 2 M := by rw [hbM, hcM]; rfl
      rwa [this] at hbc_sub
    have := List.replicate_sublist_iff.1 this
    omega

theorem count_M_insert1 {M : ℕ} {u : List ℕ} {i : ℕ} (h : ∀ x ∈ u, x < M) :
    (insert1 M u i).count M = 1 := by
  have hcu : u.count M = 0 := by
    rw [List.count_eq_zero]
    intro hc; exact absurd (h M hc) (by omega)
  have htake : (u.take i).count M = 0 :=
    Nat.le_zero.1 (hcu ▸ List.Sublist.count_le M (List.take_sublist _ _))
  have hdrop : (u.drop i).count M = 0 :=
    Nat.le_zero.1 (hcu ▸ List.Sublist.count_le M (List.drop_sublist _ _))
  rw [insert1, List.count_append, List.count_cons_self]
  omega

theorem count_M_insert2 {M : ℕ} {u : List ℕ} {i : ℕ} (h : ∀ x ∈ u, x < M) :
    (insert2 M u i).count M = 2 := by
  rw [show insert2 M u i = M :: insert1 M u i from rfl, List.count_cons_self,
    count_M_insert1 h]

theorem entries_lt {M L : ℕ} (hM : 1 ≤ M) {u : List ℕ} (h : u ∈ Dfs (M-1) L) :
    ∀ x ∈ u, x < M := by
  rw [mem_Dfs] at h
  intro x hx
  have := (h.2.1 x hx).2
  omega

theorem mem_insert1_of_mem {M : ℕ} {u : List ℕ} {i : ℕ} {x : ℕ} (hx : x ∈ u) :
    x ∈ insert1 M u i := by
  rw [insert1]
  have hx' : x ∈ u.take i ++ u.drop i := by rwa [List.take_append_drop]
  rcases List.mem_append.1 hx' with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (by simp [h])

open scoped Classical in
theorem insert1_valid {M L : ℕ} (hM : 1 ≤ M) {u : List ℕ} (h : u ∈ Dfs (M-1) L)
    (hi : i ≤ sdp u) : insert1 M u i ∈ Dfs M (L + 1) := by
  have hlt := entries_lt hM h
  rw [mem_Dfs] at h ⊢
  obtain ⟨hlen, hbd, hcov, hav⟩ := h
  refine ⟨by rw [insert1_length]; omega, ?_, ?_, ?_⟩
  · intro x hx
    rw [insert1] at hx
    rcases List.mem_append.1 hx with h1 | h1
    · have := hbd x (List.mem_of_mem_take h1); omega
    · rcases List.mem_cons.1 h1 with rfl | h2
      · exact ⟨hM, le_refl _⟩
      · have := hbd x (List.mem_of_mem_drop h2); omega
  · intro v hv1 hv2
    rcases Nat.lt_or_ge v M with hvlt | hvge
    · exact mem_insert1_of_mem (hcov v hv1 (by omega))
    · have : v = M := by omega
      subst this
      rw [insert1]
      exact List.mem_append_right _ (by simp)
  · exact avoids_insert hlt hi hav

open scoped Classical in
theorem insert2_valid {M L : ℕ} (hM : 1 ≤ M) {u : List ℕ} (h : u ∈ Dfs (M-1) L)
    (hi : i ≤ sdp u) : insert2 M u i ∈ Dfs M (L + 2) := by
  have hlt := entries_lt hM h
  have h1 : insert1 M u i ∈ Dfs M (L + 1) := insert1_valid hM h hi
  rw [mem_Dfs] at h1
  obtain ⟨hlen, hbd, hcov, hav⟩ := h1
  rw [show insert2 M u i = M :: insert1 M u i from rfl, mem_Dfs]
  refine ⟨by rw [List.length_cons, hlen], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | h2
    · exact ⟨hM, le_refl _⟩
    · exact hbd x h2
  · intro v hv1 hv2
    exact List.mem_cons_of_mem _ (hcov v hv1 hv2)
  · exact avoids_cons_max hav (fun x hx => (hbd x hx).2) (by rw [count_M_insert1 hlt])

/-- Converse of `take_chain_of_le`: a chain prefix of length `i` bounds `sdp` below. -/
theorem chain_prefix_le_sdp {l : List ℕ} {i : ℕ} (hc : (l.take i).IsChain (· > ·))
    (hi : i ≤ l.length) : i ≤ sdp l := by
  match l with
  | [] => simpa using hi
  | [a] => simp only [List.length_cons, List.length_nil] at hi; simp [sdp]; omega
  | a :: b :: t =>
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · have := sdp_pos (l := a :: b :: t) (by simp); omega
    · -- i ≥ 2
      have hbt : b < a := by
        have : (a :: b :: t).take i = a :: b :: (t.take (i-2)) := by
          have : i = (i - 2) + 2 := by omega
          rw [this]; simp [List.take_cons]
        rw [this] at hc
        exact hc.rel_head
      rw [sdp_cons_lt hbt]
      have htail : ((b :: t).take (i - 1)).IsChain (· > ·) := by
        have he : (a :: b :: t).take i = a :: ((b :: t).take (i-1)) := by
          have : i = (i - 1) + 1 := by omega
          rw [this]; simp [List.take_cons]
        rw [he] at hc
        exact hc.of_cons
      have := chain_prefix_le_sdp htail (by simp only [List.length_cons] at hi ⊢; omega)
      omega

/-- The prefix of a valid sequence before an occurrence of the maximum is strictly decreasing. -/
theorem prefix_chain_of_max {M : ℕ} {l : List ℕ} {k : ℕ} (hav : AvoidsWI3 l)
    (hle : ∀ x ∈ l, x ≤ M) (hk : k < l.length) (hkM : l[k] = M) :
    (l.take k).IsChain (· > ·) := by
  rw [List.isChain_iff_pairwise, List.pairwise_iff_forall_sublist]
  intro a b hs
  by_contra hcon
  push_neg at hcon
  have hbmem : b ∈ l.take k := hs.subset (by simp)
  have hbM : b ≤ M := hle b (List.mem_of_mem_take hbmem)
  have hsub : [a, b, M] <+ l := by
    have h1 : [a, b] ++ [M] <+ (l.take k) ++ [l[k]] := List.Sublist.append hs (by rw [hkM])
    rw [List.take_append_getElem hk] at h1
    exact h1.trans (List.take_sublist _ _)
  exact hav a b M hcon hbM hsub

open scoped Classical in
/-- Reconstruction: a valid list where `M` appears once is `insert1` of its `removeMax`. -/
theorem once_recon {M L : ℕ} (hM : 1 ≤ M) {l : List ℕ} (hl : l ∈ Dfs M L) (hc : l.count M = 1) :
    ∃ q, q ≤ sdp (removeMax M l) ∧ l = insert1 M (removeMax M l) q := by
  have hlmem := hl
  rw [mem_Dfs] at hl
  obtain ⟨hlen, hbd, hcov, hav⟩ := hl
  have hle : ∀ x ∈ l, x ≤ M := fun x hx => (hbd x hx).2
  have hM_mem : M ∈ l := List.one_le_count_iff.1 (by omega)
  obtain ⟨as, bs, hsplit, hMas⟩ := List.eq_append_cons_of_mem hM_mem
  subst hsplit
  -- M ∉ bs from count = 1
  have hcas : as.count M = 0 := List.count_eq_zero.2 hMas
  have hcbs : bs.count M = 0 := by
    have heq : count M (as ++ M :: bs) = as.count M + (bs.count M + 1) := by
      rw [List.count_append, List.count_cons_self]
    rw [heq] at hc; omega
  have hMbs : M ∉ bs := List.count_eq_zero.1 hcbs
  have has_lt : ∀ x ∈ as, x < M := by
    intro x hx
    have : x ≤ M := hle x (List.mem_append_left _ hx)
    rcases eq_or_lt_of_le this with rfl | h
    · exact absurd hx hMas
    · exact h
  have hbs_lt : ∀ x ∈ bs, x < M := by
    intro x hx
    have : x ≤ M := hle x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    rcases eq_or_lt_of_le this with rfl | h
    · exact absurd hx hMbs
    · exact h
  -- u = removeMax l = as ++ bs
  have hu : removeMax M (as ++ M :: bs) = as ++ bs := by
    rw [removeMax_append, removeMax_cons_self, removeMax_eq_self has_lt,
      removeMax_eq_self hbs_lt]
  refine ⟨as.length, ?_, ?_⟩
  · rw [hu]
    have hk : as.length < (as ++ M :: bs).length := by
      simp only [List.length_append, List.length_cons]; omega
    have hkM : (as ++ M :: bs)[as.length] = M := by
      rw [List.getElem_append_right (by omega)]; simp
    have hchain : ((as ++ M :: bs).take as.length).IsChain (· > ·) :=
      prefix_chain_of_max hav hle hk hkM
    have htake : (as ++ M :: bs).take as.length = as := by rw [List.take_left']; rfl
    rw [htake] at hchain
    have : ((as ++ bs).take as.length).IsChain (· > ·) := by
      rw [List.take_left]; exact hchain
    exact chain_prefix_le_sdp this (by simp)
  · rw [hu, insert1, List.take_left, List.drop_left]

theorem getElem_append_cons (p : List ℕ) (a : ℕ) (t : List ℕ) :
    (p ++ a :: t)[p.length]'(by simp only [List.length_append, List.length_cons]; omega) = a := by
  rw [List.getElem_append_right (le_refl _)]
  simp

open scoped Classical in
/-- Reconstruction: a valid list where `M` appears twice is `insert2` of its `removeMax`;
moreover the first `M` is at the front. -/
theorem twice_recon {M L : ℕ} (hM : 1 ≤ M) {l : List ℕ} (hl : l ∈ Dfs M L) (hc : l.count M = 2) :
    ∃ q, q ≤ sdp (removeMax M l) ∧ l = insert2 M (removeMax M l) q := by
  rw [mem_Dfs] at hl
  obtain ⟨hlen, hbd, hcov, hav⟩ := hl
  have hle : ∀ x ∈ l, x ≤ M := fun x hx => (hbd x hx).2
  have hM_mem : M ∈ l := List.one_le_count_iff.1 (by omega)
  obtain ⟨as, bs, hsplit, hMas⟩ := List.eq_append_cons_of_mem hM_mem
  subst hsplit
  have hcas : as.count M = 0 := List.count_eq_zero.2 hMas
  -- bs has count 1, so contains M
  have hcbs : bs.count M = 1 := by
    have heq : count M (as ++ M :: bs) = as.count M + (bs.count M + 1) := by
      rw [List.count_append, List.count_cons_self]
    rw [heq] at hc; omega
  have hbs_mem : M ∈ bs := List.one_le_count_iff.1 (by omega)
  obtain ⟨cs, ds, hsplit2, hMcs⟩ := List.eq_append_cons_of_mem hbs_mem
  subst hsplit2
  have hccs : cs.count M = 0 := List.count_eq_zero.2 hMcs
  have hcds : ds.count M = 0 := by
    have heq2 : count M (cs ++ M :: ds) = count M cs + (ds.count M + 1) := by
      rw [List.count_append, List.count_cons_self]
    rw [heq2] at hcbs; omega
  have hMds : M ∉ ds := List.count_eq_zero.1 hcds
  -- lt facts (membership in the nested form)
  have hcs_lt : ∀ x ∈ cs, x < M := by
    intro x hx
    have hxle : x ≤ M := hle x
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    rcases eq_or_lt_of_le hxle with rfl | h
    · exact absurd hx hMcs
    · exact h
  have hds_lt : ∀ x ∈ ds, x < M := by
    intro x hx
    have hxle : x ≤ M := hle x
      (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_cons_of_mem _ hx))))
    rcases eq_or_lt_of_le hxle with rfl | h
    · exact absurd hx hMds
    · exact h
  -- rewrite to the "nice" associativity form for prefix computations
  have hL : as ++ M :: (cs ++ M :: ds) = (as ++ M :: cs) ++ M :: ds := by
    simp [List.append_assoc]
  have hav2 : AvoidsWI3 ((as ++ M :: cs) ++ M :: ds) := hL ▸ hav
  have hle2 : ∀ x ∈ (as ++ M :: cs) ++ M :: ds, x ≤ M := hL ▸ hle
  have hk : (as ++ M :: cs).length < ((as ++ M :: cs) ++ M :: ds).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hkM : ((as ++ M :: cs) ++ M :: ds)[(as ++ M :: cs).length] = M :=
    getElem_append_cons (as ++ M :: cs) M ds
  have hchain : (((as ++ M :: cs) ++ M :: ds).take (as ++ M :: cs).length).IsChain (· > ·) :=
    prefix_chain_of_max hav2 hle2 hk hkM
  have htake_k : ((as ++ M :: cs) ++ M :: ds).take (as ++ M :: cs).length = as ++ M :: cs :=
    List.take_left
  rw [htake_k] at hchain
  -- as = []
  have has_nil : as = [] := by
    rcases as with _ | ⟨a, as'⟩
    · rfl
    · exfalso
      rw [List.isChain_iff_pairwise] at hchain
      simp only [List.cons_append, List.pairwise_cons] at hchain
      have haM : a > M := hchain.1 M (List.mem_append_right _ (List.mem_cons_self))
      have : a ≤ M := hle a (by simp)
      omega
  subst has_nil
  simp only [List.nil_append] at hchain ⊢
  -- now l = M :: (cs ++ M :: ds)
  have hu : removeMax M (M :: (cs ++ M :: ds)) = cs ++ ds := by
    rw [removeMax_cons_self, removeMax_append, removeMax_cons_self,
      removeMax_eq_self hcs_lt, removeMax_eq_self hds_lt]
  refine ⟨cs.length, ?_, ?_⟩
  · rw [hu]
    have hcschain : cs.IsChain (· > ·) := hchain.of_cons
    have : ((cs ++ ds).take cs.length).IsChain (· > ·) := by
      rw [List.take_left]; exact hcschain
    exact chain_prefix_le_sdp this (by simp)
  · rw [hu, insert2, List.take_left, List.drop_left]

open scoped Classical in
/-- A valid list covering `{1,…,M}` has length at least `M`. -/
theorem Dfs_len_ge {M L : ℕ} {l : List ℕ} (h : l ∈ Dfs M L) : M ≤ L := by
  rw [mem_Dfs] at h
  obtain ⟨hlen, hbd, hcov, hav⟩ := h
  have hsub : Finset.Icc 1 M ⊆ l.toFinset := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    rw [List.mem_toFinset]
    exact hcov v hv.1 hv.2
  have h1 : (Finset.Icc 1 M).card ≤ l.toFinset.card := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
  simp only [Nat.add_sub_cancel] at h1
  omega

open scoped Classical in
theorem Dfs_eq_empty_of_lt {M L : ℕ} (h : L < M) : Dfs M L = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro l hl
  have := Dfs_len_ge hl
  omega

open scoped Classical in
/-- Number of valid sequences with max `M`, length `M+s`, and `sdp = d`. -/
noncomputable def Ncn (M s d : ℕ) : ℕ :=
  ((Dfs M (M + s)).filter (fun l => sdp l = d)).card

open scoped Classical in
/-- Number of valid sequences with max `M`, length `M+s`, and `sdp ≥ e`. -/
noncomputable def Qcn (M s e : ℕ) : ℕ :=
  ((Dfs M (M + s)).filter (fun l => e ≤ sdp l)).card

open scoped Classical in
/-- The count-1 class of `Dfs (M+1) (M+1+s)` with `sdp = d` biject with `{u ∈ Dfs M (M+s) : sdp u ≥ d-1}`. -/
theorem count1_recursion (M s d : ℕ) (hd : 1 ≤ d) :
    ((Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d ∧ l.count (M+1) = 1)).card
      = Qcn M s (d-1) := by
  rw [Qcn]
  have hM1 : (1:ℕ) ≤ M + 1 := by omega
  -- forward map removes the maximum; inverse re-inserts it at a computed position
  refine Finset.card_nbij'
    (fun l => removeMax (M+1) l)
    (fun u => insert1 (M+1) u (if d = sdp u + 1 then 0 else d))
    ?_ ?_ ?_ ?_
  · -- MapsTo: removeMax lands in target
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl ⊢
    obtain ⟨hldfs, hsdp, hc⟩ := hl
    have hlen : l.length = M + 1 + s := (mem_Dfs.1 hldfs).1
    have hrm : removeMax (M+1) l ∈ Dfs M (M + s) := by
      have := removeMax_valid hM1 hldfs
      rwa [hlen, hc, show M + 1 + s - 1 = M + s by omega,
        show M + 1 - 1 = M from rfl] at this
    refine ⟨hrm, ?_⟩
    show d - 1 ≤ sdp (removeMax (M+1) l)
    obtain ⟨q, hq_le, hqeq⟩ := once_recon hM1 hldfs hc
    have hlt : ∀ x ∈ removeMax (M+1) l, x < M + 1 := entries_lt hM1 hrm
    have hh : sdp l = (if q = 0 then 1 + sdp (removeMax (M+1) l) else q) := by
      conv_lhs => rw [hqeq]
      exact sdp_insert1 hlt hq_le
    rw [hsdp] at hh
    split at hh <;> omega
  · -- MapsTo (inverse): insert1 lands in source
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu ⊢
    obtain ⟨hudfs, hue⟩ := hu
    have hlt : ∀ x ∈ u, x < M + 1 := entries_lt hM1 (by rwa [show M + 1 - 1 = M from rfl])
    have hudfs' : u ∈ Dfs (M+1-1) (M+s) := by rwa [show M+1-1=M from rfl]
    show insert1 (M+1) u (if d = sdp u + 1 then 0 else d) ∈ Dfs (M+1) (M+1+s)
          ∧ sdp (insert1 (M+1) u (if d = sdp u + 1 then 0 else d)) = d
          ∧ (insert1 (M+1) u (if d = sdp u + 1 then 0 else d)).count (M+1) = 1
    by_cases h : d = sdp u + 1
    · rw [if_pos h]
      refine ⟨?_, ?_, count_M_insert1 hlt⟩
      · have := insert1_valid (M:=M+1) hM1 hudfs' (by omega : (0:ℕ) ≤ sdp u)
        rwa [show M+s+1 = M+1+s by omega] at this
      · rw [sdp_insert1 hlt (by omega : (0:ℕ) ≤ sdp u), if_pos rfl]; omega
    · rw [if_neg h]
      have hdle : d ≤ sdp u := by omega
      refine ⟨?_, ?_, count_M_insert1 hlt⟩
      · have := insert1_valid (M:=M+1) hM1 hudfs' hdle
        rwa [show M+s+1 = M+1+s by omega] at this
      · rw [sdp_insert1 hlt hdle, if_neg (by omega : ¬ d = 0)]
  · -- left_inv
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    obtain ⟨hldfs, hsdp, hc⟩ := hl
    show insert1 (M+1) (removeMax (M+1) l) (if d = sdp (removeMax (M+1) l) + 1 then 0 else d) = l
    obtain ⟨q, hq_le, hqeq⟩ := once_recon hM1 hldfs hc
    have hrm : removeMax (M+1) l ∈ Dfs M (M + s) := by
      have hlen : l.length = M + 1 + s := (mem_Dfs.1 hldfs).1
      have := removeMax_valid hM1 hldfs
      rwa [hlen, hc, show M + 1 + s - 1 = M + s by omega, show M + 1 - 1 = M from rfl] at this
    have hlt : ∀ x ∈ removeMax (M+1) l, x < M + 1 := entries_lt hM1 hrm
    have hsdpins : sdp l = (if q = 0 then 1 + sdp (removeMax (M+1) l) else q) := by
      conv_lhs => rw [hqeq]
      exact sdp_insert1 hlt hq_le
    rw [hsdp] at hsdpins
    have hcond : (if d = sdp (removeMax (M+1) l) + 1 then 0 else d) = q := by
      split at hsdpins <;> rename_i hq0
      · subst hq0; rw [if_pos (by omega)]
      · rw [if_neg (by omega)]; omega
    rw [hcond]; exact hqeq.symm
  · -- right_inv
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu
    obtain ⟨hudfs, hue⟩ := hu
    show removeMax (M+1) (insert1 (M+1) u (if d = sdp u + 1 then 0 else d)) = u
    have hlt : ∀ x ∈ u, x < M + 1 := entries_lt hM1 (by rwa [show M + 1 - 1 = M from rfl])
    exact removeMax_insert1 hlt

open scoped Classical in
/-- When `s = 0` (length equals max) the count-2 class is empty. -/
theorem count2_empty (M d : ℕ) :
    ((Dfs (M+1) (M+1+0)).filter (fun l => sdp l = d ∧ l.count (M+1) = 2)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl hp
  have hM1 : (1:ℕ) ≤ M + 1 := by omega
  have hlen : l.length = M + 1 + 0 := (mem_Dfs.1 hl).1
  have hrm := removeMax_valid hM1 hl
  have hge := Dfs_len_ge hrm
  have hlen2 := removeMax_length (M+1) l
  rw [show M + 1 - 1 = M from rfl] at hge
  omega

open scoped Classical in
/-- The count-2 class of `Dfs (M+1) (M+1+(s+1))` with `sdp = d` biject with `{u ∈ Dfs M (M+s) : sdp u ≥ d-1}`. -/
theorem count2_recursion (M s d : ℕ) (hd : 1 ≤ d) :
    ((Dfs (M+1) (M+1+(s+1))).filter (fun l => sdp l = d ∧ l.count (M+1) = 2)).card
      = Qcn M s (d-1) := by
  rw [Qcn]
  have hM1 : (1:ℕ) ≤ M + 1 := by omega
  refine Finset.card_nbij'
    (fun l => removeMax (M+1) l)
    (fun u => insert2 (M+1) u (d-1))
    ?_ ?_ ?_ ?_
  · -- MapsTo
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl ⊢
    obtain ⟨hldfs, hsdp, hc⟩ := hl
    have hlen : l.length = M + 1 + (s+1) := (mem_Dfs.1 hldfs).1
    have hrm : removeMax (M+1) l ∈ Dfs M (M + s) := by
      have := removeMax_valid hM1 hldfs
      rwa [hlen, hc, show M + 1 + (s+1) - 2 = M + s by omega,
        show M + 1 - 1 = M from rfl] at this
    refine ⟨hrm, ?_⟩
    show d - 1 ≤ sdp (removeMax (M+1) l)
    obtain ⟨q, hq_le, hqeq⟩ := twice_recon hM1 hldfs hc
    have hlt : ∀ x ∈ removeMax (M+1) l, x < M + 1 := entries_lt hM1 hrm
    have hh : sdp l = q + 1 := by
      conv_lhs => rw [hqeq]
      exact sdp_insert2 hlt hq_le
    rw [hsdp] at hh
    omega
  · -- MapsTo (inverse)
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu ⊢
    obtain ⟨hudfs, hue⟩ := hu
    have hlt : ∀ x ∈ u, x < M + 1 := entries_lt hM1 (by rwa [show M + 1 - 1 = M from rfl])
    have hudfs' : u ∈ Dfs (M+1-1) (M+s) := by rwa [show M+1-1=M from rfl]
    have hdle : d - 1 ≤ sdp u := hue
    show insert2 (M+1) u (d-1) ∈ Dfs (M+1) (M+1+(s+1))
          ∧ sdp (insert2 (M+1) u (d-1)) = d
          ∧ (insert2 (M+1) u (d-1)).count (M+1) = 2
    refine ⟨?_, ?_, count_M_insert2 hlt⟩
    · have := insert2_valid (M:=M+1) hM1 hudfs' hdle
      rwa [show M+s+2 = M+1+(s+1) by omega] at this
    · rw [sdp_insert2 hlt hdle]; omega
  · -- left_inv
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    obtain ⟨hldfs, hsdp, hc⟩ := hl
    show insert2 (M+1) (removeMax (M+1) l) (d-1) = l
    obtain ⟨q, hq_le, hqeq⟩ := twice_recon hM1 hldfs hc
    have hrm : removeMax (M+1) l ∈ Dfs M (M + s) := by
      have hlen : l.length = M + 1 + (s+1) := (mem_Dfs.1 hldfs).1
      have := removeMax_valid hM1 hldfs
      rwa [hlen, hc, show M + 1 + (s+1) - 2 = M + s by omega, show M + 1 - 1 = M from rfl] at this
    have hlt : ∀ x ∈ removeMax (M+1) l, x < M + 1 := entries_lt hM1 hrm
    have hh : sdp l = q + 1 := by
      conv_lhs => rw [hqeq]
      exact sdp_insert2 hlt hq_le
    rw [hsdp] at hh
    have : d - 1 = q := by omega
    rw [this]; exact hqeq.symm
  · -- right_inv
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu
    obtain ⟨hudfs, hue⟩ := hu
    show removeMax (M+1) (insert2 (M+1) u (d-1)) = u
    have hlt : ∀ x ∈ u, x < M + 1 := entries_lt hM1 (by rwa [show M + 1 - 1 = M from rfl])
    exact removeMax_insert2 hlt

open scoped Classical in
/-- Partition the `sdp = d` class by the count of the maximum (1 or 2). -/
theorem Ncn_split (M s d : ℕ) :
    Ncn (M+1) s d
      = ((Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d ∧ l.count (M+1) = 1)).card
        + ((Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d ∧ l.count (M+1) = 2)).card := by
  rw [Ncn]
  have hpart : (Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d)
      = (Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d ∧ l.count (M+1) = 1)
        ∪ (Dfs (M+1) (M+1+s)).filter (fun l => sdp l = d ∧ l.count (M+1) = 2) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro l hl
    have h1 := count_pos (by omega : (1:ℕ) ≤ M+1) hl
    have h2 := count_le_two hl
    constructor
    · intro hs
      rcases (by omega : l.count (M+1) = 1 ∨ l.count (M+1) = 2) with hc | hc
      · exact Or.inl ⟨hs, hc⟩
      · exact Or.inr ⟨hs, hc⟩
    · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
  rw [hpart, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro l _ h1 h2
  omega

open scoped Classical in
theorem Ncn_rec0 (M d : ℕ) (hd : 1 ≤ d) : Ncn (M+1) 0 d = Qcn M 0 (d-1) := by
  rw [Ncn_split, count1_recursion M 0 d hd, count2_empty M d, Nat.add_zero]

open scoped Classical in
theorem Ncn_recS (M s d : ℕ) (hd : 1 ≤ d) :
    Ncn (M+1) (s+1) d = Qcn M (s+1) (d-1) + Qcn M s (d-1) := by
  rw [Ncn_split, count1_recursion M (s+1) d hd, count2_recursion M s d hd]

/-- Ballot numbers: `Bnum M d` will equal the count of valid single-occurrence
sequences (permutations, `s=0`) with max `M` and `sdp = d`. -/
def Bnum : ℕ → ℕ → ℕ
  | 0 => fun d => if d = 0 then 1 else 0
  | (M+1) => fun d =>
      if d = 0 then 0 else ∑ d' ∈ Finset.range (M+1), if d - 1 ≤ d' then Bnum M d' else 0

/-- Tail sums of ballot numbers. -/
def Qbal (M e : ℕ) : ℕ := ∑ d ∈ Finset.range (M+1), if e ≤ d then Bnum M d else 0

theorem Bnum_succ (M d : ℕ) : Bnum (M+1) d = if d = 0 then 0 else Qbal M (d-1) := by
  rw [Bnum, Qbal]

theorem Bnum_zero_of_lt : ∀ M d, M < d → Bnum M d = 0
  | 0, d, h => by simp only [Bnum]; rw [if_neg (by omega)]
  | (M+1), d, h => by
      simp only [Bnum]; rw [if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro d' hd'
      rw [Finset.mem_range] at hd'
      rw [if_neg (by omega)]

open scoped Classical in
theorem Dfs_zero_zero : Dfs 0 0 = {[]} := by
  ext l
  rw [Finset.mem_singleton, mem_Dfs]
  constructor
  · rintro ⟨hlen, _, _, _⟩; exact List.length_eq_zero_iff.1 hlen
  · rintro rfl
    exact ⟨rfl, by simp, by intro v h1 h2; omega, by intro a b c _ _ h; simp at h⟩

open scoped Classical in
theorem Dfs_zero_succ (s : ℕ) : Dfs 0 (s+1) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro l hl
  rw [mem_Dfs] at hl
  obtain ⟨hlen, hbd, _, _⟩ := hl
  match l with
  | [] => simp at hlen
  | x :: t => have := hbd x (by simp); omega

open scoped Classical in
/-- `Qcn` as a sum over the possible `sdp` values. -/
theorem Qcn_eq_sum (M s e : ℕ) :
    Qcn M s e = ∑ d ∈ Finset.range (M+s+1), if e ≤ d then Ncn M s d else 0 := by
  rw [Qcn]
  rw [Finset.card_eq_sum_card_fiberwise (f := sdp) (t := Finset.range (M+s+1)) ?_]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.filter_filter]
    by_cases he : e ≤ d
    · rw [if_pos he, Ncn]
      congr 1
      apply Finset.filter_congr
      intro l _
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact he, h⟩
    · rw [if_neg he, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro l _ ⟨h1, h2⟩
      rw [h2] at h1; exact he h1
  · intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    rw [Finset.mem_coe, Finset.mem_range]
    have h1 := (mem_Dfs.1 hl.1).1
    have h2 := sdp_le_length l
    omega

open scoped Classical in
/-- The closed form for `Qcn` derived from the closed form for `Ncn`. -/
theorem Qcn_closed_of {M : ℕ} (hN : ∀ s d, Ncn M s d = Nat.choose M s * Bnum M d) (s e : ℕ) :
    Qcn M s e = Nat.choose M s * Qbal M e := by
  rw [Qcn_eq_sum, Qbal, Finset.mul_sum]
  rw [Finset.sum_subset (show Finset.range (M+1) ⊆ Finset.range (M+s+1) by
        intro x hx; simp only [Finset.mem_range] at *; omega)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [hN s d, mul_ite, Nat.mul_zero]
  · intro x _ hx
    rw [Finset.mem_range, not_lt] at hx
    simp [Bnum_zero_of_lt M x (by omega)]

open scoped Classical in
/-- Master distribution formula: `Ncn M s d = C(M,s) · Bnum M d`. -/
theorem Ncn_closed : ∀ M s d, Ncn M s d = Nat.choose M s * Bnum M d := by
  intro M
  induction M with
  | zero =>
    intro s d
    cases s with
    | zero =>
      rw [Ncn, show (0:ℕ)+0 = 0 from rfl, Dfs_zero_zero, Nat.choose_self, Nat.one_mul]
      simp only [Bnum]
      by_cases hd : d = 0
      · subst hd
        rw [if_pos rfl]
        simp [Finset.filter_singleton]
      · rw [if_neg hd, Finset.filter_singleton,
          if_neg (by simp only [sdp_nil]; omega), Finset.card_empty]
    | succ s =>
      rw [Ncn, Nat.zero_add (s+1), Dfs_zero_succ, Finset.filter_empty,
        Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
  | succ M ih =>
    intro s d
    have hQ := Qcn_closed_of ih
    cases s with
    | zero =>
      by_cases hd : d = 0
      · subst hd
        rw [Bnum_succ, if_pos rfl, Nat.mul_zero, Ncn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l hl
        have hne : l ≠ [] := by
          intro he; have hlen := (mem_Dfs.1 hl).1; rw [he, List.length_nil] at hlen; omega
        have := sdp_pos hne; omega
      · rw [Ncn_rec0 M d (by omega), hQ 0 (d-1), Bnum_succ, if_neg hd,
          Nat.choose_zero_right, Nat.choose_zero_right]
    | succ s =>
      by_cases hd : d = 0
      · subst hd
        rw [Bnum_succ, if_pos rfl, Nat.mul_zero, Ncn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l hl
        have hne : l ≠ [] := by
          intro he; have hlen := (mem_Dfs.1 hl).1; rw [he, List.length_nil] at hlen; omega
        have := sdp_pos hne; omega
      · rw [Ncn_recS M s d (by omega), hQ (s+1) (d-1), hQ s (d-1), Bnum_succ, if_neg hd,
          ← Nat.add_mul, Nat.add_comm (Nat.choose M (s+1)) (Nat.choose M s),
          ← Nat.choose_succ_succ']

theorem Qbal_eq_zero_of_lt {M e : ℕ} (h : M < e) : Qbal M e = 0 := by
  rw [Qbal]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_range] at hd
  rw [if_neg (by omega)]

theorem Qbal_succ_e {M e : ℕ} (h : e ≤ M) : Qbal M e = Qbal M (e+1) + Bnum M e := by
  have hpt : ∀ d, (if e ≤ d then Bnum M d else 0)
      = (if e+1 ≤ d then Bnum M d else 0) + (if d = e then Bnum M d else 0) := by
    intro d
    rcases Nat.lt_trichotomy d e with h|h|h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_pos (by omega : e ≤ d), if_neg (by omega : ¬ e+1 ≤ d), if_pos h]; omega
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; omega
  rw [Qbal, Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq' (Finset.range (M+1)) e (fun d => Bnum M d),
      if_pos (Finset.mem_range.2 (by omega))]

/-- Additive form of the Catalan identity `catalan M = C(2M,M) - C(2M,M+1)`. -/
theorem catalan_add (M : ℕ) :
    catalan M + Nat.choose (2*M) (M+1) = Nat.choose (2*M) M := by
  have h1 : (M+1) * catalan M = Nat.choose (2*M) M := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have h2 : Nat.choose (2*M) (M+1) * (M+1) = Nat.choose (2*M) M * M := by
    have := Nat.choose_succ_right_eq (2*M) M
    rwa [show 2*M - M = M by omega] at this
  have key : (M+1) * (catalan M + Nat.choose (2*M) (M+1)) = (M+1) * Nat.choose (2*M) M := by
    rw [Nat.mul_add, h1, Nat.mul_comm (M+1) (Nat.choose (2*M) (M+1)), h2]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- Closed (additive) form for the tail sums `Qbal`, for `M ≥ 1`. -/
theorem Qbal_closed_add : ∀ {M : ℕ}, 1 ≤ M → ∀ e, e ≤ M+1 →
    Qbal M e + Nat.choose (2*M - e) (M+1) = Nat.choose (2*M - e) M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro e he
    interval_cases e <;> decide
  | succ M hM ih =>
    -- Ballot closed form at level M+1 (valid for all e ≤ M+1, including e = 0).
    have hB : ∀ e, e ≤ M+1 →
        Bnum (M+1) e + Nat.choose (2*M+1-e) (M+1) = Nat.choose (2*M+1-e) M := by
      intro e he
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · subst he0
        rw [Bnum_succ, if_pos rfl, Nat.zero_add, Nat.sub_zero]
        rw [show (M+1 : ℕ) = (2*M+1) - M by omega, Nat.choose_symm (by omega)]
      · rw [Bnum_succ, if_neg (by omega)]
        have := ih (e-1) (by omega)
        rwa [show 2*M - (e-1) = 2*M+1-e by omega] at this
    -- Downward induction on the number of remaining terms.
    have key : ∀ t e, e + t = M + 2 →
        Qbal (M+1) e + Nat.choose (2*(M+1) - e) (M+2) = Nat.choose (2*(M+1) - e) (M+1) := by
      intro t
      induction t with
      | zero =>
        intro e he
        have : e = M+2 := by omega
        subst this
        rw [Qbal_eq_zero_of_lt (by omega), Nat.zero_add,
          Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      | succ t iht =>
        intro e he
        rw [Qbal_succ_e (show e ≤ M+1 by omega)]
        have hrec := iht (e+1) (by omega)
        rw [show 2*(M+1) - (e+1) = 2*M+1-e by omega] at hrec
        have hb := hB e (by omega)
        have pasc1 : Nat.choose (2*M+2-e) (M+2)
            = Nat.choose (2*M+1-e) (M+1) + Nat.choose (2*M+1-e) (M+2) := by
          have h := Nat.choose_succ_succ' (2*M+1-e) (M+1)
          rwa [show (2*M+1-e)+1 = 2*M+2-e by omega] at h
        have pasc2 : Nat.choose (2*M+2-e) (M+1)
            = Nat.choose (2*M+1-e) M + Nat.choose (2*M+1-e) (M+1) := by
          have h := Nat.choose_succ_succ' (2*M+1-e) M
          rwa [show (2*M+1-e)+1 = 2*M+2-e by omega] at h
        rw [show 2*(M+1) - e = 2*M+2-e by omega, pasc1, pasc2]
        omega
    intro e he
    have := key (M+2 - e) e (by omega)
    convert this using 3 <;> omega

theorem Qbal_zero_eq_catalan (M : ℕ) : Qbal M 0 = catalan M := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; rw [Qbal]; simp [Bnum, catalan_zero]
  · have h1 := Qbal_closed_add h 0 (by omega)
    have h2 := catalan_add M
    rw [Nat.sub_zero] at h1
    omega

open scoped Classical in
/-- The master cardinality formula. -/
theorem card_Dfs (M s : ℕ) : (Dfs M (M+s)).card = catalan M * Nat.choose M s := by
  have hQ : (Dfs M (M+s)).card = Qcn M s 0 := by
    rw [Qcn, Finset.filter_true_of_mem (fun l _ => Nat.zero_le _)]
  rw [hQ, Qcn_closed_of (fun s d => Ncn_closed M s d) s 0, Qbal_zero_eq_catalan, Nat.mul_comm]

/-- Local copy of the `Spec.lean` pattern definition (for development). -/
def has_ndp3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length), i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

/-- The pattern condition (via `Fin`-indexed `get`) is the same as the existence of a
weakly-increasing 3-element sublist. -/
theorem has_pattern_iff (l : List ℕ) :
    has_ndp3 l ↔ ∃ a b c, a ≤ b ∧ b ≤ c ∧ [a, b, c] <+ l := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, hab, hbc⟩
    refine ⟨l.get i, l.get j, l.get k, hab, hbc, ?_⟩
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
    have hlen : [l.get i, l.get j, l.get k].length = 3 := rfl
    have hmono : StrictMono (![i, j, k] : Fin 3 → Fin l.length) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro t
      fin_cases t
      · exact hij
      · exact hjk
    refine ⟨(OrderEmbedding.ofStrictMono (fun x : Fin [l.get i, l.get j, l.get k].length =>
        ![i, j, k] (Fin.cast hlen x)) ?_), ?_⟩
    · intro x y hxy
      exact hmono (by simpa using hxy)
    · intro ix
      fin_cases ix <;> rfl
  · rintro ⟨a, b, c, hab, hbc, hsub⟩
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at hsub
    obtain ⟨f, hf⟩ := hsub
    have b0 : (0:ℕ) < [a, b, c].length := by simp
    have b1 : (1:ℕ) < [a, b, c].length := by simp
    have b2 : (2:ℕ) < [a, b, c].length := by simp
    refine ⟨f ⟨0, b0⟩, f ⟨1, b1⟩, f ⟨2, b2⟩, ?_, ?_, ?_, ?_⟩
    · exact f.strictMono (by simp [Fin.lt_def])
    · exact f.strictMono (by simp [Fin.lt_def])
    · have h0 := hf ⟨0, b0⟩
      have h1 := hf ⟨1, b1⟩
      rw [← h0, ← h1]; exact hab
    · have h1 := hf ⟨1, b1⟩
      have h2 := hf ⟨2, b2⟩
      rw [← h1, ← h2]; exact hbc

/-- Local copies of the `Spec.lean` definitions (for development). -/
def is_positive_list (l : List ℕ) : Prop := ∀ x ∈ l, 0 < x

def covers_initial_interval (l : List ℕ) : Prop :=
  is_positive_list l ∧
  (let s := l.toFinset
   match s.max with
   | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
   | none => l.isEmpty)

def avoids_pattern_xyz (l : List ℕ) : Prop := ¬ has_ndp3 l

def sequences_counted (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ covers_initial_interval l ∧ avoids_pattern_xyz l }

open scoped Classical in
noncomputable def bigDfs (n : ℕ) : Finset (List ℕ) :=
  (Finset.range n).biUnion (fun M => Dfs M (n-1))

theorem avoids_iff (l : List ℕ) : avoids_pattern_xyz l ↔ AvoidsWI3 l := by
  rw [avoids_pattern_xyz, has_pattern_iff]
  constructor
  · intro h a b c hab hbc hsub; exact h ⟨a, b, c, hab, hbc, hsub⟩
  · rintro h ⟨a, b, c, hab, hbc, hsub⟩; exact h a b c hab hbc hsub

open scoped Classical in
theorem mem_bigDfs {n : ℕ} (hn : 1 ≤ n) {l : List ℕ} :
    l ∈ bigDfs n ↔ l ∈ sequences_counted n := by
  rw [bigDfs, Finset.mem_biUnion, sequences_counted, Set.mem_setOf_eq]
  constructor
  · -- forward
    rintro ⟨M, hMrange, hlM⟩
    rw [Finset.mem_range] at hMrange
    rw [mem_Dfs] at hlM
    obtain ⟨hlen, hbd, hcov, hav⟩ := hlM
    refine ⟨hlen, ⟨fun x hx => (hbd x hx).1, ?_⟩, (avoids_iff l).2 hav⟩
    by_cases hemp : l = []
    · subst hemp; simp
    · have hne : l.toFinset.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, List.toFinset_eq_empty_iff]; exact hemp
      have hM1 : 1 ≤ M := by
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hemp
        have := (hbd x hx); omega
      have hMmem : M ∈ l.toFinset := List.mem_toFinset.2 (hcov M hM1 le_rfl)
      have hmax' : l.toFinset.max' hne = M := by
        rw [Finset.max'_eq_iff]
        exact ⟨hMmem, fun b hb => (hbd b (List.mem_toFinset.1 hb)).2⟩
      have hmaxM : l.toFinset.max = some M := by
        rw [← Finset.coe_max' hne, hmax']; rfl
      show (match l.toFinset.max with
        | some max_s => ∀ m : ℕ, 0 < m → (m ∈ l.toFinset ↔ m ≤ max_s)
        | none => l.isEmpty)
      rw [hmaxM]
      intro m hm
      rw [List.mem_toFinset]
      exact ⟨fun hml => (hbd m hml).2, fun hmM => hcov m hm hmM⟩
  · -- backward
    rintro ⟨hlen, ⟨hpos, hmatch⟩, havoid⟩
    have hav : AvoidsWI3 l := (avoids_iff l).1 havoid
    by_cases hemp : l = []
    · subst hemp
      refine ⟨0, Finset.mem_range.2 (by omega), ?_⟩
      rw [mem_Dfs]
      refine ⟨by simpa using hlen, by simp, ?_, hav⟩
      intro v h1 h2; omega
    · have hne : l.toFinset.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, List.toFinset_eq_empty_iff]; exact hemp
      have hmaxne : l.toFinset.max ≠ ⊥ := by
        rw [ne_eq, Finset.max_eq_bot, List.toFinset_eq_empty_iff]; exact hemp
      obtain ⟨max_s, hms⟩ := WithBot.ne_bot_iff_exists.mp hmaxne
      have hms2 : l.toFinset.max = some max_s := hms.symm
      have hmatch2 : ∀ m : ℕ, 0 < m → (m ∈ l.toFinset ↔ m ≤ max_s) := by
        have hh : (match l.toFinset.max with
            | some max_s => ∀ m : ℕ, 0 < m → (m ∈ l.toFinset ↔ m ≤ max_s)
            | none => l.isEmpty) := hmatch
        rw [hms2] at hh
        exact hh
      have hvalid : IsValidML max_s (n-1) l := by
        refine ⟨hlen, ?_, ?_, hav⟩
        · intro x hx
          have hx0 : 0 < x := hpos x hx
          exact ⟨hx0, (hmatch2 x hx0).1 (List.mem_toFinset.2 hx)⟩
        · intro v hv1 hv2
          exact List.mem_toFinset.1 ((hmatch2 v hv1).2 hv2)
      have hmem : l ∈ Dfs max_s (n-1) := mem_Dfs.2 hvalid
      have := Dfs_len_ge hmem
      exact ⟨max_s, Finset.mem_range.2 (by omega), hmem⟩

def A052709 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k =>
    ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

theorem A052709_eq_sum (n : ℕ) :
    A052709 n = ∑ k ∈ Finset.range n, catalan k * Nat.choose k (n-1-k) := by
  rw [A052709]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]

open scoped Classical in
theorem Dfs_disjoint {L M M' : ℕ} (h : M ≠ M') : Disjoint (Dfs M L) (Dfs M' L) := by
  rw [Finset.disjoint_left]
  intro l h1 h2
  rw [mem_Dfs] at h1 h2
  obtain ⟨_, hbd1, hcov1, _⟩ := h1
  obtain ⟨_, hbd2, hcov2, _⟩ := h2
  have heq : M = M' := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rcases Nat.eq_zero_or_pos M' with hM' | hM'
      · omega
      · exact absurd (hbd1 M' (hcov2 M' hM' le_rfl)).2 (by omega)
    · rcases Nat.eq_zero_or_pos M' with hM' | hM'
      · exact absurd (hbd2 M (hcov1 M hM le_rfl)).2 (by omega)
      · have hle1 : M ≤ M' := (hbd2 M (hcov1 M hM le_rfl)).2
        have hle2 : M' ≤ M := (hbd1 M' (hcov2 M' hM' le_rfl)).2
        omega
  exact h heq

open scoped Classical in
theorem card_bigDfs (n : ℕ) :
    (bigDfs n).card = ∑ M ∈ Finset.range n, catalan M * Nat.choose M (n-1-M) := by
  rw [bigDfs, Finset.card_biUnion (fun x _ y _ hxy => Dfs_disjoint hxy)]
  apply Finset.sum_congr rfl
  intro M hM
  rw [Finset.mem_range] at hM
  have hMs : M + (n-1-M) = n-1 := by omega
  have hc := card_Dfs M (n-1-M)
  rw [hMs] at hc
  exact hc

open scoped Classical in
theorem final (n : ℕ) (hn : 1 ≤ n) [Fintype (sequences_counted n)] :
    A052709 n = Fintype.card (sequences_counted n) := by
  rw [A052709_eq_sum, ← card_bigDfs n]
  have hset : sequences_counted n = ↑(bigDfs n) := by
    ext l; rw [Finset.mem_coe]; exact (mem_bigDfs hn).symm
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]

end A052709dev

