import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown T_{n-1}$.
$n$ is 1-indexed here.
-/
private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

/-!
### Proof development

We prove that the limit exists. The strategy:
* run-length structure of reversed rows is governed by a pair-level word model
  (`zipP`, `Piter`), whose binary shadow satisfies an exact renormalization
  (the commutation theorem and the D-identity below);
* this yields exact recurrences for the row lengths and row sums in terms of a
  sequence `pS` satisfying `pS (k+1) = pS k + rS k`, `rS (k+1) = rS k + qS k`,
  `qS (k+5) = qS (k+4) + pS k`;
* `pS` is submultiplicative up to a constant, so Fekete's subadditivity lemma
  gives convergence of `log (pS n) / n`; the row sums are squeezed between
  constant multiples of `pS (n - 11)`, and the result follows.
-/

open Filter Real Topology

namespace Dev

/-- one step of run-length-encoding: prepend an element -/
def rcons (x : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | (y, k) :: t => if x = y then (y, k+1) :: t else (x, 1) :: (y, k) :: t
  | [] => [(x, 1)]

/-- run-length encoding, structural -/
def rle (l : List ℕ) : List (ℕ × ℕ) := l.foldr rcons []

@[simp] lemma rle_nil : rle [] = [] := rfl

lemma rle_cons (x : ℕ) (l : List ℕ) : rle (x :: l) = rcons x (rle l) := rfl

lemma rle_append (l₁ l₂ : List ℕ) : rle (l₁ ++ l₂) = l₁.foldr rcons (rle l₂) := by
  simp [rle, List.foldr_append]

/-- head value of rle agrees with head of list -/
lemma rle_head? (l : List ℕ) : (rle l).head?.map Prod.fst = l.head? := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [rle_cons]
    cases h : rle t with
    | nil => simp [rcons]
    | cons p t' =>
      obtain ⟨y, k⟩ := p
      by_cases hxy : x = y <;> simp [rcons, hxy]

lemma rle_replicate_append (k : ℕ) (h : ℕ) (rest : List ℕ) (hk : 0 < k)
    (hne : ∀ y, rest.head? = some y → y ≠ h) :
    rle (List.replicate k h ++ rest) = (h, k) :: rle rest := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show List.replicate 1 h = [h] from rfl, List.singleton_append, rle_cons]
      cases hrest : rle rest with
      | nil => simp [rcons]
      | cons p t' =>
        obtain ⟨y, c⟩ := p
        have : rest.head? = some y := by
          have := rle_head? rest
          rw [hrest] at this
          simpa using this.symm
        have hyh : y ≠ h := hne y this
        have : ¬ (h = y) := fun hh => hyh hh.symm
        simp [rcons, this]
    · rw [List.replicate_succ, List.cons_append, rle_cons, ih hn]
      simp [rcons]

/-- sum of counts = length -/
lemma rle_sum_counts (l : List ℕ) : ((rle l).map Prod.snd).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [rle_cons]
    cases h : rle t with
    | nil =>
      simp only [rcons]
      have : t.length = 0 := by rw [← ih, h]; rfl
      simp [this]
    | cons p t' =>
      obtain ⟨y, k⟩ := p
      rw [h] at ih
      by_cases hxy : x = y <;> simp [rcons, hxy] at * <;> omega


namespace RLN

-- uses the private run_lengths_nat from this file

lemma drop_length_takeWhile {α : Type*} (p : α → Bool) (l : List α) :
    l.drop (l.takeWhile p).length = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    by_cases h : p x <;> simp [h, ih]

theorem run_lengths_eq_rle (l : List ℕ) : run_lengths_nat l = (rle l).map Prod.snd := by
  induction l using run_lengths_nat.induct with
  | case1 => rw [run_lengths_nat]; rfl
  | case2 h t =>
    rename_i IH
    rw [run_lengths_nat]
    set l : List ℕ := h :: t with hl
    set p : ℕ → Bool := fun x => decide (x = h) with hp
    have hdrop : l.drop (l.takeWhile p).length = l.dropWhile p := drop_length_takeWhile p l
    have htw : l.takeWhile p = List.replicate (l.takeWhile p).length h := by
      apply List.eq_replicate_of_mem
      intro b hb
      have := List.mem_takeWhile_imp hb
      simpa [hp] using this
    have hpos : 0 < (l.takeWhile p).length := by
      rw [hl]
      simp [hp]
    have hne : ∀ y, (l.dropWhile p).head? = some y → y ≠ h := by
      intro y hy
      have := List.head?_dropWhile_not p l
      rw [hy] at this
      simpa [hp] using this
    have hrle : rle l = (h, (l.takeWhile p).length) :: rle (l.dropWhile p) := by
      have hsplit : l.takeWhile p ++ l.dropWhile p = l := List.takeWhile_append_dropWhile
      calc rle l = rle (l.takeWhile p ++ l.dropWhile p) := by rw [hsplit]
        _ = rle (List.replicate (l.takeWhile p).length h ++ l.dropWhile p) := by rw [← htw]
        _ = (h, (l.takeWhile p).length) :: rle (l.dropWhile p) :=
            rle_replicate_append _ _ _ hpos hne
    rw [hrle]
    simp only [List.map_cons]
    congr 1
    rw [← hdrop]
    exact IH

end RLN

/-! ### Merge of RLE lists -/

def mergeR : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], B => B
  | [(v, c)], B =>
    match B with
    | (v', c') :: B' => if v = v' then (v, c + c') :: B' else (v, c) :: (v', c') :: B'
    | [] => [(v, c)]
  | p :: q :: A, B => p :: mergeR (q :: A) B

@[simp] lemma mergeR_nil (A : List (ℕ × ℕ)) : mergeR A [] = A := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    cases A with
    | nil => obtain ⟨v, c⟩ := p; rfl
    | cons q A' => rw [mergeR, ih]

lemma rcons_mergeR (x : ℕ) (A B : List (ℕ × ℕ)) :
    rcons x (mergeR A B) = mergeR (rcons x A) B := by
  induction A with
  | nil =>
    cases B with
    | nil => rfl
    | cons p B' =>
      obtain ⟨v', c'⟩ := p
      show rcons x ((v', c') :: B') = mergeR [(x, 1)] ((v', c') :: B')
      by_cases h : x = v'
      · subst h; simp [rcons, mergeR, Nat.add_comm]
      · simp [rcons, mergeR, h]
  | cons p A ih =>
    obtain ⟨y, k⟩ := p
    cases A with
    | nil =>
      cases B with
      | nil => simp [mergeR, rcons]
      | cons pb B' =>
        obtain ⟨v', c'⟩ := pb
        by_cases hxy : x = y
        · subst hxy
          by_cases hyv : x = v'
          · subst hyv; simp [mergeR, rcons, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
          · simp [mergeR, rcons, hyv]
        · by_cases hyv : y = v'
          · subst hyv
            simp [mergeR, rcons, hxy]
          · simp [mergeR, rcons, hxy, hyv]
    | cons q A' =>
      show rcons x ((y,k) :: mergeR (q :: A') B) = mergeR (rcons x ((y,k) :: q :: A')) B
      by_cases hxy : x = y
      · subst hxy
        have h1 : rcons x ((x,k) :: q :: A') = (x, k+1) :: q :: A' := by simp [rcons]
        have h2 : rcons x ((x,k) :: mergeR (q :: A') B) = (x, k+1) :: mergeR (q :: A') B := by
          simp [rcons]
        rw [h1, h2, mergeR]
      · have h1 : rcons x ((y,k) :: q :: A') = (x, 1) :: (y,k) :: q :: A' := by simp [rcons, hxy]
        have h2 : rcons x ((y,k) :: mergeR (q :: A') B) = (x,1) :: (y,k) :: mergeR (q :: A') B := by
          simp [rcons, hxy]
        rw [h1, h2, mergeR, mergeR]

lemma rle_append_merge (X Y : List ℕ) : rle (X ++ Y) = mergeR (rle X) (rle Y) := by
  induction X with
  | nil =>
    show rle Y = mergeR [] (rle Y)
    cases h : rle Y with
    | nil => rfl
    | cons p B => obtain ⟨v,c⟩ := p; rfl
  | cons x X ih =>
    rw [List.cons_append, rle_cons, ih, rle_cons, rcons_mergeR]

lemma mergeR_snoc_cons (A B : List (ℕ × ℕ)) (v c c' : ℕ) :
    mergeR (A ++ [(v, c)]) ((v, c') :: B) = A ++ (v, c + c') :: B := by
  induction A with
  | nil => simp [mergeR]
  | cons p A ih =>
    cases A with
    | nil => obtain ⟨y,k⟩ := p; simp [mergeR]
    | cons q A' =>
      show mergeR (p :: ((q :: A') ++ [(v,c)])) ((v,c')::B) = _
      rw [show p :: ((q :: A') ++ [(v,c)]) = p :: (q :: (A' ++ [(v,c)])) from rfl, mergeR]
      simp only [List.cons_append] at ih
      rw [ih]
      rfl

/-! ### Word-level definitions -/

/-- letters of a pair list: (m,l) ↦ a^m b^l, a = true -/
def letters (P : List (ℕ × ℕ)) : List Bool :=
  (P.map (fun p => List.replicate p.1 true ++ List.replicate p.2 false)).flatten

/-- the appended chunk of the step map, at pair level.
Input: reversed m-list. -/
def chunk : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: rest =>
    if x = 1 then
      match chunk rest with
      | (m, l) :: t => (m + 1, l) :: t
      | [] => [(1, 0)]
    else
      match rest with
      | [] => [(1, x)]
      | _ :: _ => (1, x - 1) :: chunk rest

/-- the step map at pair level -/
def phi (P : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match P.getLast? with
  | none => []
  | some (m, l) => P.dropLast ++ [(m, l - 1)] ++ chunk (P.map Prod.fst).reverse

/-- letters of the derived word, from the m-list, with a lookahead option -/
def dlA : List ℕ → Option ℕ → List Bool
  | [], _ => []
  | m :: rest, o =>
    (if 2 ≤ m then [decide ((rest.head?.or o) = some 1)] else []) ++ dlA rest o

def dletters (ms : List ℕ) : List Bool := dlA ms none

/-- for each true letter: whether the next letter is false (end counts as false→emit false) -/
def psi : List Bool → List Bool
  | [] => []
  | b :: t => (if b then [match t.head? with | some c => !c | none => false] else []) ++ psi t

/-- a-run lengths of a boolean word -/
def aR : List Bool → List ℕ
  | [] => []
  | false :: t => aR t
  | true :: t =>
    match t with
    | true :: _ =>
      match aR t with
      | n :: r => (n + 1) :: r
      | [] => [1]
    | _ => 1 :: aR t

/-- reversed derived-letters scan: first argument is the previous element -/
def rdlB : Option ℕ → List ℕ → List Bool
  | _, [] => []
  | prev, x :: t => (if 2 ≤ x then [decide (prev = some 1)] else []) ++ rdlB (some x) t

/-- decompose a value word into (v, count-of-following-1s) pairs; `parseVC v Y` parses `v :: Y` -/
def parseVC : ℕ → List ℕ → List (ℕ × ℕ)
  | v, [] => [(v, 0)]
  | v, x :: t =>
    if x = 1 then
      match parseVC v t with
      | (v', c) :: ps => (v', c + 1) :: ps
      | [] => []
    else (v, 0) :: parseVC x t

/-- rebuild the word from pairs -/
def build (ps : List (ℕ × ℕ)) : List ℕ :=
  (ps.map (fun p => p.1 :: List.replicate p.2 1)).flatten

/-! ### basic letters lemmas -/

@[simp] lemma letters_nil : letters [] = [] := rfl

lemma letters_cons (p : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    letters (p :: P) = List.replicate p.1 true ++ List.replicate p.2 false ++ letters P := by
  simp [letters]

lemma letters_append (P Q : List (ℕ × ℕ)) :
    letters (P ++ Q) = letters P ++ letters Q := by
  simp [letters]

@[simp] lemma build_nil : build [] = [] := rfl

lemma build_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    build (p :: ps) = p.1 :: (List.replicate p.2 1 ++ build ps) := by
  simp [build]

lemma build_parseVC (v : ℕ) (Y : List ℕ) : build (parseVC v Y) = v :: Y := by
  induction Y generalizing v with
  | nil => simp [parseVC, build]
  | cons x t ih =>
    rw [parseVC]
    by_cases hx : x = 1
    · subst hx
      simp only [if_pos rfl]
      cases hp : parseVC v t with
      | nil =>
        have := ih v
        rw [hp] at this
        simp [build] at this
      | cons q ps =>
        obtain ⟨v', c⟩ := q
        have h2 := ih v
        rw [hp] at h2
        show build ((v', c + 1) :: ps) = v :: 1 :: t
        rw [build_cons] at h2 ⊢
        simp only at h2 ⊢
        obtain ⟨rfl, h3⟩ := List.cons_eq_cons.mp h2
        rw [List.replicate_succ]
        simp [← h3]
    · rw [if_neg hx, build_cons]
      simp [ih x]


lemma getLast?_cons_ne {α : Type*} (x : α) (t : List α) (ht : t ≠ []) :
    (x :: t).getLast? = t.getLast? := by
  cases t with
  | nil => exact absurd rfl ht
  | cons a t' => simp

/-! ### parseVC properties -/

lemma parseVC_ne_nil (v : ℕ) (Y : List ℕ) : parseVC v Y ≠ [] := by
  intro h
  have := build_parseVC v Y
  rw [h] at this
  simp [build] at this

lemma parseVC_fst_mem (v : ℕ) (Y : List ℕ) :
    ∀ q ∈ parseVC v Y, q.1 = v ∨ (q.1 ∈ Y ∧ q.1 ≠ 1) := by
  induction Y generalizing v with
  | nil => intro q hq; simp [parseVC] at hq; simp [hq]
  | cons x t ih =>
    intro q hq
    rw [parseVC] at hq
    by_cases hx : x = 1
    · rw [if_pos hx] at hq
      cases hp : parseVC v t with
      | nil => rw [hp] at hq; simp at hq
      | cons q0 ps =>
        obtain ⟨v', c⟩ := q0
        rw [hp] at hq
        simp only at hq
        rcases List.mem_cons.mp hq with h | h
        · subst h
          have : (v', c) ∈ parseVC v t := by rw [hp]; exact List.mem_cons_self
          rcases ih v _ this with h' | h'
          · left; exact h'
          · right; exact ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩
        · have : q ∈ parseVC v t := by rw [hp]; exact List.mem_cons_of_mem _ h
          rcases ih v _ this with h' | h'
          · left; exact h'
          · right; exact ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩
    · rw [if_neg hx] at hq
      rcases List.mem_cons.mp hq with h | h
      · subst h; left; rfl
      · rcases ih x _ h with h' | h'
        · right; rw [h']; exact ⟨List.mem_cons_self, hx⟩
        · right; exact ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩

/-- the last pair of the parse has count 0 iff the word does not end with 1 -/
lemma parseVC_getLast_snd (v : ℕ) (Y : List ℕ) (hY : Y.getLast? ≠ some 1) :
    ∃ ps' w, parseVC v Y = ps' ++ [(w, 0)] := by
  induction Y generalizing v with
  | nil => exact ⟨[], v, rfl⟩
  | cons x t ih =>
    rw [parseVC]
    by_cases hx : x = 1
    · subst hx
      have ht : t ≠ [] := by
        rintro rfl
        simp at hY
      have ht' : t.getLast? ≠ some 1 := by
        rwa [getLast?_cons_ne 1 t ht] at hY
      obtain ⟨ps', w, hw⟩ := ih v ht'
      rw [if_pos rfl, hw]
      cases ps' with
      | nil =>
        exfalso
        have hb := build_parseVC v t
        rw [hw] at hb
        simp only [List.nil_append, build_cons, build_nil] at hb
        simp only [List.append_nil] at hb
        have : t = List.replicate 0 1 := by
          have := (List.cons_eq_cons.mp hb).2
          simpa using this.symm
        simp at this
        exact ht this
      | cons q ps'' =>
        obtain ⟨v', c⟩ := q
        exact ⟨(v', c+1) :: ps'', w, by simp⟩
    · rw [if_neg hx]
      by_cases ht : t = []
      · subst ht
        simp only [parseVC]
        have hxv : x ≠ 1 := hx
        refine ⟨[(v, 0)], x, ?_⟩
        simp
      · have ht' : t.getLast? ≠ some 1 := by
          rwa [getLast?_cons_ne x t ht] at hY
        obtain ⟨ps', w, hw⟩ := ih x ht'
        exact ⟨(v, 0) :: ps', w, by rw [hw]; rfl⟩

/-! ### chunk lemmas -/

lemma chunk_cons_eq (x : ℕ) (rest : List ℕ) : chunk (x :: rest) =
    if x = 1 then
      (match chunk rest with
      | (m, l) :: t => (m + 1, l) :: t
      | [] => [(1, 0)])
    else
      (match rest with
      | [] => [(1, x)]
      | _ :: _ => (1, x - 1) :: chunk rest) := rfl

lemma chunk_singleton (x : ℕ) (hx : x ≠ 1) : chunk [x] = [(1, x)] := by
  rw [chunk_cons_eq, if_neg hx]

lemma chunk_cons_cons (x y : ℕ) (rest : List ℕ) (hx : x ≠ 1) :
    chunk (x :: y :: rest) = (1, x - 1) :: chunk (y :: rest) := by
  rw [chunk_cons_eq, if_neg hx]

lemma chunk_ne_nil (L : List ℕ) (hL : L ≠ []) : chunk L ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x rest =>
    rw [chunk_cons_eq]
    by_cases hx : x = 1
    · rw [if_pos hx]
      cases chunk rest with
      | nil => simp
      | cons q t => obtain ⟨m, l⟩ := q; simp
    · rw [if_neg hx]
      cases rest with
      | nil => simp
      | cons y t => simp

lemma chunk_one_cons (rest : List ℕ) (m l : ℕ) (t : List (ℕ × ℕ))
    (h : chunk rest = (m, l) :: t) : chunk (1 :: rest) = (m + 1, l) :: t := by
  rw [chunk_cons_eq, if_pos rfl, h]

lemma chunk_ones_append (c : ℕ) (L : List ℕ) (m l : ℕ) (t : List (ℕ × ℕ))
    (h : chunk L = (m, l) :: t) :
    chunk (List.replicate c 1 ++ L) = (m + c, l) :: t := by
  induction c with
  | zero => simpa using h
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    rw [chunk_one_cons _ _ _ _ ih]
    have : m + n + 1 = m + (n + 1) := by omega
    rw [this]

lemma chunk_build (ps : List (ℕ × ℕ)) (h2 : ∀ q ∈ ps, 2 ≤ q.1)
    (hlast : ∃ ps' w, ps = ps' ++ [(w, 0)]) :
    (chunk (build ps)).map Prod.fst = 1 :: (ps.dropLast).map (fun q => q.2 + 1) := by
  induction ps with
  | nil => obtain ⟨ps', w, hw⟩ := hlast; simp at hw
  | cons q ps' ih =>
    obtain ⟨v, c⟩ := q
    have hv : 2 ≤ v := h2 (v, c) List.mem_cons_self
    have hv1 : v ≠ 1 := by omega
    rw [build_cons]
    cases hps' : ps' with
    | nil =>
      subst hps'
      obtain ⟨ps'', w, hw⟩ := hlast
      have hps'' : ps'' = [] := by
        cases ps'' with
        | nil => rfl
        | cons a b =>
          have := congrArg List.length hw
          simp at this
      subst hps''
      simp only [List.nil_append, List.cons.injEq] at hw
      obtain ⟨hvc, -⟩ := hw
      have hc0 : c = 0 := (Prod.mk.injEq _ _ _ _ ▸ hvc).2
      subst hc0
      show (chunk (v :: (List.replicate 0 1 ++ build []))).map Prod.fst = _
      simp only [List.replicate_zero, List.nil_append, build_nil]
      rw [chunk_singleton v hv1]
      simp
    | cons q0 ps'' =>
      rw [← hps']
      have hne : build ps' ≠ [] := by
        rw [hps', build_cons]
        simp
      have hlast' : ∃ ps₀ w, ps' = ps₀ ++ [(w, 0)] := by
        obtain ⟨ps₀, w, hw⟩ := hlast
        cases ps₀ with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hw
          rw [hw.2] at hps'
          simp at hps'
        | cons a ps₁ =>
          simp only [List.cons_append, List.cons.injEq] at hw
          exact ⟨ps₁, w, hw.2⟩
      have ihh := ih (fun q hq => h2 q (List.mem_cons_of_mem _ hq)) hlast'
      obtain ⟨⟨m0, l0⟩, t0, hch⟩ : ∃ p t, chunk (build ps') = p :: t := by
        cases hc : chunk (build ps') with
        | nil => exact absurd hc (chunk_ne_nil _ hne)
        | cons p t => exact ⟨p, t, rfl⟩
      have hm0 : m0 = 1 := by
        rw [hch] at ihh
        simpa using (List.cons_eq_cons.mp (by simpa using ihh)).1
      subst hm0
      have hstep := chunk_ones_append c _ _ _ _ hch
      obtain ⟨y, ys, hrest⟩ : ∃ y ys, List.replicate c 1 ++ build ps' = y :: ys := by
        cases hr : List.replicate c 1 ++ build ps' with
        | nil => simp [hne] at hr
        | cons y ys => exact ⟨y, ys, rfl⟩
      rw [hrest, chunk_cons_cons v y ys hv1, ← hrest, hstep]
      rw [hch] at ihh
      simp only [List.map_cons] at ihh ⊢
      have htail := (List.cons_eq_cons.mp ihh).2
      rw [htail, hps']
      rw [List.dropLast_cons_of_ne_nil (by simp : (q0 :: ps'') ≠ [])]
      simp only [List.map_cons]
      congr 2
      omega

/-! ### rdlB lemmas -/

lemma rdlB_cons (p : Option ℕ) (x : ℕ) (t : List ℕ) :
    rdlB p (x :: t) = (if 2 ≤ x then [decide (p = some 1)] else []) ++ rdlB (some x) t := rfl

lemma rdlB_one_cons (p : Option ℕ) (t : List ℕ) :
    rdlB p (1 :: t) = rdlB (some 1) t := by
  rw [rdlB_cons, if_neg (by omega)]
  rfl

lemma rdlB_ones (p : Option ℕ) (c : ℕ) (L : List ℕ) :
    rdlB p (List.replicate c 1 ++ L) = rdlB (if c = 0 then p else some 1) L := by
  induction c generalizing p with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, rdlB_one_cons, ih]
    simp

lemma rdlB_build (ps : List (ℕ × ℕ)) (hne : ps ≠ []) (h2 : ∀ q ∈ ps, 2 ≤ q.1) :
    ∀ p : Option ℕ, rdlB p (build ps) =
      decide (p = some 1) :: (ps.dropLast).map (fun q => decide (1 ≤ q.2)) := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons q ps' ih =>
    obtain ⟨v, c⟩ := q
    intro p
    have hv : 2 ≤ v := h2 (v, c) List.mem_cons_self
    rw [build_cons]
    simp only
    rw [rdlB_cons, if_pos hv, rdlB_ones]
    cases hps' : ps' with
    | nil =>
      subst hps'
      simp [rdlB]
    | cons q0 ps'' =>
      rw [← hps']
      have ihh := ih (by rw [hps']; simp) (fun q hq => h2 q (List.mem_cons_of_mem _ hq))
      rw [ihh]
      have hdl : ((v, c) :: ps').dropLast = (v, c) :: ps'.dropLast := by
        rw [List.dropLast_cons_of_ne_nil (by rw [hps']; simp)]
      rw [hdl]
      simp only [List.map_cons, List.cons_append, List.singleton_append]
      congr 1
      by_cases hc : c = 0
      · subst hc
        have hv1 : v ≠ 1 := by omega
        simp [hv1]
      · rw [if_neg hc]
        simp [Nat.one_le_iff_ne_zero, hc]

/-! ### dlA lemmas -/

lemma dlA_cons (m : ℕ) (rest : List ℕ) (o : Option ℕ) :
    dlA (m :: rest) o =
      (if 2 ≤ m then [decide ((rest.head?.or o) = some 1)] else []) ++ dlA rest o := rfl

lemma dlA_append (X Y : List ℕ) (o : Option ℕ) :
    dlA (X ++ Y) o = dlA X (Y.head?.or o) ++ dlA Y o := by
  induction X with
  | nil => rfl
  | cons m X' ih =>
    rw [List.cons_append, dlA_cons, dlA_cons, ih, List.append_assoc]
    congr 2
    rw [List.head?_append]
    rw [Option.or_assoc]

lemma dlA_snoc (X₀ : List ℕ) (w : ℕ) (o : Option ℕ) (hw : 2 ≤ w) :
    dlA (X₀ ++ [w]) o = dlA X₀ (some w) ++ [decide (o = some 1)] := by
  rw [dlA_append, dlA_cons]
  simp [hw, dlA]

lemma dlA_last (X : List ℕ) (X₀ : List ℕ) (w : ℕ) (hX : X = X₀ ++ [w]) (hw : 2 ≤ w)
    (o : Option ℕ) :
    dlA X o = (dletters X).dropLast ++ [decide (o = some 1)] := by
  subst hX
  rw [dlA_snoc _ _ _ hw]
  rw [dletters, dlA_snoc _ _ _ hw]
  simp

lemma dletters_eq_dlA (X : List ℕ) : dletters X = dlA X none := rfl

/-! ### psi lemmas -/

lemma psi_cons (b : Bool) (t : List Bool) :
    psi (b :: t) =
      (if b then [match t.head? with | some c => !c | none => false] else []) ++ psi t := rfl

lemma psi_false_cons (t : List Bool) : psi (false :: t) = psi t := rfl

/-- (ii*): the derived letters of the shifted counts equal psi of the indicators -/
lemma dlA_map_succ (ds : List ℕ) :
    dlA (ds.map (· + 1)) none = psi (ds.map (fun c => decide (1 ≤ c))) := by
  induction ds with
  | nil => rfl
  | cons c ds' ih =>
    rw [List.map_cons, dlA_cons, ih, List.map_cons, psi_cons]
    congr 1
    by_cases hc : 1 ≤ c
    · rw [if_pos (by omega : 2 ≤ c + 1), if_pos (by simpa using hc)]
      cases ds' with
      | nil => simp
      | cons d ds'' =>
        simp only [List.map_cons, List.head?_cons]
        congr 1
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd; simp
        · have h1 : d + 1 ≠ 1 := by omega
          have h2 : d ≠ 0 := by omega
          simp [h1, h2]
          omega
    · rw [if_neg (by omega : ¬ 2 ≤ c + 1), if_neg (by simpa using hc)]

/-! ### aR lemmas -/

lemma aR_false_cons (t : List Bool) : aR (false :: t) = aR t := rfl

lemma aR_falses (l : ℕ) (t : List Bool) : aR (List.replicate l false ++ t) = aR t := by
  induction l with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.cons_append, aR_false_cons, ih]

lemma aR_true_cons_eq (t : List Bool) :
    aR (true :: t) =
      match t with
      | true :: _ =>
        match aR t with
        | n :: r => (n + 1) :: r
        | [] => [1]
      | _ => 1 :: aR t := rfl

lemma aR_trues (m : ℕ) (hm : 1 ≤ m) (rest : List Bool) (hrest : rest.head? ≠ some true) :
    aR (List.replicate m true ++ rest) = m :: aR rest := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [List.replicate_one, List.singleton_append, aR_true_cons_eq]
      cases rest with
      | nil => rfl
      | cons b t =>
        cases b with
        | false => rfl
        | true => simp at hrest
    · rw [List.replicate_succ, List.cons_append, aR_true_cons_eq]
      have hres := ih hn
      have hhead : List.replicate n true ++ rest = true :: (List.replicate (n-1) true ++ rest) := by
        cases n with
        | zero => omega
        | succ k => rw [List.replicate_succ, List.cons_append]; simp
      rw [hhead]
      simp only
      rw [← hhead, hres]

/-- (S1): appending a false-block and a true-block adds one a-run at the end -/
lemma aR_append_block (A : List Bool) (l m : ℕ) (hl : 1 ≤ l) (hm : 1 ≤ m) :
    aR (A ++ List.replicate l false ++ List.replicate m true) = aR A ++ [m] := by
  induction A with
  | nil =>
    rw [List.nil_append, aR_falses]
    rw [show List.replicate m true = List.replicate m true ++ [] by simp]
    rw [aR_trues m hm [] (by simp)]
    rfl
  | cons b A' ih =>
    cases b with
    | false =>
      rw [List.cons_append, List.cons_append, aR_false_cons, aR_false_cons, ih]
    | true =>
      rw [List.cons_append, List.cons_append, aR_true_cons_eq, aR_true_cons_eq]
      cases hA' : A' with
      | nil =>
        simp only [List.nil_append]
        cases hl' : List.replicate l false with
        | nil => simp [List.replicate_eq_nil_iff] at hl'; omega
        | cons c cs =>
          have hc : c = false := by
            have := List.mem_replicate.mp (hl' ▸ List.mem_cons_self)
            exact this.2
          subst hc
          show 1 :: aR (false :: (cs ++ List.replicate m true)) = [1, m]
          rw [aR_false_cons, show cs ++ List.replicate m true = cs ++ (List.replicate m true ++ []) by simp]
          have hcs : ∀ x ∈ cs, x = false := by
            intro x hx
            exact (List.mem_replicate.mp (hl' ▸ List.mem_cons_of_mem _ hx)).2
          have : aR (cs ++ (List.replicate m true ++ [])) = aR (List.replicate m true ++ []) := by
            clear hl'
            induction cs with
            | nil => rfl
            | cons c0 cs' ihc =>
              have hc0 : c0 = false := hcs c0 List.mem_cons_self
              subst hc0
              rw [List.cons_append, aR_false_cons]
              exact ihc (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
          rw [this, aR_trues m hm [] (by simp)]
          rfl
      | cons b' A'' =>
        cases b' with
        | true =>
          simp only [List.cons_append]
          have ihh := ih
          rw [hA'] at ihh
          simp only [List.cons_append] at ihh
          rw [ihh]
          have : aR (true :: A'') ≠ [] := by
            rw [aR_true_cons_eq]
            cases A'' with
            | nil => simp
            | cons x y =>
              cases x with
              | false => simp
              | true =>
                cases aR (true :: y) with
                | nil => simp
                | cons u v => simp
          cases haR : aR (true :: A'') with
          | nil => exact absurd haR this
          | cons n r => simp
        | false =>
          simp only [List.cons_append]
          have ihh := ih
          rw [hA'] at ihh
          simp only [List.cons_append] at ihh
          rw [ihh]

/-- (W4.6'): the reversed m-components are the a-runs of the reversed letters -/
lemma aR_letters_reverse (Q : List (ℕ × ℕ)) (hQ : ∀ q ∈ Q, 1 ≤ q.1 ∧ 1 ≤ q.2) :
    aR ((letters Q).reverse) = (Q.map Prod.fst).reverse := by
  induction Q with
  | nil => rfl
  | cons q Q' ih =>
    obtain ⟨m, l⟩ := q
    obtain ⟨hm, hl⟩ := hQ (m, l) List.mem_cons_self
    rw [letters_cons]
    simp only [List.reverse_append, List.reverse_replicate]
    rw [← List.append_assoc]
    rw [aR_append_block _ l m hl hm]
    rw [ih (fun q hq => hQ q (List.mem_cons_of_mem _ hq))]
    simp

/-! ### rdlB / dlA reversal -/

lemma rdlB_snoc (o : Option ℕ) (A : List ℕ) (m : ℕ) :
    rdlB o (A ++ [m]) =
      rdlB o A ++ (if 2 ≤ m then [decide ((A.getLast?.or o) = some 1)] else []) := by
  induction A generalizing o with
  | nil => simp [rdlB_cons, rdlB]
  | cons x A' ih =>
    rw [List.cons_append, rdlB_cons, rdlB_cons, ih (some x), List.append_assoc]
    congr 3
    cases A' with
    | nil => rfl
    | cons a b => rw [getLast?_cons_ne x (a :: b) (by simp)]
                  simp [List.getLast?_cons_cons]
                  cases (b.getLast?) <;> simp [List.getLast?_cons]

lemma dlA_reverse (X : List ℕ) (o : Option ℕ) :
    (dlA X o).reverse = rdlB o X.reverse := by
  induction X with
  | nil => rfl
  | cons m X' ih =>
    rw [dlA_cons, List.reverse_append, ih]
    rw [show (m :: X').reverse = X'.reverse ++ [m] by simp]
    rw [rdlB_snoc]
    congr 1
    by_cases hm : 2 ≤ m
    · rw [if_pos hm, if_pos hm]
      simp
    · rw [if_neg hm, if_neg hm]
      rfl

/-! ### the core lemma (B-core) -/

lemma psi_true_ne_nil (t : List Bool) : psi (true :: t) ≠ [] := by
  rw [psi_cons]
  simp

lemma aR_true_cons_ne_nil (t : List Bool) : ∃ n r, aR (true :: t) = n :: r ∧ 1 ≤ n := by
  rw [aR_true_cons_eq]
  cases t with
  | nil => exact ⟨1, [], rfl, le_refl 1⟩
  | cons b t' =>
    cases b with
    | false => exact ⟨1, aR (false :: t'), rfl, le_refl 1⟩
    | true =>
      cases h : aR (true :: t') with
      | nil => exact ⟨1, [], rfl, le_refl 1⟩
      | cons n r => exact ⟨n + 1, r, rfl, by omega⟩

lemma letters_cons_pair (m l : ℕ) (t : List (ℕ × ℕ)) :
    letters ((m + 1, l) :: t) = true :: letters ((m, l) :: t) := by
  rw [letters_cons, letters_cons]
  simp [List.replicate_succ]

lemma bcore : ∀ (n : ℕ) (bs : List Bool), bs.length = n →
    (∃ bs₀, bs = bs₀ ++ [true, true]) →
    letters (chunk (aR bs)) = true :: psi bs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro bs hlen hex
    obtain ⟨bs₀, rfl⟩ := hex
    cases hbs₀ : bs₀ with
    | nil =>
      subst hbs₀
      decide +kernel
    | cons c bs₀' =>
      subst hbs₀
      rw [List.cons_append]
      set rest := bs₀' ++ [true, true] with hrest
      have hrestlen : rest.length < n := by
        rw [← hlen]
        simp [hrest]
      cases c with
      | false =>
        rw [aR_false_cons, psi_false_cons]
        exact ih rest.length hrestlen rest rfl ⟨bs₀', rfl⟩
      | true =>
        obtain ⟨d, rest'', hd⟩ : ∃ d rest'', rest = d :: rest'' := by
          cases bs₀' with
          | nil => exact ⟨true, [true], rfl⟩
          | cons e t => exact ⟨e, t ++ [true, true], rfl⟩
        cases d with
        | false =>
          -- rest = false :: rest'', with rest'' = bs₀'' ++ [t,t]
          obtain ⟨bs₀'', hbs''⟩ : ∃ bs₀'', rest'' = bs₀'' ++ [true, true] := by
            cases hb : bs₀' with
            | nil => rw [hb] at hrest; rw [hrest] at hd; simp at hd
            | cons e t =>
              rw [hb] at hrest
              rw [hrest] at hd
              simp only [List.cons_append, List.cons.injEq] at hd
              exact ⟨t, hd.2.symm⟩
          rw [hd]
          rw [show aR (true :: false :: rest'') = 1 :: aR rest'' from rfl]
          have hlen'' : rest''.length < n := by
            have := hrestlen
            rw [hd] at this
            simp at this
            omega
          have ihh := ih rest''.length hlen'' rest'' rfl ⟨bs₀'', hbs''⟩
          obtain ⟨⟨m0, l0⟩, t0, hch⟩ : ∃ p t, chunk (aR rest'') = p :: t := by
            cases hc : chunk (aR rest'') with
            | nil => rw [hc] at ihh; simp at ihh
            | cons p t => exact ⟨p, t, rfl⟩
          rw [chunk_one_cons _ _ _ _ hch, letters_cons_pair, ← hch, ihh]
          rw [show psi (true :: false :: rest'') = true :: psi (false :: rest'') from rfl,
              psi_false_cons]
        | true =>
          -- rest = true :: rest''
          rw [hd]
          obtain ⟨n0, r, haR, hn0⟩ := aR_true_cons_ne_nil rest''
          rw [show aR (true :: true :: rest'') =
              (match aR (true :: rest'') with
               | n :: r => (n + 1) :: r
               | [] => [1]) from rfl]
          rw [haR]
          simp only
          have ihh := ih rest.length hrestlen rest rfl ⟨bs₀', rfl⟩
          rw [hd] at ihh
          rw [haR] at ihh
          have hpsi : psi (true :: true :: rest'') = false :: psi (true :: rest'') := rfl
          rw [hpsi]
          -- now case on r
          cases hr : r with
          | nil =>
            subst hr
            -- chunk [n0+1] and chunk [n0]
            rcases Nat.lt_or_ge n0 2 with h2 | h2
            · -- n0 = 1: contradiction via psi_true_ne_nil
              interval_cases n0
              · exfalso
                rw [show chunk [1] = [(1, 0)] from rfl] at ihh
                have : letters [(1, 0)] = [true] := by decide +kernel
                rw [this] at ihh
                have := psi_true_ne_nil rest''
                rw [← List.cons_eq_cons.mp ihh |>.2] at this
                exact this rfl
            · rw [chunk_singleton (n0 + 1) (by omega)]
              rw [chunk_singleton n0 (by omega)] at ihh
              have hpsival : List.replicate n0 false = psi (true :: rest'') := by
                rw [letters_cons] at ihh
                simpa using ihh
              rw [letters_cons, ← hpsival]
              simp [List.replicate_succ]
          | cons r1 r' =>
            subst hr
            rw [chunk_cons_cons _ _ _ (by omega)]
            rcases Nat.lt_or_ge n0 2 with h2 | h2
            · -- n0 = 1
              interval_cases n0
              obtain ⟨⟨m0, l0⟩, t0, hch⟩ : ∃ p t, chunk (r1 :: r') = p :: t := by
                cases hc : chunk (r1 :: r') with
                | nil => exact absurd hc (chunk_ne_nil _ (by simp))
                | cons p t => exact ⟨p, t, rfl⟩
              rw [chunk_one_cons _ _ _ _ hch, letters_cons_pair, ← hch] at ihh
              have hpsival := (List.cons_eq_cons.mp ihh).2
              rw [← hpsival]
              rw [letters_cons]
              simp
            · -- n0 ≥ 2
              have hpsival : List.replicate (n0 - 1) false ++ letters (chunk (r1 :: r'))
                  = psi (true :: rest'') := by
                rw [show chunk (n0 :: r1 :: r') = (1, n0 - 1) :: chunk (r1 :: r') from
                    chunk_cons_cons _ _ _ (by omega)] at ihh
                rw [letters_cons] at ihh
                simpa using ihh
              rw [letters_cons, ← hpsival]
              have hsh : n0 + 1 - 1 = (n0 - 1) + 1 := by omega
              rw [hsh, List.replicate_succ, List.cons_append]
              rfl

/-! ### classes and the step map lemmas -/

/-- membership class for the orbit words -/
def InCQ (P : List (ℕ × ℕ)) : Prop :=
  (∃ m1 l1 l2 rest, P = (m1, l1) :: (1, l2) :: rest ∧ 2 ≤ m1) ∧
  (∀ q ∈ P, 1 ≤ q.1 ∧ 1 ≤ q.2) ∧
  (∃ P₀ ms ls, P = P₀ ++ [(ms, ls)] ∧ 2 ≤ ls)

def InCP (P : List (ℕ × ℕ)) : Prop :=
  InCQ P ∧ (∃ P₀ ms ls, P = P₀ ++ [(ms, ls)] ∧ 2 ≤ ls ∧ 2 ≤ ms)

lemma phi_of_snoc (P₀ : List (ℕ × ℕ)) (m l : ℕ) :
    phi (P₀ ++ [(m, l)]) = P₀ ++ [(m, l - 1)] ++ chunk (((P₀ ++ [(m, l)]).map Prod.fst).reverse) := by
  rw [phi]
  rw [List.getLast?_append]
  simp

lemma letters_phi (Q : List (ℕ × ℕ)) (Q₀ : List (ℕ × ℕ)) (M L : ℕ)
    (hQ : Q = Q₀ ++ [(M, L)]) (hL : 1 ≤ L) :
    letters (phi Q) = (letters Q).dropLast ++ letters (chunk ((Q.map Prod.fst).reverse)) := by
  subst hQ
  rw [phi_of_snoc]
  rw [letters_append, letters_append, letters_append]
  congr 1
  rw [letters_cons, letters_cons]
  simp only [letters_nil, List.append_nil]
  rw [List.dropLast_append_of_ne_nil]
  · congr 1
    rw [List.dropLast_append_of_ne_nil
      (show List.replicate L false ≠ [] by simp; omega)]
    simp
  · simp [List.replicate_eq_nil_iff]
    omega

lemma phi_map_fst (P : List (ℕ × ℕ)) (P₀ : List (ℕ × ℕ)) (m l : ℕ)
    (hP : P = P₀ ++ [(m, l)]) :
    (phi P).map Prod.fst = P.map Prod.fst ++ (chunk ((P.map Prod.fst).reverse)).map Prod.fst := by
  subst hP
  rw [phi_of_snoc]
  simp

/-! ### THE COMMUTATION THEOREM -/

theorem commutation (P Q : List (ℕ × ℕ)) (hP : InCP P) (hQ : InCQ Q)
    (H : dletters (P.map Prod.fst) = letters Q) :
    dletters ((phi P).map Prod.fst) = letters (phi Q) := by
  obtain ⟨⟨⟨m1, l1, l2, rest, hPpat, hm1⟩, hPpos, -⟩, P₀, ms, ls, hPsnoc, hls, hms⟩ := hP
  obtain ⟨⟨M1, L1, L2, Qrest, hQpat, hM1⟩, hQpos, Q₀, Ms, Ls, hQsnoc, hLs⟩ := hQ
  -- setup: Y = reversed m-list of P
  set Y : List ℕ := (P.map Prod.fst).reverse with hY
  have hP₀ne : P₀ ≠ [] := by
    rintro rfl
    rw [hPpat] at hPsnoc
    simp at hPsnoc
  have hYeq : Y = ms :: (P₀.map Prod.fst).reverse := by
    rw [hY, hPsnoc]
    simp
  -- the parse of Y
  set ps : List (ℕ × ℕ) := parseVC ms ((P₀.map Prod.fst).reverse) with hps
  have hbuild : build ps = Y := by rw [hps, build_parseVC, hYeq]
  have hps2 : ∀ q ∈ ps, 2 ≤ q.1 := by
    intro q hq
    rcases parseVC_fst_mem _ _ q hq with h | ⟨hmem, hne1⟩
    · omega
    · have : q.1 ∈ P.map Prod.fst := by
        rw [hPsnoc]
        simp only [List.map_append, List.mem_reverse] at hmem ⊢
        exact List.mem_append_left _ hmem
      obtain ⟨p, hp, hp1⟩ := List.mem_map.mp this
      have := (hPpos p hp).1
      omega
  have hpslast : ∃ ps' w, ps = ps' ++ [(w, 0)] := by
    apply parseVC_getLast_snd
    intro hcon
    have h1 : (P₀.map Prod.fst).reverse.getLast? = (P₀.map Prod.fst).head? := by
      simp
    rw [h1] at hcon
    have : P₀.head? = some (m1, l1) := by
      have : P = P₀ ++ [(ms, ls)] := hPsnoc
      rw [hPpat] at this
      cases P₀ with
      | nil => simp at hP₀ne
      | cons p0 P₀' =>
        simp only [List.cons_append, List.cons.injEq] at this
        rw [this.1]
        rfl
    rw [List.head?_map, this] at hcon
    simp at hcon
    omega
  -- chunk of Y via chunk_build
  have hchY : (chunk Y).map Prod.fst = 1 :: (ps.dropLast).map (fun q => q.2 + 1) := by
    rw [← hbuild]
    exact chunk_build ps hps2 hpslast
  set bs : List Bool := (ps.dropLast).map (fun q => decide (1 ≤ q.2)) with hbs
  -- LHS computation
  have hLHS : dletters ((phi P).map Prod.fst) =
      (letters Q).dropLast ++ [true] ++ psi bs := by
    rw [phi_map_fst P P₀ ms ls hPsnoc]
    rw [dletters_eq_dlA, dlA_append]
    have hh : ((chunk ((P.map Prod.fst).reverse)).map Prod.fst).head?.or none = some 1 := by
      rw [← hY, hchY]
      rfl
    rw [hh]
    have hmsP : P.map Prod.fst = (P₀.map Prod.fst) ++ [ms] := by
      rw [hPsnoc]; simp
    rw [dlA_last (P.map Prod.fst) (P₀.map Prod.fst) ms hmsP hms (some 1)]
    rw [← hY, hchY]
    have h1cons : dlA (1 :: (ps.dropLast).map (fun q => q.2 + 1)) none
        = dlA ((ps.dropLast).map (fun q => q.2 + 1)) none := by
      rw [dlA_cons, if_neg (by omega)]
      rfl
    rw [h1cons]
    have hmapmap : (ps.dropLast).map (fun q => q.2 + 1)
        = ((ps.dropLast).map Prod.snd).map (· + 1) := by
      simp [List.map_map]
      rfl
    rw [hmapmap, dlA_map_succ]
    have hbs2 : ((ps.dropLast).map Prod.snd).map (fun c => decide (1 ≤ c)) = bs := by
      rw [hbs]
      simp [List.map_map]
      rfl
    rw [hbs2, H]
    simp
  -- RHS computation
  have hrevQ : (letters Q).reverse = false :: bs := by
    rw [← H, dletters_eq_dlA, dlA_reverse, ← hY, ← hbuild]
    rw [rdlB_build ps (parseVC_ne_nil _ _) hps2 none]
    rfl
  have hQms : (Q.map Prod.fst).reverse = aR bs := by
    have h1 : aR ((letters Q).reverse) = (Q.map Prod.fst).reverse :=
      aR_letters_reverse Q hQpos
    rw [hrevQ] at h1
    rw [← h1]
    rfl
  have hbsex : ∃ bs₀, bs = bs₀ ++ [true, true] := by
    have h2 : letters Q = true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest)) := by
      rw [hQpat, letters_cons]
      simp only
      rw [show M1 = 2 + (M1 - 2) by omega, List.replicate_add]
      simp [List.append_assoc]
    have h3 : false :: bs = (true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest))).reverse := by
      rw [← h2, hrevQ]
    rw [show (true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest))).reverse
      = (List.replicate (M1 - 2) true ++ List.replicate L1 false ++
         letters ((1, L2) :: Qrest)).reverse ++ [true, true] from by simp] at h3
    cases hc : (List.replicate (M1 - 2) true ++ List.replicate L1 false ++
         letters ((1, L2) :: Qrest)).reverse with
    | nil =>
      rw [hc] at h3
      simp at h3
    | cons c cs =>
      rw [hc] at h3
      simp only [List.cons_append] at h3
      exact ⟨cs, (List.cons_eq_cons.mp h3).2⟩
  have hRHS : letters (phi Q) = (letters Q).dropLast ++ (true :: psi bs) := by
    rw [letters_phi Q Q₀ Ms Ls hQsnoc (by omega)]
    congr 1
    rw [hQms]
    exact bcore bs.length bs rfl hbsex
  rw [hLHS, hRHS]
  simp

/-! ### chunk positivity and last-pair structure -/

lemma chunk_pos (u₀ : List ℕ) (w : ℕ) (hpos : ∀ x ∈ u₀, 1 ≤ x) (hw : 2 ≤ w) :
    ∀ q ∈ chunk (u₀ ++ [w]), 1 ≤ q.1 ∧ 1 ≤ q.2 := by
  induction u₀ with
  | nil =>
    rw [List.nil_append, chunk_singleton w (by omega)]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨le_refl 1, by omega⟩
  | cons x u₀ ih =>
    have hpos' : ∀ y ∈ u₀, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have hx1 : 1 ≤ x := hpos x List.mem_cons_self
    rw [List.cons_append]
    by_cases hx : x = 1
    · subst hx
      obtain ⟨q0, t0, hq0⟩ : ∃ q0 t0, chunk (u₀ ++ [w]) = q0 :: t0 := by
        cases h : chunk (u₀ ++ [w]) with
        | nil => exact absurd h (chunk_ne_nil _ (by simp))
        | cons a b => exact ⟨a, b, rfl⟩
      obtain ⟨m, l⟩ := q0
      rw [chunk_one_cons _ _ _ _ hq0]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have h1 := ih hpos' (m, l) (hq0 ▸ List.mem_cons_self)
        exact ⟨by omega, h1.2⟩
      · exact ih hpos' q (by rw [hq0]; exact List.mem_cons_of_mem _ hq)
    · obtain ⟨y, rest', hyr⟩ := List.exists_cons_of_ne_nil
        (show u₀ ++ [w] ≠ [] by simp)
      rw [hyr, chunk_cons_cons _ _ _ hx]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨le_refl 1, by omega⟩
      · exact ih hpos' q (by rw [hyr]; exact hq)

lemma chunk_last (u₀ : List ℕ) (w : ℕ) (hw : 2 ≤ w) :
    ∃ t c, chunk (u₀ ++ [1, w]) = t ++ [(c, w)] ∧ 2 ≤ c := by
  induction u₀ with
  | nil =>
    refine ⟨[], 2, ?_, le_refl 2⟩
    rw [List.nil_append]
    have h1 : chunk [w] = [(1, w)] := chunk_singleton w (by omega)
    have := chunk_one_cons [w] 1 w [] h1
    rw [this]
    rfl
  | cons x u₀ ih =>
    obtain ⟨t, c, ht, hc⟩ := ih
    rw [List.cons_append]
    by_cases hx : x = 1
    · subst hx
      cases t with
      | nil =>
        rw [List.nil_append] at ht
        rw [chunk_one_cons _ _ _ _ ht]
        exact ⟨[], c + 1, rfl, by omega⟩
      | cons q t' =>
        obtain ⟨m, l⟩ := q
        rw [List.cons_append] at ht
        rw [chunk_one_cons _ _ _ _ ht]
        exact ⟨(m + 1, l) :: t', c, by simp, hc⟩
    · obtain ⟨y, rest', hyr⟩ := List.exists_cons_of_ne_nil
        (show u₀ ++ [1, w] ≠ [] by simp)
      rw [hyr, chunk_cons_cons _ _ _ hx, ← hyr, ht]
      exact ⟨(1, x - 1) :: t, c, by simp, hc⟩

/-! ### class preservation -/

lemma phi_InCP (P : List (ℕ × ℕ)) (hP : InCQ P) : InCP (phi P) := by
  obtain ⟨⟨m1, l1, l2, rest, hPpat, hm1⟩, hPpos, P₀, ms, ls, hPsnoc, hls⟩ := hP
  -- the reversed m-list has the form u₀' ++ [1, m1]
  have hu : (P.map Prod.fst).reverse = (rest.map Prod.fst).reverse ++ [1, m1] := by
    rw [hPpat]; simp
  -- positivity of all m's
  have hmpos : ∀ x ∈ (rest.map Prod.fst).reverse ++ [1, m1], 1 ≤ x := by
    intro x hx
    rw [← hu] at hx
    rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact (hPpos q hq).1
  -- the last pair of the chunk
  obtain ⟨t, c, htc, hc⟩ := chunk_last ((rest.map Prod.fst).reverse) m1 hm1
  -- structure of phi P
  have hphi : phi P = P₀ ++ [(ms, ls - 1)] ++ chunk ((P.map Prod.fst).reverse) := by
    rw [hPsnoc, phi_of_snoc, ← hPsnoc]
  have hchunkpos : ∀ q ∈ chunk ((P.map Prod.fst).reverse), 1 ≤ q.1 ∧ 1 ≤ q.2 := by
    rw [hu]
    have : (rest.map Prod.fst).reverse ++ [1, m1]
        = ((rest.map Prod.fst).reverse ++ [1]) ++ [m1] := by simp
    rw [this]
    apply chunk_pos _ _ _ hm1
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmpos x (List.mem_append.mpr (Or.inl hx))
    · simp only [List.mem_singleton] at hx; omega
  have hmem_snoc : (ms, ls) ∈ P := by rw [hPsnoc]; simp
  have hms1 : 1 ≤ ms := (hPpos _ hmem_snoc).1
  constructor
  · constructor
    · -- head pattern
      rcases eq_or_ne rest [] with hrest | hrest
      · -- P = [(m1,l1),(1,l2)], so P₀ = [(m1,l1)], ms = 1, ls = l2
        subst hrest
        have hP2 : P = [(m1, l1)] ++ [(1, l2)] := by rw [hPpat]; rfl
        have hlast : ((1 : ℕ), l2) = (ms, ls) := by
          have h1 : P.getLast? = some (1, l2) := by rw [hP2]; simp
          have h2 : P.getLast? = some (ms, ls) := by rw [hPsnoc]; simp
          rw [h1] at h2
          exact Option.some.inj h2
        have hP₀ : P₀ = [(m1, l1)] := by
          have := hPsnoc.symm.trans hP2
          rw [← hlast] at this
          exact (List.append_left_inj _).mp this
        refine ⟨m1, l1, ls - 1, chunk ((P.map Prod.fst).reverse), ?_, hm1⟩
        rw [hphi, hP₀]
        have : ms = 1 := (Prod.mk.injEq _ _ _ _ |>.mp hlast).1.symm
        rw [this]
        rfl
      · -- rest ≠ []: P₀ = (m1,l1)::(1,l2)::rest.dropLast
        have hP₀ : P₀ = (m1, l1) :: (1, l2) :: rest.dropLast := by
          have h1 : P.dropLast = P₀ := by rw [hPsnoc]; simp
          rw [hPpat] at h1
          rw [← h1, List.dropLast_cons_of_ne_nil (by simp),
            List.dropLast_cons_of_ne_nil hrest]
        refine ⟨m1, l1, l2, rest.dropLast ++ ([(ms, ls - 1)] ++ chunk ((P.map Prod.fst).reverse)), ?_, hm1⟩
        rw [hphi, hP₀]
        simp
    constructor
    · -- positivity
      intro q hq
      rw [hphi] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact hPpos q (by rw [hPsnoc]; exact List.mem_append.mpr (Or.inl hq))
        · simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨hms1, by omega⟩
      · exact hchunkpos q hq
    · -- snoc with ls' ≥ 2
      refine ⟨P₀ ++ [(ms, ls - 1)] ++ t, c, m1, ?_, hm1⟩
      rw [hphi, hu, htc]
      simp
  · -- snoc with ms' ≥ 2 as well
    refine ⟨P₀ ++ [(ms, ls - 1)] ++ t, c, m1, ?_, hm1, hc⟩
    rw [hphi, hu, htc]
    simp

/-! ### counting -/

def plen (P : List (ℕ × ℕ)) : ℕ := (P.map (fun q => q.1 + q.2)).sum
def pca (P : List (ℕ × ℕ)) : ℕ := (P.map Prod.fst).sum

@[simp] lemma plen_nil : plen [] = 0 := rfl
@[simp] lemma pca_nil : pca [] = 0 := rfl

lemma plen_cons (q : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    plen (q :: P) = q.1 + q.2 + plen P := by simp [plen]

lemma pca_cons (q : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    pca (q :: P) = q.1 + pca P := by simp [pca]

lemma plen_append (P Q : List (ℕ × ℕ)) : plen (P ++ Q) = plen P + plen Q := by
  simp [plen]

lemma pca_append (P Q : List (ℕ × ℕ)) : pca (P ++ Q) = pca P + pca Q := by
  simp [pca]

lemma letters_length (P : List (ℕ × ℕ)) : (letters P).length = plen P := by
  induction P with
  | nil => rfl
  | cons q t ih =>
    rw [letters_cons, plen_cons, ← ih]
    simp only [List.length_append, List.length_replicate]

lemma chunk_pca (u : List ℕ) : pca (chunk u) = u.length := by
  induction u with
  | nil => rfl
  | cons x rest ih =>
    by_cases hx : x = 1
    · subst hx
      cases h : chunk rest with
      | nil =>
        have hrest : rest = [] := by
          by_contra hne
          exact chunk_ne_nil rest hne h
        subst hrest
        rfl
      | cons q t =>
        obtain ⟨m, l⟩ := q
        rw [chunk_one_cons rest m l t h]
        rw [h] at ih
        rw [pca_cons] at ih ⊢
        simp only [List.length_cons]
        omega
    · cases rest with
      | nil =>
        rw [chunk_singleton x hx]
        rfl
      | cons y t =>
        rw [chunk_cons_cons x y t hx, pca_cons]
        rw [ih]
        simp only [List.length_cons]
        omega

lemma chunk_plen (u₀ : List ℕ) (w : ℕ) (hpos : ∀ x ∈ u₀, 1 ≤ x) (hw : 2 ≤ w) :
    plen (chunk (u₀ ++ [w])) = (u₀ ++ [w]).sum + 1 := by
  induction u₀ with
  | nil =>
    rw [List.nil_append, chunk_singleton w (by omega)]
    simp [plen]
    omega
  | cons x u₀ ih =>
    have hpos' : ∀ y ∈ u₀, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have hx1 : 1 ≤ x := hpos x List.mem_cons_self
    have ih' := ih hpos'
    rw [List.cons_append]
    by_cases hx : x = 1
    · subst hx
      obtain ⟨q0, t0, hq0⟩ : ∃ q0 t0, chunk (u₀ ++ [w]) = q0 :: t0 := by
        cases h : chunk (u₀ ++ [w]) with
        | nil => exact absurd h (chunk_ne_nil _ (by simp))
        | cons a b => exact ⟨a, b, rfl⟩
      obtain ⟨m, l⟩ := q0
      rw [chunk_one_cons _ _ _ _ hq0]
      rw [hq0, plen_cons] at ih'
      rw [plen_cons]
      simp only [List.sum_cons]
      omega
    · obtain ⟨y, rest', hyr⟩ := List.exists_cons_of_ne_nil
        (show u₀ ++ [w] ≠ [] by simp)
      rw [hyr, chunk_cons_cons _ _ _ hx, ← hyr, plen_cons]
      simp only [List.sum_cons]
      omega

lemma countP2_cons_one (L : List ℕ) :
    (1 :: L).countP (fun x => decide (2 ≤ x)) = L.countP (fun x => decide (2 ≤ x)) := by
  rw [List.countP_cons]
  norm_num

lemma countP2_cons_ge (x : ℕ) (hx : 2 ≤ x) (L : List ℕ) :
    (x :: L).countP (fun x => decide (2 ≤ x)) = L.countP (fun x => decide (2 ≤ x)) + 1 := by
  rw [List.countP_cons]
  simp [hx]

lemma chunk_length (u₀ : List ℕ) (w : ℕ) (hpos : ∀ x ∈ u₀, 1 ≤ x) (hw : 2 ≤ w) :
    (chunk (u₀ ++ [w])).length = (u₀ ++ [w]).countP (fun x => decide (2 ≤ x)) := by
  induction u₀ with
  | nil =>
    rw [List.nil_append, chunk_singleton w (by omega)]
    rw [show [w] = w :: ([] : List ℕ) from rfl, countP2_cons_ge w hw]
    rfl
  | cons x u₀ ih =>
    have hpos' : ∀ y ∈ u₀, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have hx1 : 1 ≤ x := hpos x List.mem_cons_self
    have ih' := ih hpos'
    rw [List.cons_append]
    by_cases hx : x = 1
    · subst hx
      rw [countP2_cons_one]
      obtain ⟨q0, t0, hq0⟩ : ∃ q0 t0, chunk (u₀ ++ [w]) = q0 :: t0 := by
        cases h : chunk (u₀ ++ [w]) with
        | nil => exact absurd h (chunk_ne_nil _ (by simp))
        | cons a b => exact ⟨a, b, rfl⟩
      obtain ⟨m, l⟩ := q0
      rw [chunk_one_cons _ _ _ _ hq0]
      rw [hq0] at ih'
      simp only [List.length_cons] at ih' ⊢
      omega
    · have h2x : 2 ≤ x := by omega
      rw [countP2_cons_ge x h2x]
      obtain ⟨y, rest', hyr⟩ := List.exists_cons_of_ne_nil
        (show u₀ ++ [w] ≠ [] by simp)
      rw [hyr, chunk_cons_cons _ _ _ hx, ← hyr]
      simp only [List.length_cons]
      omega

lemma dlA_length (ms : List ℕ) (o : Option ℕ) :
    (dlA ms o).length = ms.countP (fun x => decide (2 ≤ x)) := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    rw [dlA_cons, List.countP_cons]
    by_cases h : 2 ≤ m
    · simp [h, ih]
    · simp [h, ih]

/-- the three counting identities for the step map -/
lemma phi_counts (P : List (ℕ × ℕ)) (hP : InCQ P) :
    plen (phi P) = plen P + pca P ∧
    pca (phi P) = pca P + P.length ∧
    (phi P).length = P.length + (dletters (P.map Prod.fst)).length := by
  obtain ⟨⟨m1, l1, l2, rest, hPpat, hm1⟩, hPpos, P₀, ms, ls, hPsnoc, hls⟩ := hP
  have hphi : phi P = P₀ ++ [(ms, ls - 1)] ++ chunk ((P.map Prod.fst).reverse) := by
    rw [hPsnoc, phi_of_snoc, ← hPsnoc]
  -- u in snoc form ending with m1
  have hu : (P.map Prod.fst).reverse
      = (((1, l2) :: rest).map Prod.fst).reverse ++ [m1] := by
    rw [hPpat]; simp
  have hmpos : ∀ x ∈ (((1, l2) :: rest).map Prod.fst).reverse, 1 ≤ x := by
    intro x hx
    rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact (hPpos q (by rw [hPpat]; exact List.mem_cons_of_mem _ hq)).1
  have hsum : ((P.map Prod.fst).reverse).sum = pca P := by
    rw [List.sum_reverse]; rfl
  have hlen : ((P.map Prod.fst).reverse).length = P.length := by simp
  have hplenP : plen P = plen P₀ + (ms + ls) := by
    rw [hPsnoc, plen_append, plen_cons]; simp [plen]
  have hpcaP : pca P = pca P₀ + ms := by
    rw [hPsnoc, pca_append, pca_cons]; simp [pca]
  have hlenP : P.length = P₀.length + 1 := by rw [hPsnoc]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hphi, plen_append, plen_append, plen_cons, plen_nil]
    rw [hu, chunk_plen _ _ hmpos hm1, ← hu, hsum]
    omega
  · rw [hphi, pca_append, pca_append, pca_cons, pca_nil]
    rw [chunk_pca, hlen]
    omega
  · rw [hphi, List.length_append, List.length_append]
    rw [hu, chunk_length _ _ hmpos hm1, ← hu]
    rw [dletters_eq_dlA, dlA_length]
    have : ((P.map Prod.fst).reverse).countP (fun x => decide (2 ≤ x))
        = (P.map Prod.fst).countP (fun x => decide (2 ≤ x)) := by
      rw [List.countP_reverse]
    rw [this]
    simp only [List.length_cons, List.length_nil]
    omega

/-! ### the orbit -/

def P0 : List (ℕ × ℕ) := [(3, 1), (1, 3)]

def Piter (k : ℕ) : List (ℕ × ℕ) := phi^[k] P0

lemma Piter_zero : Piter 0 = P0 := rfl

lemma Piter_succ (k : ℕ) : Piter (k + 1) = phi (Piter k) := by
  rw [Piter, Piter, Function.iterate_succ_apply']

lemma InCQ_P0 : InCQ P0 := by
  refine ⟨⟨3, 1, 3, [], rfl, by omega⟩, ?_, [(3, 1)], 1, 3, rfl, by omega⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by omega, by omega⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨by omega, by omega⟩

lemma InCQ_Piter (k : ℕ) : InCQ (Piter k) := by
  induction k with
  | zero => exact InCQ_P0
  | succ n ih =>
    rw [Piter_succ]
    exact (phi_InCP _ ih).1

lemma InCP_Piter (k : ℕ) : InCP (Piter (k + 1)) := by
  rw [Piter_succ]
  exact phi_InCP _ (InCQ_Piter k)

/-! ### the renormalization identity -/

lemma D_iter (k : ℕ) : dletters ((Piter (k + 4)).map Prod.fst) = letters (Piter k) := by
  induction k with
  | zero => decide
  | succ n ih =>
    have h := commutation (Piter (n + 4)) (Piter n)
      (by have := InCP_Piter (n + 3); rwa [show n + 3 + 1 = n + 4 by ring] at this)
      (InCQ_Piter n) ih
    rw [show n + 1 + 4 = n + 4 + 1 by ring]
    rw [Piter_succ (n + 4), Piter_succ n]
    exact h

/-! ### the p, r, q sequences -/

def pS (k : ℕ) : ℕ := plen (Piter k)
def rS (k : ℕ) : ℕ := pca (Piter k)
def qS (k : ℕ) : ℕ := (Piter k).length

lemma pS_succ (k : ℕ) : pS (k + 1) = pS k + rS k := by
  rw [pS, pS, rS, Piter_succ]
  exact (phi_counts _ (InCQ_Piter k)).1

lemma rS_succ (k : ℕ) : rS (k + 1) = rS k + qS k := by
  rw [rS, rS, qS, Piter_succ]
  exact (phi_counts _ (InCQ_Piter k)).2.1

lemma qS_succ (k : ℕ) : qS (k + 1) = qS k + (dletters ((Piter k).map Prod.fst)).length := by
  rw [qS, qS, Piter_succ]
  exact (phi_counts _ (InCQ_Piter k)).2.2

lemma qS_succ' (k : ℕ) : qS (k + 4 + 1) = qS (k + 4) + pS k := by
  rw [qS_succ, D_iter, letters_length]
  rfl

/-! ### definitions for the bridge -/

/-- expand pairs (v, c) to runs: v once, then 1 c times -/
def zipP (qs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (qs.map (fun q => [(q.1, 1), (1, q.2)])).flatten

/-- the counts word of `zipP qs` -/
def Ew (w : List ℕ) : List ℕ := (w.map (fun c => [1, c])).flatten

/-- reversed version of `Ew` -/
def Ee (u : List ℕ) : List ℕ := (u.map (fun x => [x, 1])).flatten

/-- the shape of `rle (Ee u)`: number of leading ones, and the parse pairs -/
def eeShape : List ℕ → ℕ × List (ℕ × ℕ)
  | [] => (0, [])
  | x :: t =>
    if x = 1 then ((eeShape t).1 + 1, (eeShape t).2)
    else (0, (x, 2 * (eeShape t).1 + 1) :: (eeShape t).2)

/-- binary shadow of a word: whether each entry is at least 2 -/
def shadow (w : List ℕ) : List Bool := w.map (fun x => decide (2 ≤ x))

/-! ### basic lemmas -/

@[simp] lemma zipP_nil : zipP [] = [] := rfl

lemma zipP_cons (v c : ℕ) (qs : List (ℕ × ℕ)) :
    zipP ((v, c) :: qs) = (v, 1) :: (1, c) :: zipP qs := by simp [zipP]

lemma zipP_append (A B : List (ℕ × ℕ)) : zipP (A ++ B) = zipP A ++ zipP B := by
  simp [zipP]

lemma zipP_length (qs : List (ℕ × ℕ)) : (zipP qs).length = 2 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q t ih =>
    obtain ⟨v, c⟩ := q
    rw [zipP_cons]
    simp only [List.length_cons, ih]
    omega

@[simp] lemma Ee_nil : Ee [] = [] := rfl

lemma Ee_cons (x : ℕ) (t : List ℕ) : Ee (x :: t) = x :: 1 :: Ee t := by simp [Ee]

lemma Ee_append (A B : List ℕ) : Ee (A ++ B) = Ee A ++ Ee B := by simp [Ee]

lemma Ew_reverse (w : List ℕ) : (Ew w).reverse = Ee w.reverse := by
  induction w with
  | nil => rfl
  | cons c t ih =>
    have h1 : Ew (c :: t) = 1 :: c :: Ew t := by simp [Ew]
    rw [h1]
    rw [show (1 :: c :: Ew t).reverse = (Ew t).reverse ++ [c, 1] by simp]
    rw [ih, List.reverse_cons, Ee_append]
    rfl

lemma zipP_map_snd (qs : List (ℕ × ℕ)) :
    (zipP qs).map Prod.snd = Ew (qs.map Prod.snd) := by
  induction qs with
  | nil => rfl
  | cons q t ih =>
    obtain ⟨v, c⟩ := q
    rw [zipP_cons]
    simp only [List.map_cons]
    have h1 : Ew (c :: t.map Prod.snd) = 1 :: c :: Ew (t.map Prod.snd) := by simp [Ew]
    rw [h1, ← ih]

@[simp] lemma shadow_nil : shadow [] = [] := rfl

lemma shadow_cons (x : ℕ) (t : List ℕ) :
    shadow (x :: t) = decide (2 ≤ x) :: shadow t := rfl

lemma shadow_append (A B : List ℕ) : shadow (A ++ B) = shadow A ++ shadow B := by
  simp [shadow]

lemma shadow_reverse (w : List ℕ) : shadow w.reverse = (shadow w).reverse := by
  simp [shadow, List.map_reverse]

lemma shadow_length (w : List ℕ) : (shadow w).length = w.length := by simp [shadow]

/-! ### eeShape lemmas -/

@[simp] lemma eeShape_nil : eeShape [] = (0, []) := rfl

lemma eeShape_cons (x : ℕ) (t : List ℕ) :
    eeShape (x :: t) =
      if x = 1 then ((eeShape t).1 + 1, (eeShape t).2)
      else (0, (x, 2 * (eeShape t).1 + 1) :: (eeShape t).2) := rfl

lemma eeShape_one_cons_fst (t : List ℕ) :
    (eeShape (1 :: t)).1 = (eeShape t).1 + 1 := by
  rw [eeShape_cons, if_pos rfl]

lemma eeShape_one_cons_snd (t : List ℕ) :
    (eeShape (1 :: t)).2 = (eeShape t).2 := by
  rw [eeShape_cons, if_pos rfl]

lemma eeShape_cons_ne_fst (x : ℕ) (t : List ℕ) (hx : x ≠ 1) :
    (eeShape (x :: t)).1 = 0 := by
  rw [eeShape_cons, if_neg hx]

lemma eeShape_cons_ne_snd (x : ℕ) (t : List ℕ) (hx : x ≠ 1) :
    (eeShape (x :: t)).2 = (x, 2 * (eeShape t).1 + 1) :: (eeShape t).2 := by
  rw [eeShape_cons, if_neg hx]

lemma eeShape_fst_ne_one (u : List ℕ) : ∀ q ∈ (eeShape u).2, q.1 ≠ 1 := by
  induction u with
  | nil => intro q hq; simp at hq
  | cons x t ih =>
    by_cases hx : x = 1
    · subst hx; rw [eeShape_one_cons_snd]; exact ih
    · rw [eeShape_cons_ne_snd x t hx]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hx
      · exact ih q hq

lemma eeShape_snd_pos (u : List ℕ) : ∀ q ∈ (eeShape u).2, 1 ≤ q.2 := by
  induction u with
  | nil => intro q hq; simp at hq
  | cons x t ih =>
    by_cases hx : x = 1
    · subst hx; rw [eeShape_one_cons_snd]; exact ih
    · rw [eeShape_cons_ne_snd x t hx]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · show 1 ≤ 2 * (eeShape t).1 + 1
        omega
      · exact ih q hq

/-- convenience equation lemmas for rcons -/
lemma rcons_nil (x : ℕ) : rcons x [] = [(x, 1)] := rfl

lemma rcons_cons (x y k : ℕ) (t : List (ℕ × ℕ)) :
    rcons x ((y, k) :: t) = if x = y then (y, k + 1) :: t else (x, 1) :: (y, k) :: t := rfl

/-- (EES): the run-length encoding of `Ee u` -/
lemma rle_Ee (u : List ℕ) :
    rle (Ee u) = (if (eeShape u).1 = 0 then [] else [(1, 2 * (eeShape u).1)])
      ++ zipP (eeShape u).2 := by
  induction u with
  | nil => rfl
  | cons x t ih =>
    rw [Ee_cons, rle_cons, rle_cons]
    by_cases hx : x = 1
    · subst hx
      rw [eeShape_one_cons_fst, eeShape_one_cons_snd,
        if_neg (by omega : ¬ ((eeShape t).1 + 1 = 0))]
      rcases Nat.eq_zero_or_pos (eeShape t).1 with hj | hjpos
      · have ihe : rle (Ee t) = zipP (eeShape t).2 := by
          rw [ih, hj, if_pos rfl, List.nil_append]
        rw [ihe, hj]
        cases hps : (eeShape t).2 with
        | nil =>
          rw [zipP_nil, rcons_nil, rcons_cons, if_pos rfl]
          decide
        | cons q ps' =>
          obtain ⟨v, c⟩ := q
          have hv : ¬ ((1 : ℕ) = v) := by
            have := eeShape_fst_ne_one t (v, c) (by rw [hps]; exact List.mem_cons_self)
            simp only at this
            omega
          rw [zipP_cons, rcons_cons, if_neg hv, rcons_cons, if_pos rfl]
          norm_num
      · obtain ⟨j0, hj0⟩ : ∃ j0, (eeShape t).1 = j0 + 1 := ⟨(eeShape t).1 - 1, by omega⟩
        have ihe : rle (Ee t) = (1, 2 * (j0 + 1)) :: zipP (eeShape t).2 := by
          rw [ih, hj0, if_neg (Nat.succ_ne_zero j0)]
          rfl
        rw [ihe, hj0, rcons_cons, if_pos rfl, rcons_cons, if_pos rfl]
        have h2 : 2 * (j0 + 1) + 1 + 1 = 2 * (j0 + 1 + 1) := by omega
        rw [h2]
        rfl
    · rw [eeShape_cons_ne_fst x t hx, eeShape_cons_ne_snd x t hx,
        if_pos rfl, List.nil_append, zipP_cons]
      rcases Nat.eq_zero_or_pos (eeShape t).1 with hj | hjpos
      · have ihe : rle (Ee t) = zipP (eeShape t).2 := by
          rw [ih, hj, if_pos rfl, List.nil_append]
        rw [ihe, hj]
        cases hps : (eeShape t).2 with
        | nil =>
          rw [zipP_nil, rcons_nil, rcons_cons, if_neg hx]
        | cons q ps' =>
          obtain ⟨v, c⟩ := q
          have hv : ¬ ((1 : ℕ) = v) := by
            have := eeShape_fst_ne_one t (v, c) (by rw [hps]; exact List.mem_cons_self)
            simp only at this
            omega
          rw [zipP_cons, rcons_cons, if_neg hv, rcons_cons, if_neg hx]
      · obtain ⟨j0, hj0⟩ : ∃ j0, (eeShape t).1 = j0 + 1 := ⟨(eeShape t).1 - 1, by omega⟩
        have ihe : rle (Ee t) = (1, 2 * (j0 + 1)) :: zipP (eeShape t).2 := by
          rw [ih, hj0, if_neg (Nat.succ_ne_zero j0)]
          rfl
        rw [ihe, hj0, rcons_cons, if_pos rfl, rcons_cons, if_neg hx]

/-- (PS): the shadow of the eeShape counts is psi of the shadow -/
lemma eeShape_psi (u : List ℕ) (hpos : ∀ x ∈ u, 1 ≤ x) :
    ((eeShape u).2).map (fun q => decide (2 ≤ q.2)) = psi (shadow u) := by
  induction u with
  | nil => rfl
  | cons x t ih =>
    have hpos' : ∀ y ∈ t, 1 ≤ y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    by_cases hx : x = 1
    · subst hx
      rw [eeShape_one_cons_snd, shadow_cons]
      rw [show decide (2 ≤ 1) = false from rfl, psi_false_cons]
      exact ih hpos'
    · have hx2 : 2 ≤ x := by
        have := hpos x List.mem_cons_self
        omega
      rw [eeShape_cons_ne_snd x t hx, shadow_cons,
        show decide (2 ≤ x) = true by simpa using hx2]
      rw [psi_cons, if_pos rfl]
      simp only [List.map_cons]
      rw [ih hpos']
      congr 1
      cases t with
      | nil => rfl
      | cons y t' =>
        have hy1 : 1 ≤ y := hpos' y List.mem_cons_self
        by_cases hy : y = 1
        · subst hy
          rw [eeShape_one_cons_fst]
          simp only [shadow_cons, List.head?_cons]
          rw [show decide (2 ≤ 1) = false from rfl]
          have h4 : 2 ≤ 2 * ((eeShape t').1 + 1) + 1 := by omega
          simp [h4]
        · have hy2 : 2 ≤ y := by omega
          rw [eeShape_cons_ne_fst y t' hy]
          simp only [shadow_cons, List.head?_cons]
          rw [show decide (2 ≤ y) = true by simpa using hy2]
          simp

/-! ### chunk_letters : the standalone RHS of the commutation argument -/

lemma chunk_letters (Q : List (ℕ × ℕ)) (hQ : InCQ Q) (bs : List Bool)
    (hrevQ : (letters Q).reverse = false :: bs) :
    letters (chunk ((Q.map Prod.fst).reverse)) = true :: psi bs := by
  obtain ⟨⟨M1, L1, L2, Qrest, hQpat, hM1⟩, hQpos, -⟩ := hQ
  have hQms : (Q.map Prod.fst).reverse = aR bs := by
    have h1 : aR ((letters Q).reverse) = (Q.map Prod.fst).reverse :=
      aR_letters_reverse Q hQpos
    rw [hrevQ] at h1
    rw [← h1]
    rfl
  have hbsex : ∃ bs₀, bs = bs₀ ++ [true, true] := by
    have h2 : letters Q = true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest)) := by
      rw [hQpat, letters_cons]
      simp only
      rw [show M1 = 2 + (M1 - 2) by omega, List.replicate_add]
      simp [List.append_assoc]
    have h3 : false :: bs = (true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest))).reverse := by
      rw [← h2, hrevQ]
    rw [show (true :: true :: (List.replicate (M1 - 2) true ++
        List.replicate L1 false ++ letters ((1, L2) :: Qrest))).reverse
      = (List.replicate (M1 - 2) true ++ List.replicate L1 false ++
         letters ((1, L2) :: Qrest)).reverse ++ [true, true] from by simp] at h3
    cases hc : (List.replicate (M1 - 2) true ++ List.replicate L1 false ++
         letters ((1, L2) :: Qrest)).reverse with
    | nil =>
      rw [hc] at h3
      simp at h3
    | cons c cs =>
      rw [hc] at h3
      simp only [List.cons_append] at h3
      exact ⟨cs, (List.cons_eq_cons.mp h3).2⟩
  rw [hQms]
  exact bcore bs.length bs rfl hbsex

/-- from `InCQ`, the reversed letters start with `false` -/
lemma letters_rev_false (Q : List (ℕ × ℕ)) (hQ : InCQ Q) :
    ∃ bs, (letters Q).reverse = false :: bs := by
  obtain ⟨-, -, Q₀, ms, ls, hsnoc, hls⟩ := hQ
  obtain ⟨k, rfl⟩ : ∃ k, ls = k + 1 := ⟨ls - 1, by omega⟩
  have h1 : letters Q = (letters Q₀ ++ (List.replicate ms true ++
      List.replicate k false)) ++ [false] := by
    rw [hsnoc, letters_append, letters_cons, letters_nil, List.append_nil]
    simp only [List.replicate_succ']
    simp [List.append_assoc]
  exact ⟨(letters Q₀ ++ (List.replicate ms true ++ List.replicate k false)).reverse,
    by rw [h1, List.reverse_append]; rfl⟩

/-! ### the A381587_T sequence (development copy of A381587_T) -/

-- uses the private A381587_T from this file

lemma T_succ (m : ℕ) (hm : 3 ≤ m) :
    A381587_T (m + 1) = run_lengths_nat (A381587_T m).reverse ++ A381587_T m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rw [show k + 3 + 1 = k + 4 from rfl, A381587_T]

lemma T3 : A381587_T 3 = [2] := rfl

lemma T4 : A381587_T 4 = [1, 2] := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, T_succ 3 (by omega), T3, RLN.run_lengths_eq_rle]
  decide

lemma T5 : A381587_T 5 = [1, 1, 1, 2] := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, T_succ 4 (by omega), T4, RLN.run_lengths_eq_rle]
  decide

lemma T6 : A381587_T 6 = [1, 3, 1, 1, 1, 2] := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, T_succ 5 (by omega), T5, RLN.run_lengths_eq_rle]
  decide

lemma T7 : A381587_T 7 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, T_succ 6 (by omega), T6, RLN.run_lengths_eq_rle]
  decide

lemma T8 : A381587_T 8 = [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, T_succ 7 (by omega), T7, RLN.run_lengths_eq_rle]
  decide

lemma T9 : A381587_T 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3,
    1, 1, 1, 2] := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, T_succ 8 (by omega), T8, RLN.run_lengths_eq_rle]
  decide

lemma T10 : A381587_T 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3,
    1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, T_succ 9 (by omega), T9, RLN.run_lengths_eq_rle]
  decide

/-! ### the master invariant -/

def Inv (n : ℕ) (qs : List (ℕ × ℕ)) : Prop :=
  rle ((A381587_T n).reverse) = zipP qs ∧
  (∀ q ∈ qs, q.1 ≠ 1 ∧ 1 ≤ q.2) ∧
  shadow (qs.map Prod.snd) = letters (Piter (n - 9))

def qs10 : List (ℕ × ℕ) :=
  [(2, 3), (3, 3), (3, 3), (3, 1), (3, 5), (3, 1), (3, 1), (3, 7), (5, 3), (3, 1),
   (3, 1), (3, 1)]

lemma Inv10 : Inv 10 qs10 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [T10]
    decide
  · decide
  · decide

theorem Inv_step (n : ℕ) (hn : 10 ≤ n) (qs : List (ℕ × ℕ)) (h : Inv n qs) :
    ∃ qs', Inv (n + 1) qs' := by
  obtain ⟨hrle, hvals, hsh⟩ := h
  have hQ : InCQ (Piter (n - 9)) := InCQ_Piter (n - 9)
  have hqs_ne : qs ≠ [] := by
    rintro rfl
    obtain ⟨⟨m1, l1, l2, rest, hpat, hm1⟩, -, -⟩ := hQ
    rw [hpat] at hsh
    simp only [List.map_nil, shadow_nil, letters_cons] at hsh
    have hlen := congrArg List.length hsh
    simp at hlen
    omega
  obtain ⟨qs₀, zc, hqs⟩ := (List.eq_nil_or_concat qs).resolve_left hqs_ne
  obtain ⟨z, cl⟩ := zc
  rw [List.concat_eq_append] at hqs
  subst hqs
  have hzcl := hvals (z, cl) (by simp)
  have hclpos : 1 ≤ cl := hzcl.2
  have hw : (qs₀ ++ [(z, cl)]).map Prod.snd = qs₀.map Prod.snd ++ [cl] := by simp
  rw [hw] at hsh
  obtain ⟨bs, hbs⟩ := letters_rev_false (Piter (n - 9)) hQ
  have hshu2 : (false : Bool) :: bs
      = decide (2 ≤ cl) :: shadow ((qs₀.map Prod.snd).reverse) := by
    rw [← hbs, ← hsh, ← shadow_reverse, List.reverse_append]
    rfl
  have hcl : cl = 1 := by
    have h1 := (List.cons_eq_cons.mp hshu2).1
    by_contra hc
    have h2 : 2 ≤ cl := by omega
    rw [show decide (2 ≤ cl) = true by simpa using h2] at h1
    exact absurd h1 (by simp)
  have hbs_eq : bs = shadow ((qs₀.map Prod.snd).reverse) :=
    (List.cons_eq_cons.mp hshu2).2
  subst hcl
  -- the new A381587_T row
  have hT1 : (A381587_T (n + 1)).reverse
      = (A381587_T n).reverse ++ Ee (1 :: (qs₀.map Prod.snd).reverse) := by
    rw [T_succ n (by omega), List.reverse_append]
    congr 1
    rw [RLN.run_lengths_eq_rle, hrle, zipP_map_snd, hw, Ew_reverse]
    congr 1
    simp
  set j' : ℕ := (eeShape ((qs₀.map Prod.snd).reverse)).1 with hj'
  set ps : List (ℕ × ℕ) := (eeShape ((qs₀.map Prod.snd).reverse)).2 with hps
  have hrle1 : rle ((A381587_T (n + 1)).reverse)
      = zipP (qs₀ ++ [(z, 1 + 2 * (j' + 1))] ++ ps) := by
    rw [hT1, rle_append_merge, hrle, rle_Ee]
    rw [eeShape_one_cons_fst, eeShape_one_cons_snd, ← hj', ← hps]
    rw [if_neg (by omega : ¬ (j' + 1 = 0))]
    rw [zipP_append, zipP_cons]
    rw [show zipP qs₀ ++ (z, 1) :: (1, 1) :: zipP ([] : List (ℕ × ℕ))
      = (zipP qs₀ ++ [(z, 1)]) ++ [(1, 1)] by simp]
    rw [List.singleton_append, mergeR_snoc_cons]
    rw [zipP_append, zipP_append, zipP_cons]
    simp
  refine ⟨qs₀ ++ [(z, 1 + 2 * (j' + 1))] ++ ps, hrle1, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact hvals q (List.mem_append.mpr (Or.inl hq))
      · simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨hzcl.1, by omega⟩
    · exact ⟨eeShape_fst_ne_one _ q (hps ▸ hq), eeShape_snd_pos _ q (hps ▸ hq)⟩
  · have hn9 : n + 1 - 9 = (n - 9) + 1 := by omega
    rw [hn9, Piter_succ]
    obtain ⟨-, -, P₀, ms, ls, hPsnoc, hls⟩ := hQ
    rw [letters_phi (Piter (n - 9)) P₀ ms ls hPsnoc (by omega)]
    rw [chunk_letters (Piter (n - 9)) (InCQ_Piter (n - 9)) bs hbs]
    have hdrop : shadow (qs₀.map Prod.snd) = (letters (Piter (n - 9))).dropLast := by
      rw [← hsh, shadow_append]
      rw [show shadow [1] = [decide (2 ≤ 1)] from rfl]
      rw [List.dropLast_concat]
    have hpsi : shadow (ps.map Prod.snd) = psi bs := by
      have hupos : ∀ x ∈ (qs₀.map Prod.snd).reverse, 1 ≤ x := by
        intro x hx
        rw [List.mem_reverse, List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        exact (hvals q (List.mem_append.mpr (Or.inl hq))).2
      have h2 := eeShape_psi ((qs₀.map Prod.snd).reverse) hupos
      rw [← hps, ← hbs_eq] at h2
      rw [← h2]
      simp [shadow, List.map_map]
    have hmap : (qs₀ ++ [(z, 1 + 2 * (j' + 1))] ++ ps).map Prod.snd
        = qs₀.map Prod.snd ++ [1 + 2 * (j' + 1)] ++ ps.map Prod.snd := by simp
    rw [hmap, shadow_append, shadow_append]
    have h3 : 2 ≤ 1 + 2 * (j' + 1) := by omega
    rw [show shadow [1 + 2 * (j' + 1)] = [true] from by simp [shadow, h3]]
    rw [hpsi, hdrop]
    simp

/-- the invariant holds for all n ≥ 10 -/
lemma Inv_exists (n : ℕ) (hn : 10 ≤ n) : ∃ qs, Inv n qs := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 10 with hm | hm
    · have h10 : m + 1 = 10 := by omega
      rw [h10]
      exact ⟨qs10, Inv10⟩
    · obtain ⟨qs, hqs⟩ := ih (by omega)
      exact Inv_step m hm qs hqs

/-! ### consequences: the length and sum recurrences -/

lemma T_length_succ (n : ℕ) (hn : 10 ≤ n) :
    (A381587_T (n + 1)).length = (A381587_T n).length + 2 * pS (n - 9) := by
  obtain ⟨qs, hrle, hvals, hsh⟩ := Inv_exists n hn
  rw [T_succ n (by omega), List.length_append]
  rw [RLN.run_lengths_eq_rle, List.length_map, hrle]
  rw [zipP_length]
  have h1 : qs.length = pS (n - 9) := by
    have h2 := congrArg List.length hsh
    rw [shadow_length, List.length_map, letters_length] at h2
    exact h2
  omega

lemma T_sum_succ (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T (n + 1)).sum = (A381587_T n).length + (A381587_T n).sum := by
  rw [T_succ n hn, List.sum_append, RLN.run_lengths_eq_rle, rle_sum_counts,
    List.length_reverse]

/-! ### elementary facts about pS, rS, qS -/

lemma pS_zero : pS 0 = 8 := by decide

lemma rS_zero : rS 0 = 4 := by decide

lemma qS_zero : qS 0 = 2 := by decide

lemma qS_mono (k : ℕ) : qS k ≤ qS (k + 1) := by
  rw [qS_succ]
  omega

lemma rS_mono (k : ℕ) : rS k ≤ rS (k + 1) := by
  rw [rS_succ]
  omega

lemma pS_mono (k : ℕ) : pS k ≤ pS (k + 1) := by
  rw [pS_succ]
  omega

lemma qS_ge_two (k : ℕ) : 2 ≤ qS k := by
  induction k with
  | zero => rw [qS_zero]
  | succ n ih => have := qS_mono n; omega

lemma rS_ge_four (k : ℕ) : 4 ≤ rS k := by
  induction k with
  | zero => rw [rS_zero]
  | succ n ih => have := rS_mono n; omega

lemma pS_ge_eight (k : ℕ) : 8 ≤ pS k := by
  induction k with
  | zero => rw [pS_zero]
  | succ n ih => have := pS_mono n; omega

lemma pca_le_plen (P : List (ℕ × ℕ)) : pca P ≤ plen P := by
  induction P with
  | nil => simp
  | cons q t ih =>
    rw [pca_cons, plen_cons]
    omega

lemma length_le_plen (P : List (ℕ × ℕ)) (h : ∀ q ∈ P, 1 ≤ q.1) :
    P.length ≤ plen P := by
  induction P with
  | nil => simp
  | cons q t ih =>
    rw [plen_cons, List.length_cons]
    have h1 : 1 ≤ q.1 := h q List.mem_cons_self
    have h2 := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    omega

lemma rS_le_pS (k : ℕ) : rS k ≤ pS k := pca_le_plen _

lemma qS_le_pS (k : ℕ) : qS k ≤ pS k := by
  apply length_le_plen
  intro q hq
  exact ((InCQ_Piter k).2.1 q hq).1

lemma pS_succ_le (k : ℕ) : pS (k + 1) ≤ 2 * pS k := by
  rw [pS_succ]
  have := rS_le_pS k
  omega

/-- doubling bound over several steps -/
lemma pS_add_le (i : ℕ) : ∀ m, pS (m + i) ≤ 2 ^ i * pS m := by
  induction i with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [show m + (n + 1) = (m + n) + 1 from rfl]
    calc pS ((m + n) + 1) ≤ 2 * pS (m + n) := pS_succ_le _
      _ ≤ 2 * (2 ^ n * pS m) := by
          have := ih m
          omega
      _ = 2 ^ (n + 1) * pS m := by ring

lemma pS_le_64 (k : ℕ) : pS (k + 6) ≤ 64 * pS k := by
  have := pS_add_le 6 k
  simpa using this

lemma rS_lower (k : ℕ) : pS k ≤ rS (k + 6) := by
  have h1 : rS (k + 6) = rS (k + 5) + qS (k + 5) := by
    have := rS_succ (k + 5)
    rwa [show k + 5 + 1 = k + 6 by omega] at this
  have h2 : qS (k + 4 + 1) = qS (k + 4) + pS k := qS_succ' k
  rw [show k + 4 + 1 = k + 5 by omega] at h2
  omega

lemma ratio65 (k : ℕ) (hk : 6 ≤ k) : 65 * pS k ≤ 64 * pS (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
  have h1 := rS_lower j
  have h2 := pS_le_64 j
  have h3 := pS_succ (j + 6)
  omega

lemma ratio138 (j : ℕ) : 138 * pS j ≤ 136 * pS (j + 1) := by
  rcases Nat.lt_or_ge j 6 with hj | hj
  · interval_cases j <;> decide
  · have := ratio65 j hj
    omega

lemma ratio8970 (j : ℕ) : 8970 * pS j ≤ 8832 * pS (j + 1) := by
  rcases Nat.lt_or_ge j 6 with hj | hj
  · interval_cases j <;> decide
  · have := ratio65 j hj
    omega

/-! ### the shifted sequences lt and aa -/

def lt (j : ℕ) : ℕ := (A381587_T (j + 10)).length
def aa (j : ℕ) : ℕ := (A381587_T (j + 10)).sum

lemma lt_zero : lt 0 = 42 := by
  show (A381587_T 10).length = 42
  rw [T10]
  decide

lemma aa_zero : aa 0 = 67 := by
  show (A381587_T 10).sum = 67
  rw [T10]
  decide

lemma lt_succ (j : ℕ) : lt (j + 1) = lt j + 2 * pS (j + 1) := by
  show (A381587_T (j + 1 + 10)).length = (A381587_T (j + 10)).length + 2 * pS (j + 1)
  have h := T_length_succ (j + 10) (by omega)
  rw [show j + 1 + 10 = j + 10 + 1 by omega, h, show j + 10 - 9 = j + 1 by omega]

lemma aa_succ (j : ℕ) : aa (j + 1) = lt j + aa j := by
  show (A381587_T (j + 1 + 10)).sum = (A381587_T (j + 10)).length + (A381587_T (j + 10)).sum
  have h := T_sum_succ (j + 10) (by omega)
  rw [show j + 1 + 10 = j + 10 + 1 by omega, h]

lemma lt_le (j : ℕ) : lt j ≤ 138 * pS j := by
  induction j with
  | zero =>
    rw [lt_zero]
    have := pS_ge_eight 0
    omega
  | succ n ih =>
    rw [lt_succ]
    have := ratio138 n
    omega

lemma lt_ge (j : ℕ) : 2 * pS j ≤ lt j := by
  induction j with
  | zero =>
    rw [lt_zero, pS_zero]
    omega
  | succ n ih =>
    rw [lt_succ]
    omega

lemma aa_le (j : ℕ) : aa j ≤ 8832 * pS j := by
  induction j with
  | zero =>
    rw [aa_zero]
    have := pS_ge_eight 0
    omega
  | succ n ih =>
    rw [aa_succ]
    have h1 := lt_le n
    have h2 := ratio8970 n
    omega

lemma aa_ge (j : ℕ) : 2 * pS j ≤ aa (j + 1) := by
  rw [aa_succ]
  have := lt_ge j
  omega

lemma aa_upper (j : ℕ) : aa (j + 1) ≤ 17664 * pS j := by
  have h1 := aa_le (j + 1)
  have h2 := pS_succ_le j
  omega

/-! ### submultiplicativity -/

theorem pS_submul : ∀ n m : ℕ, pS (m + n) ≤ 16 * pS m * pS n ∧
    rS (m + n) ≤ 16 * pS m * rS n ∧ qS (m + n) ≤ 16 * pS m * qS n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro m
    rcases Nat.lt_or_ge n 6 with hn | hn
    · -- base cases n ≤ 5
      have hp32 : pS (m + n) ≤ 32 * pS m := by
        have h1 := pS_add_le n m
        have h2 : (2 : ℕ) ^ n ≤ 32 := by
          calc (2 : ℕ) ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
            _ = 32 := by norm_num
        have h3 : 2 ^ n * pS m ≤ 32 * pS m := Nat.mul_le_mul_right _ h2
        omega
      refine ⟨?_, ?_, ?_⟩
      · calc pS (m + n) ≤ 32 * pS m := hp32
          _ ≤ 16 * pS m * 8 := by omega
          _ ≤ 16 * pS m * pS n := Nat.mul_le_mul_left _ (pS_ge_eight n)
      · calc rS (m + n) ≤ pS (m + n) := rS_le_pS _
          _ ≤ 32 * pS m := hp32
          _ ≤ 16 * pS m * 4 := by omega
          _ ≤ 16 * pS m * rS n := Nat.mul_le_mul_left _ (rS_ge_four n)
      · calc qS (m + n) ≤ pS (m + n) := qS_le_pS _
          _ ≤ 32 * pS m := hp32
          _ ≤ 16 * pS m * 2 := by omega
          _ ≤ 16 * pS m * qS n := Nat.mul_le_mul_left _ (qS_ge_two n)
    · -- inductive step, n = n' + 1 with n' ≥ 5
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hn' : 5 ≤ n' := by omega
      obtain ⟨ihp, ihr, ihq⟩ := IH n' (by omega) m
      refine ⟨?_, ?_, ?_⟩
      · calc pS (m + (n' + 1)) = pS (m + n') + rS (m + n') := by
              rw [show m + (n' + 1) = (m + n') + 1 from rfl, pS_succ]
          _ ≤ 16 * pS m * pS n' + 16 * pS m * rS n' := Nat.add_le_add ihp ihr
          _ = 16 * pS m * (pS n' + rS n') := by ring
          _ = 16 * pS m * pS (n' + 1) := by rw [pS_succ]
      · calc rS (m + (n' + 1)) = rS (m + n') + qS (m + n') := by
              rw [show m + (n' + 1) = (m + n') + 1 from rfl, rS_succ]
          _ ≤ 16 * pS m * rS n' + 16 * pS m * qS n' := Nat.add_le_add ihr ihq
          _ = 16 * pS m * (rS n' + qS n') := by ring
          _ = 16 * pS m * rS (n' + 1) := by rw [rS_succ]
      · have hq1 : qS (m + (n' + 1)) = qS (m + n') + pS (m + (n' - 4)) := by
          have h := qS_succ' (m + n' - 4)
          rw [show m + n' - 4 + 4 + 1 = m + (n' + 1) by omega,
            show m + n' - 4 + 4 = m + n' by omega,
            show m + n' - 4 = m + (n' - 4) by omega] at h
          exact h
        have hq2 : qS (n' + 1) = qS n' + pS (n' - 4) := by
          have h := qS_succ' (n' - 4)
          rw [show n' - 4 + 4 + 1 = n' + 1 by omega,
            show n' - 4 + 4 = n' by omega] at h
          exact h
        calc qS (m + (n' + 1)) = qS (m + n') + pS (m + (n' - 4)) := hq1
          _ ≤ 16 * pS m * qS n' + 16 * pS m * pS (n' - 4) :=
              Nat.add_le_add ihq (IH (n' - 4) (by omega) m).1
          _ = 16 * pS m * (qS n' + pS (n' - 4)) := by ring
          _ = 16 * pS m * qS (n' + 1) := by rw [hq2]

noncomputable def uF (n : ℕ) : ℝ := Real.log (16 * pS n)

lemma pS_cast_pos (n : ℕ) : (0 : ℝ) < (pS n : ℝ) := by
  have h := pS_ge_eight n
  exact_mod_cast (by omega : 0 < pS n)

lemma uF_subadd : Subadditive uF := by
  intro m n
  have hm := pS_cast_pos m
  have hn := pS_cast_pos n
  have hmn := pS_cast_pos (m + n)
  rw [uF, uF, uF, ← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have h := (pS_submul n m).1
  have h2 : (pS (m + n) : ℝ) ≤ 16 * pS m * pS n := by exact_mod_cast h
  nlinarith [h2]

lemma uF_nonneg (n : ℕ) : 0 ≤ uF n := by
  apply Real.log_nonneg
  have h : 1 ≤ 16 * pS n := by
    have := pS_ge_eight n
    omega
  calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
    _ ≤ ((16 * pS n : ℕ) : ℝ) := by exact_mod_cast h
    _ = 16 * (pS n : ℝ) := by push_cast; ring

lemma uF_bdd : BddBelow (Set.range fun n : ℕ => uF n / n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (uF_nonneg n) (Nat.cast_nonneg n)

noncomputable def L0 : ℝ := uF_subadd.lim

lemma tendsto_uF : Tendsto (fun n : ℕ => uF n / n) atTop (𝓝 L0) :=
  uF_subadd.tendsto_lim uF_bdd

lemma tendsto_log_pS : Tendsto (fun n : ℕ => Real.log (pS n) / n) atTop (𝓝 L0) := by
  have h1 : ∀ n : ℕ, Real.log (pS n) / n = uF n / n - Real.log 16 / n := by
    intro n
    rw [uF, Real.log_mul (by norm_num) (ne_of_gt (pS_cast_pos n))]
    ring
  have h2 : Tendsto (fun n : ℕ => Real.log 16 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h3 := tendsto_uF.sub h2
  rw [sub_zero] at h3
  exact Tendsto.congr (fun n => (h1 n).symm) h3

lemma tendsto_log_pS_shift :
    Tendsto (fun j : ℕ => Real.log (pS j) / ((j : ℝ) + 11)) atTop (𝓝 L0) := by
  have h1 : Tendsto (fun j : ℕ => (Real.log (pS j) / j) * ((j : ℝ) / (j + 11)))
      atTop (𝓝 (L0 * 1)) :=
    tendsto_log_pS.mul (tendsto_natCast_div_add_atTop (11 : ℝ))
  rw [mul_one] at h1
  apply h1.congr'
  filter_upwards [eventually_ne_atTop 0] with j hj
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj
  have hj11 : (j : ℝ) + 11 ≠ 0 := by positivity
  field_simp

lemma tendsto_log_pS_sub :
    Tendsto (fun n : ℕ => Real.log (pS (n - 11)) / n) atTop (𝓝 L0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 11]
  have he : ∀ j : ℕ, Real.log (pS (j + 11 - 11)) / ((j + 11 : ℕ) : ℝ)
      = Real.log (pS j) / ((j : ℝ) + 11) := by
    intro j
    rw [show j + 11 - 11 = j by omega]
    push_cast
    ring
  exact Tendsto.congr (fun j => (he j).symm) tendsto_log_pS_shift

lemma aT_bounds (n : ℕ) (hn : 11 ≤ n) :
    2 * pS (n - 11) ≤ (A381587_T n).sum ∧ (A381587_T n).sum ≤ 17664 * pS (n - 11) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
  have h1 := aa_ge j
  have h2 := aa_upper j
  have he : aa (j + 1) = (A381587_T (j + 11)).sum := by
    show (A381587_T (j + 1 + 10)).sum = (A381587_T (j + 11)).sum
    rw [show j + 1 + 10 = j + 11 by omega]
  rw [show j + 11 - 11 = j by omega]
  omega

lemma tendsto_log_aT :
    Tendsto (fun n : ℕ => Real.log ((A381587_T n).sum) / n) atTop (𝓝 L0) := by
  have hlow : Tendsto (fun n : ℕ => (Real.log 2 + Real.log (pS (n - 11))) / n)
      atTop (𝓝 L0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add tendsto_log_pS_sub
    rw [zero_add] at h1
    exact Tendsto.congr (fun n => (add_div _ _ _).symm) h1
  have hupp : Tendsto (fun n : ℕ => (Real.log 17664 + Real.log (pS (n - 11))) / n)
      atTop (𝓝 L0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 17664)).add tendsto_log_pS_sub
    rw [zero_add] at h1
    exact Tendsto.congr (fun n => (add_div _ _ _).symm) h1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop 11] with n hn
    obtain ⟨h1, -⟩ := aT_bounds n hn
    have hp := pS_cast_pos (n - 11)
    have e1 : Real.log 2 + Real.log ((pS (n - 11) : ℝ))
        = Real.log (((2 * pS (n - 11) : ℕ) : ℝ)) := by
      push_cast
      rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
    rw [e1]
    gcongr
    · have h8 := pS_ge_eight (n - 11)
      exact_mod_cast (by omega : 0 < 2 * pS (n - 11))
  · filter_upwards [eventually_ge_atTop 11] with n hn
    obtain ⟨h1, h2⟩ := aT_bounds n hn
    have hp := pS_cast_pos (n - 11)
    have e1 : Real.log 17664 + Real.log ((pS (n - 11) : ℝ))
        = Real.log (((17664 * pS (n - 11) : ℕ) : ℝ)) := by
      push_cast
      rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
    rw [e1]
    gcongr
    · have h8 := pS_ge_eight (n - 11)
      exact_mod_cast (by omega : 0 < (A381587_T n).sum)

theorem T_limit_exists :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (((A381587_T n).sum : ℝ)) ^ ((n : ℝ)⁻¹)) atTop (𝓝 L) := by
  refine ⟨Real.exp L0, ?_⟩
  have h1 : Tendsto (fun n : ℕ => Real.exp (Real.log ((A381587_T n).sum) / n))
      atTop (𝓝 (Real.exp L0)) :=
    (Real.continuous_exp.tendsto L0).comp tendsto_log_aT
  apply h1.congr'
  filter_upwards [eventually_ge_atTop 11] with n hn
  have h8 := pS_ge_eight (n - 11)
  have h2 : (0 : ℝ) < ((A381587_T n).sum : ℝ) := by
    have h3 := (aT_bounds n hn).1
    exact_mod_cast (by omega : 0 < (A381587_T n).sum)
  rw [Real.rpow_def_of_pos h2, div_eq_mul_inv]

end Dev

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
Dev.T_limit_exists
