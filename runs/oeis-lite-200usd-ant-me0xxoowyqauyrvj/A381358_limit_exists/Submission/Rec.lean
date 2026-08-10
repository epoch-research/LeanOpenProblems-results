import FormalConjectures.Util.ProblemImports
open List Nat
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length
theorem rl_nil : run_lengths_nat [] = [] := by rw [run_lengths_nat]
theorem rl_single (a : ℕ) : run_lengths_nat [a] = [1] := by
  rw [run_lengths_nat]; simp [List.takeWhile, rl_nil]
theorem rl_cons_ne (a b : ℕ) (t : List ℕ) (h : a ≠ b) :
    run_lengths_nat (a :: b :: t) = 1 :: run_lengths_nat (b :: t) := by
  conv_lhs => rw [run_lengths_nat]
  simp only [List.takeWhile_cons, decide_eq_true_eq, if_true]
  rw [if_neg (Ne.symm h)]; simp
theorem rl_cons_eq0 (a : ℕ) (t : List ℕ) :
    run_lengths_nat (a :: a :: t) =
      ((run_lengths_nat (a :: t)).headI + 1) :: (run_lengths_nat (a :: t)).tail := by
  conv_lhs => rw [run_lengths_nat]
  conv_rhs => rw [run_lengths_nat]
  simp only [List.takeWhile_cons, decide_true, if_true, List.length_cons]
  simp only [List.drop_succ_cons, List.headI_cons, List.tail_cons]
theorem rl_ne_nil (a : ℕ) (l : List ℕ) : run_lengths_nat (a :: l) ≠ [] := by
  cases l with
  | nil => rw [rl_single]; simp
  | cons b t =>
    by_cases h : a = b
    · subst h; rw [rl_cons_eq0]; simp
    · rw [rl_cons_ne a b t h]; simp

def incFirst : List ℕ → List ℕ | [] => [] | c::t => (c+1)::t
def incLast : List ℕ → List ℕ | [] => [] | [c]=>[c+1] | c::d::t => c::incLast (d::t)

theorem incFirst_cons (c : ℕ) (t : List ℕ) : incFirst (c::t) = (c+1)::t := rfl
theorem incFirst_append (w m : List ℕ) (hw : w ≠ []) : incFirst w ++ m = incFirst (w ++ m) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons e es => rfl

theorem rl_cons_eq (a : ℕ) (t : List ℕ) :
    run_lengths_nat (a :: a :: t) = incFirst (run_lengths_nat (a :: t)) := by
  rw [rl_cons_eq0]
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (rl_ne_nil a t)
  rw [hc]; rfl

theorem incFirst_incLast_comm : ∀ (p : List ℕ), p ≠ [] →
    incFirst (incLast p) = incLast (incFirst p) := by
  intro p hp
  match p with
  | [] => exact absurd rfl hp
  | [c] => rfl
  | c::d::t => rfl

theorem rev_incLast : ∀ (l : List ℕ), (incLast l).reverse = incFirst l.reverse := by
  intro l
  induction l using incLast.induct with
  | case1 => rfl
  | case2 c => rfl
  | case3 c d t ih =>
    show (c :: incLast (d::t)).reverse = incFirst (c::d::t).reverse
    rw [List.reverse_cons, ih, incFirst_append _ _ (by simp), ← List.reverse_cons]
theorem incLast_reverse (l : List ℕ) : incLast l.reverse = (incFirst l).reverse := by
  rw [← List.reverse_reverse (incLast l.reverse), rev_incLast, List.reverse_reverse]

theorem rl_snoc_ne : ∀ (L : List ℕ) (a : ℕ), L.getLast? ≠ some a →
    run_lengths_nat (L ++ [a]) = run_lengths_nat L ++ [1] := by
  intro L
  induction L with
  | nil => intro a _; simp [rl_single, rl_nil]
  | cons x L' ih =>
    intro a hla
    cases L' with
    | nil =>
      simp only [List.getLast?_singleton, ne_eq, Option.some.injEq] at hla
      simp only [List.nil_append, List.singleton_append]
      rw [rl_cons_ne x a [] hla, rl_single, rl_single]; rfl
    | cons y L'' =>
      rw [List.getLast?_cons_cons] at hla
      by_cases hxy : x = y
      · subst hxy
        simp only [List.cons_append]
        rw [rl_cons_eq x (L'' ++ [a])]
        have ih2 := ih a hla
        simp only [List.cons_append] at ih2
        rw [ih2, rl_cons_eq x L'', incFirst_append _ _ (rl_ne_nil x L'')]
      · simp only [List.cons_append]
        rw [rl_cons_ne x y (L'' ++ [a]) hxy]
        have ih2 := ih a hla
        simp only [List.cons_append] at ih2
        rw [ih2, rl_cons_ne x y L'' hxy, List.cons_append]

theorem incLast_cons_ne_nil (c : ℕ) (p : List ℕ) (hp : p ≠ []) :
    incLast (c :: p) = c :: incLast p := by
  obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hp
  rw [hd]; rfl

theorem rl_snoc_eq : ∀ (L : List ℕ) (a : ℕ), L.getLast? = some a →
    run_lengths_nat (L ++ [a]) = incLast (run_lengths_nat L) := by
  intro L
  induction L with
  | nil => intro a h; simp at h
  | cons x L' ih =>
    intro a hla
    cases L' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hla
      subst hla
      simp only [List.nil_append, List.singleton_append]
      rw [rl_cons_eq x [], rl_single]; rfl
    | cons y L'' =>
      rw [List.getLast?_cons_cons] at hla
      by_cases hxy : x = y
      · subst hxy
        simp only [List.cons_append]
        rw [rl_cons_eq x (L'' ++ [a])]
        have ih2 := ih a hla
        simp only [List.cons_append] at ih2
        rw [ih2, rl_cons_eq x L'', incFirst_incLast_comm _ (rl_ne_nil x L'')]
      · simp only [List.cons_append]
        rw [rl_cons_ne x y (L'' ++ [a]) hxy]
        have ih2 := ih a hla
        simp only [List.cons_append] at ih2
        rw [ih2, rl_cons_ne x y L'' hxy, incLast_cons_ne_nil _ _ (rl_ne_nil y L'')]

theorem rl_reverse : ∀ (l : List ℕ), run_lengths_nat l.reverse = (run_lengths_nat l).reverse := by
  intro l
  induction l with
  | nil => simp [rl_nil]
  | cons x t ih =>
    cases t with
    | nil => simp [rl_single]
    | cons y t' =>
      by_cases hxy : x = y
      · subst hxy
        rw [List.reverse_cons]
        have hg : ((x::t').reverse).getLast? = some x := by
          rw [List.getLast?_reverse]; rfl
        rw [rl_snoc_eq _ x hg, ih, rl_cons_eq, incLast_reverse]
      · rw [List.reverse_cons]
        have hg : ((y::t').reverse).getLast? ≠ some x := by
          simp only [List.getLast?_reverse, List.head?_cons, ne_eq, Option.some.injEq]
          exact fun h => hxy h.symm
        rw [rl_snoc_ne _ x hg, ih, rl_cons_ne x y t' hxy, List.reverse_cons]

def mergeRuns : List ℕ → List ℕ → List ℕ
  | [], q => q
  | [c], q => (c + q.headI) :: q.tail
  | c::d::p', q => c :: mergeRuns (d::p') q

theorem mergeRuns_cons_ne_nil (c : ℕ) (p q : List ℕ) (hp : p ≠ []) :
    mergeRuns (c :: p) q = c :: mergeRuns p q := by
  obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hp
  rw [hd]; rfl

theorem incFirst_mergeRuns (p q : List ℕ) (hp : p ≠ []) :
    incFirst (mergeRuns p q) = mergeRuns (incFirst p) q := by
  match p, hp with
  | [c], _ => simp only [mergeRuns, incFirst]; rw [Nat.add_right_comm]
  | c::d::p', _ => rfl

theorem RL_append : ∀ (a b : List ℕ),
    run_lengths_nat (a ++ b) =
      if a.getLast? = b.head? then mergeRuns (run_lengths_nat a) (run_lengths_nat b)
      else run_lengths_nat a ++ run_lengths_nat b := by
  intro a
  induction a with
  | nil =>
    intro b
    simp only [List.nil_append, List.getLast?_nil, rl_nil]
    cases b with
    | nil => simp [mergeRuns]
    | cons d b' => simp [mergeRuns]
  | cons c a' ih =>
    intro b
    cases a' with
    | nil =>
      cases b with
      | nil => simp [rl_single, mergeRuns, rl_nil]
      | cons d b' =>
        simp only [List.getLast?_singleton, List.head?_cons, List.singleton_append]
        by_cases hcd : c = d
        · subst hcd
          rw [if_pos rfl, rl_cons_eq, rl_single]
          obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (rl_ne_nil c b')
          rw [he]; simp only [incFirst, mergeRuns, List.headI_cons, List.tail_cons]
          rw [Nat.add_comm]
        · rw [if_neg (by simp [hcd]), rl_cons_ne c d b' hcd, rl_single]; rfl
    | cons a1 a'' =>
      have hane : (a1 :: a'') ≠ [] := by simp
      rw [List.getLast?_cons_cons]
      by_cases hca1 : c = a1
      · subst hca1
        simp only [List.cons_append]
        rw [rl_cons_eq c (a'' ++ b)]
        have ihb := ih b
        simp only [List.cons_append] at ihb
        rw [ihb, rl_cons_eq c a'']
        by_cases hcond : (c :: a'').getLast? = b.head?
        · rw [if_pos hcond, if_pos hcond, incFirst_mergeRuns _ _ (rl_ne_nil c a'')]
        · rw [if_neg hcond, if_neg hcond, incFirst_append _ _ (rl_ne_nil c a'')]
      · simp only [List.cons_append]
        rw [rl_cons_ne c a1 (a'' ++ b) hca1]
        have ihb := ih b
        simp only [List.cons_append] at ihb
        rw [ihb, rl_cons_ne c a1 a'' hca1]
        by_cases hcond : (a1 :: a'').getLast? = b.head?
        · rw [if_pos hcond, if_pos hcond, mergeRuns_cons_ne_nil _ _ _ (rl_ne_nil a1 a'')]
        · rw [if_neg hcond, if_neg hcond, List.cons_append]

theorem mergeRuns_length : ∀ (p q : List ℕ), p ≠ [] → q ≠ [] →
    (mergeRuns p q).length = p.length + q.length - 1 := by
  intro p
  induction p with
  | nil => intro q hp; exact absurd rfl hp
  | cons c p' ih =>
    intro q _ hq
    cases p' with
    | nil =>
      obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hq
      rw [he]; simp [mergeRuns]
    | cons d p'' =>
      rw [mergeRuns_cons_ne_nil c (d::p'') q (by simp)]
      rw [List.length_cons, ih q (by simp) hq]
      simp only [List.length_cons]
      omega

theorem RL_append_length_merge (a b : List ℕ) (ha : a ≠ []) (hb : b ≠ [])
    (hc : a.getLast? = b.head?) :
    (run_lengths_nat (a ++ b)).length
      = (run_lengths_nat a).length + (run_lengths_nat b).length - 1 := by
  rw [RL_append, if_pos hc]
  obtain ⟨a0, as, hae⟩ := List.exists_cons_of_ne_nil ha
  obtain ⟨b0, bs, hbe⟩ := List.exists_cons_of_ne_nil hb
  rw [mergeRuns_length _ _ (by rw [hae]; exact rl_ne_nil _ _) (by rw [hbe]; exact rl_ne_nil _ _)]

/- ## Sequence layer -/
def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

-- U n := reverse of T n
def UU (n : ℕ) : List ℕ := (A381587_T n).reverse

-- U-recursion: U_n = U_{n-1} ++ rev(RL U_{n-1})
theorem UU_succ (k : ℕ) : UU (k+4) = UU (k+3) ++ (run_lengths_nat (UU (k+3))).reverse := by
  unfold UU
  show (A381587_T (k+4)).reverse = (A381587_T (k+3)).reverse ++ _
  rw [show A381587_T (k+4) = run_lengths_nat (A381587_T (k+3)).reverse ++ A381587_T (k+3) from rfl]
  rw [List.reverse_append]

/- ## Cascade helpers -/
theorem getLastI_of (l : List ℕ) (a : ℕ) (h : l.getLast? = some a) : l.getLastI = a := by
  rw [List.getLastI_eq_getLast?_getD, h]; rfl
theorem headI_of (l : List ℕ) (a : ℕ) (h : l.head? = some a) : l.headI = a := by
  cases l with
  | nil => simp at h
  | cons b t => simp_all
theorem ne_nil_of_getLast? (l : List ℕ) (a : ℕ) (h : l.getLast? = some a) : l ≠ [] := by
  intro hn; rw [hn] at h; simp at h

theorem mergeRuns_eq (q : List ℕ) : ∀ (p : List ℕ), p ≠ [] →
    mergeRuns p q = p.dropLast ++ (p.getLastI + q.headI) :: q.tail := by
  intro p
  induction p with
  | nil => intro h; exact absurd rfl h
  | cons c p' ih =>
    intro _
    cases p' with
    | nil => simp [mergeRuns, List.getLastI]
    | cons d p'' =>
      rw [mergeRuns_cons_ne_nil c (d::p'') q (by simp), ih (by simp)]
      rw [show (c :: d :: p'').dropLast = c :: (d::p'').dropLast from by simp [List.dropLast_cons₂],
          show (c :: d :: p'').getLastI = (d::p'').getLastI from by
            rw [List.getLastI_eq_getLast?_getD, List.getLastI_eq_getLast?_getD, List.getLast?_cons_cons]]
      rw [List.cons_append]

theorem incLast_snoc (g : List ℕ) (a : ℕ) : incLast (g ++ [a]) = g ++ [a+1] := by
  induction g with
  | nil => rfl
  | cons c cs ih =>
    rw [List.cons_append, incLast_cons_ne_nil c (cs ++ [a]) (by simp), ih, List.cons_append]

theorem dropLast_getLastI (l : List ℕ) (h : l ≠ []) : l.dropLast ++ [l.getLastI] = l := by
  rw [List.getLastI_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp [List.dropLast_append_getLast h]

theorem cascade (u : List ℕ)
    (h1 : u.getLast? = some 1)
    (h2 : (run_lengths_nat u).getLast? = some 1)
    (h3 : (run_lengths_nat u).dropLast.getLast? = some 1)
    (h4 : (run_lengths_nat (run_lengths_nat u)).getLast? = some 6)
    (h5 : (run_lengths_nat (run_lengths_nat u)).dropLast.getLast? = some 1)
    (h6 : (run_lengths_nat (run_lengths_nat (run_lengths_nat u))).getLast? = some 1) :
    run_lengths_nat (run_lengths_nat (run_lengths_nat (u ++ (run_lengths_nat u).reverse)))
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat u)))
        ++ (run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat u)))).reverse := by
  set v := run_lengths_nat u with hv
  set w := run_lengths_nat v with hw
  set x := run_lengths_nat w with hx
  have vne : v ≠ [] := ne_nil_of_getLast? v 1 h2
  have wne : w ≠ [] := ne_nil_of_getLast? w 6 h4
  have xne : x ≠ [] := ne_nil_of_getLast? x 1 h6
  have vdne : v.dropLast ≠ [] := ne_nil_of_getLast? v.dropLast 1 h3
  have wdne : w.dropLast ≠ [] := ne_nil_of_getLast? w.dropLast 1 h5
  -- value facts
  have hvL : v.getLastI = 1 := getLastI_of v 1 h2
  have hwL : w.getLastI = 6 := getLastI_of w 6 h4
  have hxL : x.getLastI = 1 := getLastI_of x 1 h6
  -- w.reverse.head? = some 6, w.reverse.headI = 6
  have hwr_head : w.reverse.head? = some 6 := by rw [List.head?_reverse, h4]
  have hwr_headI : w.reverse.headI = 6 := headI_of w.reverse 6 hwr_head
  -- Step 1: RL(u ++ v.reverse) = mergeRuns v w.reverse
  have hRLvrev : run_lengths_nat v.reverse = w.reverse := by rw [rl_reverse, hw]
  have step1 : run_lengths_nat (u ++ v.reverse) = mergeRuns v w.reverse := by
    rw [RL_append]
    have hcond : u.getLast? = v.reverse.head? := by rw [List.head?_reverse, h1, h2]
    rw [if_pos hcond, ← hv, hRLvrev]
  -- expand mergeRuns: V_n = v.dropLast ++ (7 :: w.reverse.tail)
  have step1' : run_lengths_nat (u ++ v.reverse) = v.dropLast ++ (7 :: w.reverse.tail) := by
    rw [step1, mergeRuns_eq w.reverse v vne, hvL, hwr_headI]
  -- reverse-tail rewrites
  have wrev_split : w.reverse = w.getLastI :: w.dropLast.reverse := by
    conv_lhs => rw [← dropLast_getLastI w wne]
    rw [List.reverse_append]; rfl
  have wrev_tail : w.reverse.tail = w.dropLast.reverse := by rw [wrev_split, List.tail_cons]
  have xrev_split : x.reverse = x.getLastI :: x.dropLast.reverse := by
    conv_lhs => rw [← dropLast_getLastI x xne]
    rw [List.reverse_append]; rfl
  have xrev_tail : x.reverse.tail = x.dropLast.reverse := by rw [xrev_split, List.tail_cons]
  -- (B) run_lengths_nat (w.dropLast) = x.dropLast
  have hwsnoc : w.dropLast ++ [6] = w := by rw [← hwL]; exact dropLast_getLastI w wne
  have RLwd : run_lengths_nat w.dropLast = x.dropLast := by
    have e := rl_snoc_ne w.dropLast 6 (by rw [h5]; simp)
    rw [hwsnoc, ← hx] at e
    rw [e, List.dropLast_concat]
  -- g := run_lengths_nat (v.dropLast); show g = w.dropLast ++ [5]
  set g := run_lengths_nat v.dropLast with hg
  have gne : g ≠ [] := by
    rw [hg]; obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil vdne; rw [hc]; exact rl_ne_nil c cs
  have hsnoc_v : v.dropLast ++ [1] = v := by rw [← hvL]; exact dropLast_getLastI v vne
  have hweq : w = incLast g := by
    have e := rl_snoc_eq v.dropLast 1 h3
    rw [hsnoc_v] at e; rw [hw]; exact e
  have hw_form : w = g.dropLast ++ [g.getLastI + 1] := by
    rw [hweq]; conv_lhs => rw [← dropLast_getLastI g gne]; rw [incLast_snoc]
  have hgL : g.getLastI = 5 := by
    have := congrArg List.getLastI hw_form
    rw [getLastI_of w 6 h4] at this
    rw [show (g.dropLast ++ [g.getLastI + 1]).getLastI = g.getLastI + 1 from by
      rw [List.getLastI_eq_getLast?_getD, List.getLast?_concat]; rfl] at this
    omega
  have hwd : w.dropLast = g.dropLast := by
    rw [hw_form, List.dropLast_concat]
  have hg5 : g = w.dropLast ++ [5] := by
    conv_lhs => rw [← dropLast_getLastI g gne]
    rw [hgL, hwd]
  -- (E) run_lengths_nat (7 :: w.reverse.tail) = 1 :: x.reverse.tail
  have wdrev_head : w.dropLast.reverse.head? = some 1 := by rw [List.head?_reverse, h5]
  have RL7 : run_lengths_nat (7 :: w.reverse.tail) = 1 :: x.reverse.tail := by
    rw [wrev_tail]
    obtain ⟨s, ss, hs⟩ := List.exists_cons_of_ne_nil (by simp [wdne] : w.dropLast.reverse ≠ [])
    have hs1 : s = 1 := by rw [hs] at wdrev_head; simpa using wdrev_head
    rw [hs, hs1, rl_cons_ne 7 1 ss (by decide), ← hs1, ← hs, rl_reverse, RLwd, ← xrev_tail]
  -- Step 2: W_n = w.dropLast ++ (5 :: 1 :: x.reverse.tail)
  have step2 : run_lengths_nat (run_lengths_nat (u ++ v.reverse))
      = w.dropLast ++ (5 :: 1 :: x.reverse.tail) := by
    rw [step1', RL_append]
    rw [if_neg (by rw [h3]; simp)]
    rw [← hg, hg5, RL7, List.append_assoc, List.singleton_append]
  -- Step 3
  have RL5 : run_lengths_nat (5 :: 1 :: x.reverse.tail) = 1 :: (run_lengths_nat x).reverse := by
    rw [rl_cons_ne 5 1 x.reverse.tail (by decide)]
    rw [show (1 :: x.reverse.tail) = x.reverse from by rw [xrev_tail, xrev_split, hxL]]
    rw [rl_reverse]
  have step3 : run_lengths_nat (run_lengths_nat (run_lengths_nat (u ++ v.reverse)))
      = x ++ (run_lengths_nat x).reverse := by
    rw [step2, RL_append, if_neg (by rw [h5]; simp), RLwd, RL5]
    rw [show x.dropLast ++ (1 :: (run_lengths_nat x).reverse)
          = (x.dropLast ++ [1]) ++ (run_lengths_nat x).reverse from by
        rw [List.append_assoc]; rfl]
    congr 1
    rw [← hxL]; exact dropLast_getLastI x xne
  exact step3

/- ## Suffix machinery and the KEY RL-suffix lemma -/

theorem suffix_getLast? {s l : List ℕ} (h : s <:+ l) (hs : s ≠ []) :
    l.getLast? = s.getLast? := by
  obtain ⟨t, rfl⟩ := h
  exact List.getLast?_append_of_ne_nil t hs

theorem suffix_dropLast {s l : List ℕ} (h : s <:+ l) (hs : s ≠ []) :
    s.dropLast <:+ l.dropLast := by
  obtain ⟨t, rfl⟩ := h
  rw [List.dropLast_append_of_ne_nil hs]
  exact ⟨t, rfl⟩

theorem suffix_dropLast_getLast? {s l : List ℕ} (h : s <:+ l) (hs2 : s.dropLast ≠ []) :
    l.dropLast.getLast? = s.dropLast.getLast? := by
  have hs : s ≠ [] := by rintro rfl; simp at hs2
  exact suffix_getLast? (suffix_dropLast h hs) hs2

theorem RL_suffix (t s : List ℕ) (hs : s ≠ []) :
    (run_lengths_nat s).tail <:+ run_lengths_nat (t ++ s) := by
  have hRLs : run_lengths_nat s ≠ [] := by
    obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hs; exact rl_ne_nil a as
  obtain ⟨h0, ts, hts⟩ := List.exists_cons_of_ne_nil hRLs
  rw [RL_append]
  by_cases hcond : t.getLast? = s.head?
  · rw [if_pos hcond]
    have htne : t ≠ [] := by
      rintro rfl
      rw [List.getLast?_nil] at hcond
      obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hs
      rw [List.head?_cons] at hcond; exact absurd hcond (by simp)
    have hRLt : run_lengths_nat t ≠ [] := by
      obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil htne; exact rl_ne_nil a as
    rw [mergeRuns_eq (run_lengths_nat s) (run_lengths_nat t) hRLt]
    exact ⟨(run_lengths_nat t).dropLast ++
            [(run_lengths_nat t).getLastI + (run_lengths_nat s).headI], by
        rw [List.append_assoc]; rfl⟩
  · rw [if_neg hcond, hts, List.tail_cons]
    exact ⟨run_lengths_nat t ++ [h0], by rw [List.append_assoc, List.singleton_append]⟩

/- ## Concrete prefix/suffix lists and the boundary facts -/

def PV30 : List ℕ := [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1,7,1,1,1,5,1,3]
def PUbig : List ℕ := [2,1,1,1,3,1,1,1,3,1,1,1,3,1,3,1,1,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,5,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,3,1,7,1,1,1,1,1,5,1,1,1]
def PUtail : List ℕ := [3,1]
def PU_huge : List ℕ := PUbig ++ PUtail

theorem prefixU : ∀ k, PU_huge <+: UU (13 + k) := by
  intro k
  induction k with
  | zero => native_decide
  | succ k ih =>
    have hstep : UU (13 + k) <+: UU (13 + k + 1) := by
      have h := UU_succ (10 + k)
      rw [show (10+k)+4 = 13+k+1 from by omega, show (10+k)+3 = 13+k from by omega] at h
      rw [h]; exact List.prefix_append _ _
    have : (13 + (k+1)) = 13 + k + 1 := by omega
    rw [this]; exact ih.trans hstep

theorem prefixU' {m : ℕ} (hm : 13 ≤ m) : PU_huge <+: UU m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact prefixU k

theorem RL_PUbig : run_lengths_nat PUbig = PV30 := by native_decide

theorem prefixV {m : ℕ} (hm : 13 ≤ m) : PV30 <+: run_lengths_nat (UU m) := by
  obtain ⟨tl, htl⟩ := prefixU' hm
  have hsplit : UU m = PUbig ++ (PUtail ++ tl) := by
    rw [← htl, show PU_huge = PUbig ++ PUtail from rfl, List.append_assoc]
  have hcut : ¬ (PUbig.getLast? = (PUtail ++ tl).head?) := by
    have h1 : PUbig.getLast? = some 1 := by native_decide
    have h2 : (PUtail ++ tl).head? = some 3 := rfl
    rw [h1, h2]; decide
  rw [hsplit, RL_append, if_neg hcut, RL_PUbig]
  exact List.prefix_append _ _

theorem sufU : ∀ k, PV30.reverse <:+ UU (14 + k) := by
  intro k
  have hu : UU (14 + k) = UU (13 + k) ++ (run_lengths_nat (UU (13 + k))).reverse := by
    have h := UU_succ (10 + k)
    rw [show (10+k)+4 = 14+k from by omega, show (10+k)+3 = 13+k from by omega] at h
    exact h
  obtain ⟨rest, hrest⟩ := prefixV (m := 13 + k) (by omega)
  rw [hu, ← hrest, List.reverse_append]
  exact ⟨UU (13+k) ++ rest.reverse, by rw [List.append_assoc]⟩

theorem sufU' {m : ℕ} (hm : 14 ≤ m) : PV30.reverse <:+ UU m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact sufU k

theorem RL_suffix' {s l : List ℕ} (h : s <:+ l) (hs : s ≠ []) :
    (run_lengths_nat s).tail <:+ run_lengths_nat l := by
  obtain ⟨t, rfl⟩ := h; exact RL_suffix t s hs

/- The six boundary facts for `u = UU m` (m ≥ 14), as needed by `cascade`. -/
theorem boundary {m : ℕ} (hm : 14 ≤ m) :
    (UU m).getLast? = some 1 ∧
    (run_lengths_nat (UU m)).getLast? = some 1 ∧
    (run_lengths_nat (UU m)).dropLast.getLast? = some 1 ∧
    (run_lengths_nat (run_lengths_nat (UU m))).getLast? = some 6 ∧
    (run_lengths_nat (run_lengths_nat (UU m))).dropLast.getLast? = some 1 ∧
    (run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m)))).getLast? = some 1 := by
  set σ := PV30.reverse with hσ
  have hσne : σ ≠ [] := by rw [hσ]; native_decide
  have hsuf0 : σ <:+ UU m := sufU' hm
  have hsuf1 : (run_lengths_nat σ).tail <:+ run_lengths_nat (UU m) := RL_suffix' hsuf0 hσne
  set σ1 := (run_lengths_nat σ).tail with hσ1
  have hσ1ne : σ1 ≠ [] := by rw [hσ1, hσ]; native_decide
  have hsuf2 : (run_lengths_nat σ1).tail <:+ run_lengths_nat (run_lengths_nat (UU m)) :=
    RL_suffix' hsuf1 hσ1ne
  set σ2 := (run_lengths_nat σ1).tail with hσ2
  have hσ2ne : σ2 ≠ [] := by rw [hσ2, hσ1, hσ]; native_decide
  have hsuf3 : (run_lengths_nat σ2).tail <:+
      run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m))) := RL_suffix' hsuf2 hσ2ne
  set σ3 := (run_lengths_nat σ2).tail with hσ3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [suffix_getLast? hsuf0 hσne]; rw [hσ]; native_decide
  · rw [suffix_getLast? hsuf1 hσ1ne]; rw [hσ1, hσ]; native_decide
  · rw [suffix_dropLast_getLast? hsuf1 (by rw [hσ1, hσ]; native_decide)]
    rw [hσ1, hσ]; native_decide
  · rw [suffix_getLast? hsuf2 hσ2ne]; rw [hσ2, hσ1, hσ]; native_decide
  · rw [suffix_dropLast_getLast? hsuf2 (by rw [hσ2, hσ1, hσ]; native_decide)]
    rw [hσ2, hσ1, hσ]; native_decide
  · rw [suffix_getLast? hsuf3 (by rw [hσ3, hσ2, hσ1, hσ]; native_decide)]
    rw [hσ3, hσ2, hσ1, hσ]; native_decide

/- ## The MASTER identity: RL³(UU n) = [6] ++ (UU (n-4)).tail -/

theorem Xrec {m : ℕ} (hm : 14 ≤ m) :
    run_lengths_nat (run_lengths_nat (run_lengths_nat (UU (m+1))))
      = run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m)))
        ++ (run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m))))).reverse := by
  obtain ⟨b1,b2,b3,b4,b5,b6⟩ := boundary hm
  have huu : UU (m+1) = UU m ++ (run_lengths_nat (UU m)).reverse := by
    have h := UU_succ (m-3)
    rw [show (m-3)+4 = m+1 from by omega, show (m-3)+3 = m from by omega] at h
    exact h
  rw [huu]
  exact cascade (UU m) b1 b2 b3 b4 b5 b6

theorem prefixU2 : ∀ k, ([2,1] : List ℕ) <+: UU (4 + k) := by
  intro k
  induction k with
  | zero => native_decide
  | succ k ih =>
    have hstep : UU (4 + k) <+: UU (4 + k + 1) := by
      have h := UU_succ (1 + k)
      rw [show (1+k)+4 = 4+k+1 from by omega, show (1+k)+3 = 4+k from by omega] at h
      rw [h]; exact List.prefix_append _ _
    have : (4 + (k+1)) = 4 + k + 1 := by omega
    rw [this]; exact ih.trans hstep

theorem prefixU2' {m : ℕ} (hm : 4 ≤ m) : ([2,1] : List ℕ) <+: UU m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact prefixU2 k

theorem RL_six_two (t' : List ℕ) :
    run_lengths_nat (6 :: 1 :: t') = run_lengths_nat (2 :: 1 :: t') := by
  rw [rl_cons_ne 6 1 t' (by decide), rl_cons_ne 2 1 t' (by decide)]

theorem MASTER : ∀ n, 14 ≤ n → run_lengths_nat (run_lengths_nat (run_lengths_nat (UU n)))
    = [6] ++ (UU (n - 4)).tail := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => native_decide
  | succ k ih =>
    have ihm := ih (by omega)
    -- UU (14+k - 4) starts with [2,1]
    obtain ⟨t', ht'⟩ := prefixU2' (m := 14 + k - 4) (by omega)
    -- ht' : [2,1] ++ t' = UU (14+k-4)
    have hU4 : UU (14 + k - 4) = 2 :: 1 :: t' := by
      rw [← ht']; rfl
    have htail4 : (UU (14 + k - 4)).tail = 1 :: t' := by rw [hU4]; rfl
    -- RL⁴(UU(14+k)) = RL(UU(14+k-4))
    have hRL4 : run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat (UU (14+k)))))
        = run_lengths_nat (UU (14 + k - 4)) := by
      rw [ihm]
      simp only [List.singleton_append]
      rw [htail4, RL_six_two, ← hU4]
    -- Xrec
    have hx := Xrec (m := 14 + k) (by omega)
    rw [show 14 + (k+1) = (14+k) + 1 from by omega]
    rw [hx, hRL4, ihm]
    -- UU(14+k-3) = UU(14+k-4) ++ (RL(UU(14+k-4))).reverse
    have huus : UU (14 + k + 1 - 4) = UU (14 + k - 4) ++ (run_lengths_nat (UU (14 + k - 4))).reverse := by
      have h := UU_succ (14 + k - 7)
      rw [show (14+k-7)+4 = 14+k+1-4 from by omega, show (14+k-7)+3 = 14+k-4 from by omega] at h
      exact h
    rw [huus]
    rw [List.tail_append_of_ne_nil (by rw [hU4]; simp)]
    rw [List.append_assoc]

/- ## Sequence layer: length / runs / sum -/

theorem rl_sum (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction l using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h t ih =>
    rename_i hIH
    rw [run_lengths_nat]
    simp only [List.sum_cons]
    rw [hIH, List.length_drop]
    have hle : (List.takeWhile (fun x => x = h) (h :: t)).length ≤ (h :: t).length :=
      (List.takeWhile_sublist _).length_le
    have heq : ih.length = (List.takeWhile (fun x => decide (x = h)) (h :: t)).length := rfl
    omega

def Ln (n : ℕ) : ℕ := (A381587_T n).length
def Rn (n : ℕ) : ℕ := (run_lengths_nat (UU n)).length
def Bn (n : ℕ) : ℕ := (run_lengths_nat (run_lengths_nat (UU n))).length
def Sn (n : ℕ) : ℕ := (A381587_T n).sum

theorem rl_rev_len (l : List ℕ) :
    (run_lengths_nat l.reverse).length = (run_lengths_nat l).length := by
  rw [rl_reverse, List.length_reverse]

theorem R0nat (k : ℕ) : Ln (k+4) = Ln (k+3) + Rn (k+3) := by
  show (A381587_T (k+4)).length = (A381587_T (k+3)).length + (run_lengths_nat (UU (k+3))).length
  have hT : A381587_T (k+4) = run_lengths_nat (A381587_T (k+3)).reverse ++ A381587_T (k+3) := rfl
  rw [hT, List.length_append, show (A381587_T (k+3)).reverse = UU (k+3) from rfl]
  omega

theorem Srecnat (k : ℕ) : Sn (k+4) = Ln (k+3) + Sn (k+3) := by
  show (A381587_T (k+4)).sum = (A381587_T (k+3)).length + (A381587_T (k+3)).sum
  have hT : A381587_T (k+4) = run_lengths_nat (A381587_T (k+3)).reverse ++ A381587_T (k+3) := rfl
  rw [hT, List.sum_append, rl_sum, List.length_reverse]

/- ## R1 and t2id combinatorial identities -/

theorem sum_UU (n : ℕ) : (UU n).sum = Sn n := by
  rw [UU, List.sum_reverse]; rfl

theorem R1nat {m : ℕ} (hm : 14 ≤ m) : Rn (m+1) + 1 = Rn m + Bn m := by
  obtain ⟨b1,b2,b3,b4,b5,b6⟩ := boundary hm
  have huu : UU (m+1) = UU m ++ (run_lengths_nat (UU m)).reverse := by
    have h := UU_succ (m-3)
    rw [show (m-3)+4 = m+1 from by omega, show (m-3)+3 = m from by omega] at h
    exact h
  have ha : UU m ≠ [] := ne_nil_of_getLast? _ _ b1
  have hRLne : run_lengths_nat (UU m) ≠ [] := ne_nil_of_getLast? _ _ b2
  have hb : (run_lengths_nat (UU m)).reverse ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, List.length_reverse]
    rw [List.length_pos_iff_ne_nil]; exact hRLne
  have hc : (UU m).getLast? = ((run_lengths_nat (UU m)).reverse).head? := by
    rw [List.head?_reverse, b1, b2]
  have hlen := RL_append_length_merge (UU m) ((run_lengths_nat (UU m)).reverse) ha hb hc
  have hRn1 : Rn (m+1) = (run_lengths_nat (UU m ++ (run_lengths_nat (UU m)).reverse)).length := by
    rw [Rn, huu]
  have hBeq : (run_lengths_nat ((run_lengths_nat (UU m)).reverse)).length = Bn m := by
    rw [rl_rev_len]; rfl
  have hBpos : 1 ≤ Bn m := by
    rw [Bn]
    exact List.length_pos_iff_ne_nil.mpr (ne_nil_of_getLast? _ _ b4)
  rw [hRn1, hlen, hBeq]
  show (run_lengths_nat (UU m)).length + Bn m - 1 + 1 = Rn m + Bn m
  rw [Rn]
  omega

theorem t2idnat {m : ℕ} (hm : 14 ≤ m) : Bn m = Sn (m-4) + 4 := by
  -- Bn m = sum (RL³ (UU m))
  have hsum : Bn m = (run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m)))).sum := by
    rw [rl_sum]; rfl
  rw [hsum, MASTER m hm]
  -- UU(m-4) = 2 :: 1 :: t'
  obtain ⟨t', ht'⟩ := prefixU2' (m := m - 4) (by omega)
  have hU4 : UU (m - 4) = 2 :: 1 :: t' := by rw [← ht']; rfl
  have htail : (UU (m - 4)).tail = 1 :: t' := by rw [hU4]; rfl
  have hsumUU : (UU (m - 4)).sum = Sn (m - 4) := sum_UU (m - 4)
  rw [hU4] at hsumUU
  -- (UU(m-4)).sum = 2 + 1 + t'.sum = Sn (m-4)
  simp only [List.singleton_append, List.sum_cons, htail]
  simp only [List.sum_cons] at hsumUU
  omega

/- ## Real recurrence -/

theorem starEq_real {i : ℕ} (hi : 10 ≤ i) :
    (Sn i : ℝ) = Ln (i+6) - 2*Ln (i+5) + Ln (i+4) - 3 := by
  have hr1 := R1nat (m := i+4) (by omega)
  have ht := t2idnat (m := i+4) (by omega)
  rw [show (i+4)-4 = i from by omega] at ht
  have hr0a := R0nat (i+1)
  have hr0b := R0nat (i+2)
  have c1 : (Rn (i+5):ℝ) + 1 = Rn (i+4) + Bn (i+4) := by exact_mod_cast hr1
  have c2 : (Bn (i+4):ℝ) = Sn i + 4 := by exact_mod_cast ht
  have c3 : (Ln (i+5):ℝ) = Ln (i+4) + Rn (i+4) := by exact_mod_cast hr0a
  have c4 : (Ln (i+6):ℝ) = Ln (i+5) + Rn (i+5) := by exact_mod_cast hr0b
  linarith

theorem LR_rec {k : ℕ} (hk : 10 ≤ k) :
    (Ln (k+7):ℝ) = 3*Ln (k+6) - 3*Ln (k+5) + Ln (k+4) + Ln k := by
  have s0 := starEq_real (i := k) hk
  have s1 := starEq_real (i := k+1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at s1
  have e3 : (Sn (k+1):ℝ) = Ln k + Sn k := by
    have h := Srecnat (k-3)
    rw [show (k-3)+4 = k+1 from by omega, show (k-3)+3 = k from by omega] at h
    exact_mod_cast h
  linarith
