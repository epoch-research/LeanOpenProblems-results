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
