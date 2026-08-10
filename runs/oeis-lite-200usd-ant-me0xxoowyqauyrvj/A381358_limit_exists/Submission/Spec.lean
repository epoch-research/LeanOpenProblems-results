import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000

private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

section RecTheory
open List Nat
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

/- Structurally-recursive equivalents that reduce in the kernel (for `decide`). -/
def rl2 : List ℕ → List ℕ
  | [] => []
  | [_] => [1]
  | a :: b :: t => if a = b then incFirst (rl2 (b::t)) else 1 :: rl2 (b::t)

def T2 : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k+4 => rl2 (T2 (k+3)).reverse ++ T2 (k+3)

theorem rl2_eq : ∀ l, rl2 l = run_lengths_nat l := by
  intro l
  induction l using rl2.induct with
  | case1 => rw [rl2, rl_nil]
  | case2 a => rw [rl2, rl_single]
  | case3 b t ih =>
    rw [rl2, if_pos (rfl : b = b), ih, rl_cons_eq]
  | case4 a b t h ih =>
    rw [rl2, if_neg h, ih, rl_cons_ne a b t h]

theorem T2_eq : ∀ n, T2 n = A381587_T n := by
  intro n
  induction n using T2.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 => rfl
  | case5 k ih =>
    show rl2 (T2 (k+3)).reverse ++ T2 (k+3)
      = run_lengths_nat (A381587_T (k+3)).reverse ++ A381587_T (k+3)
    rw [ih, rl2_eq]

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


-- U n := reverse of T n
def UU (n : ℕ) : List ℕ := (A381587_T n).reverse

/-- Rewrite `run_lengths_nat`/`A381587_T`/`UU` to their kernel-reducible
counterparts and finish by `decide`. -/
macro "rl_decide" : tactic =>
  `(tactic| ((try simp only [UU, ← T2_eq, ← rl2_eq]); decide))


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
  | zero => rl_decide
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

theorem RL_PUbig : run_lengths_nat PUbig = PV30 := by rl_decide

theorem prefixV {m : ℕ} (hm : 13 ≤ m) : PV30 <+: run_lengths_nat (UU m) := by
  obtain ⟨tl, htl⟩ := prefixU' hm
  have hsplit : UU m = PUbig ++ (PUtail ++ tl) := by
    rw [← htl, show PU_huge = PUbig ++ PUtail from rfl, List.append_assoc]
  have hcut : ¬ (PUbig.getLast? = (PUtail ++ tl).head?) := by
    have h1 : PUbig.getLast? = some 1 := by rl_decide
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
  have hσne : σ ≠ [] := by rw [hσ]; rl_decide
  have hsuf0 : σ <:+ UU m := sufU' hm
  have hsuf1 : (run_lengths_nat σ).tail <:+ run_lengths_nat (UU m) := RL_suffix' hsuf0 hσne
  set σ1 := (run_lengths_nat σ).tail with hσ1
  have hσ1ne : σ1 ≠ [] := by rw [hσ1, hσ]; rl_decide
  have hsuf2 : (run_lengths_nat σ1).tail <:+ run_lengths_nat (run_lengths_nat (UU m)) :=
    RL_suffix' hsuf1 hσ1ne
  set σ2 := (run_lengths_nat σ1).tail with hσ2
  have hσ2ne : σ2 ≠ [] := by rw [hσ2, hσ1, hσ]; rl_decide
  have hsuf3 : (run_lengths_nat σ2).tail <:+
      run_lengths_nat (run_lengths_nat (run_lengths_nat (UU m))) := RL_suffix' hsuf2 hσ2ne
  set σ3 := (run_lengths_nat σ2).tail with hσ3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [suffix_getLast? hsuf0 hσne]; rw [hσ]; rl_decide
  · rw [suffix_getLast? hsuf1 hσ1ne]; rw [hσ1, hσ]; rl_decide
  · rw [suffix_dropLast_getLast? hsuf1 (by rw [hσ1, hσ]; rl_decide)]
    rw [hσ1, hσ]; rl_decide
  · rw [suffix_getLast? hsuf2 hσ2ne]; rw [hσ2, hσ1, hσ]; rl_decide
  · rw [suffix_dropLast_getLast? hsuf2 (by rw [hσ2, hσ1, hσ]; rl_decide)]
    rw [hσ2, hσ1, hσ]; rl_decide
  · rw [suffix_getLast? hsuf3 (by rw [hσ3, hσ2, hσ1, hσ]; rl_decide)]
    rw [hσ3, hσ2, hσ1, hσ]; rl_decide

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
  | zero => rl_decide
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
  | zero => rl_decide
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

theorem Ln_eq (n : ℕ) : Ln n = (T2 n).length := by rw [Ln, T2_eq]
theorem Sn_eq (n : ℕ) : Sn n = (T2 n).sum := by rw [Sn, T2_eq]


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

end RecTheory

/- ===================== ASY ENGINE ===================== -/
open scoped BigOperators NNReal
open Filter Topology

namespace Asy

-- Activate the L∞ operator norm (sup over rows of L1 norm) on square matrices.
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

noncomputable def Amat : Matrix (Fin 7) (Fin 7) ℝ :=
  !![3,-3,1,0,0,0,1; 1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0]

noncomputable def NN (L : ℕ → ℝ) (k : ℕ) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of (fun i j => L (k + (6 - i.val) + j.val))

-- test: norm_mul_le works
example (X Y : Matrix (Fin 7) (Fin 7) ℝ) : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le X Y

example : ‖(1 : Matrix (Fin 7) (Fin 7) ℝ)‖ = 1 := norm_one

set_option maxHeartbeats 4000000 in
theorem AN_step (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (k : ℕ) (hk : 4 ≤ k) :
    Amat * NN L k = NN L (k+1) := by
  ext i j
  fin_cases i
  · -- row 0
    fin_cases j <;>
    · simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
        zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
      norm_num
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
      first
      | (have h := hrec (k+0) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+1) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+2) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+3) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+4) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+5) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+6) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
  · show (Amat * NN L k) (1:Fin 7) j = NN L (k+1) (1:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
  · show (Amat * NN L k) (2:Fin 7) j = NN L (k+1) (2:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (3:Fin 7) j = NN L (k+1) (3:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (4:Fin 7) j = NN L (k+1) (4:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (5:Fin 7) j = NN L (k+1) (5:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (6:Fin 7) j = NN L (k+1) (6:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1

/-! ### Norm helper lemmas for the L∞ operator norm -/

theorem nnentry_le (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) : ‖A i j‖₊ ≤ ‖A‖₊ := by
  rw [Matrix.linfty_opNNNorm_def]
  calc ‖A i j‖₊ ≤ ∑ j', ‖A i j'‖₊ :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (fun _ _ => zero_le _) (Finset.mem_univ j)
    _ ≤ _ := Finset.le_sup (f := fun i => ∑ j', ‖A i j'‖₊) (Finset.mem_univ i)

theorem entry_le (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) : |A i j| ≤ ‖A‖ := by
  have h1 : ‖A i j‖ ≤ ‖A‖ := by exact_mod_cast nnentry_le A i j
  rwa [Real.norm_eq_abs] at h1

theorem nn_le_of_abs_le (x b : ℝ) (h : |x| ≤ b) : ‖x‖₊ ≤ b.toNNReal := by
  rw [← Real.norm_eq_abs] at h
  have : ‖x‖₊ ≤ (b.toNNReal : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_trans (norm_nonneg _) h)]
    exact h
  exact this

theorem linftyOp_le (A : Matrix (Fin 7) (Fin 7) ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : ‖A‖ ≤ 7 * b := by
  have key : ‖A‖₊ ≤ 7 * b.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc (∑ j, ‖A i j‖₊) ≤ ∑ _j : Fin 7, b.toNNReal :=
            Finset.sum_le_sum (fun j _ => nn_le_of_abs_le _ _ (h i j))
      _ = 7 * b.toNNReal := by rw [Finset.sum_const]; simp
  have h2 : ‖A‖ ≤ ((7 * b.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast key
  rwa [NNReal.coe_mul, Real.coe_toNNReal _ hb] at h2

/-! ### Powers of `Amat` and the matrix recurrence -/

theorem AN_pow (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (m : ℕ) : Amat ^ m * NN L 5 = NN L (5 + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, AN_step L hrec (5+m) (by omega)]
    congr 1

theorem Apow_eq (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) (m : ℕ) :
    Amat ^ m = NN L (5 + m) * C := by
  have h := AN_pow L hrec m
  calc Amat ^ m = Amat ^ m * (NN L 5 * C) := by rw [hC, mul_one]
    _ = (Amat ^ m * NN L 5) * C := by rw [mul_assoc]
    _ = NN L (5 + m) * C := by rw [h]

/-! ### L-based norm bounds -/

theorem NN_entry00 (L : ℕ → ℝ) (k : ℕ) : NN L k 0 0 = L (k + 6) := by
  simp [NN]

theorem NN_norm_le (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n) (hmono : Monotone L) (k : ℕ) :
    ‖NN L k‖ ≤ 7 * L (k + 12) := by
  apply linftyOp_le _ _ (hLnn _)
  intro i j
  have hb : k + (6 - i.val) + j.val ≤ k + 12 := by
    have := i.isLt; have := j.isLt; omega
  rw [NN, Matrix.of_apply, abs_of_nonneg (hLnn _)]
  exact hmono hb

theorem NN_ne_zero (L : ℕ → ℝ) (hpos : 0 < L (k + 6)) : NN L k ≠ 0 := by
  intro hz
  have : NN L k 0 0 = 0 := by rw [hz]; rfl
  rw [NN_entry00] at this
  linarith

theorem normpow_pos (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11) (m : ℕ) : 0 < ‖Amat ^ m‖ := by
  rw [norm_pos_iff]
  intro hz
  have h := AN_pow L hrec m
  rw [hz, zero_mul] at h
  have hne : NN L (5 + m) ≠ 0 := by
    apply NN_ne_zero
    have : 0 < L 11 := hpos
    have : (11 : ℕ) ≤ 5 + m + 6 := by omega
    calc (0:ℝ) < L 11 := hpos
      _ ≤ L (5 + m + 6) := hmono this
  exact hne h.symm

theorem normpow_lb (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (n : ℕ) : L (n + 11) ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := by
  have h := AN_pow L hrec n
  have h1 : L (5 + n + 6) ≤ ‖NN L (5 + n)‖ := by
    rw [← NN_entry00 L (5 + n)]
    have h2 := entry_le (NN L (5 + n)) 0 0
    rwa [abs_of_nonneg (by rw [NN_entry00]; exact hLnn _)] at h2
  have h3 : ‖NN L (5 + n)‖ ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := by
    rw [← h]; exact norm_mul_le _ _
  have he : 5 + n + 6 = n + 11 := by omega
  rw [he] at h1
  linarith

theorem normpow_ub (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n) (hmono : Monotone L)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) (n : ℕ) :
    ‖Amat ^ n‖ ≤ 7 * L (n + 17) * ‖C‖ := by
  rw [Apow_eq L hrec C hC n]
  calc ‖NN L (5 + n) * C‖ ≤ ‖NN L (5 + n)‖ * ‖C‖ := norm_mul_le _ _
    _ ≤ 7 * L ((5 + n) + 12) * ‖C‖ := by
        apply mul_le_mul_of_nonneg_right (NN_norm_le L hLnn hmono (5 + n)) (norm_nonneg _)
    _ = 7 * L (n + 17) * ‖C‖ := by rw [show (5 + n) + 12 = n + 17 from by omega]

theorem L_ub (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (n : ℕ) (hn : 11 ≤ n) : L n ≤ ‖Amat ^ (n - 11)‖ * ‖NN L 5‖ := by
  have h := normpow_lb L hLnn hrec (n - 11)
  rwa [show (n - 11) + 11 = n from by omega] at h

/-! ### Shift/limit helpers -/

theorem shift_nat_atTop (d : ℕ) : Tendsto (fun n => n - d) atTop atTop :=
  Filter.tendsto_atTop.2 (fun N => eventually_atTop.2 ⟨N+d, fun n hn => by omega⟩)

theorem shift_tendsto (c : ℕ → ℝ) (γ B : ℝ) (d : ℕ)
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (c (n - d) + B) / n) atTop (𝓝 γ) := by
  have hB : Tendsto (fun n : ℕ => B / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat B
  have ha : Tendsto (fun n => c (n - d) / (↑(n - d) : ℝ)) atTop (𝓝 γ) := hc.comp (shift_nat_atTop d)
  have hb : Tendsto (fun n : ℕ => (↑(n - d) : ℝ) / (n:ℝ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 - (d:ℝ) / (n:ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (d:ℝ))
    rw [sub_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop (d+1)] with n hn
    have hle : d ≤ n := by omega
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Nat.cast_sub hle]
    field_simp
  have hprod : Tendsto (fun n => (c (n - d) / (↑(n - d):ℝ)) * ((↑(n - d):ℝ) / (n:ℝ))) atTop (𝓝 (γ * 1)) :=
    ha.mul hb
  rw [mul_one] at hprod
  have hsum := hprod.add hB
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (d+1)] with n hn
  have hnd : (↑(n - d):ℝ) ≠ 0 := by
    have : 0 < n - d := by omega
    positivity
  field_simp

/-! ### The growth-rate limit -/

theorem loglim (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) :
    ∃ γ : ℝ, Tendsto (fun n => Real.log (L n) / n) atTop (𝓝 γ) := by
  set c : ℕ → ℝ := fun k => Real.log ‖Amat ^ k‖ with hc_def
  have hnp : ∀ m, 0 < ‖Amat ^ m‖ := normpow_pos L hrec hmono hpos
  -- positivity of the two constant matrices
  have hNN5_pos : 0 < ‖NN L 5‖ := by
    have : 0 < L 11 := hpos
    have h2 : L (5 + 6) ≤ ‖NN L 5‖ := by
      rw [← NN_entry00 L 5]
      have h3 := entry_le (NN L 5) 0 0
      rwa [abs_of_nonneg (by rw [NN_entry00]; exact hLnn _)] at h3
    have : (11:ℕ) = 5 + 6 := by norm_num
    rw [this] at hpos; linarith
  have hC_pos : 0 < ‖C‖ := by
    rw [norm_pos_iff]
    rintro rfl
    rw [mul_zero] at hC
    exact (one_ne_zero hC.symm)
  -- subadditivity
  have hsub : Subadditive c := by
    intro m n
    show Real.log ‖Amat ^ (m+n)‖ ≤ Real.log ‖Amat ^ m‖ + Real.log ‖Amat ^ n‖
    rw [pow_add, ← Real.log_mul (ne_of_gt (hnp m)) (ne_of_gt (hnp n))]
    apply Real.log_le_log
    · rw [← pow_add]; exact hnp _
    · exact norm_mul_le _ _
  -- lower bound on c n : ‖Amat^n‖ ≥ L 11 / ‖NN L 5‖
  set P : ℝ := L 11 / ‖NN L 5‖ with hP_def
  have hP_pos : 0 < P := div_pos hpos hNN5_pos
  have hcn_lb : ∀ n, Real.log P ≤ c n := by
    intro n
    apply Real.log_le_log hP_pos
    rw [hP_def, div_le_iff₀ hNN5_pos]
    calc L 11 ≤ L (n + 11) := hmono (by omega)
      _ ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := normpow_lb L hLnn hrec n
  -- BddBelow
  have hbb : BddBelow (Set.range fun n => c n / n) := by
    refine ⟨min 0 (Real.log P), ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with h0 | hn1
    · subst h0; simp only [Nat.cast_zero, div_zero]; exact min_le_left _ _
    · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hge : Real.log P ≤ c n := hcn_lb n
      rcases le_total 0 (Real.log P) with hlp | hlp
      · have : (0:ℝ) ≤ c n / n := div_nonneg (le_trans hlp hge) (le_of_lt hnpos)
        exact le_trans (min_le_left _ _) this
      · have hmin : min 0 (Real.log P) = Real.log P := min_eq_right hlp
        rw [hmin]
        rw [le_div_iff₀ hnpos]
        have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith [hge, hlp, h1, mul_nonneg (neg_nonneg.2 hlp) (by linarith : (0:ℝ) ≤ (n:ℝ) - 1)]
  obtain ⟨γ, hγ⟩ : ∃ γ, Tendsto (fun n => c n / n) atTop (𝓝 γ) :=
    ⟨hsub.lim, hsub.tendsto_lim hbb⟩
  refine ⟨γ, ?_⟩
  -- squeeze
  have hupper : Tendsto (fun n => (c (n - 11) + Real.log ‖NN L 5‖) / n) atTop (𝓝 γ) :=
    shift_tendsto c γ (Real.log ‖NN L 5‖) 11 hγ
  have hlower : Tendsto (fun n => (c (n - 17) + (-(Real.log 7 + Real.log ‖C‖))) / n) atTop (𝓝 γ) :=
    shift_tendsto c γ (-(Real.log 7 + Real.log ‖C‖)) 17 hγ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · -- lower : (c(n-17) - (log7+log‖C‖))/n ≤ log L n / n
    filter_upwards [eventually_ge_atTop 17] with n hn
    have hLpos : 0 < L n := lt_of_lt_of_le hpos (hmono (by omega))
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    -- ‖Amat^(n-17)‖ ≤ 7 * L n * ‖C‖
    have hub := normpow_ub L hLnn hmono hrec C hC (n - 17)
    rw [show (n - 17) + 17 = n from by omega] at hub
    have hpos7 : (0:ℝ) < 7 * L n * ‖C‖ := by positivity
    have hlog : c (n - 17) ≤ Real.log 7 + Real.log (L n) + Real.log ‖C‖ := by
      have := Real.log_le_log (hnp (n - 17)) hub
      rw [Real.log_mul (by positivity) (ne_of_gt hC_pos),
          Real.log_mul (by norm_num) (ne_of_gt hLpos)] at this
      linarith
    rw [div_le_div_iff_of_pos_right hnpos]
    linarith
  · -- upper : log L n / n ≤ (c(n-11) + log‖NN L5‖)/n
    filter_upwards [eventually_ge_atTop 17] with n hn
    have hLpos : 0 < L n := lt_of_lt_of_le hpos (hmono (by omega))
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hub := L_ub L hLnn hrec n (by omega)
    have hlog : Real.log (L n) ≤ c (n - 11) + Real.log ‖NN L 5‖ := by
      have := Real.log_le_log hLpos hub
      rwa [Real.log_mul (ne_of_gt (hnp (n-11))) (ne_of_gt hNN5_pos)] at this
    rw [div_le_div_iff_of_pos_right hnpos]
    linarith

/-! ### From log-limit to rpow-limit, and the row-sum sandwich -/

theorem lognat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n:ℝ) / (n:ℝ)) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using h.tendsto_div_nhds_zero
  exact h2.comp tendsto_natCast_atTop_atTop

theorem rpow_tendsto_of_loglim (f : ℕ → ℝ) (γ : ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < f n)
    (hlog : Tendsto (fun n => Real.log (f n) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (f n) ^ ((n:ℝ)⁻¹)) atTop (𝓝 (Real.exp γ)) := by
  have hexp : Tendsto (fun n => Real.exp (Real.log (f n) / n)) atTop (𝓝 (Real.exp γ)) :=
    (Real.continuous_exp.tendsto γ).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hpos] with n hfn
  rw [Real.rpow_def_of_pos hfn, div_eq_mul_inv]

theorem S_loglim (L S : ℕ → ℝ) (γ : ℝ) (N : ℕ)
    (hL : Tendsto (fun n => Real.log (L n) / n) atTop (𝓝 γ))
    (hLpos : ∀ n, N ≤ n → 0 < L (n-1))
    (hlb : ∀ n, N ≤ n → L (n-1) ≤ S n)
    (hub : ∀ n, N ≤ n → S n ≤ (n:ℝ) * L (n-1)) :
    Tendsto (fun n => Real.log (S n) / n) atTop (𝓝 γ) := by
  have hlow : Tendsto (fun n => (Real.log (L (n-1)) + 0) / n) atTop (𝓝 γ) :=
    shift_tendsto (fun k => Real.log (L k)) γ 0 1 hL
  have hup : Tendsto (fun n : ℕ => (Real.log (n:ℝ) + Real.log (L (n-1))) / (n:ℝ)) atTop (𝓝 γ) := by
    have e : (fun n:ℕ => (Real.log (n:ℝ) + Real.log (L (n-1)))/(n:ℝ))
           = fun n : ℕ => Real.log (n:ℝ) / (n:ℝ) + (Real.log (L (n-1)) + 0)/(n:ℝ) := by
      funext n; rw [add_zero]; ring
    rw [e]
    have := (lognat_div_tendsto_zero).add hlow
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hLp : 0 < L (n-1) := hLpos n hNn
    rw [add_zero, div_le_div_iff_of_pos_right hnpos]
    exact Real.log_le_log hLp (hlb n hNn)
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hLp : 0 < L (n-1) := hLpos n hNn
    have hSp : 0 < S n := lt_of_lt_of_le hLp (hlb n hNn)
    rw [div_le_div_iff_of_pos_right hnpos]
    have h2 := Real.log_le_log hSp (hub n hNn)
    rwa [Real.log_mul (by exact_mod_cast (by omega : (0:ℕ) < n).ne') (ne_of_gt hLp)] at h2

/-! ### Top-level engine -/

theorem main_engine (L S : ℕ → ℝ)
    (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1)
    (N : ℕ)
    (hlb : ∀ n, N ≤ n → L (n-1) ≤ S n)
    (hub : ∀ n, N ≤ n → S n ≤ (n:ℝ) * L (n-1))
    (hSpos : ∀ᶠ n in atTop, 0 < S n) :
    ∃ ρ : ℝ, Tendsto (fun n => (S n) ^ ((n:ℝ)⁻¹)) atTop (𝓝 ρ) := by
  obtain ⟨γ, hγ⟩ := loglim L hLnn hrec hmono hpos C hC
  have hLpos1 : ∀ n, max N 12 ≤ n → 0 < L (n-1) := fun n hn =>
    lt_of_lt_of_le hpos (hmono (by omega))
  have hS := S_loglim L S γ (max N 12) hγ hLpos1
       (fun n hn => hlb n (le_trans (le_max_left _ _) hn))
       (fun n hn => hub n (le_trans (le_max_left _ _) hn))
  exact ⟨Real.exp γ, rpow_tendsto_of_loglim S γ hSpos hS⟩

end Asy

/- ===================== GLUE ===================== -/

theorem Ln_mono : Monotone Ln := by
  apply monotone_nat_of_le_succ
  intro n
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> (simp only [Ln_eq]; decide)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show 3+k+1 = k+4 from by omega, show 3+k = k+3 from by omega, R0nat k]
    exact Nat.le_add_right _ _

theorem Sn_mono : Monotone Sn := by
  apply monotone_nat_of_le_succ
  intro n
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> (simp only [Sn_eq]; decide)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show 3+k+1 = k+4 from by omega, show 3+k = k+3 from by omega, Srecnat k]
    exact Nat.le_add_left _ _

theorem Ln_mono_real : Monotone (fun n => (Ln n : ℝ)) :=
  fun a b hab => Nat.cast_le.mpr (Ln_mono hab)

theorem hpos_glue : 0 < (Ln 11 : ℝ) := by
  have : Ln 11 = 66 := by rw [Ln_eq]; decide
  rw [this]; norm_num

theorem hrec_glue : ∀ k, 4 ≤ k →
    (Ln (k+7):ℝ) = 3*(Ln (k+6):ℝ) - 3*(Ln (k+5):ℝ) + (Ln (k+4):ℝ) + (Ln k:ℝ) := by
  have v4 : Ln 4 = 2 := by rw [Ln_eq]; decide
  have v5 : Ln 5 = 4 := by rw [Ln_eq]; decide
  have v6 : Ln 6 = 6 := by rw [Ln_eq]; decide
  have v7 : Ln 7 = 10 := by rw [Ln_eq]; decide
  have v8 : Ln 8 = 16 := by rw [Ln_eq]; decide
  have v9 : Ln 9 = 26 := by rw [Ln_eq]; decide
  have v10 : Ln 10 = 42 := by rw [Ln_eq]; decide
  have v11 : Ln 11 = 66 := by rw [Ln_eq]; decide
  have v12 : Ln 12 = 102 := by rw [Ln_eq]; decide
  have v13 : Ln 13 = 156 := by rw [Ln_eq]; decide
  have v14 : Ln 14 = 238 := by rw [Ln_eq]; decide
  have v15 : Ln 15 = 364 := by rw [Ln_eq]; decide
  have v16 : Ln 16 = 560 := by rw [Ln_eq]; decide
  intro k hk
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;>
      norm_num [v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16]
  · exact LR_rec h

noncomputable def Cmat : Matrix (Fin 7) (Fin 7) ℝ :=
  !![(-1/2:ℝ),2,-5/2,1/2,1,-1/2,0;
     0,-1/2,2,-5/2,1/2,1,-1/2;
     -1/2,3/2,-2,5/2,-5/2,1/2,1;
     1,-7/2,9/2,-3,5/2,-5/2,1/2;
     0,3/2,-9/2,9/2,-2,2,-5/2;
     -1,3/2,3/2,-7/2,3/2,-1/2,2;
     1/2,-1,0,1,-1/2,0,-1/2]

set_option maxHeartbeats 4000000 in
theorem hC_lemma : Asy.NN (fun n => (Ln n:ℝ)) 5 * Cmat = 1 := by
  have v5 : Ln 5 = 4 := by rw [Ln_eq]; decide
  have v6 : Ln 6 = 6 := by rw [Ln_eq]; decide
  have v7 : Ln 7 = 10 := by rw [Ln_eq]; decide
  have v8 : Ln 8 = 16 := by rw [Ln_eq]; decide
  have v9 : Ln 9 = 26 := by rw [Ln_eq]; decide
  have v10 : Ln 10 = 42 := by rw [Ln_eq]; decide
  have v11 : Ln 11 = 66 := by rw [Ln_eq]; decide
  have v12 : Ln 12 = 102 := by rw [Ln_eq]; decide
  have v13 : Ln 13 = 156 := by rw [Ln_eq]; decide
  have v14 : Ln 14 = 238 := by rw [Ln_eq]; decide
  have v15 : Ln 15 = 364 := by rw [Ln_eq]; decide
  have v16 : Ln 16 = 560 := by rw [Ln_eq]; decide
  have v17 : Ln 17 = 868 := by rw [Ln_eq]; decide
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Asy.NN, Cmat, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val',
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub,
      Nat.reduceAdd] <;>
    norm_num [v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17]

theorem hlb_glue : ∀ n, 4 ≤ n → (Ln (n-1):ℝ) ≤ (Sn n:ℝ) := by
  intro n hn
  have h := Srecnat (n-4)
  rw [show (n-4)+4 = n from by omega, show (n-4)+3 = n-1 from by omega] at h
  have hnat : Ln (n-1) ≤ Sn n := by omega
  exact_mod_cast hnat

theorem hub_glue : ∀ n, 4 ≤ n → (Sn n:ℝ) ≤ (n:ℝ) * (Ln (n-1):ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [show Sn 4 = 3 from by rw [Sn_eq]; decide, show Ln 3 = 1 from by rw [Ln_eq]; decide]
  | succ n hn ih =>
    have hs := Srecnat (n-3)
    rw [show (n-3)+4 = n+1 from by omega, show (n-3)+3 = n from by omega] at hs
    have hsr : (Sn (n+1):ℝ) = (Ln n:ℝ) + (Sn n:ℝ) := by exact_mod_cast hs
    have hmono' : (Ln (n-1):ℝ) ≤ (Ln n:ℝ) := by exact_mod_cast Ln_mono (show n-1 ≤ n by omega)
    have hcoef : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
    have hprod : (n:ℝ)*(Ln (n-1):ℝ) ≤ (n:ℝ)*(Ln n:ℝ) := mul_le_mul_of_nonneg_left hmono' hcoef
    rw [show (n+1)-1 = n from by omega]
    push_cast
    nlinarith [hsr, ih, hprod]

theorem hSpos_glue : ∀ᶠ n in Filter.atTop, 0 < (Sn n:ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have h1 : 0 < Sn n := by
    have : Sn 1 ≤ Sn n := Sn_mono hn
    have : (1:ℕ) ≤ Sn n := by
      have h0 : Sn 1 = 1 := by rw [Sn_eq]; decide
      omega
    omega
  exact_mod_cast h1

theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  obtain ⟨ρ, hρ⟩ := Asy.main_engine (fun n => (Ln n:ℝ)) (fun n => (Sn n:ℝ))
    (fun n => Nat.cast_nonneg _)
    hrec_glue Ln_mono_real hpos_glue
    Cmat hC_lemma 4 hlb_glue hub_glue hSpos_glue
  exact ⟨ρ, hρ⟩

