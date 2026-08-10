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
