import FormalConjectures.Util.ProblemImports
open List Nat
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.docString.empty false


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

noncomputable section

private def bump : List ℕ → List ℕ
  | [] => []
  | a::as => (a+1)::as

private def rr : List ℕ → List ℕ
  | [] => []
  | a::as => match as with
    | [] => [1]
    | b::bs => if a=b then bump (rr as) else 1::rr as

private lemma rr_nil : rr [] = [] := rfl
private lemma rr_singleton (a : ℕ) : rr [a] = [1] := rfl
private lemma rr_cons_cons (a b : ℕ) (xs : List ℕ) :
    rr (a::b::xs) = if a=b then bump (rr (b::xs)) else 1::rr (b::xs) := rfl

private lemma rr_ne_nil (a : ℕ) (xs : List ℕ) : rr (a::xs) ≠ [] := by
  induction xs generalizing a with
  | nil => simp [rr_nil, rr_singleton, rr_cons_cons]
  | cons b bs ih =>
    rw [rr_cons_cons]
    split
    · cases hr : rr (b::bs) with
      | nil => exact (ih b hr).elim
      | cons z zs => simp [bump]
    · simp

private lemma run_lengths_pair (a b : ℕ) (xs : List ℕ) :
    run_lengths_nat (a::b::xs) =
      if a=b then bump (run_lengths_nat (b::xs)) else 1::run_lengths_nat (b::xs) := by
  by_cases h : a = b
  · subst b
    rw [if_pos rfl, run_lengths_nat.eq_2, run_lengths_nat.eq_2]
    simp only [List.takeWhile_cons, bump]
    simp only [decide_true, if_true, List.length_cons, List.drop_succ_cons]
  · rw [if_neg h, run_lengths_nat.eq_2]
    have h' : b ≠ a := Ne.symm h
    simp [h']

private lemma run_lengths_eq_rr (xs : List ℕ) : run_lengths_nat xs = rr xs := by
  induction xs with
  | nil => simp [run_lengths_nat.eq_1, rr_nil, rr_singleton, rr_cons_cons]
  | cons a as ih =>
    cases as with
    | nil => simp [run_lengths_nat.eq_2, run_lengths_nat.eq_1, rr_nil, rr_singleton, rr_cons_cons]
    | cons b bs => rw [run_lengths_pair, rr_cons_cons, ih]

private def glue (xs ys : List ℕ) : List ℕ :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | a::as, b::bs => (a::as).dropLast ++ ((a::as).getLast (by simp) + b)::bs

@[simp] private lemma glue_cons_cons (a b : ℕ) (bs : List ℕ) (z : ℕ) (zs : List ℕ) :
    glue (a::b::bs) (z::zs) = a :: glue (b::bs) (z::zs) := by
  simp [glue, List.dropLast_cons_of_ne_nil]

private lemma bump_append_of_ne (xs ys : List ℕ) (h : xs ≠ []) :
    bump (xs ++ ys) = bump xs ++ ys := by
  cases xs <;> simp_all [bump]

private lemma bump_glue (xs ys : List ℕ) (h : xs ≠ []) :
    bump (glue xs ys) = glue (bump xs) ys := by
  rcases xs with _ | ⟨a, as⟩
  · contradiction
  rcases as with _ | ⟨b, bs⟩
  · cases ys <;> simp [glue, bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · cases ys with
    | nil => rfl
    | cons z zs =>
      rw [glue_cons_cons]
      rw [show bump (a::b::bs) = (a+1)::b::bs by rfl, glue_cons_cons]
      rfl

private lemma rr_append_of_last_ne (xs : List ℕ) (b a : ℕ) (bs : List ℕ)
    (h : xs.getLast? = some a) (hne : a ≠ b) :
    rr (xs ++ b::bs) = rr xs ++ rr (b::bs) := by
  induction xs with
  | nil => simp at h
  | cons c cs ih =>
    rcases cs with _ | ⟨d, ds⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst c
      simp [rr_nil, rr_singleton, rr_cons_cons, hne]
    · have ht : (d::ds).getLast? = some a := by simpa using h
      by_cases hcd : c = d
      · simp only [List.cons_append, rr_nil, rr_singleton, rr_cons_cons, if_pos hcd]
        change bump (rr ((d::ds) ++ b::bs)) = bump (rr (d::ds)) ++ rr (b::bs)
        rw [ih ht]
        exact bump_append_of_ne _ _ (rr_ne_nil d ds)
      · simp only [List.cons_append, rr_nil, rr_singleton, rr_cons_cons, if_neg hcd, List.cons.injEq, true_and]
        exact ih ht

private lemma rr_append_of_last_eq (xs : List ℕ) (b : ℕ) (bs : List ℕ)
    (h : xs.getLast? = some b) :
    rr (xs ++ b::bs) = glue (rr xs) (rr (b::bs)) := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    rcases as with _ | ⟨c, cs⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst a
      simp only [List.singleton_append, rr_nil, rr_singleton, rr_cons_cons, if_pos rfl]
      cases hr : rr (b::bs) with
      | nil => exact (rr_ne_nil b bs hr).elim
      | cons z zs => simp [bump, glue, Nat.add_comm]
    · have ht : (c::cs).getLast? = some b := by simpa using h
      by_cases hac : a = c
      · simp only [List.cons_append, rr_nil, rr_singleton, rr_cons_cons, if_pos hac]
        change bump (rr ((c::cs) ++ b::bs)) = glue (bump (rr (c::cs))) (rr (b::bs))
        rw [ih ht]
        exact bump_glue _ _ (rr_ne_nil c cs)
      · simp only [List.cons_append, rr_nil, rr_singleton, rr_cons_cons, if_neg hac]
        change 1 :: rr ((c::cs) ++ b::bs) = glue (1::rr (c::cs)) (rr (b::bs))
        rw [ih ht]
        cases hx : rr (c::cs) with
        | nil => exact (rr_ne_nil c cs hx).elim
        | cons z zs =>
          cases hy : rr (b::bs) with
          | nil => exact (rr_ne_nil b bs hy).elim
          | cons w ws => exact (glue_cons_cons 1 z zs w ws).symm

private def bumpLast : List ℕ → List ℕ
  | [] => []
  | [a] => [a+1]
  | a::b::xs => a :: bumpLast (b::xs)
termination_by xs => xs.length

private lemma glue_singleton (xs : List ℕ) (hn : xs ≠ []) : glue xs [1] = bumpLast xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [glue, bumpLast]
    · rw [glue_cons_cons, bumpLast]
      exact congrArg (a :: ·) (ih (by simp))

private lemma bumpLast_append_singleton (xs : List ℕ) (a : ℕ) :
    bumpLast (xs ++ [a]) = xs ++ [a+1] := by
  induction xs with
  | nil => simp [bumpLast]
  | cons b bs ih =>
    rcases bs with _ | ⟨c, cs⟩
    · simp [bumpLast]
    · simp only [List.cons_append, bumpLast, List.cons.injEq, true_and]
      exact ih

private lemma reverse_bump (xs : List ℕ) : (bump xs).reverse = bumpLast xs.reverse := by
  cases xs with
  | nil => simp [bump, bumpLast]
  | cons a as => simp [bump, bumpLast_append_singleton]

private lemma rr_reverse (xs : List ℕ) : rr xs.reverse = (rr xs).reverse := by
  induction xs with
  | nil => simp [rr_nil, rr_singleton, rr_cons_cons]
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [rr_nil, rr_singleton, rr_cons_cons]
    · rw [List.reverse_cons]
      by_cases h : a = b
      · rw [rr_append_of_last_eq _ a [] (by simp [h]), ih]
        simp only [rr_nil, rr_singleton, rr_cons_cons, if_pos h, List.reverse_cons]
        rw [glue_singleton _ (by simpa using rr_ne_nil b bs), ← reverse_bump]
      · rw [rr_append_of_last_ne _ a b [] (by simp) (Ne.symm h), ih]
        simp only [rr_nil, rr_singleton, rr_cons_cons, if_neg h, List.reverse_cons]

private lemma getLast?_append_singleton (xs : List ℕ) (a : ℕ) :
    (xs ++ [a]).getLast? = some a := by simp

private lemma glue_snoc_cons (xs : List ℕ) (a b : ℕ) (bs : List ℕ) :
    glue (xs ++ [a]) (b::bs) = xs ++ (a+b)::bs := by
  induction xs with
  | nil => simp [glue]
  | cons c cs ih =>
    rcases cs with _ | ⟨d, ds⟩
    · simp [glue]
    · simp only [List.cons_append, glue_cons_cons, List.cons.injEq, true_and]
      exact ih

private def step (x : List ℕ) := x ++ (rr x).reverse

private inductive Good (x v : List ℕ) : Prop where
  | intro
      (xt vt xz vz cp cpt cpi dp dpt dpi ep ept epi vp vpt : List ℕ)
      (hxpre : x = 2::1::1::1::3::xt)
      (hvpre : v = 2::1::1::1::3::vt)
      (hxend : x = xz ++ [1])
      (hvend : v = vz ++ [1])
      (hC : rr x = cp ++ [1])
      (hcphead : cp = 1::cpt)
      (hcpend : cp = cpi ++ [1])
      (hD : rr (rr x) = dp ++ [6])
      (hdphead : dp = 1::1::dpt)
      (hdpend : dp = dpi ++ [1])
      (hEend : rr (rr (rr x)) = ep ++ [1])
      (hephead : ep = 6::1::ept)
      (hepend : ep = epi ++ [3])
      (hEv : rr (rr (rr x)) = 6 :: v.tail)
      (hrv : rr v = vp ++ [1])
      (hvphead : vp = 1::3::vpt) : Good x v

private lemma rr_cons_ne {a b : ℕ} (h : a ≠ b) (xs : List ℕ) :
    rr (a::b::xs) = 1 :: rr (b::xs) := by simp [rr_nil, rr_singleton, rr_cons_cons, h]

private lemma step_prefix (x : List ℕ) (xt : List ℕ) (h : x = 2::1::1::1::3::xt) :
    step x = 2::1::1::1::3::(xt ++ (rr x).reverse) := by simp [step, h]

private lemma reverse_bumpLast (xs : List ℕ) : (bumpLast xs).reverse = bump xs.reverse := by
  have h := reverse_bump xs.reverse
  symm
  simpa using congrArg List.reverse h

private lemma rr_ne_nil_of_last {y : List ℕ} {a : ℕ} (hy : y.getLast? = some a) : rr y ≠ [] := by
  cases y with
  | nil => simp at hy
  | cons b bs => exact rr_ne_nil b bs

private lemma bumpLast_snoc_inj (w z : List ℕ) (n : ℕ) (hw : w ≠ [])
    (h : bumpLast w = z ++ [n+1]) : w = z ++ [n] := by
  have hr := congrArg List.reverse h
  rw [reverse_bumpLast] at hr
  cases hwr : w.reverse with
  | nil =>
    have hz : w = [] := by
      have := congrArg List.reverse hwr
      simpa using this
    exact (hw hz).elim
  | cons a as =>
    rw [hwr] at hr
    simp only [bump, List.reverse_append, List.reverse_singleton] at hr
    injection hr with ha has
    have han : a = n := Nat.add_right_cancel ha
    have hwrev : w.reverse = n :: z.reverse := by simpa [hwr, han] using has
    have hx := congrArg List.reverse hwrev
    simpa using hx

private lemma rr_remove_same (y z : List ℕ) (a n : ℕ)
    (hy : y.getLast? = some a) (h : rr (y ++ [a]) = z ++ [n+1]) :
    rr y = z ++ [n] := by
  rw [rr_append_of_last_eq _ _ [] hy] at h
  simp only [rr_nil, rr_singleton, rr_cons_cons] at h
  rw [glue_singleton _ (rr_ne_nil_of_last hy)] at h
  exact bumpLast_snoc_inj _ _ _ (rr_ne_nil_of_last hy) h

private lemma rr_remove_ne (y z : List ℕ) (a b : ℕ)
    (hy : y.getLast? = some a) (hab : a ≠ b) (h : rr (y ++ [b]) = z ++ [1]) :
    rr y = z := by
  rw [rr_append_of_last_ne _ _ _ [] hy hab] at h
  simp only [rr_nil, rr_singleton, rr_cons_cons, List.append_cancel_right_eq] at h
  exact h

private lemma rr_step_formula (x cp dp : List ℕ)
    (hx : x.getLast? = some 1) (hc : rr x = cp ++ [1])
    (hd : rr (rr x) = dp ++ [6]) :
    rr (step x) = cp ++ [7] ++ dp.reverse := by
  have hc_rev : (rr x).reverse = 1 :: cp.reverse := by simp [hc]
  rw [step, hc_rev, rr_append_of_last_eq _ _ _ hx]
  have hr : rr (1 :: cp.reverse) = 6 :: dp.reverse := by
    have ht := rr_reverse (rr x)
    have hd' : rr (cp ++ [1]) = dp ++ [6] := by rw [← hc]; exact hd
    rw [hc, hd'] at ht
    simpa using ht
  rw [hc, hr, glue_snoc_cons]
  simp [List.append_assoc]

private lemma rr_append_three_ne (x : List ℕ) (a b : ℕ) (ys : List ℕ)
    (hx : x.getLast? = some a) (hab : a ≠ b) :
    rr (x ++ b :: ys) = rr x ++ rr (b::ys) :=
  rr_append_of_last_ne x b a ys hx hab

private lemma rr_second_formula (cp dp ep : List ℕ)
    (hcp : cp.getLast? = some 1) (hdp : dp.getLast? = some 1)
    (hrcp : rr cp = dp ++ [5]) (hrdp : rr dp = ep) :
    rr (cp ++ [7] ++ dp.reverse) = dp ++ [5, 1] ++ ep.reverse := by
  rw [List.append_assoc]
  change rr (cp ++ (7 :: dp.reverse)) = _
  rw [rr_append_of_last_ne cp 7 1 (dp.reverse) hcp (by decide)]
  have h7 : rr (7 :: dp.reverse) = 1 :: (rr dp).reverse := by
    have hdhead : dp.reverse.head? = some 1 := by simpa using hdp
    cases hr : dp.reverse with
    | nil => simp [hr] at hdhead
    | cons a as =>
      simp only [hr, List.head?_cons, Option.some.injEq] at hdhead
      subst a
      simp only [rr_nil, rr_singleton, rr_cons_cons, show (7:ℕ) ≠ 1 by decide, if_false]
      have := rr_reverse dp
      rw [hr] at this
      exact congrArg (List.cons 1) this
  rw [hrcp, h7, hrdp]
  simp [List.append_assoc]

private lemma rr_head_change (xs : List ℕ) : rr (6::1::xs) = rr (2::1::xs) := by
  simp [rr_nil, rr_singleton, rr_cons_cons]

private lemma rr_third_formula (dp ep v vp vt : List ℕ)
    (hdp : dp.getLast? = some 1) (hrdp : rr dp = ep)
    (hep : ep.getLast? = some 3)
    (hv : v = 2::1::1::1::3::vt)
    (hE : ep ++ [1] = 6 :: v.tail)
    (hrv : rr v = vp ++ [1]) :
    rr (dp ++ [5,1] ++ ep.reverse) = (ep ++ [1]) ++ (rr v).reverse := by
  have hdp5 : rr (dp ++ (5 :: 1 :: ep.reverse)) =
      rr dp ++ rr (5 :: 1 :: ep.reverse) :=
    rr_append_of_last_ne dp 5 1 (1::ep.reverse) hdp (by decide)
  rw [List.append_assoc]
  change rr (dp ++ (5 :: 1 :: ep.reverse)) = _
  rw [hdp5, hrdp]
  have htail : rr (5 :: 1 :: ep.reverse) = [1,1] ++ (rr ep).reverse := by
    have hehead : ep.reverse.head? = some 3 := by simpa using hep
    cases he : ep.reverse with
    | nil => simp [he] at hehead
    | cons a as =>
      simp only [he, List.head?_cons, Option.some.injEq] at hehead
      subst a
      simp only [rr_nil, rr_singleton, rr_cons_cons, show (5:ℕ) ≠ 1 by decide, if_false,
        show (1:ℕ) ≠ 3 by decide]
      have ht := rr_reverse ep
      rw [he] at ht
      simp only [ht]
      rfl
  rw [htail]
  have hrev : rr (ep ++ [1]) = rr v := by
    rw [hE, hv]
    simp [rr_nil, rr_singleton, rr_cons_cons]
  have hrep : rr ep ++ [1] = rr v := by
    have := rr_append_of_last_ne ep 1 3 [] hep (by decide)
    simp only [rr_nil, rr_singleton, rr_cons_cons] at this
    rw [this] at hrev
    exact hrev
  rw [← hrep]
  simp [List.append_assoc, List.reverse_append]

private lemma glue_end_two (xs ds : List ℕ) (d : ℕ) :
    ∃ w, glue xs (ds ++ [d,1]) = w ++ [1] := by
  induction xs with
  | nil => exact ⟨ds ++ [d], by simp [glue, List.append_assoc]⟩
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · rcases ds with _ | ⟨z, zs⟩
      · exact ⟨[a+d], by simp [glue]⟩
      · exact ⟨(a+z)::zs ++ [d], by simp [glue, List.append_assoc]⟩
    · rcases ih with ⟨w, hw⟩
      rcases ds with _ | ⟨z, zs⟩
      · simp only [List.nil_append] at hw
        exact ⟨a::w, by simp only [List.nil_append]; rw [glue_cons_cons, hw]; simp⟩
      · simp only [List.cons_append] at hw
        exact ⟨a::w, by simp only [List.cons_append]; rw [glue_cons_cons, hw]⟩

private lemma glue_prefix_end (c : ℕ) (cs ds : List ℕ) (d : ℕ) :
    ∃ w, glue (1::3::c::cs) (ds ++ [d,1]) = (1::3::w) ++ [1] := by
  rcases glue_end_two (c::cs) ds d with ⟨w, hw⟩
  rcases ds with _ | ⟨z, zs⟩
  · simp only [List.nil_append] at hw
    exact ⟨w, by simp only [List.nil_append]; rw [glue_cons_cons, glue_cons_cons, hw]; simp⟩
  · simp only [List.cons_append] at hw
    exact ⟨w, by simp only [List.cons_append]; rw [glue_cons_cons, glue_cons_cons, hw]⟩

private lemma rr_step_raw (x C D : List ℕ)
    (hx : x.getLast? = some 1) (hC : rr x = C ++ [1])
    (hD : rr (rr x) = D) :
    rr (step x) = glue (C ++ [1]) D.reverse := by
  have hrev : (rr x).reverse = 1 :: C.reverse := by simp [hC]
  rw [step, hrev, rr_append_of_last_eq _ _ _ hx, hC]
  have hr : rr (1::C.reverse) = D.reverse := by
    have ht := rr_reverse (rr x)
    have hD' : rr (C ++ [1]) = D := by rw [← hC]; exact hD
    rw [hC, hD'] at ht
    simpa using ht
  rw [hr]

private lemma rr_step_shape (v vz vp vpt : List ℕ)
    (hvlast : v = vz ++ [1]) (hvpref : vp = 1::3::vpt)
    (hrv : rr v = vp ++ [1]) :
    ∃ vp' vpt', rr (step v) = vp' ++ [1] ∧ vp' = 1::3::vpt' := by
  have hvget : v.getLast? = some 1 := by simp [hvlast]
  have hcform : rr v = (1::3::vpt) ++ [1] := by simpa [hvpref] using hrv
  let C : List ℕ := 1::3::vpt
  have hDstart : ∃ d ds, rr (rr v) = 1::d::ds := by
    rw [hcform]
    simp only [List.cons_append]
    simp only [rr_nil, rr_singleton, rr_cons_cons, show (1:ℕ) ≠ 3 by decide, if_false]
    have hn := rr_ne_nil 3 (vpt ++ [1])
    cases he : rr (3 :: (vpt ++ [1])) with
    | nil => exact (hn he).elim
    | cons d ds => exact ⟨d, ds, rfl⟩
  rcases hDstart with ⟨d, ds, hD⟩
  have hraw := rr_step_raw v C (1::d::ds) hvget (by simpa [C] using hcform) hD
  have hrev : (1::d::ds).reverse = ds.reverse ++ [d,1] := by simp
  rw [hrev] at hraw
  cases hvpt : vpt with
  | nil =>
    have hc : C ++ [1] = 1::3::1::[] := by simp [C, hvpt]
    rw [hc] at hraw
    rcases glue_prefix_end 1 [] ds.reverse d with ⟨w, hw⟩
    rw [hw] at hraw
    exact ⟨1::3::w, w, by simpa using hraw, rfl⟩
  | cons c cs =>
    have hc : C ++ [1] = 1::3::c::(cs ++ [1]) := by simp [C, hvpt]
    rw [hc] at hraw
    rcases glue_prefix_end c (cs++[1]) ds.reverse d with ⟨w, hw⟩
    rw [hw] at hraw
    exact ⟨1::3::w, w, by simpa using hraw, rfl⟩

private lemma Good_step {x v : List ℕ} (hg : Good x v) : Good (step x) (step v) := by
  rcases hg with ⟨xt, vt, xz, vz, cp, cpt, cpi, dp, dpt, dpi, ep, ept, epi,
    vp, vpt, hxpre, hvpre, hxend, hvend, hC, hcphead, hcpend, hD, hdphead,
    hdpend, hEend, hephead, hepend, hEv, hrv, hvphead⟩
  have hxlast : x.getLast? = some 1 := by simp [hxend]
  have hcplast : cp.getLast? = some 1 := by simp [hcpend]
  have hdplast : dp.getLast? = some 1 := by simp [hdpend]
  have heplast : ep.getLast? = some 3 := by simp [hepend]
  have hrcp : rr cp = dp ++ [5] := by
    apply rr_remove_same cp dp 1 5 hcplast
    rw [← hC]
    exact hD
  have hrdp : rr dp = ep := by
    apply rr_remove_ne dp ep 1 6 hdplast (by decide)
    rw [← hD]
    exact hEend
  have hC' := rr_step_formula x cp dp hxlast hC hD
  have hD' : rr (rr (step x)) = dp ++ [5,1] ++ ep.reverse := by
    rw [hC']
    exact rr_second_formula cp dp ep hcplast hdplast hrcp hrdp
  have hE' : rr (rr (rr (step x))) = (ep ++ [1]) ++ (rr v).reverse := by
    rw [hD']
    exact rr_third_formula dp ep v vp vt hdplast hrdp heplast hvpre
      (by rw [← hEend, hEv]) hrv
  rcases rr_step_shape v vz vp vpt hvend hvphead hrv with
    ⟨vp', vpt', hrv', hvphead'⟩
  let cp' := cp ++ [7] ++ ept -- temporary overwritten below
  let cpN : List ℕ := cp ++ [7] ++ dpt.reverse ++ [1]
  let cpiN : List ℕ := cp ++ [7] ++ dpt.reverse
  let dpN : List ℕ := dp ++ [5,1] ++ ept.reverse ++ [1]
  let dpiN : List ℕ := dp ++ [5,1] ++ ept.reverse
  let epN : List ℕ := ep ++ [1,1] ++ vpt.reverse ++ [3]
  let epiN : List ℕ := ep ++ [1,1] ++ vpt.reverse
  let xzN : List ℕ := x ++ 1 :: cpt.reverse
  let vzN : List ℕ := v ++ [1] ++ vpt.reverse ++ [3]
  refine ⟨xt ++ (rr x).reverse, vt ++ (rr v).reverse, xzN, vzN,
    cpN, (cpt ++ [7] ++ dpt.reverse ++ [1]), cpiN,
    dpN, (dpt ++ [5,1] ++ ept.reverse ++ [1]), dpiN,
    epN, (ept ++ [1,1] ++ vpt.reverse ++ [3]), epiN,
    vp', vpt', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [step, hxpre, List.append_assoc]
  · simpa [step, hvpre, List.append_assoc]
  · simp [xzN, step, hC, hcphead, List.reverse_append, List.append_assoc]
  · simp [vzN, step, hrv, hvphead, List.reverse_append, List.append_assoc]
  · simp [cpN, hC', hdphead, List.reverse_append, List.append_assoc]
  · simp [cpN, hcphead, List.append_assoc]
  · simp [cpN, cpiN, List.append_assoc]
  · simp [dpN, hD', hephead, List.reverse_append, List.append_assoc]
  · simp [dpN, hdphead, List.append_assoc]
  · simp [dpN, dpiN, List.append_assoc]
  · simp [epN, hE', hrv, hvphead, List.reverse_append, List.append_assoc]
  · simp [epN, hephead, List.append_assoc]
  · simp [epN, epiN, List.append_assoc]
  · rw [hE']
    have hb : ep ++ [1] = 6::1::1::1::3::vt := by
      rw [← hEend, hEv, hvpre]
      rfl
    rw [hb]
    rw [step, hvpre]
    rfl
  · exact hrv'
  · exact hvphead'

private def W : ℕ → List ℕ
  | 0 => [2]
  | n+1 => step (W n)

private lemma W3_eq : W 3 = [2,1,1,1,3,1] := by
  decide

private lemma W7_eq : W 7 = [2,1,1,1,3,1,1,1,3,1,1,1,3,1,3,1,1,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,5,1,1,1,3,1,3,1,3,1] := by
  decide

private lemma Good_initial : Good (W 7) (W 3) := by
  rw [W7_eq, W3_eq]
  have hc : rr [2,1,1,1,3,1,1,1,3,1,1,1,3,1,3,1,1,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,5,1,1,1,3,1,3,1,3,1] = [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1,1] := by decide
  have hd : rr [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1,1] = [1,1,1,1,1,1,3,1,5,1,1,1,6] := by decide
  have he : rr [1,1,1,1,1,1,3,1,5,1,1,1,6] = [6,1,1,1,3,1] := by decide
  have hp : rr [2,1,1,1,3,1] = [1,3,1,1] := by decide
  refine ⟨[1,1,1,3,1,1,1,3,1,3,1,1,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,5,1,1,1,3,1,3,1,3,1], [1], [2,1,1,1,3,1,1,1,3,1,1,1,3,1,3,1,1,1,1,1,3,1,3,1,3,1,1,1,1,1,1,1,5,1,1,1,3,1,3,1,3], [2,1,1,1,3],
    [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1], [3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1], [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1],
    [1,1,1,1,1,1,3,1,5,1,1,1], [1,1,1,1,3,1,5,1,1,1], [1,1,1,1,1,1,3,1,5,1,1],
    [6,1,1,1,3], [1,1,3], [6,1,1,1],
    [1,3,1], [1],
    rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, ?_, ?_, rfl⟩
  · exact hc
  · rw [hc]
    exact hd
  · rw [hc, hd]
    exact he
  · rw [hc, hd, he]
    rfl
  · exact hp

private lemma Good_all (k : ℕ) : Good (W (k+7)) (W (k+3)) := by
  induction k with
  | zero => simpa using Good_initial
  | succ k ih =>
    simpa [W, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Good_step ih

private lemma W_length_step (n : ℕ) :
    (W (n+1)).length = (W n).length + (rr (W n)).length := by
  simp [W, step]

private lemma W_stable_rel (k : ℕ) :
    (rr (W (k+8))).length + 1 =
      (rr (W (k+7))).length + (rr (rr (W (k+7)))).length ∧
    (rr (rr (W (k+8)))).length =
      (rr (rr (W (k+7)))).length + (W (k+3)).length := by
  have hg := Good_all k
  rcases hg with ⟨xt, vt, xz, vz, cp, cpt, cpi, dp, dpt, dpi, ep, ept, epi,
    vp, vpt, hxpre, hvpre, hxend, hvend, hC, hcphead, hcpend, hD, hdphead,
    hdpend, hEend, hephead, hepend, hEv, hrv, hvphead⟩
  have hxlast : (W (k+7)).getLast? = some 1 := by simp [hxend]
  have hcplast : cp.getLast? = some 1 := by simp [hcpend]
  have hdplast : dp.getLast? = some 1 := by simp [hdpend]
  have heplast : ep.getLast? = some 3 := by simp [hepend]
  have hrcp : rr cp = dp ++ [5] := by
    apply rr_remove_same cp dp 1 5 hcplast
    rw [← hC]
    exact hD
  have hrdp : rr dp = ep := by
    apply rr_remove_ne dp ep 1 6 hdplast (by decide)
    rw [← hD]
    exact hEend
  have hC' := rr_step_formula (W (k+7)) cp dp hxlast hC hD
  have hD' : rr (rr (step (W (k+7)))) = dp ++ [5,1] ++ ep.reverse := by
    rw [hC']
    exact rr_second_formula cp dp ep hcplast hdplast hrcp hrdp
  rw [show W (k+8) = step (W (k+7)) by rw [show k+8 = (k+7)+1 by simp [Nat.add_assoc], W]]
  have hDcp : rr (cp ++ [1]) = dp ++ [6] := by rw [← hC]; exact hD
  constructor
  · rw [hC', hC, hDcp]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]
    simp [Nat.add_assoc]
  · rw [hD', hD]
    have hlen : (ep ++ [1]).length = (W (k+3)).length := by
      rw [← hEend, hEv]
      simp [hvpre]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse] at hlen ⊢
    rw [← hlen]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private lemma T_reverse_eq_W (k : ℕ) : (A381587_T (k+3)).reverse = W k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k+1+3 = k+4 by simp [Nat.add_assoc], A381587_T]
    simp only [List.reverse_append, List.reverse_reverse]
    rw [run_lengths_eq_rr, ih]
    rfl

private lemma T_length_eq_W (k : ℕ) : (A381587_T (k+3)).length = (W k).length := by
  rw [← T_reverse_eq_W k, List.length_reverse]

private lemma sum_bump (xs : List ℕ) (h : xs ≠ []) : (bump xs).sum = xs.sum + 1 := by
  cases xs with
  | nil => contradiction
  | cons z zs =>
    simp only [bump, List.sum_cons]
    calc
      z + 1 + zs.sum = z + (1 + zs.sum) := Nat.add_assoc _ _ _
      _ = z + (zs.sum + 1) := congrArg (z + ·) (Nat.add_comm 1 zs.sum)
      _ = z + zs.sum + 1 := (Nat.add_assoc _ _ _).symm

private lemma rr_sum (xs : List ℕ) : (rr xs).sum = xs.length := by
  induction xs with
  | nil => simp [rr_nil, rr_singleton, rr_cons_cons]
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [rr_nil, rr_singleton, rr_cons_cons]
    · simp only [rr_nil, rr_singleton, rr_cons_cons]
      by_cases h : a = b
      · rw [if_pos h, sum_bump _ (rr_ne_nil b bs), ih]
        simp
      · rw [if_neg h]
        simp only [List.sum_cons, ih, List.length_cons]
        simp [Nat.add_comm]

private lemma run_lengths_sum (xs : List ℕ) : (run_lengths_nat xs).sum = xs.length := by
  rw [run_lengths_eq_rr, rr_sum]

private lemma A_sum_step (k : ℕ) :
    A381358 (k+4) = A381358 (k+3) + (W k).length := by
  rw [A381358, A381358, A381587_T]
  simp only [List.sum_append, run_lengths_sum]
  rw [List.length_reverse, T_length_eq_W]
  simp [Nat.add_comm]

private lemma W_ne_nil (k : ℕ) : W k ≠ [] := by
  induction k with
  | zero => simp [W]
  | succ k ih => simp [W, step, ih]

private lemma rr_iter_two_pos (k : ℕ) : 0 < (rr (rr (W k))).length := by
  have h1 : rr (W k) ≠ [] := by
    cases hw : W k with
    | nil => exact (W_ne_nil k hw).elim
    | cons a as => exact rr_ne_nil a as
  cases hr : rr (W k) with
  | nil => contradiction
  | cons a as => simpa [hr] using List.length_pos_iff.mpr (rr_ne_nil a as)

private inductive Ix where
  | i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7

private def X (k : ℕ) : Ix → ℕ
  | .i0 => A381358 (k+10)
  | .i1 => (W (k+7)).length
  | .i2 => (rr (W (k+7))).length
  | .i3 => (rr (rr (W (k+7)))).length - 1
  | .i4 => (W (k+6)).length
  | .i5 => (W (k+5)).length
  | .i6 => (W (k+4)).length
  | .i7 => (W (k+3)).length

private def advance (x : Ix → ℕ) : Ix → ℕ
  | .i0 => x .i0 + x .i1
  | .i1 => x .i1 + x .i2
  | .i2 => x .i2 + x .i3
  | .i3 => x .i3 + x .i7
  | .i4 => x .i1
  | .i5 => x .i4
  | .i6 => x .i5
  | .i7 => x .i6

private lemma X_step (k : ℕ) : X (k+1) = advance (X k) := by
  have hs := A_sum_step (k+7)
  have hl := W_length_step (k+7)
  have hr := (W_stable_rel k).1
  have hp := (W_stable_rel k).2
  have hpos := rr_iter_two_pos (k+7)
  funext i
  cases i with
  | i0 => simpa [X, advance, Nat.add_assoc] using hs
  | i1 => simpa [X, advance, Nat.add_assoc] using hl
  | i2 =>
      simp only [X, advance, Nat.add_assoc, Nat.reduceAdd]
      apply Nat.add_right_cancel (m := 1)
      simpa only [Nat.add_assoc, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
        using hr
  | i3 =>
      simp only [X, advance, Nat.add_assoc, Nat.reduceAdd]
      rw [hp]
      exact Nat.sub_add_comm (Nat.one_le_iff_ne_zero.mpr hpos.ne')
  | i4 => simp [X, advance, Nat.add_assoc]
  | i5 => simp [X, advance, Nat.add_assoc]
  | i6 => simp [X, advance, Nat.add_assoc]
  | i7 => simp [X, advance, Nat.add_assoc]

private lemma rr_length_le (xs : List ℕ) : (rr xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [rr_nil, rr_singleton, rr_cons_cons]
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [rr_nil, rr_singleton, rr_cons_cons]
    · simp only [rr_nil, rr_singleton, rr_cons_cons]
      split
      · cases h : rr (b::bs) with
        | nil => exact (rr_ne_nil b bs h).elim
        | cons z zs =>
          simp [bump, h] at ih ⊢
          exact ih.trans (Nat.le_add_right _ 1)
      · simp only [List.length_cons] at ih ⊢
        exact Nat.add_le_add_right ih 1

private lemma W_length_mono : Monotone (fun k => (W k).length) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [W_length_step]
  exact Nat.le_add_right _ _

private lemma rr_all_pos (xs : List ℕ) : ∀ z ∈ rr xs, 1 ≤ z := by
  induction xs with
  | nil => simp [rr_nil, rr_singleton, rr_cons_cons]
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [rr_nil, rr_singleton, rr_cons_cons]
    · simp only [rr_nil, rr_singleton, rr_cons_cons]
      split
      · cases h : rr (b::bs) with
        | nil => exact (rr_ne_nil b bs h).elim
        | cons z zs =>
          rw [h] at ih
          simp only [bump, List.mem_cons]
          intro q hq
          rcases hq with rfl | hq
          · exact Nat.le_add_left 1 z
          · exact ih q (by simp [h, hq])
      · simp only [List.mem_cons]; intro z hz
        rcases hz with rfl | hz
        · exact le_rfl
        · exact ih z hz

private lemma W_all_pos (k : ℕ) : ∀ z ∈ W k, 1 ≤ z := by
  induction k with
  | zero => simp [W]
  | succ k ih =>
    simp only [W, step, List.mem_append, List.mem_reverse]
    intro z hz
    rcases hz with hz | hz
    · exact ih z hz
    · exact rr_all_pos _ z hz

private lemma length_le_sum_of_pos (xs : List ℕ) (h : ∀ z ∈ xs, 1 ≤ z) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, List.sum_cons]
    have ha := h a (by simp)
    have ht : ∀ z ∈ as, 1 ≤ z := fun z hz => h z (by simp [hz])
    have hi := ih ht
    simpa only [Nat.add_comm a as.sum, Nat.add_comm as.length 1] using Nat.add_le_add ha hi

private lemma A_eq_W_sum (k : ℕ) : A381358 (k+3) = (W k).sum := by
  rw [A381358, ← List.sum_reverse, T_reverse_eq_W]

private lemma X_le_zero (k : ℕ) (i : Ix) : X k i ≤ X k .i0 := by
  have hsum : (W (k+7)).length ≤ A381358 (k+10) := by
    rw [show k+10 = (k+7)+3 by simp [Nat.add_assoc], A_eq_W_sum]
    exact length_le_sum_of_pos _ (W_all_pos _)
  have hr1 := rr_length_le (W (k+7))
  have hr2 := rr_length_le (rr (W (k+7)))
  have hm4 := W_length_mono (Nat.add_le_add_left (by decide : 6 ≤ 7) k)
  have hm5 := W_length_mono (Nat.add_le_add_left (by decide : 5 ≤ 7) k)
  have hm6 := W_length_mono (Nat.add_le_add_left (by decide : 4 ≤ 7) k)
  have hm7 := W_length_mono (Nat.add_le_add_left (by decide : 3 ≤ 7) k)
  cases i with
  | i0 => exact le_rfl
  | i1 => simpa only [X] using hsum
  | i2 => change (rr (W (k+7))).length ≤ A381358 (k+10); exact hr1.trans hsum
  | i3 =>
      change (rr (rr (W (k+7)))).length - 1 ≤ A381358 (k+10)
      exact (Nat.sub_le _ _).trans (hr2.trans (hr1.trans hsum))
  | i4 => change (W (k+6)).length ≤ A381358 (k+10); exact hm4.trans hsum
  | i5 => change (W (k+5)).length ≤ A381358 (k+10); exact hm5.trans hsum
  | i6 => change (W (k+4)).length ≤ A381358 (k+10); exact hm6.trans hsum
  | i7 => change (W (k+3)).length ≤ A381358 (k+10); exact hm7.trans hsum

private lemma X_zero_pos (j : Ix) : 1 ≤ X 0 j := by
  have hA : 1 ≤ A381358 10 := by
    rw [show 10 = 7+3 by decide, A_eq_W_sum, W7_eq]
    norm_num
  have hw7 : 1 ≤ (W 7).length := List.length_pos_iff.mpr (W_ne_nil _)
  have hw6 : 1 ≤ (W 6).length := List.length_pos_iff.mpr (W_ne_nil _)
  have hw5 : 1 ≤ (W 5).length := List.length_pos_iff.mpr (W_ne_nil _)
  have hw4 : 1 ≤ (W 4).length := List.length_pos_iff.mpr (W_ne_nil _)
  have hw3 : 1 ≤ (W 3).length := List.length_pos_iff.mpr (W_ne_nil _)
  have hr : 1 ≤ (rr (W 7)).length := List.length_pos_iff.mpr (by
    cases h : W 7 with
    | nil => exact (W_ne_nil _ h).elim
    | cons a as => exact rr_ne_nil a as)
  have hd : 2 ≤ (rr (rr (W 7))).length := by
    rcases Good_initial with ⟨xt, vt, xz, vz, cp, cpt, cpi, dp, dpt, dpi,
      ep, ept, epi, vp, vpt, hxpre, hvpre, hxend, hvend, hC, hcphead,
      hcpend, hD, hdphead, hdpend, hEend, hephead, hepend, hEv, hrv, hvphead⟩
    rw [hD, hdphead]
    simp
  cases j with
  | i0 => simpa only [X, Nat.zero_add] using hA
  | i1 => simpa only [X, Nat.zero_add] using hw7
  | i2 => simpa only [X, Nat.zero_add] using hr
  | i3 => simpa only [X, Nat.zero_add, Nat.reduceSub] using Nat.sub_le_sub_right hd 1
  | i4 => simpa only [X, Nat.zero_add] using hw6
  | i5 => simpa only [X, Nat.zero_add] using hw5
  | i6 => simpa only [X, Nat.zero_add] using hw4
  | i7 => simpa only [X, Nat.zero_add] using hw3

private lemma advance_le_mul (x y : Ix → ℕ) (c : ℕ)
    (h : ∀ i, x i ≤ y i * c) : ∀ i, advance x i ≤ advance y i * c := by
  intro i
  cases i with
  | i0 => simpa only [advance, Nat.add_mul] using Nat.add_le_add (h .i0) (h .i1)
  | i1 => simpa only [advance, Nat.add_mul] using Nat.add_le_add (h .i1) (h .i2)
  | i2 => simpa only [advance, Nat.add_mul] using Nat.add_le_add (h .i2) (h .i3)
  | i3 => simpa only [advance, Nat.add_mul] using Nat.add_le_add (h .i3) (h .i7)
  | i4 => exact h .i1
  | i5 => exact h .i4
  | i6 => exact h .i5
  | i7 => exact h .i6

private lemma X_shift_le (m n : ℕ) (i : Ix) : X (m+n) i ≤ X m i * X n .i0 := by
  induction m generalizing i with
  | zero =>
    simp only [zero_add]
    exact (X_le_zero n i).trans (Nat.le_mul_of_pos_left _
      (lt_of_lt_of_le Nat.zero_lt_one (X_zero_pos i)))
  | succ m ih =>
    have h := advance_le_mul (X (m+n)) (X m) (X n .i0) ih
    rw [show m+1+n = (m+n)+1 by simp [Nat.add_assoc, Nat.add_comm], X_step (m+n), X_step m]
    exact h i

private lemma X_zero_submul (m n : ℕ) : X (m+n) .i0 ≤ X m .i0 * X n .i0 :=
  X_shift_le m n .i0

private def B (n : ℕ) : ℕ := X n .i0

private lemma B_pos (n : ℕ) : 0 < B n := by
  induction n with
  | zero => exact lt_of_lt_of_le Nat.zero_lt_one (X_zero_pos .i0)
  | succ n ih =>
    rw [B, X_step, advance]
    exact Nat.add_pos_left ih _

private lemma B_submul (m n : ℕ) : B (m+n) ≤ B m * B n :=
  X_zero_submul m n

private def u (n : ℕ) : ℝ := Real.log (B n : ℝ)

private lemma u_subadditive : Subadditive u := by
  intro m n
  have hB : (B (m+n) : ℝ) ≤ (B m : ℝ) * B n := by exact_mod_cast B_submul m n
  have hp : (0:ℝ) < B (m+n) := by exact_mod_cast B_pos (m+n)
  have hp' : (0:ℝ) < (B m : ℝ) * B n := mul_pos (by exact_mod_cast B_pos m) (by exact_mod_cast B_pos n)
  calc
    u (m+n) ≤ Real.log ((B m : ℝ) * B n) :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hp') hB
    _ = u m + u n := by
      rw [Real.log_mul (by exact_mod_cast (B_pos m).ne') (by exact_mod_cast (B_pos n).ne')]
      rfl

private lemma u_bdd : BddBelow (Set.range fun n => u n / (n:ℝ)) := by
  rw [bddBelow_def]
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  apply div_nonneg
  · apply Real.log_nonneg
    have hn : 1 ≤ B n := Nat.one_le_iff_ne_zero.mpr (B_pos n).ne'
    exact_mod_cast hn
  · positivity

private lemma B_root_tendsto :
    Filter.Tendsto (fun n : ℕ => (B n : ℝ) ^ ((n:ℝ)⁻¹)) Filter.atTop
      (nhds (Real.exp u_subadditive.lim)) := by
  have h := u_subadditive.tendsto_lim u_bdd
  have he := Real.continuous_exp.continuousAt.tendsto.comp h
  apply he.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.rpow_def_of_pos (by exact_mod_cast B_pos n)]
  simp only [Function.comp_apply, u]
  rw [div_eq_mul_inv]

private lemma X_root_tendsto :
    Filter.Tendsto (fun n : ℕ => (X n .i0 : ℝ) ^ ((n:ℝ)⁻¹)) Filter.atTop
      (nhds (Real.exp u_subadditive.lim)) := by
  simpa [B] using B_root_tendsto

private lemma shifted_root_tendsto :
    Filter.Tendsto (fun k : ℕ => (A381358 (k+10) : ℝ) ^ (((k+10 : ℕ) : ℝ)⁻¹))
      Filter.atTop (nhds (Real.exp u_subadditive.lim)) := by
  have hq : Filter.Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 10)) Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop 10
  have hpow := X_root_tendsto.rpow hq (Or.inr (by norm_num : (0:ℝ)<1))
  simp only [Real.rpow_one] at hpow
  apply hpow.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hx : X k .i0 = A381358 (k+10) := by rfl
  rw [hx]
  have he : ((k : ℝ)⁻¹) * ((k : ℝ) / ((k : ℝ) + 10)) =
      (((k+10 : ℕ) : ℝ)⁻¹) := by
    push_cast
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀]
    · simp
    · exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
  rw [← he, Real.rpow_mul (by positivity : (0:ℝ) ≤ A381358 (k+10))]

private lemma A_root_tendsto :
    Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ)⁻¹)) Filter.atTop
      (nhds (Real.exp u_subadditive.lim)) := by
  apply (Filter.tendsto_add_atTop_iff_nat 10).mp
  simpa [Nat.cast_add] using shifted_root_tendsto

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/

theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by
  exact ⟨Real.exp u_subadditive.lim, A_root_tendsto⟩
