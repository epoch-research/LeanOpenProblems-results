import FormalConjectures.Util.ProblemImports
open List Nat

namespace A381

/-- run-length encoding: list of (value, count) of maximal runs. -/
def runsOf : List ℕ → List (ℕ × ℕ)
  | [] => []
  | h :: t =>
    match runsOf t with
    | [] => [(h, 1)]
    | (v, c) :: rest => if h = v then (v, c + 1) :: rest else (h, 1) :: (v, c) :: rest

/-- decode a run-list back to a flat list. -/
def decode : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (v, c) :: rest => List.replicate c v ++ decode rest

#eval runsOf [1,1,1,3,1]   -- expect [(1,3),(3,1),(1,1)]
#eval decode (runsOf [1,1,1,3,1])
#eval runsOf [2,1,1,1]

/-- `run_lengths_nat` from Spec, copied here for development. -/
def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

-- decode∘runsOf = id
theorem decode_runsOf (l : List ℕ) : decode (runsOf l) = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [runsOf]
    cases hr : runsOf t with
    | nil =>
      rw [hr] at ih
      simp only [decode] at ih
      simp only [decode, List.replicate_one]
      rw [← ih]; rfl
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      rw [hr] at ih
      simp only [decode] at ih
      by_cases hhv : h = v
      · subst hhv
        simp only [if_true, decode, List.replicate_succ, List.cons_append, ih]
      · simp only [if_neg hhv, decode, List.replicate_one, List.singleton_append, ih]

/-- prepend a single value `h` to a run-list (the head step of `runsOf`). -/
def prependRun (h : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(h, 1)]
  | (v, c) :: rest => if h = v then (v, c + 1) :: rest else (h, 1) :: (v, c) :: rest

theorem runsOf_cons (h : ℕ) (t : List ℕ) :
    runsOf (h :: t) = prependRun h (runsOf t) := by
  simp only [runsOf, prependRun]

/-- concatenate two run-lists, merging the boundary runs if equal value. -/
def mergeConcat : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], B => B
  | [(v, c)], B =>
      match B with
      | [] => [(v, c)]
      | (v', c') :: B' => if v = v' then (v, c + c') :: B' else (v, c) :: (v', c') :: B'
  | (a :: b :: A'), B => a :: mergeConcat (b :: A') B

@[simp] theorem mergeConcat_nil_left (B : List (ℕ × ℕ)) : mergeConcat [] B = B := rfl

@[simp] theorem mergeConcat_single_nil (v c : ℕ) : mergeConcat [(v, c)] [] = [(v, c)] := rfl

theorem mergeConcat_single_cons (v c v' c' : ℕ) (B' : List (ℕ × ℕ)) :
    mergeConcat [(v, c)] ((v', c') :: B') =
      if v = v' then (v, c + c') :: B' else (v, c) :: (v', c') :: B' := rfl

theorem mergeConcat_cons_cons (a b : ℕ × ℕ) (A' B : List (ℕ × ℕ)) :
    mergeConcat (a :: b :: A') B = a :: mergeConcat (b :: A') B := rfl

/-- key commutation lemma. -/
theorem mergeConcat_prependRun (h : ℕ) (R1 R2 : List (ℕ × ℕ)) :
    mergeConcat (prependRun h R1) R2 = prependRun h (mergeConcat R1 R2) := by
  cases R1 with
  | nil =>
    simp only [prependRun, mergeConcat_nil_left]
    cases R2 with
    | nil => rfl
    | cons p B' =>
      obtain ⟨v', c'⟩ := p
      rw [mergeConcat_single_cons]
      by_cases hv : h = v'
      · simp only [if_pos hv, prependRun, hv, Nat.add_comm]
      · simp only [if_neg hv, prependRun, if_neg hv]
  | cons p rest =>
    obtain ⟨v, c⟩ := p
    by_cases hv : h = v
    · simp only [prependRun, if_pos hv]
      cases rest with
      | nil =>
        cases R2 with
        | nil => simp only [mergeConcat_single_nil, prependRun, if_pos hv]
        | cons q B' =>
          obtain ⟨v', c'⟩ := q
          by_cases hv2 : v = v'
          · simp only [mergeConcat_single_cons, if_pos hv2, prependRun, if_pos hv,
              Nat.add_right_comm]
          · simp only [mergeConcat_single_cons, if_neg hv2, prependRun, if_pos hv]
      | cons r rest' =>
        simp only [mergeConcat_cons_cons, prependRun, if_pos hv]
    · simp only [prependRun, if_neg hv]
      cases rest with
      | nil =>
        cases R2 with
        | nil => simp only [mergeConcat_cons_cons, mergeConcat_single_nil, prependRun, if_neg hv]
        | cons q B' =>
          obtain ⟨v', c'⟩ := q
          by_cases hv2 : v = v'
          · simp only [mergeConcat_cons_cons, mergeConcat_single_cons, if_pos hv2, prependRun,
              if_neg hv]
          · simp only [mergeConcat_cons_cons, mergeConcat_single_cons, if_neg hv2, prependRun,
              if_neg hv]
      | cons r rest' =>
        simp only [mergeConcat_cons_cons, prependRun, if_neg hv]

/-- runs of a concatenation. -/
theorem runsOf_append (A B : List ℕ) :
    runsOf (A ++ B) = mergeConcat (runsOf A) (runsOf B) := by
  induction A with
  | nil => simp [runsOf]
  | cons h A' ih =>
    rw [List.cons_append, runsOf_cons, ih, runsOf_cons, mergeConcat_prependRun]

theorem mergeConcat_cons_ne (x : ℕ × ℕ) (rest B : List (ℕ × ℕ)) (h : rest ≠ []) :
    mergeConcat (x :: rest) B = x :: mergeConcat rest B := by
  cases rest with
  | nil => exact absurd rfl h
  | cons b A' => rw [mergeConcat_cons_cons]

/-- mergeConcat only touches the boundary: appending on the left distributes. -/
theorem mergeConcat_append_singleton_left (X : List (ℕ × ℕ)) (a : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    mergeConcat (X ++ [a]) B = X ++ mergeConcat [a] B := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    rw [List.cons_append, mergeConcat_cons_ne _ _ _ (by simp), ih, List.cons_append]

theorem mergeConcat_singleton_right (v c h : ℕ) :
    mergeConcat [(v, c)] [(h, 1)] = if v = h then [(v, c + 1)] else [(v, c), (h, 1)] := by
  rw [mergeConcat_single_cons]

/-- reversal equivariance for run-length encoding. -/
theorem runsOf_reverse (L : List ℕ) : runsOf L.reverse = (runsOf L).reverse := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    rw [List.reverse_cons, runsOf_append, ih, runsOf_cons]
    -- goal: mergeConcat (runsOf t).reverse (runsOf [h]) = (prependRun h (runsOf t)).reverse
    show mergeConcat (runsOf t).reverse [(h, 1)] = (prependRun h (runsOf t)).reverse
    cases hR : runsOf t with
    | nil => simp [prependRun]
    | cons p rest =>
      obtain ⟨v, c⟩ := p
      rw [List.reverse_cons, mergeConcat_append_singleton_left, mergeConcat_singleton_right]
      simp only [prependRun]
      by_cases hhv : h = v
      · rw [if_pos hhv]
        have : v = h := hhv.symm
        rw [if_pos this, List.reverse_cons]
      · rw [if_neg hhv]
        have : ¬ v = h := fun hc => hhv hc.symm
        rw [if_neg this, List.reverse_cons, List.reverse_cons]
        simp

/-- the first run of `runsOf (h :: t)` has value `h`. -/
theorem runsOf_cons_head (h : ℕ) (t : List ℕ) :
    ∃ c rest, runsOf (h :: t) = (h, c) :: rest := by
  rw [runsOf_cons]
  cases runsOf t with
  | nil => exact ⟨1, [], rfl⟩
  | cons p rest =>
    obtain ⟨v, c⟩ := p
    simp only [prependRun]
    by_cases hv : h = v
    · subst hv; rw [if_pos rfl]; exact ⟨c + 1, rest, rfl⟩
    · rw [if_neg hv]; exact ⟨1, (v, c) :: rest, rfl⟩

/-- grouping: `runsOf` of `h :: t` exposes the first whole run. -/
theorem runsOf_group (h : ℕ) (t : List ℕ) :
    runsOf (h :: t) =
      (h, (List.takeWhile (fun x => x = h) (h :: t)).length) ::
        runsOf (List.dropWhile (fun x => x = h) (h :: t)) := by
  induction t with
  | nil => simp [runsOf, List.takeWhile, List.dropWhile]
  | cons h' t' ih =>
    rw [runsOf_cons]
    by_cases hh : h' = h
    · subst hh
      -- both takeWhile of (h'::h'::t')
      rw [ih]
      simp only [prependRun, if_pos rfl]
      rw [List.takeWhile_cons_of_pos (by simp), List.takeWhile_cons_of_pos (by simp),
        List.dropWhile_cons_of_pos (by simp), List.dropWhile_cons_of_pos (by simp)]
      simp [List.length_cons]
    · -- h' ≠ h
      rw [List.takeWhile_cons_of_pos (by simp), List.dropWhile_cons_of_pos (by simp),
        List.takeWhile_cons_of_neg (by simp [hh]), List.dropWhile_cons_of_neg (by simp [hh])]
      simp only [List.length_nil, List.length_cons, Nat.zero_add]
      obtain ⟨c, rest, hcr⟩ := runsOf_cons_head h' t'
      rw [hcr]
      simp only [prependRun]
      rw [if_neg (Ne.symm hh)]

theorem run_lengths_nat_eq (l : List ℕ) : run_lengths_nat l = (runsOf l).map Prod.snd := by
  fun_induction run_lengths_nat l with
  | case1 => rfl
  | case2 h t rp rest ih =>
    have hr : rest = (h :: t).dropWhile (fun x => x = h) := by
      show (h :: t).drop (List.takeWhile (fun x => x = h) (h :: t)).length
          = (h :: t).dropWhile (fun x => x = h)
      nth_rewrite 2 [← List.takeWhile_append_dropWhile (p := fun x => x = h) (l := h :: t)]
      rw [List.drop_left]
    rw [hr] at ih
    rw [runsOf_group h t, List.map_cons, show rp = _ from rfl, hr, ih]

/-! ## Connection to A381587 / A381358 -/

def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

def A381358 (n : ℕ) : ℕ := (A381587_T n).sum

/-- the run-list of `U_n = reverse (T n)`. -/
def RU (n : ℕ) : List (ℕ × ℕ) := runsOf (A381587_T n).reverse

/-- weighted sum of a run-list = sum of the decoded list. -/
def sumRL (R : List (ℕ × ℕ)) : ℕ := (R.map (fun p => p.1 * p.2)).sum

theorem sumRL_eq_decode_sum (R : List (ℕ × ℕ)) : sumRL R = (decode R).sum := by
  induction R with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, c⟩ := p
    simp only [sumRL, decode, List.map_cons, List.sum_cons, List.sum_append, List.sum_replicate,
      smul_eq_mul, sumRL] at *
    rw [ih]; ring

theorem A381358_eq_sumRL (n : ℕ) : A381358 n = sumRL (RU n) := by
  rw [sumRL_eq_decode_sum, RU, decode_runsOf, A381358, List.sum_reverse]

/-- the step map on run-lists. -/
def stepRL (R : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  mergeConcat R ((runsOf (R.map Prod.snd)).reverse)

theorem RU_succ (n : ℕ) : RU (n + 4) = stepRL (RU (n + 3)) := by
  have hT : A381587_T (n + 4) = run_lengths_nat (A381587_T (n + 3)).reverse ++ A381587_T (n + 3) :=
    rfl
  rw [RU, hT, List.reverse_append, runsOf_append]
  rw [RU, stepRL]
  congr 1
  -- runsOf (reverse (run_lengths_nat (reverse (T (n+3))))) = (runsOf ((RU (n+3)).map Prod.snd)).reverse
  rw [runsOf_reverse, run_lengths_nat_eq]

/-! ## Shape invariant and the `cseq`/`PM` machinery -/

/-- `interleave1 [b1,...,bk] = [1,b1,1,b2,...,1,bk]`, the `map snd` of a canonical run-list. -/
def interleave1 : List ℕ → List ℕ
  | [] => []
  | b :: c' => 1 :: b :: interleave1 c'

/-- `PM c = runsOf (interleave1 c)`. -/
def PM (c : List ℕ) : List (ℕ × ℕ) := runsOf (interleave1 c)

theorem PM_nil : PM [] = [] := rfl

theorem PM_cons (b : ℕ) (c' : List ℕ) :
    PM (b :: c') = prependRun 1 (prependRun b (PM c')) := by
  simp only [PM, interleave1, runsOf_cons]

/-- The canonical alternating shape: `(a₀,1),(1,b₁),(a₁,1),(1,b₂),…,(a_{k-1},1),(1,b_k)`
with separators `a_i ≠ 1` and odd 1-run counts `b_i`. -/
inductive Canon : List (ℕ × ℕ) → Prop
  | nil : Canon []
  | cons (a b : ℕ) (R' : List (ℕ × ℕ)) (ha : a ≠ 1) (h : Canon R') :
      Canon ((a, 1) :: (1, b) :: R')

/-- The "co-canonical" shape of `PM c`: starts and ends with a `1`-run,
`(1,L₀),(g₁,1),(1,L₁),…,(g_q,1),(1,L_q)` with big separators `g_j ≠ 1`. -/
inductive CoCanon : List (ℕ × ℕ) → Prop
  | single (L : ℕ) : CoCanon [(1, L)]
  | cons (L g : ℕ) (R' : List (ℕ × ℕ)) (hg : g ≠ 1) (h : CoCanon R') :
      CoCanon ((1, L) :: (g, 1) :: R')

/-- `cseq R` extracts the list `[b₁,…,b_k]` of 1-run counts from a canonical run-list. -/
def cseq : List (ℕ × ℕ) → List ℕ
  | [] => []
  | _ :: (_, b) :: R' => b :: cseq R'
  | [_] => []

theorem mapsnd_eq_interleave1 {R : List (ℕ × ℕ)} (h : Canon R) :
    R.map Prod.snd = interleave1 (cseq R) := by
  induction h with
  | nil => rfl
  | cons a b R' ha hR ih =>
    simp only [cseq, List.map_cons, interleave1]
    rw [ih]

/-- Snoc decomposition of a canonical list: a nonempty canonical list ends with `(a,1),(1,b)`. -/
theorem Canon_snoc {R : List (ℕ × ℕ)} (h : Canon R) :
    R = [] ∨ ∃ R0 a b, a ≠ 1 ∧ Canon R0 ∧ R = R0 ++ [(a, 1), (1, b)] := by
  induction h with
  | nil => left; rfl
  | cons a b R' ha hR' ih =>
    rcases ih with h0 | ⟨R0, a', b', ha', hR0, hEq⟩
    · subst h0; right; exact ⟨[], a, b, ha, Canon.nil, rfl⟩
    · right
      refine ⟨(a, 1) :: (1, b) :: R0, a', b', ha', Canon.cons a b R0 ha hR0, ?_⟩
      rw [hEq]; rfl

/-- The first run of `PM c` (for `c ≠ []`) is a `1`-run. -/
theorem PM_head {c : List ℕ} (hc : c ≠ []) :
    ∃ L rest, PM c = (1, L) :: rest := by
  obtain ⟨b, c', rfl⟩ : ∃ b c', c = b :: c' := by
    cases c with
    | nil => exact absurd rfl hc
    | cons b c' => exact ⟨b, c', rfl⟩
  rw [PM_cons]
  -- prependRun 1 (prependRun b (PM c')) starts with value 1
  cases hpr : prependRun b (PM c') with
  | nil => exact ⟨1, [], rfl⟩
  | cons p rest =>
    obtain ⟨v, w⟩ := p
    simp only [prependRun]
    by_cases h1v : (1 : ℕ) = v
    · rw [if_pos h1v]; exact ⟨w + 1, rest, by rw [h1v]⟩
    · rw [if_neg h1v]; exact ⟨1, (v, w) :: rest, rfl⟩

/-- `PM c` is co-canonical whenever the last entry of `c` is `1`. -/
theorem PM_coCanon : ∀ (c : List ℕ), c.getLast? = some 1 → CoCanon (PM c) := by
  intro c
  induction c with
  | nil => intro h; simp at h
  | cons b c' ih =>
    intro h
    cases c' with
    | nil =>
      -- c = [b], getLast? = some b = some 1 ⇒ b = 1
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      -- PM [1] = (1,2)
      have : PM [1] = [(1, 2)] := by decide
      rw [this]; exact CoCanon.single 2
    | cons b2 c'' =>
      -- c' ≠ [], so getLast? (b :: c') = getLast? c'
      have hlast : (b2 :: c'').getLast? = some 1 := by
        rwa [List.getLast?_cons_cons] at h
      have hco := ih hlast
      -- PM (b :: c') = prependRun 1 (prependRun b (PM c'))
      rw [PM_cons]
      obtain ⟨L0, rest, hPM⟩ := PM_head (c := b2 :: c'') (by simp)
      rw [hPM]
      by_cases hb : b = 1
      · subst hb
        -- prependRun 1 (prependRun 1 ((1,L0)::rest)) = (1, L0+2)::rest
        simp only [prependRun, if_pos rfl]
        -- now goal CoCanon ((1, L0+1+1)::rest) ; from hco: CoCanon ((1,L0)::rest)
        rw [hPM] at hco
        cases hco with
        | single L =>
          -- rest = [], (1,L0)=(1,L) so L0 = L
          simp only [List.cons.injEq, Prod.mk.injEq] at *
          exact CoCanon.single _
        | cons L g R' hg h =>
          exact CoCanon.cons (L0 + 1 + 1) g R' hg h
      · -- b ≠ 1
        simp only [prependRun, if_neg (Ne.symm hb), if_neg hb]
        -- goal: CoCanon ((1,1)::(b,1)::(1,L0)::rest)
        rw [hPM] at hco
        exact CoCanon.cons 1 b _ hb hco

/-- Append two `(g,1),(1,L)` cells to the end of a co-canonical list. -/
theorem CoCanon_snoc {Z : List (ℕ × ℕ)} (h : CoCanon Z) (g L : ℕ) (hg : g ≠ 1) :
    CoCanon (Z ++ [(g, 1), (1, L)]) := by
  induction h with
  | single M => exact CoCanon.cons M g [(1, L)] hg (CoCanon.single L)
  | cons M g' R' hg' h ih => exact CoCanon.cons M g' _ hg' ih

theorem CoCanon_reverse {X : List (ℕ × ℕ)} (h : CoCanon X) : CoCanon X.reverse := by
  induction h with
  | single M => exact CoCanon.single M
  | cons L g R' hg h ih =>
    -- X = (1,L)::(g,1)::R'; reverse = R'.reverse ++ [(g,1),(1,L)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    exact CoCanon_snoc ih g L hg

/-- A co-canonical list starts with a `1`-run, and the remainder is canonical. -/
theorem CoCanon_split {X : List (ℕ × ℕ)} (h : CoCanon X) :
    ∃ M Y, X = (1, M) :: Y ∧ Canon Y := by
  induction h with
  | single M => exact ⟨M, [], rfl, Canon.nil⟩
  | cons L g R' hg h ih =>
    obtain ⟨M', Y', hX, hY'⟩ := ih
    exact ⟨L, (g, 1) :: (1, M') :: Y', by rw [hX], Canon.cons g M' Y' hg hY'⟩

theorem Canon_append {A B : List (ℕ × ℕ)} (hA : Canon A) (hB : Canon B) : Canon (A ++ B) := by
  induction hA with
  | nil => simpa using hB
  | cons a b R' ha hR' ih => exact Canon.cons a b _ ha ih

theorem cseq_append {A : List (ℕ × ℕ)} (hA : Canon A) (B : List (ℕ × ℕ)) :
    cseq (A ++ B) = cseq A ++ cseq B := by
  induction hA with
  | nil => rfl
  | cons a b R' ha hR' ih =>
    simp only [List.cons_append, cseq]
    rw [ih]

/-- The merge step: appending the reverse of a co-canonical list to a nonempty canonical list,
merging at the boundary, yields a canonical list. -/
theorem Canon_mergeConcat {R Q : List (ℕ × ℕ)} (hR : Canon R) (hRne : R ≠ [])
    (hQ : CoCanon Q.reverse) :
    Canon (mergeConcat R Q) ∧
      ∃ R0 a b M Y, R = R0 ++ [(a, 1), (1, b)] ∧ Q = (1, M) :: Y ∧ Canon Y ∧ Canon R0 ∧
        mergeConcat R Q = R0 ++ (a, 1) :: (1, b + M) :: Y := by
  -- decompose R via snoc
  rcases Canon_snoc hR with h0 | ⟨R0, a, b, ha, hR0, hREq⟩
  · exact absurd h0 hRne
  -- Q is co-canonical (reverse of a co-canonical), split it
  have hQco : CoCanon Q := by simpa using CoCanon_reverse hQ
  obtain ⟨M, Y, hQEq, hY⟩ := CoCanon_split hQco
  have hmerge : mergeConcat R Q = R0 ++ (a, 1) :: (1, b + M) :: Y := by
    rw [hREq, hQEq]
    -- R = (R0 ++ [(a,1)]) ++ [(1,b)]
    have hsplit : R0 ++ [(a, 1), (1, b)] = (R0 ++ [(a, 1)]) ++ [(1, b)] := by
      simp [List.append_assoc]
    rw [hsplit, mergeConcat_append_singleton_left, mergeConcat_single_cons, if_pos rfl]
    simp [List.append_assoc]
  refine ⟨?_, R0, a, b, M, Y, hREq, hQEq, hY, hR0, hmerge⟩
  rw [hmerge]
  exact Canon_append hR0 (Canon.cons a (b + M) Y ha hY)

/-- `bigCount c` = number of entries `≥ 2` in `c`. -/
def bigCount (c : List ℕ) : ℕ := c.countP (fun x => decide (2 ≤ x))

theorem bigCount_cons (b : ℕ) (c' : List ℕ) :
    bigCount (b :: c') = (if 2 ≤ b then 1 else 0) + bigCount c' := by
  simp only [bigCount, List.countP_cons]
  by_cases h : 2 ≤ b <;> simp [h, Nat.add_comm]

/-- Length of `PM c` when `c` ends in `1`. -/
theorem PM_length_of_last : ∀ (c : List ℕ), c.getLast? = some 1 → (∀ x ∈ c, 1 ≤ x) →
    (PM c).length = 2 * bigCount c + 1 := by
  intro c
  induction c with
  | nil => intro h; simp at h
  | cons b c' ih =>
    intro h hpos
    cases c' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      have : PM [1] = [(1, 2)] := by decide
      rw [this]; simp [bigCount]
    | cons b2 c'' =>
      have hlast : (b2 :: c'').getLast? = some 1 := by rwa [List.getLast?_cons_cons] at h
      have hpos' : ∀ x ∈ (b2 :: c''), 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      have hbpos : 1 ≤ b := hpos b (by simp)
      have ihc := ih hlast hpos'
      obtain ⟨L0, rest, hPM⟩ := PM_head (c := b2 :: c'') (by simp)
      rw [PM_cons, hPM]
      rw [hPM, List.length_cons] at ihc
      rw [bigCount_cons]
      by_cases hb : b = 1
      · subst hb
        have hlen : (prependRun 1 (prependRun 1 ((1, L0) :: rest))).length = rest.length + 1 := by
          simp [prependRun]
        rw [hlen]
        simp only [show ¬ (2 ≤ 1) by norm_num, if_false, Nat.zero_add]
        omega
      · have hb2 : 2 ≤ b := by omega -- from hbpos and hb
        have hlen : (prependRun 1 (prependRun b ((1, L0) :: rest))).length = rest.length + 3 := by
          simp [prependRun, hb, Ne.symm hb]
        rw [hlen, if_pos hb2]
        omega

/-- For canonical `R`, the step map is the boundary-merge of `R` with `reverse (PM (cseq R))`. -/
theorem stepRL_eq_merge {R : List (ℕ × ℕ)} (hR : Canon R) :
    stepRL R = mergeConcat R (PM (cseq R)).reverse := by
  rw [stepRL, mapsnd_eq_interleave1 hR]; rfl

/-- Main structural step: `stepRL` preserves canonicity and gives the `cseq` recurrence. -/
theorem Canon_stepRL {R : List (ℕ × ℕ)} (hR : Canon R) (hne : R ≠ [])
    (hlast : (cseq R).getLast? = some 1) :
    Canon (stepRL R) ∧
      ∃ R0 a b M Y, R = R0 ++ [(a, 1), (1, b)] ∧ (PM (cseq R)).reverse = (1, M) :: Y ∧
        Canon Y ∧ Canon R0 ∧ cseq R = cseq R0 ++ [b] ∧
        cseq (stepRL R) = cseq R0 ++ (b + M) :: cseq Y := by
  have hcne : cseq R ≠ [] := by
    intro h; rw [h] at hlast; simp at hlast
  have hco : CoCanon (PM (cseq R)) := PM_coCanon (cseq R) hlast
  have hQrev : CoCanon (((PM (cseq R)).reverse).reverse) := by
    rw [List.reverse_reverse]; exact hco
  rw [stepRL_eq_merge hR]
  obtain ⟨hCanon, R0, a, b, M, Y, hREq, hQEq, hY, hR0, hmerge⟩ :=
    Canon_mergeConcat hR hne hQrev
  refine ⟨hCanon, R0, a, b, M, Y, hREq, hQEq, hY, hR0, ?_, ?_⟩
  · rw [hREq, cseq_append hR0]; rfl
  · rw [hmerge, cseq_append hR0]; rfl

/-! ## PHASE 1 infrastructure: additivity of weighted/count sums -/

/-- decode distributes over `mergeConcat`. -/
theorem decode_mergeConcat (A B : List (ℕ × ℕ)) :
    decode (mergeConcat A B) = decode A ++ decode B := by
  induction A with
  | nil => simp [mergeConcat, decode]
  | cons a A' ih =>
    obtain ⟨v, c⟩ := a
    cases A' with
    | nil =>
      cases B with
      | nil => simp [mergeConcat, decode]
      | cons b B' =>
        obtain ⟨v', c'⟩ := b
        rw [mergeConcat_single_cons]
        by_cases hv : v = v'
        · subst hv
          simp only [if_true, decode, List.replicate_add, List.append_nil, List.append_assoc]
        · simp only [if_neg hv, decode, List.append_nil, List.append_assoc]
    | cons a2 A'' =>
      obtain ⟨v2, c2⟩ := a2
      rw [mergeConcat_cons_cons]
      simp only [decode]
      rw [ih]
      simp only [decode, List.append_assoc]

/-- count (sum of run lengths) = length of decoded list. -/
def countRL (R : List (ℕ × ℕ)) : ℕ := (R.map Prod.snd).sum

theorem countRL_eq_decode_length (R : List (ℕ × ℕ)) : countRL R = (decode R).length := by
  induction R with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, c⟩ := p
    simp only [countRL, decode, List.map_cons, List.sum_cons, List.length_append,
      List.length_replicate] at *
    rw [ih]

theorem sumRL_mergeConcat (A B : List (ℕ × ℕ)) :
    sumRL (mergeConcat A B) = sumRL A + sumRL B := by
  rw [sumRL_eq_decode_sum, sumRL_eq_decode_sum, sumRL_eq_decode_sum, decode_mergeConcat,
    List.sum_append]

theorem countRL_mergeConcat (A B : List (ℕ × ℕ)) :
    countRL (mergeConcat A B) = countRL A + countRL B := by
  rw [countRL_eq_decode_length, countRL_eq_decode_length, countRL_eq_decode_length,
    decode_mergeConcat, List.length_append]

theorem sumRL_reverse (X : List (ℕ × ℕ)) : sumRL X.reverse = sumRL X := by
  simp only [sumRL, List.map_reverse, List.sum_reverse]

theorem countRL_reverse (X : List (ℕ × ℕ)) : countRL X.reverse = countRL X := by
  simp only [countRL, List.map_reverse, List.sum_reverse]

theorem sumRL_runsOf (Y : List ℕ) : sumRL (runsOf Y) = Y.sum := by
  rw [sumRL_eq_decode_sum, decode_runsOf]

theorem countRL_runsOf (Y : List ℕ) : countRL (runsOf Y) = Y.length := by
  rw [countRL_eq_decode_length, decode_runsOf]

/-! ## PHASE 1: the count functions of `n` and their easy recurrences -/

/-- `RU` step for all `n ≥ 3`. -/
theorem RU_step (n : ℕ) (hn : 3 ≤ n) : RU (n + 1) = stepRL (RU n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact RU_succ m

/-- `Sf n = A381358 n = sum of the row`. -/
def Sf (n : ℕ) : ℕ := sumRL (RU n)
/-- `Lf n = length of `U_n` (= number of cells in the row). -/
def Lf (n : ℕ) : ℕ := countRL (RU n)
/-- `Rf n = number of runs in `U_n`. -/
def Rf (n : ℕ) : ℕ := (RU n).length

theorem Sf_eq (n : ℕ) : Sf n = A381358 n := (A381358_eq_sumRL n).symm

/-- `S(n+1) = S(n) + L(n)`. -/
theorem Sf_rec (n : ℕ) (hn : 3 ≤ n) : Sf (n + 1) = Sf n + Lf n := by
  rw [Sf, RU_step n hn, stepRL, sumRL_mergeConcat, sumRL_reverse, sumRL_runsOf]
  rw [Sf, Lf, countRL]

/-- `L(n+1) = L(n) + R(n)`. -/
theorem Lf_rec (n : ℕ) (hn : 3 ≤ n) : Lf (n + 1) = Lf n + Rf n := by
  rw [Lf, RU_step n hn, stepRL, countRL_mergeConcat, countRL_reverse, countRL_runsOf]
  rw [Lf, Rf, List.length_map]

/-! ## PHASE 1b: the `oneBlocks` structure of `PM c` -/

/-- Add 2 to the head of a list (identity on `[]`). -/
def addHead2 : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x + 2) :: xs

/-- Add `b` to the head of a list (identity on `[]`). -/
def addHead (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => (b + x) :: xs

/-- The lengths of the maximal `1`-runs of `interleave1 c` (for `c` ending in `1`). -/
def oneBlocks : List ℕ → List ℕ
  | [] => []
  | [_] => [2]
  | b :: d :: c' => if b = 1 then addHead2 (oneBlocks (d :: c')) else 1 :: oneBlocks (d :: c')

/-- The big separators of `c` (entries `≠ 1`). -/
def bigsOf (c : List ℕ) : List ℕ := c.filter (fun x => decide (x ≠ 1))

theorem bigsOf_cons (b : ℕ) (c' : List ℕ) :
    bigsOf (b :: c') = if b = 1 then bigsOf c' else b :: bigsOf c' := by
  simp only [bigsOf, List.filter_cons]
  by_cases h : b = 1 <;> simp [h]

/-- Assemble a co-canonical list from `1`-run lengths `Ls` and big separators `Gs`. -/
def buildCo : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], _ => []
  | L :: _, [] => [(1, L)]
  | L :: Ls, g :: Gs => (1, L) :: (g, 1) :: buildCo Ls Gs

theorem oneBlocks_cons2 (b d : ℕ) (c'' : List ℕ) :
    oneBlocks (b :: d :: c'') =
      if b = 1 then addHead2 (oneBlocks (d :: c'')) else 1 :: oneBlocks (d :: c'') := rfl

theorem addHead2_length (l : List ℕ) : (addHead2 l).length = l.length := by
  cases l <;> simp [addHead2]

theorem addHead_length (b : ℕ) (l : List ℕ) : (addHead b l).length = l.length := by
  cases l <;> simp [addHead]

theorem oneBlocks_pos : ∀ (c : List ℕ), c.getLast? = some 1 →
    (oneBlocks c).length = (bigsOf c).length + 1 := by
  intro c
  induction c with
  | nil => intro h; simp at h
  | cons b c' ih =>
    intro hlast
    cases c' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp [oneBlocks, bigsOf]
    | cons d c'' =>
      have hlast' : (d :: c'').getLast? = some 1 := by rwa [List.getLast?_cons_cons] at hlast
      have ihc := ih hlast'
      rw [oneBlocks_cons2, bigsOf_cons]
      by_cases hb : b = 1
      · rw [if_pos hb, if_pos hb, addHead2_length, ihc]
      · rw [if_neg hb, if_neg hb, List.length_cons, List.length_cons, ihc]

theorem prepend_twice_buildCo (x : ℕ) (Ls Gs : List ℕ) :
    prependRun 1 (prependRun 1 (buildCo (x :: Ls) Gs)) = buildCo ((x + 2) :: Ls) Gs := by
  cases Gs with
  | nil => simp [buildCo, prependRun]
  | cons g Gs' => simp [buildCo, prependRun]

theorem prepend_b_buildCo (b x : ℕ) (Ls Gs : List ℕ) (hb : b ≠ 1) :
    prependRun 1 (prependRun b (buildCo (x :: Ls) Gs)) = (1, 1) :: (b, 1) :: buildCo (x :: Ls) Gs := by
  cases Gs with
  | nil => simp [buildCo, prependRun, hb, Ne.symm hb]
  | cons g Gs' => simp [buildCo, prependRun, hb, Ne.symm hb]

/-- `oneBlocks` of a list ending in `1` is nonempty. -/
theorem oneBlocks_ne {c : List ℕ} (hlast : c.getLast? = some 1) : oneBlocks c ≠ [] := by
  have := oneBlocks_pos c hlast
  intro h; rw [h] at this; simp at this

/-- The key structure lemma: `PM c = buildCo (oneBlocks c) (bigsOf c)` for `c` ending in `1`. -/
theorem PM_eq_buildCo : ∀ (c : List ℕ), c.getLast? = some 1 →
    PM c = buildCo (oneBlocks c) (bigsOf c) := by
  intro c
  induction c with
  | nil => intro h; simp at h
  | cons b c' ih =>
    intro hlast
    cases c' with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      decide
    | cons d c'' =>
      have hlast' : (d :: c'').getLast? = some 1 := by rwa [List.getLast?_cons_cons] at hlast
      have ihc := ih hlast'
      -- write oneBlocks (d :: c'') = x :: Ls
      obtain ⟨x, Ls, hob⟩ : ∃ x Ls, oneBlocks (d :: c'') = x :: Ls := by
        cases h : oneBlocks (d :: c'') with
        | nil => exact absurd h (oneBlocks_ne hlast')
        | cons x Ls => exact ⟨x, Ls, rfl⟩
      by_cases hb : b = 1
      · have hone : oneBlocks (b :: d :: c'') = addHead2 (oneBlocks (d :: c'')) := by
          rw [oneBlocks_cons2, if_pos hb]
        have hbig : bigsOf (b :: d :: c'') = bigsOf (d :: c'') := by
          rw [bigsOf_cons, if_pos hb]
        rw [hone, hbig, hob, addHead2, PM_cons, ihc, hob]
        rw [hb]
        exact prepend_twice_buildCo x Ls (bigsOf (d :: c''))
      · have hone : oneBlocks (b :: d :: c'') = 1 :: oneBlocks (d :: c'') := by
          rw [oneBlocks_cons2, if_neg hb]
        have hbig : bigsOf (b :: d :: c'') = b :: bigsOf (d :: c'') := by
          rw [bigsOf_cons, if_neg hb]
        rw [hone, hbig, hob, PM_cons, ihc, hob]
        rw [show (1 : ℕ) :: x :: Ls = (1 : ℕ) :: (x :: Ls) from rfl]
        rw [show buildCo ((1:ℕ) :: x :: Ls) (b :: bigsOf (d :: c''))
              = (1, 1) :: (b, 1) :: buildCo (x :: Ls) (bigsOf (d :: c'')) from rfl]
        exact prepend_b_buildCo b x Ls (bigsOf (d :: c'')) hb

/-- `cseq` of `(g,1) :: buildCo Ls Gs` recovers `Ls`, when `|Ls| = |Gs| + 1`. -/
theorem cseqBuild : ∀ (Ls Gs : List ℕ) (g : ℕ), Ls.length = Gs.length + 1 →
    cseq ((g, 1) :: buildCo Ls Gs) = Ls := by
  intro Ls
  induction Ls with
  | nil => intro Gs g h; simp at h
  | cons L0 Ls' ih =>
    intro Gs g h
    cases Gs with
    | nil =>
      -- Ls' = []
      have hnil : Ls' = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using h)
      subst hnil
      simp [buildCo, cseq]
    | cons g0 Gs' =>
      have h' : Ls'.length = Gs'.length + 1 := by simpa using h
      simp only [buildCo, cseq]
      rw [ih Gs' g0 h']

/-- Append form of `buildCo`. -/
theorem buildCo_snoc : ∀ (A B : List ℕ) (L g : ℕ), A.length = B.length + 1 →
    buildCo (A ++ [L]) (B ++ [g]) = buildCo A B ++ [(g, 1), (1, L)] := by
  intro A
  induction A with
  | nil => intro B L g h; simp at h
  | cons A0 A' ih =>
    intro B L g h
    cases B with
    | nil =>
      have hnil : A' = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using h)
      subst hnil
      simp [buildCo]
    | cons b0 B' =>
      have h' : A'.length = B'.length + 1 := by simpa using h
      simp only [List.cons_append, buildCo]
      rw [ih B' L g h']

theorem buildCo_reverse : ∀ (Ls Gs : List ℕ), Ls.length = Gs.length + 1 →
    (buildCo Ls Gs).reverse = buildCo Ls.reverse Gs.reverse := by
  intro Ls
  induction Ls with
  | nil => intro Gs h; simp at h
  | cons L0 Ls' ih =>
    intro Gs h
    cases Gs with
    | nil =>
      have hnil : Ls' = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using h)
      subst hnil
      simp [buildCo]
    | cons g0 Gs' =>
      have h' : Ls'.length = Gs'.length + 1 := by simpa using h
      simp only [buildCo, List.reverse_cons]
      rw [ih Gs' h']
      -- goal: buildCo Ls'.reverse Gs'.reverse ++ [(g0,1),(1,L0)] = buildCo (Ls'.reverse ++ [L0]) (Gs'.reverse ++ [g0])
      rw [buildCo_snoc Ls'.reverse Gs'.reverse L0 g0 (by simp [h'])]
      simp [List.reverse_cons]

/-- The clean `cseq` recurrence (bridge to list combinatorics). -/
theorem cseq_stepRL {R : List (ℕ × ℕ)} (hR : Canon R) (hne : R ≠ [])
    (hlast : (cseq R).getLast? = some 1) :
    cseq (stepRL R) = (cseq R).dropLast ++ addHead 1 ((oneBlocks (cseq R)).reverse) := by
  obtain ⟨_, R0, a, b, M, Y, hREq, hQEq, hY, hR0, hcsR, hcsStep⟩ := Canon_stepRL hR hne hlast
  -- b = 1 (last of cseq R), cseq R0 = dropLast (cseq R)
  have hb1 : b = 1 := by
    have : (cseq R).getLast? = some b := by rw [hcsR]; simp
    rw [this] at hlast; exact Option.some.injEq _ _ |>.mp hlast.symm |>.symm
  have hdrop : (cseq R).dropLast = cseq R0 := by rw [hcsR]; simp
  -- Identify (PM (cseq R)).reverse = buildCo (ob.reverse) (bigs.reverse)
  set ob := oneBlocks (cseq R) with hob
  set bigs := bigsOf (cseq R) with hbigs
  have hcne : cseq R ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have hlen : ob.length = bigs.length + 1 := oneBlocks_pos (cseq R) hlast
  have hPMrev : (PM (cseq R)).reverse = buildCo ob.reverse bigs.reverse := by
    rw [PM_eq_buildCo (cseq R) hlast, buildCo_reverse ob bigs hlen]
  -- ob nonempty
  have hobne : ob ≠ [] := oneBlocks_ne hlast
  obtain ⟨M', rtail, hrob⟩ : ∃ M' rtail, ob.reverse = M' :: rtail := by
    cases hr : ob.reverse with
    | nil => exact absurd (by rw [← List.reverse_eq_nil_iff, hr]) hobne
    | cons M' rtail => exact ⟨M', rtail, rfl⟩
  -- From hQEq: (PM (cseq R)).reverse = (1, M) :: Y
  rw [hPMrev, hrob] at hQEq
  -- buildCo (M' :: rtail) bigs.reverse = (1, M') :: ...
  -- length of rtail
  have hrtaillen : rtail.length = bigs.reverse.length := by
    have : ob.reverse.length = rtail.length + 1 := by rw [hrob]; simp
    rw [List.length_reverse] at this
    rw [List.length_reverse]
    omega
  -- Determine M and cseq Y
  have hMcs : M = M' ∧ cseq Y = rtail := by
    cases hbr : bigs.reverse with
    | nil =>
      -- rtail = [] since lengths equal
      have hrt : rtail = [] := by
        rw [hbr] at hrtaillen; simpa using hrtaillen
      subst hrt
      rw [hbr] at hQEq
      simp only [buildCo] at hQEq
      rw [List.cons.injEq] at hQEq
      obtain ⟨h1, h2⟩ := hQEq
      refine ⟨(Prod.mk.injEq _ _ _ _ |>.mp h1).2.symm, ?_⟩
      rw [← h2]; rfl
    | cons g Gs =>
      rw [hbr] at hQEq
      simp only [buildCo] at hQEq
      rw [List.cons.injEq] at hQEq
      obtain ⟨h1, h2⟩ := hQEq
      have hM : M = M' := (Prod.mk.injEq _ _ _ _ |>.mp h1).2.symm
      refine ⟨hM, ?_⟩
      rw [← h2]
      -- cseq ((g,1) :: buildCo rtail Gs) = rtail
      apply cseqBuild rtail Gs g
      have : rtail.length = (g :: Gs).length := by rw [← hbr]; exact hrtaillen
      simpa using this
  obtain ⟨hM, hcsY⟩ := hMcs
  rw [hcsStep, hdrop, hcsY, hM, hb1, hrob]
  rfl

/-! ## PHASE 2: asymptotics -/

open Filter Topology

/-- The growth rate `ρ`: the real root in `(1,2)` of `x^4 (x-1)^3 = 1`. -/
theorem exists_rho : ∃ ρ : ℝ, 1 < ρ ∧ ρ < 2 ∧ ρ ^ 4 * (ρ - 1) ^ 3 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by fun_prop))
  have h1 : (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 1 = 0 := by norm_num
  have h2 : (fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 2 = 16 := by norm_num
  have hmem : (1 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 1)
      ((fun x : ℝ => x ^ 4 * (x - 1) ^ 3) 2) := by rw [h1, h2]; constructor <;> norm_num
  obtain ⟨ρ, hρmem, hρ⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  obtain ⟨hρ1, hρ2⟩ := hρmem
  refine ⟨ρ, ?_, ?_, hρ⟩
  · rcases lt_or_eq_of_le hρ1 with h | h
    · exact h
    · exfalso; rw [← h] at hρ; norm_num at hρ
  · rcases lt_or_eq_of_le hρ2 with h | h
    · exact h
    · exfalso; rw [h] at hρ; norm_num at hρ

/-- Left-eigenvector potential for the (k,q,p) system. -/
noncomputable def Psi (k q p : ℕ → ℕ) (ρ : ℝ) (n : ℕ) : ℝ :=
  (ρ - 1) ^ 2 * k (n + 4) + (ρ - 1) * q (n + 4) + p (n + 4)
  + (ρ - 1) ^ 3 * ((k (n + 3) : ℝ) + ρ * k (n + 2) + ρ ^ 2 * k (n + 1) + ρ ^ 3 * k n)

theorem Psi_step (k q p : ℕ → ℕ) (ρ : ℝ) (hρe : ρ ^ 4 * (ρ - 1) ^ 3 = 1) (N : ℕ)
    (hk : ∀ n ≥ N, k (n + 1) = k n + q n)
    (hq : ∀ n ≥ N, q (n + 1) = q n + p n)
    (hp : ∀ n ≥ N, p (n + 5) = p (n + 4) + k n) :
    ∀ n ≥ N, Psi k q p ρ (n + 1) = ρ * Psi k q p ρ n := by
  intro n hn
  have e1 := hk (n + 4) (by omega)
  have e2 := hq (n + 4) (by omega)
  have e3 := hp n hn
  simp only [Psi]
  have e1' : ((k (n + 5) : ℝ)) = (k (n + 4) : ℝ) + (q (n + 4) : ℝ) := by exact_mod_cast e1
  have e2' : ((q (n + 5) : ℝ)) = (q (n + 4) : ℝ) + (p (n + 4) : ℝ) := by exact_mod_cast e2
  have e3' : ((p (n + 5) : ℝ)) = (p (n + 4) : ℝ) + (k n : ℝ) := by exact_mod_cast e3
  show (ρ - 1) ^ 2 * (k (n + 5) : ℝ) + (ρ - 1) * q (n + 5) + p (n + 5)
      + (ρ - 1) ^ 3 * ((k (n + 4) : ℝ) + ρ * k (n + 3) + ρ ^ 2 * k (n + 2) + ρ ^ 3 * k (n + 1))
    = ρ * ((ρ - 1) ^ 2 * (k (n + 4) : ℝ) + (ρ - 1) * q (n + 4) + p (n + 4)
      + (ρ - 1) ^ 3 * ((k (n + 3) : ℝ) + ρ * k (n + 2) + ρ ^ 2 * k (n + 1) + ρ ^ 3 * k n))
  rw [e1', e2', e3']
  linear_combination (-(k n : ℝ)) * hρe

/-- If `c ρ^n ≤ a n ≤ C ρ^n` for large `n` (with `c, ρ > 0`), then `(a n)^(1/n) → ρ`. -/
theorem tendsto_rpow_of_squeeze (a : ℕ → ℕ) (ρ c C : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (N : ℕ)
    (hlb : ∀ n ≥ N, c * ρ ^ n ≤ (a n : ℝ)) (hub : ∀ n ≥ N, (a n : ℝ) ≤ C * ρ ^ n) :
    Tendsto (fun n => (a n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (nhds ρ) := by
  -- positivity of `a n` for large n
  have hapos : ∀ n ≥ N, 0 < (a n : ℝ) := by
    intro n hn
    exact lt_of_lt_of_le (by positivity) (hlb n hn)
  -- log (a n)/n squeezed
  have hg : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (nhds (Real.log ρ)) := by
    have hlow : Tendsto (fun n : ℕ => Real.log c / n + Real.log ρ) atTop (nhds (Real.log ρ)) := by
      have : Tendsto (fun n : ℕ => Real.log c / n) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      simpa using this.add tendsto_const_nhds
    have hhigh : Tendsto (fun n : ℕ => Real.log C / n + Real.log ρ) atTop (nhds (Real.log ρ)) := by
      have : Tendsto (fun n : ℕ => Real.log C / n) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      simpa using this.add tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
      have hnN : n ≥ N := le_of_max_le_left hn
      have hn1 : (1 : ℕ) ≤ n := le_of_max_le_right hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [div_add' _ _ _ (ne_of_gt hnpos), div_le_div_iff_of_pos_right hnpos]
      have h1 : Real.log c + (n : ℝ) * Real.log ρ ≤ Real.log (a n) := by
        have := hlb n hnN
        have hcast : Real.log (c * ρ ^ n) ≤ Real.log (a n) :=
          Real.log_le_log (by positivity) this
        rwa [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow] at hcast
      linarith
    · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
      have hnN : n ≥ N := le_of_max_le_left hn
      have hn1 : (1 : ℕ) ≤ n := le_of_max_le_right hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [div_add' _ _ _ (ne_of_gt hnpos), div_le_div_iff_of_pos_right hnpos]
      have h2 : Real.log (a n) ≤ Real.log C + (n : ℝ) * Real.log ρ := by
        have := hub n hnN
        have hcast : Real.log (a n) ≤ Real.log (C * ρ ^ n) :=
          Real.log_le_log (hapos n hnN) this
        rwa [Real.log_mul (by
          rcases lt_or_ge 0 C with hC | hC
          · exact ne_of_gt hC
          · exfalso; have := hub n hnN
            have : (a n : ℝ) ≤ 0 := le_trans this (by nlinarith [pow_pos hρ n])
            linarith [hapos n hnN]) (by positivity), Real.log_pow] at hcast
      linarith
  -- compose with exp
  have hcomp : Tendsto (fun n : ℕ => Real.exp (Real.log (a n) / n)) atTop (nhds ρ) := by
    have := (Real.continuous_exp.tendsto (Real.log ρ)).comp hg
    rwa [Real.exp_log hρ] at this
  apply hcomp.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.rpow_def_of_pos (hapos n hn), mul_comm]
  congr 1
  rw [div_eq_inv_mul]

/-- Upper-bound helper: if `b(n+1)=b(n)+a(n)` and `a(n) ≤ A ρ^n`, then `b(n) ≤ C ρ^n`. -/
theorem geom_upper (a b : ℕ → ℕ) (ρ A : ℝ) (hρ : 1 < ρ) (N : ℕ)
    (hrec : ∀ n ≥ N, b (n + 1) = b n + a n)
    (ha : ∀ n ≥ N, (a n : ℝ) ≤ A * ρ ^ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≥ N, (b n : ℝ) ≤ C * ρ ^ n := by
  have hρ0 : 0 < ρ := by linarith
  have hAnn : 0 ≤ A := by
    have := ha N (le_refl N)
    have h1 : (0:ℝ) ≤ (a N : ℝ) := by positivity
    have h2 : 0 < ρ ^ N := by positivity
    nlinarith [this, h1, h2]
  set C : ℝ := max (A / (ρ - 1)) ((b N : ℝ) / ρ ^ N) + 1 with hC
  have hCpos : 0 < C := by
    have : (0:ℝ) ≤ max (A / (ρ - 1)) ((b N : ℝ) / ρ ^ N) := by
      apply le_max_of_le_right; positivity
    rw [hC]; linarith
  have hCge1 : A / (ρ - 1) ≤ C := by rw [hC]; exact le_trans (le_max_left _ _) (by linarith)
  have hCgeBase : (b N : ℝ) / ρ ^ N ≤ C := by
    rw [hC]; exact le_trans (le_max_right _ _) (by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  induction n with
  | zero =>
    have hN0 : N = 0 := Nat.le_zero.mp hn
    subst hN0
    have hpow : ρ ^ 0 = 1 := by norm_num
    have := hCgeBase
    rw [hpow] at this ⊢; simpa using this
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · -- N ≤ m, use ih
      have hmN : N ≤ m := Nat.lt_succ_iff.mp hlt
      have ihm := ih hmN
      have hrecm := hrec m hmN
      have ham := ha m hmN
      have hcast : (b (m + 1) : ℝ) = (b m : ℝ) + (a m : ℝ) := by exact_mod_cast hrecm
      rw [hcast]
      have hpm : (0:ℝ) < ρ ^ m := by positivity
      calc (b m : ℝ) + (a m : ℝ) ≤ C * ρ ^ m + A * ρ ^ m := by linarith
        _ = (C + A) * ρ ^ m := by ring
        _ ≤ (C * ρ) * ρ ^ m := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hpm)
            have : A ≤ C * (ρ - 1) := by
              rw [div_le_iff₀ (by linarith)] at hCge1; linarith
            nlinarith
        _ = C * ρ ^ (m + 1) := by ring
    · -- m+1 ≤ N and N ≤ m+1, so N = m+1
      have : N = m + 1 := le_antisymm hn hge
      subst this
      have := hCgeBase
      rw [div_le_iff₀ (by positivity)] at this
      linarith

/-- A sequence satisfying `f(n+1)=ρ f(n)` for `n≥N` is `ρ^(n-N) f(N)`. -/
theorem geom_from_step (f : ℕ → ℝ) (ρ : ℝ) (N : ℕ) (h : ∀ n ≥ N, f (n + 1) = ρ * f n) :
    ∀ n ≥ N, f n = ρ ^ (n - N) * f N := by
  intro n hn
  induction n with
  | zero => simp [Nat.le_zero.mp hn]
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · have hmN : N ≤ m := Nat.lt_succ_iff.mp hlt
      rw [h m hmN, ih hmN]
      have : m + 1 - N = (m - N) + 1 := by omega
      rw [this, pow_succ]; ring
    · have : N = m + 1 := le_antisymm hn hge
      subst this; simp

/-- Monotonicity of `k` from relation A. -/
theorem k_mono {k q : ℕ → ℕ} {N : ℕ} (hA : ∀ n ≥ N, k (n + 1) = k n + q n) :
    ∀ m, N ≤ m → ∀ n, m ≤ n → k m ≤ k n := by
  intro m hm n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ j hj ih =>
    have hjN : N ≤ j := le_trans hm hj
    have := hA j hjN
    omega

/-- PHASE 2 master theorem: from the linear relations and side facts, the limit holds. -/
theorem phase2 (k q p L S R : ℕ → ℕ) (ρ : ℝ) (N : ℕ)
    (hρ1 : 1 < ρ) (hρe : ρ ^ 4 * (ρ - 1) ^ 3 = 1)
    (hA : ∀ n ≥ N, k (n + 1) = k n + q n)
    (hB : ∀ n ≥ N, q (n + 1) = q n + p n)
    (hC : ∀ n ≥ N, p (n + 5) = p (n + 4) + k n)
    (hqk : ∀ n, q n ≤ k n) (hpk : ∀ n, p n ≤ k n)
    (hR : ∀ n, R n = 2 * k n)
    (hLrec : ∀ n ≥ N, L (n + 1) = L n + R n)
    (hSrec : ∀ n ≥ N, S (n + 1) = S n + L n)
    (hbase : 0 < k N) :
    Filter.Tendsto (fun n => (S n : ℝ) ^ ((n : ℝ)⁻¹)) Filter.atTop (nhds ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hρm1 : 0 < ρ - 1 := by linarith
  -- monotonicity of k
  have hkmono := k_mono hA
  -- ψ evolves geometrically
  set ψ : ℕ → ℝ := Psi k q p ρ with hψdef
  have hψstep : ∀ n ≥ N, ψ (n + 1) = ρ * ψ n := Psi_step k q p ρ hρe N hA hB hC
  have hψgeo : ∀ n ≥ N, ψ n = ρ ^ (n - N) * ψ N := geom_from_step ψ ρ N hψstep
  -- ψ N > 0
  have hkN4 : 0 < k (N + 4) := lt_of_lt_of_le hbase (hkmono N (le_refl N) (N + 4) (by omega))
  have hψNpos : 0 < ψ N := by
    rw [hψdef, Psi]
    have h1 : (0:ℝ) < (ρ - 1) ^ 2 * (k (N + 4) : ℝ) := by
      have : (0:ℝ) < (k (N+4):ℝ) := by exact_mod_cast hkN4
      positivity
    have h2 : (0:ℝ) ≤ (ρ - 1) * (q (N+4):ℝ) := by positivity
    have h3 : (0:ℝ) ≤ (p (N+4):ℝ) := by positivity
    have h4 : (0:ℝ) ≤ (ρ-1)^3 * ((k (N+3):ℝ) + ρ * k (N+2) + ρ^2 * k (N+1) + ρ^3 * k N) := by
      positivity
    linarith
  -- key inequalities for ψ in terms of k(n+4)
  have hψlb_k : ∀ n ≥ N, (ρ - 1) ^ 2 * (k (n + 4) : ℝ) ≤ ψ n := by
    intro n hn
    rw [hψdef, Psi]
    have h2 : (0:ℝ) ≤ (ρ - 1) * (q (n+4):ℝ) := by positivity
    have h3 : (0:ℝ) ≤ (p (n+4):ℝ) := by positivity
    have h4 : (0:ℝ) ≤ (ρ-1)^3 * ((k (n+3):ℝ) + ρ * k (n+2) + ρ^2 * k (n+1) + ρ^3 * k n) := by
      positivity
    linarith
  set D : ℝ := (ρ-1)^2 + (ρ-1) + 1 + (ρ-1)^3 * (1 + ρ + ρ^2 + ρ^3) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hψub_k : ∀ n ≥ N, ψ n ≤ D * (k (n + 4) : ℝ) := by
    intro n hn
    have m0 : (k (n+3):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+3) (by omega) (n+4) (by omega); exact_mod_cast this
    have m1 : (k (n+2):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+2) (by omega) (n+4) (by omega); exact_mod_cast this
    have m2 : (k (n+1):ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono (n+1) (by omega) (n+4) (by omega); exact_mod_cast this
    have m3 : (k n:ℝ) ≤ (k (n+4):ℝ) := by
      have := hkmono n (by omega) (n+4) (by omega); exact_mod_cast this
    have hq : (q (n+4):ℝ) ≤ (k (n+4):ℝ) := by exact_mod_cast hqk (n+4)
    have hp : (p (n+4):ℝ) ≤ (k (n+4):ℝ) := by exact_mod_cast hpk (n+4)
    have a2 : ρ*(k (n+2):ℝ) ≤ ρ*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m1 (le_of_lt hρ0)
    have a3 : ρ^2*(k (n+1):ℝ) ≤ ρ^2*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m2 (by positivity)
    have a4 : ρ^3*(k n:ℝ) ≤ ρ^3*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left m3 (by positivity)
    have hsum : (k (n+3):ℝ) + ρ*(k (n+2):ℝ) + ρ^2*(k (n+1):ℝ) + ρ^3*(k n:ℝ)
        ≤ (1 + ρ + ρ^2 + ρ^3) * (k (n+4):ℝ) := by nlinarith [m0, a2, a3, a4]
    have t1 : (ρ-1)*(q (n+4):ℝ) ≤ (ρ-1)*(k (n+4):ℝ) := by
      apply mul_le_mul_of_nonneg_left hq (le_of_lt hρm1)
    have t3 : (ρ-1)^3 * ((k (n+3):ℝ) + ρ*(k (n+2):ℝ) + ρ^2*(k (n+1):ℝ) + ρ^3*(k n:ℝ))
        ≤ (ρ-1)^3 * ((1 + ρ + ρ^2 + ρ^3) * (k (n+4):ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [hψdef, Psi, hD]
    nlinarith [t1, hp, t3]
  -- bounds on k(m) for m ≥ N+4
  set Ck : ℝ := ψ N / ((ρ-1)^2 * ρ ^ (N+4)) with hCk
  set ck : ℝ := ψ N / (D * ρ ^ (N+4)) with hck
  have hCkpos : 0 < Ck := by rw [hCk]; positivity
  have hckpos : 0 < ck := by rw [hck]; positivity
  have hne1 : ((ρ-1)^2 : ℝ) ≠ 0 := by positivity
  have hne2 : ((ρ:ℝ) ^ (N+4)) ≠ 0 := by positivity
  have hneD : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  have hk_ub : ∀ m ≥ N + 4, (k m : ℝ) ≤ Ck * ρ ^ m := by
    intro m hm
    have hn : m - 4 ≥ N := by omega
    have e1 := hψlb_k (m - 4) hn
    have e2 := hψgeo (m - 4) hn
    have hm4 : m - 4 + 4 = m := by omega
    rw [hm4, e2] at e1
    have hpoweq : (ρ:ℝ)^m = ρ^(m-4-N) * ρ^(N+4) := by rw [← pow_add]; congr 1; omega
    have hkey : ((ρ-1)^2 : ℝ) * (Ck * ρ^m) = ρ^(m-4-N) * ψ N := by
      rw [hCk, hpoweq]; field_simp
    rw [← hkey] at e1
    exact le_of_mul_le_mul_left e1 (by positivity)
  have hk_lb : ∀ m ≥ N + 4, ck * ρ ^ m ≤ (k m : ℝ) := by
    intro m hm
    have hn : m - 4 ≥ N := by omega
    have e1 := hψub_k (m - 4) hn
    have e2 := hψgeo (m - 4) hn
    have hm4 : m - 4 + 4 = m := by omega
    rw [hm4, e2] at e1
    have hpoweq : (ρ:ℝ)^m = ρ^(m-4-N) * ρ^(N+4) := by rw [← pow_add]; congr 1; omega
    have hkey : (D : ℝ) * (ck * ρ^m) = ρ^(m-4-N) * ψ N := by
      rw [hck, hpoweq]; field_simp
    rw [← hkey] at e1
    exact le_of_mul_le_mul_left e1 hDpos
  -- R bounds
  have hR_ub : ∀ m ≥ N + 4, (R m : ℝ) ≤ (2*Ck) * ρ ^ m := by
    intro m hm; rw [hR]; push_cast; have := hk_ub m hm; nlinarith [this]
  have hR_lb : ∀ m ≥ N + 4, (2*ck) * ρ ^ m ≤ (R m : ℝ) := by
    intro m hm; rw [hR]; push_cast; have := hk_lb m hm; nlinarith [this]
  -- L upper via geom_upper
  obtain ⟨CL, hCLpos, hL_ub⟩ :=
    geom_upper R L ρ (2*Ck) hρ1 (N+4) (fun n hn => hLrec n (by omega)) hR_ub
  -- S upper via geom_upper
  obtain ⟨CS, hCSpos, hS_ub⟩ :=
    geom_upper L S ρ CL hρ1 (N+4) (fun n hn => hSrec n (by omega)) hL_ub
  -- division/power helper
  have rdiv : ∀ (a : ℝ) (d e : ℕ), d ≤ e → a / ρ^d * ρ^e = a * ρ^(e-d) := by
    intro a d e hde
    have hpe : (ρ:ℝ)^e = ρ^d * ρ^(e-d) := by rw [← pow_add]; congr 1; omega
    rw [hpe]; field_simp
  -- L lower: L m ≥ R (m-1) for m ≥ N+5
  have hL_lb : ∀ m ≥ N + 5, (2*ck/ρ) * ρ ^ m ≤ (L m : ℝ) := by
    intro m hm
    have hrec := hLrec (m-1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1] at hrec
    have hcast : (L m : ℝ) = (L (m-1):ℝ) + (R (m-1):ℝ) := by exact_mod_cast hrec
    have hRlb := hR_lb (m-1) (by omega)
    have hLm1 : (0:ℝ) ≤ (L (m-1):ℝ) := by positivity
    have hconv : (2*ck/ρ) * ρ^m = (2*ck) * ρ^(m-1) := by
      have := rdiv (2*ck) 1 m (by omega)
      simpa [pow_one] using this
    rw [hcast, hconv]; linarith
  -- S lower: S m ≥ L (m-1) for m ≥ N+6
  have hS_lb : ∀ m ≥ N + 6, (2*ck/ρ^2) * ρ ^ m ≤ (S m : ℝ) := by
    intro m hm
    have hrec := hSrec (m-1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1] at hrec
    have hcast : (S m : ℝ) = (S (m-1):ℝ) + (L (m-1):ℝ) := by exact_mod_cast hrec
    have hLlb := hL_lb (m-1) (by omega)
    have hSm1 : (0:ℝ) ≤ (S (m-1):ℝ) := by positivity
    have hconv : (2*ck/ρ^2) * ρ^m = (2*ck/ρ) * ρ^(m-1) := by
      have h1 := rdiv (2*ck) 2 m (by omega)
      have h2 := rdiv (2*ck) 1 (m-1) (by omega)
      have hee : m - 2 = (m-1) - 1 := by omega
      rw [h1, hee, ← h2, pow_one]
    rw [hcast, hconv]; linarith
  -- assemble squeeze
  apply tendsto_rpow_of_squeeze S ρ (2*ck/ρ^2) CS hρ0 (by positivity) (N+6)
  · intro n hn; exact hS_lb n hn
  · intro n hn; exact hS_ub n (by omega)

end A381
