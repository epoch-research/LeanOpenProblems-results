import FormalConjectures.Util.ProblemImports

open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps

namespace A300997

/-- The list-based CA step, matching the definition inside `a`. -/
def caStep (config : List ℕ) : List ℕ :=
  let base_masses := config.map (fun m => (m + 1) / 2) ++ [0]
  let received_masses := 0 :: config.map (fun m => m / 2)
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  (List.reverse next_config_long).dropWhile (fun x => x = 0) |>.reverse

/-- The function-space step (config as `ℕ → ℕ`, i.e. `i ↦ mass at cell i`). -/
def stepF (f : ℕ → ℕ) : ℕ → ℕ :=
  fun i => (f i + 1) / 2 + (if i = 0 then 0 else f (i-1) / 2)

/-- `foldl` with a constant-in-index function is iteration. -/
lemma foldl_range_iterate {α : Type*} (f : α → α) (init : α) (k : ℕ) :
    (List.range k).foldl (fun acc _ => f acc) init = f^[k] init := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ']
    simp

/-- The untrimmed next configuration. -/
def caStepLong (config : List ℕ) : List ℕ :=
  List.zipWith Nat.add (config.map (fun m => (m + 1) / 2) ++ [0]) (0 :: config.map (fun m => m / 2))

/-- getD of the "base masses" list. -/
lemma getD_base (L : List ℕ) (i : ℕ) :
    (L.map (fun m => (m + 1) / 2) ++ [0]).getD i 0 = (L.getD i 0 + 1) / 2 := by
  rcases lt_or_ge i L.length with h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_map]
    rw [List.getElem?_eq_getElem h]
    simp
  · -- i ≥ L.length, so base value beyond is 0, and L.getD is 0
    have hL : L.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hL]
    rcases Nat.lt_or_ge i (L.length + 1) with h2 | h2
    · -- i = L.length
      have : i = L.length := by omega
      subst this
      rw [List.getD_eq_getElem?_getD]
      simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h2)]
      rfl

/-- getD of the "received masses" list. -/
lemma getD_recv (L : List ℕ) (i : ℕ) :
    (0 :: L.map (fun m => m / 2)).getD i 0 = (if i = 0 then 0 else L.getD (i-1) 0 / 2) := by
  cases i with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases lt_or_ge j L.length with h | h
    · rw [List.getElem?_eq_getElem h]; simp
    · rw [List.getElem?_eq_none (by omega)]; rfl

/-- getD of a zipWith of equal-length lists. -/
lemma getD_zipWith_add (A B : List ℕ) (h : A.length = B.length) (i : ℕ) :
    (List.zipWith Nat.add A B).getD i 0 = A.getD i 0 + B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith]
  rcases lt_or_ge i A.length with hi | hi
  · rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : i < B.length)]
    simp
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega : B.length ≤ i)]
    simp

/-- Trimming trailing zeros does not change `getD`. -/
lemma getD_dropTrail (X : List ℕ) (i : ℕ) :
    ((X.reverse.dropWhile (fun x => x = 0)).reverse).getD i 0 = X.getD i 0 := by
  set trimmed := (X.reverse.dropWhile (fun x => x = 0)).reverse with htrim
  set t := (X.reverse.takeWhile (fun x => x = 0)).reverse with htdef
  have hsplit : trimmed ++ t = X := by
    rw [htrim, htdef, ← List.reverse_append, List.takeWhile_append_dropWhile]
    exact List.reverse_reverse X
  have hzero : ∀ x ∈ t, x = 0 := by
    intro x hx
    rw [htdef, List.mem_reverse] at hx
    have := List.mem_takeWhile_imp hx
    simpa using this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_or_ge i trimmed.length with hi | hi
  · rw [← hsplit, List.getElem?_append_left hi]
  · rw [List.getElem?_eq_none hi]
    rw [← hsplit]
    rcases lt_or_ge i (trimmed ++ t).length with hi2 | hi2
    · rw [List.getElem?_append_right hi]
      rw [List.getElem?_eq_getElem (by rw [List.length_append] at hi2; omega)]
      simp only [Option.getD_some, Option.getD_none]
      exact (hzero _ (List.getElem_mem _)).symm
    · rw [List.getElem?_eq_none hi2]

/-- The key bridge: the list CA step corresponds pointwise (via `getD`) to `stepF`. -/
lemma caStep_getD (L : List ℕ) (i : ℕ) :
    (caStep L).getD i 0 = stepF (fun j => L.getD j 0) i := by
  have h1 : (caStep L).getD i 0 = (caStepLong L).getD i 0 := by
    rw [caStep, caStepLong]
    exact getD_dropTrail _ i
  rw [h1, caStepLong]
  rw [getD_zipWith_add _ _ (by simp) i]
  rw [getD_base, getD_recv]
  rfl

/-- A list is "reduced" if it has no trailing zero. -/
def Reduced (L : List ℕ) : Prop := L.getLast? ≠ some 0

lemma reduced_replicate_one (n : ℕ) : Reduced (List.replicate n 1) := by
  cases n with
  | zero => simp [Reduced]
  | succ m =>
    rw [Reduced, List.getLast?_replicate]
    simp

/-- `caStep` always produces a reduced list. -/
lemma reduced_caStep (L : List ℕ) : Reduced (caStep L) := by
  rw [Reduced, caStep, List.getLast?_reverse]
  set Y := (caStepLong L).reverse with hY
  show (Y.dropWhile (fun x => x = 0)).head? ≠ some 0
  intro hcon
  have hne : Y.dropWhile (fun x => x = 0) ≠ [] := by
    intro h; rw [h] at hcon; simp at hcon
  have hhead : (Y.dropWhile (fun x => x = 0)).head hne = 0 := by
    have h := List.head?_eq_some_head hne
    rw [h] at hcon
    exact (Option.some_inj.mp hcon)
  have hnot := List.head_dropWhile_not (fun x => x = 0) hne
  rw [hhead] at hnot
  simp at hnot

/-- Two reduced lists with the same `getD` are equal. -/
lemma eq_of_getD_reduced {L1 L2 : List ℕ} (h1 : Reduced L1) (h2 : Reduced L2)
    (hg : ∀ i, L1.getD i 0 = L2.getD i 0) : L1 = L2 := by
  have key : ∀ (A B : List ℕ), Reduced B → (∀ i, A.getD i 0 = B.getD i 0) → A.length ≥ B.length := by
    intro A B hB hAB
    by_contra hlt
    push_neg at hlt
    have hBne : B ≠ [] := by
      intro h; rw [h] at hlt; simp at hlt
    have hlast : B.getLast hBne ≠ 0 := by
      intro h
      apply hB
      rw [List.getLast?_eq_some_getLast hBne, h]
    have hi : B.getD (B.length - 1) 0 = B.getLast hBne := by
      rw [List.getD_eq_getElem?_getD, List.getLast_eq_getElem,
        List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil hBne; omega)]
      rfl
    have hAi : A.getD (B.length - 1) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have := hAB (B.length - 1)
    rw [hAi, hi] at this
    exact hlast this.symm
  have hle1 := key L1 L2 h2 hg
  have hle2 := key L2 L1 h1 (fun i => (hg i).symm)
  have hlen : L1.length = L2.length := le_antisymm hle2 hle1
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have := hg i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at this
  simpa using this

/-- Iterated correspondence between the list CA and `stepF`. -/
lemma caStep_iterate_getD (L : List ℕ) (k i : ℕ) :
    ((caStep^[k] L)).getD i 0 = (stepF^[k] (fun j => L.getD j 0)) i := by
  induction k generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [caStep_getD]
    congr 1
    funext j
    exact ih j

/-- Initial function-space config. -/
def initF (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

/-- Target function-space config. -/
def targetF (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

/-- The function-space process. -/
def P (n t : ℕ) : ℕ → ℕ := stepF^[t] (initF n)

lemma getD_singleton (n j : ℕ) : ([n] : List ℕ).getD j 0 = initF n j := by
  cases j with
  | zero => simp [initF]
  | succ m => simp [initF]

lemma getD_replicate_one (n i : ℕ) : (List.replicate n 1).getD i 0 = targetF n i := by
  rw [targetF, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_eq_getElem (by simpa using h)]; simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; simp [h]

/-- The process in function space, matching the list iterate. -/
lemma iterate_caStep_getD (n k i : ℕ) :
    ((caStep^[k] [n])).getD i 0 = P n k i := by
  rw [caStep_iterate_getD, P]
  have : (fun j => ([n] : List ℕ).getD j 0) = initF n := funext (getD_singleton n)
  rw [this]

/-- For `n ≥ 1`, every iterate of `caStep` from `[n]` is reduced. -/
lemma reduced_iterate (n k : ℕ) (hn : 1 ≤ n) : Reduced (caStep^[k] [n]) := by
  cases k with
  | zero =>
    simp only [Function.iterate_zero, id]
    rw [Reduced, List.getLast?_singleton]
    simp only [ne_eq, Option.some.injEq]
    omega
  | succ m =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact reduced_caStep _

/-- Reaching the target (list level) iff reaching it (function level). -/
lemma reach_iff (n k : ℕ) (hn : 1 ≤ n) :
    caStep^[k] [n] = List.replicate n 1 ↔ P n k = targetF n := by
  constructor
  · intro h
    funext i
    rw [← iterate_caStep_getD, h, getD_replicate_one]
  · intro h
    apply eq_of_getD_reduced (reduced_iterate n k hn) (reduced_replicate_one n)
    intro i
    rw [iterate_caStep_getD, getD_replicate_one]
    exact congrFun h i

/-- Local copy of the sequence `a`, matching `Submission.a`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k | (List.range k).foldl (fun acc _ => caStep acc) [n] = List.replicate n 1}

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = sInf {k | P n k = targetF n} := by
  rw [a, if_neg (by omega)]
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  rw [foldl_range_iterate]
  exact reach_iff n k hn

/-- Unit mass at position `g`. -/
def eOne (g : ℕ) : ℕ → ℕ := fun j => if j = g then 1 else 0

/-- The defect position. -/
def gdef (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | (t+1) => gdef n t + (if (P n t (gdef n t)) % 2 = 1 then 1 else 0)

/-- The single-step coupling: adding a unit at `g` and stepping equals stepping and
    adding a unit at `g' = g + [f g odd]`. -/
lemma stepF_coupling (f : ℕ → ℕ) (g : ℕ) :
    stepF (fun j => f j + eOne g j) =
      fun i => stepF f i + eOne (g + (if (f g) % 2 = 1 then 1 else 0)) i := by
  funext i
  rcases Nat.even_or_odd (f g) with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [if_neg (show ¬ f g % 2 = 1 by omega)]
    rcases i with _ | j
    · by_cases hg : g = 0
      · subst hg; simp only [stepF, eOne]
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
      · simp only [stepF, eOne]
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
    · simp only [stepF, eOne, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      by_cases hgj1 : j + 1 = g
      · subst hgj1
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
      · by_cases hgj : j = g
        · subst hgj
          split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
        · split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
  · rw [if_pos (show f g % 2 = 1 by omega)]
    rcases i with _ | j
    · by_cases hg : g = 0
      · subst hg; simp only [stepF, eOne]
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
      · simp only [stepF, eOne]
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
    · simp only [stepF, eOne, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      by_cases hgj1 : j + 1 = g
      · subst hgj1
        split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
      · by_cases hgj : j = g
        · subst hgj
          split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega
        · split_ifs <;> (try contradiction) <;> (try simp only [Nat.add_zero]) <;> omega

/-- The coupling: the `(n+1)`-process equals the `n`-process plus a unit at the defect. -/
lemma P_coupling (n : ℕ) : ∀ t, P (n+1) t = fun j => P n t j + eOne (gdef n t) j := by
  intro t
  induction t with
  | zero =>
    simp only [P, Function.iterate_zero, id, gdef]
    funext j
    simp only [initF, eOne]
    split_ifs <;> omega
  | succ s ih =>
    have hP1 : P (n+1) (s+1) = stepF (P (n+1) s) := by
      rw [P, Function.iterate_succ', Function.comp_apply, ← P]
    have hPn : P n (s+1) = stepF (P n s) := by
      rw [P, Function.iterate_succ', Function.comp_apply, ← P]
    rw [hP1, ih, stepF_coupling (P n s) (gdef n s)]
    funext i
    rw [hPn]
    rfl

/-- `stepF` at a successor index. -/
lemma stepF_succ (f : ℕ → ℕ) (i : ℕ) :
    stepF f (i + 1) = (f (i + 1) + 1) / 2 + f i / 2 := by
  simp only [stepF, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]

/-- `stepF` at index 0. -/
lemma stepF_zero (f : ℕ → ℕ) : stepF f 0 = (f 0 + 1) / 2 := by
  simp only [stepF, if_pos, Nat.add_zero]

/-- Support propagation: if `f` is supported on `[0, fr]`, then `stepF f` is supported on `[0, fr+1]`. -/
lemma stepF_support (f : ℕ → ℕ) (fr : ℕ) (hf : ∀ i, fr < i → f i = 0) :
    ∀ i, fr + 1 < i → stepF f i = 0 := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [stepF_succ]
  rw [hf (j+1) (by omega), hf j (by omega)]

/-- The cell just past the front. -/
lemma stepF_front_next (f : ℕ → ℕ) (fr : ℕ) (hf : ∀ i, fr < i → f i = 0) :
    stepF f (fr + 1) = f fr / 2 := by
  rw [stepF_succ, hf (fr+1) (by omega)]
  simp

/-- Contiguity is preserved (cells `[0,fr]` stay `≥ 1`). -/
lemma stepF_contig (f : ℕ → ℕ) (fr : ℕ) (hf : ∀ i, i ≤ fr → 1 ≤ f i) :
    ∀ i, i ≤ fr → 1 ≤ stepF f i := by
  intro i hi
  rcases i with _ | j
  · rw [stepF_zero]; have := hf 0 (by omega); omega
  · rw [stepF_succ]; have := hf (j+1) hi; omega

/-- Cells strictly below the leftmost `≥ 2` cell stay `= 1` under stepping. -/
lemma stepF_ones (f : ℕ → ℕ) (bl : ℕ) (hbl : ∀ i, i < bl → f i = 1) :
    ∀ i, i < bl → stepF f i = 1 := by
  intro i hi
  rcases i with _ | j
  · rw [stepF_zero, hbl 0 (by omega)]
  · rw [stepF_succ, hbl (j+1) (by omega), hbl j (by omega)]

/-- A sum of cells each `≥ 1` is at least the number of cells. -/
lemma sum_ge_card (F : ℕ → ℕ) (m : ℕ) (h : ∀ i, i < m → 1 ≤ F i) :
    m ≤ ∑ i ∈ Finset.range m, F i := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have := ih (fun i hi => h i (by omega))
    have := h k (by omega)
    omega

/-- Mass-conservation identity for `stepF` (additive form to avoid nat subtraction). -/
lemma stepF_sum (f : ℕ → ℕ) (K : ℕ) :
    (∑ i ∈ Finset.range (K + 1), stepF f i) + f K / 2 = ∑ i ∈ Finset.range (K + 1), f i := by
  induction K with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_one, stepF_zero]; omega
  | succ k ih =>
    rw [Finset.sum_range_succ (fun i => stepF f i) (k+1),
        Finset.sum_range_succ f (k+1), stepF_succ]
    omega

/-- The structural invariant maintained by the process while non-terminal.
`fr` is the front (rightmost nonzero cell), `bl` the leftmost cell `≥ 2`. -/
def Inv (n g : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ fr bl : ℕ,
    fr < n ∧ bl ≤ fr ∧
    (∀ i, i ≤ fr → 1 ≤ f i) ∧
    (∀ i, fr < i → f i = 0) ∧
    2 ≤ f bl ∧
    (∀ i, i < bl → f i = 1) ∧
    (∑ i ∈ Finset.range (n + 1), f i = n) ∧
    bl ≤ g + 1 ∧ g ≤ fr + 1

/-- The defect update expression. -/
def gstep (f : ℕ → ℕ) (g : ℕ) : ℕ := g + (if f g % 2 = 1 then 1 else 0)

/-- Preservation of the invariant under one step, provided the next config is non-terminal. -/
lemma Inv_step (n g : ℕ) (f : ℕ → ℕ) (h : Inv n g f)
    (hnt : ∃ b, 2 ≤ stepF f b) :
    Inv n (gstep f g) (stepF f) := by
  obtain ⟨fr, bl, hfrn, hblfr, hcontig, hsupp, hbl2, hones, hmass, hglow, hghigh⟩ := h
  have hffr : 1 ≤ f fr := hcontig fr le_rfl
  -- mass conservation for stepF f
  have hfn : f n = 0 := hsupp n hfrn
  have hmassF : ∑ i ∈ Finset.range (n + 1), stepF f i = n := by
    have h1 := stepF_sum f n
    rw [hfn, hmass] at h1
    simpa using h1
  -- basic stepF facts
  have hFsupp_gen : ∀ i, fr + 1 < i → stepF f i = 0 := stepF_support f fr hsupp
  have hFfrn : stepF f (fr + 1) = f fr / 2 := stepF_front_next f fr hsupp
  have hFcontig : ∀ i, i ≤ fr → 1 ≤ stepF f i := stepF_contig f fr hcontig
  have hFones : ∀ i, i < bl → stepF f i = 1 := stepF_ones f bl hones
  -- Determine the new front fr'
  obtain ⟨fr', hfr'eq, hfr'supp, hfr'contig, hgh'⟩ :
      ∃ fr', (fr = fr' ∨ fr + 1 = fr') ∧
        (∀ i, fr' < i → stepF f i = 0) ∧
        (∀ i, i ≤ fr' → 1 ≤ stepF f i) ∧
        gstep f g ≤ fr' + 1 := by
    by_cases hfr2 : 2 ≤ f fr
    · refine ⟨fr + 1, Or.inr rfl, hFsupp_gen, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (fr + 1) with h | h
        · exact hFcontig i (by omega)
        · have : i = fr + 1 := by omega
          rw [this, hFfrn]; omega
      · unfold gstep; split_ifs <;> omega
    · -- f fr = 1
      have hfr1 : f fr = 1 := by omega
      refine ⟨fr, Or.inl rfl, ?_, hFcontig, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (fr + 2) with h | h
        · have : i = fr + 1 := by omega
          rw [this, hFfrn, hfr1]
        · exact hFsupp_gen i (by omega)
      · by_cases hgfr : g ≤ fr
        · unfold gstep; split_ifs <;> omega
        · have hfg0 : f g = 0 := hsupp g (by omega)
          have hpar : ¬ (f g % 2 = 1) := by omega
          unfold gstep; rw [if_neg hpar]; omega
  -- fr' ≤ n
  have hfr'le : fr' ≤ n := by rcases hfr'eq with h | h <;> omega
  -- fr' < n via mass
  have hfr'n : fr' < n := by
    have hsub : Finset.range (fr' + 1) ⊆ Finset.range (n + 1) := by
      intro x hx; simp only [Finset.mem_range] at *; omega
    have hle : (∑ i ∈ Finset.range (fr' + 1), stepF f i) ≤ ∑ i ∈ Finset.range (n + 1), stepF f i :=
      Finset.sum_le_sum_of_subset hsub
    have hge : fr' + 1 ≤ ∑ i ∈ Finset.range (fr' + 1), stepF f i :=
      sum_ge_card (stepF f) (fr' + 1) (fun i hi => hfr'contig i (by omega))
    omega
  -- Determine the new leftmost-≥2 bl'
  obtain ⟨bl', hbl'le, hbl'2, hbl'ones, hbl'glow⟩ :
      ∃ bl', bl' ≤ fr' ∧ 2 ≤ stepF f bl' ∧
        (∀ i, i < bl' → stepF f i = 1) ∧
        bl' ≤ gstep f g + 1 := by
    by_cases hbl3 : 3 ≤ f bl
    · refine ⟨bl, ?_, ?_, hFones, ?_⟩
      · rcases hfr'eq with h | h <;> omega
      · simp only [stepF]; split_ifs <;> omega
      · unfold gstep; split_ifs <;> omega
    · -- f bl = 2
      have hfbl2 : f bl = 2 := by omega
      -- value of stepF at bl is 1
      have hstepbl : stepF f bl = 1 := by
        rcases Nat.eq_zero_or_pos bl with hb0 | hbpos
        · subst hb0; rw [stepF_zero, hfbl2]
        · obtain ⟨c, rfl⟩ : ∃ c, bl = c + 1 := ⟨bl - 1, by omega⟩
          rw [stepF_succ, hfbl2, hones c (by omega)]
      -- non-terminality forces bl < fr
      have hblfr' : bl < fr := by
        rcases Nat.lt_or_ge bl fr with h | h
        · exact h
        · exfalso
          have hbleqfr : bl = fr := by omega
          have hffr2 : f fr = 2 := by rw [← hbleqfr]; exact hfbl2
          obtain ⟨b, hb⟩ := hnt
          have hble : stepF f b ≤ 1 := by
            rcases Nat.lt_trichotomy b fr with hlt | heq | hgt
            · rw [hFones b (by omega)]
            · rw [heq, ← hbleqfr, hstepbl]
            · rcases Nat.lt_or_ge b (fr + 2) with h2 | h2
              · have : b = fr + 1 := by omega
                rw [this, hFfrn, hffr2]
              · rw [hFsupp_gen b (by omega)]; omega
          omega
      refine ⟨bl + 1, ?_, ?_, ?_, ?_⟩
      · rcases hfr'eq with h | h <;> omega
      · rw [stepF_succ, hfbl2]
        have : 1 ≤ f (bl + 1) := hcontig (bl + 1) (by omega)
        omega
      · intro i hi
        rcases Nat.lt_or_ge i bl with h | h
        · exact hFones i h
        · have hib : i = bl := by omega
          rw [hib, hstepbl]
      · by_cases hgb : bl ≤ g
        · unfold gstep; split_ifs <;> omega
        · have hg : g = bl - 1 := by omega
          have hbl1 : 1 ≤ bl := by omega
          have hfg : f g = 1 := hones g (by omega)
          unfold gstep; rw [if_pos (by rw [hfg])]; omega
  exact ⟨fr', bl', hfr'n, hbl'le, hfr'contig, hfr'supp, hbl'2, hbl'ones, hmassF, hbl'glow, hgh'⟩

/-- Weaker structural invariant (contiguity + mass) that holds at **all** times. -/
def Struct (n : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ fr, fr < n ∧
    (∀ i, i ≤ fr → 1 ≤ f i) ∧
    (∀ i, fr < i → f i = 0) ∧
    (∑ i ∈ Finset.range (n + 1), f i = n)

/-- `Struct` is preserved by `stepF` (unconditionally). -/
lemma Struct_step (n : ℕ) (f : ℕ → ℕ) (h : Struct n f) : Struct n (stepF f) := by
  obtain ⟨fr, hfrn, hcontig, hsupp, hmass⟩ := h
  have hffr : 1 ≤ f fr := hcontig fr le_rfl
  have hfn : f n = 0 := hsupp n hfrn
  have hmassF : ∑ i ∈ Finset.range (n + 1), stepF f i = n := by
    have h1 := stepF_sum f n; rw [hfn, hmass] at h1; simpa using h1
  have hFsupp_gen : ∀ i, fr + 1 < i → stepF f i = 0 := stepF_support f fr hsupp
  have hFfrn : stepF f (fr + 1) = f fr / 2 := stepF_front_next f fr hsupp
  have hFcontig : ∀ i, i ≤ fr → 1 ≤ stepF f i := stepF_contig f fr hcontig
  obtain ⟨fr', hfr'eq, hfr'supp, hfr'contig⟩ :
      ∃ fr', (fr = fr' ∨ fr + 1 = fr') ∧
        (∀ i, fr' < i → stepF f i = 0) ∧
        (∀ i, i ≤ fr' → 1 ≤ stepF f i) := by
    by_cases hfr2 : 2 ≤ f fr
    · refine ⟨fr + 1, Or.inr rfl, hFsupp_gen, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i (fr + 1) with h | h
      · exact hFcontig i (by omega)
      · have : i = fr + 1 := by omega
        rw [this, hFfrn]; omega
    · have hfr1 : f fr = 1 := by omega
      refine ⟨fr, Or.inl rfl, ?_, hFcontig⟩
      intro i hi
      rcases Nat.lt_or_ge i (fr + 2) with h | h
      · have : i = fr + 1 := by omega
        rw [this, hFfrn, hfr1]
      · exact hFsupp_gen i (by omega)
  have hfr'le : fr' ≤ n := by rcases hfr'eq with h | h <;> omega
  have hfr'n : fr' < n := by
    have hsub : Finset.range (fr' + 1) ⊆ Finset.range (n + 1) := by
      intro x hx; simp only [Finset.mem_range] at *; omega
    have hle : (∑ i ∈ Finset.range (fr' + 1), stepF f i) ≤ ∑ i ∈ Finset.range (n + 1), stepF f i :=
      Finset.sum_le_sum_of_subset hsub
    have hge : fr' + 1 ≤ ∑ i ∈ Finset.range (fr' + 1), stepF f i :=
      sum_ge_card (stepF f) (fr' + 1) (fun i hi => hfr'contig i (by omega))
    omega
  exact ⟨fr', hfr'n, hfr'contig, hfr'supp, hmassF⟩

/-- `Struct` holds initially (for `n ≥ 1`). -/
lemma Struct_init (n : ℕ) (hn : 1 ≤ n) : Struct n (initF n) := by
  refine ⟨0, by omega, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i; simp only [initF, if_pos]; omega
  · intro i hi; simp only [initF]; rw [if_neg (by omega)]
  · have : ∀ i, initF n i = if i = 0 then n else 0 := fun i => rfl
    simp only [this]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => n)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- `Struct` holds along the whole process. -/
lemma Struct_P (n : ℕ) (hn : 1 ≤ n) (t : ℕ) : Struct n (P n t) := by
  induction t with
  | zero => simpa [P] using Struct_init n hn
  | succ s ih =>
    have : P n (s + 1) = stepF (P n s) := by
      rw [P, Function.iterate_succ', Function.comp_apply, ← P]
    rw [this]
    exact Struct_step n (P n s) ih

/-- If a `Struct` config has all cells `≤ 1`, it is the target. -/
lemma Struct_le_one_eq_target (n : ℕ) (f : ℕ → ℕ) (h : Struct n f)
    (hle : ∀ b, f b ≤ 1) : f = targetF n := by
  obtain ⟨fr, hfrn, hcontig, hsupp, hmass⟩ := h
  have hone : ∀ i, i ≤ fr → f i = 1 := fun i hi => le_antisymm (hle i) (hcontig i hi)
  -- split the mass sum at fr+1
  have hsplit : (∑ i ∈ Finset.range (fr + 1), f i) + (∑ i ∈ Finset.Ico (fr + 1) (n + 1), f i)
      = ∑ i ∈ Finset.range (n + 1), f i :=
    Finset.sum_range_add_sum_Ico f (by omega)
  have hlow : (∑ i ∈ Finset.range (fr + 1), f i) = fr + 1 := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi; rw [Finset.mem_range] at hi; exact hone i (by omega)
  have hhigh : (∑ i ∈ Finset.Ico (fr + 1) (n + 1), f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi; rw [Finset.mem_Ico] at hi; exact hsupp i (by omega)
  have hfreq : fr + 1 = n := by rw [hlow, hhigh, hmass] at hsplit; omega
  funext i
  simp only [targetF]
  by_cases hi : i ≤ fr
  · rw [hone i hi, if_pos (by omega)]
  · rw [hsupp i (by omega), if_neg (by omega)]

/-- A `Struct` config that is not the target has a cell `≥ 2`. -/
lemma Struct_ne_target_cell2 (n : ℕ) (f : ℕ → ℕ) (h : Struct n f)
    (hne : f ≠ targetF n) : ∃ b, 2 ≤ f b := by
  by_contra hcon
  push_neg at hcon
  exact hne (Struct_le_one_eq_target n f h (fun b => by have := hcon b; omega))

/-- Tail mass strictly to the right of `k`. -/
def tail (n : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.Ico (k + 1) (n + 1), f i

/-- Center-of-mass potential (sum of tail masses). -/
def Phi (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.range n, tail n f k

/-- Each tail-mass increases by `⌊f k / 2⌋` under a step. -/
lemma tail_step (n : ℕ) (f : ℕ → ℕ) (k : ℕ) (hk : k ≤ n) (hfn : f n = 0) :
    tail n (stepF f) k = tail n f k + f k / 2 := by
  unfold tail
  have dstep := Finset.sum_range_add_sum_Ico (stepF f) (show k + 1 ≤ n + 1 by omega)
  have df := Finset.sum_range_add_sum_Ico f (show k + 1 ≤ n + 1 by omega)
  have sN := stepF_sum f n
  have sk := stepF_sum f k
  omega

/-- The potential increases by the total halved mass under a step. -/
lemma Phi_step (n : ℕ) (f : ℕ → ℕ) (hfn : f n = 0) :
    Phi n (stepF f) = Phi n f + ∑ k ∈ Finset.range n, f k / 2 := by
  unfold Phi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact tail_step n f k (by omega) hfn

/-- The process terminates: it eventually reaches the target. -/
lemma terminates (n : ℕ) (hn : 1 ≤ n) : ∃ k, P n k = targetF n := by
  by_contra hcon
  push_neg at hcon
  -- Φ increases by ≥ 1 each step
  have hmono : ∀ t, t ≤ Phi n (P n t) := by
    intro t
    induction t with
    | zero => exact Nat.zero_le _
    | succ s ih =>
      have hstep : P n (s + 1) = stepF (P n s) := by
        rw [P, Function.iterate_succ', Function.comp_apply, ← P]
      obtain ⟨fr, hfrn, hcontig, hsupp, hmass⟩ := Struct_P n hn s
      have hfn : P n s n = 0 := hsupp n hfrn
      have hPhi : Phi n (P n (s + 1)) = Phi n (P n s) + ∑ k ∈ Finset.range n, (P n s) k / 2 := by
        rw [hstep]; exact Phi_step n (P n s) hfn
      obtain ⟨b, hb⟩ := Struct_ne_target_cell2 n (P n s) (Struct_P n hn s) (hcon s)
      have hbn : b < n := by
        by_contra hbc
        rcases Nat.lt_or_ge fr b with h | h
        · rw [hsupp b h] at hb; omega
        · omega
      have hhalf : 1 ≤ ∑ k ∈ Finset.range n, (P n s) k / 2 := by
        have h1 : (P n s) b / 2 ≤ ∑ k ∈ Finset.range n, (P n s) k / 2 :=
          Finset.single_le_sum (f := fun k => (P n s) k / 2)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hbn)
        omega
      omega
  -- Φ is bounded by n*n
  have hbound : ∀ t, Phi n (P n t) ≤ n * n := by
    intro t
    obtain ⟨fr, hfrn, hcontig, hsupp, hmass⟩ := Struct_P n hn t
    have htail : ∀ k, tail n (P n t) k ≤ n := by
      intro k
      unfold tail
      calc ∑ i ∈ Finset.Ico (k + 1) (n + 1), (P n t) i
          ≤ ∑ i ∈ Finset.range (n + 1), (P n t) i := by
            apply Finset.sum_le_sum_of_subset
            intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega
        _ = n := hmass
    calc Phi n (P n t) = ∑ k ∈ Finset.range n, tail n (P n t) k := rfl
      _ ≤ ∑ k ∈ Finset.range n, n := Finset.sum_le_sum (fun k _ => htail k)
      _ = n * n := by rw [Finset.sum_const, Finset.card_range]; ring
  have h1 := hmono (n * n + 1)
  have h2 := hbound (n * n + 1)
  omega

/-- One step of the process. -/
lemma P_succ (n t : ℕ) : P n (t + 1) = stepF (P n t) := by
  rw [P, Function.iterate_succ', Function.comp_apply, ← P]

/-- The target is a fixed point of `stepF`. -/
lemma stepF_targetF (n : ℕ) (hn : 1 ≤ n) : stepF (targetF n) = targetF n := by
  funext i
  simp only [stepF, targetF]
  split_ifs <;> omega

/-- The `(n+1)`-target is the `n`-target with an extra unit at position `n`. -/
lemma targetF_succ (n : ℕ) : targetF (n + 1) = fun j => targetF n j + eOne n j := by
  funext j
  simp only [targetF, eOne]
  split_ifs <;> omega

/-- The defect recursion in terms of `gstep`. -/
lemma gdef_succ (n t : ℕ) : gdef n (t + 1) = gstep (P n t) (gdef n t) := by
  rw [gdef, gstep]

/-- The process reaches the target at time `a n`. -/
lemma a_mem (n : ℕ) (hn : 1 ≤ n) : P n (a n) = targetF n := by
  rw [a_eq n hn]
  exact Nat.sInf_mem (terminates n hn)

/-- Before time `a n` the target is not reached. -/
lemma a_min (n : ℕ) (hn : 1 ≤ n) : ∀ t, t < a n → P n t ≠ targetF n := by
  intro t ht hmem
  rw [a_eq n hn] at ht
  have := Nat.sInf_le (show t ∈ {k | P n k = targetF n} from hmem)
  omega

/-- The process stabilizes at the target after time `a n`. -/
lemma P_stab (n : ℕ) (hn : 1 ≤ n) : ∀ s, P n (a n + s) = targetF n := by
  intro s
  induction s with
  | zero => simpa using a_mem n hn
  | succ k ih =>
    rw [show a n + (k + 1) = (a n + k) + 1 from by ring, P_succ, ih, stepF_targetF n hn]

/-- For `n ≥ 2`, `a n ≥ 1`. -/
lemma a_pos (n : ℕ) (hn2 : 2 ≤ n) : 1 ≤ a n := by
  rcases Nat.eq_zero_or_pos (a n) with h | h
  · exfalso
    have hm := a_mem n (by omega)
    rw [h] at hm
    have h0 : P n 0 0 = targetF n 0 := congrFun hm 0
    have e1 : P n 0 0 = n := by simp [P, initF]
    have e2 : targetF n 0 = 1 := by
      simp only [targetF]; rw [if_pos (by omega)]
    rw [e1, e2] at h0
    omega
  · exact h

/-- The invariant at time `0`. -/
lemma Inv_init (n : ℕ) (hn2 : 2 ≤ n) : Inv n (gdef n 0) (P n 0) := by
  have hP0 : P n 0 = initF n := by simp [P]
  have hg0 : gdef n 0 = 0 := rfl
  rw [hP0, hg0]
  refine ⟨0, 0, by omega, le_refl 0, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · intro i hi; interval_cases i; simp only [initF, if_pos]; omega
  · intro i hi; simp only [initF]; rw [if_neg (by omega)]
  · simp only [initF, if_pos]; omega
  · intro i hi; omega
  · have : ∀ i, initF n i = if i = 0 then n else 0 := fun i => rfl
    simp only [this]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => n)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- The invariant holds at every non-terminal time. -/
lemma Inv_holds (n : ℕ) (hn2 : 2 ≤ n) : ∀ t, t < a n → Inv n (gdef n t) (P n t) := by
  intro t
  induction t with
  | zero => intro _; exact Inv_init n hn2
  | succ s ih =>
    intro hlt
    have hsa : s < a n := by omega
    have hInvs := ih hsa
    have hne : P n (s + 1) ≠ targetF n := a_min n (by omega) (s + 1) hlt
    have hnt : ∃ b, 2 ≤ P n (s + 1) b :=
      Struct_ne_target_cell2 n (P n (s + 1)) (Struct_P n (by omega) (s + 1)) hne
    rw [P_succ] at hnt
    rw [gdef_succ, P_succ]
    exact Inv_step n (gdef n s) (P n s) hInvs hnt

/-- A sum of `m` cells each `≥ 1`, one of which is `≥ 2`, is at least `m + 1`. -/
lemma sum_ge_card_add (C : ℕ → ℕ) (m b : ℕ) (h : ∀ i, i < m → 1 ≤ C i)
    (hb : b < m) (hb2 : 2 ≤ C b) : m + 1 ≤ ∑ i ∈ Finset.range m, C i := by
  have hmem : b ∈ Finset.range m := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase (Finset.range m) C hmem]
  have herase : ((Finset.range m).erase b).card = m - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_range]
  have hge : ((Finset.range m).erase b).card ≤ ∑ i ∈ (Finset.range m).erase b, C i := by
    have hh := Finset.card_nsmul_le_sum ((Finset.range m).erase b) C 1
      (fun i hi => h i (Finset.mem_range.mp (Finset.mem_of_mem_erase hi)))
    simpa using hh
  omega

/-- The defect at the terminal time is `n-2` or `n-1`. -/
lemma d_bound (n : ℕ) (hn2 : 2 ≤ n) :
    gdef n (a n) = n - 2 ∨ gdef n (a n) = n - 1 := by
  obtain ⟨p, hp⟩ : ∃ p, a n = p + 1 := ⟨a n - 1, by have := a_pos n hn2; omega⟩
  have hpa : p < a n := by omega
  have hInvp := Inv_holds n hn2 p hpa
  set C := P n p with hC
  have hstep : stepF C = targetF n := by
    rw [hC, ← P_succ, ← hp]; exact a_mem n (by omega)
  obtain ⟨fr, bl, hfrn, hblfr, hcontig, hsupp, hbl2, hones, hmass, hglow, hghigh⟩ := hInvp
  -- (a) fr ≥ n-2
  have hval : stepF C (n - 1) = 1 := by
    rw [hstep]; simp only [targetF]; rw [if_pos (by omega)]
  have hfr_ge : n - 2 ≤ fr := by
    by_contra hc
    have : stepF C (n - 1) = 0 := stepF_support C fr hsupp (n - 1) (by omega)
    omega
  -- (b) fr ≤ n-2 (fr ≠ n-1)
  have hfr_le : fr ≤ n - 2 := by
    by_contra hc
    have hCn : C n = 0 := hsupp n hfrn
    have hsum : ∑ i ∈ Finset.range (n + 1), C i = ∑ i ∈ Finset.range n, C i := by
      rw [Finset.sum_range_succ, hCn, Nat.add_zero]
    have hge : n + 1 ≤ ∑ i ∈ Finset.range n, C i :=
      sum_ge_card_add C n bl (fun i hi => hcontig i (by omega)) (by omega) hbl2
    omega
  have hfr : fr = n - 2 := by omega
  -- C bl = 2
  have hCbl2 : C bl = 2 := by
    by_contra hc
    have hc3 : 3 ≤ C bl := by omega
    have h2 : 2 ≤ stepF C bl := by simp only [stepF]; split_ifs <;> omega
    have hle1 : targetF n bl ≤ 1 := by simp only [targetF]; split_ifs <;> omega
    have := congrFun hstep bl
    omega
  -- bl = fr
  have hbleqfr : bl = fr := by
    by_contra hc
    have hblfr2 : bl < fr := by omega
    have h2 : 2 ≤ stepF C (bl + 1) := by
      rw [stepF_succ, hCbl2]
      have : 1 ≤ C (bl + 1) := hcontig (bl + 1) (by omega)
      omega
    have hle1 : targetF n (bl + 1) ≤ 1 := by simp only [targetF]; split_ifs <;> omega
    have := congrFun hstep (bl + 1)
    omega
  -- compute d
  have hd : gdef n (a n) = gstep C (gdef n p) := by rw [hp, gdef_succ, ← hC]
  set g0 := gdef n p with hg0
  have hg0lo : fr ≤ g0 + 1 := by rw [← hbleqfr]; exact hglow
  have hg0hi : g0 ≤ fr + 1 := hghigh
  rw [hd, gstep]
  rcases Nat.lt_trichotomy g0 fr with h | h | h
  · -- g0 < fr : C g0 = 1
    have hCg : C g0 = 1 := hones g0 (by omega)
    rw [hCg, if_pos (by decide)]
    left; omega
  · -- g0 = fr : C g0 = 2
    have hCg : C g0 = 2 := by rw [h, ← hbleqfr]; exact hCbl2
    rw [hCg, if_neg (by decide)]
    left; omega
  · -- g0 > fr : g0 = fr+1, C g0 = 0
    have hCg : C g0 = 0 := hsupp g0 (by omega)
    rw [hCg, if_neg (by decide)]
    right; omega

/-- The process is always zero at position `n`. -/
lemma P_zero_at_n (n : ℕ) (hn : 1 ≤ n) (t : ℕ) : P n t n = 0 := by
  obtain ⟨fr, hfrn, hcontig, hsupp, hmass⟩ := Struct_P n hn t
  exact hsupp n hfrn

/-- Stepping the defect on the (stable) target. -/
lemma gstep_targetF (n g : ℕ) : gstep (targetF n) g = g + (if g < n then 1 else 0) := by
  simp only [gstep, targetF]
  by_cases hg : g < n <;> simp [hg]

/-- The defect, after the process stabilizes, increases by one each step until it hits `n`. -/
lemma gdef_after (n : ℕ) (hn : 1 ≤ n) (hd : gdef n (a n) ≤ n) (s : ℕ) :
    gdef n (a n + s) = min (gdef n (a n) + s) n := by
  induction s with
  | zero => simp; omega
  | succ k ih =>
    rw [show a n + (k + 1) = (a n + k) + 1 from by ring, gdef_succ, ih, P_stab n hn k,
        gstep_targetF]
    split_ifs <;> omega

/-- Characterization of when the `(n+1)`-process reaches its target. -/
lemma coupling_target (n t : ℕ) (hn : 1 ≤ n) :
    P (n + 1) t = targetF (n + 1) ↔ (P n t = targetF n ∧ gdef n t = n) := by
  have hc := P_coupling n t
  have ht := targetF_succ n
  constructor
  · intro h
    have key : ∀ j, P n t j + eOne (gdef n t) j = targetF n j + eOne n j := by
      intro j
      have hj := congrFun h j
      rw [hc, ht] at hj
      simpa using hj
    have hgn : gdef n t = n := by
      have hj := key n
      have h1 : P n t n = 0 := P_zero_at_n n hn t
      have h2 : targetF n n = 0 := by simp only [targetF]; rw [if_neg (by omega)]
      have h3 : eOne n n = 1 := by simp [eOne]
      rw [h1, h2, h3] at hj
      simp only [eOne] at hj
      by_contra hne
      rw [if_neg (by omega)] at hj
      omega
    refine ⟨?_, hgn⟩
    funext j
    have hj := key j
    rw [hgn] at hj
    omega
  · intro ⟨h1, h2⟩
    rw [hc, ht]
    funext j
    rw [h2]
    have hj := congrFun h1 j
    omega

/-- The reduction formula: `a(n+1) = a n + (n - gdef n (a n))`. -/
lemma a_succ_eq (n : ℕ) (hn : 1 ≤ n) (hd : gdef n (a n) ≤ n) :
    a (n + 1) = a n + (n - gdef n (a n)) := by
  rw [a_eq (n + 1) (by omega)]
  have hmemT : P (n + 1) (a n + (n - gdef n (a n))) = targetF (n + 1) := by
    rw [coupling_target n _ hn]
    refine ⟨P_stab n hn (n - gdef n (a n)), ?_⟩
    rw [gdef_after n hn hd (n - gdef n (a n))]; omega
  have hminT : ∀ t, t < a n + (n - gdef n (a n)) → P (n + 1) t ≠ targetF (n + 1) := by
    intro t ht hcon
    rw [coupling_target n t hn] at hcon
    obtain ⟨hPt, hgt⟩ := hcon
    rcases Nat.lt_or_ge t (a n) with hlt | hge
    · exact a_min n hn t hlt hPt
    · obtain ⟨s, rfl⟩ : ∃ s, t = a n + s := ⟨t - a n, by omega⟩
      rw [gdef_after n hn hd s] at hgt
      omega
  have hne : {t | P (n + 1) t = targetF (n + 1)}.Nonempty := ⟨_, hmemT⟩
  have hle : sInf {t | P (n + 1) t = targetF (n + 1)} ≤ a n + (n - gdef n (a n)) :=
    Nat.sInf_le hmemT
  have hmem := Nat.sInf_mem hne
  by_contra hcon
  have hlt : sInf {t | P (n + 1) t = targetF (n + 1)} < a n + (n - gdef n (a n)) := by omega
  exact hminT _ hlt hmem

/-- Main result for the local sequence `a`. -/
theorem main (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have ha1 : a 1 = 0 := by
      rw [a_eq 1 (by omega)]
      have h0 : P 1 0 = targetF 1 := by
        funext j; simp only [P, Function.iterate_zero, id, initF, targetF]
        split_ifs <;> omega
      have hmem : (0 : ℕ) ∈ {k | P 1 k = targetF 1} := h0
      have := Nat.sInf_le hmem
      omega
    have hd : gdef 1 (a 1) ≤ 1 := by
      rw [ha1]; have h : gdef 1 0 = 0 := rfl; omega
    rw [a_succ_eq 1 (by omega) hd, ha1]
    left
    have h : gdef 1 0 = 0 := rfl
    omega
  · have hd := d_bound n h2
    have hdle : gdef n (a n) ≤ n := by rcases hd with h | h <;> omega
    rw [a_succ_eq n hn hdle]
    rcases hd with h | h
    · right; rw [h]; omega
    · left; rw [h]; omega

end A300997

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  exact A300997.main n hn
