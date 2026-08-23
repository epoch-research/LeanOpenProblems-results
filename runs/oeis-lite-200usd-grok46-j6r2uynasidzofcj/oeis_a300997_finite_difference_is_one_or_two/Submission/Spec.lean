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

/-! ### Helper CA definitions (definitionally matching those inside `a`) -/

def halfCeil (m : ℕ) : ℕ := (m + 1) / 2
def halfFloor (m : ℕ) : ℕ := m / 2

def trimTrailingZeros (l : List ℕ) : List ℕ :=
  (l.reverse.dropWhile (fun x => x = 0)).reverse

def caStep (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfCeil ++ [0]
  let received_masses := 0 :: config.map halfFloor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trimTrailingZeros next_config_long

/-- Cell value at index `i`, or `0` if out of range. -/
def dget (c : List ℕ) (i : ℕ) : ℕ := c.getD i 0

lemma foldl_range_iterate {α : Type*} (f : α → α) (x : α) (t : ℕ) :
    (List.range t).foldl (fun acc _ => f acc) x = f^[t] x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [range_succ, foldl_append, ih, foldl_cons, foldl_nil, iterate_succ_apply']

lemma iterate_congr_fn {α : Type*} {f g : α → α} (h : ∀ x, f x = g x) (n : ℕ) (x : α) :
    f^[n] x = g^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', h, ih]

lemma caStep_unfold (c : List ℕ) :
    caStep c =
      trimTrailingZeros
        (zipWith Nat.add (c.map halfCeil ++ [0]) (0 :: c.map halfFloor)) := rfl

lemma a_eq_sInf (n : ℕ) (hn : n ≠ 0) :
    a n = sInf {k | caStep^[k] [n] = List.replicate n 1} := by
  unfold a
  simp only [hn, ↓reduceIte]
  congr 1
  ext k
  have hstep : ∀ c, (fun acc =>
      (dropWhile (fun x => decide (x = 0))
          (zipWith Nat.add (map (fun m => (m + 1) / 2) acc ++ [0])
            (0 :: map (fun m => m / 2) acc)).reverse).reverse) c =
      caStep c := by
    intro c
    unfold caStep halfCeil halfFloor trimTrailingZeros
    rfl
  simp only [Set.mem_setOf_eq, foldl_range_iterate, iterate_congr_fn hstep]

/-! ### Functional CA model -/

def stepF (c : ℕ → ℕ) : ℕ → ℕ :=
  fun i => (c i + 1) / 2 + if i = 0 then 0 else c (i - 1) / 2

def initF (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

def onesF (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

def addAt (c : ℕ → ℕ) (p : ℕ) : ℕ → ℕ :=
  fun i => c i + if i = p then 1 else 0

lemma stepF_zero (c : ℕ → ℕ) : stepF c 0 = (c 0 + 1) / 2 := by simp [stepF]

lemma stepF_succ (c : ℕ → ℕ) (j : ℕ) :
    stepF c (j + 1) = (c (j + 1) + 1) / 2 + c j / 2 := by simp [stepF]

lemma onesF_step (n : ℕ) : stepF (onesF n) = onesF n := by
  ext i
  simp only [stepF, onesF]
  cases i with
  | zero =>
    by_cases h : 0 < n <;> simp [h]
  | succ j =>
    simp only [succ_ne_zero, ↓reduceIte, add_tsub_cancel_right]
    by_cases h1 : j + 1 < n
    · have hj : j < n := by omega
      simp [h1, hj]
    · by_cases hj : j < n
      · have : j + 1 = n := by omega
        simp [h1, hj]
      · simp [h1, hj]

lemma initF_zero : initF 0 = onesF 0 := by
  ext i; cases i <;> rfl

lemma initF_one : initF 1 = onesF 1 := by
  ext i; cases i <;> simp [initF, onesF]

/-! ### Extra particle coupling -/

lemma ceil_half_succ (m : ℕ) :
    (m + 2) / 2 = (m + 1) / 2 + (1 - m % 2) := by omega

lemma floor_half_succ (m : ℕ) :
    (m + 1) / 2 = m / 2 + m % 2 := by omega

lemma stepF_addAt (c : ℕ → ℕ) (p : ℕ) :
    stepF (addAt c p) =
      addAt (stepF c) (if c p % 2 = 1 then p + 1 else p) := by
  funext i
  unfold stepF addAt
  grind

/-- Position of the extra particle comparing mass `n+1` against mass `n`. -/
def extraPos (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      let c := stepF^[t] (initF n)
      let p := extraPos n t
      if c p % 2 = 1 then p + 1 else p

lemma extraPos_succ (n t : ℕ) :
    extraPos n (t + 1) =
      if (stepF^[t] (initF n)) (extraPos n t) % 2 = 1 then
        extraPos n t + 1 else extraPos n t := rfl

lemma addAt_init (n : ℕ) : addAt (initF n) 0 = initF (n + 1) := by
  ext i
  simp [addAt, initF]
  split_ifs <;> omega

lemma stepF_iterate_addAt (n t : ℕ) :
    stepF^[t] (initF (n + 1)) = addAt (stepF^[t] (initF n)) (extraPos n t) := by
  induction t with
  | zero =>
    simp [extraPos, addAt_init]
  | succ t ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, stepF_addAt, extraPos_succ]

/-! ### Support, mass, potential -/

def suppBound (c : ℕ → ℕ) (N : ℕ) : Prop := ∀ i, N ≤ i → c i = 0

lemma suppBound_init (n : ℕ) : suppBound (initF n) 1 := by
  intro i hi
  simp [initF]
  omega

lemma suppBound_ones (n : ℕ) : suppBound (onesF n) n := by
  intro i hi
  simp [onesF]
  omega

lemma suppBound_step {c : ℕ → ℕ} {N : ℕ} (h : suppBound c N) :
    suppBound (stepF c) (N + 1) := by
  intro i hi
  simp only [stepF]
  have h1 : c i = 0 := h i (by omega)
  by_cases hi0 : i = 0
  · subst hi0
    simp [h1]
  · have h2 : c (i - 1) = 0 := h (i - 1) (by omega)
    simp [hi0, h1, h2]

lemma suppBound_iterate (n t : ℕ) : suppBound (stepF^[t] (initF n)) (t + 1) := by
  induction t with
  | zero => exact suppBound_init n
  | succ t ih =>
    rw [iterate_succ_apply']
    exact suppBound_step ih

lemma suppBound_mono {c : ℕ → ℕ} {N M : ℕ} (h : suppBound c N) (hNM : N ≤ M) :
    suppBound c M :=
  fun i hi => h i (le_trans hNM hi)

def massR (c : ℕ → ℕ) (N : ℕ) : ℕ := ∑ i ∈ Finset.range N, c i

lemma massR_init (n : ℕ) : massR (initF n) 1 = n := by
  simp [massR, initF]

lemma massR_ones (n : ℕ) : massR (onesF n) n = n := by
  simp only [massR]
  trans ∑ _i ∈ Finset.range n, (1 : ℕ)
  · apply Finset.sum_congr rfl
    intro i hi
    simp [onesF, Finset.mem_range.mp hi]
  · simp

lemma massR_step {c : ℕ → ℕ} {N : ℕ} (h : suppBound c N) :
    massR (stepF c) (N + 1) = massR c N := by
  simp only [massR, stepF]
  have hN : c N = 0 := h N le_rfl
  rw [Finset.sum_add_distrib]
  have hleft : ∑ i ∈ Finset.range (N + 1), (c i + 1) / 2 =
      ∑ i ∈ Finset.range N, (c i + 1) / 2 := by
    rw [Finset.sum_range_succ, hN]
    simp
  have hright : ∑ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c (i - 1) / 2) =
      ∑ i ∈ Finset.range N, c i / 2 := by
    simp [Finset.sum_range_succ']
  rw [hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  omega

lemma massR_iterate (n t : ℕ) : massR (stepF^[t] (initF n)) (t + 1) = n := by
  induction t with
  | zero => exact massR_init n
  | succ t ih =>
    rw [iterate_succ_apply', massR_step (suppBound_iterate n t), ih]

lemma massR_eq_of_supp {c : ℕ → ℕ} {N M : ℕ} (hN : suppBound c N) (hNM : N ≤ M) :
    massR c M = massR c N := by
  simp only [massR]
  rw [← Finset.sum_range_add_sum_Ico _ hNM]
  have : ∑ i ∈ Finset.Ico N M, c i = 0 :=
    Finset.sum_eq_zero (fun i hi => hN i (Finset.mem_Ico.mp hi).1)
  rw [this, add_zero]

def potR (c : ℕ → ℕ) (N : ℕ) : ℕ := ∑ i ∈ Finset.range N, i * c i

lemma potR_init (n : ℕ) : potR (initF n) 1 = 0 := by
  simp [potR, initF]

lemma potR_ones (n : ℕ) : potR (onesF n) n = ∑ i ∈ Finset.range n, i := by
  simp only [potR]
  apply Finset.sum_congr rfl
  intro i hi
  simp [onesF, Finset.mem_range.mp hi]

lemma potR_step {c : ℕ → ℕ} {N : ℕ} (h : suppBound c N) :
    potR (stepF c) (N + 1) = potR c N + ∑ i ∈ Finset.range N, c i / 2 := by
  simp only [potR, stepF]
  have hN : c N = 0 := h N le_rfl
  -- Split ∑ i * stepF i = ∑ i * (c i + 1)/2 + ∑ i * [i≠0] c(i-1)/2
  have hsplit :
      ∑ i ∈ Finset.range (N + 1),
        i * ((c i + 1) / 2 + if i = 0 then 0 else c (i - 1) / 2) =
      ∑ i ∈ Finset.range (N + 1), i * ((c i + 1) / 2) +
        ∑ i ∈ Finset.range (N + 1), i * (if i = 0 then 0 else c (i - 1) / 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsplit]
  have h1 : ∑ i ∈ Finset.range (N + 1), i * ((c i + 1) / 2) =
      ∑ i ∈ Finset.range N, i * ((c i + 1) / 2) := by
    rw [Finset.sum_range_succ, hN]
    simp
  have h2 : ∑ i ∈ Finset.range (N + 1), i * (if i = 0 then 0 else c (i - 1) / 2) =
      ∑ j ∈ Finset.range N, (j + 1) * (c j / 2) := by
    simp [Finset.sum_range_succ']
  rw [h1, h2]
  have h3 : ∑ j ∈ Finset.range N, (j + 1) * (c j / 2) =
      ∑ j ∈ Finset.range N, j * (c j / 2) + ∑ j ∈ Finset.range N, c j / 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h3]
  have h4 : ∑ i ∈ Finset.range N, i * ((c i + 1) / 2) +
        ∑ j ∈ Finset.range N, j * (c j / 2) =
      ∑ i ∈ Finset.range N, i * c i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have : i * ((c i + 1) / 2) + i * (c i / 2) = i * c i := by
      have : (c i + 1) / 2 + c i / 2 = c i := by omega
      rw [← Nat.mul_add, this]
    exact this
  grind

/-! ### Leading ones and the q-invariant -/

lemma exists_ne_one_of_supp {c : ℕ → ℕ} {N : ℕ} (h : suppBound c N) :
    ∃ i, c i ≠ 1 :=
  ⟨N, by simp [h N le_rfl]⟩

noncomputable def lead (c : ℕ → ℕ) (h : ∃ i, c i ≠ 1) : ℕ := Nat.find h

lemma lead_prefix {c : ℕ → ℕ} (h : ∃ i, c i ≠ 1) :
    ∀ i < lead c h, c i = 1 := by
  intro i hi
  have : ¬ (c i ≠ 1) := Nat.find_min h hi
  exact of_not_not this

lemma lead_ne {c : ℕ → ℕ} (h : ∃ i, c i ≠ 1) : c (lead c h) ≠ 1 :=
  Nat.find_spec h

lemma lead_min {c : ℕ → ℕ} (h : ∃ i, c i ≠ 1) {i : ℕ} (hi : c i ≠ 1) :
    lead c h ≤ i :=
  Nat.find_min' h hi

lemma lead_ones (n : ℕ) : lead (onesF n) (exists_ne_one_of_supp (suppBound_ones n)) = n := by
  set h := exists_ne_one_of_supp (suppBound_ones n)
  have hn : onesF n n ≠ 1 := by simp [onesF]
  have hle : lead (onesF n) h ≤ n := lead_min h hn
  apply le_antisymm hle
  by_contra hlt
  have : lead (onesF n) h < n := Nat.lt_of_not_ge hlt
  have : onesF n (lead (onesF n) h) = 1 := by simp [onesF, this]
  exact lead_ne h this

/-- A configuration is "good" if it has finite support, no internal zeros, and
    cells after the leading ones (if any remain) start with a cell `≥ 2`. -/
def noInternalZero (c : ℕ → ℕ) : Prop :=
  ∀ i, c (i + 1) ≠ 0 → c i ≠ 0

lemma noInternalZero_init (n : ℕ) : noInternalZero (initF n) := by
  intro i
  simp [initF]

lemma noInternalZero_ones (n : ℕ) : noInternalZero (onesF n) := by
  intro i
  simp [onesF]
  omega

lemma stepF_pos_zero {c : ℕ → ℕ} (h : c 0 ≠ 0) : stepF c 0 ≠ 0 := by
  simp [stepF]
  have : 1 ≤ c 0 := Nat.one_le_iff_ne_zero.mpr h
  omega

lemma noInternalZero_step {c : ℕ → ℕ} (h : noInternalZero c) (hpos0 : c 0 ≠ 0) :
    noInternalZero (stepF c) := by
  intro i hi
  cases i with
  | zero => exact stepF_pos_zero hpos0
  | succ j =>
    simp [stepF] at hi ⊢
    by_contra hz
    have cj1 : c (j + 1) = 0 := by omega
    rw [cj1] at hi
    have : c (j + 2) ≠ 0 := by
      intro h0; simp [h0] at hi
    exact h (j + 1) this cj1

lemma init_pos (n : ℕ) (hn : n ≠ 0) : initF n 0 ≠ 0 := by
  simp [initF, hn]

lemma iterate_pos_zero (n t : ℕ) (hn : n ≠ 0) : (stepF^[t] (initF n)) 0 ≠ 0 := by
  induction t with
  | zero => exact init_pos n hn
  | succ t ih =>
    rw [iterate_succ_apply']
    exact stepF_pos_zero ih

lemma iterate_noInternalZero (n t : ℕ) (hn : n ≠ 0) :
    noInternalZero (stepF^[t] (initF n)) := by
  induction t with
  | zero => exact noInternalZero_init n
  | succ t ih =>
    rw [iterate_succ_apply']
    exact noInternalZero_step ih (iterate_pos_zero n t hn)

lemma noInternalZero_le {c : ℕ → ℕ} (h : noInternalZero c) {i j : ℕ}
    (hij : j ≤ i) (hi : c i ≠ 0) : c j ≠ 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  subst i
  clear hij
  revert hi
  induction k with
  | zero => intro hi; simpa using hi
  | succ k ih =>
    intro hi
    apply ih
    exact h (j + k) (by simpa [Nat.add_assoc] using hi)

def stateF (n t : ℕ) : ℕ → ℕ := stepF^[t] (initF n)

lemma stateF_mass (n t : ℕ) : massR (stateF n t) (t + 1) = n :=
  massR_iterate n t

lemma stateF_supp (n t : ℕ) : suppBound (stateF n t) (t + 1) :=
  suppBound_iterate n t

lemma exists_ne_one_state (n t : ℕ) : ∃ i, stateF n t i ≠ 1 :=
  exists_ne_one_of_supp (stateF_supp n t)

noncomputable def leadState (n t : ℕ) : ℕ := lead (stateF n t) (exists_ne_one_state n t)

lemma leadState_prefix (n t : ℕ) :
    ∀ i < leadState n t, stateF n t i = 1 :=
  lead_prefix (exists_ne_one_state n t)

lemma leadState_ne (n t : ℕ) : stateF n t (leadState n t) ≠ 1 :=
  lead_ne (exists_ne_one_state n t)

lemma leadState_min (n t : ℕ) {i : ℕ} (hi : stateF n t i ≠ 1) :
    leadState n t ≤ i :=
  lead_min (exists_ne_one_state n t) hi

lemma after_zero_all_zero {c : ℕ → ℕ} (hni : noInternalZero c) {L : ℕ}
    (h0 : c L = 0) : ∀ i ≥ L, c i = 0 := by
  intro i hi
  by_contra hzi
  exact noInternalZero_le hni hi hzi h0

/-- If a reachable config of mass `n` is not `onesF n`, the first non-1 cell is `≥ 2`. -/
lemma lead_cell_ge_two (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n) :
    2 ≤ stateF n t (leadState n t) := by
  have hpref := leadState_prefix n t
  have hne := leadState_ne n t
  have hni := iterate_noInternalZero n t hn
  set L := leadState n t
  have h0 : stateF n t L ≠ 0 := by
    intro hz
    have hall : ∀ i ≥ L, stateF n t i = 0 := after_zero_all_zero hni hz
    have hsupp := stateF_supp n t
    have Lle : L ≤ t + 1 :=
      leadState_min n t (by simp [hsupp (t + 1) le_rfl])
    have hmassL : massR (stateF n t) (t + 1) = L := by
      simp only [massR]
      rw [← Finset.sum_range_add_sum_Ico _ Lle]
      have h1 : ∑ i ∈ Finset.range L, stateF n t i = ∑ _i ∈ Finset.range L, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpref i (Finset.mem_range.mp hi)
      have h2 : ∑ i ∈ Finset.Ico L (t + 1), stateF n t i = 0 :=
        Finset.sum_eq_zero (fun i hi => hall i (Finset.mem_Ico.mp hi).1)
      rw [h1, h2, add_zero]
      simp
    have Ln : L = n := by
      have := stateF_mass n t
      omega
    have : stateF n t = onesF n := by
      funext i
      by_cases hi : i < n
      · have hiL : i < L := by omega
        simp [onesF, hi, hpref i hiL]
      · have hiL : L ≤ i := by omega
        simp [onesF, hi, hall i hiL]
    exact hnot this
  omega

lemma onesF_iff_all_le_one (n t : ℕ) (hn : n ≠ 0) :
    stateF n t = onesF n ↔ ∀ i, stateF n t i ≤ 1 := by
  constructor
  · intro h i; rw [h]; simp [onesF]; split_ifs <;> omega
  · intro hle
    by_contra hnot
    have := lead_cell_ge_two n t hn hnot
    have := hle (leadState n t)
    omega

lemma stepF_sum_div2_pos {c : ℕ → ℕ} {N : ℕ} (h : suppBound c N)
    (hex : ∃ i, 2 ≤ c i) :
    1 ≤ ∑ i ∈ Finset.range N, c i / 2 := by
  obtain ⟨i, hi⟩ := hex
  have hiN : i < N := by
    by_contra hge
    have : c i = 0 := h i (Nat.le_of_not_gt hge)
    omega
  have : 1 ≤ c i / 2 := by omega
  exact le_trans this
    (Finset.single_le_sum (f := fun k => c k / 2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hiN))

/-- Occupied support of a reachable mass-`n` config is contained in `0 .. n-1`. -/
lemma stateF_supp_n (n t : ℕ) (hn : n ≠ 0) : suppBound (stateF n t) n := by
  intro i hi
  by_contra hzi
  have hni := iterate_noInternalZero n t hn
  have hpos : ∀ j ≤ i, stateF n t j ≠ 0 :=
    fun j hj => noInternalZero_le hni hj hzi
  have hi_lt : i < t + 1 := by
    by_contra hge
    exact hzi (stateF_supp n t i (by omega))
  have : i + 1 ≤ massR (stateF n t) (t + 1) := by
    simp only [massR]
    have ile : i + 1 ≤ t + 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ ile]
    have hge : i + 1 ≤ ∑ j ∈ Finset.range (i + 1), stateF n t j := by
      trans ∑ _j ∈ Finset.range (i + 1), (1 : ℕ)
      · simp
      · apply Finset.sum_le_sum
        intro j hj
        exact Nat.one_le_iff_ne_zero.mpr (hpos j (by simp at hj; omega))
    omega
  have := stateF_mass n t
  omega

lemma mass_at_n (n t : ℕ) (hn : n ≠ 0) :
    ∑ i ∈ Finset.range n, stateF n t i = n := by
  cases le_total n (t + 1) with
  | inl hle =>
    -- n ≤ t+1: extra cells n..t are 0 by stateF_supp_n
    have h := massR_eq_of_supp (stateF_supp_n n t hn) hle
    simpa [massR] using h.symm.trans (stateF_mass n t)
  | inr hle =>
    -- t+1 ≤ n: extra cells t+1..n-1 are 0 by stateF_supp
    have hm := stateF_mass n t
    have : ∑ i ∈ Finset.range n, stateF n t i =
        ∑ i ∈ Finset.range (t + 1), stateF n t i := by
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      have : ∑ i ∈ Finset.Ico (t + 1) n, stateF n t i = 0 :=
        Finset.sum_eq_zero (fun i hi => stateF_supp n t i (Finset.mem_Ico.mp hi).1)
      rw [this, add_zero]
    simpa [massR] using this.trans hm

lemma pot_bounded (n t : ℕ) (hn : n ≠ 0) :
    potR (stateF n t) (t + 1) ≤ n * n := by
  have hsn := stateF_supp_n n t hn
  have hpotn : potR (stateF n t) n ≤ n * n := by
    simp only [potR]
    have : ∑ i ∈ Finset.range n, i * stateF n t i ≤
        ∑ i ∈ Finset.range n, n * stateF n t i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_right _ (by simp at hi; omega)
    refine le_trans this ?_
    rw [← Finset.mul_sum, mass_at_n n t hn]
  cases le_total (t + 1) n with
  | inl hle =>
    have : potR (stateF n t) (t + 1) ≤ potR (stateF n t) n := by
      simp only [potR]
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      exact Nat.le_add_right _ _
    exact le_trans this hpotn
  | inr hle =>
    have : potR (stateF n t) (t + 1) = potR (stateF n t) n := by
      simp only [potR]
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      have : ∑ i ∈ Finset.Ico n (t + 1), i * stateF n t i = 0 :=
        Finset.sum_eq_zero (fun i hi => by simp [hsn i (Finset.mem_Ico.mp hi).1])
      rw [this, add_zero]
    rwa [this]

lemma exists_stable (n : ℕ) (hn : n ≠ 0) : ∃ t, stateF n t = onesF n := by
  classical
  let P (t : ℕ) : ℕ := potR (stateF n t) (t + 1)
  have hinc : ∀ t, stateF n t ≠ onesF n → P t + 1 ≤ P (t + 1) := by
    intro t hnot
    have hex : ∃ i, 2 ≤ stateF n t i := ⟨leadState n t, lead_cell_ge_two n t hn hnot⟩
    have hsum : 1 ≤ ∑ i ∈ Finset.range (t + 1), stateF n t i / 2 :=
      stepF_sum_div2_pos (stateF_supp n t) hex
    have heq : P (t + 1) = P t + ∑ i ∈ Finset.range (t + 1), stateF n t i / 2 := by
      simp only [P, stateF]
      rw [iterate_succ_apply', potR_step (suppBound_iterate n t)]
    rw [heq]
    omega
  have hbd : ∀ t, P t ≤ n * n := fun t => pot_bounded n t hn
  by_contra hnone
  push_neg at hnone
  have hmono : ∀ t, t ≤ P t := by
    intro t
    induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      have : P t + 1 ≤ P (t + 1) := hinc t (hnone t)
      omega
  have : n * n + 1 ≤ P (n * n + 1) := hmono (n * n + 1)
  have : P (n * n + 1) ≤ n * n := hbd (n * n + 1)
  omega

lemma stateF_succ (n t : ℕ) : stateF n (t + 1) = stepF (stateF n t) := by
  simp [stateF, iterate_succ_apply']

/- List–function correspondence -/

lemma dget_init (n : ℕ) : dget [n] = initF n := by
  funext i
  cases i with
  | zero => simp [dget, initF]
  | succ j => simp [dget, initF]

lemma dget_ones (n : ℕ) : dget (replicate n 1) = onesF n := by
  funext i
  simp [dget, onesF, List.getD, getElem?_replicate]
  split_ifs <;> simp

lemma trim_append_zero (l : List ℕ) :
    trimTrailingZeros (l ++ [0]) = trimTrailingZeros l := by
  simp [trimTrailingZeros, reverse_append]

lemma trim_append_pos (l : List ℕ) {a : ℕ} (ha : a ≠ 0) :
    trimTrailingZeros (l ++ [a]) = l ++ [a] := by
  simp [trimTrailingZeros, reverse_append, ha]

lemma dget_eq_getElem? (l : List ℕ) (i : ℕ) : dget l i = (l[i]?).getD 0 :=
  rfl

lemma dget_of_ge {l : List ℕ} {i : ℕ} (hi : l.length ≤ i) : dget l i = 0 := by
  simp [dget, List.getD, getElem?_eq_none hi]

lemma dget_append_singleton (l : List ℕ) (a i : ℕ) :
    dget (l ++ [a]) i = if i = l.length then a else dget l i := by
  simp [dget, List.getD, getElem?_append]
  by_cases hi : i < l.length
  · have : i ≠ l.length := by omega
    simp [hi, this]
  · simp [hi]
    by_cases h' : i = l.length
    · subst h'
      simp
    · have : ¬ i - l.length < 1 := by omega
      simp [this, h']

lemma dget_trim (l : List ℕ) : dget (trimTrailingZeros l) = dget l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    by_cases ha : a = 0
    · subst ha
      rw [trim_append_zero, ih]
      funext i
      rw [dget_append_singleton]
      split_ifs with h
      · exact dget_of_ge (l := l) (i := i) (Nat.le_of_eq h.symm)
      · rfl
    · rw [trim_append_pos l ha]

lemma dget_map_halfCeil (c : List ℕ) (i : ℕ) :
    dget (c.map halfCeil) i = halfCeil (dget c i) := by
  by_cases hi : i < c.length
  · have him : i < (c.map halfCeil).length := by simpa
    simp [dget, List.getD, getElem?_pos, hi, him, getElem_map]
  · have hge : c.length ≤ i := Nat.le_of_not_gt hi
    have hgem : (c.map halfCeil).length ≤ i := by simpa
    rw [dget_of_ge hge, dget_of_ge hgem]; rfl

lemma dget_map_halfFloor (c : List ℕ) (i : ℕ) :
    dget (c.map halfFloor) i = halfFloor (dget c i) := by
  by_cases hi : i < c.length
  · have him : i < (c.map halfFloor).length := by simpa
    simp [dget, List.getD, getElem?_pos, hi, him, getElem_map]
  · have hge : c.length ≤ i := Nat.le_of_not_gt hi
    have hgem : (c.map halfFloor).length ≤ i := by simpa
    rw [dget_of_ge hge, dget_of_ge hgem]; rfl

lemma dget_zipWith_add (l₁ l₂ : List ℕ) (i : ℕ) (hlen : l₁.length = l₂.length) :
    dget (zipWith Nat.add l₁ l₂) i = dget l₁ i + dget l₂ i := by
  by_cases h1 : i < l₁.length
  · have h2 : i < l₂.length := by omega
    have hz : i < (zipWith Nat.add l₁ l₂).length := by
      simp [length_zipWith]; omega
    simp [dget, List.getD, getElem?_pos, h1, h2, hz, getElem_zipWith]
  · have hz : (zipWith Nat.add l₁ l₂).length ≤ i := by
      simp [length_zipWith]; omega
    rw [dget_of_ge hz, dget_of_ge (Nat.le_of_not_gt h1),
        dget_of_ge (by omega : l₂.length ≤ i)]

lemma dget_caStep (c : List ℕ) : dget (caStep c) = stepF (dget c) := by
  funext i
  rw [caStep_unfold, dget_trim]
  have hbase : dget (c.map halfCeil ++ [0]) i = halfCeil (dget c i) := by
    rw [dget_append_singleton, dget_map_halfCeil]
    split_ifs with h
    · have : c.length ≤ i := by simp at h ⊢; omega
      rw [dget_of_ge this]
      simp [halfCeil]
    · rfl
  have hrecv : dget (0 :: c.map halfFloor) i =
      if i = 0 then 0 else halfFloor (dget c (i - 1)) := by
    cases i with
    | zero => simp [dget, List.getD]
    | succ j =>
      simp [dget, List.getD]
      simpa [dget] using dget_map_halfFloor c j
  have hlen : (c.map halfCeil ++ [0]).length = (0 :: c.map halfFloor).length := by simp
  rw [dget_zipWith_add _ _ _ hlen, hbase, hrecv]
  rfl

lemma dget_iterate (n t : ℕ) : dget (caStep^[t] [n]) = stateF n t := by
  induction t with
  | zero => simpa [stateF] using dget_init n
  | succ t ih =>
    rw [iterate_succ_apply', dget_caStep, stateF_succ, ih]

lemma caStep_getLast_ne_zero (c : List ℕ) (hne : caStep c ≠ []) :
    (caStep c).getLast hne ≠ 0 := by
  unfold caStep trimTrailingZeros
  set long := zipWith Nat.add (c.map halfCeil ++ [0]) (0 :: c.map halfFloor) with hlong
  set dw := long.reverse.dropWhile (fun x : ℕ => decide (x = 0)) with hdw
  have hne' : dw.reverse ≠ [] := by
    intro h
    apply hne
    simp [caStep, trimTrailingZeros, long, dw] at h ⊢
    exact h
  have hdwne : dw ≠ [] := by
    intro h; simp [h] at hne'
  have h0 : 0 < dw.length := length_pos_iff.mpr hdwne
  have hp : ¬ (fun x : ℕ => decide (x = 0)) (dw[0]'(Nat.zero_lt_of_lt h0)) :=
    dropWhile_get_zero_not (p := fun x : ℕ => decide (x = 0)) long.reverse h0
  have hhead : dw.head hdwne ≠ 0 := by
    rw [head_eq_getElem]
    intro hz; simp [hz] at hp
  simpa [caStep, trimTrailingZeros, long, dw] using
    (by
      have : dw.reverse.getLast hne' = dw.head hdwne := getLast_reverse hne'
      exact this ▸ hhead)

lemma iterate_ne_nil (n t : ℕ) (hn : n ≠ 0) : caStep^[t] [n] ≠ [] := by
  intro h
  have : dget (caStep^[t] [n]) 0 = 0 := by simp [dget, h]
  rw [dget_iterate] at this
  exact iterate_pos_zero n t hn this

lemma getLast_eq_dget {l : List ℕ} (hne : l ≠ []) :
    l.getLast hne = dget l (l.length - 1) := by
  have hix : l.length - 1 < l.length := by
    have := length_pos_iff.mpr hne; omega
  simp [dget, List.getD, getElem?_pos, hix, getLast_eq_getElem]

lemma iterate_last_dget_ne_zero (n t : ℕ) (hn : n ≠ 0) :
    dget (caStep^[t] [n]) ((caStep^[t] [n]).length - 1) ≠ 0 := by
  have hne := iterate_ne_nil n t hn
  rw [← getLast_eq_dget hne]
  cases t with
  | zero =>
    simp [hn]
  | succ t =>
    have hne' : caStep (caStep^[t] [n]) ≠ [] := by
      have := iterate_ne_nil n (t + 1) hn
      rw [iterate_succ_apply'] at this
      exact this
    have h := caStep_getLast_ne_zero (caStep^[t] [n]) hne'
    -- transport along iterate_succ
    have heq : caStep^[t + 1] [n] = caStep (caStep^[t] [n]) := iterate_succ_apply' _ _ _
    simp [heq] at h ⊢
    exact h

lemma eq_replicate_ones {l : List ℕ} {n : ℕ} (hn : n ≠ 0)
    (hne : l ≠ []) (hlast : dget l (l.length - 1) ≠ 0)
    (heq : dget l = onesF n) : l = replicate n 1 := by
  have hlen : l.length = n := by
    apply le_antisymm
    · by_contra h
      have : n < l.length := by omega
      have : n ≤ l.length - 1 := by omega
      have hz : dget l (l.length - 1) = 0 := by
        rw [heq]; simp [onesF]; omega
      exact hlast hz
    · have : dget l (n - 1) = 1 := by
        rw [heq]; simp [onesF]; omega
      have : n - 1 < l.length := by
        by_contra h
        have : dget l (n - 1) = 0 := dget_of_ge (by omega)
        omega
      omega
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hi'
    have h1 : dget l i = 1 := by
      rw [heq]; simp [onesF]; omega
    have hget : dget l i = l[i] := by
      simp [dget, List.getD, getElem?_pos, hi]
    have : l[i] = 1 := by rw [← hget]; exact h1
    simp [this, getElem_replicate]

lemma caStep_eq_ones_iff (n t : ℕ) (hn : n ≠ 0) :
    caStep^[t] [n] = replicate n 1 ↔ stateF n t = onesF n := by
  constructor
  · intro h
    rw [← dget_iterate, h, dget_ones]
  · intro h
    exact eq_replicate_ones hn (iterate_ne_nil n t hn) (iterate_last_dget_ne_zero n t hn)
      (by rw [dget_iterate, h])

lemma a_eq_sInf_state (n : ℕ) (hn : n ≠ 0) :
    a n = sInf {k | stateF n k = onesF n} := by
  rw [a_eq_sInf n hn]
  congr 1
  ext k
  exact caStep_eq_ones_iff n k hn

lemma stateF_at_a (n : ℕ) (hn : n ≠ 0) : stateF n (a n) = onesF n := by
  rw [a_eq_sInf_state n hn]
  exact Nat.sInf_mem (exists_stable n hn)

lemma stateF_before_a (n : ℕ) (hn : n ≠ 0) {t : ℕ} (ht : t < a n) :
    stateF n t ≠ onesF n := by
  rw [a_eq_sInf_state n hn] at ht
  exact Nat.notMem_of_lt_sInf ht

lemma stateF_addAt (n t : ℕ) :
    stateF (n + 1) t = addAt (stateF n t) (extraPos n t) :=
  stepF_iterate_addAt n t

/- Lead evolution -/

lemma leadState_lt_n (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n) :
    leadState n t < n := by
  by_contra hge
  have hle : n ≤ leadState n t := by omega
  have hpref : ∀ i < n, stateF n t i = 1 :=
    fun i hi => leadState_prefix n t i (lt_of_lt_of_le hi hle)
  have : stateF n t = onesF n := by
    funext i
    by_cases hi : i < n
    · simp [onesF, hi, hpref i hi]
    · simp [onesF, hi, stateF_supp_n n t hn i (by omega)]
  exact hnot this

lemma step_prefix_ones (n t : ℕ) (hnot : stateF n t ≠ onesF n) :
    ∀ i < leadState n t, stateF n (t + 1) i = 1 := by
  intro i hi
  have ci : stateF n t i = 1 := leadState_prefix n t i hi
  rw [stateF_succ]
  cases i with
  | zero => simp [stepF, ci]
  | succ j =>
    have cj : stateF n t j = 1 := leadState_prefix n t j (by omega)
    simp [stepF, ci, cj]

lemma step_at_lead (n t : ℕ) (hnot : stateF n t ≠ onesF n) :
    stateF n (t + 1) (leadState n t) = (stateF n t (leadState n t) + 1) / 2 := by
  rw [stateF_succ]
  by_cases hL : leadState n t = 0
  · simp [stepF, hL]
  · have : stateF n t (leadState n t - 1) = 1 :=
      leadState_prefix n t _ (by omega)
    simp only [stepF, hL, ↓reduceIte]
    omega

lemma lead_of_ge_three (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n)
    (hge : 3 ≤ stateF n t (leadState n t)) :
    leadState n (t + 1) = leadState n t := by
  have hpref := step_prefix_ones n t hnot
  have hat := step_at_lead n t hnot
  have hcell : stateF n (t + 1) (leadState n t) ≠ 1 := by
    rw [hat]; omega
  apply le_antisymm
  · exact leadState_min n (t + 1) hcell
  · by_contra h
    have hlt : leadState n (t + 1) < leadState n t := by omega
    have : stateF n (t + 1) (leadState n (t + 1)) = 1 := hpref _ hlt
    exact leadState_ne n (t + 1) this

lemma leadState_eq_of_ones (n t : ℕ) (h : stateF n t = onesF n) :
    leadState n t = n := by
  have hne : stateF n t n ≠ 1 := by rw [h]; simp [onesF]
  have hle : leadState n t ≤ n := leadState_min n t hne
  have hge : n ≤ leadState n t := by
    by_contra hlt
    have : stateF n t (leadState n t) = 1 := by
      rw [h]; simp [onesF]; omega
    exact leadState_ne n t this
  omega

lemma not_ones_of_ge_three (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n)
    (hge : 3 ≤ stateF n t (leadState n t)) :
    stateF n (t + 1) ≠ onesF n := by
  intro h
  have hL' : leadState n (t + 1) = n := leadState_eq_of_ones n (t + 1) h
  have := lead_of_ge_three n t hn hnot hge
  have := leadState_lt_n n t hn hnot
  omega

lemma last_config_of_zero (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n)
    (h2 : stateF n t (leadState n t) = 2)
    (hz : stateF n t (leadState n t + 1) = 0) :
    stateF n (t + 1) = onesF n ∧ leadState n t + 2 = n := by
  set L := leadState n t with hLdef
  have hni := iterate_noInternalZero n t hn
  have hall : ∀ i ≥ L + 1, stateF n t i = 0 := after_zero_all_zero hni hz
  have hpref := leadState_prefix n t
  have Llt : L < n := leadState_lt_n n t hn hnot
  have hcell : ∀ i, stateF n t i =
      if i < L then 1 else if i = L then 2 else 0 := by
    intro i
    by_cases h1 : i < L
    · simp [h1, hpref i h1]
    · by_cases h2' : i = L
      · simp [h1, h2', h2]
      · simp [h1, h2', hall i (by omega)]
  have hmass : n = L + 2 := by
    have hm := mass_at_n n t hn
    have hsum : ∑ i ∈ Finset.range n, stateF n t i = L + 2 := by
      have hle : L + 1 ≤ n := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      have s1 : ∑ i ∈ Finset.range (L + 1), stateF n t i = L + 2 := by
        rw [Finset.sum_range_succ]
        have s0 : ∑ i ∈ Finset.range L, stateF n t i = ∑ _i ∈ Finset.range L, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpref i (Finset.mem_range.mp hi)
        simp [s0, h2]
      have s2 : ∑ i ∈ Finset.Ico (L + 1) n, stateF n t i = 0 :=
        Finset.sum_eq_zero (fun i hi => hall i (Finset.mem_Ico.mp hi).1)
      omega
    omega
  refine ⟨?_, hmass.symm⟩
  funext i
  simp only [onesF]
  by_cases hi : i < n
  · simp only [hi, ↓reduceIte]
    have hiL : i < L + 2 := by omega
    rw [stateF_succ]
    simp only [stepF]
    by_cases hi0 : i = 0
    · subst i
      simp only [↓reduceIte]
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · have : stateF n t 0 = 2 := by
          have := hcell 0; simp [hL0] at this; exact this
        omega
      · have : stateF n t 0 = 1 := hpref 0 hLpos
        omega
    · simp only [hi0, ↓reduceIte]
      have hc := hcell i
      have hl := hcell (i - 1)
      by_cases hilt : i < L
      · have : stateF n t i = 1 := by simp [hilt] at hc; exact hc
        have : stateF n t (i - 1) = 1 := by
          have : i - 1 < L := by omega
          simp [this] at hl; exact hl
        omega
      · by_cases hieq : i = L
        · have hi2 : stateF n t i = 2 := by rw [hieq]; exact h2
          have hl1 : stateF n t (i - 1) = 1 := by
            have : i - 1 < L := by omega
            simp [this] at hl; exact hl
          omega
        · have hiL1 : i = L + 1 := by omega
          have hi0' : stateF n t i = 0 := hall i (by omega)
          have hl2 : stateF n t (i - 1) = 2 := by
            have : i - 1 = L := by omega
            rw [this]; exact h2
          omega
  · simp only [hi, ↓reduceIte]
    have : L + 2 ≤ i := by omega
    rw [stateF_succ]
    simp only [stepF]
    by_cases hi0 : i = 0
    · subst i; omega
    · simp only [hi0, ↓reduceIte]
      have : stateF n t i = 0 := hall i (by omega)
      have : stateF n t (i - 1) = 0 := hall (i - 1) (by omega)
      omega

lemma lead_of_two (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n)
    (h2 : stateF n t (leadState n t) = 2)
    (hnext : stateF n (t + 1) ≠ onesF n) :
    leadState n (t + 1) = leadState n t + 1 := by
  have hpref := step_prefix_ones n t hnot
  have hat := step_at_lead n t hnot
  have hat1 : stateF n (t + 1) (leadState n t) = 1 := by rw [hat, h2]
  have hgt : leadState n t < leadState n (t + 1) := by
    by_contra hle
    have : leadState n (t + 1) ≤ leadState n t := by omega
    have hall1 : ∀ i ≤ leadState n t, stateF n (t + 1) i = 1 := by
      intro i hi
      rcases eq_or_lt_of_le hi with hieq | hilt
      · rw [hieq]; exact hat1
      · exact hpref i hilt
    have : stateF n (t + 1) (leadState n (t + 1)) = 1 := hall1 _ (by omega)
    exact leadState_ne n (t + 1) this
  have hcell : 2 ≤ stateF n (t + 1) (leadState n t + 1) := by
    set L := leadState n t
    by_cases hz : stateF n t (L + 1) = 0
    · exact (hnext (last_config_of_zero n t hn hnot h2 hz).1).elim
    · have hge1 : 1 ≤ stateF n t (L + 1) := Nat.one_le_iff_ne_zero.mpr hz
      rw [stateF_succ]
      simp only [stepF]
      have : L + 1 ≠ 0 := by omega
      simp [this, h2]
      omega
  have hne1 : stateF n (t + 1) (leadState n t + 1) ≠ 1 := by omega
  have hle : leadState n (t + 1) ≤ leadState n t + 1 :=
    leadState_min n (t + 1) hne1
  omega

lemma last_step_shape (n t : ℕ) (hn : n ≠ 0)
    (hnot : stateF n t ≠ onesF n) (hnext : stateF n (t + 1) = onesF n) :
    leadState n t + 2 = n ∧
      stateF n t (leadState n t) = 2 ∧
      ∀ i, leadState n t < i → stateF n t i = 0 := by
  have hge := lead_cell_ge_two n t hn hnot
  by_cases h3 : 3 ≤ stateF n t (leadState n t)
  · exact (not_ones_of_ge_three n t hn hnot h3 hnext).elim
  have h2 : stateF n t (leadState n t) = 2 := by omega
  by_cases hz : stateF n t (leadState n t + 1) = 0
  · have hcfg := last_config_of_zero n t hn hnot h2 hz
    refine ⟨hcfg.2, h2, ?_⟩
    intro i hi
    exact after_zero_all_zero (iterate_noInternalZero n t hn) hz i (by omega)
  · have hge1 : 1 ≤ stateF n t (leadState n t + 1) :=
      Nat.one_le_iff_ne_zero.mpr hz
    have L1lt : leadState n t + 1 < n := by
      by_contra hge'
      exact hz (stateF_supp_n n t hn _ (by omega))
    have hm := mass_at_n n t hn
    have hsum : leadState n t + 3 ≤ n := by
      have hle : leadState n t + 2 ≤ n := by omega
      have hge' : ∑ i ∈ Finset.range (leadState n t + 2), stateF n t i ≤
          ∑ i ∈ Finset.range n, stateF n t i := by
        rw [← Finset.sum_range_add_sum_Ico _ hle]
        exact Nat.le_add_right _ _
      have hs : ∑ i ∈ Finset.range (leadState n t + 2), stateF n t i =
          leadState n t + 2 + stateF n t (leadState n t + 1) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have s0 : ∑ i ∈ Finset.range (leadState n t), stateF n t i =
            ∑ _i ∈ Finset.range (leadState n t), (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact leadState_prefix n t i (Finset.mem_range.mp hi)
        simp [s0, h2]
      have : leadState n t + 3 ≤
          ∑ i ∈ Finset.range (leadState n t + 2), stateF n t i := by
        omega
      omega
    have hat := step_at_lead n t hnot
    have hat1 : stateF n (t + 1) (leadState n t) = 1 := by rw [hat, h2]
    have hcell : 2 ≤ stateF n (t + 1) (leadState n t + 1) := by
      rw [stateF_succ]
      simp only [stepF]
      have : leadState n t + 1 ≠ 0 := by omega
      simp [this, h2]
      omega
    have hne1 : stateF n (t + 1) (leadState n t + 1) ≠ 1 := by omega
    have hlead : leadState n (t + 1) = leadState n t + 1 := by
      apply le_antisymm
      · exact leadState_min n (t + 1) hne1
      · have hpref := step_prefix_ones n t hnot
        have hgt : leadState n t < leadState n (t + 1) := by
          by_contra hle
          have hall1 : ∀ i ≤ leadState n t, stateF n (t + 1) i = 1 := by
            intro i hi
            rcases eq_or_lt_of_le hi with hieq | hilt
            · rw [hieq]; exact hat1
            · exact hpref i hilt
          have : stateF n (t + 1) (leadState n (t + 1)) = 1 := hall1 _ (by omega)
          exact leadState_ne n (t + 1) this
        omega
    have : leadState n (t + 1) = n := leadState_eq_of_ones n (t + 1) hnext
    omega

/- q-invariant and extra-particle location -/

lemma extraPos_lt (n t : ℕ) (hn : n ≠ 0)
    (hun : ∀ s < t, stateF n s ≠ onesF n) :
    extraPos n t < n := by
  induction t with
  | zero =>
    simp [extraPos]
    exact Nat.pos_of_ne_zero hn
  | succ t ih =>
    have hun' : ∀ s < t, stateF n s ≠ onesF n := fun s hs => hun s (by omega)
    have hp : extraPos n t < n := ih hun'
    have hnot : stateF n t ≠ onesF n := hun t (by omega)
    rw [extraPos_succ]
    split_ifs with hodd
    · by_contra hge
      have hp' : extraPos n t = n - 1 := by omega
      have hcell : stateF n t (n - 1) % 2 = 1 := by simpa [hp'] using hodd
      have hpos : stateF n t (n - 1) ≠ 0 := by omega
      have hni := iterate_noInternalZero n t hn
      have hallpos : ∀ j ≤ n - 1, stateF n t j ≠ 0 :=
        fun j hj => noInternalZero_le hni hj hpos
      have hm := mass_at_n n t hn
      have hle : ∀ i ∈ Finset.range n, (1 : ℕ) ≤ stateF n t i := by
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (hallpos i (by simp at hi; omega))
      have hsum1 : ∑ i ∈ Finset.range n, (1 : ℕ) = n := by simp
      have heq : ∀ i ∈ Finset.range n, stateF n t i = 1 := by
        have := (Finset.sum_eq_sum_iff_of_le hle).1 (by omega)
        intro i hi
        exact (this i hi).symm
      have : stateF n t = onesF n := by
        funext i
        by_cases hi : i < n
        · simp [onesF, hi, heq i (Finset.mem_range.mpr hi)]
        · simp [onesF, hi, stateF_supp_n n t hn i (by omega)]
      exact hnot this
    · omega

lemma extra_ge_lead (n t : ℕ) (hn : n ≠ 0) (hnot : stateF n t ≠ onesF n) :
    leadState n t ≤ extraPos n t + 1 := by
  induction t with
  | zero =>
    simp [extraPos]
    have h0 : stateF n 0 0 ≠ 1 := by
      intro heq
      have hn1 : n = 1 := by simp [stateF, initF] at heq; omega
      apply hnot
      funext i; cases i <;> simp [stateF, initF, onesF, hn1]
    have : leadState n 0 ≤ 0 := leadState_min (i := 0) n 0 h0
    omega
  | succ t ih =>
    have hnot0 : stateF n t ≠ onesF n := by
      intro h
      have : stateF n (t + 1) = onesF n := by rw [stateF_succ, h, onesF_step]
      exact hnot this
    have IH := ih hnot0
    set L := leadState n t
    set p := extraPos n t
    have hge := lead_cell_ge_two n t hn hnot0
    by_cases h3 : 3 ≤ stateF n t L
    · have hL' : leadState n (t + 1) = L := by
        simpa [L] using lead_of_ge_three n t hn hnot0 (by simpa [L] using h3)
      rw [hL', extraPos_succ]
      split_ifs <;> omega
    · have h2 : stateF n t L = 2 := by
        have : 2 ≤ stateF n t L := by simpa [L] using hge
        omega
      have hL' : leadState n (t + 1) = L + 1 := by
        simpa [L] using lead_of_two n t hn hnot0 (by simpa [L] using h2) hnot
      rw [hL', extraPos_succ]
      split_ifs with hodd
      · omega
      · by_contra hlt
        have hpL : p + 1 = L := by omega
        have hLpos : 0 < L := by omega
        have hp1 : stateF n t p = 1 := leadState_prefix n t p (by omega)
        have : stateF n t p % 2 = 1 := by omega
        exact hodd this

lemma extraPos_at_a (n : ℕ) (hn : n ≠ 0) :
    extraPos n (a n) = n - 1 ∨ 2 ≤ n ∧ extraPos n (a n) = n - 2 := by
  have hT := stateF_at_a n hn
  by_cases hT0 : a n = 0
  · have hinit : initF n = onesF n := by simpa [stateF, hT0] using hT
    have hn1 : n = 1 := by
      have h00 : initF n 0 = onesF n 0 := by rw [hinit]
      simp [initF, onesF] at h00
      rwa [if_pos (Nat.pos_of_ne_zero hn)] at h00
    subst hn1
    simp [extraPos, hT0]
  · set T := a n
    have hTpos : 0 < T := by omega
    have hprev : stateF n (T - 1) ≠ onesF n :=
      stateF_before_a n hn (Nat.sub_one_lt_of_lt hTpos)
    have hnext : stateF n (T - 1 + 1) = onesF n := by
      convert hT; omega
    obtain ⟨hLn, h2, htail⟩ := last_step_shape n (T - 1) hn hprev hnext
    have hq : leadState n (T - 1) ≤ extraPos n (T - 1) + 1 :=
      extra_ge_lead n (T - 1) hn hprev
    have hun : ∀ s < T - 1, stateF n s ≠ onesF n :=
      fun s hs => stateF_before_a n hn (lt_trans hs (Nat.sub_one_lt_of_lt hTpos))
    have hpbound : extraPos n (T - 1) < n := extraPos_lt n (T - 1) hn hun
    have hn2 : 2 ≤ n := by
      have h0 : stateF n 0 ≠ onesF n :=
        stateF_before_a n hn (by omega)
      have : n ≠ 1 := by
        intro hn1
        apply h0
        ext i; cases i <;> simp [stateF, initF, onesF, hn1]
      omega
    have hLeq : leadState n (T - 1) = n - 2 := by omega
    have hpge : n - 3 ≤ extraPos n (T - 1) := by
      have : n - 2 ≤ extraPos n (T - 1) + 1 := by
        rwa [hLeq] at hq
      omega
    have hTeq : extraPos n T = extraPos n (T - 1 + 1) := by
      congr 1; omega
    rw [hTeq, extraPos_succ]
    set p := extraPos n (T - 1)
    split_ifs with hodd
    · have hodd' : stateF n (T - 1) p % 2 = 1 := by
        simpa [stateF, p] using hodd
      have hp_ne_mid : p ≠ n - 2 := by
        intro hp
        have hval : stateF n (T - 1) p = 2 := by rw [hp, ← hLeq]; exact h2
        rw [hval] at hodd'
        exact absurd hodd' (by decide)
      have hp_ne_end : p ≠ n - 1 := by
        intro hp
        have : leadState n (T - 1) < p := by omega
        have hval : stateF n (T - 1) p = 0 := htail p this
        rw [hval] at hodd'
        exact absurd hodd' (by decide)
      have : p = n - 3 := by omega
      refine Or.inr ⟨hn2, ?_⟩
      omega
    · have heven : stateF n (T - 1) p % 2 ≠ 1 := by
        simpa [stateF, p] using hodd
      have : p = n - 2 ∨ p = n - 1 := by
        by_contra hne
        push_neg at hne
        have : p < leadState n (T - 1) := by omega
        have hval : stateF n (T - 1) p = 1 := leadState_prefix n (T - 1) p this
        rw [hval] at heven
        exact heven (by decide)
      rcases this with h | h
      · exact Or.inr ⟨hn2, h⟩
      · exact Or.inl h

lemma addAt_ones_ne (n p : ℕ) (hn : n ≠ 0) (hp : p < n) :
    addAt (onesF n) p ≠ onesF (n + 1) := by
  intro h
  have : addAt (onesF n) p n = 1 := by
    rw [h]; simp [onesF]
  simp [addAt, onesF] at this
  omega

lemma step_addAt_ones_pred (n : ℕ) (hn : n ≠ 0) :
    stepF (addAt (onesF n) (n - 1)) = onesF (n + 1) := by
  have hcell : onesF n (n - 1) = 1 := by simp [onesF]; omega
  have hodd : onesF n (n - 1) % 2 = 1 := by omega
  rw [stepF_addAt, if_pos hodd, onesF_step]
  funext i
  simp [addAt, onesF]
  split_ifs <;> omega

lemma step_addAt_ones_pred2 (n : ℕ) (hn : 2 ≤ n) :
    stepF (addAt (onesF n) (n - 2)) = addAt (onesF n) (n - 1) := by
  have hcell : onesF n (n - 2) = 1 := by simp [onesF]; omega
  have hodd : onesF n (n - 2) % 2 = 1 := by omega
  rw [stepF_addAt, if_pos hodd, onesF_step]
  congr 1
  omega

lemma stateF_succ_ne_ones_before (n t : ℕ) (hn : n ≠ 0)
    (hnot : stateF n t ≠ onesF n) :
    stateF (n + 1) t ≠ onesF (n + 1) := by
  intro h
  have heq : addAt (stateF n t) (extraPos n t) = onesF (n + 1) := by
    rw [← stateF_addAt, h]
  have hp_lt : extraPos n t < n + 1 := by
    by_contra hge
    have hones : ∀ i < n + 1, stateF n t i = 1 := by
      intro i hi
      have hne : i ≠ extraPos n t := by omega
      have hadd : addAt (stateF n t) (extraPos n t) i = 1 := by
        rw [heq]; simp [onesF, hi]
      simpa [addAt, hne] using hadd
    have hn1 : stateF n t n = 1 := hones n (by omega)
    have hn0 : stateF n t n = 0 := stateF_supp_n n t hn n le_rfl
    omega
  have hp0 : stateF n t (extraPos n t) = 0 := by
    have hadd : addAt (stateF n t) (extraPos n t) (extraPos n t) = 1 := by
      rw [heq]; simp [onesF]; omega
    simp [addAt] at hadd; omega
  have hones_else : ∀ i, i ≠ extraPos n t →
      stateF n t i = onesF (n + 1) i := by
    intro i hi
    have : addAt (stateF n t) (extraPos n t) i = onesF (n + 1) i := by rw [heq]
    simpa [addAt, hi] using this
  have hni := iterate_noInternalZero n t hn
  by_cases hpn : extraPos n t = n
  · have : stateF n t = onesF n := by
      funext i
      by_cases hi : i < n
      · have hne : i ≠ extraPos n t := by omega
        have hi' : i < n + 1 := by omega
        have := hones_else i hne
        simp [onesF, hi'] at this
        simp [onesF, hi, this]
      · simp [onesF, hi, stateF_supp_n n t hn i (by omega)]
    exact hnot this
  · have hplt : extraPos n t < n := by omega
    have hnext : stateF n t (extraPos n t + 1) ≠ 0 := by
      have hne : extraPos n t + 1 ≠ extraPos n t := by omega
      have hlt : extraPos n t + 1 < n + 1 := by omega
      have := hones_else (extraPos n t + 1) hne
      simp [onesF, hlt] at this
      omega
    exact hni (extraPos n t) hnext hp0

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n + 1 ≠ 0 := by omega
  have hT := stateF_at_a n hn0
  have hextra := extraPos_at_a n hn0
  have hrel : stateF (n + 1) (a n) = addAt (onesF n) (extraPos n (a n)) := by
    rw [stateF_addAt, hT]
  have hne_at_T : stateF (n + 1) (a n) ≠ onesF (n + 1) := by
    rw [hrel]
    rcases hextra with h | ⟨_, h⟩
    · rw [h]; exact addAt_ones_ne n (n - 1) hn0 (by omega)
    · rw [h]; exact addAt_ones_ne n (n - 2) hn0 (by omega)
  have hbefore : ∀ t ≤ a n, stateF (n + 1) t ≠ onesF (n + 1) := by
    intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact stateF_succ_ne_ones_before n t hn0 (stateF_before_a n hn0 hlt)
    · exact hne_at_T
  have hstab : ∀ t, stateF (n + 1) t = onesF (n + 1) ↔ a (n + 1) ≤ t := by
    intro t
    constructor
    · intro h
      rw [a_eq_sInf_state (n + 1) hn1]
      exact Nat.sInf_le h
    · intro h
      have hmem := stateF_at_a (n + 1) hn1
      have : a (n + 1) + (t - a (n + 1)) = t := by omega
      rw [← this]
      -- ones is a fixed point, so it stays
      have hfix : ∀ k, stateF (n + 1) (a (n + 1) + k) = onesF (n + 1) := by
        intro k
        induction k with
        | zero => simpa using hmem
        | succ k ih =>
          rw [show a (n + 1) + (k + 1) = a (n + 1) + k + 1 from (Nat.add_assoc _ _ _).symm]
          rw [stateF_succ, ih, onesF_step]
      simpa using hfix (t - a (n + 1))
  rcases hextra with hp1 | ⟨hn2, hp2⟩
  · left
    have hstep : stateF (n + 1) (a n + 1) = onesF (n + 1) := by
      rw [stateF_succ, hrel, hp1, step_addAt_ones_pred n hn0]
    have hge : a (n + 1) ≤ a n + 1 := (hstab (a n + 1)).mp hstep
    have hgt : a n < a (n + 1) := by
      by_contra hle
      exact hbefore (a (n + 1)) (by omega) ((hstab (a (n + 1))).mpr le_rfl)
    omega
  · right
    have hstep1 : stateF (n + 1) (a n + 1) = addAt (onesF n) (n - 1) := by
      rw [stateF_succ, hrel, hp2, step_addAt_ones_pred2 n hn2]
    have hstep2 : stateF (n + 1) (a n + 2) = onesF (n + 1) := by
      rw [show a n + 2 = (a n + 1) + 1 from rfl, stateF_succ, hstep1,
          step_addAt_ones_pred n hn0]
    have hge : a (n + 1) ≤ a n + 2 := (hstab (a n + 2)).mp hstep2
    have hne1 : stateF (n + 1) (a n + 1) ≠ onesF (n + 1) := by
      rw [hstep1]
      exact addAt_ones_ne n (n - 1) hn0 (by omega)
    have hgt : a n + 1 < a (n + 1) := by
      by_contra hle
      have : a (n + 1) ≤ a n + 1 := by omega
      have : a (n + 1) ≤ a n ∨ a (n + 1) = a n + 1 := by omega
      rcases this with hle' | heq
      · exact hbefore (a (n + 1)) (by omega) ((hstab (a (n + 1))).mpr le_rfl)
      · exact hne1 ((hstab (a n + 1)).mpr (by omega))
    omega


