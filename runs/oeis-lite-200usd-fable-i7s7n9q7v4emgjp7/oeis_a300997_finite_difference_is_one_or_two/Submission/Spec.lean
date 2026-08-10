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

/-- Function-level CA step: each cell keeps `⌈m/2⌉` and receives `⌊m'/2⌋` from its
left neighbour. -/
def stepF (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => (f 0 + 1) / 2
  | i + 1 => (f (i + 1) + 1) / 2 + f i / 2

/-- Evolution from a single block of mass `n` at the origin. -/
def evolve (n : ℕ) : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 0 then n else 0
  | t + 1 => stepF (evolve n t)

/-- The stable target configuration: `n` ones. -/
def targetF (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

/-- The position of the extra grain in the coupling of system `n+1` over system `n`. -/
def grain (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => grain n t + evolve n t (grain n t) % 2

/-- Add one unit of mass at position `s`. -/
def addGrain (f : ℕ → ℕ) (s : ℕ) : ℕ → ℕ := fun i => f i + if i = s then 1 else 0

/-- One-step coupling: stepping a configuration with one extra grain at `s` gives the
step of the configuration with the grain at `s` (if the mass under it is even) or `s+1`
(if odd). -/
lemma stepF_addGrain (f : ℕ → ℕ) (s : ℕ) :
    stepF (addGrain f s) = addGrain (stepF f) (s + f s % 2) := by
  funext i
  cases i with
  | zero =>
    show (addGrain f s 0 + 1) / 2 = (f 0 + 1) / 2 + _
    unfold addGrain
    rcases eq_or_ne s 0 with rfl | hs
    · simp only [reduceIte]
      split_ifs with h <;> omega
    · rw [if_neg (Ne.symm hs), if_neg (by omega)]
      omega
  | succ j =>
    show (addGrain f s (j+1) + 1) / 2 + addGrain f s j / 2
        = ((f (j+1) + 1) / 2 + f j / 2) + _
    unfold addGrain
    rcases eq_or_ne (j+1) s with rfl | h1
    · rw [if_pos rfl, if_neg (by omega)]
      split_ifs with h <;> omega
    · rcases eq_or_ne j s with rfl | h2
      · rw [if_neg h1, if_pos rfl]
        split_ifs with h <;> omega
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]
        omega

/-- The coupling: system `n+1` is system `n` plus one grain. -/
lemma evolve_succ_eq (n : ℕ) : ∀ t, evolve (n + 1) t = addGrain (evolve n t) (grain n t)
  | 0 => by
    funext i
    simp only [evolve, addGrain, grain]
    split_ifs <;> omega
  | t + 1 => by
    show stepF (evolve (n+1) t) = _
    rw [evolve_succ_eq n t, stepF_addGrain]
    rfl

/-- A configuration is hole-free if its support is downward closed. -/
def Holefree (f : ℕ → ℕ) : Prop := ∀ i, f i = 0 → f (i + 1) = 0

lemma holefree_stepF {f : ℕ → ℕ} (hf : Holefree f) : Holefree (stepF f) := by
  intro i h
  cases i with
  | zero =>
    have h0 : f 0 = 0 := by
      have := h; simp only [stepF] at this; omega
    have h1 : f 1 = 0 := hf 0 h0
    show (f 1 + 1) / 2 + f 0 / 2 = 0
    omega
  | succ j =>
    have hj : f (j+1) = 0 ∧ f j ≤ 1 := by
      have := h; simp only [stepF] at this; omega
    have h2 : f (j+2) = 0 := hf (j+1) hj.1
    show (f (j+2) + 1) / 2 + f (j+1) / 2 = 0
    omega

lemma Holefree.zero_from {f : ℕ → ℕ} (hf : Holefree f) {i : ℕ} (h : f i = 0) :
    ∀ j, i ≤ j → f j = 0 := by
  intro j hij
  induction j with
  | zero => exact (Nat.le_zero.mp hij) ▸ h
  | succ k ih =>
    rcases Nat.lt_or_ge i (k+1) with hlt | hge
    · exact hf k (ih (by omega))
    · exact (Nat.le_antisymm hij hge) ▸ h

lemma holefree_evolve (n : ℕ) : ∀ t, Holefree (evolve n t)
  | 0 => by intro i h; simp [evolve]
  | t + 1 => holefree_stepF (holefree_evolve n t)

/-- Support bound: after `t` steps the mass lives in `[0, t]`. -/
lemma evolve_zero_of_lt (n : ℕ) : ∀ t i, t < i → evolve n t i = 0
  | 0, i, h => by simp [evolve]; omega
  | t + 1, i, h => by
    match i, h with
    | i + 1, h =>
      show (evolve n t (i+1) + 1) / 2 + evolve n t i / 2 = 0
      have h1 : evolve n t (i+1) = 0 := evolve_zero_of_lt n t (i+1) (by omega)
      have h2 : evolve n t i = 0 := evolve_zero_of_lt n t i (by omega)
      omega

lemma sum_stepF_aux (f : ℕ → ℕ) : ∀ M : ℕ,
    ∑ i ∈ Finset.range (M + 1), stepF f i
      = (∑ i ∈ Finset.range M, f i) + (f M + 1) / 2
  | 0 => by
    simp [stepF]
  | M + 1 => by
    rw [Finset.sum_range_succ (f := stepF f), sum_stepF_aux f M,
      Finset.sum_range_succ (f := f)]
    have : stepF f (M + 1) = (f (M+1) + 1) / 2 + f M / 2 := rfl
    rw [this]
    omega

lemma sum_stepF (f : ℕ → ℕ) (M : ℕ) (hM : f M = 0) :
    ∑ i ∈ Finset.range (M + 1), stepF f i = ∑ i ∈ Finset.range M, f i := by
  rw [sum_stepF_aux f M, hM]
  simp

/-- Mass conservation. -/
lemma mass_evolve (n : ℕ) : ∀ t M, t < M → ∑ i ∈ Finset.range M, evolve n t i = n := by
  intro t
  induction t with
  | zero =>
    intro M hM
    have h0 : (0 : ℕ) ∈ Finset.range M := Finset.mem_range.mpr hM
    rw [show (evolve n 0) = fun i => if i = 0 then n else 0 from rfl]
    rw [Finset.sum_ite_eq' (Finset.range M) 0 (fun _ => n)]
    simp [h0]
  | succ t ih =>
    intro M hM
    match M, hM with
    | M + 1, hM =>
      show ∑ i ∈ Finset.range (M+1), stepF (evolve n t) i = n
      rw [sum_stepF _ M (evolve_zero_of_lt n t M (by omega))]
      exact ih M (by omega)

/-- The target is a fixed point. -/
lemma stepF_targetF (n : ℕ) : stepF (targetF n) = targetF n := by
  funext i
  cases i with
  | zero =>
    show (targetF n 0 + 1) / 2 = targetF n 0
    unfold targetF
    split_ifs <;> omega
  | succ j =>
    show (targetF n (j+1) + 1) / 2 + targetF n j / 2 = targetF n (j+1)
    unfold targetF
    split_ifs <;> omega

lemma target_persist {n t : ℕ} (h : evolve n t = targetF n) :
    ∀ u, t ≤ u → evolve n u = targetF n := by
  intro u hu
  induction u with
  | zero => exact (Nat.le_zero.mp hu) ▸ h
  | succ v ih =>
    rcases Nat.lt_or_ge t (v+1) with hlt | hge
    · show stepF (evolve n v) = targetF n
      rw [ih (by omega), stepF_targetF]
    · exact (Nat.le_antisymm hu hge) ▸ h

/-- If the grain has reached position `n`, the underlying system has settled. -/
lemma eq_target_of_grain_eq_n {n t : ℕ} (h : grain n t = n) : evolve n t = targetF n := by
  have hc := evolve_succ_eq n t
  rw [h] at hc
  have hhole : Holefree (evolve (n+1) t) := holefree_evolve (n+1) t
  -- every position `< n` has positive mass in system `n+1`, hence in system `n`
  have hpos : ∀ i, i < n → 1 ≤ evolve n t i := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    have hzero : evolve (n+1) t i = 0 := by
      rw [hc]
      show evolve n t i + _ = 0
      rw [if_neg (by omega)]
      omega
    have : evolve (n+1) t n = 0 := hhole.zero_from hzero n (by omega)
    rw [hc] at this
    revert this
    show ¬ (evolve n t n + if n = n then 1 else 0) = 0
    rw [if_pos rfl]
    omega
  -- mass forces all these to be exactly one and the rest zero
  obtain ⟨M, hMt, hMn⟩ : ∃ M, t < M ∧ n < M :=
    ⟨max (t + 1) (n + 1), lt_of_lt_of_le (Nat.lt_succ_self t) (le_max_left _ _),
      lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)⟩
  have hmass : ∑ i ∈ Finset.range M, evolve n t i = n := mass_evolve n t M hMt
  have hone : ∀ i, i < n → evolve n t i = 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₀, hi₀, hne⟩ := hcon
    have h2 : 2 ≤ evolve n t i₀ := by have := hpos i₀ hi₀; omega
    have hsub : Finset.range n ⊆ Finset.range M := by
      exact Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
    have hlt : n < ∑ i ∈ Finset.range n, evolve n t i := by
      have h1 : ∑ i ∈ Finset.range n, (1 : ℕ) < ∑ i ∈ Finset.range n, evolve n t i := by
        apply Finset.sum_lt_sum (fun i hi => hpos i (Finset.mem_range.mp hi))
        exact ⟨i₀, Finset.mem_range.mpr hi₀, h2⟩
      simpa using h1
    have hle : ∑ i ∈ Finset.range n, evolve n t i ≤ ∑ i ∈ Finset.range M, evolve n t i :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hzero : ∀ i, n ≤ i → evolve n t i = 0 := by
    intro i hi
    rcases Nat.lt_or_ge i M with hiM | hiM
    · -- sum over [n, M) is zero
      have hsplit : ∑ i ∈ Finset.range M, evolve n t i
          = ∑ i ∈ Finset.range n, evolve n t i + ∑ i ∈ Finset.Ico n M, evolve n t i := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega : n ≤ M)]
      have hsum1 : ∑ i ∈ Finset.range n, evolve n t i = n := by
        rw [Finset.sum_congr rfl (fun i hi => hone i (Finset.mem_range.mp hi))]
        simp
      have : ∑ i ∈ Finset.Ico n M, evolve n t i = 0 := by omega
      have hz := (Finset.sum_eq_zero_iff).mp this
      exact hz i (Finset.mem_Ico.mpr ⟨hi, hiM⟩)
    · exact evolve_zero_of_lt n t i (by omega)
  funext i
  unfold targetF
  split_ifs with hi
  · exact hone i hi
  · exact hzero i (by omega)

lemma grain_le (n : ℕ) : ∀ t, grain n t ≤ n
  | 0 => Nat.zero_le n
  | t + 1 => by
    rcases Nat.lt_or_ge (grain n t) n with hlt | hge
    · show grain n t + evolve n t (grain n t) % 2 ≤ n
      have : evolve n t (grain n t) % 2 ≤ 1 := by omega
      omega
    · have heq : grain n t = n := Nat.le_antisymm (grain_le n t) hge
      show grain n t + evolve n t (grain n t) % 2 ≤ n
      rw [heq, eq_target_of_grain_eq_n heq]
      show n + targetF n n % 2 ≤ n
      unfold targetF
      rw [if_neg (by omega)]
      omega

lemma stepF_eval (f : ℕ → ℕ) (i : ℕ) :
    stepF f i = (f i + 1) / 2 + (if i = 0 then 0 else f (i - 1) / 2) := by
  cases i with
  | zero => simp [stepF]
  | succ j => simp [stepF]

/-- If mass one everywhere below `n`, the configuration is the target. -/
lemma eq_target_of_ones {n t : ℕ} (h : ∀ i, i < n → evolve n t i = 1) :
    evolve n t = targetF n := by
  obtain ⟨M, hMt, hMn⟩ : ∃ M, t < M ∧ n < M :=
    ⟨max (t + 1) (n + 1), lt_of_lt_of_le (Nat.lt_succ_self t) (le_max_left _ _),
      lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)⟩
  have hmass : ∑ i ∈ Finset.range M, evolve n t i = n := mass_evolve n t M hMt
  have hzero : ∀ i, n ≤ i → evolve n t i = 0 := by
    intro i hi
    rcases Nat.lt_or_ge i M with hiM | hiM
    · have hsplit : ∑ i ∈ Finset.range M, evolve n t i
          = ∑ i ∈ Finset.range n, evolve n t i + ∑ i ∈ Finset.Ico n M, evolve n t i := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega : n ≤ M)]
      have hsum1 : ∑ i ∈ Finset.range n, evolve n t i = n := by
        rw [Finset.sum_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))]
        simp
      have hz0 : ∑ i ∈ Finset.Ico n M, evolve n t i = 0 := by omega
      exact (Finset.sum_eq_zero_iff).mp hz0 i (Finset.mem_Ico.mpr ⟨hi, hiM⟩)
    · exact evolve_zero_of_lt n t i (by omega)
  funext i
  unfold targetF
  split_ifs with hi
  · exact h i hi
  · exact hzero i (by omega)

/-- Stepping the configuration `[1^p, 2]` gives `p+2` ones. -/
lemma stepF_block {E : ℕ → ℕ} {p : ℕ}
    (hone : ∀ j, j < p → E j = 1) (hp : E p = 2) (hzero : ∀ j, p + 1 ≤ j → E j = 0) :
    stepF E = targetF (p + 2) := by
  funext i
  rw [stepF_eval]
  unfold targetF
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, if_pos (by omega)]
    rcases Nat.eq_zero_or_pos p with hp0 | hpp
    · have h2 : E 0 = 2 := hp0 ▸ hp
      omega
    · have h1 : E 0 = 1 := hone 0 hpp
      omega
  · rw [if_neg h0]
    rcases Nat.lt_or_ge i p with hip | hip
    · have e1 : E i = 1 := hone i hip
      have e2 : E (i - 1) = 1 := hone _ (by omega)
      rw [if_pos (by omega)]
      omega
    · rcases Nat.eq_or_lt_of_le hip with heq | hgt
      · -- i = p
        have e1 : E i = 2 := heq ▸ hp
        have e2 : E (i - 1) = 1 := hone _ (by omega)
        rw [if_pos (by omega)]
        omega
      · rcases Nat.eq_or_lt_of_le hgt with heq1 | hgt1
        · -- i = p + 1
          have e1 : E i = 0 := hzero i (by omega)
          have e2 : E (i - 1) = 2 := by
            have : i - 1 = p := by omega
            rw [this]; exact hp
          rw [if_pos (by omega)]
          omega
        · -- i ≥ p + 2
          have e1 : E i = 0 := hzero i (by omega)
          have e2 : E (i - 1) = 0 := hzero _ (by omega)
          rw [if_neg (by omega)]
          omega

/-- The key invariant: at any time, either the system has settled, or there is a
non-one cell within distance one to the right of the grain. -/
lemma inv (n : ℕ) : ∀ t, evolve n t = targetF n ∨ ∃ i, i ≤ grain n t + 1 ∧ evolve n t i ≠ 1 := by
  intro t
  induction t with
  | zero =>
    right
    refine ⟨1, ?_, ?_⟩
    · show 1 ≤ grain n 0 + 1
      omega
    · show (if (1:ℕ) = 0 then n else 0) ≠ 1
      simp
  | succ t ih =>
    rcases ih with hset | ⟨i₀, hi₀, hne⟩
    · left
      show stepF (evolve n t) = targetF n
      rw [hset, stepF_targetF]
    · have hex : ∃ i, evolve n t i ≠ 1 := ⟨i₀, hne⟩
      obtain ⟨p, hpne, hpmin, hple⟩ :
          ∃ p, evolve n t p ≠ 1 ∧ (∀ j, j < p → evolve n t j = 1) ∧ p ≤ grain n t + 1 :=
        ⟨Nat.find hex, Nat.find_spec hex,
          fun j hj => by simpa using Nat.find_min hex hj,
          (Nat.find_min' hex hne).trans hi₀⟩
      have hstep1 : ∀ i, evolve n (t+1) i = stepF (evolve n t) i := fun _ => rfl
      have hg1 : grain n (t+1) = grain n t + evolve n t (grain n t) % 2 := rfl
      rcases Nat.lt_or_ge (evolve n t p) 2 with hlt2 | hge2
      · -- `E p = 0`
        have hp0 : evolve n t p = 0 := by omega
        right
        refine ⟨p, by omega, ?_⟩
        rw [hstep1, stepF_eval]
        split_ifs with h0
        · have : evolve n t p = 0 := hp0
          rw [h0] at this
          omega
        · have h1 : evolve n t (p-1) = 1 := hpmin (p-1) (by omega)
          omega
      · rcases Nat.lt_or_ge (evolve n t p) 3 with hlt3 | hge3
        · -- `E p = 2`
          have hp2 : evolve n t p = 2 := by omega
          by_cases hnext : evolve n t (p+1) = 0
          · -- the configuration is `[1^p, 2]`; it settles in one step
            left
            have hzero : ∀ j, p + 1 ≤ j → evolve n t j = 0 :=
              (holefree_evolve n t).zero_from hnext
            -- mass gives `n = p + 2`
            obtain ⟨M, hMt, hMp⟩ : ∃ M, t < M ∧ p + 2 < M :=
              ⟨max (t + 1) (p + 3), lt_of_lt_of_le (Nat.lt_succ_self t) (le_max_left _ _),
                lt_of_lt_of_le (by omega) (le_max_right _ _)⟩
            have hmass : ∑ i ∈ Finset.range M, evolve n t i = n := mass_evolve n t M hMt
            have h1 : ∑ i ∈ Finset.range (p+2), evolve n t i
                = ∑ i ∈ Finset.range M, evolve n t i := by
              apply Finset.sum_subset
                (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
              intro x _ hx
              have := Finset.mem_range.not.mp hx
              exact hzero x (by omega)
            have h2 : ∑ i ∈ Finset.range (p+2), evolve n t i = p + 2 := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
              have hsump : ∑ i ∈ Finset.range p, evolve n t i = p := by
                rw [Finset.sum_congr rfl (fun j hj => hpmin j (Finset.mem_range.mp hj))]
                simp
              rw [hsump, hp2, hnext]
            have hn : n = p + 2 := by omega
            show stepF (evolve n t) = targetF n
            rw [show targetF n = targetF (p + 2) from by rw [hn]]
            exact stepF_block hpmin hp2 hzero
          · right
            have hnext1 : 1 ≤ evolve n t (p+1) := by omega
            refine ⟨p+1, ?_, ?_⟩
            · -- `p + 1 ≤ grain (t+1) + 1`
              rcases Nat.lt_or_ge (grain n t) p with hsp | hsp
              · have h1 : evolve n t (grain n t) = 1 := hpmin _ (by omega)
                rw [hg1, h1]
                omega
              · rw [hg1]
                omega
            · rw [hstep1, stepF_eval]
              rw [if_neg (by omega : ¬ (p + 1 = 0))]
              have hs : p + 1 - 1 = p := by omega
              rw [hs, hp2]
              omega
        · -- `E p ≥ 3`
          right
          refine ⟨p, by omega, ?_⟩
          rw [hstep1, stepF_eval]
          split_ifs with h0 <;> omega

/-- The unique non-settled predecessor of the target is `[1^(n-2), 2]`. -/
lemma predecessor {n : ℕ} (hn : 2 ≤ n) {t : ℕ}
    (hstep : evolve n (t+1) = targetF n) (hne : evolve n t ≠ targetF n) :
    (∀ i, i + 2 < n → evolve n t i = 1) ∧ evolve n t (n - 2) = 2 ∧
      (∀ i, n - 2 < i → evolve n t i = 0) := by
  have hhole := holefree_evolve n t
  obtain ⟨M, hMt, hMn⟩ : ∃ M, t < M ∧ n < M :=
    ⟨max (t + 1) (n + 1), lt_of_lt_of_le (Nat.lt_succ_self t) (le_max_left _ _),
      lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)⟩
  have hmass : ∑ i ∈ Finset.range M, evolve n t i = n := mass_evolve n t M hMt
  have hstepi : ∀ i, stepF (evolve n t) i = targetF n i := fun i => congrFun hstep i
  have hex : ∃ i, evolve n t i ≠ 1 := ⟨M, by rw [evolve_zero_of_lt n t M hMt]; omega⟩
  obtain ⟨k, hkne, hkmin⟩ :
      ∃ k, evolve n t k ≠ 1 ∧ (∀ j, j < k → evolve n t j = 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => by simpa using Nat.find_min hex hj⟩
  have hkn : k < n := by
    by_contra hcon
    push_neg at hcon
    exact hne (eq_target_of_ones (fun i hi => hkmin i (by omega)))
  have hk2 : 2 ≤ evolve n t k := by
    rcases Nat.lt_or_ge (evolve n t k) 2 with h2 | h2
    · exfalso
      have hk0 : evolve n t k = 0 := by omega
      have hz : ∀ j, k ≤ j → evolve n t j = 0 := hhole.zero_from hk0
      have h1 : ∑ i ∈ Finset.range k, evolve n t i
          = ∑ i ∈ Finset.range M, evolve n t i := by
        apply Finset.sum_subset
          (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
        intro x _ hx
        exact hz x (by simpa using Finset.mem_range.not.mp hx)
      have h2' : ∑ i ∈ Finset.range k, evolve n t i = k := by
        rw [Finset.sum_congr rfl (fun j hj => hkmin j (Finset.mem_range.mp hj))]
        simp
      omega
    · exact h2
  have hkn2 : k + 1 < n := by
    by_contra hcon
    push_neg at hcon
    have hk_eq : k = n - 1 := by omega
    have h0 : stepF (evolve n t) n = 0 := by
      rw [hstepi n]
      unfold targetF
      rw [if_neg (by omega)]
    rw [stepF_eval] at h0
    rw [if_neg (by omega : ¬ (n = 0))] at h0
    have : n - 1 = k := by omega
    rw [this] at h0
    omega
  have hkval : evolve n t k = 2 := by
    have h1 : stepF (evolve n t) k = 1 := by
      rw [hstepi k]
      unfold targetF
      rw [if_pos (by omega)]
    rw [stepF_eval] at h1
    split_ifs at h1 with hk0
    · omega
    · have hprev : evolve n t (k-1) = 1 := hkmin (k-1) (by omega)
      omega
  have hk10 : evolve n t (k+1) = 0 := by
    have h1 : stepF (evolve n t) (k+1) = 1 := by
      rw [hstepi (k+1)]
      unfold targetF
      rw [if_pos (by omega)]
    rw [stepF_eval] at h1
    rw [if_neg (by omega : ¬ (k + 1 = 0))] at h1
    have hs : k + 1 - 1 = k := by omega
    rw [hs, hkval] at h1
    omega
  have hbeyond : ∀ j, k + 1 ≤ j → evolve n t j = 0 := hhole.zero_from hk10
  have hsum : n = k + 2 := by
    have h1 : ∑ i ∈ Finset.range (k+1), evolve n t i
        = ∑ i ∈ Finset.range M, evolve n t i := by
      apply Finset.sum_subset
        (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
      intro x _ hx
      exact hbeyond x (by simpa using Finset.mem_range.not.mp hx)
    have h2 : ∑ i ∈ Finset.range (k+1), evolve n t i = k + 2 := by
      rw [Finset.sum_range_succ]
      have hsump : ∑ i ∈ Finset.range k, evolve n t i = k := by
        rw [Finset.sum_congr rfl (fun j hj => hkmin j (Finset.mem_range.mp hj))]
        simp
      rw [hsump, hkval]
    omega
  refine ⟨fun i hi => hkmin i (by omega), ?_, fun i hi => hbeyond i (by omega)⟩
  have : n - 2 = k := by omega
  rw [this]
  exact hkval

/-- The set of times at which system `n` has settled. -/
def Stab (n : ℕ) : Set ℕ := {t | evolve n t = targetF n}

lemma stab_one : (0 : ℕ) ∈ Stab 1 := by
  show evolve 1 0 = targetF 1
  funext i
  show (if i = 0 then 1 else 0) = if i < 1 then 1 else 0
  split_ifs <;> omega

/-- System `n+1` has settled iff system `n` has settled and the grain is at `n`. -/
lemma mem_stab_char (n u : ℕ) :
    u ∈ Stab (n+1) ↔ (evolve n u = targetF n ∧ grain n u = n) := by
  constructor
  · intro hu
    have hc : addGrain (evolve n u) (grain n u) = targetF (n+1) := by
      rw [← evolve_succ_eq]; exact hu
    have hsle : grain n u ≤ n := grain_le n u
    have hEs : evolve n u (grain n u) = 0 := by
      have h := congrFun hc (grain n u)
      unfold addGrain targetF at h
      rw [if_pos rfl, if_pos (by omega)] at h
      omega
    have hsn : grain n u = n := by
      by_contra hne'
      have hlt : grain n u < n := by omega
      have hEn : evolve n u n = 1 := by
        have h := congrFun hc n
        unfold addGrain targetF at h
        rw [if_neg (by omega), if_pos (by omega)] at h
        omega
      have := (holefree_evolve n u).zero_from hEs n (by omega)
      omega
    exact ⟨eq_target_of_grain_eq_n hsn, hsn⟩
  · rintro ⟨h1, h2⟩
    show evolve (n+1) u = targetF (n+1)
    rw [evolve_succ_eq, h1, h2]
    funext i
    unfold addGrain targetF
    split_ifs <;> omega

/-- The key step: if system `n` settles, so does system `n+1`, exactly one or two
steps later. -/
lemma key {n : ℕ} (hn : 1 ≤ n) (hne : (Stab n).Nonempty) :
    (Stab (n+1)).Nonempty ∧
      (sInf (Stab (n+1)) = sInf (Stab n) + 1 ∨ sInf (Stab (n+1)) = sInf (Stab n) + 2) := by
  obtain ⟨T, hTdef⟩ : ∃ T, T = sInf (Stab n) := ⟨_, rfl⟩
  have hT : evolve n T = targetF n := by
    rw [hTdef]; exact Nat.sInf_mem hne
  have hTmin : ∀ u, u < T → evolve n u ≠ targetF n := by
    intro u hu hcon
    have : sInf (Stab n) ≤ u := Nat.sInf_le hcon
    omega
  have hgle : grain n T ≤ n := grain_le n T
  -- the grain is at `n-1` or `n-2` at the settling time
  have hgrain : grain n T + 1 = n ∨ grain n T + 2 = n := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- n = 1
      have hn1 : n = 1 := by omega
      subst hn1
      have hT0 : T = 0 := by
        have h0 := Nat.sInf_le stab_one
        omega
      subst hT0
      left
      rfl
    · -- n ≥ 2
      have hT1 : T ≠ 0 := by
        intro h0
        subst h0
        have h := congrFun hT 1
        show False
        rw [show evolve n 0 1 = 0 from rfl] at h
        unfold targetF at h
        rw [if_pos (by omega)] at h
        omega
      obtain ⟨u, rfl⟩ : ∃ u, T = u + 1 := ⟨T - 1, by omega⟩
      have hdne : evolve n u ≠ targetF n := hTmin u (by omega)
      obtain ⟨h1, h2', h3⟩ := predecessor h2 hT hdne
      have hs_le : grain n u ≤ n := grain_le n u
      have hs_ne : grain n u ≠ n := fun h => hdne (eq_target_of_grain_eq_n h)
      rcases inv n u with hcon | ⟨i, hi_le, hi_ne⟩
      · exact absurd hcon hdne
      have hi_ge : ¬ (i + 2 < n) := fun h => hi_ne (h1 i h)
      have hg_succ : grain n (u+1) = grain n u + evolve n u (grain n u) % 2 := rfl
      rcases (by omega : grain n u + 1 = n ∨ grain n u + 2 = n ∨ grain n u + 3 = n)
        with hc | hc | hc
      · have hE : evolve n u (grain n u) = 0 := h3 _ (by omega)
        left
        rw [hg_succ, hE]
        omega
      · have hE : evolve n u (grain n u) = 2 := by
          have hh : grain n u = n - 2 := by omega
          rw [hh]; exact h2'
        right
        rw [hg_succ, hE]
        omega
      · have hE : evolve n u (grain n u) = 1 := h1 _ (by omega)
        right
        rw [hg_succ, hE]
        omega
  -- after settling, the grain walks right at unit speed
  have hrun : ∀ j, grain n T + j ≤ n →
      evolve n (T + j) = targetF n ∧ grain n (T + j) = grain n T + j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hT, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨ha, hb⟩ := ih (by omega)
      constructor
      · show stepF (evolve n (T + j)) = targetF n
        rw [ha, stepF_targetF]
      · show grain n (T + j) + evolve n (T + j) (grain n (T + j)) % 2 = grain n T + (j + 1)
        rw [ha, hb]
        show grain n T + j + targetF n (grain n T + j) % 2 = _
        unfold targetF
        rw [if_pos (by omega)]
        omega
  obtain ⟨j0, hj0⟩ : ∃ j0, grain n T + j0 = n := ⟨n - grain n T, by omega⟩
  have hj012 : j0 = 1 ∨ j0 = 2 := by omega
  have hmem : (T + j0) ∈ Stab (n+1) := by
    rw [mem_stab_char]
    obtain ⟨ha, hb⟩ := hrun j0 (by omega)
    exact ⟨ha, by omega⟩
  have hlow : ∀ u, u < T + j0 → u ∉ Stab (n+1) := by
    intro u hu hmem'
    obtain ⟨ha, hb⟩ := (mem_stab_char n u).mp hmem'
    rcases Nat.lt_or_ge u T with h | h
    · exact hTmin u h ha
    · obtain ⟨j, rfl⟩ : ∃ j, u = T + j := ⟨u - T, by omega⟩
      have := (hrun j (by omega)).2
      omega
  refine ⟨⟨T + j0, hmem⟩, ?_⟩
  have heq : sInf (Stab (n+1)) = T + j0 := by
    apply le_antisymm (Nat.sInf_le hmem)
    by_contra hcon
    push_neg at hcon
    exact hlow _ hcon (Nat.sInf_mem ⟨T + j0, hmem⟩)
  rw [heq, ← hTdef]
  omega

lemma stab_nonempty : ∀ n, 1 ≤ n → (Stab n).Nonempty := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, stab_one⟩
    · exact (key hm (ih hm)).1

theorem main_evolve (n : ℕ) (hn : 1 ≤ n) :
    sInf (Stab (n+1)) = sInf (Stab n) + 1 ∨ sInf (Stab (n+1)) = sInf (Stab n) + 2 :=
  (key hn (stab_nonempty n hn)).2

/-! ### Transfer to the list-level definition -/

/-- Mirror of the list-level step function used in the definition of `a`. -/
def caStep (config : List ℕ) : List ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  (List.reverse next_config_long).dropWhile (fun x => x = 0) |>.reverse

/-- Mirror of the list-level evolution used in the definition of `a`. -/
def SL (n : ℕ) (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => caStep acc) [n]

lemma getD_replicate_zero : ∀ (k i : ℕ), (List.replicate k (0:ℕ)).getD i 0 = 0
  | 0, i => by simp
  | k + 1, 0 => by simp [List.replicate]
  | k + 1, i + 1 => by
    show (List.replicate k (0:ℕ)).getD i 0 = 0
    exact getD_replicate_zero k i

lemma getD_append_replicate_zero : ∀ (t : List ℕ) (k i : ℕ),
    (t ++ List.replicate k 0).getD i 0 = t.getD i 0
  | [], k, i => by
    simp only [List.nil_append]
    rw [getD_replicate_zero]
    simp
  | x :: t, k, 0 => by simp
  | x :: t, k, i + 1 => by
    show ((t ++ List.replicate k 0)).getD i 0 = t.getD i 0
    exact getD_append_replicate_zero t k i

/-- Removing trailing zeros does not change `getD · 0`. -/
lemma getD_trim (l : List ℕ) (i : ℕ) :
    ((l.reverse.dropWhile (fun x => x = 0)).reverse).getD i 0 = l.getD i 0 := by
  have hsplit : l.reverse.takeWhile (fun x => x = 0) ++ l.reverse.dropWhile (fun x => x = 0)
      = l.reverse := List.takeWhile_append_dropWhile
  have htake : l.reverse.takeWhile (fun x => x = 0)
      = List.replicate (l.reverse.takeWhile (fun x => x = 0)).length 0 := by
    rw [List.eq_replicate_iff]
    exact ⟨rfl, fun b hb => by simpa using List.mem_takeWhile_imp hb⟩
  have hl : l = (l.reverse.dropWhile (fun x => x = 0)).reverse
      ++ List.replicate (l.reverse.takeWhile (fun x => x = 0)).length 0 := by
    conv_lhs => rw [← List.reverse_reverse l, ← hsplit]
    rw [List.reverse_append, htake, List.reverse_replicate, List.length_replicate]
  conv_rhs => rw [hl]
  rw [getD_append_replicate_zero]

/-- A list has no trailing zero. -/
def NoTrail (l : List ℕ) : Prop := ∀ x ∈ l.getLast?, x ≠ 0

lemma noTrail_trim (l : List ℕ) :
    NoTrail ((l.reverse.dropWhile (fun x => x = 0)).reverse) := by
  intro x hx
  rw [List.getLast?_reverse] at hx
  have hne : l.reverse.dropWhile (fun x => decide (x = 0)) ≠ [] := by
    intro h
    rw [h] at hx
    simp at hx
  rw [List.head?_eq_some_head hne] at hx
  have hhead := List.head_dropWhile_not (fun x : ℕ => decide (x = 0)) hne
  simp only [Option.mem_def, Option.some.injEq] at hx
  subst hx
  simpa using hhead

lemma getD_zipWith_add : ∀ (xs ys : List ℕ), xs.length = ys.length → ∀ i,
    (List.zipWith Nat.add xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0
  | [], [], _, i => by simp
  | [], y :: ys, h, i => by simp at h
  | x :: xs, [], h, i => by simp at h
  | x :: xs, y :: ys, h, 0 => by simp [List.zipWith]
  | x :: xs, y :: ys, h, i + 1 => by
    show (List.zipWith Nat.add xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0
    exact getD_zipWith_add xs ys (by simpa using h) i

lemma getD_base : ∀ (l : List ℕ) (i : ℕ),
    (l.map (fun m => (m + 1) / 2) ++ [0]).getD i 0 = (l.getD i 0 + 1) / 2
  | [], 0 => by simp
  | [], i + 1 => by simp
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by
    show ((l.map (fun m => (m + 1) / 2) ++ [0])).getD i 0 = (l.getD i 0 + 1) / 2
    exact getD_base l i

lemma getD_map_div : ∀ (l : List ℕ) (i : ℕ),
    (l.map (fun m => m / 2)).getD i 0 = l.getD i 0 / 2
  | [], i => by simp
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by
    show (l.map (fun m => m / 2)).getD i 0 = l.getD i 0 / 2
    exact getD_map_div l i

lemma getD_caStep (l : List ℕ) (i : ℕ) :
    (caStep l).getD i 0 = stepF (fun j => l.getD j 0) i := by
  show ((List.zipWith Nat.add (l.map (fun m => (m + 1) / 2) ++ [0])
      (0 :: l.map (fun m => m / 2))).reverse.dropWhile (fun x => x = 0)).reverse.getD i 0 = _
  rw [getD_trim]
  rw [getD_zipWith_add _ _ (by simp)]
  rw [getD_base]
  rw [stepF_eval]
  congr 1
  cases i with
  | zero => simp
  | succ j =>
    show (l.map (fun m => m / 2)).getD j 0 = _
    rw [getD_map_div]
    simp

lemma SL_succ (n t : ℕ) : SL n (t + 1) = caStep (SL n t) := by
  unfold SL
  rw [List.range_succ, List.foldl_append]
  rfl

lemma getD_SL (n : ℕ) : ∀ t i, (SL n t).getD i 0 = evolve n t i
  | 0, 0 => rfl
  | 0, i + 1 => by
    show (0:ℕ) = evolve n 0 (i + 1)
    show (0:ℕ) = if i + 1 = 0 then n else 0
    rw [if_neg (by omega)]
  | t + 1, i => by
    rw [SL_succ, getD_caStep]
    show stepF (fun j => (SL n t).getD j 0) i = stepF (evolve n t) i
    have h : (fun j => (SL n t).getD j 0) = evolve n t := funext (getD_SL n t)
    rw [h]

lemma noTrail_SL (n : ℕ) (hn : n ≠ 0) : ∀ t, NoTrail (SL n t)
  | 0 => by
    intro x hx
    simp only [SL, List.range_zero, List.foldl_nil, List.getLast?_singleton,
      Option.mem_def, Option.some.injEq] at hx
    omega
  | t + 1 => by
    rw [SL_succ]
    exact noTrail_trim _

lemma getD_replicate_one (n : ℕ) : ∀ i, (List.replicate n (1:ℕ)).getD i 0 = targetF n i := by
  induction n with
  | zero =>
    intro i
    show ([] : List ℕ).getD i 0 = targetF 0 i
    unfold targetF
    rw [if_neg (by omega)]
    simp
  | succ m ih =>
    intro i
    cases i with
    | zero =>
      show (1 :: List.replicate m (1:ℕ)).getD 0 0 = targetF (m+1) 0
      unfold targetF
      rw [if_pos (by omega)]
      rfl
    | succ j =>
      show (List.replicate m (1:ℕ)).getD j 0 = targetF (m+1) (j+1)
      rw [ih j]
      unfold targetF
      split_ifs <;> omega

lemma SL_eq_replicate_iff (n k : ℕ) (hn : 1 ≤ n) :
    SL n k = List.replicate n 1 ↔ evolve n k = targetF n := by
  constructor
  · intro h
    funext i
    rw [← getD_SL n k i, h, getD_replicate_one]
  · intro h
    have hgd : ∀ i, (SL n k).getD i 0 = targetF n i :=
      fun i => (getD_SL n k i).trans (congrFun h i)
    have hnt := noTrail_SL n (by omega) k
    have hlen : (SL n k).length = n := by
      rcases Nat.lt_trichotomy (SL n k).length n with hl | hl | hl
      · exfalso
        have h1 := hgd (n - 1)
        rw [List.getD_eq_default _ _ (by omega)] at h1
        unfold targetF at h1
        rw [if_pos (by omega)] at h1
        omega
      · exact hl
      · exfalso
        have hlpos : 0 < (SL n k).length := by omega
        have hgetl : (SL n k).getLast? = some ((SL n k)[(SL n k).length - 1]) := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        have h0 : (SL n k)[(SL n k).length - 1] ≠ 0 := by
          apply hnt
          rw [hgetl]
          rfl
        have h1 := hgd ((SL n k).length - 1)
        rw [List.getD_eq_getElem _ _ (by omega)] at h1
        unfold targetF at h1
        rw [if_neg (by omega)] at h1
        exact h0 h1
    apply List.ext_getElem (by rw [hlen, List.length_replicate])
    intro i h1 h2
    have h3 := hgd i
    rw [List.getD_eq_getElem _ _ h1] at h3
    rw [List.getElem_replicate]
    unfold targetF at h3
    rw [if_pos (by rw [hlen] at h1; exact h1)] at h3
    exact h3

/-- Unfolding of the list-level definition of `a`. -/
lemma a_eq (n : ℕ) : a n = if n = 0 then 0 else sInf {k | SL n k = List.replicate n 1} := rfl

lemma a_eq_sInf (n : ℕ) (hn : 1 ≤ n) : a n = sInf (Stab n) := by
  rw [a_eq, if_neg (by omega)]
  congr 1
  ext k
  exact SL_eq_replicate_iff n k hn

end A300997

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  rw [A300997.a_eq_sInf (n + 1) (by omega), A300997.a_eq_sInf n hn]
  exact A300997.main_evolve n hn
