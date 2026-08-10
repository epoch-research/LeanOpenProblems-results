import FormalConjectures.Util.ProblemImports

open List Nat Function Set

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

    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    let stable_steps : Set ℕ := {k | S k = target_config}

    sInf stable_steps

namespace A300997

/-- The cellular-automaton step on functions `ℕ → ℕ`.
`F M i = ⌈M i / 2⌉ + ⌊M (i-1) / 2⌋` where the left-neighbour term is `0` at `i = 0`. -/
def F (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => (M 0 + 1) / 2
  | (i+1) => (M (i+1) + 1) / 2 + M i / 2

/-- Initial state: mass `n` at position `0`. -/
def init (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

/-- Target (stable) state: `1` on positions `< n`, `0` elsewhere. -/
def tgt (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

/-- State after `t` steps of the automaton started with mass `n`. -/
def state (n t : ℕ) : ℕ → ℕ := F^[t] (init n)

@[simp] lemma state_zero (n : ℕ) : state n 0 = init n := rfl

lemma state_succ (n t : ℕ) : state n (t+1) = F (state n t) := by
  simp only [state, Function.iterate_succ_apply']

lemma F_zero (M : ℕ → ℕ) : F M 0 = (M 0 + 1)/2 := rfl
lemma F_succ (M : ℕ → ℕ) (i : ℕ) : F M (i+1) = (M (i+1) + 1)/2 + M i / 2 := rfl

/-- Indicator: mass `1` at position `p`. -/
def e (p : ℕ) : ℕ → ℕ := fun i => if i = p then 1 else 0

@[simp] lemma e_apply (p i : ℕ) : e p i = if i = p then 1 else 0 := rfl

lemma add_apply (M N : ℕ → ℕ) (i : ℕ) : (M + N) i = M i + N i := rfl

/-- The next chip position, given current position `p` and the underlying value `v = M p`. -/
def nextp (v p : ℕ) : ℕ := if v % 2 = 1 then p + 1 else p

/-- **Step 3 core:** adding a unit chip at `p` to `M` and stepping equals stepping `M`
and adding a unit chip at `nextp (M p) p`. -/
lemma F_add_e (M : ℕ → ℕ) (p : ℕ) :
    F (M + e p) = F M + e (nextp (M p) p) := by
  funext i
  simp only [add_apply, nextp, e_apply]
  rcases i with _ | i
  · -- i = 0
    simp only [F_zero, add_apply, e_apply]
    by_cases hp : (0 : ℕ) = p
    · subst hp; simp only [if_pos rfl]
      by_cases hv : M 0 % 2 = 1 <;> simp [hv] <;> omega
    · simp only [if_neg hp]
      by_cases hv : M p % 2 = 1 <;> simp [hv, hp] <;> omega
  · -- i = i+1
    simp only [F_succ, add_apply, e_apply]
    by_cases hv : M p % 2 = 1 <;> simp only [hv, if_true, if_false]
    · -- chip moves to p+1
      by_cases h1 : i + 1 = p
      · by_cases h2 : i = p <;> simp [h1, h2] <;> omega
      · by_cases h2 : i = p <;> simp [h1, h2] <;>
          (first | omega | (subst h2; omega))
    · -- chip stays at p
      by_cases h1 : i + 1 = p
      · by_cases h2 : i = p <;> simp [h1, h2] <;> omega
      · by_cases h2 : i = p <;> simp [h1, h2] <;> omega

/-- Chip position at time `t` for the coupling of systems `n` and `n+1`. -/
def chip (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | (t+1) => nextp (state n t (chip n t)) (chip n t)

@[simp] lemma chip_zero (n : ℕ) : chip n 0 = 0 := rfl
lemma chip_succ (n t : ℕ) : chip n (t+1) = nextp (state n t (chip n t)) (chip n t) := rfl

lemma init_succ_eq (n : ℕ) : init (n+1) = init n + e 0 := by
  funext i; simp only [init, add_apply, e_apply]
  by_cases h : i = 0 <;> simp [h]

/-- **Step 3:** the `(n+1)`-system equals the `n`-system plus one unit chip at `chip n t`. -/
lemma coupling (n t : ℕ) : state (n+1) t = state n t + e (chip n t) := by
  induction t with
  | zero => simp only [state_zero, chip_zero]; exact init_succ_eq n
  | succ t ih =>
    rw [state_succ, ih, F_add_e, state_succ, chip_succ]

/-! ## Support and gaplessness -/

/-- If `M` vanishes from `N` on, then `F M` vanishes from `N+1` on. -/
lemma F_supp {M : ℕ → ℕ} {N : ℕ} (h : ∀ i, N ≤ i → M i = 0) :
    ∀ i, N + 1 ≤ i → F M i = 0 := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [F_succ]
  have h1 : M (j+1) = 0 := h _ (by omega)
  have h2 : M j = 0 := h _ (by omega)
  simp [h1, h2]

/-- The state after `t` steps is supported on `[0, t]`. -/
lemma state_supp (n t : ℕ) : ∀ i, t + 1 ≤ i → state n t i = 0 := by
  induction t with
  | zero =>
    intro i hi; simp only [state_zero, init]
    have : i ≠ 0 := by omega
    simp [this]
  | succ t ih =>
    rw [state_succ]
    exact F_supp ih

/-- `M` is *gapless* if its support is an initial segment. -/
def Gapless (M : ℕ → ℕ) : Prop := ∀ i, M i = 0 → M (i+1) = 0

lemma init_gapless (n : ℕ) : Gapless (init n) := by
  intro i hi
  simp only [init]
  have : i + 1 ≠ 0 := by omega
  simp [this]

lemma F_gapless {M : ℕ → ℕ} (h : Gapless M) : Gapless (F M) := by
  intro i hi
  rcases i with _ | i
  · -- F M 0 = 0 → F M 1 = 0
    rw [F_zero] at hi
    have hM0 : M 0 = 0 := by omega
    have hM1 : M 1 = 0 := h 0 hM0
    rw [F_succ]; simp [hM0, hM1]
  · rw [F_succ] at hi
    have hMi1 : M (i+1) = 0 := by omega
    have hMi2 : M (i+2) = 0 := h (i+1) hMi1
    rw [F_succ]; simp [hMi1, hMi2]

lemma state_gapless (n t : ℕ) : Gapless (state n t) := by
  induction t with
  | zero => simpa using init_gapless n
  | succ t ih => rw [state_succ]; exact F_gapless ih

/-- Gaplessness propagated: if `M i = 0` then `M j = 0` for all `j ≥ i`. -/
lemma Gapless.zero_of_ge {M : ℕ → ℕ} (h : Gapless M) {i j : ℕ} (hij : i ≤ j)
    (hi : M i = 0) : M j = 0 := by
  induction j with
  | zero =>
      have hi0 : i = 0 := Nat.le_zero.mp hij
      subst hi0; exact hi
  | succ j ihj =>
    rcases Nat.lt_or_ge i (j+1) with hlt | hge
    · exact h j (ihj (by omega))
    · have : i = j + 1 := by omega
      rwa [← this]

/-! ## Leading run of ones -/

/-- Length of the leading run of `1`s: the least position whose value is not `1`. -/
noncomputable def lead (M : ℕ → ℕ) : ℕ := sInf {i | M i ≠ 1}

lemma lead_le {M : ℕ → ℕ} {j : ℕ} (hj : M j ≠ 1) : lead M ≤ j :=
  Nat.sInf_le hj

lemma eq_one_of_lt_lead {M : ℕ → ℕ} {j : ℕ} (hj : j < lead M) : M j = 1 := by
  by_contra h
  exact absurd (lead_le h) (by omega)

lemma lead_ne_one {M : ℕ → ℕ} (h : ∃ j, M j ≠ 1) : M (lead M) ≠ 1 :=
  Nat.sInf_mem h

/-- States eventually take a value `≠ 1` (namely `0`), so `lead` is well-behaved. -/
lemma state_exists_ne_one (n t : ℕ) : ∃ j, state n t j ≠ 1 :=
  ⟨t + 1, by rw [state_supp n t (t+1) (le_refl _)]; omega⟩

lemma lead_state_ne_one (n t : ℕ) : state n t (lead (state n t)) ≠ 1 :=
  lead_ne_one (state_exists_ne_one n t)

/-! ## Target lemmas -/

@[simp] lemma tgt_apply (n i : ℕ) : tgt n i = if i < n then 1 else 0 := rfl

lemma tgt_lt {n i : ℕ} (h : i < n) : tgt n i = 1 := by simp [tgt, h]
lemma tgt_ge {n i : ℕ} (h : n ≤ i) : tgt n i = 0 := by simp [tgt]; omega

/-- `tgt` is a fixed point of `F`. -/
lemma F_tgt (n : ℕ) : F (tgt n) = tgt n := by
  funext i
  rcases i with _ | i
  · rw [F_zero]
    rcases n with _ | n
    · simp [tgt]
    · rw [tgt_lt (show 0 < n+1 by omega)]
  · rw [F_succ]
    by_cases h : i + 1 < n
    · rw [tgt_lt h, tgt_lt (show i < n by omega)]
    · rw [tgt_ge (by omega : n ≤ i+1)]
      by_cases h2 : i < n
      · rw [tgt_lt h2]
      · rw [tgt_ge (by omega : n ≤ i)]

lemma tgt_injective {m n : ℕ} (h : tgt m = tgt n) : m = n := by
  by_contra hne
  rcases Nat.lt_or_ge m n with hlt | hge
  · have := congrFun h m
    rw [tgt_ge (le_refl m), tgt_lt hlt] at this
    exact absurd this (by omega)
  · have hgt : n < m := by omega
    have := congrFun h n
    rw [tgt_lt hgt, tgt_ge (le_refl n)] at this
    exact absurd this (by omega)

lemma lead_tgt (n : ℕ) : lead (tgt n) = n := by
  apply le_antisymm
  · exact lead_le (by rw [tgt_ge (le_refl n)]; omega)
  · by_contra h
    push_neg at h
    have : tgt n (lead (tgt n)) = 1 := tgt_lt (by omega)
    exact lead_ne_one ⟨n, by rw [tgt_ge (le_refl n)]; omega⟩ this

/-- Value of `F M` at the leading position: `⌈M (lead M) / 2⌉` (left neighbour is `1`). -/
lemma F_at_lead (M : ℕ → ℕ) : F M (lead M) = (M (lead M) + 1) / 2 := by
  rcases hs : lead M with _ | s
  · rw [F_zero]
  · rw [F_succ]
    have : M s = 1 := eq_one_of_lt_lead (by rw [hs]; omega)
    rw [this]; omega

/-! ## Mass conservation and containment -/

open Finset in
/-- One step of `F` preserves the total mass (summed over a range containing the support). -/
lemma sum_F_step {M : ℕ → ℕ} {N : ℕ} (hM : M N = 0) :
    ∑ i ∈ Finset.range (N+1), F M i = ∑ i ∈ Finset.range N, M i := by
  have hsplit : ∑ i ∈ Finset.range (N+1), F M i
      = ∑ i ∈ Finset.range (N+1), (M i + 1)/2 + ∑ i ∈ Finset.range N, M i / 2 := by
    rw [Finset.sum_range_succ' (fun i => F M i) N]
    have h0 : F M 0 = (M 0 + 1)/2 := F_zero M
    have hstep : ∀ i ∈ Finset.range N, F M (i+1) = (M (i+1) + 1)/2 + M i / 2 :=
      fun i _ => F_succ M i
    rw [Finset.sum_congr rfl hstep, h0, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i => (M i + 1)/2) N]
    ring
  rw [hsplit, Finset.sum_range_succ (fun i => (M i + 1)/2) N, hM]
  simp only [Nat.zero_add, Nat.reduceDiv, Nat.add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; omega

open Finset in
/-- Total mass of the state is `n`. -/
lemma mass (n t : ℕ) : ∑ i ∈ Finset.range (t+1), state n t i = n := by
  induction t with
  | zero =>
    rw [Finset.sum_range_one]; simp [state_zero, init]
  | succ t ih =>
    rw [state_succ]
    have hz : state n t (t+1) = 0 := state_supp n t (t+1) (le_refl _)
    rw [sum_F_step hz]; exact ih

/-- **Containment (K):** the mass stays within positions `0, …, n-1`. -/
lemma state_zero_ge (n t : ℕ) : ∀ i, n ≤ i → state n t i = 0 := by
  intro i hi
  by_contra hne
  -- all positions `0..i` are nonzero, giving mass ≥ i+1 ≥ n+1
  have hpos : ∀ j, j ≤ i → 1 ≤ state n t j := by
    intro j hj
    rcases Nat.eq_zero_or_pos (state n t j) with h0 | hp
    · exact absurd (state_gapless n t |>.zero_of_ge hj h0) hne
    · exact hp
  -- sum over range (i+1) is at least i+1
  have hbig : i + 1 ≤ ∑ j ∈ Finset.range (i+1), state n t j := by
    calc i + 1 = ∑ _j ∈ Finset.range (i+1), 1 := by simp
    _ ≤ ∑ j ∈ Finset.range (i+1), state n t j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hpos j (by simp at hj; omega)
  -- the sum over range (i+1) is bounded by the total mass n
  have hsum_le : ∑ j ∈ Finset.range (i+1), state n t j ≤ n := by
    have hsub : Finset.range (i+1) ⊆ Finset.range ((i+1) + (t+1)) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hmono : ∑ j ∈ Finset.range (i+1), state n t j
        ≤ ∑ j ∈ Finset.range ((i+1)+(t+1)), state n t j :=
      Finset.sum_le_sum_of_subset hsub
    have hbig' : ∑ j ∈ Finset.range ((i+1)+(t+1)), state n t j = n := by
      rw [← Finset.sum_range_add_sum_Ico (fun j => state n t j)
            (show t+1 ≤ (i+1)+(t+1) by omega), mass n t]
      have hz : ∑ j ∈ Finset.Ico (t+1) ((i+1)+(t+1)), state n t j = 0 :=
        Finset.sum_eq_zero (fun j hj => state_supp n t j
          (by rw [Finset.mem_Ico] at hj; omega))
      omega
    omega
  omega

/-! ## Growth of the leading run -/

/-- `F` preserves the leading run of ones. -/
lemma F_eq_one_of_lt_lead {M : ℕ → ℕ} {i : ℕ} (hi : i < lead M) : F M i = 1 := by
  rcases i with _ | k
  · rw [F_zero, eq_one_of_lt_lead hi]
  · rw [F_succ, eq_one_of_lt_lead hi, eq_one_of_lt_lead (by omega : k < lead M)]

lemma lead_le_lead_F {M : ℕ → ℕ} (hex : ∃ j, F M j ≠ 1) : lead M ≤ lead (F M) := by
  by_contra hc
  push_neg at hc
  exact (lead_ne_one hex) (F_eq_one_of_lt_lead hc)

/-- If the leading run grows by at least two, `M` has the terminal shape at the front. -/
lemma big_growth {M : ℕ → ℕ} (hex : ∃ j, M j ≠ 1)
    (hbig : lead M + 2 ≤ lead (F M)) :
    M (lead M) = 2 ∧ M (lead M + 1) = 0 := by
  have h1 : F M (lead M) = 1 := eq_one_of_lt_lead (by omega)
  have h2 : F M (lead M + 1) = 1 := eq_one_of_lt_lead (by omega)
  rw [F_at_lead] at h1
  have hMs : M (lead M) = 2 := by
    have hne : M (lead M) ≠ 1 := lead_ne_one hex
    omega
  rw [F_succ, hMs] at h2
  exact ⟨hMs, by omega⟩

/-- Terminal shape: if `M s = 2, M (s+1) = 0` at `s = lead M`, then `F M = tgt (s+2)`. -/
lemma terminal_shape {M : ℕ → ℕ} (hg : Gapless M)
    (h2 : M (lead M) = 2) (h0 : M (lead M + 1) = 0) :
    F M = tgt (lead M + 2) := by
  funext i
  rcases lt_trichotomy i (lead M) with hlt | heq | hgt
  · rw [F_eq_one_of_lt_lead hlt, tgt_lt (by omega)]
  · rw [heq, F_at_lead, h2, tgt_lt (by omega)]
  · -- i > lead M
    rcases Nat.lt_or_ge i (lead M + 2) with hs2 | hs2
    · -- i = lead M + 1
      have hi1 : i = lead M + 1 := by omega
      rw [hi1, F_succ, h0, h2, tgt_lt (by omega)]
    · -- i ≥ lead M + 2
      rw [tgt_ge hs2]
      have hz : ∀ j, lead M + 1 ≤ j → M j = 0 := fun j hj => hg.zero_of_ge hj h0
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [F_succ, hz (k+1) (by omega), hz k (by omega)]

/-- Sum of `tgt m` over an initial segment. -/
lemma sum_tgt_eq_min (m N : ℕ) : ∑ i ∈ Finset.range N, tgt m i = min m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, tgt_apply]
    by_cases h : N < m <;> simp [h] <;> omega

/-- A state that equals some target must have the matching size. -/
lemma state_eq_tgt_size {n t m : ℕ} (h : state n t = tgt m) : m = n := by
  have hmass : min m (t+1) = n := by
    have := mass n t
    rw [h] at this
    rw [sum_tgt_eq_min] at this
    exact this
  have hle : m ≤ n := by
    have hz : tgt m n = 0 := by rw [← h]; exact state_zero_ge n t n (le_refl n)
    by_contra hlt
    rw [tgt_lt (by omega : n < m)] at hz
    omega
  omega

/-- **J1-growth:** if the next state is not the target, the leading run grows by at most one. -/
lemma lead_step_le {n t : ℕ} (h : state n (t+1) ≠ tgt n) :
    lead (state n (t+1)) ≤ lead (state n t) + 1 := by
  by_contra hc
  push_neg at hc
  have hM : state n (t+1) = F (state n t) := state_succ n t
  rw [hM] at hc h
  have hbg := big_growth (state_exists_ne_one n t) (by omega)
  have hterm : F (state n t) = tgt (lead (state n t) + 2) :=
    terminal_shape (state_gapless n t) hbg.1 hbg.2
  have hsize : lead (state n t) + 2 = n := by
    apply state_eq_tgt_size (t := t+1)
    rw [state_succ, hterm]
  rw [hterm, hsize] at h
  exact h rfl

/-! ## Frontier bound on the chip -/

/-- Position of the first zero. -/
noncomputable def frontier (M : ℕ → ℕ) : ℕ := sInf {L | M L = 0}

lemma frontier_zero {M : ℕ → ℕ} (h : ∃ L, M L = 0) : M (frontier M) = 0 :=
  Nat.sInf_mem h

lemma ne_zero_of_lt_frontier {M : ℕ → ℕ} {j : ℕ} (hj : j < frontier M) : M j ≠ 0 := by
  intro h0
  have hle : frontier M ≤ j := Nat.sInf_le h0
  omega

/-- Beyond the frontier, a gapless function is zero. -/
lemma zero_ge_frontier {M : ℕ → ℕ} (hg : Gapless M) (h : ∃ L, M L = 0)
    {j : ℕ} (hj : frontier M ≤ j) : M j = 0 :=
  hg.zero_of_ge hj (frontier_zero h)

/-- Before the frontier of `M`, the stepped `F M` is still nonzero. -/
lemma F_ne_zero_of_lt_frontier {M : ℕ → ℕ} {i : ℕ} (hi : i < frontier M) : F M i ≠ 0 := by
  have hMi : M i ≠ 0 := ne_zero_of_lt_frontier hi
  rcases i with _ | k
  · rw [F_zero]; omega
  · rw [F_succ]; omega

/-- `F` does not shrink the frontier (for gapless `M`). -/
lemma frontier_mono {M : ℕ → ℕ} (hFex : ∃ L, F M L = 0) :
    frontier M ≤ frontier (F M) := by
  by_contra hc
  push_neg at hc
  exact (F_ne_zero_of_lt_frontier hc) (frontier_zero hFex)

lemma state_frontier_ex (n t : ℕ) : ∃ L, state n t L = 0 :=
  ⟨t+1, state_supp n t (t+1) (le_refl _)⟩

lemma nextp_ge (v p : ℕ) : p ≤ nextp v p := by
  unfold nextp; split <;> omega

lemma nextp_odd {v : ℕ} (h : v % 2 = 1) (p : ℕ) : nextp v p = p + 1 := by
  unfold nextp; simp [h]

lemma nextp_even {v : ℕ} (h : v % 2 ≠ 1) (p : ℕ) : nextp v p = p := by
  unfold nextp; simp [h]

/-- The chip never overtakes the frontier. -/
lemma chip_le_frontier (n t : ℕ) : chip n t ≤ frontier (state n t) := by
  induction t with
  | zero => rw [chip_zero]; exact Nat.zero_le _
  | succ t ih =>
    have hfm : frontier (state n t) ≤ frontier (state n (t+1)) := by
      rw [state_succ]
      exact frontier_mono (by rw [← state_succ]; exact state_frontier_ex n (t+1))
    rw [chip_succ]
    by_cases hodd : state n t (chip n t) % 2 = 1
    · rw [nextp_odd hodd]
      have hne : state n t (chip n t) ≠ 0 := by omega
      have hlt : chip n t < frontier (state n t) := by
        by_contra hge; push_neg at hge
        exact hne (zero_ge_frontier (state_gapless n t) (state_frontier_ex n t) hge)
      omega
    · rw [nextp_even hodd]; omega

/-! ## The key invariant J1 -/

/-- **J1:** while unsettled, the chip is at most one behind the leading run. -/
lemma J1 (n t : ℕ) (h : state n t ≠ tgt n) : lead (state n t) ≤ chip n t + 1 := by
  induction t with
  | zero =>
    have : lead (state n 0) ≤ 1 := by
      apply lead_le
      show state n 0 1 ≠ 1
      rw [state_zero]; simp [init]
    simpa using this
  | succ t ih =>
    have hprev : state n t ≠ tgt n := by
      intro hcontra
      apply h
      rw [state_succ, hcontra, F_tgt]
    have ihp := ih hprev
    have hstep := lead_step_le h
    -- reduce to: lead (state n t) ≤ chip n (t+1)
    have hkey : lead (state n t) ≤ chip n (t+1) := by
      rw [chip_succ]
      by_cases hq : chip n t < lead (state n t)
      · have hval : state n t (chip n t) = 1 := eq_one_of_lt_lead hq
        rw [nextp_odd (by rw [hval])]
        omega
      · calc lead (state n t) ≤ chip n t := by omega
          _ ≤ nextp (state n t (chip n t)) (chip n t) := nextp_ge _ _
    omega

/-! ## The penultimate state -/

/-- The step just before settling has the shape `[1,…,1,2]` (of length `n-1`). -/
lemma penult (n t : ℕ) (hn : 2 ≤ n)
    (h1 : state n (t+1) = tgt n) (h0 : state n t ≠ tgt n) :
    lead (state n t) = n - 2 ∧ state n t (n-2) = 2 ∧ (∀ i, n - 1 ≤ i → state n t i = 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hFA : F (state (m+2) t) = tgt (m+2) := by rw [← state_succ]; exact h1
  have hleadFA : lead (F (state (m+2) t)) = m + 2 := by rw [hFA, lead_tgt]
  have hgap := state_gapless (m+2) t
  have hex := state_exists_ne_one (m+2) t
  -- Show lead (state (m+2) t) = m.
  have hsm : lead (state (m+2) t) = m := by
    -- s ≤ m+2
    have hsle : lead (state (m+2) t) ≤ m + 2 := by
      by_contra hc; push_neg at hc
      have hone : F (state (m+2) t) (m+2) = 1 := F_eq_one_of_lt_lead (by omega)
      rw [hFA, tgt_ge (le_refl (m+2))] at hone; omega
    -- s ≠ m+2
    have hne2 : lead (state (m+2) t) ≠ m + 2 := by
      intro he
      apply h0
      funext i
      by_cases hi : i < m + 2
      · have h1i : state (m+2) t i = 1 :=
          eq_one_of_lt_lead (show i < lead (state (m+2) t) by rw [he]; exact hi)
        rw [h1i, tgt_lt hi]
      · rw [state_zero_ge (m+2) t i (by omega), tgt_ge (by omega)]
    -- s ≠ m+1
    have hne1 : lead (state (m+2) t) ≠ m + 1 := by
      intro he
      have hval : F (state (m+2) t) (m+1) = 1 := by rw [hFA, tgt_lt (by omega)]
      rw [← he, F_at_lead, he] at hval
      have hne_lead : state (m+2) t (m+1) ≠ 1 := by
        have h' := lead_ne_one hex; rwa [he] at h'
      have hval2 : state (m+2) t (m+1) = 2 := by omega
      have hz : F (state (m+2) t) (m+2) = 0 := by rw [hFA, tgt_ge (le_refl (m+2))]
      rw [show m + 2 = (m+1) + 1 from rfl, F_succ, hval2] at hz
      omega
    have hsm' : lead (state (m+2) t) ≤ m := by omega
    -- now big_growth
    have hbig : lead (state (m+2) t) + 2 ≤ lead (F (state (m+2) t)) := by
      rw [hleadFA]; omega
    have hbg := big_growth hex hbig
    have hterm := terminal_shape hgap hbg.1 hbg.2
    rw [hFA] at hterm
    have := tgt_injective hterm.symm
    omega
  refine ⟨by rw [hsm]; omega, ?_, ?_⟩
  · -- state (m+2) t (m) = 2
    have hbig : lead (state (m+2) t) + 2 ≤ lead (F (state (m+2) t)) := by
      omega
    have hbg := big_growth hex hbig
    rw [hsm] at hbg
    simpa using hbg.1
  · -- ∀ i ≥ m+1, state = 0
    have hbig : lead (state (m+2) t) + 2 ≤ lead (F (state (m+2) t)) := by
      omega
    have hbg := big_growth hex hbig
    rw [hsm] at hbg
    intro i hi
    have h0' : state (m+2) t (m+1) = 0 := hbg.2
    exact hgap.zero_of_ge (by omega : m + 1 ≤ i) h0'

/-! ## First-moment monovariant -/

/-- Weighted version of `sum_F_step`: the first moment increases by `∑ M i / 2`. -/
lemma sum_weighted_F_step {M : ℕ → ℕ} {N : ℕ} (hM : M N = 0) :
    ∑ i ∈ Finset.range (N+1), i * F M i
      = (∑ i ∈ Finset.range N, i * M i) + ∑ i ∈ Finset.range N, M i / 2 := by
  have hstep : ∀ i ∈ Finset.range N, (i+1) * F M (i+1)
      = (i+1) * ((M (i+1) + 1)/2) + (i+1) * (M i / 2) := by
    intro i _; rw [F_succ, Nat.mul_add]
  have hA : ∑ i ∈ Finset.range N, (i+1) * ((M (i+1) + 1)/2)
      = ∑ i ∈ Finset.range N, i * ((M i + 1)/2) := by
    have key := Finset.sum_range_succ' (fun j => j * ((M j + 1)/2)) N
    rw [Finset.sum_range_succ (fun j => j * ((M j + 1)/2)) N] at key
    simp only [hM, Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at key
    omega
  have hB : ∑ i ∈ Finset.range N, (i+1) * (M i / 2)
      = (∑ i ∈ Finset.range N, i * (M i / 2)) + ∑ i ∈ Finset.range N, M i / 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hC : (∑ i ∈ Finset.range N, i * ((M i + 1)/2))
        + (∑ i ∈ Finset.range N, i * (M i / 2))
      = ∑ i ∈ Finset.range N, i * M i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [Finset.sum_range_succ' (fun i => i * F M i) N]
  simp only [Nat.zero_mul, Nat.add_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hA, hB]
  omega

/-- First moment of the state after `t` steps. -/
def moment (n t : ℕ) : ℕ := ∑ i ∈ Finset.range (t+1), i * state n t i

lemma moment_zero (n : ℕ) : moment n 0 = 0 := by
  unfold moment; simp

lemma moment_succ (n t : ℕ) :
    moment n (t+1) = moment n t + ∑ i ∈ Finset.range (t+1), state n t i / 2 := by
  unfold moment
  rw [state_succ]
  have hz : state n t (t+1) = 0 := state_supp n t (t+1) (le_refl _)
  rw [sum_weighted_F_step hz]

/-- The first moment is bounded by `n * n`. -/
lemma moment_bound (n t : ℕ) : moment n t ≤ n * n := by
  unfold moment
  calc ∑ i ∈ Finset.range (t+1), i * state n t i
      ≤ ∑ i ∈ Finset.range (t+1), n * state n t i := by
        apply Finset.sum_le_sum
        intro i _
        rcases Nat.eq_zero_or_pos (state n t i) with h0 | hp
        · rw [h0]; simp
        · have hlt : i < n := by
            by_contra hge; push_neg at hge
            exact absurd (state_zero_ge n t i hge) (by omega)
          exact Nat.mul_le_mul (by omega) (le_refl _)
    _ = n * ∑ i ∈ Finset.range (t+1), state n t i := by rw [Finset.mul_sum]
    _ = n * n := by rw [mass n t]

/-- The total mass over `range n` is `n`. -/
lemma mass_range_n (n t : ℕ) : ∑ i ∈ Finset.range n, state n t i = n := by
  have hm1 : ∑ i ∈ Finset.range (max n (t+1)), state n t i = n := by
    rw [← Finset.sum_range_add_sum_Ico (fun i => state n t i)
          (show t+1 ≤ max n (t+1) from le_max_right _ _), mass n t]
    have hz : ∑ i ∈ Finset.Ico (t+1) (max n (t+1)), state n t i = 0 :=
      Finset.sum_eq_zero (fun i hi => state_supp n t i
        (by rw [Finset.mem_Ico] at hi; omega))
    omega
  have hm2 : ∑ i ∈ Finset.range (max n (t+1)), state n t i
      = ∑ i ∈ Finset.range n, state n t i := by
    rw [← Finset.sum_range_add_sum_Ico (fun i => state n t i)
          (show n ≤ max n (t+1) from le_max_left _ _)]
    have hz : ∑ i ∈ Finset.Ico n (max n (t+1)), state n t i = 0 :=
      Finset.sum_eq_zero (fun i hi => state_zero_ge n t i
        (by rw [Finset.mem_Ico] at hi; omega))
    omega
  omega

/-- If all cells are `≤ 1`, the state is exactly the target. -/
lemma zero_one_eq_tgt (n t : ℕ) (h : ∀ i, state n t i ≤ 1) : state n t = tgt n := by
  funext i
  by_cases hi : i < n
  · rw [tgt_lt hi]
    by_contra hne
    have h0 : state n t i = 0 := by have := h i; omega
    have hlt : ∑ j ∈ Finset.range n, state n t j < ∑ j ∈ Finset.range n, 1 :=
      Finset.sum_lt_sum (fun j _ => h j)
        ⟨i, Finset.mem_range.mpr hi, by rw [h0]; omega⟩
    rw [mass_range_n] at hlt
    simp at hlt
  · push_neg at hi
    rw [state_zero_ge n t i hi, tgt_ge hi]

/-- While unsettled, the moment drift is at least `1`. -/
lemma drift_pos (n t : ℕ) (h : state n t ≠ tgt n) :
    1 ≤ ∑ i ∈ Finset.range (t+1), state n t i / 2 := by
  by_contra hc
  push_neg at hc
  have hall : ∀ i, state n t i ≤ 1 := by
    intro i
    by_cases hi : i < t+1
    · have hterm : state n t i / 2 ≤ ∑ j ∈ Finset.range (t+1), state n t j / 2 :=
        Finset.single_le_sum (f := fun j => state n t j / 2)
          (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
      omega
    · have : state n t i = 0 := state_supp n t i (by omega)
      omega
  exact h (zero_one_eq_tgt n t hall)

/-- Under the (false) assumption of never settling, the moment grows without bound. -/
lemma moment_ge_of_unsettled (n : ℕ) (h : ∀ k, state n k ≠ tgt n) :
    ∀ t, t ≤ moment n t := by
  intro t
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have hd : 1 ≤ ∑ i ∈ Finset.range (t+1), state n t i / 2 := drift_pos n t (h t)
    rw [moment_succ]
    omega

lemma settle_exists (n : ℕ) : ∃ k, state n k = tgt n := by
  by_contra hc
  push_neg at hc
  have hge := moment_ge_of_unsettled n hc (n*n+1)
  have hle := moment_bound n (n*n+1)
  omega

/-! ## The settling time -/

noncomputable def settle (n : ℕ) : ℕ := sInf {k | state n k = tgt n}

lemma settle_mem (n : ℕ) : state n (settle n) = tgt n :=
  Nat.sInf_mem (settle_exists n)

lemma settle_le (n : ℕ) {k : ℕ} (h : state n k = tgt n) : settle n ≤ k :=
  Nat.sInf_le h

lemma settle_min (n t : ℕ) (h : t < settle n) : state n t ≠ tgt n := by
  intro hc
  exact absurd (settle_le n hc) (by omega)

lemma settled_ge (n : ℕ) : ∀ d, state n (settle n + d) = tgt n := by
  intro d
  induction d with
  | zero => simpa using settle_mem n
  | succ d ih =>
    rw [show settle n + (d+1) = (settle n + d) + 1 from rfl, state_succ, ih, F_tgt]

lemma settle_pos (n : ℕ) (hn : 2 ≤ n) : 1 ≤ settle n := by
  rcases Nat.eq_zero_or_pos (settle n) with h | h
  · exfalso
    have hm := settle_mem n
    rw [h, state_zero] at hm
    have h1 := congrFun hm 1
    rw [show init n 1 = 0 from by simp [init], show tgt n 1 = 1 from tgt_lt (by omega)] at h1
    exact absurd h1 (by norm_num)
  · exact h

lemma settle_one : settle 1 = 0 := by
  apply Nat.le_antisymm _ (Nat.zero_le _)
  apply settle_le
  rw [state_zero]
  funext i
  by_cases hi : i = 0
  · subst hi; rw [tgt_lt (by omega)]; simp [init]
  · rw [show init 1 i = 0 from by simp [init, hi], tgt_ge (by omega)]

/-! ## The chip position at settle time is within 2 of the front -/

lemma chip_settle_bound (n : ℕ) (hn : 1 ≤ n) :
    chip n (settle n) < n ∧ n ≤ chip n (settle n) + 2 := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    rw [settle_one, chip_zero]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hsp := settle_pos (m+2) h2
    obtain ⟨t, ht⟩ : ∃ t, settle (m+2) = t + 1 := ⟨settle (m+2) - 1, by omega⟩
    have hmem : state (m+2) (t+1) = tgt (m+2) := by rw [← ht]; exact settle_mem (m+2)
    have h0 : state (m+2) t ≠ tgt (m+2) := settle_min (m+2) t (by omega)
    have hpen := penult (m+2) t h2 hmem h0
    have hP2 : state (m+2) t m = 2 := by have := hpen.2.1; simpa using this
    have hJ : lead (state (m+2) t) ≤ chip (m+2) t + 1 := J1 (m+2) t h0
    rw [hpen.1] at hJ
    -- frontier = m+1
    have hfront : frontier (state (m+2) t) = m + 1 := by
      have hle : frontier (state (m+2) t) ≤ m + 1 :=
        Nat.sInf_le (hpen.2.2 (m+1) (le_refl _))
      have hge : m + 1 ≤ frontier (state (m+2) t) := by
        by_contra hc
        push_neg at hc
        have hz : state (m+2) t (frontier (state (m+2) t)) = 0 :=
          frontier_zero (state_frontier_ex (m+2) t)
        rcases Nat.lt_or_ge (frontier (state (m+2) t)) m with hlt | hge2
        · have h1' := eq_one_of_lt_lead
            (show frontier (state (m+2) t) < lead (state (m+2) t) by rw [hpen.1]; exact hlt)
          omega
        · have heq : frontier (state (m+2) t) = m := by omega
          rw [heq] at hz
          omega
      omega
    have hqf : chip (m+2) t ≤ m + 1 := by
      have := chip_le_frontier (m+2) t
      rw [hfront] at this; exact this
    rw [ht, chip_succ]
    rcases Nat.lt_trichotomy (chip (m+2) t) m with hlt | heq | hgt
    · have hv : state (m+2) t (chip (m+2) t) = 1 :=
        eq_one_of_lt_lead (show chip (m+2) t < lead (state (m+2) t) by rw [hpen.1]; exact hlt)
      rw [hv, nextp_odd (by decide)]; omega
    · rw [heq, hP2, nextp_even (by decide)]; omega
    · have hqeq : chip (m+2) t = m + 1 := by omega
      rw [hqeq]
      have hv : state (m+2) t (m+1) = 0 := hpen.2.2 (m+1) (le_refl _)
      rw [hv, nextp_even (by decide)]; omega

/-! ## Helper lemmas for the assembly -/

lemma e_inj {p q : ℕ} (h : e p = e q) : p = q := by
  by_contra hne
  have hc := congrFun h p
  rw [e_apply, e_apply, if_pos rfl, if_neg (by omega : ¬ (p = q))] at hc
  exact absurd hc (by norm_num)

lemma add_e_cancel {M N : ℕ → ℕ} {p : ℕ} (h : M + e p = N + e p) : M = N := by
  funext i
  have hc := congrFun h i
  rw [add_apply, add_apply] at hc
  omega

lemma tgt_succ (n : ℕ) : tgt (n+1) = tgt n + e n := by
  funext i
  rw [add_apply, tgt_apply, tgt_apply, e_apply]
  split_ifs <;> omega

/-! ## The assembly: `settle (n+1) = settle n + (n - chip n (settle n))` -/

lemma settle_succ (n : ℕ) (hn : 1 ≤ n) :
    settle (n+1) = settle n + (n - chip n (settle n)) := by
  -- chip advances after settle time
  have chip_after : ∀ k, chip n (settle n + k) = min (chip n (settle n) + k) n := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero]
      have := (chip_settle_bound n hn).1; omega
    | succ k ih =>
      rw [show settle n + (k+1) = (settle n + k) + 1 from rfl, chip_succ,
          settled_ge n k, ih]
      rcases Nat.lt_or_ge (chip n (settle n) + k) n with hlt | hge
      · rw [Nat.min_eq_left (le_of_lt hlt), tgt_lt hlt, nextp_odd (by decide)]
        omega
      · rw [Nat.min_eq_right hge, tgt_ge (le_refl n), nextp_even (by decide)]
        omega
  -- state (n+1) reaches target at settle n + d
  have hreach : state (n+1) (settle n + (n - chip n (settle n))) = tgt (n+1) := by
    rw [coupling, settled_ge n (n - chip n (settle n)), chip_after, tgt_succ]
    have hmin : min (chip n (settle n) + (n - chip n (settle n))) n = n := by
      have := (chip_settle_bound n hn).1; omega
    rw [hmin]
  have hle : settle (n+1) ≤ settle n + (n - chip n (settle n)) := settle_le (n+1) hreach
  -- no earlier settle time
  have hlb : ∀ t, t < settle n + (n - chip n (settle n)) → state (n+1) t ≠ tgt (n+1) := by
    intro t ht hc
    rw [coupling, tgt_succ] at hc
    have hidx := congrFun hc n
    rw [add_apply, add_apply, state_zero_ge n t n (le_refl n), tgt_ge (le_refl n)] at hidx
    have hchipn : chip n t = n := by
      by_contra hne
      have hz1 : e (chip n t) n = 0 := by rw [e_apply]; exact if_neg (by omega)
      have hz2 : e n n = 1 := by rw [e_apply]; exact if_pos rfl
      rw [hz1, hz2] at hidx
      omega
    rcases Nat.lt_or_ge t (settle n) with hts | hts
    · have hcancel : state n t = tgt n := by
        rw [hchipn] at hc; exact add_e_cancel hc
      exact settle_min n t hts hcancel
    · obtain ⟨k, rfl⟩ : ∃ k, t = settle n + k := ⟨t - settle n, by omega⟩
      have hca := chip_after k
      rw [hca] at hchipn
      have hb := (chip_settle_bound n hn).1
      omega
  have hge : settle n + (n - chip n (settle n)) ≤ settle (n+1) := by
    by_contra hcon
    push_neg at hcon
    exact hlb (settle (n+1)) hcon (settle_mem (n+1))
  omega

/-! ## STEP 1: the list automaton `a` equals `settle` -/

def trimZ (l : List ℕ) : List ℕ := (l.reverse.dropWhile (fun x => x = 0)).reverse

def caStep (config : List ℕ) : List ℕ :=
  trimZ (List.zipWith Nat.add (config.map (fun m => (m+1)/2) ++ [0]) (0 :: config.map (fun m => m/2)))

def Slist (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => caStep acc) [n]

def toFun (L : List ℕ) : ℕ → ℕ := fun i => L.getD i 0

lemma a_eq (n : ℕ) (hn : n ≠ 0) : a n = sInf {k | Slist n k = List.replicate n 1} := by
  simp only [a, Slist, caStep, trimZ, if_neg hn]

lemma Slist_zero (n : ℕ) : Slist n 0 = [n] := rfl

lemma Slist_succ (n t : ℕ) : Slist n (t+1) = caStep (Slist n t) := by
  unfold Slist
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The head of `dropWhile p` does not satisfy `p`. -/
lemma head?_dropWhile_not (p : ℕ → Bool) (l : List ℕ) (a : ℕ)
    (h : (l.dropWhile p).head? = some a) : p a = false := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hpx : p x
    · rw [List.dropWhile_cons_of_pos hpx] at h; exact ih h
    · rw [List.dropWhile_cons_of_neg (by simpa using hpx), List.head?_cons] at h
      have hxa : x = a := by simpa using h
      rw [← hxa]; simpa using hpx

/-- `x` is `trimZ x` followed by some zeros. -/
lemma trimZ_append (x : List ℕ) :
    ∃ z : List ℕ, x = trimZ x ++ z ∧ ∀ a ∈ z, a = 0 := by
  refine ⟨(x.reverse.takeWhile (fun y => y = 0)).reverse, ?_, ?_⟩
  · have hx : x.reverse
        = x.reverse.takeWhile (fun y => y = 0) ++ x.reverse.dropWhile (fun y => y = 0) :=
      (List.takeWhile_append_dropWhile).symm
    calc x = x.reverse.reverse := (List.reverse_reverse x).symm
      _ = (x.reverse.takeWhile (fun y => y = 0)
              ++ x.reverse.dropWhile (fun y => y = 0)).reverse := by rw [← hx]
      _ = (x.reverse.dropWhile (fun y => y = 0)).reverse
              ++ (x.reverse.takeWhile (fun y => y = 0)).reverse := by rw [List.reverse_append]
      _ = trimZ x ++ (x.reverse.takeWhile (fun y => y = 0)).reverse := rfl
  · intro a ha
    rw [List.mem_reverse] at ha
    have := List.mem_takeWhile_imp ha
    simpa using this

lemma trimZ_getD (x : List ℕ) (i : ℕ) : (trimZ x).getD i 0 = x.getD i 0 := by
  obtain ⟨z, hz, hz0⟩ := trimZ_append x
  have hzero : ∀ j, z.getD j 0 = 0 := by
    intro j
    rcases Nat.lt_or_ge j z.length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]; exact hz0 _ (List.getElem_mem hj)
    · exact List.getD_eq_default _ _ hj
  rcases Nat.lt_or_ge i (trimZ x).length with hi | hi
  · conv_rhs => rw [hz, List.getD_append _ _ _ _ hi]
  · rw [List.getD_eq_default _ _ hi]
    conv_rhs => rw [hz, List.getD_append_right _ _ _ _ hi]
    exact (hzero _).symm

lemma getD_zipWith_add (a b : List ℕ) (hlen : a.length = b.length) (i : ℕ) :
    (List.zipWith Nat.add a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  rcases Nat.lt_or_ge i (List.zipWith Nat.add a b).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi, List.getElem_zipWith]
    rw [List.length_zipWith] at hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    rfl
  · have h1 : (List.zipWith Nat.add a b).getD i 0 = 0 := List.getD_eq_default _ _ hi
    rw [List.length_zipWith] at hi
    rw [h1, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma A_getD (L : List ℕ) (i : ℕ) :
    (L.map (fun m => (m+1)/2) ++ [0]).getD i 0 = (L.getD i 0 + 1)/2 := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi), List.getD_eq_default L 0 hi]
    rcases (i - (L.map (fun m => (m+1)/2)).length) with _ | k <;> simp

lemma map_half_getD (L : List ℕ) (j : ℕ) :
    (L.map (fun m => m/2)).getD j 0 = (L.getD j 0)/2 := by
  rcases Nat.lt_or_ge j L.length with hj | hj
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
  · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ hj]

lemma toFun_caStep (L : List ℕ) : toFun (caStep L) = F (toFun L) := by
  funext i
  unfold toFun caStep
  rw [trimZ_getD, getD_zipWith_add _ _ (by simp) i, A_getD]
  rcases i with _ | j
  · rw [F_zero]
    simp only [List.getD_cons_zero]
    rfl
  · rw [F_succ, List.getD_cons_succ, map_half_getD]

lemma toFun_Slist (n t : ℕ) : toFun (Slist n t) = state n t := by
  induction t with
  | zero =>
    rw [Slist_zero, state_zero]
    funext i
    unfold toFun init
    rcases i with _ | k
    · rfl
    · simp
  | succ t ih => rw [Slist_succ, toFun_caStep, ih, ← state_succ]

lemma toFun_replicate (n : ℕ) : toFun (List.replicate n 1) = tgt n := by
  funext i
  unfold toFun tgt
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate, if_pos hi]
  · rw [List.getD_eq_default _ _ (by simpa using hi), if_neg (by omega)]

def NT (L : List ℕ) : Prop := L.getLast? ≠ some 0

lemma NT_trimZ (y : List ℕ) : NT (trimZ y) := by
  unfold NT trimZ
  rw [List.getLast?_reverse]
  intro h
  have := head?_dropWhile_not (fun x => x = 0) y.reverse 0 h
  simpa using this

lemma NT_replicate (n : ℕ) : NT (List.replicate n 1) := by
  unfold NT
  rcases eq_or_ne (List.replicate n 1) [] with h | h
  · rw [h]; simp
  · rw [List.getLast?_eq_some_getLast h]
    intro hc
    have heq : (List.replicate n 1).getLast h = 0 := by simpa using hc
    have hmem := List.getLast_mem h
    rw [heq] at hmem
    exact absurd (List.eq_of_mem_replicate hmem) (by norm_num)

lemma NT_Slist (n t : ℕ) (hn : n ≠ 0) : NT (Slist n t) := by
  cases t with
  | zero =>
    rw [Slist_zero]
    unfold NT
    simpa using hn
  | succ t => rw [Slist_succ]; unfold caStep; exact NT_trimZ _

lemma eq_of_NT_toFun {L1 L2 : List ℕ} (h1 : NT L1) (h2 : NT L2)
    (h : ∀ i, L1.getD i 0 = L2.getD i 0) : L1 = L2 := by
  have key : ∀ A B : List ℕ, NT B → (∀ i, A.getD i 0 = B.getD i 0) → B.length ≤ A.length := by
    intro A B hB hAB
    rcases eq_or_ne B [] with rfl | hBne
    · simp
    · have hpos := List.length_pos_of_ne_nil hBne
      have hj : B.length - 1 < B.length := by omega
      have hBlast : B.getD (B.length - 1) 0 ≠ 0 := by
        have hsome : B.getLast? = some (B.getLast hBne) := List.getLast?_eq_some_getLast hBne
        have hne0 : B.getLast hBne ≠ 0 := by
          intro hc; apply hB; rw [hsome, hc]
        rw [List.getD_eq_getElem _ _ hj, ← getLast_eq_getElem hBne]
        exact hne0
      by_contra hlt
      push_neg at hlt
      have h0 : A.getD (B.length - 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
      rw [hAB (B.length - 1)] at h0
      exact hBlast h0
  have e1 : L2.length ≤ L1.length := key L1 L2 h2 h
  have e2 : L1.length ≤ L2.length := key L2 L1 h1 (fun i => (h i).symm)
  have hlen : L1.length = L2.length := le_antisymm e2 e1
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have := h i
  rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at this

lemma Slist_iff (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    Slist n k = List.replicate n 1 ↔ state n k = tgt n := by
  constructor
  · intro hS
    rw [← toFun_Slist, hS, toFun_replicate]
  · intro hst
    apply eq_of_NT_toFun (NT_Slist n k hn) (NT_replicate n)
    intro i
    have hfun : toFun (Slist n k) = toFun (List.replicate n 1) := by
      rw [toFun_Slist, toFun_replicate, hst]
    exact congrFun hfun i

lemma a_eq_settle (n : ℕ) (hn : n ≠ 0) : a n = settle n := by
  rw [a_eq n hn, settle]
  congr 1
  apply Set.ext
  intro k
  simp only [Set.mem_setOf_eq]
  exact Slist_iff n hn k

/-! ## The main theorem -/

theorem main (n : ℕ) (hn : 1 ≤ n) : a (n+1) = a n + 1 ∨ a (n+1) = a n + 2 := by
  rw [a_eq_settle (n+1) (by omega), a_eq_settle n (by omega), settle_succ n hn]
  obtain ⟨hb1, hb2⟩ := chip_settle_bound n hn
  omega

end A300997
