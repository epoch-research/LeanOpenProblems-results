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

def hc (m : ℕ) : ℕ := (m + 1) / 2
def hf (m : ℕ) : ℕ := m / 2
def trim (l : List ℕ) : List ℕ := (l.reverse.dropWhile (· = 0)).reverse
def rawstep (c : List ℕ) : List ℕ :=
  zipWith Nat.add (c.map hc ++ [0]) (0 :: c.map hf)
def step (c : List ℕ) : List ℕ := trim (rawstep c)

/-- suffix sum -/
def T (c : List ℕ) (j : ℕ) : ℕ := (c.drop j).sum

-- sum of zipWith add equals sum of parts (equal lengths)
theorem sum_zipWith_add (a b : List ℕ) (h : a.length = b.length) :
    (zipWith Nat.add a b).sum = a.sum + b.sum := by
  induction a generalizing b with
  | nil => cases b with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [zipWith_cons_cons, sum_cons, length_cons, Nat.add_eq] at *
      rw [ih ys (by omega)]
      omega

theorem hc_add_hf (x : ℕ) : hc x + hf x = x := by
  unfold hc hf; omega

theorem sum_map_hc_hf (l : List ℕ) : (l.map hc).sum + (l.map hf).sum = l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, sum_cons]
    have := hc_add_hf x
    omega

theorem sum_drop_append_zero (l : List ℕ) (j : ℕ) :
    ((l ++ [0]).drop j).sum = (l.drop j).sum := by
  by_cases h : j ≤ l.length
  · rw [drop_append_of_le_length h]; simp
  · have h1 : (l ++ [0]).length ≤ j := by simp; omega
    rw [drop_eq_nil_of_le h1, drop_eq_nil_of_le (by omega : l.length ≤ j)]

theorem sum_drop_cons_zero (l : List ℕ) (j : ℕ) :
    ((0 :: l).drop j).sum = (l.drop (j - 1)).sum := by
  cases j with
  | zero => simp
  | succ i => simp

theorem T_rawstep (c : List ℕ) (j : ℕ) :
    T (rawstep c) j = (T c (j - 1) + T c j) / 2 := by
  -- first, rewrite T (rawstep c) j
  have hlen : (c.map hc ++ [0]).length = (0 :: c.map hf).length := by simp
  have step1 : T (rawstep c) j
      = ((c.map hc ++ [0]).drop j).sum + ((0 :: c.map hf).drop j).sum := by
    unfold T rawstep
    rw [drop_zipWith,
      sum_zipWith_add _ _ (by rw [length_drop, length_drop, hlen])]
  rw [sum_drop_append_zero, sum_drop_cons_zero] at step1
  -- now: T (rawstep c) j = ((c.map hc).drop j).sum + ((c.map hf).drop (j-1)).sum
  rw [← map_drop, ← map_drop] at step1
  -- step1 : T (rawstep c) j = ((c.drop j).map hc).sum + ((c.drop (j-1)).map hf).sum
  rw [step1]
  unfold T
  -- goal: ((c.drop j).map hc).sum + ((c.drop (j-1)).map hf).sum
  --        = ((c.drop (j-1)).sum + (c.drop j).sum) / 2
  cases j with
  | zero =>
    simp only [Nat.zero_sub]
    have h1 := sum_map_hc_hf (c.drop 0)
    omega
  | succ i =>
    simp only [Nat.add_sub_cancel]
    rcases Nat.lt_or_ge i c.length with h | h
    · obtain ⟨e, hd⟩ : ∃ e, c.drop i = e :: c.drop (i+1) :=
        ⟨_, drop_eq_getElem_cons h⟩
      rw [hd]
      simp only [map_cons, sum_cons]
      have h1 := sum_map_hc_hf (c.drop (i+1))
      have h5 : hf e = e / 2 := rfl
      omega
    · rw [drop_eq_nil_of_le h, drop_eq_nil_of_le (by omega : c.length ≤ i + 1)]
      simp

theorem dropsum_append_zeros (a z : List ℕ) (hz : ∀ x ∈ z, x = 0) (j : ℕ) :
    ((a ++ z).drop j).sum = (a.drop j).sum := by
  by_cases h : j ≤ a.length
  · rw [drop_append_of_le_length h, sum_append, List.sum_eq_zero hz, Nat.add_zero]
  · rw [drop_eq_nil_of_le (by omega : a.length ≤ j)]
    have hj : j = a.length + (j - a.length) := by omega
    rw [hj, drop_length_add_append, List.sum_eq_zero, sum_nil]
    intro x hx
    exact hz x (mem_of_mem_drop hx)

theorem T_trim (l : List ℕ) (j : ℕ) : T (trim l) j = T l j := by
  have key : trim l ++ (l.reverse.takeWhile (· = 0)).reverse = l := by
    unfold trim
    rw [← reverse_append, takeWhile_append_dropWhile, reverse_reverse]
  have hz : ∀ x ∈ (l.reverse.takeWhile (· = 0)).reverse, x = 0 := by
    intro x hx
    rw [mem_reverse] at hx
    have := mem_takeWhile_imp hx
    simpa using this
  unfold T
  conv_rhs => rw [← key]
  rw [dropsum_append_zeros _ _ hz]

theorem T_step (c : List ℕ) (j : ℕ) :
    T (step c) j = (T c (j - 1) + T c j) / 2 := by
  unfold step
  rw [T_trim, T_rawstep]

theorem foldl_range_const {α : Type*} (f : α → α) (init : α) (t : ℕ) :
    (List.range t).foldl (fun acc _ => f acc) init = f^[t] init := by
  induction t generalizing init with
  | zero => simp
  | succ k ih =>
    rw [range_succ, foldl_append, ih]
    simp only [foldl_cons, foldl_nil]
    exact (Function.iterate_succ_apply' f k init).symm.trans
      (Function.iterate_succ_apply f k init)

/-- iterated state -/
def St (n t : ℕ) : List ℕ := step^[t] [n]

/-- cumulative (suffix-sum) state -/
def cum (n t j : ℕ) : ℕ := T (St n t) j

theorem cum_zero (n j : ℕ) : cum n 0 j = if j = 0 then n else 0 := by
  unfold cum St T
  simp only [Function.iterate_zero, id_eq]
  rcases j with _ | i
  · simp
  · simp

theorem cum_succ (n t j : ℕ) :
    cum n (t + 1) j = (cum n t (j - 1) + cum n t j) / 2 := by
  unfold cum St
  rw [Function.iterate_succ', Function.comp_apply, ← St, T_step]

theorem T_cons (a : ℕ) (c : List ℕ) (j : ℕ) : T (a :: c) (j + 1) = T c j := by
  unfold T; simp

theorem T_inj (n : ℕ) (c : List ℕ) (htf : c.getLast? ≠ some 0)
    (h : ∀ j, T c j = n - j) : c = replicate n 1 := by
  induction n generalizing c with
  | zero =>
    have hne' : c ≠ [] → False := by
      intro hne
      have hsum : c.sum = 0 := by have := h 0; simpa [T] using this
      have hmem : c.getLast hne ∈ c := getLast_mem hne
      have hz : c.getLast hne = 0 := List.sum_eq_zero_iff.mp hsum _ hmem
      apply htf
      rw [getLast?_eq_some_getLast hne, hz]
    rw [replicate_zero]
    by_contra hc
    exact hne' hc
  | succ m ih =>
    have hcne : c ≠ [] := by
      intro hc; subst hc; have := h 0; simp [T] at this
    cases c with
    | nil => exact absurd rfl hcne
    | cons a c' =>
      have h0 : a + c'.sum = m + 1 := by have := h 0; simpa [T] using this
      have h1 : c'.sum = m := by
        have := h 1; rw [T_cons] at this; simpa [T] using this
      have ha : a = 1 := by omega
      have htf' : c'.getLast? ≠ some 0 := by
        intro hcontra
        apply htf
        rw [getLast?_cons, hcontra]
        rfl
      have hc' : c' = replicate m 1 := by
        apply ih c' htf'
        intro j
        have := h (j + 1)
        rw [T_cons] at this
        simpa using this
      rw [ha, hc', replicate_succ]

theorem dropWhile_head_prop (p : ℕ → Bool) (l : List ℕ) (x : ℕ)
    (h : (l.dropWhile p).head? = some x) : p x = false := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hy : p y
    · rw [dropWhile_cons_of_pos hy] at h; exact ih h
    · rw [dropWhile_cons_of_neg (by simpa using hy)] at h
      simp only [head?_cons, Option.some.injEq] at h
      rw [← h]; simpa using hy

theorem trim_tzf (l : List ℕ) : (trim l).getLast? ≠ some 0 := by
  unfold trim
  rw [getLast?_reverse]
  intro h
  have := dropWhile_head_prop _ _ _ h
  simp at this

theorem St_tzf (n t : ℕ) (hn : n ≠ 0) : (St n t).getLast? ≠ some 0 := by
  cases t with
  | zero => unfold St; simp [hn]
  | succ k =>
    unfold St
    rw [Function.iterate_succ', Function.comp_apply]
    exact trim_tzf _

theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    a n = sInf {t | St n t = List.replicate n 1} := by
  unfold a
  rw [if_neg hn]
  refine congrArg sInf ?_
  ext k
  simp only [Set.mem_setOf_eq]
  rw [foldl_range_const]
  rfl

theorem T_replicate_one (n j : ℕ) : T (replicate n 1) j = n - j := by
  unfold T
  rw [drop_replicate]
  simp

/-- The cascade form of the stopping condition. -/
theorem a_eq_cum (n : ℕ) (hn : n ≠ 0) :
    a n = sInf {t | ∀ j, cum n t j = n - j} := by
  rw [a_eq n hn]
  refine congrArg sInf ?_
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h j
    rw [cum, h, T_replicate_one]
  · intro h
    apply T_inj n (St n t) (St_tzf n t hn)
    intro j
    have := h j
    rwa [cum] at this

/-- `cum` is non-increasing in `j`. -/
theorem cum_anti (n t j : ℕ) : cum n t (j + 1) ≤ cum n t j := by
  induction t generalizing j with
  | zero =>
    rw [cum_zero, cum_zero]
    split <;> split <;> omega
  | succ t ih =>
    rw [cum_succ, cum_succ, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h0 := ih 0
      simp only [Nat.zero_sub]
      omega
    · have h1 := ih j
      have hb : cum n t j ≤ cum n t (j - 1) := by
        have := ih (j - 1); rwa [Nat.sub_add_cancel hj] at this
      omega

/-- `cum` is bounded by the target `n - j`. -/
theorem cum_le (n t j : ℕ) : cum n t j ≤ n - j := by
  induction t generalizing j with
  | zero => rw [cum_zero]; split <;> omega
  | succ t ih =>
    rw [cum_succ]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp; have := ih 0; omega
    · have h1 := ih (j - 1)
      have h2 := ih j
      have hj1 : n - (j - 1) = (n - j) + 1 ∨ n - j = 0 := by omega
      omega

/-- Deficit: `D n t j = (n - j) - cum n t j`. -/
def Dd (n t j : ℕ) : ℕ := (n - j) - cum n t j

theorem Dd_zero (n j : ℕ) : Dd n 0 j = if j = 0 then 0 else n - j := by
  unfold Dd
  rw [cum_zero]
  split <;> omega

theorem Dd_succ (n t j : ℕ) :
    Dd n (t + 1) j = (Dd n t (j - 1) + Dd n t j) / 2 := by
  unfold Dd
  rw [cum_succ]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have h2 := cum_le n t 0
    simp only [Nat.zero_sub, Nat.sub_zero]
    omega
  · have h1 := cum_le n t (j - 1)
    have h2 := cum_le n t j
    have h3 : n - (j - 1) = (n - j) + 1 ∨ (n - j = 0 ∧ n - (j - 1) = 0) := by omega
    omega

theorem Dd_bound (n t j : ℕ) : Dd n t j ≤ n - j := by
  unfold Dd; omega

theorem Dd_zero_of_ge (n t j : ℕ) (h : n ≤ j) : Dd n t j = 0 := by
  have := Dd_bound n t j; omega

/-- The boundary cell `j = 0` is always zero (mass conservation). -/
theorem Dd_at_zero (n t : ℕ) : Dd n t 0 = 0 := by
  induction t with
  | zero => rw [Dd_zero]; simp
  | succ t ih =>
    have hs : Dd n (t+1) 0 = (Dd n t 0 + Dd n t 0) / 2 := Dd_succ n t 0
    rw [hs, ih]

/-- Monotone coupling between systems `n` and `n+1`. -/
theorem Dd_sandwich (n : ℕ) : ∀ t j,
    Dd n t j ≤ Dd (n+1) t j ∧ Dd (n+1) t j ≤ Dd n t j + 1 := by
  intro t
  induction t with
  | zero =>
    intro j
    by_cases hj : j = 0
    · subst hj; simp [Dd_zero]
    · simp only [Dd_zero, if_neg hj]; omega
  | succ t ih =>
    intro j
    have ih1 := ih (j-1)
    have ih2 := ih j
    rw [Dd_succ n t j, Dd_succ (n+1) t j]
    omega

/-- ZERO-PREFIX: zeros propagate to the left (within `[1, n-1]`). -/
theorem Dd_zp (n : ℕ) : ∀ t j, 1 ≤ j → j ≤ n - 1 → Dd n t j = 0 →
    Dd n t (j - 1) = 0 := by
  intro t
  induction t with
  | zero =>
    intro j hj1 hj2 h
    rw [Dd_zero] at h
    rw [if_neg (show ¬ (j = 0) by omega)] at h
    omega
  | succ t ih =>
    intro j hj1 hj2 h
    rw [Dd_succ] at h
    have hsum : Dd n t (j-1) + Dd n t j ≤ 1 := by omega
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rw [show j - 1 = 0 by omega]
      exact Dd_at_zero n (t+1)
    · have hd1 : Dd n t (j-1) = 0 := by
        by_contra hne
        have hj0 : Dd n t j = 0 := by omega
        exact hne (ih j hj1 hj2 hj0)
      have hd2 : Dd n t (j-2) = 0 := by
        have h2 := ih (j-1) (by omega) (by omega) hd1
        rwa [show (j-1)-1 = j-2 by omega] at h2
      rw [Dd_succ, show (j-1)-1 = j-2 by omega, hd2, hd1]

/-- INV: `D^{n+1}` is drained one cell to the left of `D^n`'s drained prefix. -/
theorem Dd_inv (n : ℕ) : ∀ t j, j + 1 ≤ n - 1 → Dd n t (j+1) = 0 →
    Dd (n+1) t j = 0 := by
  intro t
  induction t with
  | zero =>
    intro j hj h
    rw [Dd_zero] at h
    rw [if_neg (show ¬ (j + 1 = 0) by omega)] at h
    omega
  | succ t ih =>
    intro j hj h
    rw [Dd_succ] at h
    simp only [Nat.add_sub_cancel] at h
    have hsum : Dd n t j + Dd n t (j+1) ≤ 1 := by omega
    have hzj : Dd n t j = 0 := by
      rcases Nat.eq_zero_or_pos (Dd n t (j+1)) with h0 | hp
      · exact Dd_zp n t (j+1) (by omega) (by omega) h0
      · omega
    rcases Nat.eq_zero_or_pos j with hj0 | hjp
    · subst hj0; exact Dd_at_zero (n+1) (t+1)
    · rw [Dd_succ]
      have e1 : Dd (n+1) t (j-1) = 0 := by
        have := ih (j-1) (by omega) (by rw [show (j-1)+1 = j by omega]; exact hzj)
        exact this
      have e2 : Dd (n+1) t j ≤ 1 := by
        have := (Dd_sandwich n t j).2; omega
      rw [e1]; omega

/-- If the last relevant cell `n-1` is drained, the whole row is drained. -/
theorem Dd_drained_of_last (n t : ℕ) (hn : 1 ≤ n) (h : Dd n t (n-1) = 0) :
    ∀ j, Dd n t j = 0 := by
  have key : ∀ k, k ≤ n - 1 → Dd n t (n - 1 - k) = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using h
    | succ k ihk =>
      intro hk
      have hprev := ihk (by omega)
      have := Dd_zp n t (n-1-k) (by omega) (by omega) hprev
      rwa [show (n-1-k)-1 = n-1-(k+1) by omega] at this
  intro j
  rcases Nat.lt_or_ge j n with hjn | hjn
  · have hjeq : j = n - 1 - (n - 1 - j) := by omega
    rw [hjeq]; exact key (n-1-j) (by omega)
  · exact Dd_zero_of_ge n t j hjn

theorem stab_iff_cum (n t : ℕ) :
    (∀ j, cum n t j = n - j) ↔ (∀ j, Dd n t j = 0) := by
  constructor
  · intro h j; unfold Dd; rw [h]; omega
  · intro h j
    have hj := h j
    unfold Dd at hj
    have hb := cum_le n t j
    omega

theorem a_eq_stab (n : ℕ) (hn : n ≠ 0) :
    a n = sInf {t | ∀ j, Dd n t j = 0} := by
  rw [a_eq_cum n hn]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  exact stab_iff_cum n t

theorem a_eq_last (n : ℕ) (hn : 1 ≤ n) :
    a n = sInf {t | Dd n t (n-1) = 0} := by
  rw [a_eq_stab n (by omega)]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; exact h (n-1)
  · intro h; exact Dd_drained_of_last n t hn h

/-- The upper-bound drain: from a drained `D^n` at time `A`, `D^{n+1}` drains
its critical cell `n` two steps later. -/
theorem upper_drain (n : ℕ) (hn : 1 ≤ n) (A : ℕ) (hA : ∀ j, Dd n A j = 0) :
    Dd (n+1) (A+2) n = 0 := by
  have hlast : Dd n A (n-1) = 0 := hA (n-1)
  have hterm1 : Dd (n+1) A ((n-1)-1) = 0 := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rw [show (n-1)-1 = 0 by omega]; exact Dd_at_zero (n+1) A
    · rw [show (n-1)-1 = n-2 by omega]
      exact Dd_inv n A (n-2) (by omega)
        (by rw [show (n-2)+1 = n-1 by omega]; exact hlast)
  have hterm2 : Dd (n+1) A (n-1) ≤ 1 := by
    have := (Dd_sandwich n A (n-1)).2; omega
  have hmid : Dd (n+1) (A+1) (n-1) = 0 := by
    rw [Dd_succ, hterm1]; omega
  have hn1 : Dd (n+1) (A+1) n ≤ 1 := by
    have hs := (Dd_sandwich n (A+1) n).2
    have hz : Dd n (A+1) n = 0 := Dd_zero_of_ge n (A+1) n (by omega)
    omega
  have hfin : Dd (n+1) (A+2) n = (Dd (n+1) (A+1) (n-1) + Dd (n+1) (A+1) n) / 2 :=
    Dd_succ (n+1) (A+1) n
  rw [hfin, hmid]; omega

/-- Nonemptiness: every system eventually drains. -/
theorem NE (n : ℕ) (hn : 1 ≤ n) : ∃ t, ∀ j, Dd n t j = 0 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact ⟨0, by intro j; rw [Dd_zero]; split <;> omega⟩
    · obtain ⟨A, hA⟩ := ih hm
      refine ⟨A+2, Dd_drained_of_last (m+1) (A+2) (by omega) ?_⟩
      exact upper_drain m hm A hA

/-- The main increment bound. -/
theorem main_increment (n : ℕ) (hn : 1 ≤ n) :
    a (n+1) = a n + 1 ∨ a (n+1) = a n + 2 := by
  have hSne : {t | Dd n t (n-1) = 0}.Nonempty := by
    obtain ⟨t, ht⟩ := NE n hn; exact ⟨t, ht (n-1)⟩
  have hAlast : a n = sInf {t | Dd n t (n-1) = 0} := a_eq_last n hn
  have hAmem : Dd n (a n) (n-1) = 0 := by rw [hAlast]; exact Nat.sInf_mem hSne
  have hAdrain : ∀ j, Dd n (a n) j = 0 := Dd_drained_of_last n (a n) hn hAmem
  have hlt : ∀ t, t < a n → Dd n t (n-1) ≠ 0 := by
    intro t ht hcontra
    have hle := Nat.sInf_le (show t ∈ {t | Dd n t (n-1) = 0} from hcontra)
    rw [← hAlast] at hle
    omega
  have hlow : ∀ t, t ≤ a n → 1 ≤ Dd (n+1) t n := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Dd_zero]
      rw [if_neg (show ¬ (n = 0) by omega)]
      omega
    | succ t iht =>
      intro hsucc
      have htA : t < a n := by omega
      have iht' := iht (by omega)
      rw [Dd_succ]
      have h1 : 1 ≤ Dd n t (n-1) := by
        have := hlt t htA; have hb := Dd_bound n t (n-1); omega
      have h2 : Dd n t (n-1) ≤ Dd (n+1) t (n-1) := (Dd_sandwich n t (n-1)).1
      omega
  have hSne1 : {t | Dd (n+1) t n = 0}.Nonempty := by
    obtain ⟨t, ht⟩ := NE (n+1) (by omega); exact ⟨t, ht n⟩
  have hA1last : a (n+1) = sInf {t | Dd (n+1) t n = 0} := a_eq_last (n+1) (by omega)
  have hge : a n + 1 ≤ a (n+1) := by
    rw [hA1last]
    by_contra hcon
    push_neg at hcon
    have hmem : Dd (n+1) (sInf {t | Dd (n+1) t n = 0}) n = 0 := Nat.sInf_mem hSne1
    have hle : sInf {t | Dd (n+1) t n = 0} ≤ a n := by omega
    have := hlow _ hle
    omega
  have hle2 : a (n+1) ≤ a n + 2 := by
    rw [hA1last]
    exact Nat.sInf_le
      (show (a n + 2) ∈ {t | Dd (n+1) t n = 0} from upper_drain n hn (a n) hAdrain)
  omega

end A300997


/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  exact A300997.main_increment n hn
