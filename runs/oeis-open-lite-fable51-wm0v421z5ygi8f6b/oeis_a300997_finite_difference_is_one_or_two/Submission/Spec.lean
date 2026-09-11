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

/-- function-level step -/
def F (g : ℕ → ℕ) : ℕ → ℕ := fun i => (g i + 1) / 2 + (if i = 0 then 0 else g (i - 1) / 2)

def ind (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

def delta (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

def c (n t : ℕ) : ℕ → ℕ := F^[t] (delta n)

def P (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => P n t + (c n t (P n t)) % 2

lemma c_zero (n : ℕ) : c n 0 = delta n := rfl
lemma c_succ (n t : ℕ) : c n (t+1) = F (c n t) := Function.iterate_succ_apply' F t (delta n)

lemma P_zero (n : ℕ) : P n 0 = 0 := rfl
lemma P_succ (n t : ℕ) : P n (t+1) = P n t + (c n t (P n t)) % 2 := rfl

lemma P_mono (n t : ℕ) : P n t ≤ P n (t+1) := by rw [P_succ]; omega
lemma P_succ_le (n t : ℕ) : P n (t+1) ≤ P n t + 1 := by rw [P_succ]; omega

def Pos (g : ℕ → ℕ) : Prop := ∀ i, g i = 0 → g (i+1) = 0

lemma Pos.ge {g : ℕ → ℕ} (h : Pos g) {i j : ℕ} (hij : i ≤ j) (hi : g i = 0) : g j = 0 := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j _ ih => exact h j ih

lemma Pos_F {g : ℕ → ℕ} (h : Pos g) : Pos (F g) := by
  intro i hi
  simp only [F] at hi ⊢
  have h1 : g i = 0 := by omega
  have h2 : g (i+1) = 0 := h i h1
  simp [h2, h1]

lemma Pos_delta (n : ℕ) : Pos (delta n) := by
  intro i hi
  simp [delta]

lemma Pos_c (n t : ℕ) : Pos (c n t) := by
  induction t with
  | zero => exact Pos_delta n
  | succ t ih => rw [c_succ]; exact Pos_F ih

def addChip (g : ℕ → ℕ) (p : ℕ) : ℕ → ℕ := fun i => g i + if i = p then 1 else 0

lemma F_addChip (g : ℕ → ℕ) (p : ℕ) : F (addChip g p) = addChip (F g) (p + g p % 2) := by
  funext i
  simp only [F, addChip]
  by_cases hip : i = p
  · subst hip
    by_cases h0 : i = 0
    · subst h0; simp; split_ifs <;> omega
    · simp only [h0, if_false]
      have : i - 1 ≠ i := by omega
      simp only [this, if_false, add_zero]
      split_ifs <;> omega
  · by_cases hip1 : i = p + 1
    · subst hip1
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true]
      simp only [hip, if_false, add_zero]
      split_ifs <;> omega
    · by_cases h0 : i = 0
      · subst h0
        simp only [if_true]
        have : (0:ℕ) ≠ p + g p % 2 := by omega
        simp [hip, this]
      · have : i - 1 ≠ p := by omega
        have h3 : i ≠ p + g p % 2 := by omega
        simp [h0, hip, this, h3]

lemma c_succ_n (n t : ℕ) : c (n+1) t = addChip (c n t) (P n t) := by
  induction t with
  | zero =>
    funext i
    simp only [c_zero, P_zero, delta, addChip]
    split_ifs <;> omega
  | succ t ih =>
    rw [c_succ, ih, F_addChip, ← c_succ, P_succ]

lemma F_ind (m : ℕ) : F (ind m) = ind m := by
  funext i
  simp only [F, ind]
  split_ifs <;> omega

lemma c_fixed {n m T : ℕ} (h : c n T = ind m) {s : ℕ} (hs : T ≤ s) : c n s = ind m := by
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => rw [c_succ, ih, F_ind]

lemma ind_inj {a b : ℕ} (h : ind a = ind b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := congrFun h a
    simp [ind, hlt] at this
  · have := congrFun h b
    simp [ind, hgt] at this

lemma P_le {n t : ℕ} (h : c n t = ind n) : P n t ≤ n := by
  by_contra hP
  push_neg at hP
  have hpos := Pos_c (n+1) t
  rw [c_succ_n, h] at hpos
  have h1 : addChip (ind n) (P n t) n = 0 := by
    simp only [addChip, ind]
    have : n ≠ P n t := by omega
    simp [this]
  have h2 := hpos.ge hP.le h1
  simp [addChip] at h2

lemma P_move {n t : ℕ} (h : c n t = ind n) (hP : P n t < n) : P n (t+1) = P n t + 1 := by
  rw [P_succ, h]
  simp [ind, hP]

lemma P_ride {n T : ℕ} (h : c n T = ind n) : ∀ j, j ≤ n - P n T → P n (T + j) = P n T + j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ n - P n T := by omega
    have := ih hj'
    rw [← add_assoc, P_move (c_fixed h (by omega)) (by omega), this]
    omega

lemma terminates : ∀ n, ∃ T, c n T = ind n := by
  intro n
  induction n with
  | zero => exact ⟨0, by funext i; simp [c_zero, delta, ind]⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T + (n - P n T), ?_⟩
    rw [c_succ_n, c_fixed hT (by omega), P_ride hT _ le_rfl]
    have := P_le hT
    have h2 : P n T + (n - P n T) = n := by omega
    rw [h2]
    funext i
    simp only [addChip, ind]
    split_ifs <;> omega



lemma step_cases {g : ℕ → ℕ} (hg : Pos g) {i : ℕ} (h1 : ∀ i' < i, g i' = 1) (hi : g i ≠ 1) :
    (F g i ≠ 1) ∨ (F g (i+1) ≠ 1) ∨
      (g i = 2 ∧ (∀ j, i + 1 ≤ j → g j = 0) ∧ F g = ind (i + 2)) := by
  have hprev : i ≠ 0 → g (i-1) = 1 := fun h => h1 (i-1) (by omega)
  rcases Nat.eq_zero_or_pos (g i) with h0 | hpos
  · -- g i = 0
    left
    simp only [F, h0]
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have := hprev (by omega); simp [this]
  · have hm : 2 ≤ g i := by omega
    rcases Nat.eq_zero_or_pos (g (i+1)) with h0' | hpos'
    · -- g (i+1) = 0
      have hzero : ∀ j, i + 1 ≤ j → g j = 0 := fun j hj => hg.ge hj h0'
      rcases (show g i = 2 ∨ g i = 3 ∨ 4 ≤ g i by omega) with h2 | h3 | h4
      · right; right
        refine ⟨h2, hzero, ?_⟩
        funext j
        simp only [F, ind]
        rcases lt_trichotomy j i with hj | hj | hj
        · have hj1 := h1 j hj
          by_cases hj0 : j = 0
          · subst hj0; simp [hj1]
          · have hj2 := h1 (j-1) (by omega)
            simp [hj0, hj1, hj2]; omega
        · subst hj
          rcases Nat.eq_zero_or_pos j with h | h
          · subst h; simp [h2]
          · have := hprev (by omega)
            have : j ≠ 0 := by omega
            simp [this, ‹g (j-1) = 1›, h2]
        · by_cases hj1 : j = i + 1
          · subst hj1; simp [h0', h2]
          · have hz : g j = 0 := hzero j (by omega)
            have hz' : g (j-1) = 0 := hzero (j-1) (by omega)
            have hj0 : j ≠ 0 := by omega
            have hj2 : ¬ j < i + 2 := by omega
            simp [hz, hz', hj0, hj2]
      · left
        simp only [F, h3]
        rcases Nat.eq_zero_or_pos i with h | h
        · simp [h]
        · have := hprev (by omega); simp [this]
      · right; left
        simp only [F, h0']
        simp; omega
    · right; left
      simp only [F]
      simp; omega

lemma pred {g : ℕ → ℕ} {n : ℕ} (hg : Pos g) (hF : F g = ind n) (hne : g ≠ ind n) :
    2 ≤ n ∧ (∀ i, i < n - 2 → g i = 1) ∧ g (n-2) = 2 ∧ (∀ i, n - 1 ≤ i → g i = 0) := by
  have hex : ∃ i, g i ≠ 1 := by
    by_contra hall
    push_neg at hall
    have : F g = fun _ => 1 := by
      funext i; simp only [F, hall]; split_ifs <;> simp
    rw [hF] at this
    have := congrFun this n
    simp [ind] at this
  classical
  obtain ⟨i, hi, h1⟩ : ∃ i, g i ≠ 1 ∧ ∀ i' < i, g i' = 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i' hi' => by
      have := Nat.find_min hex hi'; push_neg at this; exact this⟩
  -- auxiliary: if n ≤ i then contradiction
  have hFn : F g n = 0 := by rw [hF]; simp [ind]
  have hgn : g n = 0 := by simp only [F] at hFn; omega
  have hni : i ≤ n := by
    by_contra hlt; push_neg at hlt
    have := h1 n hlt; omega
  have hi_ne_n : i ≠ n := by
    intro heq
    apply hne
    funext j
    simp only [ind]
    split_ifs with hj
    · exact h1 j (heq ▸ hj)
    · exact hg.ge (by omega) hgn
  have hin : i < n := lt_of_le_of_ne hni hi_ne_n
  rcases step_cases hg h1 hi with h | h | ⟨h2, hz, hFi⟩
  · exfalso; apply h; rw [hF]; simp [ind, hin]
  · exfalso
    have hi1 : i + 1 = n := by
      by_contra hne'
      apply h; rw [hF]; simp [ind]; omega
    subst hi1
    have hFi : F g i = 1 := by rw [hF]; simp [ind]
    have hgi : g i = 2 := by
      simp only [F] at hFi
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp at hFi; omega
      · have : g (i-1) = 1 := h1 (i-1) (by omega)
        have : i ≠ 0 := by omega
        simp [this, ‹g (i-1) = 1›] at hFi; omega
    simp only [F] at hFn
    simp [hgi] at hFn
  · have hn : n = i + 2 := ind_inj (hF.symm.trans hFi)
    subst hn
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro j hj; exact h1 j (by omega)
    · simpa using h2
    · intro j hj; exact hz j (by omega)

/-- The main invariant. -/
def Inv (n t : ℕ) : Prop :=
  (c n t ≠ ind n ∧ ∃ i ≤ P n t + 1, c n t i ≠ 1) ∨ (c n t = ind n ∧ n ≤ P n t + 2)

lemma Inv_zero (n : ℕ) : Inv n 0 := by
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h | h | h
  · right; subst h
    refine ⟨?_, by simp⟩
    funext i; simp [c_zero, delta, ind]
  · right; subst h
    refine ⟨?_, by simp⟩
    funext i; simp only [c_zero, delta, ind]; split_ifs <;> omega
  · left
    refine ⟨?_, 0, by simp, ?_⟩
    · intro heq
      have := congrFun heq 0
      simp [c_zero, delta, ind, show 0 < n by omega] at this; omega
    · simp [c_zero, delta]; omega

lemma key_le {n t i : ℕ} (hi : i ≤ P n t + 1) (h1 : ∀ i' < i, c n t i' = 1) : i ≤ P n (t+1) := by
  rcases eq_or_lt_of_le hi with heq | hlt
  · have := h1 (P n t) (by omega)
    rw [P_succ, this]; omega
  · have := P_mono n t; omega

lemma Inv_succ (n t : ℕ) (h : Inv n t) : Inv n (t+1) := by
  rcases h with ⟨hne, hex⟩ | ⟨heq, hP⟩
  · classical
    obtain ⟨i, hi, hi1, h1⟩ : ∃ i, i ≤ P n t + 1 ∧ c n t i ≠ 1 ∧ ∀ i' < i, c n t i' = 1 := by
      have hex' : ∃ i, c n t i ≠ 1 := by obtain ⟨i, _, hi⟩ := hex; exact ⟨i, hi⟩
      refine ⟨Nat.find hex', ?_, Nat.find_spec hex', fun i' hi' => by
        have := Nat.find_min hex' hi'; push_neg at this; exact this⟩
      obtain ⟨j, hj, hj1⟩ := hex
      exact le_trans (Nat.find_min' hex' hj1) hj
    have hle : i ≤ P n (t+1) := key_le hi h1
    rcases step_cases (Pos_c n t) h1 hi1 with hc | hc | ⟨_, _, hc⟩
    · rw [← c_succ] at hc
      by_cases hfin : c n (t+1) = ind n
      · right; refine ⟨hfin, ?_⟩
        rw [hfin] at hc
        have : ¬ i < n := by intro hlt; apply hc; simp [ind, hlt]
        omega
      · left; exact ⟨hfin, i, by omega, hc⟩
    · rw [← c_succ] at hc
      by_cases hfin : c n (t+1) = ind n
      · right; refine ⟨hfin, ?_⟩
        rw [hfin] at hc
        have : ¬ i + 1 < n := by intro hlt; apply hc; simp [ind, hlt]
        omega
      · left; exact ⟨hfin, i + 1, by omega, hc⟩
    · rw [← c_succ] at hc
      obtain ⟨T, hT⟩ := terminates n
      have e1 : c n (max T (t+1)) = ind n := c_fixed hT (le_max_left _ _)
      have e2 : c n (max T (t+1)) = ind (i+2) := c_fixed hc (le_max_right _ _)
      have hn : n = i + 2 := ind_inj (e1.symm.trans e2)
      right
      refine ⟨hc.trans (by rw [hn]), by omega⟩
  · right
    refine ⟨by rw [c_succ, heq, F_ind], ?_⟩
    have := P_mono n t; omega

lemma Inv_all (n t : ℕ) : Inv n t := by
  induction t with
  | zero => exact Inv_zero n
  | succ t ih => exact Inv_succ n t ih

lemma P_ge {n t : ℕ} (h : c n t = ind n) : n ≤ P n t + 2 := by
  rcases Inv_all n t with ⟨hne, _⟩ | ⟨_, hP⟩
  · exact absurd h hne
  · exact hP

lemma P_upper {n t : ℕ} (hne : c n t ≠ ind n) (h : c n (t+1) = ind n) : P n (t+1) + 1 ≤ n := by
  obtain ⟨hn2, h1, h2, h3⟩ := pred (Pos_c n t) (c_succ n t ▸ h) hne
  have hPt : P n t ≤ n - 1 := by
    by_contra hP; push_neg at hP
    have hpos := Pos_c (n+1) t
    rw [c_succ_n] at hpos
    have e1 : addChip (c n t) (P n t) (n-1) = 0 := by
      simp only [addChip, h3 (n-1) le_rfl]
      have : n - 1 ≠ P n t := by omega
      simp [this]
    have e2 := hpos.ge (by omega : n - 1 ≤ P n t) e1
    simp [addChip] at e2
  rcases eq_or_lt_of_le hPt with heq | hlt
  · rw [P_succ, heq, h3 (n-1) le_rfl]; simp; omega
  · have := P_succ_le n t; omega



def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def trim (l : List ℕ) : List ℕ := (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
def ca_step (config : List ℕ) : List ℕ :=
  trim (List.zipWith Nat.add (config.map half_ceil ++ [0]) (0 :: config.map half_floor))
def S (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) [n]

lemma a_eq (n : ℕ) : a n = if n = 0 then 0 else sInf {k | S n k = List.replicate n 1} := rfl

lemma S_zero (n : ℕ) : S n 0 = [n] := rfl
lemma S_succ (n t : ℕ) : S n (t+1) = ca_step (S n t) := by
  simp [S, List.range_succ, List.foldl_append]

def G (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

lemma G_append_zeros (l : List ℕ) (k : ℕ) : G (l ++ List.replicate k 0) = G l := by
  funext i
  simp only [G]
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h]
    simp [List.getElem_append_left h]
  · push_neg at h
    rw [List.getD_eq_default _ _ h]
    by_cases h2 : i < l.length + k
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp [List.getElem_append_right h]
    · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma trim_spec (l : List ℕ) : ∃ k, l = trim l ++ List.replicate k 0 := by
  have h := List.takeWhile_append_dropWhile (p := fun x : ℕ => decide (x = 0)) (l := l.reverse)
  have hrep : List.takeWhile (fun x : ℕ => decide (x = 0)) l.reverse =
      List.replicate (List.takeWhile (fun x : ℕ => decide (x = 0)) l.reverse).length 0 := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have := List.mem_takeWhile_imp hb
    simpa using this
  refine ⟨(List.takeWhile (fun x : ℕ => decide (x = 0)) l.reverse).length, ?_⟩
  simp only [trim]
  conv_lhs => rw [← List.reverse_reverse l, ← h, hrep]
  rw [List.reverse_append, List.reverse_replicate]

lemma G_trim (l : List ℕ) : G (trim l) = G l := by
  obtain ⟨k, hk⟩ := trim_spec l
  conv_rhs => rw [hk]
  rw [G_append_zeros]

def NTZ (l : List ℕ) : Prop := l.getLast? ≠ some 0

lemma NTZ_trim (l : List ℕ) : NTZ (trim l) := by
  simp only [NTZ, trim, List.getLast?_reverse]
  by_cases h : List.dropWhile (fun x : ℕ => decide (x = 0)) l.reverse = []
  · rw [h]; simp
  · rw [List.head?_eq_some_head h]
    have := List.head_dropWhile_not (fun x : ℕ => decide (x = 0)) h
    simpa using this

lemma G_inj {l l' : List ℕ} (h : NTZ l) (h' : NTZ l') (hG : G l = G l') : l = l' := by
  have aux : ∀ {l l' : List ℕ}, NTZ l' → G l = G l' → l.length < l'.length → False := by
    intro l l' h' hG hlt
    have hne' : l' ≠ [] := by intro h; simp [h] at hlt
    apply h'
    rw [List.getLast?_eq_some_getLast hne', List.getLast_eq_getElem]
    have := congrFun hG (l'.length - 1)
    simp only [G] at this
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    rw [← this]
  have hlen : l.length = l'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact aux h' hG hlt
    · exact aux h hG.symm hgt
  apply List.ext_getElem hlen
  intro i h1 h2
  have := congrFun hG i
  simp only [G] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

lemma G_zipWith_add (A B : List ℕ) (hAB : A.length = B.length) (i : ℕ) :
    G (List.zipWith Nat.add A B) i = G A i + G B i := by
  simp only [G]
  by_cases h : i < A.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
      List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
    rfl
  · push_neg at h
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

lemma G_map_of_zero (f : ℕ → ℕ) (hf : f 0 = 0) (l : List ℕ) (i : ℕ) :
    G (l.map f) i = f (G l i) := by
  simp only [G]
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h, List.getElem_map]
  · push_neg at h
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h, hf]

lemma G_cons (x : ℕ) (L : List ℕ) (i : ℕ) : G (x :: L) i = if i = 0 then x else G L (i - 1) := by
  cases i with
  | zero => simp [G]
  | succ i => simp [G]

lemma G_ca_step (l : List ℕ) : G (ca_step l) = F (G l) := by
  funext i
  simp only [ca_step]
  rw [G_trim, G_zipWith_add _ _ (by simp)]
  have h1 : G (l.map half_ceil ++ [0]) i = half_ceil (G l i) := by
    have := G_append_zeros (l.map half_ceil) 1
    simp only [List.replicate_one] at this
    rw [this, G_map_of_zero _ (by simp [half_ceil])]
  rw [h1, G_cons]
  simp only [F, half_ceil]
  split_ifs
  · rfl
  · rw [G_map_of_zero _ (by simp [half_floor])]; rfl

lemma G_replicate (m : ℕ) : G (List.replicate m 1) = fun i => if i < m then 1 else 0 := by
  funext i
  simp only [G]
  by_cases h : i < m
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

lemma NTZ_replicate (m : ℕ) : NTZ (List.replicate m 1) := by
  simp only [NTZ]
  cases m with
  | zero => simp
  | succ m => simp [List.getLast?_replicate]

lemma NTZ_S {n : ℕ} (hn : n ≠ 0) (t : ℕ) : NTZ (S n t) := by
  cases t with
  | zero => simp [S_zero, NTZ, hn]
  | succ t => rw [S_succ]; exact NTZ_trim _


lemma S_eq_iff {n : ℕ} (hn : n ≠ 0) (t m : ℕ) : S n t = List.replicate m 1 ↔ c n t = ind m := by
  have hG : G (S n t) = c n t := by
    induction t with
    | zero => funext i; simp [S_zero, G, c_zero, delta]; cases i <;> simp
    | succ t ih => rw [S_succ, G_ca_step, ih, c_succ]
  have hind : G (List.replicate m 1) = ind m := G_replicate m
  constructor
  · intro h; rw [← hG, h, hind]
  · intro h; exact G_inj (NTZ_S hn t) (NTZ_replicate m) (by rw [hG, h, hind])

theorem main (n : ℕ) (hn : 1 ≤ n) : a (n+1) = a n + 1 ∨ a (n+1) = a n + 2 := by
  have hn0 : n ≠ 0 := by omega
  rw [a_eq, a_eq, if_neg hn0, if_neg (Nat.succ_ne_zero n)]
  set T := sInf {k | S n k = List.replicate n 1} with hT
  have hne : {k | S n k = List.replicate n 1}.Nonempty := by
    obtain ⟨T0, h⟩ := terminates n
    exact ⟨T0, (S_eq_iff hn0 T0 n).2 h⟩
  have hTmem : c n T = ind n := (S_eq_iff hn0 T n).1 (Nat.sInf_mem hne)
  have hTmin : ∀ k, c n k = ind n → T ≤ k := fun k hk => Nat.sInf_le ((S_eq_iff hn0 k n).2 hk)
  have hlow : n ≤ P n T + 2 := P_ge hTmem
  have hup : P n T + 1 ≤ n := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0, P_zero]; omega
    · obtain ⟨t, ht⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
      have hct : c n t ≠ ind n := fun h => absurd (hTmin t h) (by omega)
      rw [ht] at hTmem ⊢
      exact P_upper hct hTmem
  have key : sInf {k | S (n+1) k = List.replicate (n+1) 1} = T + (n - P n T) := by
    apply le_antisymm
    · apply Nat.sInf_le
      show S (n+1) (T + (n - P n T)) = List.replicate (n+1) 1
      rw [S_eq_iff (Nat.succ_ne_zero n), c_succ_n, c_fixed hTmem (by omega), P_ride hTmem _ le_rfl]
      have h2 : P n T + (n - P n T) = n := by omega
      rw [h2]; funext i; simp only [addChip, ind]; split_ifs <;> omega
    · apply le_csInf
      · obtain ⟨T1, h⟩ := terminates (n+1)
        exact ⟨T1, (S_eq_iff (Nat.succ_ne_zero n) T1 (n+1)).2 h⟩
      · intro k hk
        simp only [Set.mem_setOf_eq] at hk
        rw [S_eq_iff (Nat.succ_ne_zero n), c_succ_n] at hk
        by_contra hlt; push_neg at hlt
        have hPk : P n k = n := by
          have h1 := congrFun hk (P n k)
          have h2 := congrFun hk n
          simp only [addChip, ind] at h1 h2
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt
          · have e0 : c n k (P n k) = 0 := by
              simp only [if_true, show P n k < n + 1 by omega] at h1; omega
            have := (Pos_c n k).ge hlt'.le e0
            have hne' : n ≠ P n k := by omega
            simp only [hne', if_false, add_zero, show n < n + 1 by omega, if_true] at h2
            omega
          · simp only [if_true, show ¬ P n k < n + 1 by omega, if_false] at h1
            omega
        have hck : c n k = ind n := by
          funext i
          have := congrFun hk i
          simp only [addChip, ind, hPk] at this ⊢
          split_ifs at this ⊢ <;> omega
        have hTk := hTmin k hck
        have := P_ride hTmem (k - T) (by omega)
        rw [show T + (k - T) = k by omega] at this
        omega
  rw [key]
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
  exact A300997.main n hn

theorem oeis_a300997_finite_difference_is_one_or_two.disproof : ¬ (type_of% @oeis_a300997_finite_difference_is_one_or_two) := sorry
