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

lemma dropWhile_append_singleton_of_neg {α} (p : α → Bool) :
    ∀ (l : List α) {x : α}, ¬ p x → (l ++ [x]).dropWhile p = l.dropWhile p ++ [x]
| [], x, hx => by simp [hx]
| y::ys, x, hx => by
  by_cases hy : p y
  · simp [List.dropWhile, hy, dropWhile_append_singleton_of_neg p ys hx]
  · simp [List.dropWhile, hy]

noncomputable def trim0 (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

lemma trim0_nil : trim0 [] = [] := by simp [trim0]

lemma trim0_single (x : ℕ) : trim0 [x] = if x = 0 then [] else [x] := by
  by_cases hx : x = 0 <;> simp [trim0, hx]

lemma trim0_cons_pos {x : ℕ} {l : List ℕ} (hx : x ≠ 0) : trim0 (x::l) = x :: trim0 l := by
  unfold trim0
  rw [show (x :: l).reverse = l.reverse ++ [x] by simp]
  rw [dropWhile_append_singleton_of_neg (fun x : ℕ => x = 0) l.reverse]
  · simp
  · simpa using hx

noncomputable def origAux (carry : ℕ) (config : List ℕ) : List ℕ :=
  trim0 (List.zipWith Nat.add (config.map (fun m => (m + 1) / 2) ++ [0]) (carry :: config.map (fun m => m / 2)))

noncomputable def origStep (config : List ℕ) : List ℕ := origAux 0 config

def stepAux : ℕ → List ℕ → List ℕ
| carry, [] => if carry = 0 then [] else [carry]
| carry, m :: ms => (carry + (m + 1) / 2) :: stepAux (m / 2) ms

def rStep (config : List ℕ) : List ℕ := stepAux 0 config

def allPos : List ℕ → Prop
| [] => True
| x::xs => 0 < x ∧ allPos xs

lemma origAux_nil (carry : ℕ) : origAux carry [] = stepAux carry [] := by
  by_cases h : carry = 0 <;> simp [origAux, stepAux, trim0_single, h]

lemma head_pos {carry m : ℕ} (hm : 0 < m) : carry + (m+1)/2 ≠ 0 := by
  have : 0 < (m + 1) / 2 := by omega
  omega

lemma origAux_eq_stepAux_of_allPos : ∀ {config : List ℕ} {carry : ℕ}, allPos config → origAux carry config = stepAux carry config
| [], carry, h => origAux_nil carry
| m::ms, carry, h => by
  have hm : 0 < m := h.1
  have hms : allPos ms := h.2
  unfold origAux stepAux
  simp [List.zipWith]
  rw [show (m + 1) / 2 + carry = carry + (m + 1) / 2 by omega]
  rw [trim0_cons_pos (head_pos (carry := carry) hm)]
  exact congrArg (fun t => (carry + (m + 1) / 2) :: t) (origAux_eq_stepAux_of_allPos hms)

lemma origStep_eq_rStep_of_allPos {config : List ℕ} (h : allPos config) : origStep config = rStep config := by
  unfold origStep rStep
  exact origAux_eq_stepAux_of_allPos h


lemma stepAux_allPos : ∀ {config : List ℕ} {carry : ℕ}, allPos config → allPos (stepAux carry config)
| [], carry, h => by
  by_cases hc : carry = 0
  · simp [stepAux, hc, allPos]
  · simp [stepAux, hc, allPos]
    omega
| m::ms, carry, h => by
  have hm : 0 < m := h.1
  have hms : allPos ms := h.2
  simp [stepAux]
  constructor
  · have : 0 < (m + 1) / 2 := by omega
    omega
  · exact stepAux_allPos hms

lemma rStep_allPos {config : List ℕ} (h : allPos config) : allPos (rStep config) := by
  unfold rStep
  exact stepAux_allPos h

lemma length_le_stepAux : ∀ {config : List ℕ} {carry : ℕ}, allPos config → config.length ≤ (stepAux carry config).length
| [], carry, h => by
  by_cases hc : carry = 0 <;> simp [stepAux, hc]
| m::ms, carry, h => by
  have hms : allPos ms := h.2
  simp [stepAux]
  exact length_le_stepAux hms





def addAt : List ℕ → ℕ → List ℕ
| [], 0 => [1]
| [], p+1 => 0 :: addAt [] p
| x::xs, 0 => (x+1)::xs
| x::xs, p+1 => x :: addAt xs p

lemma addAt_ne_nil : ∀ (c : List ℕ) (p : ℕ), p ≤ c.length → addAt c p ≠ []
| [], p, hp => by
  have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
  subst p
  simp [addAt]
| x::xs, 0, hp => by simp [addAt]
| x::xs, p+1, hp => by simp [addAt]


def nextP (c : List ℕ) (p : ℕ) : ℕ := p + if c.getD p 0 % 2 = 1 then 1 else 0

lemma addAt_zero_cons (x : ℕ) (xs : List ℕ) : addAt (x::xs) 0 = (x+1)::xs := by rfl
lemma addAt_succ_cons (x : ℕ) (xs : List ℕ) (p : ℕ) : addAt (x::xs) (p+1) = x :: addAt xs p := by rfl

lemma ceil_inc_even {m : ℕ} (h : m % 2 = 0) : (m + 1 + 1) / 2 = (m + 1) / 2 + 1 := by
  have he : Even m := Nat.even_iff.mpr h
  rcases he with ⟨k, rfl⟩
  omega

lemma floor_inc_even {m : ℕ} (h : m % 2 = 0) : (m + 1) / 2 = m / 2 := by
  have he : Even m := Nat.even_iff.mpr h
  rcases he with ⟨k, rfl⟩
  omega

lemma ceil_inc_odd {m : ℕ} (h : m % 2 = 1) : (m + 1 + 1) / 2 = (m + 1) / 2 := by
  have ho : Odd m := Nat.odd_iff.mpr h
  rcases ho with ⟨k, rfl⟩
  omega

lemma floor_inc_odd {m : ℕ} (h : m % 2 = 1) : (m + 1) / 2 = m / 2 + 1 := by
  have ho : Odd m := Nat.odd_iff.mpr h
  rcases ho with ⟨k, rfl⟩
  omega

lemma mod2_zero_or_one (m : ℕ) : m % 2 = 0 ∨ m % 2 = 1 := by omega

lemma stepAux_carry_succ : ∀ (c : List ℕ) (carry : ℕ),
    stepAux (carry + 1) c = addAt (stepAux carry c) 0
| [], carry => by
  by_cases h : carry = 0
  · simp [stepAux, addAt, h]
  · simp [stepAux, addAt, h]
| m::ms, carry => by
  simp [stepAux, addAt]
  omega


lemma stepAux_addAt : ∀ {c : List ℕ} {p carry : ℕ}, p ≤ c.length →
    stepAux carry (addAt c p) = addAt (stepAux carry c) (p + if c.getD p 0 % 2 = 1 then 1 else 0)
| [], p, carry, hp => by
  have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
  subst p
  by_cases h : carry = 0 <;> simp [addAt, stepAux, h]
| m::ms, 0, carry, hp => by
  simp [addAt, stepAux]
  cases mod2_zero_or_one m with
  | inl h0 =>
    have hc := ceil_inc_even h0
    have hf := floor_inc_even h0
    simp [h0, hc, hf, addAt]
    omega
  | inr h1 =>
    have hc := ceil_inc_odd h1
    have hf := floor_inc_odd h1
    simp [h1, hc, hf, addAt]
    exact stepAux_carry_succ ms (m / 2)
| m::ms, p+1, carry, hp => by
  have hp' : p ≤ ms.length := Nat.succ_le_succ_iff.mp hp
  simp [addAt, stepAux]
  rw [stepAux_addAt (c := ms) (p := p) (carry := m/2) hp']
  by_cases hpar : (ms[p]?.getD 0) % 2 = 1
  · simp [hpar, addAt, Nat.add_assoc]
  · simp [hpar, addAt, Nat.add_assoc]

lemma rStep_addAt {c : List ℕ} {p : ℕ} (hp : p ≤ c.length) :
    rStep (addAt c p) = addAt (rStep c) (nextP c p) := by
  unfold rStep nextP
  exact stepAux_addAt (c := c) (p := p) (carry := 0) hp


def pref : List ℕ → ℕ
| [] => 0
| x::xs => if x = 1 then pref xs + 1 else 0

def GoodInv (c : List ℕ) (p : ℕ) : Prop :=
  p ≤ c.length ∧ pref c ≤ p + 2 ∧ (c.getD (pref c) 0 = 2 → pref c ≤ p + 1)

lemma pref_le_length : ∀ c : List ℕ, pref c ≤ c.length
| [] => by simp [pref]
| x::xs => by
  by_cases hx : x = 1
  · simp [pref, hx]
    exact pref_le_length xs
  · simp [pref, hx]

lemma GoodInv_preserve : ∀ {c : List ℕ} {p : ℕ}, allPos c → GoodInv c p → GoodInv (rStep c) (nextP c p) := by
  intro c
  induction c with
  | nil =>
    intro p hp hi
    have hp0 : p = 0 := Nat.eq_zero_of_le_zero hi.1
    subst p
    simp [GoodInv, rStep, nextP, stepAux, pref]
  | cons x xs ih =>
    intro p hp hi
    cases p with
    | zero =>
      simp [GoodInv, nextP, rStep, stepAux] at hi ⊢
      have hxpos : 0 < x := hp.1
      by_cases hx1 : x = 1
      · subst x
        simp [pref] at hi ⊢
        cases xs with
        | nil => simp [stepAux, pref]
        | cons y ys =>
          have hypos : 0 < y := hp.2.1
          by_cases hy1 : y = 1
          · subst y
            simp [pref] at hi ⊢
            cases ys with
            | nil => simp [stepAux, pref]
            | cons z zs =>
              have hzpos : 0 < z := hp.2.2.1
              have hprefys : pref (z :: zs) = 0 := by omega
              have hznot2 : ¬ z = 2 := by
                intro hz2
                have hget : (z :: zs)[pref (z :: zs)]?.getD 0 = 2 := by simp [hz2, pref]
                have := hi.2 hget
                omega
              have hznot1 : ¬ z = 1 := by
                intro hz1
                simp [pref, hz1] at hprefys
              have hzceil : (z + 1) / 2 ≠ 1 := by omega
              simp [stepAux, pref, hzceil]
          · by_cases hy2 : y = 2
            · subst y
              cases ys with
              | nil => simp [stepAux, pref]
              | cons z zs =>
                have hzpos : 0 < z := hp.2.2.1
                simp [stepAux, pref]
                have hnot : ¬ z + 1 < 2 := by omega
                simp [hnot]
            · have hyceil : (y + 1) / 2 ≠ 1 := by omega
              simp [stepAux, pref, hyceil]
      · by_cases hx2 : x = 2
        · subst x
          cases xs with
          | nil => simp [pref, stepAux]
          | cons y ys =>
            have hypos : 0 < y := hp.2.1
            simp [pref, stepAux]
            have hnot : ¬ y + 1 < 2 := by omega
            simp [hnot]
            intro _
            omega
        · have hxceil : (x + 1) / 2 ≠ 1 := by omega
          simp [pref, hxceil]
          by_cases hodd : x % 2 = 1 <;> simp [hodd] <;> omega
    | succ p =>
      simp [GoodInv, nextP, rStep, stepAux] at hi ⊢
      have hxspos : allPos xs := hp.2
      by_cases hx1 : x = 1
      · subst x
        simp [pref] at hi ⊢
        have hgi : GoodInv xs p := by
          constructor
          · exact hi.1
          constructor
          · omega
          · intro hget
            have := hi.2.2 hget
            omega
        have hih := ih hxspos hgi
        simp [GoodInv, rStep, nextP] at hih
        rcases hih with ⟨hlen, hpref, hcond⟩
        constructor
        · omega
        constructor
        · omega
        · intro hget
          have := hcond hget
          omega
      · by_cases hx2 : x = 2
        · subst x
          have hlen0 := length_le_stepAux (config := xs) (carry := 1) hxspos
          constructor
          · by_cases hpar : (xs[p]?.getD 0) % 2 = 1
            · have hplt : p < xs.length := by
                by_contra hnot
                have hp_eq : p = xs.length := by omega
                subst p
                simp at hpar
              simp [hpar]
              omega
            · simp [hpar]
              omega
          cases xs with
          | nil => simp [pref, stepAux]
          | cons y ys =>
            have hypos : 0 < y := hxspos.1
            simp [pref, stepAux]
            have hnot : ¬ y + 1 < 2 := by omega
            simp [hnot]
        · have hxceil : (x + 1) / 2 ≠ 1 := by omega
          simp [pref, hxceil]
          have hlen0 := length_le_stepAux (config := xs) (carry := x / 2) hxspos
          by_cases hpar : (xs[p]?.getD 0) % 2 = 1
          · have hplt : p < xs.length := by
              by_contra hnot
              have hp_eq : p = xs.length := by omega
              subst p
              simp at hpar
            simp [hpar]
            omega
          · simp [hpar]
            omega


def State (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => rStep acc) [n]

def PosSeq (n : ℕ) : ℕ → ℕ
| 0 => 0
| t+1 => nextP (State n t) (PosSeq n t)

lemma State_zero (n : ℕ) : State n 0 = [n] := by simp [State]

lemma State_succ (n t : ℕ) : State n (t+1) = rStep (State n t) := by
  unfold State
  rw [List.range_succ]
  simp [List.foldl_append]

lemma allPos_single {n : ℕ} (hn : 0 < n) : allPos [n] := by simp [allPos, hn]

lemma State_allPos {n t : ℕ} (hn : 0 < n) : allPos (State n t) := by
  induction t with
  | zero => simp [State_zero, allPos, hn]
  | succ t ih => rw [State_succ]; exact rStep_allPos ih

lemma PosSeq_good {n t : ℕ} (hn : 0 < n) : GoodInv (State n t) (PosSeq n t) := by
  induction t with
  | zero =>
    simp [State_zero, PosSeq, GoodInv]
    by_cases h1 : n = 1
    · subst n
      simp [pref]
    · have hpref : pref [n] = 0 := by simp [pref, h1]
      simp [hpref]
  | succ t ih =>
    rw [State_succ]
    change GoodInv (rStep (State n t)) (nextP (State n t) (PosSeq n t))
    exact GoodInv_preserve (State_allPos hn) ih

lemma State_couple {n t : ℕ} (hn : 0 < n) :
    State (n+1) t = addAt (State n t) (PosSeq n t) := by
  induction t with
  | zero => simp [State_zero, PosSeq, addAt]
  | succ t ih =>
    rw [State_succ, State_succ, ih]
    have hg := PosSeq_good (n := n) (t := t) hn
    exact rStep_addAt hg.1


lemma pref_replicate_one (n : ℕ) : pref (List.replicate n 1) = n := by
  induction n with
  | zero => simp [pref]
  | succ n ih =>
    change (if (1:ℕ) = 1 then pref (List.replicate n 1) + 1 else 0) = n + 1
    simp [ih]

lemma p_near_of_good_replicate {n p : ℕ} (hg : GoodInv (List.replicate n 1) p) :
    p = n ∨ p + 1 = n ∨ p + 2 = n := by
  have hp_le : p ≤ n := by simpa [GoodInv] using hg.1
  have hp_ge : n ≤ p + 2 := by
    have := hg.2.1
    simpa [pref_replicate_one] using this
  omega

lemma rStep_replicate (n : ℕ) : rStep (List.replicate n 1) = List.replicate n 1 := by
  induction n with
  | zero => simp [rStep, stepAux]
  | succ n ih =>
    change (1 :: rStep (List.replicate n 1)) = 1 :: List.replicate n 1
    rw [ih]

lemma rStep_pre_stable (n : ℕ) : rStep (List.replicate n 1 ++ [2]) = List.replicate (n+2) 1 := by
  induction n with
  | zero => simp [rStep, stepAux]
  | succ n ih =>
    change (1 :: rStep (List.replicate n 1 ++ [2])) = 1 :: List.replicate (n+2) 1
    rw [ih]

lemma rStep_pre2 (n : ℕ) : rStep (List.replicate n 1 ++ [2,1]) = List.replicate (n+1) 1 ++ [2] := by
  induction n with
  | zero => simp [rStep, stepAux]
  | succ n ih =>
    change (1 :: rStep (List.replicate n 1 ++ [2,1])) = 1 :: (List.replicate (n+1) 1 ++ [2])
    rw [ih]

lemma addAt_replicate_end (n : ℕ) : addAt (List.replicate n 1) n = List.replicate (n+1) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 :: addAt (List.replicate n 1) n = 1 :: List.replicate (n+1) 1
    rw [ih]

lemma addAt_replicate_pred (n : ℕ) : addAt (List.replicate (n+1) 1) n = List.replicate n 1 ++ [2] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 :: addAt (List.replicate (n+1) 1) n = 1 :: (List.replicate n 1 ++ [2])
    rw [ih]

lemma addAt_replicate_pred2 (n : ℕ) : addAt (List.replicate (n+2) 1) n = List.replicate n 1 ++ [2,1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 :: addAt (List.replicate (n+2) 1) n = 1 :: (List.replicate n 1 ++ [2,1])
    rw [ih]

lemma stable_next_two {n t : ℕ} (hn : 0 < n) (hst : State n t = List.replicate n 1) :
    State (n+1) (t+2) = List.replicate (n+1) 1 := by
  rw [show t+2 = (t+1)+1 by omega, State_succ, State_succ]
  rw [State_couple hn, hst]
  have hg := PosSeq_good (n := n) (t := t) hn
  rw [hst] at hg
  rcases p_near_of_good_replicate hg with hp | hp | hp
  · rw [hp]
    rw [addAt_replicate_end, rStep_replicate, rStep_replicate]
  · have hp' : PosSeq n t = n - 1 := by omega
    rw [hp']
    cases n with
    | zero => omega
    | succ m =>
      simp at hp'
      rw [show Nat.succ m - 1 = m by omega]
      rw [addAt_replicate_pred, rStep_pre_stable, rStep_replicate]
  · have hp' : PosSeq n t = n - 2 := by omega
    rw [hp']
    cases n with
    | zero => omega
    | succ n1 =>
      cases n1 with
      | zero =>
        simp at hp
      | succ m =>
        rw [show Nat.succ (Nat.succ m) - 2 = m by omega]
        change rStep (rStep (addAt (List.replicate (m+2) 1) m)) = List.replicate (m+3) 1
        rw [addAt_replicate_pred2, rStep_pre2, rStep_pre_stable]


lemma exists_State_stable : ∀ {n : ℕ}, 0 < n → ∃ t, State n t = List.replicate n 1
| 0, hn => by omega
| 1, hn => by use 0; simp [State_zero]
| Nat.succ (Nat.succ n), hn => by
  have hprev : 0 < Nat.succ n := by omega
  rcases exists_State_stable hprev with ⟨t, ht⟩
  use t + 2
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using stable_next_two hprev ht

lemma addAt_eq_replicate_succ : ∀ (c : List ℕ) (p N : ℕ), allPos c → p ≤ c.length →
    addAt c p = List.replicate (N+1) 1 → c = List.replicate N 1
| [], p, N, hc, hp, h => by
  have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
  subst p
  cases N with
  | zero => rfl
  | succ N =>
    have hl : 1 = N + 2 := by simpa [addAt] using congrArg List.length h
    have contra : False := by omega
    exact False.elim contra
| x::xs, 0, N, hc, hp, h => by
  cases N with
  | zero =>
    change (x+1)::xs = [1] at h
    injection h with hx hxs
    have hxpos : 0 < x := hc.1
    have contra : False := by omega
    exact False.elim contra
  | succ N =>
    change (x+1)::xs = 1 :: List.replicate (N+1) 1 at h
    injection h with hx hxs
    have hxpos : 0 < x := hc.1
    have contra : False := by omega
    exact False.elim contra
| x::xs, p+1, 0, hc, hp, h => by
  simp [addAt] at h
  exact False.elim ((addAt_ne_nil xs p (Nat.succ_le_succ_iff.mp hp)) h.2)
| x::xs, p+1, Nat.succ N, hc, hp, h => by
  change x :: addAt xs p = 1 :: List.replicate (N+1) 1 at h
  injection h with hx htail
  have hp' : p ≤ xs.length := Nat.succ_le_succ_iff.mp hp
  have hxs := addAt_eq_replicate_succ xs p N hc.2 hp' htail
  subst x
  rw [hxs]
  rfl

lemma stable_of_next_stable {n k : ℕ} (hn : 0 < n)
    (h : State (n+1) k = List.replicate (n+1) 1) :
    State n k = List.replicate n 1 := by
  rw [State_couple hn] at h
  have hg := PosSeq_good (n := n) (t := k) hn
  exact addAt_eq_replicate_succ (State n k) (PosSeq n k) n (State_allPos hn) hg.1 h


lemma stepAux_one_eq_replicate : ∀ {c : List ℕ} {n : ℕ}, allPos c → stepAux 1 c = List.replicate n 1 → c = [] ∧ n = 1
| [], n, hc, h => by
  cases n with
  | zero => simp [stepAux] at h
  | succ n =>
    cases n with
    | zero => simp [stepAux]
    | succ n =>
      have hl : 1 = n + 2 := by simpa [stepAux] using congrArg List.length h
      have contra : False := by omega
      exact False.elim contra
| x::xs, n, hc, h => by
  cases n with
  | zero => simp [stepAux] at h
  | succ n =>
    change (1 + (x + 1) / 2) :: stepAux (x / 2) xs = 1 :: List.replicate n 1 at h
    injection h with hxhead _
    have hxpos : 0 < x := hc.1
    have contra : False := by omega
    exact False.elim contra

lemma rStep_preimage_replicate : ∀ {c : List ℕ} {n : ℕ}, allPos c → rStep c = List.replicate n 1 →
    c = List.replicate n 1 ∨ ∃ k, n = k + 2 ∧ c = List.replicate k 1 ++ [2]
| [], n, hc, h => by
  cases n with
  | zero => left; rfl
  | succ n => simp [rStep, stepAux] at h
| x::xs, n, hc, h => by
  cases n with
  | zero => simp [rStep, stepAux] at h
  | succ n =>
    change stepAux 0 (x::xs) = 1 :: List.replicate n 1 at h
    simp [stepAux] at h
    have hxhead : (x + 1) / 2 = 1 := h.1
    have htail : stepAux (x / 2) xs = List.replicate n 1 := h.2
    have hxpos : 0 < x := hc.1
    have hxcase : x = 1 ∨ x = 2 := by omega
    rcases hxcase with hx1 | hx2
    · subst x
      have htail0 : rStep xs = List.replicate n 1 := by simpa [rStep] using htail
      rcases rStep_preimage_replicate hc.2 htail0 with hs | hs
      · left
        rw [hs]
        rfl
      · rcases hs with ⟨k, hn, hxs⟩
        right
        refine ⟨k+1, ?_, ?_⟩
        · omega
        · rw [hxs]
          rfl
    · subst x
      have hs := stepAux_one_eq_replicate hc.2 (by simpa using htail)
      rcases hs with ⟨hxs, hn⟩
      subst xs
      subst n
      right
      refine ⟨0, by simp, by simp [rStep]⟩

lemma addAt_replicate_eq_end {n p : ℕ} (hp : p ≤ n)
    (h : addAt (List.replicate n 1) p = List.replicate (n+1) 1) : p = n := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases p with
    | zero =>
      change 2 :: List.replicate n 1 = 1 :: List.replicate (n+1) 1 at h
      injection h with hhead _
      omega
    | succ p =>
      change 1 :: addAt (List.replicate n 1) p = 1 :: List.replicate (n+1) 1 at h
      injection h with _ htail
      have hp' : p ≤ n := Nat.succ_le_succ_iff.mp hp
      have := ih hp' htail
      omega

lemma pref_replicate_append_two (k : ℕ) : pref (List.replicate k 1 ++ [2]) = k := by
  induction k with
  | zero => simp [pref]
  | succ k ih =>
    change (if (1:ℕ)=1 then pref (List.replicate k 1 ++ [2]) + 1 else 0) = k + 1
    simp [ih]



lemma nextP_pre_stable_ne_end (k p : ℕ)
    (hg : GoodInv (List.replicate k 1 ++ [2]) p) :
    nextP (List.replicate k 1 ++ [2]) p ≠ k + 2 := by
  have hp_le : p ≤ k + 1 := by simpa [GoodInv] using hg.1
  have hp_ge : k ≤ p + 1 := by
    have := hg.2.2
    have hget : (List.replicate k 1 ++ [2]).getD (pref (List.replicate k 1 ++ [2])) 0 = 2 := by
      rw [pref_replicate_append_two]
      simp
    have hk := this hget
    simpa [pref_replicate_append_two] using hk
  by_cases hp_eq_end : p = k + 1
  · subst p
    simp [nextP]
  · have hp_lt_end : p < k + 1 := by omega
    have hcases : p = k ∨ p + 1 = k := by omega
    rcases hcases with hp_eq | hp_eq
    · subst p
      simp [nextP]
    · have hp_eq' : p = k - 1 := by omega
      subst p
      cases k with
      | zero => simp at hp_eq
      | succ k =>
        simp [nextP]


noncomputable def A (n : ℕ) : ℕ := sInf {t : ℕ | State n t = List.replicate n 1}

lemma A_mem {n : ℕ} (hn : 0 < n) : State n (A n) = List.replicate n 1 := by
  unfold A
  exact Nat.sInf_mem (exists_State_stable hn)

lemma A_le_of_stable {n t : ℕ} (h : State n t = List.replicate n 1) : A n ≤ t := by
  unfold A
  exact Nat.sInf_le h

lemma A_one : A 1 = 0 := by
  unfold A
  rw [Nat.sInf_eq_zero]
  left
  simp [State_zero]

lemma A_pos {n : ℕ} (hn : 1 < n) : 0 < A n := by
  by_contra h0
  have hA0 : A n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h0)
  have hm := A_mem (by omega : 0 < n)
  rw [hA0, State_zero] at hm
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      have hl : 1 = n + 2 := by simpa using congrArg List.length hm
      omega

lemma not_stable_next_at_A {n : ℕ} (hn : 0 < n) :
    State (n+1) (A n) ≠ List.replicate (n+1) 1 := by
  intro hnext
  have hbase := A_mem hn
  rw [State_couple hn, hbase] at hnext
  have hg := PosSeq_good (n := n) (t := A n) hn
  rw [hbase] at hg
  have hp_le_n : PosSeq n (A n) ≤ n := by simpa using hg.1
  have hp_end : PosSeq n (A n) = n := addAt_replicate_eq_end hp_le_n hnext
  cases n with
  | zero => omega
  | succ n0 =>
    cases n0 with
    | zero =>
      rw [A_one] at hp_end
      simp [PosSeq] at hp_end
    | succ m =>
      have hApos : 0 < A (Nat.succ (Nat.succ m)) := A_pos (by omega)
      let u := A (Nat.succ (Nat.succ m)) - 1
      have hAsucc : A (Nat.succ (Nat.succ m)) = u + 1 := by omega
      have hprev_step : rStep (State (Nat.succ (Nat.succ m)) u) = List.replicate (Nat.succ (Nat.succ m)) 1 := by
        rw [← State_succ, ← hAsucc]
        exact A_mem (by omega)
      have hprev_not : State (Nat.succ (Nat.succ m)) u ≠ List.replicate (Nat.succ (Nat.succ m)) 1 := by
        intro hs
        have Ale := A_le_of_stable hs
        omega
      have hpre := rStep_preimage_replicate (State_allPos (n := Nat.succ (Nat.succ m)) (t := u) (by omega)) hprev_step
      rcases hpre with hstable | hpre2
      · exact hprev_not hstable
      · rcases hpre2 with ⟨k, hkN, hstate⟩
        have hk : k = m := by omega
        subst k
        have hposrec : PosSeq (Nat.succ (Nat.succ m)) (u+1) =
            nextP (State (Nat.succ (Nat.succ m)) u) (PosSeq (Nat.succ (Nat.succ m)) u) := by rfl
        rw [← hAsucc] at hposrec
        rw [hp_end] at hposrec
        rw [hstate] at hposrec
        have hgprev := PosSeq_good (n := Nat.succ (Nat.succ m)) (t := u) (by omega)
        rw [hstate] at hgprev
        have hne := nextP_pre_stable_ne_end m (PosSeq (Nat.succ (Nat.succ m)) u) hgprev
        omega

lemma A_next_gt (n : ℕ) (hn : 0 < n) : A n < A (n+1) := by
  have hnext := A_mem (by omega : 0 < n+1)
  have hbase := stable_of_next_stable hn hnext
  have Ale : A n ≤ A (n+1) := A_le_of_stable hbase
  have hneq : A (n+1) ≠ A n := by
    intro heq
    have hbad := not_stable_next_at_A hn
    rw [← heq] at hbad
    exact hbad hnext
  omega

lemma A_next_le_two (n : ℕ) (hn : 0 < n) : A (n+1) ≤ A n + 2 := by
  exact A_le_of_stable (stable_next_two hn (A_mem hn))

lemma A_diff_one_or_two (n : ℕ) (hn : 0 < n) : A (n+1) = A n + 1 ∨ A (n+1) = A n + 2 := by
  have hgt := A_next_gt n hn
  have hle := A_next_le_two n hn
  omega


noncomputable def test_a (n : ℕ) : ℕ :=
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

noncomputable def OState (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => origStep acc) [n]

lemma OState_succ (n t : ℕ) : OState n (t+1) = origStep (OState n t) := by
  unfold OState
  rw [List.range_succ]
  simp [List.foldl_append]

lemma OState_eq_State {n t : ℕ} (hn : 0 < n) : OState n t = State n t := by
  induction t with
  | zero => simp [OState, State]
  | succ t ih =>
    rw [OState_succ, State_succ, ih]
    rw [origStep_eq_rStep_of_allPos (State_allPos hn)]

lemma test_a_eq_A {n : ℕ} (hn : 0 < n) : test_a n = A n := by
  unfold test_a A
  have hnz : ¬ n = 0 := by omega
  simp [hnz]
  apply congrArg sInf
  ext k
  change OState n k = List.replicate n 1 ↔ State n k = List.replicate n 1
  rw [OState_eq_State hn]


lemma a_eq_A {n : ℕ} (hn : 0 < n) : a n = A n := by
  unfold a A
  have hnz : ¬ n = 0 := by omega
  simp [hnz]
  apply congrArg sInf
  ext k
  change OState n k = List.replicate n 1 ↔ State n k = List.replicate n 1
  rw [OState_eq_State hn]

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  have hnpos : 0 < n := by omega
  have hA := A_diff_one_or_two n hnpos
  rw [a_eq_A hnpos, a_eq_A (by omega : 0 < n+1)]
  exact hA
