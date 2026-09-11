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

/-!
We use a recursive version of the update, with an incoming mass `b`.
The following argument has three ingredients:
* adjacent initial masses remain related by the addition of one unit;
* configurations consist of leading ones, a block of masses at least two,
  and at most one trailing one (unless already stable);
* every positive configuration eventually stabilizes.
The recursive update is then identified with the update in `a`.
-/
namespace CA

def flow (b : ℕ) : List ℕ → List ℕ
  | [] => if b = 0 then [] else [b]
  | x :: xs => ((x + 1) / 2 + b) :: flow (x / 2) xs

def step := flow 0

def Pos (l : List ℕ) : Prop := ∀ x ∈ l, 0 < x

def Ones (l : List ℕ) : Prop := ∀ x ∈ l, x = 1

@[simp] theorem flow_nil (b : ℕ) : flow b [] = if b = 0 then [] else [b] := rfl
@[simp] theorem flow_cons (b x : ℕ) (xs : List ℕ) :
    flow b (x :: xs) = ((x + 1) / 2 + b) :: flow (x / 2) xs := rfl
@[simp] theorem step_nil : step [] = [] := rfl
@[simp] theorem step_one (xs : List ℕ) : step (1 :: xs) = 1 :: step xs := rfl
@[simp] theorem pos_cons (x : ℕ) (xs : List ℕ) : Pos (x :: xs) ↔ 0 < x ∧ Pos xs := by
  simp [Pos]
@[simp] theorem pos_nil : Pos [] := by simp [Pos]
@[simp] theorem ones_cons (x : ℕ) (xs : List ℕ) : Ones (x :: xs) ↔ x = 1 ∧ Ones xs := by
  simp [Ones]
@[simp] theorem ones_nil : Ones [] := by simp [Ones]

theorem flow_pos {l : List ℕ} (h : Pos l) (b : ℕ) : Pos (flow b l) := by
  induction l generalizing b with
  | nil =>
    simp only [flow_nil]
    split <;> simp_all
    omega
  | cons x xs ih =>
    rw [pos_cons] at h
    simp only [flow_cons, pos_cons]
    exact ⟨by omega, ih h.2 _⟩

theorem flow_sum (b : ℕ) (l : List ℕ) : (flow b l).sum = b + l.sum := by
  induction l generalizing b with
  | nil => simp only [flow_nil]; split <;> simp_all
  | cons x xs ih => simp only [flow_cons, List.sum_cons, ih]; omega

theorem ones_eq {l : List ℕ} (h : Ones l) : l = List.replicate l.sum 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨rfl, hx⟩ := (ones_cons _ _).mp h
    simpa [Nat.add_comm, List.replicate_succ] using congrArg (1 :: ·) (ih hx)

theorem ones_replicate (n : ℕ) : Ones (List.replicate n 1) := by simp [Ones]

theorem step_replicate (n : ℕ) : step (List.replicate n 1) = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (1 :: ·) ih

/-- One unit is added to a cell, or a new last cell of mass one is appended. -/
inductive Extra : List ℕ → List ℕ → Prop
  | nil : Extra [] [1]
  | head (x : ℕ) (xs : List ℕ) : Extra (x :: xs) ((x+1) :: xs)
  | cons (x : ℕ) {xs ys : List ℕ} : Extra xs ys → Extra (x :: xs) (x :: ys)

theorem extra_nonempty {xs ys : List ℕ} (h : Extra xs ys) : ys ≠ [] := by cases h <;> simp

theorem extra_pos {xs ys : List ℕ} (h : Extra xs ys) (hp : Pos xs) : Pos ys := by
  induction h with
  | nil => simp
  | head x xs => simp_all
  | cons x h ih => simp_all

theorem flow_extra_carry (b : ℕ) (xs : List ℕ) : Extra (flow b xs) (flow (b+1) xs) := by
  cases xs with
  | nil =>
    by_cases hb : b = 0
    · simp [hb]; exact Extra.nil
    · simp [hb]; exact Extra.head b []
  | cons x xs =>
    simp only [flow_cons]
    convert Extra.head ((x+1)/2+b) (flow (x/2) xs) using 1

theorem flow_extra {xs ys : List ℕ} (h : Extra xs ys) (b : ℕ) :
    Extra (flow b xs) (flow b ys) := by
  induction h generalizing b with
  | nil =>
    by_cases hb : b = 0
    · simp [hb]; exact Extra.nil
    · simp [hb, Nat.add_comm]; exact Extra.head b []
  | head x xs =>
    simp only [flow_cons]
    have hd : (x+1)/2 = x/2 ∨ (x+1)/2 = x/2+1 := by omega
    rcases hd with hd | hd
    · have hc : (x+1+1)/2 = (x+1)/2+1 := by omega
      rw [hc, hd]
      convert Extra.head (x/2+b) (flow (x/2) xs) using 1
      congr 1
      omega
    · have hc : (x+1+1)/2 = (x+1)/2 := by omega
      rw [hc]
      apply Extra.cons
      rw [hd]
      exact flow_extra_carry _ _
  | cons x h ih => exact Extra.cons _ (ih _)

/-- A block of masses at least two, with at most one final one. -/
inductive Core : List ℕ → Prop
  | nil : Core []
  | one : Core [1]
  | cons {x : ℕ} {xs : List ℕ} : 2 ≤ x → Core xs → Core (x :: xs)

/-- The shape invariant: an arbitrary prefix of ones followed by a core. -/
inductive Nice : List ℕ → Prop
  | core {xs : List ℕ} : Core xs → Nice xs
  | one {xs : List ℕ} : Nice xs → Nice (1 :: xs)

theorem core_tail {x : ℕ} {xs : List ℕ} (h : Core (x::xs)) : Core xs := by
  cases h with
  | one => exact Core.nil
  | cons _ ht => exact ht

theorem nice_tail {x : ℕ} {xs : List ℕ} (h : Nice (x::xs)) : Nice xs := by
  cases h with
  | core h => exact Nice.core (core_tail h)
  | one h => exact h

theorem core_flow {xs : List ℕ} (h : Core xs) {b : ℕ} (hb : 1 ≤ b) : Core (flow b xs) := by
  induction h generalizing b with
  | nil =>
    simp only [flow_nil, if_neg (by omega : b ≠ 0)]
    by_cases h : b = 1
    · subst b; exact Core.one
    · exact Core.cons (by omega) Core.nil
  | one =>
    simp only [flow_cons, flow_nil]
    exact Core.cons (by omega) Core.nil
  | @cons x xs hx ht ih =>
    simp only [flow_cons]
    exact Core.cons (by omega) (ih (by omega))

theorem nice_step {xs : List ℕ} (h : Nice xs) : Nice (step xs) := by
  induction h with
  | one h ih => rw [step_one]; exact Nice.one ih
  | @core xs h =>
    cases h with
    | nil => exact Nice.core Core.nil
    | one => exact Nice.one (Nice.core Core.nil)
    | @cons x xs hx ht =>
      change Nice (((x+1)/2+0) :: flow (x/2) xs)
      have hc := core_flow ht (by omega : 1 ≤ x/2)
      by_cases h : (x+1)/2+0 = 1
      · rw [h]; exact Nice.one (Nice.core hc)
      · exact Nice.core (Core.cons (by omega) hc)

theorem core_one_tail {xs : List ℕ} (h : Core (1 :: xs)) : xs = [] := by
  cases h with
  | one => rfl
  | cons hx _ => omega

theorem nice_two_replicate {n : ℕ} (h : Nice (2 :: List.replicate n 1)) : n ≤ 1 := by
  cases h with
  | core h =>
    have ht := core_tail h
    cases n with
    | zero => omega
    | succ n =>
      rw [List.replicate_succ] at ht
      have hz := congrArg List.length (core_one_tail ht)
      simp only [List.length_replicate, List.length_nil] at hz
      omega

/-- An extra unit on a stable configuration of the invariant shape
needs at most two more updates. -/
theorem extra_ones_two {n : ℕ} {ys : List ℕ}
    (h : Extra (List.replicate n 1) ys) (hn : Nice ys) :
    step (step ys) = List.replicate (n+1) 1 := by
  induction n generalizing ys with
  | zero =>
    cases h
    rfl
  | succ n ih =>
    rw [List.replicate_succ] at h
    cases h with
    | head =>
      have hn' := nice_two_replicate hn
      interval_cases n <;> rfl
    | cons x h =>
      simpa [List.replicate_succ] using congrArg (1 :: ·) (ih h (nice_tail hn))


theorem ones_flow_carry {xs : List ℕ} (hp : Pos xs) {b : ℕ} (hb : 1 ≤ b)
    (h : Ones (flow b xs)) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have hx := (pos_cons _ _).mp hp
    have hy := (ones_cons _ _).mp h
    omega

/-- If the larger configuration becomes stable in one step, the smaller
configuration was already stable. -/
theorem extra_predecessor {xs ys : List ℕ} (he : Extra xs ys) (hp : Pos xs)
    (ho : Ones (step ys)) : Ones xs := by
  induction he with
  | nil => exact ones_nil
  | head x xs =>
    have hx := (pos_cons _ _).mp hp
    have hy := (ones_cons _ _).mp ho
    have hx1 : x = 1 := by omega
    subst x
    have hz : xs = [] := ones_flow_carry hx.2 (by omega) hy.2
    subst xs
    simp
  | @cons x xs ys he ih =>
    have hx := (pos_cons _ _).mp hp
    have hy := (ones_cons _ _).mp ho
    have hx12 : x = 1 ∨ x = 2 := by omega
    rcases hx12 with rfl | rfl
    · exact (ones_cons _ _).mpr ⟨rfl, ih hx.2 hy.2⟩
    · have hz : ys = [] := ones_flow_carry (extra_pos he hx.2) (by omega) hy.2
      exact False.elim (extra_nonempty he hz)


theorem iterate_one (t : ℕ) (xs : List ℕ) : step^[t] (1 :: xs) = 1 :: step^[t] xs := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_one, Function.iterate_succ_apply']

/-- Termination by nested induction on total mass and the first cell's mass.
A first cell of mass one can be removed; otherwise its mass strictly decreases. -/
theorem converges_aux (n : ℕ) : ∀ l : List ℕ, l.sum = n → Pos l →
    ∃ t : ℕ, step^[t] l = List.replicate n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    suffices hh : ∀ x : ℕ, ∀ xs : List ℕ, (x :: xs).sum = n → Pos (x :: xs) →
        ∃ t : ℕ, step^[t] (x :: xs) = List.replicate n 1 by
      intro l hs hp
      cases l with
      | nil => exact ⟨0, by simpa using congrArg (fun k => List.replicate k 1) hs⟩
      | cons x xs => exact hh x xs hs hp
    intro x
    induction x using Nat.strong_induction_on with
    | h x ihx =>
      intro xs hs hp
      obtain ⟨hx, hxs⟩ := (pos_cons _ _).mp hp
      by_cases hx1 : x = 1
      · subst x
        obtain ⟨t, ht⟩ := ih xs.sum (by simp only [List.sum_cons] at hs; omega) xs rfl hxs
        refine ⟨t, ?_⟩
        rw [iterate_one, ht]
        simp only [List.sum_cons] at hs
        rw [← hs, Nat.add_comm, List.replicate_succ]
      · have hs' : (((x+1)/2) :: flow (x/2) xs).sum = n := by
          simpa [step, flow] using (flow_sum 0 (x :: xs)).trans (by simpa using hs)
        have hp' : Pos (((x+1)/2) :: flow (x/2) xs) := by
          simpa [flow] using flow_pos hp 0
        obtain ⟨t, ht⟩ := ihx ((x+1)/2) (by omega) (flow (x/2) xs) hs' hp'
        exact ⟨t+1, by simpa [Function.iterate_succ_apply, step, flow] using ht⟩

def run (n t : ℕ) : List ℕ := step^[t] [n]

@[simp] theorem run_zero (n : ℕ) : run n 0 = [n] := rfl
@[simp] theorem run_succ (n t : ℕ) : run n (t+1) = step (run n t) :=
  Function.iterate_succ_apply' _ _ _

theorem run_pos {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : Pos (run n t) := by
  induction t with
  | zero => simpa using hn
  | succ t ih => simpa only [run_succ, step] using flow_pos ih 0

theorem run_sum (n t : ℕ) : (run n t).sum = n := by
  induction t with
  | zero => simp
  | succ t ih => simpa [run_succ, step, flow_sum] using ih

theorem run_nice {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : Nice (run n t) := by
  induction t with
  | zero =>
    by_cases h : n = 1
    · subst n; exact Nice.core Core.one
    · exact Nice.core (Core.cons (by omega) Core.nil)
  | succ t ih => simpa only [run_succ] using nice_step ih

theorem run_extra (n t : ℕ) : Extra (run n t) (run (n+1) t) := by
  induction t with
  | zero => exact Extra.head n []
  | succ t ih => simpa only [run_succ, step] using flow_extra ih 0

theorem run_converges {n : ℕ} (hn : 1 ≤ n) : ∃ t, run n t = List.replicate n 1 :=
  converges_aux n [n] (by simp) (by simpa using hn)


def trim (l : List ℕ) : List ℕ := (l.reverse.dropWhile (fun x => x = 0)).reverse

def raw (b : ℕ) (l : List ℕ) : List ℕ :=
  List.zipWith Nat.add (l.map (fun x => (x+1)/2) ++ [0]) (b :: l.map (fun x => x/2))

@[simp] theorem raw_nil (b : ℕ) : raw b [] = [b] := by simp [raw]
@[simp] theorem raw_cons (b x : ℕ) (xs : List ℕ) :
    raw b (x::xs) = ((x+1)/2+b) :: raw (x/2) xs := by simp [raw]

theorem trim_cons {x : ℕ} (hx : x ≠ 0) (xs : List ℕ) :
    trim (x :: xs) = x :: trim xs := by
  simp only [trim, List.reverse_cons, List.dropWhile_append]
  split_ifs <;> simp_all
  assumption

theorem trim_raw {xs : List ℕ} (hp : Pos xs) (b : ℕ) : trim (raw b xs) = flow b xs := by
  induction xs generalizing b with
  | nil =>
    simp only [raw_nil, flow_nil]
    by_cases hb : b = 0 <;> simp [trim, hb]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := (pos_cons _ _).mp hp
    rw [raw_cons, flow_cons, trim_cons (by omega), ih hxs]

def originalStep (l : List ℕ) : List ℕ := trim (raw 0 l)

theorem originalStep_eq {l : List ℕ} (hp : Pos l) : originalStep l = step l :=
  trim_raw hp 0

theorem original_iterate {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : originalStep^[t] [n] = run n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, run_succ]
    exact originalStep_eq (run_pos hn t)

theorem a_eq {n : ℕ} (hn : 1 ≤ n) : a n = sInf {t | run n t = List.replicate n 1} := by
  unfold a
  rw [if_neg (by omega : n ≠ 0)]
  change sInf {t | (List.range t).foldl (fun acc _ => originalStep acc) [n] = List.replicate n 1} = _
  simp only [List.foldl_const, List.length_range, original_iterate hn]

theorem a_reaches {n : ℕ} (hn : 1 ≤ n) : run n (a n) = List.replicate n 1 := by
  rw [a_eq hn]
  exact csInf_mem (run_converges hn)

theorem a_le {n t : ℕ} (hn : 1 ≤ n) (ht : run n t = List.replicate n 1) : a n ≤ t := by
  rw [a_eq hn]
  exact csInf_le' ht


theorem a_strict {n : ℕ} (hn : 1 ≤ n) : a n < a (n+1) := by
  have hn' : 1 ≤ n+1 := by omega
  have hr := a_reaches hn'
  have htpos : 0 < a (n+1) := by
    by_contra h
    have hz : a (n+1) = 0 := by omega
    rw [hz, run_zero] at hr
    have ho := ones_replicate (n+1)
    rw [← hr] at ho
    have hh := (ones_cons _ _).mp ho
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a (n+1) ≠ 0)
  change a (n+1) = t+1 at ht
  have ho : Ones (step (run (n+1) t)) := by
    rw [← run_succ, ← ht, hr]
    exact ones_replicate _
  have hp := extra_predecessor (run_extra n t) (run_pos hn t) ho
  have hs := ones_eq hp
  rw [run_sum] at hs
  have hle := a_le hn hs
  omega

theorem a_upper {n : ℕ} (hn : 1 ≤ n) : a (n+1) ≤ a n + 2 := by
  apply a_le (by omega : 1 ≤ n+1)
  have he := run_extra n (a n)
  rw [a_reaches hn] at he
  have hh := extra_ones_two he (run_nice (by omega : 1 ≤ n+1) (a n))
  simpa only [show a n + 2 = (a n + 1) + 1 by omega, run_succ] using hh

end CA

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  have hl := CA.a_strict hn
  have hu := CA.a_upper hn
  omega

theorem oeis_a300997_finite_difference_is_one_or_two.disproof : ¬ (type_of% @oeis_a300997_finite_difference_is_one_or_two) := sorry
