import FormalConjecturesUtil

/-! A finite integer counter for the five-prime quarter-period example.
The semantic connection to survivor counts is proved separately. -/
namespace Erdos970.GapAverages.QuarterTracker

def strictNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

lemma strictNat_eq {α : Type} (n : ℕ) (f : ℕ → α) : strictNat n f = f n := by
  cases n <;> rfl

@[ext] structure State where
  c3 : ℕ
  c7 : ℕ
  c11 : ℕ
  c19 : ℕ
  c23 : ℕ
  d1 : ℕ
  d2 : ℕ
  w1 : ℕ
  w2 : ℕ
  deriving DecidableEq, Repr

def inc (p c : ℕ) : ℕ := if c+1 = p then 0 else c+1

def oldGood (s : State) : ℕ :=
  if s.c3 ≠ 0 ∧ s.c7 ≠ 0 ∧ s.c11 ≠ 0 ∧ s.c19 ≠ 0 ∧ s.c23 ≠ 0 then 1 else 0

def endGood1 (s : State) : ℕ :=
  if s.c3 ≠ 0 ∧ s.c7 ≠ 6 ∧ s.c11 ≠ 9 ∧ s.c19 ≠ 15 ∧ s.c23 ≠ 18 then 1 else 0

def endGood2 (s : State) : ℕ :=
  if s.c3 ≠ 0 ∧ s.c7 ≠ 5 ∧ s.c11 ≠ 7 ∧ s.c19 ≠ 11 ∧ s.c23 ≠ 13 then 1 else 0

def step (s : State) : State :=
  strictNat (inc 3 s.c3) fun c3 =>
  strictNat (inc 7 s.c7) fun c7 =>
  strictNat (inc 11 s.c11) fun c11 =>
  strictNat (inc 19 s.c19) fun c19 =>
  strictNat (inc 23 s.c23) fun c23 =>
  strictNat (s.d1+oldGood s-endGood1 s) fun d1 =>
  strictNat (s.d2+oldGood s-endGood2 s) fun d2 =>
  strictNat (s.w1+2^s.d1) fun w1 =>
  strictNat (s.w2+2^s.d2) fun w2 =>
  ⟨c3,c7,c11,c19,c23,d1,d2,w1,w2⟩

lemma step_eq (s : State) : step s =
    ⟨inc 3 s.c3, inc 7 s.c7, inc 11 s.c11, inc 19 s.c19, inc 23 s.c23,
      s.d1+oldGood s-endGood1 s, s.d2+oldGood s-endGood2 s,
      s.w1+2^s.d1, s.w2+2^s.d2⟩ := by
  simp only [step, strictNat_eq]

def run (n : ℕ) (s : State) : State :=
  Nat.rec (motive := fun _ => State → State) (fun s => s)
    (fun _ rec s => match step s with
      | ⟨a,b,c,d,e,f,g,h,i⟩ => rec ⟨a,b,c,d,e,f,g,h,i⟩) n s

lemma run_zero (s : State) : run 0 s = s := rfl
lemma run_succ (n : ℕ) (s : State) : run (n+1) s = run n (step s) := by
  change (match step s with
    | ⟨a,b,c,d,e,f,g,h,i⟩ => run n ⟨a,b,c,d,e,f,g,h,i⟩) = run n (step s)
  cases step s
  rfl

lemma run_add (n m : ℕ) (s : State) : run (n+m) s = run m (run n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, run_zero]
  | succ n ih =>
    rw [show (n+1)+m = (n+m)+1 by omega, run_succ, ih, run_succ]

def initial : State := ⟨1,1,1,1,1,15,15,0,0⟩

end Erdos970.GapAverages.QuarterTracker
