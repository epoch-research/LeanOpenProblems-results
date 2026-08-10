import FormalConjectures.Util.ProblemImports
import Mathlib.Data.List.ModifyLast

open List Nat

private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
  termination_by l => l.length

private theorem run_lengths_nat_ne_nil {l : List ℕ} (h : l ≠ []) : run_lengths_nat l ≠ [] := by
  cases l with
  | nil => contradiction
  | cons a t => simp [run_lengths_nat]

private lemma run_lengths_nat_singleton (a : ℕ) : run_lengths_nat [a] = [1] := by
  simp [run_lengths_nat]

private lemma run_lengths_nat_cons_cons_of_ne (a b : ℕ) (xs : List ℕ) (hab : a ≠ b) :
    run_lengths_nat (a :: b :: xs) = 1 :: run_lengths_nat (b :: xs) := by
  simp [run_lengths_nat, Ne.symm hab]


private lemma run_lengths_nat_cons_cons_change_first
    (a a' b : ℕ) (xs : List ℕ) (hab : a ≠ b) (ha'b : a' ≠ b) :
    run_lengths_nat (a :: b :: xs) = run_lengths_nat (a' :: b :: xs) := by
  rw [run_lengths_nat_cons_cons_of_ne a b xs hab,
      run_lengths_nat_cons_cons_of_ne a' b xs ha'b]

private lemma run_lengths_nat_cons_cons_of_eq (a : ℕ) (xs : List ℕ) :
    run_lengths_nat (a :: a :: xs) = (run_lengths_nat (a :: xs)).modifyHead Nat.succ := by
  simp [run_lengths_nat]

private lemma modifyHead_append_of_ne_nil {α : Type*} (f : α → α) {l m : List α} (hl : l ≠ []) :
    (l ++ m).modifyHead f = l.modifyHead f ++ m := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.modifyHead]


private lemma modifyLast_singleton {α : Type*} (f : α → α) (x : α) :
    ([x] : List α).modifyLast f = [f x] := by
  simpa using (List.modifyLast_concat f x ([] : List α))

private lemma modifyLast_cons_of_ne_nil {α : Type*} (f : α → α) (x : α) {xs : List α} (hxs : xs ≠ []) :
    (x :: xs).modifyLast f = x :: xs.modifyLast f := by
  simpa using (List.modifyLast_append_of_right_ne_nil f [x] xs hxs)

private lemma modifyHead_modifyLast_succ_comm {l : List ℕ} (hl : l ≠ []) :
    (l.modifyLast Nat.succ).modifyHead Nat.succ = (l.modifyHead Nat.succ).modifyLast Nat.succ := by
  cases l with
  | nil => contradiction
  | cons x xs =>
      cases xs with
      | nil => simp [modifyLast_singleton, List.modifyHead]
      | cons y ys =>
          simp [List.modifyHead, modifyLast_cons_of_ne_nil]


private theorem run_lengths_nat_append_of_getLast?_ne_head?
    (l m : List ℕ) (hbd : l.getLast? ≠ m.head?) :
    run_lengths_nat (l ++ m) = run_lengths_nat l ++ run_lengths_nat m := by
  induction l with
  | nil => simp [run_lengths_nat]
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases m with
          | nil => simp [run_lengths_nat]
          | cons b ys =>
              have hab : a ≠ b := by
                intro heq
                apply hbd
                simp [heq]
              simp [run_lengths_nat_singleton, run_lengths_nat_cons_cons_of_ne a b ys hab]
      | cons b xs =>
          have hbd' : (b :: xs).getLast? ≠ m.head? := by
            simpa using hbd
          by_cases hab : a = b
          · subst b
            rw [show (a :: a :: xs) ++ m = a :: ((a :: xs) ++ m) by rfl]
            rw [show run_lengths_nat (a :: (a :: xs ++ m)) = (run_lengths_nat ((a :: xs) ++ m)).modifyHead Nat.succ by
              simpa [List.cons_append] using run_lengths_nat_cons_cons_of_eq a (xs ++ m)]
            rw [ih hbd']
            rw [run_lengths_nat_cons_cons_of_eq]
            rw [modifyHead_append_of_ne_nil Nat.succ (run_lengths_nat_ne_nil (by simp : (a :: xs) ≠ []))]
          · calc
              run_lengths_nat (a :: (b :: xs ++ m))
                  = 1 :: run_lengths_nat (b :: xs ++ m) := by
                    simpa [List.cons_append] using
                      run_lengths_nat_cons_cons_of_ne a b (xs ++ m) hab
              _ = 1 :: (run_lengths_nat (b :: xs) ++ run_lengths_nat m) := by
                    rw [ih hbd']
              _ = run_lengths_nat (a :: b :: xs) ++ run_lengths_nat m := by
                    rw [run_lengths_nat_cons_cons_of_ne a b xs hab]
                    rfl


private theorem run_lengths_nat_append_singleton_eq_last
    (l : List ℕ) (a : ℕ) (hlast : l.getLast? = some a) :
    run_lengths_nat (l ++ [a]) = (run_lengths_nat l).modifyLast Nat.succ := by
  induction l with
  | nil => simp at hlast
  | cons b xs ih =>
      cases xs with
      | nil =>
          simp at hlast
          subst b
          change run_lengths_nat (a :: a :: []) = (run_lengths_nat [a]).modifyLast Nat.succ
          rw [run_lengths_nat_cons_cons_of_eq, run_lengths_nat_singleton]
          rw [modifyLast_singleton]
          rfl
      | cons c xs =>
          have hlast' : (c :: xs).getLast? = some a := by simpa using hlast
          by_cases hbc : b = c
          · subst c
            calc
              run_lengths_nat (b :: (b :: xs ++ [a]))
                  = (run_lengths_nat (b :: xs ++ [a])).modifyHead Nat.succ := by
                    simpa [List.cons_append] using run_lengths_nat_cons_cons_of_eq b (xs ++ [a])
              _ = ((run_lengths_nat (b :: xs)).modifyLast Nat.succ).modifyHead Nat.succ := by
                    rw [ih hlast']
              _ = ((run_lengths_nat (b :: b :: xs)).modifyLast Nat.succ) := by
                    rw [run_lengths_nat_cons_cons_of_eq]
                    exact modifyHead_modifyLast_succ_comm (run_lengths_nat_ne_nil (by simp : (b :: xs) ≠ []))
          · calc
              run_lengths_nat (b :: (c :: xs ++ [a]))
                  = 1 :: run_lengths_nat (c :: xs ++ [a]) := by
                    simpa [List.cons_append] using run_lengths_nat_cons_cons_of_ne b c (xs ++ [a]) hbc
              _ = 1 :: (run_lengths_nat (c :: xs)).modifyLast Nat.succ := by rw [ih hlast']
              _ = (run_lengths_nat (b :: c :: xs)).modifyLast Nat.succ := by
                    rw [run_lengths_nat_cons_cons_of_ne b c xs hbc]
                    rw [modifyLast_cons_of_ne_nil Nat.succ 1 (run_lengths_nat_ne_nil (by simp : (c :: xs) ≠ []))]


private lemma reverse_modifyHead {α : Type*} (f : α → α) (l : List α) :
    (l.modifyHead f).reverse = l.reverse.modifyLast f := by
  cases l with
  | nil => rfl
  | cons x xs => simp [List.modifyHead, List.modifyLast_concat]

private theorem run_lengths_nat_reverse : ∀ l : List ℕ,
    run_lengths_nat l.reverse = (run_lengths_nat l).reverse := by
  intro l
  induction l with
  | nil => simp [run_lengths_nat]
  | cons a xs ih =>
      cases xs with
      | nil => simp [run_lengths_nat_singleton]
      | cons b ys =>
          by_cases hab : a = b
          · subst b
            calc
              run_lengths_nat ((a :: a :: ys).reverse)
                  = run_lengths_nat ((a :: ys).reverse ++ [a]) := by simp
              _ = (run_lengths_nat ((a :: ys).reverse)).modifyLast Nat.succ := by
                    apply run_lengths_nat_append_singleton_eq_last
                    simp
              _ = ((run_lengths_nat (a :: ys)).reverse).modifyLast Nat.succ := by rw [ih]
              _ = ((run_lengths_nat (a :: ys)).modifyHead Nat.succ).reverse := by
                    rw [reverse_modifyHead]
              _ = (run_lengths_nat (a :: a :: ys)).reverse := by
                    rw [run_lengths_nat_cons_cons_of_eq]
          · calc
              run_lengths_nat ((a :: b :: ys).reverse)
                  = run_lengths_nat ((b :: ys).reverse ++ [a]) := by simp
              _ = run_lengths_nat ((b :: ys).reverse) ++ run_lengths_nat [a] := by
                    apply run_lengths_nat_append_of_getLast?_ne_head?
                    simpa using (Ne.symm hab)
              _ = (run_lengths_nat (b :: ys)).reverse ++ [1] := by
                    rw [ih, run_lengths_nat_singleton]
              _ = (run_lengths_nat (a :: b :: ys)).reverse := by
                    rw [run_lengths_nat_cons_cons_of_ne a b ys hab]
                    simp


private lemma modifyHead_succ_eq_headD_tail {l : List ℕ} (hl : l ≠ []) :
    l.modifyHead Nat.succ = (l.headD 0 + 1) :: l.tail := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.modifyHead]

private lemma modifyHead_succ_merge_aux {r t : List ℕ} (hr : r ≠ []) (k : ℕ) :
    ((r.modifyLast (fun n => n + k)) ++ t).modifyHead Nat.succ =
      ((r.modifyHead Nat.succ).modifyLast (fun n => n + k)) ++ t := by
  cases r with
  | nil => contradiction
  | cons x xs =>
      cases xs with
      | nil =>
          simp [modifyLast_singleton, List.modifyHead]
          omega
      | cons y ys =>
          rw [modifyLast_cons_of_ne_nil (fun n => n + k) x (by simp : (y :: ys) ≠ [])]
          simp [List.modifyHead]
          rw [modifyLast_cons_of_ne_nil (fun n => n + k) (x + 1) (by simp : (y :: ys) ≠ [])]
          simp [List.cons_append]

private theorem run_lengths_nat_append_of_getLast?_eq_head?
    (l m : List ℕ) {a : ℕ} (hlast : l.getLast? = some a) (hhead : m.head? = some a) :
    run_lengths_nat (l ++ m) =
      (run_lengths_nat l).modifyLast (fun n => n + (run_lengths_nat m).headD 0) ++
        (run_lengths_nat m).tail := by
  induction l with
  | nil => simp at hlast
  | cons b xs ih =>
      cases xs with
      | nil =>
          cases m with
          | nil => simp at hhead
          | cons c ys =>
              simp at hlast hhead
              subst b
              subst c
              rw [show [a] ++ (a :: ys) = a :: a :: ys by rfl]
              rw [run_lengths_nat_cons_cons_of_eq]
              rw [run_lengths_nat_singleton]
              rw [modifyLast_singleton]
              rw [modifyHead_succ_eq_headD_tail (run_lengths_nat_ne_nil (by simp : (a :: ys) ≠ []))]
              simp
              omega
      | cons c xs =>
          have hlast' : (c :: xs).getLast? = some a := by simpa using hlast
          by_cases hbc : b = c
          · subst c
            calc
              run_lengths_nat (b :: ((b :: xs) ++ m))
                  = (run_lengths_nat ((b :: xs) ++ m)).modifyHead Nat.succ := by
                    simpa [List.cons_append] using run_lengths_nat_cons_cons_of_eq b (xs ++ m)
              _ = (((run_lengths_nat (b :: xs)).modifyLast
                    (fun n => n + (run_lengths_nat m).headD 0)) ++
                    (run_lengths_nat m).tail).modifyHead Nat.succ := by rw [ih hlast']
              _ = (((run_lengths_nat (b :: xs)).modifyHead Nat.succ).modifyLast
                    (fun n => n + (run_lengths_nat m).headD 0)) ++
                    (run_lengths_nat m).tail := by
                    rw [modifyHead_succ_merge_aux (run_lengths_nat_ne_nil (by simp : (b :: xs) ≠ []))]
              _ = (run_lengths_nat (b :: b :: xs)).modifyLast
                    (fun n => n + (run_lengths_nat m).headD 0) ++
                    (run_lengths_nat m).tail := by
                    rw [run_lengths_nat_cons_cons_of_eq]
          · calc
              run_lengths_nat (b :: ((c :: xs) ++ m))
                  = 1 :: run_lengths_nat ((c :: xs) ++ m) := by
                    simpa [List.cons_append] using run_lengths_nat_cons_cons_of_ne b c (xs ++ m) hbc
              _ = 1 :: ((run_lengths_nat (c :: xs)).modifyLast
                    (fun n => n + (run_lengths_nat m).headD 0) ++
                    (run_lengths_nat m).tail) := by rw [ih hlast']
              _ = (run_lengths_nat (b :: c :: xs)).modifyLast
                    (fun n => n + (run_lengths_nat m).headD 0) ++
                    (run_lengths_nat m).tail := by
                    rw [run_lengths_nat_cons_cons_of_ne b c xs hbc]
                    rw [modifyLast_cons_of_ne_nil (fun n => n + (run_lengths_nat m).headD 0) 1
                      (run_lengths_nat_ne_nil (by simp : (c :: xs) ≠ []))]
                    rfl




/-!
## A381587 transition scratch

This section keeps the final `Spec.lean` untouched.  The predicate `Good` is
an executable/local shape predicate for rows on which we expect the third-RLE
transition

  `R^3 (F l) = F (R^3 l)`

where `F l = R (reverse l) ++ l`.  `GoodStep` is a local certificate predicate:
it packages the shape assumptions, the transition conclusion, and the next-row
shape.  The concrete base row `T_8` and its transition to a `Good 6` row are
checked by `native_decide`.

The remaining mathematical work is to replace `GoodStep` by a proof that the
shape-only `Good` predicate implies the two certificate fields.  The generic RLE
append/reverse lemmas above are the intended tools for that proof.
-/

private abbrev R (l : List ℕ) : List ℕ := run_lengths_nat l

private def R3 (l : List ℕ) : List ℕ := R (R (R l))

private def F (l : List ℕ) : List ℕ := R l.reverse ++ l

private lemma F_eq_R_reverse_append (l : List ℕ) :
    F l = (R l).reverse ++ l := by
  simp [F, R, run_lengths_nat_reverse]

private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    F prev_T

private lemma A381587_T_step_F (k : ℕ) :
    A381587_T (k + 5) = F (A381587_T (k + 4)) := by
  change A381587_T ((k + 1) + 4) = F (A381587_T (k + 4))
  simp [A381587_T]

private def startsWithSingleOne (l : List ℕ) : Bool :=
  l.head? == some 1 && (l.drop 1).head? != some 1

/-- `l` starts with exactly `p` entries equal to `1`. -/
private def startsWithExactlyPOnes (p : ℕ) (l : List ℕ) : Bool :=
  l.take p == List.replicate p 1 && (l.drop p).head? != some 1

/-- `l` starts with exactly one entry equal to `a`. -/
private def startsWithSingleValue (a : ℕ) (l : List ℕ) : Bool :=
  l.head? == some a && (l.drop 1).head? != some a

private def endsWith (suf l : List ℕ) : Bool :=
  suf.length ≤ l.length && l.drop (l.length - suf.length) == suf

private def startsWithValue (a : ℕ) (l : List ℕ) : Bool :=
  l.head? == some a

/--
Executable Good-shape predicate for the rows used in the transition scratch.
For `A = R l`, `B = R A`, and `C = R B`, it records the local row properties
observed from `T_8` onward:
* `l` starts with a single `1`;
* `A` starts with exactly `p` ones;
* `B` starts with a single `p` and ends with six ones;
* `C` starts with `1` and ends with `[1, 6]`;
* the parameter is the base `p = 4` or is already in the stable range `p ≥ 3`.
-/
private def GoodBool (p : ℕ) (l : List ℕ) : Bool :=
  let A := R l
  let B := R A
  let C := R B
  ((p == 4) || (3 ≤ p)) &&
    startsWithSingleOne l &&
    startsWithExactlyPOnes p A &&
    startsWithSingleValue p B &&
    endsWith [1, 1, 1, 1, 1, 1] B &&
    startsWithValue 1 C &&
    endsWith [1, 6] C

private abbrev Good (p : ℕ) (l : List ℕ) : Prop :=
  GoodBool p l = true

/-- A local one-step certificate: shape at `p`, the desired transition, and
shape of the successor with parameter `6`. -/
private abbrev GoodStep (p : ℕ) (l : List ℕ) : Prop :=
  Good p l ∧ R3 (F l) = F (R3 l) ∧ Good 6 (F l)

private theorem transition_of_GoodStep {p : ℕ} {l : List ℕ} (h : GoodStep p l) :
    R3 (F l) = F (R3 l) ∧ Good 6 (F l) := by
  exact ⟨h.2.1, h.2.2⟩

private theorem A381587_T8_good : Good 4 (A381587_T 8) := by
  native_decide

private theorem A381587_T8_transition :
    R3 (F (A381587_T 8)) = F (R3 (A381587_T 8)) := by
  native_decide

private theorem A381587_T8_next_good : Good 6 (F (A381587_T 8)) := by
  native_decide

private theorem A381587_T8_goodStep : GoodStep 4 (A381587_T 8) := by
  native_decide

private theorem A381587_T9_good : Good 6 (A381587_T 9) := by
  native_decide

private theorem A381587_T9_transition :
    R3 (F (A381587_T 9)) = F (R3 (A381587_T 9)) := by
  native_decide

private theorem A381587_T10_good : Good 6 (A381587_T 10) := by
  native_decide

private theorem A381587_T11_good : Good 6 (A381587_T 11) := by
  native_decide



/-! Additional symbolic transition attempt. -/

private lemma getLast?_reverse_eq_head? {α : Type*} (l : List α) : l.reverse.getLast? = l.head? := by
  cases l with
  | nil => simp
  | cons x xs => simp

private lemma head?_reverse_eq_getLast? {α : Type*} (l : List α) : l.reverse.head? = l.getLast? := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x => simp

private lemma headD_eq_of_head?_eq_some {α : Type*} [Inhabited α] {l : List α} {a : α}
    (h : l.head? = some a) : l.headD default = a := by
  cases l with
  | nil => simp at h
  | cons x xs => simpa using h

private lemma reverse_modifyHead_succ_nat (l : List ℕ) :
    (l.modifyHead Nat.succ).reverse = l.reverse.modifyLast Nat.succ := by
  exact reverse_modifyHead Nat.succ l

private lemma modifyLast_reverse_succ_nat (l : List ℕ) :
    l.reverse.modifyLast Nat.succ = (l.modifyHead Nat.succ).reverse := by
  rw [reverse_modifyHead_succ_nat]

private theorem R_F_formula {l A B : List ℕ}
    (hA : R l = A) (hB : R A = B) (hl : l.head? = some 1) (hAh : A.head? = some 1) :
    R (F l) = (B.modifyHead Nat.succ).reverse ++ A.tail := by
  rw [F_eq_R_reverse_append, hA]
  have hlast : A.reverse.getLast? = some 1 := by simpa [getLast?_reverse_eq_head?] using hAh
  have hhead : l.head? = some 1 := hl
  rw [show R (A.reverse ++ l) =
      (R A.reverse).modifyLast (fun n => n + (R l).headD 0) ++ (R l).tail by
    exact run_lengths_nat_append_of_getLast?_eq_head? A.reverse l hlast hhead]
  simp only [R] at hA hB ⊢
  rw [run_lengths_nat_reverse A, hB]
  have hhd : A.headD 0 = 1 := headD_eq_of_head?_eq_some hAh
  have hfun : (fun n => n + A.headD 0) = Nat.succ := by
    funext n
    rw [hhd]
  rw [hA]
  rw [hfun, modifyLast_reverse_succ_nat]

private def decHead : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x - 1) :: xs

private lemma R_replicate_one_prefix : ∀ n : ℕ, 0 < n → ∀ {a : ℕ} {t : List ℕ}, a ≠ 1 →
    R (List.replicate n 1 ++ a :: t) = n :: R (a :: t)
  | 0, hn, a, t, ha => by omega
  | 1, hn, a, t, ha => by
      simpa [R] using run_lengths_nat_cons_cons_of_ne 1 a t (Ne.symm ha)
  | n + 2, hn, a, t, ha => by
      rw [show List.replicate (n + 2) 1 ++ a :: t = 1 :: 1 :: (List.replicate n 1 ++ a :: t) by
        simp [List.replicate_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]]
      simp only [R]
      rw [run_lengths_nat_cons_cons_of_eq]
      rw [show run_lengths_nat (1 :: (List.replicate n 1 ++ a :: t)) = R (List.replicate (n + 1) 1 ++ a :: t) by
        simp [R, List.replicate_succ]]
      rw [R_replicate_one_prefix (n + 1) (by omega) (a := a) (t := t) ha]
      simp [List.modifyHead]

private lemma R_tail_replicate_prefix {p a : ℕ} {t : List ℕ} (hp : 2 ≤ p) (ha : a ≠ 1) :
    R ((List.replicate p 1 ++ a :: t).tail) = decHead (R (List.replicate p 1 ++ a :: t)) := by
  cases p with
  | zero => omega
  | succ q =>
      cases q with
      | zero => omega
      | succ r =>
          have htail : (List.replicate (r + 2) 1 ++ a :: t).tail =
              List.replicate (r + 1) 1 ++ a :: t := by
            cases r <;> simp [List.replicate_succ]
          change R ((List.replicate (r + 2) 1 ++ a :: t).tail) =
            decHead (R (List.replicate (r + 2) 1 ++ a :: t))
          rw [htail]
          rw [R_replicate_one_prefix (r + 2) (by omega) (a := a) (t := t) ha]
          rw [R_replicate_one_prefix (r + 1) (by omega) (a := a) (t := t) ha]
          simp [decHead]


private lemma modifyHead_succ_cons (x : ℕ) (xs : List ℕ) :
    (x :: xs).modifyHead Nat.succ = (x + 1) :: xs := by
  rfl

private lemma R_modifyHead_succ_of_second_one {p : ℕ} {bt : List ℕ} (hp : 2 ≤ p) :
    R ((p :: 1 :: bt).modifyHead Nat.succ) = R (p :: 1 :: bt) := by
  simp [List.modifyHead]
  apply run_lengths_nat_cons_cons_change_first (p + 1) p 1 bt
  · omega
  · omega

private theorem R_R_F_formula {l A B C : List ℕ} {p a : ℕ} {tailA bt : List ℕ}
    (hp : 2 ≤ p) (ha : a ≠ 1)
    (hRF : R (F l) = (B.modifyHead Nat.succ).reverse ++ A.tail)
    (hAdec : A = List.replicate p 1 ++ a :: tailA)
    (hB : R A = B) (hBdec : B = p :: 1 :: bt) (hC : R B = C) :
    R (R (F l)) = C.reverse ++ decHead B := by
  rw [hRF]
  have hlast : ((B.modifyHead Nat.succ).reverse).getLast? = some (p + 1) := by
    rw [hBdec]
    simp [List.modifyHead, getLast?_reverse_eq_head?]
  have hhead : (A.tail).head? = some 1 := by
    rw [hAdec]
    cases p with
    | zero => omega
    | succ q =>
        cases q with
        | zero => omega
        | succ r =>
            simp [List.replicate_succ]
  have hbd : ((B.modifyHead Nat.succ).reverse).getLast? ≠ (A.tail).head? := by
    rw [hlast, hhead]
    simp
    omega
  rw [show R ((B.modifyHead Nat.succ).reverse ++ A.tail) =
      R ((B.modifyHead Nat.succ).reverse) ++ R A.tail by
    exact run_lengths_nat_append_of_getLast?_ne_head? _ _ hbd]
  have hleft : R ((B.modifyHead Nat.succ).reverse) = C.reverse := by
    rw [show R ((B.modifyHead Nat.succ).reverse) = (R (B.modifyHead Nat.succ)).reverse by
      exact run_lengths_nat_reverse (B.modifyHead Nat.succ)]
    rw [hBdec]
    rw [R_modifyHead_succ_of_second_one (p := p) (bt := bt) (by omega)]
    rw [← hBdec, hC]
  have hright : R A.tail = decHead B := by
    rw [hAdec]
    rw [R_tail_replicate_prefix (p := p) (a := a) (t := tailA) hp ha]
    rw [← hAdec, hB]
  rw [hleft, hright]


private lemma R_decHead_of_second_one {p : ℕ} {bt : List ℕ} (hp : 3 ≤ p) :
    R (decHead (p :: 1 :: bt)) = R (p :: 1 :: bt) := by
  simp [decHead]
  apply run_lengths_nat_cons_cons_change_first (p - 1) p 1 bt
  · omega
  · omega

private theorem R_R_R_F_formula {l B C : List ℕ} {p : ℕ} {bt : List ℕ}
    (hp : 3 ≤ p)
    (hRRF : R (R (F l)) = C.reverse ++ decHead B)
    (hBdec : B = p :: 1 :: bt) (hC : R B = C) (hCh : C.head? = some 1) :
    R (R (R (F l))) = F C := by
  rw [hRRF]
  have hlast : C.reverse.getLast? = some 1 := by simpa [getLast?_reverse_eq_head?] using hCh
  have hhead : (decHead B).head? = some (p - 1) := by rw [hBdec]; simp [decHead]
  have hbd : C.reverse.getLast? ≠ (decHead B).head? := by
    rw [hlast, hhead]
    simp
    omega
  rw [show R (C.reverse ++ decHead B) = R C.reverse ++ R (decHead B) by
    exact run_lengths_nat_append_of_getLast?_ne_head? _ _ hbd]
  rw [show R C.reverse = (R C).reverse by exact run_lengths_nat_reverse C]
  have hdec : R (decHead B) = C := by
    rw [hBdec]
    rw [R_decHead_of_second_one (p := p) (bt := bt) hp]
    rw [← hBdec, hC]
  rw [hdec]
  simp [F, R, run_lengths_nat_reverse]


private def Shape (p : ℕ) (l : List ℕ) : Prop :=
  ∃ (x : ℕ) (xs : List ℕ) (a : ℕ) (tailA bt cpre : List ℕ),
    3 ≤ p ∧
    l = 1 :: x :: xs ∧ x ≠ 1 ∧
    R l = List.replicate p 1 ++ a :: tailA ∧ a ≠ 1 ∧
    R (R l) = p :: 1 :: bt ∧
    R (R (R l)) = cpre ++ [1, 6] ∧
    (R (R (R l))).head? = some 1

private theorem R3_F_eq_F_R3_of_Shape {p : ℕ} {l : List ℕ} (h : Shape p l) :
    R3 (F l) = F (R3 l) := by
  rcases h with ⟨x, xs, a, tailA, bt, cpre, hp, hl, hx, hA, ha, hB, hCend, hChead⟩
  let A := R l
  let B := R A
  let C := R B
  have hlhead : l.head? = some 1 := by rw [hl]; simp
  have hAhead : A.head? = some 1 := by
    dsimp [A]
    rw [hA]
    cases p with
    | zero => omega
    | succ q => simp [List.replicate_succ]
  have hBdef : R A = B := rfl
  have hCdef : R B = C := rfl
  have hBdec : B = p :: 1 :: bt := by
    dsimp [B, A]
    exact hB
  have hChead' : C.head? = some 1 := by
    dsimp [C, B, A]
    exact hChead
  have hRF : R (F l) = (B.modifyHead Nat.succ).reverse ++ A.tail :=
    R_F_formula (l := l) (A := A) (B := B) rfl hBdef hlhead hAhead
  have hRRF : R (R (F l)) = C.reverse ++ decHead B := by
    apply R_R_F_formula (l := l) (A := A) (B := B) (C := C) (p := p) (a := a)
      (tailA := tailA) (bt := bt)
    · omega
    · exact ha
    · exact hRF
    · dsimp [A]; exact hA
    · exact hBdef
    · exact hBdec
    · exact hCdef
  dsimp [R3]
  exact R_R_R_F_formula (l := l) (B := B) (C := C) (p := p) (bt := bt) hp hRRF hBdec hCdef hChead'



/- Strong shape predicate preserving the three-RLE transition. -/

private def sixOnes : List ℕ := [1, 1, 1, 1, 1, 1]

/--
A stronger, fully propositional local shape predicate.  With `A = R l`,
`B = R A`, and `C = R B`, it records enough boundary data to re-establish the
same shape for `F l` with stable parameter `6`.
-/
private def StrongShape (p : ℕ) (l : List ℕ) : Prop :=
  ∃ (x : ℕ) (xs : List ℕ) (a u zB zM zD : ℕ)
      (tailA apre bt bpre bMpre bDpre cpre : List ℕ),
    3 ≤ p ∧
    l = 1 :: x :: xs ∧ x ≠ 1 ∧
    R l = List.replicate p 1 ++ a :: tailA ∧ a ≠ 1 ∧
    (R l).tail = apre ++ [u, 1] ∧ u ≠ 1 ∧
    R (R l) = p :: 1 :: bt ∧
    R (R l) = bpre ++ zB :: sixOnes ∧ zB ≠ 1 ∧ 0 < zB ∧
    (R (R l)).modifyHead Nat.succ = bMpre ++ zM :: sixOnes ∧ zM ≠ 1 ∧ 0 < zM ∧
    decHead (R (R l)) = bDpre ++ zD :: sixOnes ∧ zD ≠ 1 ∧ 0 < zD ∧
    R (R (R l)) = cpre ++ [1, 6] ∧
    (R (R (R l))).head? = some 1

private theorem Shape_of_StrongShape {p : ℕ} {l : List ℕ} (h : StrongShape p l) :
    Shape p l := by
  rcases h with ⟨x, xs, a, u, zB, zM, zD, tailA, apre, bt, bpre, bMpre, bDpre, cpre,
    hp, hl, hx, hA, ha, htailA, hu, hB, hBsuf, hzB, hzBpos, hBmodsuf, hzM, hzMpos,
    hBdecsuf, hzD, hzDpos, hC, hChead⟩
  exact ⟨x, xs, a, tailA, bt, cpre, hp, hl, hx, hA, ha, hB, hC, hChead⟩

private lemma reverse_starts_two_of_head_tail_suffix {A pre : List ℕ} {u : ℕ}
    (hhead : A.head? = some 1) (htail : A.tail = pre ++ [u, 1]) :
    ∃ ys : List ℕ, A.reverse = 1 :: u :: ys := by
  cases A with
  | nil => simp at hhead
  | cons x xs =>
      simp at hhead
      subst x
      simp at htail
      subst xs
      refine ⟨pre.reverse ++ [1], ?_⟩
      simp

private lemma F_starts_single_one_of_A_tail_suffix {l A pre : List ℕ} {u : ℕ}
    (hA : R l = A) (hhead : A.head? = some 1) (htail : A.tail = pre ++ [u, 1]) :
    ∃ ys : List ℕ, F l = 1 :: u :: ys := by
  rcases reverse_starts_two_of_head_tail_suffix (A := A) hhead htail with ⟨ys, hrev⟩
  refine ⟨ys ++ l, ?_⟩
  rw [F_eq_R_reverse_append, hA, hrev]
  rfl

private theorem StrongShape_step {p : ℕ} {l : List ℕ} (h : StrongShape p l) :
    StrongShape 6 (F l) ∧ R3 (F l) = F (R3 l) := by
  rcases h with ⟨x, xs, a, u, zB, zM, zD, tailA, apre, bt, bpre, bMpre, bDpre, cpre,
    hp, hl, hx, hA, ha, htailA, hu, hB, hBsuf, hzB, hzBpos, hBmodsuf, hzM, hzMpos,
    hBdecsuf, hzD, hzDpos, hCend, hChead⟩
  let A := R l
  let B := R A
  let C := R B
  have htrans : R3 (F l) = F (R3 l) := by
    exact R3_F_eq_F_R3_of_Shape (Shape_of_StrongShape ⟨x, xs, a, u, zB, zM, zD,
      tailA, apre, bt, bpre, bMpre, bDpre, cpre, hp, hl, hx, hA, ha, htailA, hu,
      hB, hBsuf, hzB, hzBpos, hBmodsuf, hzM, hzMpos, hBdecsuf, hzD, hzDpos,
      hCend, hChead⟩)
  have hlhead : l.head? = some 1 := by rw [hl]; simp
  have hAhead : A.head? = some 1 := by
    dsimp [A]
    rw [hA]
    cases p with
    | zero => omega
    | succ q => simp [List.replicate_succ]
  have hAtail : A.tail = apre ++ [u, 1] := by
    dsimp [A]
    exact htailA
  have hFstart : ∃ ys : List ℕ, F l = 1 :: u :: ys :=
    F_starts_single_one_of_A_tail_suffix (l := l) (A := A) (pre := apre) (u := u)
      rfl hAhead hAtail
  rcases hFstart with ⟨lxs, hlF⟩
  have hBdef : R A = B := rfl
  have hCdef : R B = C := rfl
  have hBdec : B = p :: 1 :: bt := by dsimp [B, A]; exact hB
  have hBmodsuf' : B.modifyHead Nat.succ = bMpre ++ zM :: sixOnes := by
    dsimp [B, A]
    exact hBmodsuf
  have hBdecsuf' : decHead B = bDpre ++ zD :: sixOnes := by
    dsimp [B, A]
    exact hBdecsuf
  have hCeq : C = cpre ++ [1, 6] := by dsimp [C, B, A]; exact hCend
  have hChead' : C.head? = some 1 := by dsimp [C, B, A]; exact hChead
  have hRF : R (F l) = (B.modifyHead Nat.succ).reverse ++ A.tail :=
    R_F_formula (l := l) (A := A) (B := B) rfl hBdef hlhead hAhead
  have hRRF : R (R (F l)) = C.reverse ++ decHead B := by
    apply R_R_F_formula (l := l) (A := A) (B := B) (C := C) (p := p) (a := a)
      (tailA := tailA) (bt := bt)
    · omega
    · exact ha
    · exact hRF
    · dsimp [A]; exact hA
    · exact hBdef
    · exact hBdec
    · exact hCdef
  have hRRRF : R (R (R (F l))) = F C := by
    exact R_R_R_F_formula (l := l) (B := B) (C := C) (p := p) (bt := bt) hp hRRF hBdec hCdef hChead'
  let tailA' : List ℕ := bMpre.reverse ++ A.tail
  let apre' : List ℕ := List.replicate 5 1 ++ zM :: bMpre.reverse ++ apre
  let bt' : List ℕ := cpre.reverse ++ decHead B
  let bpre' : List ℕ := 6 :: 1 :: cpre.reverse ++ bDpre
  let bMpre' : List ℕ := 7 :: 1 :: cpre.reverse ++ bDpre
  let bDpre' : List ℕ := 5 :: 1 :: cpre.reverse ++ bDpre
  let cpre' : List ℕ := (R C.reverse) ++ cpre
  have hA' : R (F l) = List.replicate 6 1 ++ zM :: tailA' := by
    dsimp [tailA']
    rw [hRF, hBmodsuf']
    simp [sixOnes]
  have htailA' : (R (F l)).tail = apre' ++ [u, 1] := by
    rw [hA']
    dsimp [tailA', apre']
    rw [hAtail]
    simp [List.append_assoc]
  have hB' : R (R (F l)) = 6 :: 1 :: bt' := by
    dsimp [bt']
    rw [hRRF, hCeq]
    simp
  have hBsuf' : R (R (F l)) = bpre' ++ zD :: sixOnes := by
    rw [hB']
    dsimp [bt', bpre']
    rw [hBdecsuf']
    simp [List.append_assoc]
  have hBmodsuf'new : (R (R (F l))).modifyHead Nat.succ = bMpre' ++ zD :: sixOnes := by
    rw [hB']
    dsimp [bt', bMpre']
    rw [hBdecsuf']
    simp [List.modifyHead, List.append_assoc]
  have hBdecsuf'new : decHead (R (R (F l))) = bDpre' ++ zD :: sixOnes := by
    rw [hB']
    dsimp [bt', bDpre']
    rw [hBdecsuf']
    simp [decHead, List.append_assoc]
  have hC' : R (R (R (F l))) = cpre' ++ [1, 6] := by
    dsimp [cpre']
    rw [hRRRF, F]
    rw [hCeq]
    simp [List.append_assoc]
  have hC'head : (R (R (R (F l)))).head? = some 1 := by
    rw [hRRRF, F, hCeq]
    have hrev : (cpre ++ ([1, 6] : List ℕ)).reverse = 6 :: 1 :: cpre.reverse := by simp
    rw [hrev]
    rw [show R (6 :: 1 :: cpre.reverse) = 1 :: R (1 :: cpre.reverse) by
      simpa [R] using run_lengths_nat_cons_cons_of_ne 6 1 cpre.reverse (by decide)]
    simp
  refine ⟨?_, htrans⟩
  refine ⟨u, lxs, zM, u, zD, zD, zD, tailA', apre', bt', bpre', bMpre', bDpre', cpre', ?_⟩
  exact ⟨by decide, hlF, hu, hA', hzM, htailA', hu, hB', hBsuf', hzD, hzDpos,
    hBmodsuf'new, hzD, hzDpos, hBdecsuf'new, hzD, hzDpos, hC', hC'head⟩

private theorem StrongShape_preserves_transition {p : ℕ} {l : List ℕ} (h : StrongShape p l) :
    StrongShape 6 (F l) ∧ R3 (F l) = F (R3 l) :=
  StrongShape_step h


private theorem A381587_T8_strongShape : StrongShape 4 (A381587_T 8) := by
  refine ⟨3,
    [1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2],
    3, 3, 4, 5, 3,
    [1, 3, 1, 3, 1],
    [1, 1, 1, 3, 1, 3, 1],
    [1, 1, 1, 1, 1],
    [], [], [], [], ?_⟩
  native_decide

private theorem A381587_T8_strongShape_step :
    StrongShape 6 (F (A381587_T 8)) ∧ R3 (F (A381587_T 8)) = F (R3 (A381587_T 8)) :=
  StrongShape_preserves_transition A381587_T8_strongShape


private theorem A381587_T8plus_strongShape_transition :
    ∀ k : ℕ, StrongShape (if k = 0 then 4 else 6) (A381587_T (k + 8)) ∧
      R3 (A381587_T (k + 9)) = F (R3 (A381587_T (k + 8))) := by
  intro k
  induction k with
  | zero =>
      constructor
      · simpa using A381587_T8_strongShape
      · rw [A381587_T_step_F 4]
        exact (StrongShape_preserves_transition A381587_T8_strongShape).2
  | succ k ih =>
      have hshape_next : StrongShape 6 (F (A381587_T (k + 8))) ∧
          R3 (F (A381587_T (k + 8))) = F (R3 (A381587_T (k + 8))) :=
        StrongShape_preserves_transition ih.1
      have hTnext : A381587_T (k + 9) = F (A381587_T (k + 8)) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using A381587_T_step_F (k + 4)
      constructor
      · simp only [Nat.succ_ne_zero, ↓reduceIte]
        simpa [hTnext] using hshape_next.1
      · have hshape_next2 := StrongShape_preserves_transition hshape_next.1
        have hTnext2 : A381587_T (Nat.succ k + 9) = F (A381587_T (Nat.succ k + 8)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using A381587_T_step_F (k + 5)
        rw [hTnext2]
        exact hshape_next2.2

private theorem A381587_R3_transition (k : ℕ) :
    R3 (A381587_T (k + 9)) = F (R3 (A381587_T (k + 8))) :=
  (A381587_T8plus_strongShape_transition k).2


private def bumpLast4 : List ℕ → List ℕ
  | [] => []
  | [x] => [x + 4]
  | x :: xs => x :: bumpLast4 xs

private lemma bumpLast4_append_two (xs : List ℕ) (a b : ℕ) :
    bumpLast4 (xs ++ [a, b]) = xs ++ [a, b + 4] := by
  induction xs with
  | nil => simp [bumpLast4]
  | cons x xs ih => simp [bumpLast4, ih]

private lemma run_lengths_nat_reverse_bumpLast4_append_two
    (xs : List ℕ) (a b : ℕ) (h : b + 4 ≠ a) (h' : b ≠ a) :
    R (bumpLast4 (xs ++ [a, b])).reverse = R (xs ++ [a, b]).reverse := by
  rw [bumpLast4_append_two]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
  exact run_lengths_nat_cons_cons_change_first (b + 4) b a xs.reverse h h'

private lemma bumpLast4_append_append_two (p xs : List ℕ) (a b : ℕ) :
    bumpLast4 (p ++ (xs ++ [a, b])) = p ++ (xs ++ [a, b + 4]) := by
  induction p with
  | nil => simp [bumpLast4_append_two]
  | cons x p ih => simp [bumpLast4, ih]

private lemma F_bumpLast4_append_two
    (xs : List ℕ) (a b : ℕ) (h : b + 4 ≠ a) (h' : b ≠ a) :
    F (bumpLast4 (xs ++ [a, b])) = bumpLast4 (F (xs ++ [a, b])) := by
  simp only [F]
  rw [run_lengths_nat_reverse_bumpLast4_append_two xs a b h h']
  rw [bumpLast4_append_two]
  rw [bumpLast4_append_append_two (R (xs ++ [a, b]).reverse) xs a b]

private lemma A381587_structural_base :
    R3 (A381587_T 8) = bumpLast4 (A381587_T 4) := by
  native_decide

private lemma A381587_T_suffix_12 :
    ∀ k : ℕ, ∃ xs : List ℕ, A381587_T (k + 4) = xs ++ [1, 2] := by
  intro k
  induction k with
  | zero =>
      refine ⟨[], ?_⟩
      simp [A381587_T, F, R, run_lengths_nat]
  | succ k ih =>
      rcases ih with ⟨xs, hxs⟩
      refine ⟨R (A381587_T (k + 4)).reverse ++ xs, ?_⟩
      rw [A381587_T_step_F k, F, hxs]
      simp [List.append_assoc]

private theorem A381587_structural_bump :
    ∀ k : ℕ, R3 (A381587_T (k + 8)) = bumpLast4 (A381587_T (k + 4)) := by
  intro k
  induction k with
  | zero => simpa using A381587_structural_base
  | succ k ih =>
      rw [A381587_R3_transition k, ih]
      rcases A381587_T_suffix_12 k with ⟨xs, hxs⟩
      rw [hxs]
      rw [F_bumpLast4_append_two xs 1 2 (by omega) (by omega)]
      rw [← hxs]
      rw [A381587_T_step_F k]



/-! Scalar row-sum recurrence extracted from the structural bump theorem. -/

private def A381587_S (n : ℕ) : ℕ :=
  (A381587_T n).sum

private def A381587_bR (n : ℕ) : ℝ :=
  (A381587_S n : ℝ) + 3

private lemma length_takeWhile_le {α : Type*} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := by
  have hlen : (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
    simpa only [List.length_append] using
      congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := l))
  omega

private theorem run_lengths_nat_sum_eq_length :
    ∀ l : List ℕ, (run_lengths_nat l).sum = l.length := by
  intro l
  induction l using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h tail run_prefix rest ih =>
      have hle : run_prefix.length ≤ (h :: tail).length := by
        simpa [run_prefix] using length_takeWhile_le (fun x => x = h) (h :: tail)
      calc
        (run_lengths_nat (h :: tail)).sum
            = run_prefix.length + (run_lengths_nat rest).sum := by
                simp [run_lengths_nat, run_prefix, rest]
        _ = run_prefix.length + rest.length := by rw [ih]
        _ = (h :: tail).length := by
          rw [show rest.length = (h :: tail).length - run_prefix.length by
            simp [rest, List.length_drop]]
          omega

private lemma F_sum (l : List ℕ) :
    (F l).sum = l.length + l.sum := by
  simp [F, R, run_lengths_nat_sum_eq_length]

private lemma A381587_S_step (k : ℕ) :
    A381587_S (k + 5) = A381587_S (k + 4) + (A381587_T (k + 4)).length := by
  rw [A381587_S, A381587_T_step_F k, F_sum]
  simp [A381587_S]
  omega

private lemma A381587_T_length_step (k : ℕ) :
    (A381587_T (k + 5)).length =
      (R (A381587_T (k + 4))).length + (A381587_T (k + 4)).length := by
  rw [A381587_T_step_F k]
  simp [F, R, run_lengths_nat_reverse]

private lemma R3_sum_eq_RR_length (l : List ℕ) :
    (R3 l).sum = (R (R l)).length := by
  simp [R3, R, run_lengths_nat_sum_eq_length]

private lemma bumpLast4_sum_append_two (xs : List ℕ) (a b : ℕ) :
    (bumpLast4 (xs ++ [a, b])).sum = (xs ++ [a, b]).sum + 4 := by
  rw [bumpLast4_append_two]
  simp
  omega

private lemma A381587_RR_length_eq_S_add_four (k : ℕ) :
    (R (R (A381587_T (k + 12)))).length = A381587_S (k + 8) + 4 := by
  have hstruct : R3 (A381587_T (k + 12)) = bumpLast4 (A381587_T (k + 8)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      A381587_structural_bump (k + 4)
  rcases A381587_T_suffix_12 (k + 4) with ⟨xs, hxs⟩
  have hxs8 : A381587_T (k + 8) = xs ++ [1, 2] := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxs
  calc
    (R (R (A381587_T (k + 12)))).length = (R3 (A381587_T (k + 12))).sum := by
      rw [R3_sum_eq_RR_length]
    _ = (bumpLast4 (A381587_T (k + 8))).sum := by rw [hstruct]
    _ = A381587_S (k + 8) + 4 := by
      rw [hxs8, bumpLast4_sum_append_two]
      simp [A381587_S, hxs8]


private lemma tail_length_real_of_head?_eq_some {α : Type*} {l : List α} {a : α}
    (h : l.head? = some a) :
    ((l.tail.length : ℝ) = (l.length : ℝ) - 1) := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

private lemma A381587_R_step_length_real (k : ℕ) :
    ((R (A381587_T (k + 9))).length : ℝ) =
      ((R (R (A381587_T (k + 8)))).length : ℝ) +
        ((R (A381587_T (k + 8))).length : ℝ) - 1 := by
  let l := A381587_T (k + 8)
  let A := R l
  let B := R A
  have hshape := (A381587_T8plus_strongShape_transition k).1
  rcases hshape with ⟨x, xs, a, u, zB, zM, zD, tailA, apre, bt, bpre, bMpre,
    bDpre, cpre, hp, hl, hx, hA, ha, htailA, hu, hB, hBsuf, hzB, hzBpos,
    hBmodsuf, hzM, hzMpos, hBdecsuf, hzD, hzDpos, hCend, hChead⟩
  have hlhead : l.head? = some 1 := by
    dsimp [l]
    rw [hl]
    simp
  have hAhead : A.head? = some 1 := by
    dsimp [A, l]
    rw [hA]
    by_cases hk : k = 0 <;> simp [hk]
  have hRF : R (F l) = (B.modifyHead Nat.succ).reverse ++ A.tail := by
    exact R_F_formula (l := l) (A := A) (B := B) rfl rfl hlhead hAhead
  have hlenNat : (R (F l)).length = B.length + A.tail.length := by
    rw [hRF]
    simp [B]
  have htail : ((A.tail.length : ℝ) = (A.length : ℝ) - 1) :=
    tail_length_real_of_head?_eq_some hAhead
  have hT : A381587_T (k + 9) = F l := by
    dsimp [l]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using A381587_T_step_F (k + 4)
  calc
    ((R (A381587_T (k + 9))).length : ℝ) = ((R (F l)).length : ℝ) := by rw [hT]
    _ = (B.length : ℝ) + (A.tail.length : ℝ) := by exact_mod_cast hlenNat
    _ = (B.length : ℝ) + (A.length : ℝ) - 1 := by rw [htail]; ring
    _ = ((R (R (A381587_T (k + 8)))).length : ℝ) +
        ((R (A381587_T (k + 8))).length : ℝ) - 1 := by rfl

private lemma A381587_S_step_real (k : ℕ) :
    ((A381587_S (k + 5) : ℝ) =
      (A381587_S (k + 4) : ℝ) + ((A381587_T (k + 4)).length : ℝ)) := by
  exact_mod_cast A381587_S_step k

private lemma A381587_T_length_step_real (k : ℕ) :
    (((A381587_T (k + 5)).length : ℝ) =
      ((R (A381587_T (k + 4))).length : ℝ) +
        ((A381587_T (k + 4)).length : ℝ)) := by
  exact_mod_cast A381587_T_length_step k

private theorem A381587_scalar_recurrence_S_real (k : ℕ) :
    (A381587_S (k + 15) : ℝ) =
      3 * (A381587_S (k + 14) : ℝ) - 3 * (A381587_S (k + 13) : ℝ) +
        (A381587_S (k + 12) : ℝ) + (A381587_S (k + 8) : ℝ) + 3 := by
  have hs13 := A381587_S_step_real (k + 8)
  have hs14 := A381587_S_step_real (k + 9)
  have hs15 := A381587_S_step_real (k + 10)
  have hl13 := A381587_T_length_step_real (k + 8)
  have hl14 := A381587_T_length_step_real (k + 9)
  have hd13 := A381587_R_step_length_real (k + 4)
  have he12 : (((R (R (A381587_T (k + 12)))).length : ℝ) =
      (A381587_S (k + 8) : ℝ) + 4) := by
    exact_mod_cast A381587_RR_length_eq_S_add_four k
  nlinarith

private theorem A381587_scalar_recurrence_bR (k : ℕ) :
    A381587_bR (k + 15) =
      3 * A381587_bR (k + 14) - 3 * A381587_bR (k + 13) +
        A381587_bR (k + 12) + A381587_bR (k + 8) := by
  unfold A381587_bR
  rw [A381587_scalar_recurrence_S_real k]
  ring


open Filter Set Real
open scoped Topology Matrix

noncomputable section

abbrev Idx := Fin 7

/-- The concrete 7 by 7 nonnegative matrix used in the A381358 transfer-matrix scratch work. -/
def A7 : Matrix Idx Idx ℝ := !![
  1, 1, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1;
  1, 0, 0, 0, 0, 0, 0]

def A7pow10 : Matrix Idx Idx ℝ := !![
  21, 25, 51, 37, 28, 21, 15;
  15, 21, 25, 14, 9, 7, 6;
  6, 15, 21, 11, 5, 2, 1;
  1, 6, 15, 10, 6, 3, 1;
  2, 7, 21, 15, 10, 6, 3;
  5, 9, 28, 21, 15, 10, 6;
  11, 14, 37, 28, 21, 15, 10]

set_option maxHeartbeats 2000000 in
theorem A7_pow10 : A7 ^ 10 = A7pow10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A7, A7pow10, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem A7_primitive : Matrix.IsPrimitive A7 := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A7]
  · refine ⟨10, by norm_num, ?_⟩
    intro i j
    rw [A7_pow10]
    fin_cases i <;> fin_cases j <;> norm_num [A7pow10]

/-- First coordinate of the `A7` orbit of `v`. -/
def firstCoord (v : Idx → ℝ) (n : ℕ) : ℝ := (A7 ^ n *ᵥ v) 0

/-- Total mass of the `A7` orbit of `v`; this is the comparison sequence used
for the almost-multiplicativity argument. -/
def totalMass (v : Idx → ℝ) (n : ℕ) : ℝ := ∑ i : Idx, (A7 ^ n *ᵥ v) i


/-- A Fekete-lemma wrapper: a positive, almost-submultiplicative real sequence whose
logarithms divided by `n` are bounded below has a root limit.  The harmless constant
`C` is absorbed by applying Fekete to `log (t n) + log C`. -/
theorem exists_root_limit_of_almost_submultiplicative
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n) {C : ℝ} (hC : 0 < C)
    (hsub : ∀ m n, t (m + n) ≤ C * t m * t n)
    (hbdd : BddBelow (range fun n : ℕ => (Real.log (t n) + Real.log C) / (n : ℝ))) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (t n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  let u : ℕ → ℝ := fun n => Real.log (t n) + Real.log C
  have hu : Subadditive u := by
    intro m n
    have hpos_m : 0 < t m := htpos m
    have hpos_n : 0 < t n := htpos n
    have hpos_mul : 0 < C * t m * t n := mul_pos (mul_pos hC hpos_m) hpos_n
    have hlog_le : Real.log (t (m + n)) ≤ Real.log (C * t m * t n) :=
      Real.log_le_log (htpos (m + n)) (hsub m n)
    calc
      u (m + n) = Real.log (t (m + n)) + Real.log C := rfl
      _ ≤ Real.log (C * t m * t n) + Real.log C := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hlog_le (Real.log C)
      _ = (Real.log (t m) + Real.log C) + (Real.log (t n) + Real.log C) := by
        rw [Real.log_mul (mul_ne_zero hC.ne' hpos_m.ne') hpos_n.ne',
            Real.log_mul hC.ne' hpos_m.ne']
        ring_nf
      _ = u m + u n := rfl
  rcases hu.tendsto_lim hbdd with hlim_u
  let a : ℝ := hu.lim
  refine ⟨Real.exp a, ?_⟩
  have hloglim : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (t n)) atTop (𝓝 a) := by
    have hCterm : Tendsto (fun n : ℕ => (Real.log C) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_comm] using
        ((tendsto_const_nhds (x := Real.log C)).mul tendsto_one_div_atTop_nhds_zero_nat)
    have hdiff := hlim_u.sub hCterm
    have hdiff' : Tendsto (fun n : ℕ => u n / (n : ℝ) - Real.log C / (n : ℝ)) atTop (𝓝 a) := by
      simpa [a] using hdiff
    refine Tendsto.congr' ?_ hdiff'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp [u]
    field_simp [hn0]
    ring_nf
  have hexp : Tendsto (fun n : ℕ => Real.exp ((1 / (n : ℝ)) * Real.log (t n))) atTop (𝓝 (Real.exp a)) :=
    Real.continuous_exp.tendsto a |>.comp hloglim
  refine Tendsto.congr' ?_ hexp
  filter_upwards with n
  have hpos : 0 < t n := htpos n
  rw [Real.rpow_def_of_pos hpos]
  ring_nf


/-- Constant factors disappear after taking `n`-th roots. -/
theorem const_rpow_one_div_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using (tendsto_const_nhds.rpow h0 (Or.inl hc.ne'))

/-- If two nonnegative sequences differ only by eventual positive constant factors,
they have the same root limit. -/
theorem rpow_one_div_sandwich
    {a b : ℕ → ℝ} {L c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => b n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L))
    (hlo : ∀ᶠ n in atTop, c * b n ≤ a n)
    (hhi : ∀ᶠ n in atTop, a n ≤ d * b n) :
    Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  have hcle : ∀ᶠ n : ℕ in atTop,
      c ^ ((1 : ℝ) / (n : ℝ)) * b n ^ ((1 : ℝ) / (n : ℝ)) ≤
        a n ^ ((1 : ℝ) / (n : ℝ)) := by
    filter_upwards [hlo, (eventually_ge_atTop (1 : ℕ))] with n hn hnpos
    rw [← Real.mul_rpow hc.le (hb_nonneg n)]
    exact Real.rpow_le_rpow (mul_nonneg hc.le (hb_nonneg n)) hn (by positivity)
  have hhle : ∀ᶠ n : ℕ in atTop,
      a n ^ ((1 : ℝ) / (n : ℝ)) ≤
        d ^ ((1 : ℝ) / (n : ℝ)) * b n ^ ((1 : ℝ) / (n : ℝ)) := by
    filter_upwards [hhi, (eventually_ge_atTop (1 : ℕ))] with n hn hnpos
    rw [← Real.mul_rpow hd.le (hb_nonneg n)]
    exact Real.rpow_le_rpow (ha_nonneg n) hn (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hcle hhle
  · have hcroot := const_rpow_one_div_tendsto_one hc
    simpa [one_mul] using hcroot.mul hlim
  · have hdroot := const_rpow_one_div_tendsto_one hd
    simpa [one_mul] using hdroot.mul hlim

/-- Combined form tailored to matrix-coordinate applications: if a positive
almost-submultiplicative comparison sequence `b` has the logarithmic lower bound
needed by Fekete, and `a` is eventually within fixed positive multiples of `b`,
then `a n ^ (1/n)` converges. -/
theorem exists_root_limit_of_sandwiched_almost_submultiplicative
    (a b : ℕ → ℝ) (hbpos : ∀ n, 0 < b n) (hanonneg : ∀ n, 0 ≤ a n)
    {C c d : ℝ} (hC : 0 < C) (hc : 0 < c) (hd : 0 < d)
    (hsub : ∀ m n, b (m + n) ≤ C * b m * b n)
    (hbdd : BddBelow (range fun n : ℕ => (Real.log (b n) + Real.log C) / (n : ℝ)))
    (hlo : ∀ᶠ n in atTop, c * b n ≤ a n)
    (hhi : ∀ᶠ n in atTop, a n ≤ d * b n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  rcases exists_root_limit_of_almost_submultiplicative b hbpos hC hsub hbdd with ⟨L, hL⟩
  exact ⟨L, rpow_one_div_sandwich hc hd (fun n => (hbpos n).le) hanonneg hL hlo hhi⟩


/-- A concrete `A7`-coordinate corollary.  The remaining matrix-specific work is to
prove the displayed hypotheses for `totalMass v` and `firstCoord v`; once those
bounds are available, the root limit for the first coordinate follows without any
Perron--Frobenius eigenvalue calculation. -/
theorem exists_firstCoord_A7_root_limit_from_totalMass_bounds
    (v : Idx → ℝ) (htpos : ∀ n, 0 < totalMass v n)
    (hfirst_nonneg : ∀ n, 0 ≤ firstCoord v n)
    {C c d : ℝ} (hC : 0 < C) (hc : 0 < c) (hd : 0 < d)
    (hsub : ∀ m n, totalMass v (m + n) ≤ C * totalMass v m * totalMass v n)
    (hbdd : BddBelow (range fun n : ℕ =>
      (Real.log (totalMass v n) + Real.log C) / (n : ℝ)))
    (hlo : ∀ᶠ n in atTop, c * totalMass v n ≤ firstCoord v n)
    (hhi : ∀ᶠ n in atTop, firstCoord v n ≤ d * totalMass v n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (firstCoord v n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  exact exists_root_limit_of_sandwiched_almost_submultiplicative
    (firstCoord v) (totalMass v) htpos hfirst_nonneg hC hc hd hsub hbdd hlo hhi



theorem A7_entry_nonneg (i j : Idx) : 0 ≤ A7 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [A7]

theorem A7_pow_entry_nonneg (n : ℕ) (i j : Idx) : 0 ≤ (A7 ^ n) i j := by
  induction n generalizing i j with
  | zero =>
      by_cases h : i = j <;> simp [h]
  | succ n ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (A7_entry_nonneg k j)

theorem A7_iterate_nonneg {v : Idx → ℝ} (hv : ∀ i, 0 ≤ v i) (n : ℕ) (i : Idx) :
    0 ≤ (A7 ^ n *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (A7_pow_entry_nonneg n i j) (hv j)

theorem firstCoord_nonneg_of_nonneg {v : Idx → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ n, 0 ≤ firstCoord v n := by
  intro n
  exact A7_iterate_nonneg hv n 0

theorem A7_pow_zero_zero_ge_one (n : ℕ) : (1 : ℝ) ≤ (A7 ^ n) (0 : Idx) (0 : Idx) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * A7 x (0 : Idx) := by
        intro x hx
        exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (A7_entry_nonneg x 0)
      have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * A7 (0 : Idx) (0 : Idx) ≤
          ∑ x : Idx, (A7 ^ n) (0 : Idx) x * A7 x (0 : Idx) := by
        exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
      have hA : A7 (0 : Idx) (0 : Idx) = 1 := by norm_num [A7]
      nlinarith

theorem firstCoord_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, 0 < firstCoord v n := by
  intro n
  simp only [firstCoord, Matrix.mulVec, dotProduct]
  have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * v x := by
    intro x hx
    exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (hv x).le
  have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) ≤
      ∑ x : Idx, (A7 ^ n) (0 : Idx) x * v x := by
    exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
  have hpos : 0 < (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) :=
    mul_pos (lt_of_lt_of_le zero_lt_one (A7_pow_zero_zero_ge_one n)) (hv 0)
  exact lt_of_lt_of_le hpos hle

theorem totalMass_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, 0 < totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  have hle : (A7 ^ n *ᵥ v) (0 : Idx) ≤ ∑ i : Idx, (A7 ^ n *ᵥ v) i := by
    exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)
  exact lt_of_lt_of_le (firstCoord_pos_of_pos hv n) (by simpa [totalMass, firstCoord] using hle)

theorem firstCoord_ge_v0_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, v (0 : Idx) ≤ firstCoord v n := by
  intro n
  simp only [firstCoord, Matrix.mulVec, dotProduct]
  have hterm_nonneg : ∀ x ∈ Finset.univ, 0 ≤ (A7 ^ n) (0 : Idx) x * v x := by
    intro x hx
    exact mul_nonneg (A7_pow_entry_nonneg n 0 x) (hv x).le
  have hle : (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) ≤
      ∑ x : Idx, (A7 ^ n) (0 : Idx) x * v x := by
    exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ _)
  have hv0non : 0 ≤ v (0 : Idx) := (hv 0).le
  have hmul : v (0 : Idx) ≤ (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) := by
    calc
      v (0 : Idx) = 1 * v (0 : Idx) := by ring
      _ ≤ (A7 ^ n) (0 : Idx) (0 : Idx) * v (0 : Idx) :=
        mul_le_mul_of_nonneg_right (A7_pow_zero_zero_ge_one n) hv0non
  exact le_trans hmul hle

theorem totalMass_ge_v0_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, v (0 : Idx) ≤ totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  have hle : (A7 ^ n *ᵥ v) (0 : Idx) ≤ ∑ i : Idx, (A7 ^ n *ᵥ v) i := by
    exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)
  exact le_trans (firstCoord_ge_v0_of_pos hv n) (by simpa [totalMass, firstCoord] using hle)


theorem invSum_pos_of_pos {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    0 < ∑ i : Idx, (v i)⁻¹ := by
  exact Finset.sum_pos (fun i hi => inv_pos.mpr (hv i)) (Finset.univ_nonempty)

theorem A7_col_sum_mul_v_le_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i)
    (m : ℕ) (j : Idx) :
    (∑ i : Idx, (A7 ^ m) i j) * v j ≤ totalMass v m := by
  rw [Finset.sum_mul]
  simp only [totalMass, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun i hi =>
    Finset.single_le_sum
      (fun k hk => mul_nonneg (A7_pow_entry_nonneg m i k) (le_of_lt (hv k)))
      (Finset.mem_univ j)

theorem A7_col_sum_le_inv_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i)
    (m : ℕ) (j : Idx) :
    (∑ i : Idx, (A7 ^ m) i j) ≤ (v j)⁻¹ * totalMass v m := by
  have h := mul_le_mul_of_nonneg_left (A7_col_sum_mul_v_le_totalMass hv m j)
      (inv_nonneg.mpr (le_of_lt (hv j)))
  have hvne : v j ≠ 0 := (hv j).ne'
  calc
    (∑ i : Idx, (A7 ^ m) i j) = (v j)⁻¹ * ((∑ i : Idx, (A7 ^ m) i j) * v j) := by
      field_simp [hvne]
    _ ≤ (v j)⁻¹ * totalMass v m := h

theorem totalMass_almost_submultiplicative_invSum {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ m n, totalMass v (m + n) ≤ (∑ j : Idx, (v j)⁻¹) * totalMass v m * totalMass v n := by
  intro m n
  let C : ℝ := ∑ j : Idx, (v j)⁻¹
  have hC_nonneg : 0 ≤ C := (invSum_pos_of_pos hv).le
  have htm_nonneg : 0 ≤ totalMass v m := (totalMass_pos_of_pos hv m).le
  have hx_nonneg : ∀ j : Idx, 0 ≤ (A7 ^ n *ᵥ v) j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : totalMass v (m + n) =
      ∑ j : Idx, (∑ i : Idx, (A7 ^ m) i j) * (A7 ^ n *ᵥ v) j := by
    simp only [totalMass]
    rw [pow_add, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [h_expand]
  calc
    (∑ j : Idx, (∑ i : Idx, (A7 ^ m) i j) * (A7 ^ n *ᵥ v) j)
        ≤ ∑ j : Idx, ((v j)⁻¹ * totalMass v m) * (A7 ^ n *ᵥ v) j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7_col_sum_le_inv_totalMass hv m j) (hx_nonneg j)
    _ ≤ ∑ j : Idx, (C * totalMass v m) * (A7 ^ n *ᵥ v) j := by
      exact Finset.sum_le_sum fun j hj => by
        have hinv_le : (v j)⁻¹ ≤ C := by
          exact Finset.single_le_sum (fun k hk => (inv_pos.mpr (hv k)).le) (Finset.mem_univ j)
        have hleft : (v j)⁻¹ * totalMass v m ≤ C * totalMass v m :=
          mul_le_mul_of_nonneg_right hinv_le htm_nonneg
        exact mul_le_mul_of_nonneg_right hleft (hx_nonneg j)
    _ = C * totalMass v m * totalMass v n := by
      simp [totalMass, Finset.mul_sum]

theorem totalMass_log_bddBelow_invSum {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    BddBelow (range fun n : ℕ =>
      (Real.log (totalMass v n) + Real.log (∑ j : Idx, (v j)⁻¹)) / (n : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  let C : ℝ := ∑ j : Idx, (v j)⁻¹
  have hCpos : 0 < C := invSum_pos_of_pos hv
  have htmpos : 0 < totalMass v n := totalMass_pos_of_pos hv n
  have hinv_le_C : (v (0 : Idx))⁻¹ ≤ C := by
    exact Finset.single_le_sum (fun k hk => (inv_pos.mpr (hv k)).le) (Finset.mem_univ _)
  have hv0pos : 0 < v (0 : Idx) := hv 0
  have h_one_le_v0C : (1 : ℝ) ≤ v (0 : Idx) * C := by
    calc
      (1 : ℝ) = v (0 : Idx) * (v (0 : Idx))⁻¹ := by
        field_simp [hv0pos.ne']
      _ ≤ v (0 : Idx) * C := mul_le_mul_of_nonneg_left hinv_le_C hv0pos.le
  have h_one_le_tmC : (1 : ℝ) ≤ totalMass v n * C := by
    exact le_trans h_one_le_v0C
      (mul_le_mul_of_nonneg_right (totalMass_ge_v0_of_pos hv n) hCpos.le)
  have hlog_mul_nonneg : 0 ≤ Real.log (totalMass v n * C) := by
    rw [← Real.log_one]
    exact Real.log_le_log zero_lt_one h_one_le_tmC
  have hnum_nonneg : 0 ≤ Real.log (totalMass v n) + Real.log C := by
    rwa [Real.log_mul htmpos.ne' hCpos.ne'] at hlog_mul_nonneg
  exact div_nonneg hnum_nonneg (Nat.cast_nonneg n)

theorem A7pow10_row0_ge_one (j : Idx) : (1 : ℝ) ≤ A7pow10 (0 : Idx) j := by
  fin_cases j <;> norm_num [A7pow10]

theorem A7pow10_col_sum_le_300 (j : Idx) :
    (∑ i : Idx, A7pow10 i j) ≤ (300 : ℝ) := by
  fin_cases j <;> norm_num [A7pow10, Fin.sum_univ_succ]

theorem firstCoord_ten_add_ge_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) (n : ℕ) :
    totalMass v n ≤ firstCoord v (10 + n) := by
  let x : Idx → ℝ := A7 ^ n *ᵥ v
  have hx_nonneg : ∀ j : Idx, 0 ≤ x j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : firstCoord v (10 + n) = ∑ j : Idx, A7pow10 (0 : Idx) j * x j := by
    simp only [firstCoord]
    rw [pow_add, ← Matrix.mulVec_mulVec, A7_pow10]
    rfl
  rw [h_expand]
  simp only [totalMass]
  calc
    (∑ j : Idx, x j) = ∑ j : Idx, (1 : ℝ) * x j := by simp
    _ ≤ ∑ j : Idx, A7pow10 (0 : Idx) j * x j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7pow10_row0_ge_one j) (hx_nonneg j)

theorem totalMass_ten_add_le_300 {v : Idx → ℝ} (hv : ∀ i, 0 < v i) (n : ℕ) :
    totalMass v (10 + n) ≤ (300 : ℝ) * totalMass v n := by
  let w : Idx → ℝ := A7 ^ n *ᵥ v
  have hw_nonneg : ∀ j : Idx, 0 ≤ w j := A7_iterate_nonneg (fun i => (hv i).le) n
  have h_expand : totalMass v (10 + n) = ∑ j : Idx, (∑ i : Idx, A7pow10 i j) * w j := by
    simp only [totalMass]
    rw [pow_add, ← Matrix.mulVec_mulVec, A7_pow10]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [w, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [h_expand]
  calc
    (∑ j : Idx, (∑ i : Idx, A7pow10 i j) * w j)
        ≤ ∑ j : Idx, (300 : ℝ) * w j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (A7pow10_col_sum_le_300 j) (hw_nonneg j)
    _ = (300 : ℝ) * totalMass v n := by
      simp [totalMass, w, Finset.mul_sum]

theorem firstCoord_eventually_lower_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ᶠ n in atTop, ((1 : ℝ) / 300) * totalMass v n ≤ firstCoord v n := by
  filter_upwards [eventually_ge_atTop (10 : ℕ)] with N hN
  rcases Nat.exists_eq_add_of_le hN with ⟨n, rfl⟩
  have htm_pos : 0 < totalMass v (10 + n) := totalMass_pos_of_pos hv (10 + n)
  have hupper := totalMass_ten_add_le_300 hv n
  have hlower := firstCoord_ten_add_ge_totalMass hv n
  have h300pos : (0 : ℝ) < 300 := by norm_num
  calc
    ((1 : ℝ) / 300) * totalMass v (10 + n)
        ≤ (1 / 300 : ℝ) * ((300 : ℝ) * totalMass v n) := by
      exact mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = totalMass v n := by ring
    _ ≤ firstCoord v (10 + n) := hlower

theorem firstCoord_le_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ n, firstCoord v n ≤ totalMass v n := by
  intro n
  have hnon : ∀ i : Idx, 0 ≤ (A7 ^ n *ᵥ v) i := A7_iterate_nonneg (fun i => (hv i).le) n
  exact Finset.single_le_sum (fun x hx => hnon x) (Finset.mem_univ _)

theorem firstCoord_eventually_upper_totalMass {v : Idx → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ᶠ n in atTop, firstCoord v n ≤ (1 : ℝ) * totalMass v n := by
  filter_upwards with n
  simpa using firstCoord_le_totalMass hv n

/-- Fully automatic concrete corollary: every strictly positive initial vector has a
convergent first-coordinate root-growth sequence for the `A7` orbit. -/
theorem exists_firstCoord_A7_root_limit_of_pos
    (v : Idx → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (firstCoord v n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  refine exists_firstCoord_A7_root_limit_from_totalMass_bounds
    v (totalMass_pos_of_pos hv) (firstCoord_nonneg_of_nonneg (fun i => (hv i).le))
    (C := ∑ j : Idx, (v j)⁻¹) (c := (1 : ℝ) / 300) (d := 1)
    ?hC ?hc ?hd ?hsub ?hbdd ?hlo ?hhi
  · exact invSum_pos_of_pos hv
  · norm_num
  · norm_num
  · exact totalMass_almost_submultiplicative_invSum hv
  · exact totalMass_log_bddBelow_invSum hv
  · exact firstCoord_eventually_lower_totalMass hv
  · exact firstCoord_eventually_upper_totalMass hv







private lemma A381587_S_4_val : A381587_S 4 = 3 := by native_decide
private lemma A381587_S_5_val : A381587_S 5 = 5 := by native_decide
private lemma A381587_S_6_val : A381587_S 6 = 9 := by native_decide
private lemma A381587_S_7_val : A381587_S 7 = 15 := by native_decide
private lemma A381587_S_8_val : A381587_S 8 = 25 := by native_decide
private lemma A381587_S_9_val : A381587_S 9 = 41 := by native_decide
private lemma A381587_S_10_val : A381587_S 10 = 67 := by native_decide
private lemma A381587_S_11_val : A381587_S 11 = 109 := by native_decide
private lemma A381587_S_12_val : A381587_S 12 = 175 := by native_decide
private lemma A381587_S_13_val : A381587_S 13 = 277 := by native_decide
private lemma A381587_S_14_val : A381587_S 14 = 433 := by native_decide

private lemma A381587_bR_4_val : A381587_bR 4 = 6 := by
  unfold A381587_bR; rw [A381587_S_4_val]; norm_num
private lemma A381587_bR_5_val : A381587_bR 5 = 8 := by
  unfold A381587_bR; rw [A381587_S_5_val]; norm_num
private lemma A381587_bR_6_val : A381587_bR 6 = 12 := by
  unfold A381587_bR; rw [A381587_S_6_val]; norm_num
private lemma A381587_bR_7_val : A381587_bR 7 = 18 := by
  unfold A381587_bR; rw [A381587_S_7_val]; norm_num
private lemma A381587_bR_8_val : A381587_bR 8 = 28 := by
  unfold A381587_bR; rw [A381587_S_8_val]; norm_num
private lemma A381587_bR_9_val : A381587_bR 9 = 44 := by
  unfold A381587_bR; rw [A381587_S_9_val]; norm_num
private lemma A381587_bR_10_val : A381587_bR 10 = 70 := by
  unfold A381587_bR; rw [A381587_S_10_val]; norm_num
private lemma A381587_bR_11_val : A381587_bR 11 = 112 := by
  unfold A381587_bR; rw [A381587_S_11_val]; norm_num
private lemma A381587_bR_12_val : A381587_bR 12 = 178 := by
  unfold A381587_bR; rw [A381587_S_12_val]; norm_num
private lemma A381587_bR_13_val : A381587_bR 13 = 280 := by
  unfold A381587_bR; rw [A381587_S_13_val]; norm_num
private lemma A381587_bR_14_val : A381587_bR 14 = 436 := by
  unfold A381587_bR; rw [A381587_S_14_val]; norm_num

/-- The `A7` state naturally attached to the shifted `bR` sequence.  At shift `k` it is
`[b_{k+8}, Δ b_{k+8}, Δ² b_{k+8}, b_{k+4}, b_{k+5}, b_{k+6}, b_{k+7}]`. -/
private def A381587_bR_A7_state (k : ℕ) : Idx → ℝ
  | 0 => A381587_bR (k + 8)
  | 1 => A381587_bR (k + 9) - A381587_bR (k + 8)
  | 2 => A381587_bR (k + 10) - 2 * A381587_bR (k + 9) + A381587_bR (k + 8)
  | 3 => A381587_bR (k + 4)
  | 4 => A381587_bR (k + 5)
  | 5 => A381587_bR (k + 6)
  | 6 => A381587_bR (k + 7)

private def A381587_bR_A7_v : Idx → ℝ := A381587_bR_A7_state 0

private lemma A381587_bR_delta3_shift (k : ℕ) :
    A381587_bR (k + 11) - 3 * A381587_bR (k + 10) +
        3 * A381587_bR (k + 9) - A381587_bR (k + 8) = A381587_bR (k + 4) := by
  rcases lt_or_ge k 4 with hk | hk
  · interval_cases k <;> norm_num [A381587_bR_4_val, A381587_bR_5_val,
      A381587_bR_6_val, A381587_bR_7_val, A381587_bR_8_val, A381587_bR_9_val,
      A381587_bR_10_val, A381587_bR_11_val, A381587_bR_12_val,
      A381587_bR_13_val, A381587_bR_14_val]
  · rcases Nat.exists_eq_add_of_le hk with ⟨s, rfl⟩
    have h := A381587_scalar_recurrence_bR s
    have h' : A381587_bR (s + 15) - 3 * A381587_bR (s + 14) +
        3 * A381587_bR (s + 13) - A381587_bR (s + 12) = A381587_bR (s + 8) := by
      nlinarith [h]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

private lemma A381587_bR_A7_state_succ (k : ℕ) :
    A7 *ᵥ A381587_bR_A7_state k = A381587_bR_A7_state (k + 1) := by
  ext i
  fin_cases i
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    have h := A381587_bR_delta3_shift k
    nlinarith [h]
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [A381587_bR_A7_state, A7, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem A381587_bR_A7_orbit_state (k : ℕ) :
    A7 ^ k *ᵥ A381587_bR_A7_v = A381587_bR_A7_state k := by
  induction k with
  | zero =>
      simp [A381587_bR_A7_v]
  | succ k ih =>
      rw [show A7 ^ (k + 1) = A7 * A7 ^ k by simpa using (pow_succ' A7 k),
        ← Matrix.mulVec_mulVec, ih]
      simpa [Nat.succ_eq_add_one] using A381587_bR_A7_state_succ k

private theorem A381587_exists_positive_A7_state_for_bR_shift :
    ∃ v : Idx → ℝ, (∀ i, 0 < v i) ∧
      ∀ k : ℕ, firstCoord v k = A381587_bR (k + 8) := by
  refine ⟨A381587_bR_A7_v, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [A381587_bR_A7_v, A381587_bR_A7_state,
      A381587_bR_4_val, A381587_bR_5_val, A381587_bR_6_val, A381587_bR_7_val,
      A381587_bR_8_val, A381587_bR_9_val, A381587_bR_10_val]
  · intro k
    rw [firstCoord, A381587_bR_A7_orbit_state]
    simp [A381587_bR_A7_state]

private theorem A381587_bR_shifted_root_limit :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (A381587_bR (k + 8)) ^ ((1 : ℝ) / (k : ℝ))) atTop (𝓝 L) := by
  rcases A381587_exists_positive_A7_state_for_bR_shift with ⟨v, hvpos, hfirst⟩
  rcases exists_firstCoord_A7_root_limit_of_pos v hvpos with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  refine hL.congr' ?_
  filter_upwards with k
  rw [hfirst k]



/- Final transfer from the shifted `bR = S + 3` root limit to the row-sum root limit. -/

private lemma A381587_S_nonneg_real (n : ℕ) : 0 ≤ (A381587_S n : ℝ) := by
  exact_mod_cast (Nat.zero_le (A381587_S n))

private lemma A381587_bR_nonneg (n : ℕ) : 0 ≤ A381587_bR n := by
  unfold A381587_bR
  positivity

private theorem A381587_bR_shifted_root_limit_shifted_exponent :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (A381587_bR (k + 8)) ^ ((1 : ℝ) / ((k + 8 : ℕ) : ℝ))) atTop (𝓝 L) := by
  rcases A381587_bR_shifted_root_limit with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  have hexp : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 8)) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (8 : ℝ))
  have hpow : Tendsto (fun k : ℕ =>
      ((A381587_bR (k + 8)) ^ ((1 : ℝ) / (k : ℝ))) ^
        ((k : ℝ) / ((k : ℝ) + 8))) atTop (𝓝 L) := by
    simpa [Real.rpow_one] using hL.rpow hexp (Or.inr zero_lt_one)
  refine hpow.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hbase : 0 ≤ A381587_bR (k + 8) := A381587_bR_nonneg (k + 8)
  calc
    ((A381587_bR (k + 8)) ^ ((1 : ℝ) / (k : ℝ))) ^
          ((k : ℝ) / ((k : ℝ) + 8))
        = (A381587_bR (k + 8)) ^
            (((1 : ℝ) / (k : ℝ)) * ((k : ℝ) / ((k : ℝ) + 8))) := by
          rw [Real.rpow_mul hbase]
    _ = (A381587_bR (k + 8)) ^ ((1 : ℝ) / ((k + 8 : ℕ) : ℝ)) := by
          congr 1
          rw [Nat.cast_add]
          norm_num
          field_simp [hk0]

private theorem A381587_bR_root_limit :
    ∃ L : ℝ, Tendsto (fun n : ℕ =>
      (A381587_bR n) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  rcases A381587_bR_shifted_root_limit_shifted_exponent with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  exact (Filter.tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => (A381587_bR n) ^ ((1 : ℝ) / (n : ℝ))) 8).mp hL

private lemma A381587_S_ge_one_eventually :
    ∀ᶠ n : ℕ in atTop, 1 ≤ A381587_S n := by
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases A381587_T_suffix_12 k with ⟨xs, hxs⟩
  change 1 ≤ (A381587_T (4 + k)).sum
  rw [show 4 + k = k + 4 by omega, hxs]
  simp

private lemma A381587_bR_le_four_S_eventually :
    ∀ᶠ n : ℕ in atTop, A381587_bR n ≤ 4 * (A381587_S n : ℝ) := by
  filter_upwards [A381587_S_ge_one_eventually] with n hn
  unfold A381587_bR
  have hnR : (1 : ℝ) ≤ (A381587_S n : ℝ) := by exact_mod_cast hn
  nlinarith

private lemma A381587_S_le_bR (n : ℕ) :
    (A381587_S n : ℝ) ≤ A381587_bR n := by
  unfold A381587_bR
  linarith

private theorem A381587_S_root_limit_div :
    ∃ L : ℝ, Tendsto (fun n : ℕ =>
      (A381587_S n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (𝓝 L) := by
  rcases A381587_bR_root_limit with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  refine rpow_one_div_sandwich (a := fun n : ℕ => (A381587_S n : ℝ))
    (b := A381587_bR) (L := L) (c := (1 / 4 : ℝ)) (d := 1) ?_ ?_
    A381587_bR_nonneg A381587_S_nonneg_real hL ?_ ?_
  · norm_num
  · norm_num
  · filter_upwards [A381587_bR_le_four_S_eventually] with n hn
    nlinarith
  · filter_upwards with n
    simpa [one_mul] using A381587_S_le_bR n

/-- Scratch version of the final `Spec.lean` theorem, with inverse-exponent notation. -/
theorem A381587_S_limit_exists :
    ∃ L : ℝ, Tendsto (fun n : ℕ =>
      (A381587_S n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 L) := by
  rcases A381587_S_root_limit_div with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  simpa [one_div] using hL
