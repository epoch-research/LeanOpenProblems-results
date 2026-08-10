import FormalConjectures.Util.ProblemImports

open Nat

/--
A290472: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 7z^2$, where $x$ is a positive integer, and $y$ and $z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  let R : ℕ := Nat.sqrt N + 1
  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R
  let search_space := X.product (Y.product Z)
  Finset.card $ Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd
    x > 0 ∧ x * x + 3 * y * y + 7 * z * z = N) search_space

abbrev Triple := ℕ × ℕ × ℕ

def MOD : Nat := 24640
def MOD3 : Nat := 73920

def setSqMod (fuel i : Nat) (arr : Array Bool) : Array Bool :=
  match fuel with
  | 0 => arr
  | fuel'+1 => setSqMod fuel' (i+1) (arr.set! ((i*i) % MOD) true)

def sqModArr : Array Bool := setSqMod MOD 0 (Array.replicate MOD false)

def allowedForAux (fuel z a : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel'+1 =>
    let zz := (7*z*z) % MOD3
    let rem := (a + MOD3 - zz) % MOD3
    if rem % 3 = 0 && sqModArr.getD ((rem/3) % MOD) false then
      allowedForAux fuel' (z+1) a (z :: acc)
    else
      allowedForAux fuel' (z+1) a acc

def allowedFor (a : Nat) : List Nat := (allowedForAux 651 0 a []).reverse

def buildAllowedAux (fuel a : Nat) (arr : Array (List Nat)) : Array (List Nat) :=
  match fuel with
  | 0 => arr
  | fuel'+1 => buildAllowedAux fuel' (a+1) (arr.set! a (allowedFor a))

def allowedArr : Array (List Nat) := buildAllowedAux MOD3 0 (Array.replicate MOD3 [])

def maxY2 : Nat := 20000001

def setSquares (fuel i : Nat) (arr : Array Bool) : Array Bool :=
  match fuel with
  | 0 => arr
  | fuel'+1 => setSquares fuel' (i+1) (arr.set! (i*i) true)

def squareArr : Array Bool := setSquares 4473 0 (Array.replicate maxY2 false)

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : ℕ) (t : Triple) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if repB N t then
    match fst with
    | none => Sum.inr (some t)
    | some u => if decide (u = t) then Sum.inr fst else Sum.inl (u,t)
  else Sum.inr fst

def searchZList (zs : List Nat) (N k d : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  match zs with
  | [] => Sum.inr fst
  | z :: zs' =>
    let x := k - d
    let rem0 := N - x*x
    let zz := 7*z*z
    if zz > rem0 then searchZList zs' N k d fst else
    let rem := rem0 - zz
    if rem % 3 = 0 && squareArr.getD (rem/3) false then
      let y := Nat.sqrt (rem/3)
      match upd N (x,y,z) fst with
      | Sum.inl p => Sum.inl p
      | Sum.inr fst' => searchZList zs' N k d fst'
    else searchZList zs' N k d fst

def searchDFuel (fuel N k d : Nat) (fst : Option Triple) : Option (Triple × Triple) :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    let rem0 := N - (k-d)*(k-d)
    let zs := allowedArr.getD (rem0 % MOD3) []
    match searchZList zs N k d fst with
    | Sum.inl p => some p
    | Sum.inr fst' => searchDFuel fuel' N k (d+1) fst'

def findTwoK (n k : Nat) : Option (Triple × Triple) :=
  let N := 6*n+1
  searchDFuel 233 N k 0 none

def checkOneK (n k : Nat) : Bool :=
  match findTwoK n k with
  | some (u,v) => repB (6*n+1) u && repB (6*n+1) v && decide (u ≠ v)
  | none => false

def nextK (n k : Nat) : Nat :=
  if (k+1)*(k+1) ≤ 6*(n+1)+1 then k+1 else k

def checkFuelK (fuel n k : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkOneK n k && checkFuelK fuel' (n+1) (nextK n k)

def checkRange (lo hi : Nat) : Bool := checkFuelK (hi+1-lo) lo (Nat.sqrt (6*lo+1))

set_option maxRecDepth 1000000

theorem checked_low : checkRange 287 5000000 = true := by native_decide

theorem checked_high : checkRange 5000001 10000000 = true := by native_decide

lemma in_search_of_rep {n x y z : ℕ}
    (hx : 0 < x)
    (hrep : x * x + 3 * y * y + 7 * z * z = 6 * n + 1) :
    (x, (y, z)) ∈
      (Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
        ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
          (Finset.range (Nat.sqrt (6 * n + 1) + 1))) := by
  simp [Finset.mem_product, Finset.mem_range]
  constructor
  · have hxle : x * x ≤ 6 * n + 1 := by omega
    have : x ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hxle
    omega
  constructor
  · have hyle : y * y ≤ 6 * n + 1 := by nlinarith [hrep]
    have : y ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hyle
    omega
  · have hzle : z * z ≤ 6 * n + 1 := by nlinarith [hrep]
    have : z ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hzle
    omega

lemma a_gt_one_of_two {n x₁ y₁ z₁ x₂ y₂ z₂ : ℕ}
    (hneq : (x₁, (y₁, z₁)) ≠ (x₂, (y₂, z₂)))
    (hx₁ : 0 < x₁)
    (hrep₁ : x₁ * x₁ + 3 * y₁ * y₁ + 7 * z₁ * z₁ = 6 * n + 1)
    (hx₂ : 0 < x₂)
    (hrep₂ : x₂ * x₂ + 3 * y₂ * y₂ + 7 * z₂ * z₂ = 6 * n + 1) :
    a n > 1 := by
  rw [a]
  change 1 < Finset.card (Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd
    x > 0 ∧ x * x + 3 * y * y + 7 * z * z = 6 * n + 1)
    ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
      ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
        (Finset.range (Nat.sqrt (6 * n + 1) + 1)))))
  rw [Finset.one_lt_card_iff]
  refine ⟨(x₁, (y₁, z₁)), (x₂, (y₂, z₂)), ?_, ?_, hneq⟩
  · simp only [Finset.mem_filter]
    exact ⟨in_search_of_rep hx₁ hrep₁, hx₁, hrep₁⟩
  · simp only [Finset.mem_filter]
    exact ⟨in_search_of_rep hx₂ hrep₂, hx₂, hrep₂⟩

lemma repB_true {N : ℕ} {t : Triple} (h : repB N t = true) :
    0 < t.1 ∧ t.1 * t.1 + 3 * t.2.1 * t.2.1 + 7 * t.2.2 * t.2.2 = N := by
  unfold repB at h
  simpa using h

lemma a_gt_one_of_checkOneK {n k : ℕ} (h : checkOneK n k = true) : a n > 1 := by
  unfold checkOneK at h
  cases hfind : findTwoK n k with
  | none =>
    rw [hfind] at h
    contradiction
  | some p =>
    rcases p with ⟨u, v⟩
    rw [hfind] at h
    simp at h
    rcases u with ⟨x₁, y₁, z₁⟩
    rcases v with ⟨x₂, y₂, z₂⟩
    have h₁ := repB_true (N := 6*n+1) (t := (x₁,y₁,z₁)) h.1.1
    have h₂ := repB_true (N := 6*n+1) (t := (x₂,y₂,z₂)) h.1.2
    exact a_gt_one_of_two h.2 h₁.1 h₁.2 h₂.1 h₂.2

lemma checkFuelK_true {fuel lo k n : ℕ}
    (h : checkFuelK fuel lo k = true) (hnlo : lo ≤ n) (hnhi : n < lo + fuel) :
    ∃ k', checkOneK n k' = true := by
  induction fuel generalizing lo k n with
  | zero => omega
  | succ fuel ih =>
    simp [checkFuelK] at h
    by_cases hn : n = lo
    · subst n
      exact ⟨k, h.1⟩
    · exact ih h.2 (by omega) (by omega)

lemma checkRange_true {lo hi n : ℕ} (h : checkRange lo hi = true)
    (hlo : lo ≤ n) (hhi : n ≤ hi) : ∃ k, checkOneK n k = true := by
  unfold checkRange at h
  apply checkFuelK_true h hlo
  omega

/--
In support of the first conjecture, a(n) > 1 for $286 < n \\le 10^7$.
-/
theorem oeis_290472_conjecture_3 :
  ∀ n : ℕ, 286 < n ∧ n ≤ 10000000 → a n > 1 := by
  intro n hn
  by_cases hmid : n ≤ 5000000
  · rcases checkRange_true checked_low (by omega) hmid with ⟨k, hk⟩
    exact a_gt_one_of_checkOneK hk
  · rcases checkRange_true checked_high (by omega) hn.2 with ⟨k, hk⟩
    exact a_gt_one_of_checkOneK hk
