import FormalConjectures.Util.ProblemImports

open Nat

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

abbrev Row := Nat×Nat×Nat×Nat×Nat×Nat

def goodRow (n : Nat) (r : Row) : Bool :=
  let (x1,y1,z1,x2,y2,z2) := r
  decide (0 < x1 ∧ x1*x1+3*y1*y1+7*z1*z1 = 6*n+1 ∧ 0<x2 ∧ x2*x2+3*y2*y2+7*z2*z2=6*n+1 ∧ (x1,y1,z1) ≠ (x2,y2,z2))

def checkAux (base : Nat) (rows : Array Row) (i fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => goodRow (base+i) (rows.getD i (0,0,0,0,0,0)) && checkAux base rows (i+1) fuel'
def rows0 : Array Row := #[
  (20,21,0,39,3,5),
  (41,4,0,31,16,0),
  (36,12,1,6,23,4),
  (17,22,0,39,8,2),
  (40,7,0,41,1,3),
  (5,24,0,21,20,4),
  (26,19,0,12,23,2),
  (3,24,2,27,14,8),
  (42,0,1,39,9,1),
  (7,24,0,35,10,6),
  (14,23,0,42,2,1),
  (41,6,0,33,14,4),
  (42,1,2,30,17,2),
  (37,12,0,31,14,6),
  (38,11,0,22,21,0),
  (35,14,0,29,18,0),
  (42,4,1,27,19,1),
  (25,20,0,39,8,4),
  (34,15,0,36,13,2),
  (9,24,2,33,10,8),
  (40,9,0,16,23,0),
  (43,0,0,11,24,0),
  (40,8,3,32,16,3),
  (43,2,0,29,16,6),
  (28,19,0,42,5,2),
  (41,8,0,13,22,6),
  (2,25,0,42,6,1),
  (33,16,2,17,14,12),
  (32,17,0,4,25,0),
  (43,4,0,13,24,0),
  (42,3,4,36,12,5),
  (35,12,6,3,22,8),
  (43,1,3,23,21,3),
  (21,22,2,9,24,4),
  (24,21,2,40,5,6),
  (31,18,0,39,10,4),
  (44,1,0,8,25,0),
  (41,2,6,27,16,8),
  (38,13,0,42,5,4),
  (43,6,0,37,14,0),
  (44,3,0,40,11,0),
  (33,16,4,39,0,8),
  (10,25,0,20,21,6),
  (41,10,0,23,22,0),
  (20,23,0,43,5,3),
  (35,16,0,17,22,6),
  (26,21,0,36,15,2),
  (21,22,4,5,24,6),
  (44,5,0,30,19,2),
  (17,24,0,39,4,8),
  (34,17,0,42,7,4),
  (1,26,0,7,24,6),
  (45,1,1,39,13,1),
  (43,8,0,29,20,0),
  (12,25,2,44,4,3),
  (5,26,0,45,0,2),
  (45,3,1,27,21,1),
  (45,2,2,3,26,2),
  (22,23,0,14,25,0),
  (25,22,0,7,26,0),
  (44,7,0,36,15,4),
  (19,24,0,33,18,2),
  (40,12,3,38,14,3),
  (45,4,2,43,0,6),
  (40,13,0,32,19,0),
  (41,12,0,43,2,6),
  (46,1,0,38,15,0),
  (41,8,6,33,14,8),
  (16,25,0,12,25,4),
  (37,16,0,39,14,2),
  (46,3,0,32,17,6),
  (43,10,0,11,26,0),
  (42,11,2,43,9,3),
  (31,20,0,45,6,2),
  (40,0,9,20,20,9),
  (33,18,4,9,10,16),
  (44,9,0,45,7,1),
  (45,4,4,31,18,6),
  (46,5,0,2,27,0),
  (35,18,0,13,26,0),
  (4,27,0,42,12,1),
  (47,0,0,27,22,2),
  (44,3,6,40,11,6),
  (47,2,0,39,14,4),
  (18,25,2,46,4,3),
  (41,10,6,23,22,6),
  (34,19,0,42,11,4),
  (45,8,2,45,6,4),
  (8,27,0,30,21,2),
  (47,4,0,23,24,0),
  (46,7,0,26,23,0),
  (41,14,0,17,24,6),
  (40,15,0,20,25,0),
  (43,12,0,15,26,2),
  (10,27,0,46,6,3),
  (29,22,0,27,22,4),
  (44,11,0,42,13,2),
  (5,26,6,33,16,8),
  (38,17,0,48,0,1),
  (47,6,0,17,26,0)
]
def rows1 : Array Row := #[
  (48,2,1,27,23,1),
  (45,8,4,25,22,6),
  (48,1,2,30,21,4),
  (37,18,0,19,24,6),
  (32,21,0,47,5,3),
  (25,24,0,1,28,0),
  (46,9,0,22,25,0),
  (15,26,4,41,12,6),
  (28,23,0,46,8,3),
  (5,28,0,27,20,8),
  (14,27,0,42,13,4),
  (19,26,0,3,28,2),
  (45,11,1,39,17,1),
  (49,0,0,47,8,0),
  (48,5,2,36,19,2),
  (49,2,0,31,22,0),
  (48,6,1,33,21,1),
  (35,20,0,37,4,12),
  (44,12,3,40,16,3),
  (43,14,0,45,10,4),
  (44,13,0,16,27,0),
  (49,4,0,41,16,0),
  (4,27,6,42,9,8),
  (9,28,2,47,0,6),
  (40,17,0,42,15,2),
  (11,28,0,3,28,4),
  (46,11,0,34,21,0),
  (45,12,2,27,24,2),
  (49,3,3,29,23,3),
  (21,26,2,17,20,12),
  (50,1,0,48,8,1),
  (49,6,0,47,10,0),
  (30,23,2,47,9,3),
  (13,28,0,39,18,2),
  (50,3,0,38,19,0),
  (43,12,6,35,10,12),
  (4,29,0,45,13,1),
  (9,28,4,29,22,6),
  (26,25,0,42,15,4),
  (23,26,0,39,14,8),
  (50,0,3,25,25,3),
  (37,20,0,29,24,0),
  (50,5,0,48,9,2),
  (21,26,4,45,6,8),
  (20,27,0,8,29,0),
  (49,8,0,37,18,6),
  (30,23,4,32,21,6),
  (15,28,2,39,18,4),
  (44,15,0,32,23,0),
  (43,16,0,21,24,8),
  (46,13,0,10,29,0),
  (51,0,2,5,28,6),
  (51,3,1,30,24,1),
  (47,12,0,17,28,0),
  (50,7,0,36,21,2),
  (41,18,0,25,26,0),
  (28,25,0,42,17,2),
  (49,2,6,31,22,6),
  (22,27,0,50,6,3),
  (35,22,0,51,4,2),
  (40,19,0,51,5,1),
  (31,24,0,15,28,4),
  (48,11,2,12,29,2),
  (49,10,0,1,30,0),
  (52,1,0,45,15,1),
  (19,28,0,51,0,4),
  (14,29,0,40,17,6),
  (5,30,0,51,2,4),
  (52,3,0,36,21,4),
  (51,6,2,3,30,2),
  (50,9,0,34,23,0),
  (7,30,0,39,20,2),
  (51,7,1,36,22,1),
  (51,4,4,49,6,6),
  (38,21,0,52,0,3),
  (13,28,6,45,10,8),
  (52,5,0,16,29,0),
  (27,26,2,7,24,12),
  (46,15,0,24,27,2),
  (47,14,0,41,6,12),
  (44,17,0,30,25,2),
  (53,0,0,9,30,2),
  (52,4,3,32,24,3),
  (53,2,0,43,18,0),
  (49,11,3,41,19,3),
  (49,12,0,39,20,4),
  (48,13,2,20,27,6),
  (33,24,2,49,8,6),
  (52,7,0,51,9,1),
  (53,4,0,43,0,12),
  (50,11,0,26,27,0),
  (29,26,0,13,30,0),
  (42,19,2,18,29,2),
  (41,20,0,23,28,0),
  (2,31,0,30,25,4),
  (9,30,4,47,12,6),
  (32,25,0,4,31,0),
  (51,8,4,45,16,4),
  (36,23,2,48,12,5),
  (53,6,0,21,26,8)
]
def rowsOf : Nat -> Array Row
| 0 => rows0
| 1 => rows1
| _ => #[]
def numChunks : Nat := 2
def chunkSize : Nat := 100
def chunkBase (j:Nat) := 287+chunkSize*j
def chunkLen (j:Nat) := if j = numChunks-1 then 100 else chunkSize
def checkChunk (j:Nat) : Bool := checkAux (chunkBase j) (rowsOf j) 0 (chunkLen j)
theorem cert0 : checkChunk 0 = true := by decide +kernel
theorem cert1 : checkChunk 1 = true := by decide +kernel
def checkAllAux (j fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => checkChunk j && checkAllAux (j+1) fuel'

theorem checked_all : checkAllAux 0 numChunks = true := by
  simp [checkAllAux, cert0, cert1, numChunks]

lemma checkAllAux_true {j fuel k : Nat}
    (h : checkAllAux j fuel = true) (hlo : j ≤ k) (hhi : k < j + fuel) :
    checkChunk k = true := by
  induction fuel generalizing j with
  | zero => omega
  | succ fuel ih =>
    simp [checkAllAux] at h
    by_cases hk : k = j
    · subst k
      exact h.1
    · exact ih h.2 (by omega) (by omega)

lemma checkAux_true {base : Nat} {rows : Array Row} {fuel i n : Nat}
    (h : checkAux base rows i fuel = true) (hlo : base + i ≤ n) (hhi : n < base + i + fuel) :
    ∃ r, goodRow n r = true := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp [checkAux] at h
    by_cases hn : n = base + i
    · subst n
      exact ⟨rows[i]?.getD (0,0,0,0,0,0), h.1⟩
    · exact ih h.2 (by omega) (by omega)

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
    (hneq : (x₁, y₁, z₁) ≠ (x₂, y₂, z₂))
    (hx₁ : 0 < x₁)
    (hrep₁ : x₁ * x₁ + 3 * y₁ * y₁ + 7 * z₁ * z₁ = 6 * n + 1)
    (hx₂ : 0 < x₂)
    (hrep₂ : x₂ * x₂ + 3 * y₂ * y₂ + 7 * z₂ * z₂ = 6 * n + 1) :
    a n > 1 := by
  rw [a]
  change 1 < Finset.card (Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst; let y := p.snd.fst; let z := p.snd.snd
    x > 0 ∧ x * x + 3 * y * y + 7 * z * z = 6 * n + 1)
    ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
      ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
        (Finset.range (Nat.sqrt (6 * n + 1) + 1)))))
  rw [Finset.one_lt_card_iff]
  refine ⟨(x₁, (y₁, z₁)), (x₂, (y₂, z₂)), ?_, ?_, ?_⟩
  · simp only [Finset.mem_filter]
    exact ⟨in_search_of_rep hx₁ hrep₁, hx₁, hrep₁⟩
  · simp only [Finset.mem_filter]
    exact ⟨in_search_of_rep hx₂ hrep₂, hx₂, hrep₂⟩
  · intro h
    apply hneq
    simpa using h

lemma a_gt_one_of_goodRow {n r} (h : goodRow n r = true) : a n > 1 := by
  unfold goodRow at h
  rcases r with ⟨x₁,y₁,z₁,x₂,y₂,z₂⟩
  simp at h
  have hneq : (x₁, y₁, z₁) ≠ (x₂, y₂, z₂) := by
    intro heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    simp at h
  exact a_gt_one_of_two hneq h.1 h.2.1 h.2.2.1 h.2.2.2.1

theorem small : ∀ n : ℕ, 286 < n ∧ n ≤ 486 → a n > 1 := by
  intro n hn
  let j := (n - 287) / chunkSize
  have hj : j < numChunks := by
    simp [j, numChunks, chunkSize]
    omega
  have hbase : chunkBase j ≤ n := by
    simp [j, chunkBase, chunkSize]
    omega
  have htop : n < chunkBase j + chunkLen j := by
    simp [j, chunkBase, chunkLen, chunkSize, numChunks]
    omega
  have hch : checkChunk j = true := checkAllAux_true checked_all (Nat.zero_le j) (by simpa [j] using hj)
  unfold checkChunk at hch
  rcases checkAux_true hch hbase htop with ⟨r, hr⟩
  exact a_gt_one_of_goodRow hr
#print axioms small
