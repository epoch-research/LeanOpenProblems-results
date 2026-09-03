import FormalConjecturesUtil

/-!
# Finite ordered-representation obstructions (partial results only)

This file concerns finite initial intervals and **global** bounds on the ordered
representation function `AdditiveCombinatorics.sumRep`. It neither proves nor
refutes the Erdős–Turán conjecture. It does not import `Submission.Spec` or
`Submission.Reduction`.

A certificate is a chronological binary prefix tree. Its root is `(1, 1)`;
`mask` encodes the already chosen elements below `n`. An omit edge leads to
`(n + 1, mask)`, an include edge to `(n + 1, mask ||| 2 ^ n)`. Labels are thus
implicit. Every missing omit edge is checked to have no representation of `n`;
every missing include edge supplies an integer whose ordered representation
count exceeds the cap. Both remaining edges must be checked recursively.
All nodes must lie within the coverage horizon. This also allows redundant
inadmissible edges: soundness only requires that no admissible edge is missing.

The checker does not trust the search's assertions that earlier integers are
covered or that prefix counts obey the cap. Those facts follow along any
hypothetical branch from the arbitrary set being ruled out. In particular, an
include-edge witness is *not* restricted to the coverage horizon.

Large trees are split into small proof-carrying fragments. Each graft contains
an already proved subtree-checker equality, and its cached chronological state
is checked. `checkFragment_sound` proves that successful fragment checks assemble
into a successful check of the entire original binary tree. Every numerical
check uses kernel reduction (`decide +kernel`), never native evaluation.
-/

open Set AdditiveCombinatorics
open scoped Pointwise

namespace Erdos28.FiniteCertificate

/-- The finite set represented by a natural-number bit mask. -/
def maskSet (mask : ℕ) : Set ℕ := {a | mask.testBit a = true}

/-- A computable count of ordered pairs in a bit mask, not unordered pairs. -/
def repCount (mask s : ℕ) : ℕ :=
  ((Finset.antidiagonal s).filter
    (fun p : ℕ × ℕ ↦ mask.testBit p.1 = true ∧ mask.testBit p.2 = true)).card

/-- Connection between the executable count and the problem's genuine count. -/
theorem repCount_eq_sumRep (mask s : ℕ) :
    repCount mask s = sumRep (maskSet mask) s := by
  classical
  rw [sumRep_def]
  unfold repCount
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, maskSet, Set.mem_setOf_eq]

/-- Ordered representation counts are monotone under inclusion of sets. -/
theorem sumRep_mono {A B : Set ℕ} (h : A ⊆ B) (s : ℕ) :
    sumRep A s ≤ sumRep B s := by
  classical
  simp only [sumRep_def]
  apply Finset.card_le_card
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp, ha, hb⟩
  exact Finset.mem_filter.mpr ⟨hp, h ha, h hb⟩

/-- Positive ordered count is equivalent to membership in the sumset. -/
theorem sumRep_pos_iff (A : Set ℕ) (s : ℕ) :
    0 < sumRep A s ↔ s ∈ A + A := by
  classical
  rw [sumRep_def, Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, hp⟩
    rcases Finset.mem_filter.mp hp with ⟨hab, ha, hb⟩
    exact Set.mem_add.mpr ⟨a, ha, b, hb, Finset.mem_antidiagonal.mp hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hab, ha, hb⟩⟩

/-- Setting bit `n` is precisely adjoining `n` to the represented set. -/
theorem maskSet_include (mask n : ℕ) :
    maskSet (mask ||| 2 ^ n) = insert n (maskSet mask) := by
  ext a
  simp only [maskSet, Set.mem_setOf_eq, Set.mem_insert_iff, Nat.testBit_or,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  tauto

/-- The mask describes exactly the part of `A` below the next decision `n`.
This records the support bound as well as both membership directions. -/
def Matches (A : Set ℕ) (n mask : ℕ) : Prop :=
  ∀ a, a ∈ maskSet mask ↔ a < n ∧ a ∈ A

theorem Matches.subset {A : Set ℕ} {n mask : ℕ} (h : Matches A n mask) :
    maskSet mask ⊆ A := fun a ha ↦ (h a).mp ha |>.2

theorem Matches.omit {A : Set ℕ} {n mask : ℕ}
    (h : Matches A n mask) (hn : n ∉ A) : Matches A (n + 1) mask := by
  intro a
  rw [h a]
  constructor
  · rintro ⟨ha, hA⟩
    exact ⟨by omega, hA⟩
  · rintro ⟨ha, hA⟩
    refine ⟨?_, hA⟩
    by_contra hnot
    have : a = n := by omega
    exact hn (this ▸ hA)

theorem Matches.include {A : Set ℕ} {n mask : ℕ}
    (h : Matches A n mask) (hn : n ∈ A) :
    Matches A (n + 1) (mask ||| 2 ^ n) := by
  intro a
  rw [maskSet_include, Set.mem_insert_iff, h a]
  constructor
  · rintro (rfl | ⟨ha, hA⟩)
    · exact ⟨by omega, hn⟩
    · exact ⟨by omega, hA⟩
  · rintro ⟨ha, hA⟩
    by_cases han : a = n
    · exact Or.inl han
    · exact Or.inr ⟨by omega, hA⟩

/-- If zero is covered, the initial prefix is exactly `{0}`. -/
theorem matches_root {A : Set ℕ} (hzero : 0 ∈ A + A) : Matches A 1 1 := by
  obtain ⟨a, ha, b, _, hab⟩ := Set.mem_add.mp hzero
  have ha0 : a = 0 := by omega
  have h0 : 0 ∈ A := ha0 ▸ ha
  intro x
  simp only [maskSet, Set.mem_setOf_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · rintro rfl
    exact ⟨by omega, h0⟩
  · rintro ⟨hx, _⟩
    omega

/-- Coverage forces an omit edge to have a positive prefix count. -/
theorem omit_count_pos {A : Set ℕ} {n mask : ℕ} (h : Matches A n mask)
    (hn : n ∉ A) (hcov : n ∈ A + A) : 0 < repCount mask n := by
  rw [repCount_eq_sumRep, sumRep_pos_iff]
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hcov
  have han : a ≠ n := fun heq ↦ hn (heq ▸ ha)
  have hbn : b ≠ n := fun heq ↦ hn (heq ▸ hb)
  exact Set.mem_add.mpr ⟨a, (h a).mpr ⟨by omega, ha⟩,
    b, (h b).mpr ⟨by omega, hb⟩, hab⟩

/-- Prefix counts are bounded by the count of the arbitrary ambient set. -/
theorem count_le_of_matches {A : Set ℕ} {n mask : ℕ} (h : Matches A n mask)
    (s : ℕ) : repCount mask s ≤ sumRep A s := by
  rw [repCount_eq_sumRep]
  exact sumRep_mono h.subset s

/-- The four possibilities for the two edges. A missing include edge carries
an explicit sum at which adjoining the next element violates the global cap. -/
inductive Certificate where
  | closed (witness : ℕ)
  | onlyOmit (witness : ℕ) (child : Certificate)
  | onlyInclude (child : Certificate)
  | split (omitChild includeChild : Certificate)

/-- Boolean certificate checker. Only missing edges require numeric tests:
kept edges are recursively checked with their forced chronological labels. -/
def check (K N n mask : ℕ) : Certificate → Bool
  | .closed s => decide (n ≤ N) && decide (repCount mask n = 0) &&
      decide (K < repCount (mask ||| 2 ^ n) s)
  | .onlyOmit s c => decide (n ≤ N) && check K N (n + 1) mask c &&
      decide (K < repCount (mask ||| 2 ^ n) s)
  | .onlyInclude c => decide (n ≤ N) && decide (repCount mask n = 0) &&
      check K N (n + 1) (mask ||| 2 ^ n) c
  | .split c d => decide (n ≤ N) && check K N (n + 1) mask c &&
      check K N (n + 1) (mask ||| 2 ^ n) d

/-- Generic soundness, by structural induction on the finite certificate.
Every putative set must choose one of the two edges; a missing edge contradicts
coverage or the global cap, and a kept edge invokes a smaller certificate. -/
theorem check_sound (c : Certificate) (K N n mask : ℕ)
    (hc : check K N n mask c = true) (A : Set ℕ)
    (hm : Matches A n mask) (hcov : ∀ s ≤ N, s ∈ A + A)
    (hcap : ∀ s, sumRep A s ≤ K) : False := by
  induction c generalizing n mask with
  | closed s =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hn : n ∈ A
    · have hle := (count_le_of_matches (hm.include hn) s).trans (hcap s)
      omega
    · have hpos := omit_count_pos hm hn (hcov n hc.1.1)
      omega
  | onlyOmit s c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hn : n ∈ A
    · have hle := (count_le_of_matches (hm.include hn) s).trans (hcap s)
      omega
    · exact ih (n + 1) mask hc.1.2 (hm.omit hn)
  | onlyInclude c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hn : n ∈ A
    · exact ih (n + 1) (mask ||| 2 ^ n) hc.2 (hm.include hn)
    · have hpos := omit_count_pos hm hn (hcov n hc.1.1)
      omega
  | split c d ihc ihd =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hn : n ∈ A
    · exact ihd (n + 1) (mask ||| 2 ^ n) hc.2 (hm.include hn)
    · exact ihc (n + 1) mask hc.1.2 (hm.omit hn)

/-- A successfully checked root rules out the given *global* cap. The sum at
which it fails need not lie inside the coverage interval. -/
theorem obstruction_of_check (K N : ℕ) (c : Certificate)
    (hc : check K N 1 1 c = true) (A : Set ℕ)
    (hcov : ∀ s ≤ N, s ∈ A + A) : ∃ s, K < sumRep A s := by
  by_contra! hcap
  exact check_sound c K N 1 1 hc A (matches_root (hcov 0 (Nat.zero_le N))) hcov hcap

/-- A small certificate block may graft in an already verified subtree.
The proof carried by `graft` is essential: an unchecked external reference is
never accepted. This permits bounded-memory kernel verification of large trees. -/
inductive Fragment (K N : ℕ) where
  | graft (next mask : ℕ) (tree : Certificate) (checked : check K N next mask tree = true)
  | closed (witness : ℕ)
  | onlyOmit (witness : ℕ) (child : Fragment K N)
  | onlyInclude (child : Fragment K N)
  | split (omitChild includeChild : Fragment K N)

/-- Replace each verified graft by its actual subtree. -/
def Fragment.toCertificate {K N : ℕ} : Fragment K N → Certificate
  | .graft _ _ c _ => c
  | .closed s => .closed s
  | .onlyOmit s c => .onlyOmit s c.toCertificate
  | .onlyInclude c => .onlyInclude c.toCertificate
  | .split c d => .split c.toCertificate d.toCertificate

/-- Check one finite block, testing the exact chronological state at each graft.
The previously proved subtree counts need not be recomputed. -/
def checkFragment (K N n mask : ℕ) : Fragment K N → Bool
  | .graft next bits _ _ => decide (n = next ∧ mask = bits)
  | .closed s => decide (n ≤ N) && decide (repCount mask n = 0) &&
      decide (K < repCount (mask ||| 2 ^ n) s)
  | .onlyOmit s c => decide (n ≤ N) && checkFragment K N (n + 1) mask c &&
      decide (K < repCount (mask ||| 2 ^ n) s)
  | .onlyInclude c => decide (n ≤ N) && decide (repCount mask n = 0) &&
      checkFragment K N (n + 1) (mask ||| 2 ^ n) c
  | .split c d => decide (n ≤ N) && checkFragment K N (n + 1) mask c &&
      checkFragment K N (n + 1) (mask ||| 2 ^ n) d

/-- Verified reflection for blocks: all grafts carry genuine checker proofs,
and their cached states are checked rather than trusted. -/
theorem checkFragment_sound {K N : ℕ} (f : Fragment K N) (n mask : ℕ)
    (hf : checkFragment K N n mask f = true) :
    check K N n mask f.toCertificate = true := by
  induction f generalizing n mask with
  | graft next bits c hc =>
    simp only [checkFragment, decide_eq_true_eq] at hf
    rcases hf with ⟨rfl, rfl⟩
    exact hc
  | closed s => exact hf
  | onlyOmit s c ih =>
    change (decide (n ≤ N) && checkFragment K N (n + 1) mask c &&
      decide (K < repCount (mask ||| 2 ^ n) s)) = true at hf
    change (decide (n ≤ N) && check K N (n + 1) mask c.toCertificate &&
      decide (K < repCount (mask ||| 2 ^ n) s)) = true
    simp only [Bool.and_eq_true] at hf ⊢
    exact ⟨⟨hf.1.1, ih (n + 1) mask hf.1.2⟩, hf.2⟩
  | onlyInclude c ih =>
    change (decide (n ≤ N) && decide (repCount mask n = 0) &&
      checkFragment K N (n + 1) (mask ||| 2 ^ n) c) = true at hf
    change (decide (n ≤ N) && decide (repCount mask n = 0) &&
      check K N (n + 1) (mask ||| 2 ^ n) c.toCertificate) = true
    simp only [Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, ih (n + 1) (mask ||| 2 ^ n) hf.2⟩
  | split c d ihc ihd =>
    change (decide (n ≤ N) && checkFragment K N (n + 1) mask c &&
      checkFragment K N (n + 1) (mask ||| 2 ^ n) d) = true at hf
    change (decide (n ≤ N) && check K N (n + 1) mask c.toCertificate &&
      check K N (n + 1) (mask ||| 2 ^ n) d.toCertificate) = true
    simp only [Bool.and_eq_true] at hf ⊢
    exact ⟨⟨hf.1.1, ihc (n + 1) mask hf.1.2⟩, ihd (n + 1) (mask ||| 2 ^ n) hf.2⟩

/- BEGIN GENERATED FINITE CERTIFICATES -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


private def cap2Root : Fragment 2 5 :=
  (.onlyInclude (.onlyOmit 2 (.onlyInclude (.onlyOmit 4 (.closed 6)))))

/-- Reified from `cap_2_certificate.json`: 5 nodes.
SHA-256: `f30887537ad7a44a42d4c1495ec81763747884ee59cfcc5a12b72de218e108a9`. -/
def cap2Certificate : Certificate := cap2Root.toCertificate

/-- Kernel computation of the complete cap-2 tree, in proof-carrying blocks. -/
theorem cap2_checked : check 2 5 1 1 cap2Certificate = true :=
  checkFragment_sound cap2Root 1 1 (by decide +kernel)

/-- **Partial finite result, not Erdős–Turán:** coverage of `0..5`
forces some global ordered representation count to exceed 2. -/
theorem cap2_obstruction (A : Set ℕ) (hcov : ∀ n ≤ 5, n ∈ A + A) :
    ∃ n, 2 < sumRep A n :=
  obstruction_of_check 2 5 cap2Certificate cap2_checked A hcov

#print axioms cap2_checked
#print axioms cap2_obstruction


private def cap3Root : Fragment 3 11 :=
  (.onlyInclude (.split (.onlyInclude (.onlyOmit 4 (.onlyInclude (.onlyOmit 6 (.closed 8)))))
    (.onlyOmit 3 (.split (.onlyInclude (.onlyOmit 6 (.onlyOmit 7 (.onlyInclude (.onlyOmit 9 (.onlyOmit 10 (.closed 13)))))))
    (.onlyOmit 5 (.onlyOmit 6 (.onlyInclude (.onlyOmit 8 (.onlyOmit 9 (.closed 11))))))))))

/-- Reified from `cap_3_certificate.json`: 22 nodes.
SHA-256: `ad25363d44b009118aab000d57b1f808daf1b540a1856d92969b11c9cc64a184`. -/
def cap3Certificate : Certificate := cap3Root.toCertificate

/-- Kernel computation of the complete cap-3 tree, in proof-carrying blocks. -/
theorem cap3_checked : check 3 11 1 1 cap3Certificate = true :=
  checkFragment_sound cap3Root 1 1 (by decide +kernel)

/-- **Partial finite result, not Erdős–Turán:** coverage of `0..11`
forces some global ordered representation count to exceed 3. -/
theorem cap3_obstruction (A : Set ℕ) (hcov : ∀ n ≤ 11, n ∈ A + A) :
    ∃ n, 3 < sumRep A n :=
  obstruction_of_check 3 11 cap3Certificate cap3_checked A hcov

#print axioms cap3_checked
#print axioms cap3_obstruction

private def cap4Part0Block : Fragment 4 46 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 12 (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 32)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 27))))))))
    (.split (.closed 18)
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))))))
    (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 25))))))))
    (.onlyOmit 14 (.split (.split (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 17 (.onlyOmit 22 (.onlyOmit 20 (.onlyOmit 20 (.closed 22))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 24 (.closed 22)))))))))))
    (.split (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 19 (.closed 18)))
    (.onlyOmit 18 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 30))))))))))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 14 (.split (.closed 20)
    (.onlyOmit 19 (.closed 18)))))))))
    (.split (.onlyInclude (.onlyOmit 11 (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 18 (.split (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 24))))))))
    (.onlyOmit 14 (.closed 16)))
    (.onlyOmit 13 (.split (.onlyOmit 16 (.onlyOmit 16 (.closed 20)))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))))))))
    (.split (.onlyOmit 12 (.onlyOmit 12 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 23 (.closed 22))))))))
    (.onlyOmit 17 (.closed 16)))))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 18 (.closed 18))))))))

private def cap4Part0 : Certificate := cap4Part0Block.toCertificate

private theorem cap4Part0_checked : check 4 46 8 27 cap4Part0 = true :=
  checkFragment_sound cap4Part0Block 8 27 (by decide +kernel)

private def cap4Part1Block : Fragment 4 46 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.closed 25))))))))))
    (.split (.onlyOmit 20 (.onlyOmit 20 (.split (.closed 20)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 28 (.closed 24))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 36))))))))))))))
    (.onlyOmit 25 (.closed 24))))))))))
    (.onlyOmit 14 (.closed 16)))
    (.onlyOmit 13 (.split (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.closed 20)))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.closed 29))))))))
    (.onlyOmit 21 (.closed 20)))
    (.onlyOmit 17 (.closed 22)))
    (.onlyOmit 16 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))
    (.onlyOmit 38 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.closed 37))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 26 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 29))))))))))))))))))

private def cap4Part1 : Certificate := cap4Part1Block.toCertificate

private theorem cap4Part1_checked : check 4 46 11 1115 cap4Part1 = true :=
  checkFragment_sound cap4Part1Block 11 1115 (by decide +kernel)

private def cap4Part2Block : Fragment 4 46 :=
  (.split (.split (.graft 8 27 cap4Part0 cap4Part0_checked)
    (.onlyOmit 8 (.onlyInclude (.onlyOmit 10 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 18 (.split (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 23 (.onlyOmit 23 (.closed 28))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 30)))))))))))))
    (.onlyOmit 14 (.closed 16)))
    (.onlyOmit 13 (.split (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 34))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.closed 21)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.closed 26))))))))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 18 (.split (.closed 18)
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 32 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))))))))))))))))))
    (.onlyOmit 7 (.split (.split (.split (.onlyInclude (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.split (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.closed 24)))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.closed 26))))))))))
    (.graft 11 1115 cap4Part1 cap4Part1_checked))
    (.onlyOmit 10 (.closed 12)))
    (.onlyOmit 9 (.split (.onlyOmit 12 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.closed 16)))))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.closed 16))))))))))

private def cap4Part2 : Certificate := cap4Part2Block.toCertificate

private theorem cap4Part2_checked : check 4 46 6 27 cap4Part2 = true :=
  checkFragment_sound cap4Part2Block 6 27 (by decide +kernel)

private def cap4Part3Block : Fragment 4 46 :=
  (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 24 (.closed 22)))
    (.onlyOmit 22 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 26 (.closed 31))))))))))
    (.onlyOmit 18 (.closed 22)))))))
    (.onlyOmit 16 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 22 (.closed 23)))
    (.onlyOmit 22 (.closed 22)))))))))
    (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 28)))
    (.onlyOmit 28 (.closed 36)))
    (.onlyOmit 24 (.closed 28)))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.closed 30)))))))))
    (.onlyOmit 22 (.closed 20)))
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))))))))))
    (.onlyOmit 15 (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 21 (.closed 20)))
    (.onlyOmit 20 (.closed 21)))))))))
    (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 34 (.closed 32)))))))))
    (.onlyOmit 27 (.closed 25)))
    (.onlyOmit 22 (.closed 32)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 27 (.closed 27)))))))))
    (.onlyOmit 16 (.closed 18)))))))))

private def cap4Part3 : Certificate := cap4Part3Block.toCertificate

private theorem cap4Part3_checked : check 4 46 9 59 cap4Part3 = true :=
  checkFragment_sound cap4Part3Block 9 59 (by decide +kernel)

private def cap4Part4Block : Fragment 4 46 :=
  (.split (.onlyInclude (.onlyOmit 10 (.onlyOmit 11 (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.closed 18))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.closed 18)
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.closed 21)))))))))))
    (.onlyOmit 10 (.onlyOmit 10 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23)))))
    (.onlyOmit 23 (.split (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 34))))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 22 (.closed 22))))))))
    (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 16 (.split (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.closed 23)))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 30))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 20 (.closed 20))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 16 (.closed 16))))))))

private def cap4Part4 : Certificate := cap4Part4Block.toCertificate

private theorem cap4Part4_checked : check 4 46 8 103 cap4Part4 = true :=
  checkFragment_sound cap4Part4Block 8 103 (by decide +kernel)

private def cap4Part5Block : Fragment 4 46 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.closed 22)))))))
    (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 38 (.closed 30)))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 32)))))))))
    (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))))))))
    (.onlyOmit 18 (.split (.closed 22)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 30)))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.closed 29))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 22 (.closed 22))))
    (.onlyOmit 22 (.split (.closed 22)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 36 (.closed 36))))))))))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.closed 20)))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.closed 22))))
    (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 29)))))))))
    (.onlyOmit 17 (.onlyOmit 20 (.closed 20))))
    (.onlyOmit 16 (.onlyOmit 17 (.closed 20)))))))
    (.onlyOmit 12 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.closed 27))))))))))
    (.onlyOmit 21 (.onlyOmit 20 (.closed 20))))))))))

private def cap4Part5 : Certificate := cap4Part5Block.toCertificate

private theorem cap4Part5_checked : check 4 46 10 55 cap4Part5 = true :=
  checkFragment_sound cap4Part5Block 10 55 (by decide +kernel)

private def cap4Part6Block : Fragment 4 46 :=
  (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.closed 24)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 42 (.closed 36))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 30 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))))))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 34))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 36)))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))
    (.onlyOmit 16 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 42))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 32 (.onlyOmit 30 (.closed 30))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 34)))))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.closed 18)))))))

private def cap4Part6 : Certificate := cap4Part6Block.toCertificate

private theorem cap4Part6_checked : check 4 46 11 567 cap4Part6 = true :=
  checkFragment_sound cap4Part6Block 11 567 (by decide +kernel)

private def cap4Part7Block : Fragment 4 46 :=
  (.onlyOmit 12 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.closed 22)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 36))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.closed 30))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 43 (.onlyOmit 48 (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 48 (.onlyOmit 56 (.closed 48)))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 48 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.closed 48))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 35))))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 30 (.onlyOmit 26 (.closed 26)))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.closed 18))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 26 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 26))))))))))))))

private def cap4Part7 : Certificate := cap4Part7Block.toCertificate

private theorem cap4Part7_checked : check 4 46 12 2231 cap4Part7 = true :=
  checkFragment_sound cap4Part7Block 12 2231 (by decide +kernel)

private def cap4Part8Block : Fragment 4 46 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 10 (.onlyOmit 10 (.onlyInclude (.onlyOmit 13 (.onlyOmit 13 (.closed 16)))))))
    (.split (.split (.split (.onlyInclude (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 30)))))
    (.onlyOmit 20 (.onlyOmit 20 (.closed 22)))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.closed 22)))))))
    (.onlyOmit 14 (.split (.onlyOmit 18 (.closed 18))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 20)))))))))
    (.onlyOmit 12 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.closed 20))))))))))
    (.onlyOmit 10 (.split (.onlyOmit 14 (.closed 14))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.closed 16)))))))
    (.onlyOmit 9 (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.closed 22))))))))))))))
    (.onlyOmit 7 (.graft 8 103 cap4Part4 cap4Part4_checked))))
    (.split (.split (.onlyInclude (.onlyOmit 8 (.split (.onlyInclude (.onlyOmit 11 (.onlyOmit 14 (.closed 14))))
    (.onlyOmit 11 (.onlyOmit 11 (.onlyInclude (.onlyOmit 13 (.onlyOmit 14 (.closed 16)))))))))
    (.onlyOmit 8 (.onlyOmit 8 (.onlyInclude (.onlyOmit 10 (.split (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 18 (.closed 18))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))))))))))
    (.onlyOmit 13 (.onlyOmit 18 (.split (.onlyOmit 18 (.closed 18))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 21 (.closed 21)))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.closed 15)))))))))
    (.onlyOmit 6 (.split (.split (.split (.graft 10 55 cap4Part5 cap4Part5_checked)
    (.onlyOmit 10 (.graft 11 567 cap4Part6 cap4Part6_checked)))
    (.onlyOmit 9 (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.onlyOmit 13 (.closed 16)))))))
    (.onlyOmit 8 (.onlyOmit 9 (.split (.split (.split (.onlyInclude (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.closed 20))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 28 (.closed 26))))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.closed 19)))))))
    (.graft 12 2231 cap4Part7 cap4Part7_checked))
    (.onlyOmit 11 (.onlyOmit 12 (.closed 14))))))))))

private def cap4Part8 : Certificate := cap4Part8Block.toCertificate

private theorem cap4Part8_checked : check 4 46 4 7 cap4Part8 = true :=
  checkFragment_sound cap4Part8Block 4 7 (by decide +kernel)

private def cap4Part9Block : Fragment 4 46 :=
  (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.closed 22)))))))))
    (.split (.split (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))))))))))
    (.onlyOmit 14 (.split (.split (.onlyOmit 20 (.closed 20))
    (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.closed 23))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 20 (.closed 20)))))))
    (.onlyOmit 13 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 28)))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.closed 32)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 40 (.closed 32))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyOmit 22 (.onlyOmit 22 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 25))))))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.closed 22))))))))))

private def cap4Part9 : Certificate := cap4Part9Block.toCertificate

private theorem cap4Part9_checked : check 4 46 10 143 cap4Part9 = true :=
  checkFragment_sound cap4Part9Block 10 143 (by decide +kernel)

private def cap4Part10Block : Fragment 4 46 :=
  (.split (.split (.graft 10 143 cap4Part9 cap4Part9_checked)
    (.onlyOmit 10 (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 32))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyOmit 32 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 40 (.onlyOmit 32 (.closed 32)))))))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 24))))))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.closed 18)))))))
    (.onlyOmit 9 (.onlyOmit 10 (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.closed 24)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 28))))))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyOmit 28 (.closed 28))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.closed 27))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 22 (.closed 22)))))))))))))

private def cap4Part10 : Certificate := cap4Part10Block.toCertificate

private theorem cap4Part10_checked : check 4 46 8 143 cap4Part10 = true :=
  checkFragment_sound cap4Part10Block 8 143 (by decide +kernel)

private def cap4Part11Block : Fragment 4 46 :=
  (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.closed 30)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 34))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.onlyOmit 42 (.onlyOmit 38 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 30))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 26))))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.closed 29)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 33))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.closed 24)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 28))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 31))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))))))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.closed 30)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 30)))))))))))))))))

private def cap4Part11 : Certificate := cap4Part11Block.toCertificate

private theorem cap4Part11_checked : check 4 46 11 335 cap4Part11 = true :=
  checkFragment_sound cap4Part11Block 11 335 (by decide +kernel)

private def cap4Part12Block : Fragment 4 46 :=
  (.split (.onlyInclude (.onlyOmit 10 (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 18 (.onlyOmit 18 (.closed 18)))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.closed 24))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 20)))))))))))
    (.onlyOmit 10 (.onlyOmit 10 (.split (.onlyInclude (.onlyOmit 13 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 26))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 33 (.closed 33)))))))))))))))
    (.onlyOmit 17 (.split (.onlyOmit 24 (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.closed 28))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.closed 24)))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 20 (.closed 20)))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.onlyOmit 16 (.closed 16))))))))

private def cap4Part12 : Certificate := cap4Part12Block.toCertificate

private theorem cap4Part12_checked : check 4 46 8 47 cap4Part12 = true :=
  checkFragment_sound cap4Part12Block 8 47 (by decide +kernel)

private def cap4Part13Block : Fragment 4 46 :=
  (.split (.split (.onlyInclude (.graft 8 143 cap4Part10 cap4Part10_checked))
    (.split (.split (.split (.onlyInclude (.onlyOmit 12 (.onlyOmit 12 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 20 (.closed 20)))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.closed 23))))))))))))
    (.onlyOmit 12 (.onlyOmit 12 (.onlyOmit 12 (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 26 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.closed 22))))))))))))
    (.onlyOmit 9 (.split (.graft 11 335 cap4Part11 cap4Part11_checked)
    (.onlyOmit 11 (.onlyOmit 12 (.onlyOmit 16 (.onlyOmit 16 (.closed 16))))))))
    (.onlyOmit 8 (.onlyOmit 9 (.split (.onlyInclude (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.closed 22)))))))))
    (.onlyOmit 12 (.onlyOmit 12 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.closed 25)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.closed 20)))))))))))))
    (.onlyOmit 6 (.split (.graft 8 47 cap4Part12 cap4Part12_checked)
    (.onlyOmit 8 (.onlyOmit 10 (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 22)))))))))))))))

private def cap4Part13 : Certificate := cap4Part13Block.toCertificate

private theorem cap4Part13_checked : check 4 46 5 15 cap4Part13 = true :=
  checkFragment_sound cap4Part13Block 5 15 (by decide +kernel)

private def cap4Root : Fragment 4 46 :=
  (.onlyInclude (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 6 (.onlyInclude (.onlyOmit 8 (.closed 10)))))
    (.split (.graft 6 27 cap4Part2 cap4Part2_checked)
    (.onlyOmit 6 (.onlyOmit 8 (.onlyOmit 8 (.graft 9 59 cap4Part3 cap4Part3_checked)))))))
    (.split (.graft 4 7 cap4Part8 cap4Part8_checked)
    (.onlyOmit 4 (.graft 5 15 cap4Part13 cap4Part13_checked)))))

/-- Reified from `cap_4_certificate.json`: 1,765 nodes.
SHA-256: `3cb1ae95f5bb6d889e5e41602b12a53dba506fe79572532741916328936c60bd`. -/
def cap4Certificate : Certificate := cap4Root.toCertificate

/-- Kernel computation of the complete cap-4 tree, in proof-carrying blocks. -/
theorem cap4_checked : check 4 46 1 1 cap4Certificate = true :=
  checkFragment_sound cap4Root 1 1 (by decide +kernel)

/-- **Partial finite result, not Erdős–Turán:** coverage of `0..46`
forces some global ordered representation count to exceed 4. -/
theorem cap4_obstruction (A : Set ℕ) (hcov : ∀ n ≤ 46, n ∈ A + A) :
    ∃ n, 4 < sumRep A n :=
  obstruction_of_check 4 46 cap4Certificate cap4_checked A hcov

#print axioms cap4_checked
#print axioms cap4_obstruction

private def cap5Part0Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 16 (.closed 18)))
    (.split (.onlyOmit 19 (.split (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 27 (.onlyInclude (.onlyOmit 24 (.closed 26)))))
    (.split (.onlyInclude (.onlyOmit 23 (.closed 25)))
    (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.closed 34))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 27 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 30))))))
    (.onlyOmit 24 (.closed 26))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 28 (.closed 27)))
    (.onlyOmit 27 (.onlyInclude (.onlyOmit 24 (.closed 26)))))))))))))
    (.split (.onlyInclude (.onlyOmit 15 (.closed 17)))
    (.split (.onlyOmit 18 (.split (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 22 (.closed 24)))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 33 (.closed 32)))))
    (.onlyOmit 32 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 46)))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 28)))))))))))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 27 (.closed 26)))
    (.onlyOmit 26 (.closed 25)))))))))))

private def cap5Part0 : Certificate := cap5Part0Block.toCertificate

private theorem cap5Part0_checked : check 5 60 12 107 cap5Part0 = true :=
  checkFragment_sound cap5Part0Block 12 107 (by decide +kernel)

private def cap5Part1Block : Fragment 5 60 :=
  (.split (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 33 (.closed 30)))
    (.onlyOmit 27 (.closed 31)))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 31 (.closed 30)))))))))
    (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 31 (.onlyInclude (.onlyOmit 31 (.closed 30))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 32 (.closed 31))))))))))
    (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.onlyInclude (.onlyOmit 30 (.closed 29)))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.split (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 47 (.closed 47)))))))))
    (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 39 (.closed 38)))))))))))
    (.onlyOmit 27 (.closed 31)))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 31 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 43)))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.closed 51))))))))))
    (.onlyOmit 31 (.closed 35)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.closed 42))))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40)))))))))))))))))))))

private def cap5Part1 : Certificate := cap5Part1Block.toCertificate

private theorem cap5Part1_checked : check 5 60 15 6251 cap5Part1 = true :=
  checkFragment_sound cap5Part1Block 15 6251 (by decide +kernel)

private def cap5Part2Block : Fragment 5 60 :=
  (.split (.split (.graft 12 107 cap5Part0 cap5Part0_checked)
    (.split (.onlyInclude (.onlyOmit 14 (.closed 16)))
    (.split (.onlyOmit 17 (.graft 15 6251 cap5Part1 cap5Part1_checked))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 33 (.closed 32)))
    (.onlyOmit 32 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 32 (.closed 33)))))))))
    (.onlyOmit 25 (.closed 24)))))))))))
    (.onlyOmit 11 (.split (.split (.onlyInclude (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 19 (.split (.onlyOmit 24 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.closed 32))))))
    (.onlyOmit 21 (.closed 23)))))
    (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 31)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.closed 35)))))))))))))
    (.onlyOmit 17 (.closed 19)))))
    (.split (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 23 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 30))))))))))
    (.onlyOmit 20 (.closed 22)))))))
    (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 35)))))))))
    (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.closed 34))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.closed 27)))))))))
    (.onlyOmit 13 (.closed 15)))))

private def cap5Part2 : Certificate := cap5Part2Block.toCertificate

private theorem cap5Part2_checked : check 5 60 10 107 cap5Part2 = true :=
  checkFragment_sound cap5Part2Block 10 107 (by decide +kernel)

private def cap5Part3Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 22 (.split (.closed 22)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 29))))))))))))
    (.onlyOmit 22 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 29 (.closed 25)))))))))
    (.onlyOmit 16 (.closed 18)))))
    (.split (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 21 (.split (.closed 21)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 28))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 33 (.closed 32)))))
    (.onlyOmit 32 (.closed 29)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 32))))))))
    (.onlyOmit 25 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 32 (.closed 28)))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.closed 21)))))))))
    (.onlyOmit 12 (.closed 14)))
    (.onlyOmit 11 (.onlyOmit 15 (.split (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 26 (.onlyOmit 27 (.closed 26)))))
    (.onlyOmit 26 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 29)))))))))
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 35)))))))))))))
    (.split (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 33 (.closed 32)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 33 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 33 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 40)))))))))))))
    (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 39)))))))))))))
    (.onlyOmit 22 (.closed 26)))
    (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 26 (.closed 25)))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 26 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 33)))))))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 23 (.closed 22))))))))))))

private def cap5Part3 : Certificate := cap5Part3Block.toCertificate

private theorem cap5Part3_checked : check 5 60 10 619 cap5Part3 = true :=
  checkFragment_sound cap5Part3Block 10 619 (by decide +kernel)

private def cap5Part4Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 32)))
    (.split (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 52 (.closed 46)))))))))))))
    (.onlyOmit 33 (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 46 (.closed 40))))))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.split (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.closed 66)))))))))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyInclude (.onlyOmit 57 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 57 (.closed 56))))))))))))))))))
    (.onlyOmit 43 (.closed 40))))))))))))
    (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 27 (.split (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 42 (.closed 36))))))))))))

private def cap5Part4 : Certificate := cap5Part4Block.toCertificate

private theorem cap5Part4_checked : check 5 60 24 4473195 cap5Part4 = true :=
  checkFragment_sound cap5Part4Block 24 4473195 (by decide +kernel)

private def cap5Part5Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 30)))))
    (.split (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.onlyInclude (.onlyOmit 35 (.onlyOmit 42 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 48 (.closed 42)))))))))))))
    (.onlyOmit 29 (.split (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 42 (.onlyInclude (.onlyOmit 36 (.closed 38))))
    (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 42 (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))))
    (.onlyOmit 26 (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.split (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.split (.closed 42)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 58)))))))))
    (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 49)))))))))))
    (.onlyOmit 39 (.closed 38)))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 42 (.onlyInclude (.onlyOmit 36 (.closed 38))))))))))))))
    (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 23 (.graft 24 4473195 cap5Part4 cap5Part4_checked)))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 32)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 38 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 38 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))))))))))

private def cap5Part5 : Certificate := cap5Part5Block.toCertificate

private theorem cap5Part5_checked : check 5 60 20 278891 cap5Part5 = true :=
  checkFragment_sound cap5Part5Block 20 278891 (by decide +kernel)

private def cap5Part6Block : Fragment 5 60 :=
  (.split (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.split (.onlyInclude (.split (.closed 29)
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 33 (.closed 39)))))))))))
    (.onlyOmit 29 (.onlyInclude (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.closed 27)))))
    (.onlyOmit 22 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 33 (.closed 35)))
    (.onlyOmit 46 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 46)))))))))))
    (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyOmit 33 (.onlyOmit 33 (.closed 35)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 52 (.closed 39))))))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.closed 33)))
    (.split (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 48 (.closed 42))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 39)))))))))))))))))

private def cap5Part6 : Certificate := cap5Part6Block.toCertificate

private theorem cap5Part6_checked : check 5 60 18 49515 cap5Part6 = true :=
  checkFragment_sound cap5Part6Block 18 49515 (by decide +kernel)

private def cap5Part7Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.graft 20 278891 cap5Part5 cap5Part5_checked)))
    (.split (.onlyOmit 20 (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 45)
    (.onlyOmit 42 (.closed 41))))))))))))
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 32 (.closed 31)))))
    (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.split (.onlyOmit 38 (.onlyOmit 41 (.closed 38)))
    (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.closed 51)))))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.closed 41))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 42 (.split (.onlyOmit 42 (.closed 42))
    (.onlyOmit 36 (.closed 38))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))))))))))))))
    (.onlyOmit 17 (.closed 19)))
    (.split (.onlyOmit 20 (.graft 18 49515 cap5Part6 cap5Part6_checked))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 31 (.closed 30)))
    (.onlyOmit 30 (.closed 29)))
    (.onlyOmit 24 (.closed 31)))))))))))

private def cap5Part7 : Certificate := cap5Part7Block.toCertificate

private theorem cap5Part7_checked : check 5 60 15 16747 cap5Part7 = true :=
  checkFragment_sound cap5Part7Block 15 16747 (by decide +kernel)

private def cap5Part8Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.split (.onlyOmit 21 (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyInclude (.onlyOmit 28 (.closed 30)))))
    (.split (.onlyInclude (.onlyOmit 27 (.closed 29)))
    (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.closed 40))))))))))))
    (.onlyOmit 24 (.closed 31)))
    (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.closed 38)))
    (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 38 (.closed 37)))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 34))))))))
    (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.closed 27)))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.closed 31)))
    (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 44)))))))))
    (.onlyOmit 28 (.closed 30))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 32 (.closed 31)))
    (.onlyOmit 31 (.closed 33)))
    (.onlyOmit 25 (.closed 32))))))))))))
    (.graft 15 16747 cap5Part7 cap5Part7_checked))
    (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.closed 18)))))

private def cap5Part8 : Certificate := cap5Part8Block.toCertificate

private theorem cap5Part8_checked : check 5 60 13 363 cap5Part8 = true :=
  checkFragment_sound cap5Part8Block 13 363 (by decide +kernel)

private def cap5Part9Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 40))))))
    (.onlyOmit 27 (.onlyOmit 34 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 44 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))))))))))))))
    (.split (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 43)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 53)))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 33))))))))))))
    (.onlyOmit 21 (.closed 23)))
    (.onlyOmit 20 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 44 (.closed 50)))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 37 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 47 (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 47)
    (.onlyOmit 47 (.onlyOmit 41 (.onlyOmit 41 (.closed 47)))))))))))))))
    (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 46 (.split (.split (.split (.onlyOmit 46 (.split (.onlyOmit 46 (.closed 46))
    (.onlyOmit 40 (.closed 46))))
    (.onlyOmit 46 (.onlyOmit 40 (.onlyOmit 40 (.closed 46)))))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.closed 54))))))))))))))
    (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 46 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 46 (.closed 47))))))))))))))))
    (.onlyOmit 27 (.closed 31)))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 31 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 40))))))))))))))

private def cap5Part9 : Certificate := cap5Part9Block.toCertificate

private theorem cap5Part9_checked : check 5 60 19 266603 cap5Part9 = true :=
  checkFragment_sound cap5Part9Block 19 266603 (by decide +kernel)

private def cap5Part10Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))
    (.graft 19 266603 cap5Part9 cap5Part9_checked))
    (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 17 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.closed 28)))
    (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 38 (.closed 34)))))))))
    (.onlyOmit 25 (.closed 27)))))
    (.onlyOmit 22 (.closed 24)))
    (.onlyOmit 21 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 28 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 42 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))))))
    (.onlyOmit 25 (.onlyOmit 32 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 36 (.closed 32))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 28 (.onlyOmit 28 (.closed 30))))))))))))))
    (.split (.onlyOmit 18 (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 37 (.onlyOmit 41 (.closed 37))))))))))))
    (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.closed 36))))))))))))
    (.onlyOmit 24 (.closed 28)))
    (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 28 (.closed 27))))))))))))

private def cap5Part10 : Certificate := cap5Part10Block.toCertificate

private theorem cap5Part10_checked : check 5 60 15 4459 cap5Part10 = true :=
  checkFragment_sound cap5Part10Block 15 4459 (by decide +kernel)

private def cap5Part11Block : Fragment 5 60 :=
  (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 36 (.closed 32)))
    (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 44 (.split (.onlyOmit 44 (.onlyOmit 58 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 50 (.onlyOmit 58 (.closed 50)))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 68 (.closed 50))))))))))))
    (.onlyOmit 44 (.closed 40))))))))))
    (.onlyOmit 35 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 44 (.closed 40))))))))))))
    (.onlyOmit 28 (.closed 32)))
    (.onlyOmit 27 (.split (.onlyOmit 32 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 46))))))
    (.onlyOmit 29 (.closed 31)))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 32)))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 44 (.onlyInclude (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 58 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 54 (.onlyOmit 66 (.closed 54)))))))))))))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 44 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))))))))))))

private def cap5Part11 : Certificate := cap5Part11Block.toCertificate

private theorem cap5Part11_checked : check 5 60 21 1118443 cap5Part11 = true :=
  checkFragment_sound cap5Part11Block 21 1118443 (by decide +kernel)

private def cap5Part12Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 48)))))))))
    (.onlyOmit 38 (.closed 35)))
    (.onlyOmit 32 (.closed 38)))))))))
    (.onlyOmit 30 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 38 (.closed 35)))
    (.onlyOmit 38 (.closed 36)))))))))))
    (.split (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 34 (.closed 40))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 37 (.closed 34)))
    (.onlyOmit 37 (.closed 35)))))))))))
    (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 27 (.split (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 43 (.closed 43)))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 48 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 40 (.closed 46))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 40 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.closed 43)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 32 (.closed 38))))))))))))))

private def cap5Part12 : Certificate := cap5Part12Block.toCertificate

private theorem cap5Part12_checked : check 5 60 20 37099 cap5Part12 = true :=
  checkFragment_sound cap5Part12Block 20 37099 (by decide +kernel)

private def cap5Part13Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.graft 21 1118443 cap5Part11 cap5Part11_checked))))))
    (.split (.onlyOmit 18 (.onlyOmit 18 (.split (.graft 20 37099 cap5Part12 cap5Part12_checked)
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 55)))))))))
    (.onlyOmit 38 (.closed 34)))
    (.onlyOmit 31 (.closed 35)))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 35 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 35)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 42 (.closed 42))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 39))))))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 45))))))))))))))))))
    (.onlyOmit 31 (.closed 27)))
    (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 39 (.closed 39)))))))))))))))))))
    (.onlyOmit 15 (.closed 17)))

private def cap5Part13 : Certificate := cap5Part13Block.toCertificate

private theorem cap5Part13_checked : check 5 60 14 4331 cap5Part13 = true :=
  checkFragment_sound cap5Part13Block 14 4331 (by decide +kernel)

private def cap5Part14Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 49 (.closed 40))))))
    (.onlyOmit 34 (.closed 40))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 40))))))))))))))
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))
    (.onlyOmit 37 (.closed 34)))))))))))
    (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 36 (.closed 33)))))))))))
    (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 32 (.closed 34)))
    (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 44 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 44)))))))))
    (.onlyOmit 30 (.closed 32)))))))))
    (.onlyOmit 28 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 33 (.closed 35)))))
    (.onlyOmit 35 (.closed 32)))))))))))

private def cap5Part14 : Certificate := cap5Part14Block.toCertificate

private theorem cap5Part14_checked : check 5 60 21 18667 cap5Part14 = true :=
  checkFragment_sound cap5Part14Block 21 18667 (by decide +kernel)

private def cap5Part15Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 31 (.closed 31)))
    (.split (.onlyInclude (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 39 (.closed 39)))))))))))))))))))
    (.split (.onlyInclude (.onlyOmit 17 (.closed 19)))
    (.onlyOmit 21 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 29 (.onlyInclude (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 29 (.closed 29)))))))))))
    (.split (.onlyInclude (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 20 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 36 (.closed 36))))))))))
    (.onlyOmit 27 (.onlyInclude (.onlyOmit 24 (.closed 26)))))))))))))
    (.onlyOmit 13 (.graft 14 4331 cap5Part13 cap5Part13_checked)))
    (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26)))))))))
    (.split (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.split (.graft 21 18667 cap5Part14 cap5Part14_checked)
    (.onlyOmit 21 (.onlyOmit 25 (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 46 (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 43 (.onlyOmit 43 (.closed 55))))))))))))))
    (.onlyOmit 31 (.closed 37)))))))))))))
    (.onlyOmit 20 (.split (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 30))))))
    (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 32 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 37)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 29 (.closed 25)))))))))))
    (.onlyOmit 14 (.closed 16)))))

private def cap5Part15 : Certificate := cap5Part15Block.toCertificate

private theorem cap5Part15_checked : check 5 60 11 235 cap5Part15 = true :=
  checkFragment_sound cap5Part15Block 11 235 (by decide +kernel)

private def cap5Part16Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 40)))))))))))))
    (.onlyOmit 28 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.split (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 32 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 47)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 36 (.onlyOmit 36 (.closed 47)))))))))))))))))
    (.onlyOmit 21 (.closed 23)))
    (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 30 (.closed 32)))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 37)))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 45))))))))))))))))))
    (.split (.onlyInclude (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 43 (.onlyOmit 44 (.closed 43)))))
    (.onlyOmit 43 (.closed 40))))))))))
    (.onlyOmit 35 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 43 (.closed 44)))))))))))))
    (.onlyOmit 29 (.closed 31)))))
    (.split (.onlyOmit 28 (.onlyOmit 28 (.closed 35)))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 43 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 43 (.closed 43)))))))))))))))))))))

private def cap5Part16 : Certificate := cap5Part16Block.toCertificate

private theorem cap5Part16_checked : check 5 60 17 1259 cap5Part16 = true :=
  checkFragment_sound cap5Part16Block 17 1259 (by decide +kernel)

private def cap5Part17Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.closed 34)))
    (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 56 (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 56 (.closed 48))))))))))
    (.onlyOmit 44 (.closed 40)))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 44)))))))))
    (.onlyOmit 36 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 44 (.onlyOmit 42 (.onlyOmit 47 (.closed 42)))))))))))))
    (.onlyOmit 29 (.closed 31)))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 42 (.onlyOmit 45 (.closed 42))))))))))))))
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.split (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 50 (.closed 50))))))
    (.onlyOmit 39 (.onlyOmit 56 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 48 (.split (.onlyOmit 48 (.closed 56))
    (.onlyOmit 45 (.closed 56))))))))))))))))
    (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.split (.onlyOmit 40 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 54 (.onlyOmit 48 (.split (.closed 48)
    (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 54 (.closed 56))))))))))))))
    (.onlyOmit 37 (.closed 54))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 48 (.onlyOmit 40 (.onlyOmit 40 (.closed 42)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 42 (.onlyOmit 34 (.onlyOmit 34 (.closed 42))))))))))))

private def cap5Part17 : Certificate := cap5Part17Block.toCertificate

private theorem cap5Part17_checked : check 5 60 24 328939 cap5Part17 = true :=
  checkFragment_sound cap5Part17Block 24 328939 (by decide +kernel)

private def cap5Part18Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.closed 35)))
    (.split (.onlyInclude (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 44 (.closed 44)))))))))))))
    (.onlyOmit 27 (.closed 35)))
    (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))
    (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.split (.onlyInclude (.onlyOmit 45 (.closed 43)))
    (.onlyOmit 43 (.closed 42)))
    (.onlyOmit 37 (.closed 43)))))))))))
    (.onlyOmit 28 (.closed 30)))))))))))))
    (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 25)))))
    (.onlyOmit 25 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.closed 32)))))
    (.split (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 43 (.closed 42)))
    (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 42 (.closed 43)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 28)))))))))
    (.onlyOmit 19 (.closed 21)))
    (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyInclude (.onlyOmit 30 (.closed 32)))))
    (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))))))))))

private def cap5Part18 : Certificate := cap5Part18Block.toCertificate

private theorem cap5Part18_checked : check 5 60 16 747 cap5Part18 = true :=
  checkFragment_sound cap5Part18Block 16 747 (by decide +kernel)

private def cap5Part19Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 30 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.closed 35)))
    (.onlyOmit 38 (.onlyOmit 38 (.split (.onlyOmit 38 (.onlyOmit 45 (.onlyOmit 38 (.onlyOmit 38 (.closed 45)))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 55 (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 52 (.closed 48)))))))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))))))
    (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 54 (.split (.split (.split (.split (.closed 54)
    (.onlyOmit 54 (.onlyOmit 47 (.onlyOmit 47 (.closed 53)))))
    (.onlyOmit 65 (.closed 46)))
    (.onlyOmit 43 (.onlyOmit 47 (.onlyOmit 54 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 54 (.onlyOmit 54 (.onlyInclude (.onlyOmit 51 (.closed 53)))))))))))
    (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 47 (.closed 46))))))))))))))
    (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 53 (.split (.split (.split (.split (.onlyOmit 53 (.split (.onlyOmit 53 (.closed 53))
    (.onlyOmit 46 (.closed 52))))
    (.onlyOmit 53 (.onlyOmit 46 (.onlyOmit 46 (.closed 52)))))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 63 (.closed 53)))))))))
    (.onlyOmit 63 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 53 (.closed 63)))))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 53 (.closed 53))))))))))))))))))
    (.onlyOmit 31 (.closed 35)))
    (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 35 (.closed 36))))))))))))

private def cap5Part19 : Certificate := cap5Part19Block.toCertificate

private theorem cap5Part19_checked : check 5 60 22 2114283 cap5Part19 = true :=
  checkFragment_sound cap5Part19Block 22 2114283 (by decide +kernel)

private def cap5Part20Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.closed 32)))))
    (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.closed 40)))
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 43 (.onlyOmit 55 (.onlyOmit 43 (.onlyOmit 43 (.closed 45)))))))))))))))))))
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 50 (.onlyOmit 48 (.onlyOmit 55 (.onlyOmit 48 (.onlyOmit 48 (.closed 50))))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 38 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 43 (.onlyOmit 38 (.onlyOmit 43 (.closed 38))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.closed 33)))
    (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.closed 48)))))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 43 (.onlyOmit 41 (.onlyOmit 48 (.onlyOmit 41 (.onlyOmit 41 (.closed 43))))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.split (.closed 41)
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 48 (.onlyOmit 46 (.onlyOmit 51 (.onlyOmit 46 (.onlyOmit 46 (.closed 48)))))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 31)))))))))

private def cap5Part20 : Certificate := cap5Part20Block.toCertificate

private theorem cap5Part20_checked : check 5 60 22 541419 cap5Part20 = true :=
  checkFragment_sound cap5Part20Block 22 541419 (by decide +kernel)

private def cap5Part21Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.closed 27)))))
    (.graft 22 2114283 cap5Part19 cap5Part19_checked))
    (.onlyOmit 21 (.closed 23)))
    (.onlyOmit 20 (.split (.graft 22 541419 cap5Part20 cap5Part20_checked)
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.closed 23)))))
    (.onlyOmit 23 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 41 (.onlyOmit 38 (.closed 41)))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 38 (.onlyOmit 38 (.split (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 53 (.closed 41))))))
    (.onlyOmit 35 (.onlyOmit 41 (.onlyOmit 38 (.onlyOmit 38 (.split (.onlyOmit 41 (.onlyOmit 41 (.closed 43)))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 53 (.onlyOmit 46 (.onlyOmit 46 (.closed 48))))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 41 (.closed 41))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))))

private def cap5Part21 : Certificate := cap5Part21Block.toCertificate

private theorem cap5Part21_checked : check 5 60 17 17131 cap5Part21 = true :=
  checkFragment_sound cap5Part21Block 17 17131 (by decide +kernel)

private def cap5Part22Block : Fragment 5 60 :=
  (.split (.split (.graft 11 235 cap5Part15 cap5Part15_checked)
    (.onlyOmit 11 (.onlyOmit 13 (.onlyOmit 13 (.split (.split (.split (.graft 17 1259 cap5Part16 cap5Part16_checked)
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.graft 24 328939 cap5Part17 cap5Part17_checked)))))))))
    (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))))))
    (.onlyOmit 25 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyOmit 33 (.split (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 44 (.closed 41)))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 41 (.closed 36))))))
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 44 (.onlyOmit 36 (.onlyOmit 36 (.closed 44))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 33 (.closed 28))))))))))
    (.onlyOmit 18 (.closed 20)))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 32)))))))))))))))))
    (.onlyOmit 10 (.onlyOmit 12 (.onlyOmit 12 (.split (.split (.split (.graft 16 747 cap5Part18 cap5Part18_checked)
    (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.closed 20)))))
    (.onlyOmit 15 (.split (.graft 17 17131 cap5Part21 cap5Part21_checked)
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 40)))))))))))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 22)))))))))))))

private def cap5Part22 : Certificate := cap5Part22Block.toCertificate

private theorem cap5Part22_checked : check 5 60 9 235 cap5Part22 = true :=
  checkFragment_sound cap5Part22Block 9 235 (by decide +kernel)

private def cap5Part23Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 32))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.closed 27)
    (.onlyOmit 27 (.closed 25)))
    (.onlyOmit 22 (.closed 27))))))))
    (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 26 (.closed 24)))))))
    (.onlyOmit 20 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 25 (.closed 24)))))))))
    (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.split (.onlyOmit 20 (.onlyOmit 20 (.closed 25)))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.closed 25)))))))))))
    (.onlyOmit 14 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 34))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 29))))))))
    (.split (.closed 20)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.closed 26)))))))))
    (.onlyOmit 17 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 27))))))))
    (.onlyOmit 16 (.split (.split (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 26 (.closed 24)))))))))))

private def cap5Part23 : Certificate := cap5Part23Block.toCertificate

private theorem cap5Part23_checked : check 5 60 13 2587 cap5Part23 = true :=
  checkFragment_sound cap5Part23Block 13 2587 (by decide +kernel)

private def cap5Part24Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.closed 18)
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.closed 31)
    (.onlyOmit 31 (.closed 29))))))))
    (.onlyOmit 24 (.closed 23))))))))
    (.onlyOmit 18 (.split (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.split (.closed 22)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 39)))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 20 (.closed 22))))))))
    (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 42)))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 42 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.closed 42)))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 48 (.closed 42)))))))))))))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 36))))))))))))))))))))
    (.onlyOmit 13 (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26))))))))
    (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 15 (.split (.onlyOmit 18 (.onlyOmit 18 (.closed 22)))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 22))))))))))

private def cap5Part24 : Certificate := cap5Part24Block.toCertificate

private theorem cap5Part24_checked : check 5 60 12 1307 cap5Part24 = true :=
  checkFragment_sound cap5Part24Block 12 1307 (by decide +kernel)

private def cap5Part25Block : Fragment 5 60 :=
  (.split (.onlyOmit 12 (.onlyOmit 12 (.split (.onlyInclude (.split (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 23 (.closed 22)))
    (.onlyOmit 22 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 38)))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 23 (.closed 23)))))))
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 28))))))
    (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 28 (.closed 28)))))))
    (.onlyOmit 19 (.closed 21))))))))))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 30 (.closed 29))))))))
    (.onlyOmit 24 (.closed 23))))))))
    (.onlyOmit 18 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 29 (.closed 35)))))))
    (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 29 (.closed 28))))))))
    (.onlyOmit 23 (.closed 22))))))))))))

private def cap5Part25 : Certificate := cap5Part25Block.toCertificate

private theorem cap5Part25_checked : check 5 60 10 795 cap5Part25 = true :=
  checkFragment_sound cap5Part25Block 10 795 (by decide +kernel)

private def cap5Part26Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 12 (.graft 13 2587 cap5Part23 cap5Part23_checked)))
    (.split (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 19 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.closed 32)
    (.onlyOmit 31 (.closed 32))))))))
    (.onlyOmit 25 (.closed 24)))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 37 (.closed 32))))))))))))))
    (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 24 (.closed 23)))))))
    (.onlyOmit 19 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 24 (.closed 24))))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 32 (.closed 39))))))))
    (.onlyOmit 26 (.closed 25)))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 32)))))))))))))
    (.onlyOmit 19 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 26 (.closed 26)))))))))))))))
    (.split (.onlyInclude (.onlyOmit 11 (.graft 12 1307 cap5Part24 cap5Part24_checked)))
    (.graft 10 795 cap5Part25 cap5Part25_checked)))

private def cap5Part26 : Certificate := cap5Part26Block.toCertificate

private theorem cap5Part26_checked : check 5 60 8 27 cap5Part26 = true :=
  checkFragment_sound cap5Part26Block 8 27 (by decide +kernel)

private def cap5Part27Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 28 (.onlyOmit 28 (.closed 33))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 35)))))))))))))
    (.split (.closed 21)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33))))))))))))
    (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))))
    (.onlyOmit 17 (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 30))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 25)))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 29))))))
    (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 45)))))))))))))))))))))))))))

private def cap5Part27 : Certificate := cap5Part27Block.toCertificate

private theorem cap5Part27_checked : check 5 60 15 17051 cap5Part27 = true :=
  checkFragment_sound cap5Part27Block 15 17051 (by decide +kernel)

private def cap5Part28Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.closed 24)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.closed 36)))
    (.onlyOmit 36 (.onlyOmit 49 (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 49 (.closed 44))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 56 (.closed 44)))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))))))))
    (.graft 15 17051 cap5Part27 cap5Part27_checked))
    (.split (.closed 16)
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 27 (.closed 27))))))))))))
    (.onlyOmit 13 (.split (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 21 (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 39))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 29 (.onlyOmit 29 (.closed 31)))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 26 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 36 (.closed 31))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 21 (.onlyOmit 21 (.split (.closed 21)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 33))))))))))))))))))

private def cap5Part28 : Certificate := cap5Part28Block.toCertificate

private theorem cap5Part28_checked : check 5 60 12 667 cap5Part28 = true :=
  checkFragment_sound cap5Part28Block 12 667 (by decide +kernel)

private def cap5Part29Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 37 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 30)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.closed 25)))))))))
    (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 15 (.split (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 28 (.onlyOmit 28 (.closed 33))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.closed 28)))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 23 (.onlyOmit 23 (.closed 25)))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 20 (.split (.closed 20)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))))))))))

private def cap5Part29 : Certificate := cap5Part29Block.toCertificate

private theorem cap5Part29_checked : check 5 60 13 2715 cap5Part29 = true :=
  checkFragment_sound cap5Part29Block 13 2715 (by decide +kernel)

private def cap5Part30Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 26 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 26 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 32))))))))))))
    (.onlyOmit 21 (.closed 20)))
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 45 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.onlyOmit 45 (.closed 45))
    (.onlyOmit 37 (.closed 45)))
    (.onlyOmit 36 (.onlyOmit 45 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 42)))))))))))))))
    (.onlyOmit 34 (.closed 29)))
    (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 38 (.closed 40)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40)))))))))))))
    (.onlyOmit 25 (.split (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 42)))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 42)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 39)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 34))))))))))))))))))

private def cap5Part30 : Certificate := cap5Part30Block.toCertificate

private theorem cap5Part30_checked : check 5 60 16 8603 cap5Part30 = true :=
  checkFragment_sound cap5Part30Block 16 8603 (by decide +kernel)

private def cap5Part31Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 37 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 37 (.closed 37))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.onlyOmit 39 (.onlyOmit 39 (.split (.split (.closed 39)
    (.onlyOmit 39 (.closed 37)))
    (.onlyOmit 34 (.closed 39)))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 39))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 39))))))))))))
    (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 38 (.onlyOmit 38 (.split (.split (.closed 38)
    (.onlyOmit 38 (.closed 36)))
    (.onlyOmit 33 (.closed 38)))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 37))))))))))))
    (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 37 (.onlyOmit 37 (.split (.split (.closed 37)
    (.onlyOmit 37 (.closed 35)))
    (.onlyOmit 32 (.closed 37)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.closed 37)))))))))))))))
    (.onlyOmit 22 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 24 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 36 (.split (.split (.closed 36)
    (.onlyOmit 36 (.closed 34)))
    (.onlyOmit 31 (.closed 36))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 36))))))))))))

private def cap5Part31 : Certificate := cap5Part31Block.toCertificate

private theorem cap5Part31_checked : check 5 60 21 41371 cap5Part31 = true :=
  checkFragment_sound cap5Part31Block 21 41371 (by decide +kernel)

private def cap5Part32Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.graft 21 41371 cap5Part31 cap5Part31_checked)
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 37))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 41)))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.closed 41))))))))))))
    (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))
    (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.closed 32)))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 41 (.onlyOmit 41 (.closed 39))))))))))))
    (.onlyOmit 24 (.split (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 36))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 40 (.onlyOmit 38 (.closed 38)))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))))))

private def cap5Part32 : Certificate := cap5Part32Block.toCertificate

private theorem cap5Part32_checked : check 5 60 17 41371 cap5Part32 = true :=
  checkFragment_sound cap5Part32Block 17 41371 (by decide +kernel)

private def cap5Part33Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 21 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyInclude (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.split (.onlyOmit 50 (.closed 50))
    (.onlyOmit 41 (.closed 50)))))))))))))
    (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 48 (.closed 48)))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 48 (.onlyOmit 48 (.closed 50)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 38)))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 40 (.onlyInclude (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 52 (.onlyOmit 52 (.closed 52))))))))))))))
    (.onlyOmit 40 (.closed 40)))
    (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 50 (.onlyOmit 50 (.closed 50))))))))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.closed 27))))))

private def cap5Part33 : Certificate := cap5Part33Block.toCertificate

private theorem cap5Part33_checked : check 5 60 19 263067 cap5Part33 = true :=
  checkFragment_sound cap5Part33Block 19 263067 (by decide +kernel)

private def cap5Part34Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 40 (.closed 40)))
    (.split (.onlyInclude (.onlyOmit 33 (.split (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 51 (.closed 51))
    (.onlyOmit 49 (.closed 51)))))))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 51 (.onlyOmit 51 (.closed 51)))))))))))))
    (.onlyOmit 39 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.closed 39)))))))
    (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 50)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 40)))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.onlyInclude (.onlyOmit 42 (.closed 42)))
    (.onlyOmit 40 (.onlyInclude (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.split (.onlyOmit 53 (.closed 53))
    (.onlyOmit 44 (.closed 53))))))))))))))
    (.onlyOmit 32 (.closed 40)))))))))))))
    (.onlyOmit 28 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.closed 28)))))))
    (.graft 19 263067 cap5Part33 cap5Part33_checked))

private def cap5Part34 : Certificate := cap5Part34Block.toCertificate

private theorem cap5Part34_checked : check 5 60 18 923 cap5Part34 = true :=
  checkFragment_sound cap5Part34Block 18 923 (by decide +kernel)

private def cap5Part35Block : Fragment 5 60 :=
  (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 46 (.onlyOmit 46 (.onlyInclude (.onlyOmit 44 (.closed 46)))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 48 (.onlyOmit 48 (.closed 46)))))))))))))
    (.onlyOmit 37 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 47 (.closed 57)))
    (.onlyOmit 46 (.closed 47)))))))))))))
    (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 45 (.onlyOmit 45 (.onlyInclude (.onlyOmit 43 (.closed 45)))))))))))))
    (.onlyOmit 36 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.closed 34)))))))
    (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 44 (.onlyOmit 44 (.onlyInclude (.onlyOmit 42 (.closed 44)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 38)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 48 (.onlyOmit 48 (.closed 50)))))))))))))
    (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 46 (.onlyOmit 48 (.closed 48))))))))))))))))))))))

private def cap5Part35 : Certificate := cap5Part35Block.toCertificate

private theorem cap5Part35_checked : check 5 60 20 328603 cap5Part35 = true :=
  checkFragment_sound cap5Part35Block 20 328603 (by decide +kernel)

private def cap5Part36Block : Fragment 5 60 :=
  (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 57)))))))))))))))))))))
    (.onlyOmit 24 (.closed 23)))
    (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 35 (.closed 40)))
    (.split (.split (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 49 (.onlyOmit 49 (.closed 51)))))))
    (.onlyOmit 44 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 49)))))))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 51 (.closed 51))
    (.onlyOmit 49 (.closed 51))))))))))))
    (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 37)))))))
    (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 50)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 35)))))))))))))
    (.onlyOmit 19 (.graft 20 328603 cap5Part35 cap5Part35_checked))))

private def cap5Part36 : Certificate := cap5Part36Block.toCertificate

private theorem cap5Part36_checked : check 5 60 17 66459 cap5Part36 = true :=
  checkFragment_sound cap5Part36Block 17 66459 (by decide +kernel)

private def cap5Part37Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.closed 45)
    (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 55 (.closed 45))))))))))))))))))))))
    (.onlyOmit 23 (.closed 22)))
    (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.split (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyInclude (.onlyOmit 45 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 49 (.closed 51))))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 51 (.closed 51))
    (.onlyOmit 42 (.closed 51)))))))))))))
    (.onlyOmit 38 (.closed 33)))
    (.onlyOmit 33 (.closed 38)))
    (.onlyOmit 29 (.split (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.split (.closed 48)
    (.onlyOmit 42 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 46 (.closed 48))))))))))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 48 (.closed 48))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 38))))))))))))))))))))

private def cap5Part37 : Certificate := cap5Part37Block.toCertificate

private theorem cap5Part37_checked : check 5 60 18 33691 cap5Part37 = true :=
  checkFragment_sound cap5Part37Block 18 33691 (by decide +kernel)

private def cap5Part38Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 44 (.split (.onlyInclude (.onlyOmit 44 (.closed 42)))
    (.onlyOmit 42 (.closed 44))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 42)))))))))))
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))
    (.split (.onlyInclude (.onlyOmit 29 (.split (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 43 (.split (.onlyInclude (.onlyOmit 43 (.closed 41)))
    (.onlyOmit 41 (.closed 43))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 41))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 45 (.onlyOmit 43 (.closed 43)))))))))))))
    (.onlyOmit 35 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 41 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 54 (.split (.onlyInclude (.onlyOmit 53 (.closed 52)))
    (.onlyOmit 52 (.closed 54))))))))))))))
    (.onlyOmit 44 (.closed 53)))))))))))))
    (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 42 (.split (.onlyInclude (.onlyOmit 42 (.closed 40)))
    (.onlyOmit 40 (.closed 42))))))))))))))

private def cap5Part38 : Certificate := cap5Part38Block.toCertificate

private theorem cap5Part38_checked : check 5 60 25 164763 cap5Part38 = true :=
  checkFragment_sound cap5Part38Block 25 164763 (by decide +kernel)

private def cap5Part39Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 18 923 cap5Part34 cap5Part34_checked)
    (.split (.onlyInclude (.onlyOmit 20 (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 48 (.closed 48)))))))))))
    (.onlyOmit 38 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 36)))))))
    (.onlyOmit 36 (.onlyInclude (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 47 (.onlyOmit 47 (.closed 47)))))))))))))
    (.onlyOmit 28 (.closed 36)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 40 (.closed 40)))
    (.onlyOmit 38 (.onlyInclude (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 49 (.onlyOmit 49 (.closed 51))))))))))))))
    (.onlyOmit 30 (.closed 38)))))))))))))
    (.onlyOmit 26 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.closed 26)))))))
    (.graft 17 66459 cap5Part36 cap5Part36_checked))
    (.onlyOmit 16 (.split (.graft 18 33691 cap5Part37 cap5Part37_checked)
    (.onlyOmit 18 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.graft 25 164763 cap5Part38 cap5Part38_checked)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42))))))
    (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 49 (.closed 44))))))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 36)))))))
    (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 45 (.onlyOmit 47 (.closed 47)))))))))))))
    (.onlyOmit 28 (.closed 36)))))))))))))))

private def cap5Part39 : Certificate := cap5Part39Block.toCertificate

private theorem cap5Part39_checked : check 5 60 15 923 cap5Part39 = true :=
  checkFragment_sound cap5Part39Block 15 923 (by decide +kernel)

private def cap5Part40Block : Fragment 5 60 :=
  (.split (.onlyOmit 11 (.onlyOmit 11 (.split (.onlyInclude (.split (.split (.graft 16 8603 cap5Part30 cap5Part30_checked)
    (.onlyOmit 16 (.graft 17 41371 cap5Part32 cap5Part32_checked)))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 21 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 27 (.closed 27))))))))))))
    (.split (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.split (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 29 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 39)))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 29)))))))
    (.onlyOmit 25 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 35))))))))))))
    (.onlyOmit 20 (.closed 19)))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 20 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 31)))))))))))))))))))
    (.onlyOmit 10 (.onlyOmit 11 (.onlyOmit 12 (.split (.split (.graft 15 923 cap5Part39 cap5Part39_checked)
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 22 (.closed 21)))))))
    (.onlyOmit 17 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32))))))
    (.onlyOmit 27 (.closed 26)))))))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 31))))))))))))))))))))

private def cap5Part40 : Certificate := cap5Part40Block.toCertificate

private theorem cap5Part40_checked : check 5 60 9 411 cap5Part40 = true :=
  checkFragment_sound cap5Part40Block 9 411 (by decide +kernel)

private def cap5Part41Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 36))))))
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 37))))))))))))))
    (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 45))))))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 35)))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 31)))))))))))
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.split (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.closed 36)))
    (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.closed 41))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))
    (.onlyOmit 43 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))
    (.onlyOmit 28 (.closed 27)))
    (.onlyOmit 24 (.closed 29)))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.closed 36))))))))))))))))

private def cap5Part41 : Certificate := cap5Part41Block.toCertificate

private theorem cap5Part41_checked : check 5 60 18 71771 cap5Part41 = true :=
  checkFragment_sound cap5Part41Block 18 71771 (by decide +kernel)

private def cap5Part42Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 40 (.split (.split (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.split (.onlyOmit 40 (.onlyOmit 40 (.closed 47)))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 52 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 59 (.closed 47))))))))))))))
    (.onlyOmit 33 (.closed 35)))
    (.onlyOmit 32 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 45 (.closed 57))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 52 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 47 (.closed 45))))))))))))))))))))))))))
    (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.closed 24)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 32 (.closed 28))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.split (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 40 (.closed 36))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 37)))))))))
    (.onlyOmit 29 (.closed 28))))))))))
    (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 17 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))))

private def cap5Part42 : Certificate := cap5Part42Block.toCertificate

private theorem cap5Part42_checked : check 5 60 16 17499 cap5Part42 = true :=
  checkFragment_sound cap5Part42Block 16 17499 (by decide +kernel)

private def cap5Part43Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 25))))))))))
    (.split (.graft 16 17499 cap5Part42 cap5Part42_checked)
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.split (.split (.onlyOmit 37 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 33 (.closed 37))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 37))))))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 36 (.closed 32))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 37)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 37 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 36))))))))))))))
    (.onlyOmit 25 (.closed 24)))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.closed 42)))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.closed 49))))))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 25 (.onlyOmit 25 (.closed 29)))))))))))))

private def cap5Part43 : Certificate := cap5Part43Block.toCertificate

private theorem cap5Part43_checked : check 5 60 14 1115 cap5Part43 = true :=
  checkFragment_sound cap5Part43Block 14 1115 (by decide +kernel)

private def cap5Part44Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.closed 29)))
    (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 40 (.closed 36))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 29 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 25 (.closed 29)))))))))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.closed 27))))))))))
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.closed 26))))))))))
    (.onlyOmit 16 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))
    (.onlyOmit 38 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.closed 37))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 26 (.closed 25)))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.closed 29)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 33))))))))))))))))))

private def cap5Part44 : Certificate := cap5Part44Block.toCertificate

private theorem cap5Part44_checked : check 5 60 15 3163 cap5Part44 = true :=
  checkFragment_sound cap5Part44Block 15 3163 (by decide +kernel)

private def cap5Part45Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 14 (.split (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.closed 24)))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))))))))))
    (.split (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.closed 32))))))))))
    (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.closed 31))))))))
    (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 29 (.closed 30))))))))))
    (.onlyOmit 18 (.closed 23)))
    (.onlyOmit 17 (.graft 18 71771 cap5Part41 cap5Part41_checked)))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 31 (.closed 33)))
    (.split (.closed 32)
    (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 38)))))))))
    (.onlyOmit 26 (.closed 31))))))))
    (.onlyOmit 23 (.closed 25)))
    (.onlyOmit 19 (.closed 24))))))))))
    (.split (.split (.split (.graft 14 1115 cap5Part43 cap5Part43_checked)
    (.onlyOmit 14 (.closed 16)))
    (.onlyOmit 13 (.split (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 25 (.closed 27))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.closed 22))))))))))
    (.split (.onlyOmit 14 (.onlyOmit 14 (.graft 15 3163 cap5Part44 cap5Part44_checked)))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 29)))
    (.onlyOmit 29 (.closed 31)))
    (.onlyOmit 25 (.closed 30))))))))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 29 (.closed 28)))
    (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 24 (.closed 29))))))))
    (.onlyOmit 18 (.closed 23))))))))))

private def cap5Part45 : Certificate := cap5Part45Block.toCertificate

private theorem cap5Part45_checked : check 5 60 10 91 cap5Part45 = true :=
  checkFragment_sound cap5Part45Block 10 91 (by decide +kernel)

private def cap5Part46Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.closed 20)))
    (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))))
    (.onlyOmit 16 (.closed 18)))
    (.onlyOmit 15 (.onlyOmit 20 (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.split (.split (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 30 (.onlyOmit 30 (.closed 34))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 35 (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 31 (.closed 35))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.closed 34))))))))))))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))))))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 28))))))))
    (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 32 (.closed 31)))
    (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 35))))))))
    (.onlyOmit 27 (.closed 32)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 31))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 30))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.closed 25))))))))))

private def cap5Part46 : Certificate := cap5Part46Block.toCertificate

private theorem cap5Part46_checked : check 5 60 13 4443 cap5Part46 = true :=
  checkFragment_sound cap5Part46Block 13 4443 (by decide +kernel)

private def cap5Part47Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 24 (.closed 24)))
    (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 29 (.closed 31))))))))
    (.onlyOmit 23 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 29 (.closed 30))))))))))
    (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 30)))))))))))))
    (.onlyOmit 16 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 23 (.closed 23)))
    (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 29 (.closed 28)))
    (.onlyOmit 28 (.closed 29))))))))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 29 (.closed 29)))))))))))))))
    (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 28)))
    (.onlyOmit 28 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 36 (.closed 36)))))))))
    (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 25 (.closed 30)))))))))
    (.onlyOmit 22 (.closed 22)))
    (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))))))))))
    (.onlyOmit 15 (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 21 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 36)))))))
    (.onlyOmit 28 (.closed 27)))
    (.onlyOmit 24 (.closed 28)))))))))
    (.onlyOmit 21 (.closed 21)))))))))

private def cap5Part47 : Certificate := cap5Part47Block.toCertificate

private theorem cap5Part47_checked : check 5 60 10 59 cap5Part47 = true :=
  checkFragment_sound cap5Part47Block 10 59 (by decide +kernel)

private def cap5Part48Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.split (.closed 20)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 35)))))))
    (.onlyOmit 27 (.closed 26)))))))))
    (.onlyOmit 20 (.split (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 34 (.closed 32)))
    (.onlyOmit 32 (.closed 39)))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))
    (.onlyOmit 27 (.closed 25)))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))))))))
    (.onlyOmit 16 (.closed 20)))))))
    (.onlyOmit 14 (.onlyOmit 13 (.onlyOmit 13 (.onlyOmit 14 (.split (.onlyInclude (.split (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 26 (.closed 25)))
    (.onlyOmit 25 (.closed 26)))
    (.onlyOmit 21 (.closed 25)))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 26 (.closed 26))))))))
    (.onlyOmit 19 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 32)))))))
    (.onlyOmit 22 (.closed 24))))))))))))))

private def cap5Part48 : Certificate := cap5Part48Block.toCertificate

private theorem cap5Part48_checked : check 5 60 10 571 cap5Part48 = true :=
  checkFragment_sound cap5Part48Block 10 571 (by decide +kernel)

private def cap5Part49Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 46))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.closed 40)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.closed 46)))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.closed 46)))))))))))))
    (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 46))))))))))))))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 46 (.closed 40))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 34 (.onlyOmit 34 (.closed 43)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.closed 46))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 34)))
    (.split (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 42 (.closed 36)))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 42))))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 36))))))))
    (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.closed 46))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))))))))

private def cap5Part49 : Certificate := cap5Part49Block.toCertificate

private theorem cap5Part49_checked : check 5 60 22 1065275 cap5Part49 = true :=
  checkFragment_sound cap5Part49Block 22 1065275 (by decide +kernel)

private def cap5Part50Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.graft 22 1065275 cap5Part49 cap5Part49_checked)
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 41))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 41))))))))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.closed 46)))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 34))))))))))))))
    (.split (.closed 22)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 46 (.onlyOmit 40 (.onlyOmit 40 (.closed 46)))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.closed 40))))))))))))
    (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.closed 39)))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 33))))))))))))))
    (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.closed 32)))
    (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 46 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.closed 38))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 34))))))))
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.closed 38))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))))))))))

private def cap5Part50 : Certificate := cap5Part50Block.toCertificate

private theorem cap5Part50_checked : check 5 60 18 16699 cap5Part50 = true :=
  checkFragment_sound cap5Part50Block 18 16699 (by decide +kernel)

private def cap5Part51Block : Fragment 5 60 :=
  (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.split (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 43 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 49 (.onlyOmit 46 (.onlyOmit 46 (.closed 52))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 55 (.closed 52))))))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 49 (.onlyOmit 46 (.onlyOmit 46 (.closed 52)))))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 49 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 52 (.onlyOmit 49 (.onlyOmit 49 (.closed 58))))))))))))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.closed 46)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.closed 37))))))))))

private def cap5Part51 : Certificate := cap5Part51Block.toCertificate

private theorem cap5Part51_checked : check 5 60 20 147771 cap5Part51 = true :=
  checkFragment_sound cap5Part51Block 20 147771 (by decide +kernel)

private def cap5Part52Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 39 (.split (.split (.closed 39)
    (.onlyOmit 37 (.closed 39)))
    (.onlyOmit 33 (.closed 37))))))))))))
    (.split (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 48 (.closed 50))))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.closed 36)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 38)))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 50 (.closed 48))))))))))))))))))))))))))
    (.onlyOmit 22 (.closed 24)))
    (.onlyOmit 21 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.closed 46))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))))
    (.onlyOmit 30 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.closed 30))))))))))

private def cap5Part52 : Certificate := cap5Part52Block.toCertificate

private theorem cap5Part52_checked : check 5 60 20 82235 cap5Part52 = true :=
  checkFragment_sound cap5Part52Block 20 82235 (by decide +kernel)

private def cap5Part53Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 18 16699 cap5Part50 cap5Part50_checked)
    (.onlyOmit 18 (.onlyOmit 22 (.graft 20 147771 cap5Part51 cap5Part51_checked))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.graft 20 82235 cap5Part52 cap5Part52_checked)))))
    (.onlyOmit 19 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 47 (.onlyOmit 47 (.closed 48))))))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 36 (.closed 35)))
    (.onlyOmit 35 (.closed 36)))
    (.onlyOmit 31 (.closed 35)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 48)))))))))))))))))))))))))
    (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.closed 46)))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 34))))))))
    (.onlyOmit 29 (.closed 28)))
    (.onlyOmit 25 (.closed 29)))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 35)))))))))))))

private def cap5Part53 : Certificate := cap5Part53Block.toCertificate

private theorem cap5Part53_checked : check 5 60 15 16699 cap5Part53 = true :=
  checkFragment_sound cap5Part53Block 15 16699 (by decide +kernel)

private def cap5Part54Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 28 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 48 (.onlyOmit 48 (.closed 48)))))))
    (.onlyOmit 42 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 46 (.closed 48)))))))
    (.onlyOmit 38 (.closed 40)))))))
    (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.split (.closed 59)
    (.onlyOmit 47 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.closed 53))))))))))))))))))
    (.onlyOmit 32 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.closed 40)))
    (.onlyOmit 40 (.onlyOmit 51 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 57 (.onlyOmit 51 (.onlyOmit 57 (.split (.closed 51)
    (.onlyOmit 49 (.closed 48))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 49 (.closed 51))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.onlyOmit 42 (.closed 42))
    (.onlyOmit 37 (.closed 42)))
    (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 40 (.onlyOmit 40 (.closed 42)))))))))))))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 47 (.onlyOmit 47 (.closed 47)))))))
    (.onlyOmit 41 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 45 (.closed 47))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 53)))))))))))))

private def cap5Part54 : Certificate := cap5Part54Block.toCertificate

private theorem cap5Part54_checked : check 5 60 26 2138427 cap5Part54 = true :=
  checkFragment_sound cap5Part54Block 26 2138427 (by decide +kernel)

private def cap5Part55Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.graft 26 2138427 cap5Part54 cap5Part54_checked)
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.closed 34)))
    (.onlyOmit 34 (.onlyOmit 45 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.onlyOmit 45 (.split (.split (.closed 45)
    (.onlyOmit 43 (.closed 45)))
    (.onlyOmit 39 (.closed 43))))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 51 (.onlyOmit 45 (.onlyOmit 45 (.closed 51)))))))))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 43 (.closed 45))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 31 (.closed 36)))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.closed 34)))
    (.onlyOmit 34 (.closed 35)))
    (.onlyOmit 30 (.closed 34)))
    (.onlyOmit 29 (.onlyOmit 43 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 43)
    (.onlyOmit 41 (.closed 43)))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 43 (.onlyOmit 43 (.closed 43)))))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 48 (.closed 48)))))))
    (.onlyOmit 42 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 48 (.closed 46))))))))))))))))))))))))

private def cap5Part55 : Certificate := cap5Part55Block.toCertificate

private theorem cap5Part55_checked : check 5 60 22 2138427 cap5Part55 = true :=
  checkFragment_sound cap5Part55Block 22 2138427 (by decide +kernel)

private def cap5Part56Block : Fragment 5 60 :=
  (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 44 (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 44 (.onlyOmit 50 (.closed 44))))))))
    (.onlyOmit 36 (.closed 38)))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 44 (.closed 55)))))))))))))
    (.onlyOmit 30 (.closed 32)))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 39 (.closed 38)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 51 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 45 (.closed 45))))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 43 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 49 (.closed 43)))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 34 (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.closed 34)))))))))))

private def cap5Part56 : Certificate := cap5Part56Block.toCertificate

private theorem cap5Part56_checked : check 5 60 21 565563 cap5Part56 = true :=
  checkFragment_sound cap5Part56Block 21 565563 (by decide +kernel)

private def cap5Part57Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.closed 34)))
    (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.closed 41)))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 43 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 49 (.onlyOmit 43 (.onlyOmit 43 (.closed 49))))))))))))))))))
    (.onlyOmit 27 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 46))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.closed 40))))))))))))
    (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.closed 45)))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 33))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.closed 44)))))))
    (.onlyOmit 33 (.closed 32))))))))
    (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 43)))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.closed 34)))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 42 (.onlyOmit 36 (.onlyOmit 36 (.closed 42))))))))))))))))

private def cap5Part57 : Certificate := cap5Part57Block.toCertificate

private theorem cap5Part57_checked : check 5 60 22 1073467 cap5Part57 = true :=
  checkFragment_sound cap5Part57Block 22 1073467 (by decide +kernel)

private def cap5Part58Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 22 (.closed 26)))
    (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.closed 32)))
    (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 46 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 34))))))))
    (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 44 (.closed 38)))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 43 (.closed 37))))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.closed 34)
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))
    (.onlyOmit 28 (.closed 30))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 41 (.onlyOmit 35 (.onlyOmit 35 (.closed 41)))))))))))))))))

private def cap5Part58 : Certificate := cap5Part58Block.toCertificate

private theorem cap5Part58_checked : check 5 60 20 20795 cap5Part58 = true :=
  checkFragment_sound cap5Part58Block 20 20795 (by decide +kernel)

private def cap5Part59Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.graft 15 16699 cap5Part53 cap5Part53_checked))
    (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 32 (.closed 37)))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))))))))
    (.graft 22 2138427 cap5Part55 cap5Part55_checked))
    (.onlyOmit 21 (.closed 23)))
    (.onlyOmit 20 (.graft 21 565563 cap5Part56 cap5Part56_checked)))))))
    (.onlyOmit 18 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.graft 22 1073467 cap5Part57 cap5Part57_checked)))
    (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.closed 44)))))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 33 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.closed 33)))))))))))))))))
    (.onlyOmit 13 (.onlyInclude (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.graft 20 20795 cap5Part58 cap5Part58_checked)
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 42 (.onlyOmit 42 (.closed 44)))))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 32 (.onlyOmit 26 (.onlyOmit 26 (.closed 32))))))))))))))))

private def cap5Part59 : Certificate := cap5Part59Block.toCertificate

private theorem cap5Part59_checked : check 5 60 12 315 cap5Part59 = true :=
  checkFragment_sound cap5Part59Block 12 315 (by decide +kernel)

private def cap5Part60Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.closed 43))))))))))))))))
    (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40))))))))))))))
    (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 47 (.closed 44)))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))))))
    (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 37 (.onlyOmit 31 (.onlyOmit 31 (.closed 37)))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 43 (.closed 43))))))))
    (.onlyOmit 36 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 45 (.closed 36))))))))))
    (.onlyOmit 30 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 36)))))))
    (.onlyOmit 25 (.closed 27)))
    (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))))))

private def cap5Part60 : Certificate := cap5Part60Block.toCertificate

private theorem cap5Part60_checked : check 5 60 19 133435 cap5Part60 = true :=
  checkFragment_sound cap5Part60Block 19 133435 (by decide +kernel)

private def cap5Part61Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.graft 19 133435 cap5Part60 cap5Part60_checked)
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 35)))))))
    (.onlyOmit 28 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.closed 35)))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 46 (.onlyOmit 46 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 49 (.onlyOmit 49 (.closed 55))))))))))))))))))))))))))))))))))
    (.split (.closed 19)
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40)))))))))))))
    (.onlyOmit 27 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.closed 33))))))))))))))
    (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 41 (.onlyOmit 35 (.onlyOmit 35 (.closed 41))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 41 (.onlyOmit 32 (.onlyOmit 32 (.closed 41))))))))))
    (.onlyOmit 28 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))
    (.onlyOmit 23 (.closed 25)))
    (.onlyOmit 22 (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 32)))))))))))))

private def cap5Part61 : Certificate := cap5Part61Block.toCertificate

private theorem cap5Part61_checked : check 5 60 15 2363 cap5Part61 = true :=
  checkFragment_sound cap5Part61Block 15 2363 (by decide +kernel)

private def cap5Part62Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 21 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 35 (.closed 37))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 52 (.onlyOmit 49 (.onlyOmit 49 (.closed 58)))))))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 46))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 46))))))))))))))))
    (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 42 (.onlyOmit 42 (.closed 44)))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 53))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 39 (.onlyOmit 39 (.closed 41))))))))))))))))))))))

private def cap5Part62 : Certificate := cap5Part62Block.toCertificate

private theorem cap5Part62_checked : check 5 60 19 10555 cap5Part62 = true :=
  checkFragment_sound cap5Part62Block 19 10555 (by decide +kernel)

private def cap5Part63Block : Fragment 5 60 :=
  (.split (.split (.graft 15 2363 cap5Part61 cap5Part61_checked)
    (.onlyOmit 15 (.onlyOmit 19 (.split (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.closed 46)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.closed 34))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 25 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 37 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))))))))))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.graft 19 10555 cap5Part62 cap5Part62_checked)
    (.onlyOmit 19 (.closed 21)))
    (.onlyOmit 18 (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 43))))))))))))))))
    (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 39 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 45 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 50 (.onlyOmit 48 (.onlyOmit 48 (.closed 50))))))))))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 45 (.onlyOmit 39 (.onlyOmit 39 (.closed 45))))))))))))))))))))))))))))

private def cap5Part63 : Certificate := cap5Part63Block.toCertificate

private theorem cap5Part63_checked : check 5 60 13 2363 cap5Part63 = true :=
  checkFragment_sound cap5Part63Block 13 2363 (by decide +kernel)

private def cap5Part64Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 32 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.closed 40)))))))))))))))
    (.onlyOmit 26 (.closed 24)))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 38)))))))))))))))
    (.onlyOmit 20 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 35 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 35 (.closed 35)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 38 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 26 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 34 (.closed 34)))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 33 (.closed 33)))))))
    (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.closed 38)))))))))))))))))))

private def cap5Part64 : Certificate := cap5Part64Block.toCertificate

private theorem cap5Part64_checked : check 5 60 17 66875 cap5Part64 = true :=
  checkFragment_sound cap5Part64Block 17 66875 (by decide +kernel)

private def cap5Part65Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyInclude (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 48 (.closed 68)))))))))))))))))))
    (.onlyOmit 35 (.closed 33))))))))))))))))
    (.graft 17 66875 cap5Part64 cap5Part64_checked))
    (.split (.closed 18)
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 31 (.closed 30))))))))
    (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 31)))))))))))))
    (.onlyOmit 15 (.split (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.closed 24)))
    (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.closed 46))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))))
    (.onlyOmit 30 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 42 (.closed 36))))))))))))))))
    (.onlyOmit 24 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 24 (.split (.closed 24)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 38)))))))))))))))))))))

private def cap5Part65 : Certificate := cap5Part65Block.toCertificate

private theorem cap5Part65_checked : check 5 60 14 1339 cap5Part65 = true :=
  checkFragment_sound cap5Part65Block 14 1339 (by decide +kernel)

private def cap5Part66Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 44 (.closed 43)))))))
    (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 44 (.closed 44)))))))
    (.onlyOmit 35 (.closed 37))))))))))))
    (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 43 (.closed 54))))))))))))
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 43 (.closed 42)))))))
    (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 29 (.closed 31)))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 38 (.closed 37)))))))))))))
    (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.split (.split (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 52)))))))
    (.onlyOmit 43 (.closed 41)))
    (.onlyOmit 41 (.closed 44)))
    (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 41 (.onlyOmit 41 (.closed 43)))))))))))))
    (.onlyOmit 33 (.closed 32)))
    (.onlyOmit 29 (.closed 33)))))))))

private def cap5Part66 : Certificate := cap5Part66Block.toCertificate

private theorem cap5Part66_checked : check 5 60 22 549051 cap5Part66 = true :=
  checkFragment_sound cap5Part66Block 22 549051 (by decide +kernel)

private def cap5Part67Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 40)))))))))))))))))
    (.split (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 29)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.closed 34))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 35 (.closed 34)))
    (.onlyOmit 34 (.closed 35)))))))))))
    (.onlyOmit 22 (.closed 24)))
    (.onlyOmit 21 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.closed 29)))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 37 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.closed 36)))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 29)))
    (.onlyOmit 29 (.closed 30)))
    (.onlyOmit 25 (.closed 29)))
    (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 30 (.onlyOmit 30 (.closed 35))))))))))))))

private def cap5Part67 : Certificate := cap5Part67Block.toCertificate

private theorem cap5Part67_checked : check 5 60 18 135355 cap5Part67 = true :=
  checkFragment_sound cap5Part67Block 18 135355 (by decide +kernel)

private def cap5Part68Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 38)))))))))))))))))
    (.graft 18 135355 cap5Part67 cap5Part67_checked))
    (.onlyOmit 17 (.closed 19)))
    (.onlyOmit 16 (.split (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.closed 36)))))))))))
    (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 33 (.closed 32)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 35)))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 29 (.closed 34)))))))))))))))))

private def cap5Part68 : Certificate := cap5Part68Block.toCertificate

private theorem cap5Part68_checked : check 5 60 14 4283 cap5Part68 = true :=
  checkFragment_sound cap5Part68Block 14 4283 (by decide +kernel)

private def cap5Part69Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 28)))))))))
    (.onlyOmit 18 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.closed 27)))
    (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 21 (.closed 27)))
    (.onlyOmit 20 (.split (.graft 22 549051 cap5Part66 cap5Part66_checked)
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 33 (.closed 32)))
    (.onlyOmit 32 (.closed 33)))
    (.onlyOmit 28 (.closed 32)))))))))))))))))
    (.split (.graft 14 4283 cap5Part68 cap5Part68_checked)
    (.onlyOmit 17 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.closed 34)))))))))))
    (.onlyOmit 25 (.closed 25)))
    (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 31 (.closed 30)))
    (.onlyOmit 30 (.closed 31)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 41 (.closed 40))))))))))))))))))))))))))))

private def cap5Part69 : Certificate := cap5Part69Block.toCertificate

private theorem cap5Part69_checked : check 5 60 12 187 cap5Part69 = true :=
  checkFragment_sound cap5Part69Block 12 187 (by decide +kernel)

private def cap5Part70Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 44 (.closed 36)))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 35)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 33 (.onlyOmit 33 (.closed 35)))))))))))))))
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 25 (.onlyOmit 22 (.onlyOmit 22 (.split (.closed 25)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 28 (.onlyOmit 28 (.closed 33))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 51 (.closed 43)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.closed 40)))
    (.split (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 47))))))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 48))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 39 (.onlyOmit 34 (.onlyOmit 34 (.closed 39))))))))))))
    (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.split (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 39 (.closed 39))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))
    (.onlyOmit 33 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 38)))))))
    (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 39 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 39 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 34 (.closed 38)))))))))))))
    (.onlyOmit 23 (.closed 25)))
    (.onlyOmit 22 (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 31))))))))))))

private def cap5Part70 : Certificate := cap5Part70Block.toCertificate

private theorem cap5Part70_checked : check 5 60 16 33979 cap5Part70 = true :=
  checkFragment_sound cap5Part70Block 16 33979 (by decide +kernel)

private def cap5Part71Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 34 (.closed 34))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 42 (.onlyOmit 34 (.onlyOmit 34 (.closed 42))))))))))))))))))))
    (.graft 16 33979 cap5Part70 cap5Part70_checked))
    (.onlyOmit 15 (.closed 17)))
    (.onlyOmit 14 (.split (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 34)))))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 42 (.onlyOmit 34 (.onlyOmit 34 (.closed 42))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 31 (.closed 28))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 28 (.onlyOmit 25 (.onlyOmit 25 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 36 (.onlyOmit 31 (.onlyOmit 31 (.closed 36))))))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.split (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.closed 44)))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 38)))))))))
    (.onlyOmit 30 (.closed 28)))
    (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 36)))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 30)))))))))))))))

private def cap5Part71 : Certificate := cap5Part71Block.toCertificate

private theorem cap5Part71_checked : check 5 60 12 1211 cap5Part71 = true :=
  checkFragment_sound cap5Part71Block 12 1211 (by decide +kernel)

private def cap5Part72Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.closed 23)))
    (.onlyOmit 23 (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 28)))))))))
    (.onlyOmit 19 (.closed 21)))
    (.onlyOmit 18 (.split (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 34)))))))))
    (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.closed 38))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.split (.onlyInclude (.onlyOmit 39 (.closed 38)))
    (.onlyOmit 38 (.closed 39)))
    (.onlyOmit 34 (.closed 38)))
    (.onlyOmit 33 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 39 (.onlyOmit 39 (.closed 41)))))))))))))))))
    (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 31 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))))

private def cap5Part72 : Certificate := cap5Part72Block.toCertificate

private theorem cap5Part72_checked : check 5 60 17 17083 cap5Part72 = true :=
  checkFragment_sound cap5Part72Block 17 17083 (by decide +kernel)

private def cap5Part73Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 12 187 cap5Part69 cap5Part69_checked)
    (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.closed 24)))))))))))
    (.onlyOmit 11 (.graft 12 1211 cap5Part71 cap5Part71_checked)))
    (.onlyOmit 10 (.onlyOmit 12 (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))))))
    (.split (.split (.graft 17 17083 cap5Part72 cap5Part72_checked)
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.closed 23)))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))
    (.onlyOmit 29 (.closed 29)))
    (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 36 (.closed 37)))
    (.onlyOmit 36 (.closed 36)))
    (.onlyOmit 31 (.closed 37)))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.closed 36))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 26 (.closed 28)))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 29 (.closed 29)))))))))))))
    (.onlyOmit 14 (.closed 16)))))))

private def cap5Part73 : Certificate := cap5Part73Block.toCertificate

private theorem cap5Part73_checked : check 5 60 9 187 cap5Part73 = true :=
  checkFragment_sound cap5Part73Block 9 187 (by decide +kernel)

private def cap5Part74Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 28 (.closed 28)))
    (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 34 (.closed 34)))))))))
    (.onlyOmit 26 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 35)))))))))))))))
    (.onlyOmit 18 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 27 (.closed 27)))
    (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 33 (.closed 34)))
    (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 25 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.closed 34)))))))))))))))))
    (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 25 (.closed 25)))
    (.onlyOmit 25 (.closed 25))))))))))

private def cap5Part74 : Certificate := cap5Part74Block.toCertificate

private theorem cap5Part74_checked : check 5 60 12 123 cap5Part74 = true :=
  checkFragment_sound cap5Part74Block 12 123 (by decide +kernel)

private def cap5Part75Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.closed 29)))
    (.onlyOmit 29 (.split (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 42 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 35 (.closed 36)))
    (.onlyOmit 31 (.closed 35)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 44 (.split (.split (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 42 (.closed 42)))
    (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 42 (.onlyOmit 42 (.closed 44))))))))
    (.onlyOmit 36 (.split (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 52 (.closed 44))))))
    (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 62 (.onlyOmit 52 (.onlyOmit 52 (.closed 52)))))))))))))))
    (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 44 (.onlyOmit 44 (.closed 44))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.closed 42)))))))))))))))
    (.onlyOmit 25 (.closed 27))))))))
    (.onlyOmit 22 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 43)))))))))
    (.onlyOmit 28 (.closed 27)))))))))

private def cap5Part75 : Certificate := cap5Part75Block.toCertificate

private theorem cap5Part75_checked : check 5 60 18 132219 cap5Part75 = true :=
  checkFragment_sound cap5Part75Block 18 132219 (by decide +kernel)

private def cap5Part76Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.closed 28)))
    (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 42 (.closed 34))))))))))
    (.onlyOmit 24 (.closed 26))))))))
    (.onlyOmit 21 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.closed 49))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 30 (.closed 34)))
    (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 40 (.closed 38))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 41 (.split (.split (.split (.onlyOmit 41 (.closed 41))
    (.onlyOmit 35 (.closed 40)))
    (.onlyOmit 34 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 49 (.onlyOmit 41 (.onlyOmit 41 (.split (.onlyOmit 49 (.closed 49))
    (.onlyOmit 43 (.closed 49))))))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 42))))))))))))))))
    (.onlyOmit 27 (.closed 26)))))))))

private def cap5Part76 : Certificate := cap5Part76Block.toCertificate

private theorem cap5Part76_checked : check 5 60 17 66683 cap5Part76 = true :=
  checkFragment_sound cap5Part76Block 17 66683 (by decide +kernel)

private def cap5Part77Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 40 (.split (.split (.split (.onlyOmit 54 (.split (.split (.onlyInclude (.onlyOmit 48 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 62 (.onlyOmit 54 (.onlyOmit 54 (.closed 70)))))))))
    (.split (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 56 (.closed 54))))))
    (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 54 (.onlyOmit 54 (.closed 56))))))))))
    (.onlyOmit 46 (.closed 48))))
    (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.closed 54))))))))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 54 (.closed 54)))))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.split (.onlyOmit 54 (.onlyOmit 54 (.closed 54)))
    (.onlyOmit 48 (.onlyOmit 54 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 56 (.onlyOmit 54 (.onlyOmit 54 (.closed 56)))))))))))))))))
    (.split (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.closed 48))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 48 (.split (.closed 48)
    (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 56 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 56 (.onlyOmit 56 (.closed 61))))))))))))))))))))
    (.onlyOmit 38 (.closed 40)))
    (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 46 (.closed 46))))))))

private def cap5Part77 : Certificate := cap5Part77Block.toCertificate

private theorem cap5Part77_checked : check 5 60 36 2156037243 cap5Part77 = true :=
  checkFragment_sound cap5Part77Block 36 2156037243 (by decide +kernel)

private def cap5Part78Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.split (.split (.split (.graft 36 2156037243 cap5Part77 cap5Part77_checked)
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyInclude (.onlyOmit 46 (.closed 45))))))))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyInclude (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.split (.closed 65)
    (.onlyOmit 54 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 59 (.closed 57)))))))))))))))
    (.onlyOmit 46 (.closed 44))))))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.split (.split (.split (.closed 48)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.closed 64)))))))))
    (.onlyOmit 41 (.closed 43)))
    (.onlyOmit 40 (.onlyOmit 56 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 56 (.closed 48)))))))))))))))))
    (.split (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 61 (.onlyOmit 48 (.onlyOmit 48 (.closed 53))))))))))))))))))))
    (.onlyOmit 33 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.closed 38))))))))

private def cap5Part78 : Certificate := cap5Part78Block.toCertificate

private theorem cap5Part78_checked : check 5 60 28 8553595 cap5Part78 = true :=
  checkFragment_sound cap5Part78Block 28 8553595 (by decide +kernel)

private def cap5Part79Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.split (.onlyOmit 46 (.onlyOmit 46 (.closed 57)))
    (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.closed 54))))))))))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 50 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 50 (.closed 65)))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 35 (.onlyOmit 35 (.closed 39))))))))))))
    (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 38 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 42 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 49 (.onlyOmit 46 (.onlyOmit 46 (.closed 57))))))))))))))))))))))))
    (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.split (.onlyOmit 46 (.onlyOmit 46 (.closed 57)))
    (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.closed 54)))))))))))))))))))))))))))))

private def cap5Part79 : Certificate := cap5Part79Block.toCertificate

private theorem cap5Part79_checked : check 5 60 23 148603 cap5Part79 = true :=
  checkFragment_sound cap5Part79Block 23 148603 (by decide +kernel)

private def cap5Part80Block : Fragment 5 60 :=
  (.split (.split (.graft 23 148603 cap5Part79 cap5Part79_checked)
    (.onlyOmit 23 (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 51 (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 51)
    (.onlyOmit 51 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 51 (.onlyOmit 54 (.onlyOmit 51 (.onlyOmit 51 (.closed 66))))))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 47 (.closed 51)))))))))))))))))
    (.onlyOmit 32 (.closed 31)))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 39 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 39)
    (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 54 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 57 (.closed 54)))))))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 31 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 31 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.split (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.closed 50)))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 50)))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43))))))))))))))))))))

private def cap5Part80 : Certificate := cap5Part80Block.toCertificate

private theorem cap5Part80_checked : check 5 60 21 148603 cap5Part80 = true :=
  checkFragment_sound cap5Part80Block 21 148603 (by decide +kernel)

private def cap5Part81Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.split (.closed 24)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 43 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 43)
    (.onlyOmit 43 (.closed 39))))))))))
    (.onlyOmit 32 (.closed 31))))))))))
    (.onlyOmit 24 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.closed 38))))))))))
    (.onlyOmit 28 (.closed 30))))))))))
    (.onlyOmit 20 (.closed 24)))
    (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 39 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 51)))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 28 (.onlyOmit 28 (.closed 32))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.graft 21 148603 cap5Part80 cap5Part80_checked)))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.closed 26)))
    (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))
    (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.closed 34))))))))))))
    (.onlyOmit 22 (.closed 24))))))))

private def cap5Part81 : Certificate := cap5Part81Block.toCertificate

private theorem cap5Part81_checked : check 5 60 16 17531 cap5Part81 = true :=
  checkFragment_sound cap5Part81Block 16 17531 (by decide +kernel)

private def cap5Part82Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.closed 31)))
    (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.closed 39)))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 48 (.closed 48))
    (.onlyOmit 42 (.closed 48)))))))))))))))))
    (.onlyOmit 27 (.closed 31)))
    (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 38 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 45 (.closed 42)))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 42 (.closed 46))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 42 (.closed 46)))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 45 (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 45)
    (.onlyOmit 42 (.closed 45)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 31 (.closed 33)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 50 (.onlyOmit 42 (.onlyOmit 42 (.split (.onlyOmit 50 (.closed 50))
    (.onlyOmit 44 (.closed 50)))))))))
    (.onlyOmit 42 (.closed 39)))
    (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.split (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 58 (.closed 50))))))
    (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.closed 56)))))))))))))))))))))))
    (.onlyOmit 29 (.closed 31))))))))

private def cap5Part82 : Certificate := cap5Part82Block.toCertificate

private theorem cap5Part82_checked : check 5 60 23 2106491 cap5Part82 = true :=
  checkFragment_sound cap5Part82Block 23 2106491 (by decide +kernel)

private def cap5Part83Block : Fragment 5 60 :=
  (.split (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 31 (.closed 28)))
    (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.closed 42))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 45 (.onlyOmit 42 (.onlyOmit 42 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 56 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 53 (.onlyOmit 53 (.closed 56))))))))))))))))))))
    (.onlyOmit 37 (.closed 34)))
    (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.closed 42))))))))))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 42 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))
    (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 53 (.onlyOmit 42 (.onlyOmit 42 (.closed 53)))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.closed 36)))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.closed 50)))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 50 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 47 (.closed 47))))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.closed 50))))))))))))))))))))

private def cap5Part83 : Certificate := cap5Part83Block.toCertificate

private theorem cap5Part83_checked : check 5 60 21 271483 cap5Part83 = true :=
  checkFragment_sound cap5Part83Block 21 271483 (by decide +kernel)

private def cap5Part84Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.graft 23 2106491 cap5Part82 cap5Part82_checked)
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 42 (.closed 39))))))))))
    (.onlyOmit 32 (.closed 31))))))))))
    (.split (.closed 23)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 41))))))))
    (.onlyOmit 31 (.closed 30))))))))))
    (.onlyOmit 23 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 29 (.closed 31)))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 34 (.closed 40)))))))))
    (.onlyOmit 27 (.closed 29))))))))))
    (.onlyOmit 19 (.onlyOmit 23 (.graft 21 271483 cap5Part83 cap5Part83_checked))))
    (.onlyOmit 18 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 30 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 37 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 41)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 45))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 38))))))))))))))))

private def cap5Part84 : Certificate := cap5Part84Block.toCertificate

private theorem cap5Part84_checked : check 5 60 17 9339 cap5Part84 = true :=
  checkFragment_sound cap5Part84Block 17 9339 (by decide +kernel)

private def cap5Part85Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.graft 18 132219 cap5Part75 cap5Part75_checked))
    (.graft 17 66683 cap5Part76 cap5Part76_checked))
    (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.closed 27)))
    (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.graft 28 8553595 cap5Part78 cap5Part78_checked)))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 40 (.split (.split (.split (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 42 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 56 (.onlyOmit 48 (.onlyOmit 48 (.onlyInclude (.onlyOmit 50 (.onlyOmit 56 (.onlyOmit 56 (.onlyOmit 56 (.onlyOmit 58 (.onlyOmit 56 (.onlyOmit 56 (.closed 58)))))))))))))))))))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))))
    (.onlyOmit 32 (.onlyOmit 48 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 48 (.closed 40)))))))))))))))))
    (.onlyOmit 23 (.closed 25))))))))))
    (.onlyOmit 15 (.graft 16 17531 cap5Part81 cap5Part81_checked)))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.graft 17 9339 cap5Part84 cap5Part84_checked)))))
    (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.onlyInclude (.split (.closed 22)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 30 (.closed 29))))))))))
    (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 30 (.closed 28)))
    (.onlyOmit 28 (.closed 30)))
    (.onlyOmit 24 (.closed 28)))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))
    (.onlyOmit 18 (.closed 22))))))))

private def cap5Part85 : Certificate := cap5Part85Block.toCertificate

private theorem cap5Part85_checked : check 5 60 12 1147 cap5Part85 = true :=
  checkFragment_sound cap5Part85Block 12 1147 (by decide +kernel)

private def cap5Part86Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.graft 10 59 cap5Part47 cap5Part47_checked)
    (.graft 10 571 cap5Part48 cap5Part48_checked))
    (.onlyOmit 9 (.split (.split (.graft 12 315 cap5Part59 cap5Part59_checked)
    (.onlyOmit 12 (.graft 13 2363 cap5Part63 cap5Part63_checked)))
    (.onlyOmit 11 (.onlyOmit 13 (.onlyOmit 13 (.graft 14 1339 cap5Part65 cap5Part65_checked)))))))
    (.onlyOmit 8 (.graft 9 187 cap5Part73 cap5Part73_checked)))
    (.onlyOmit 7 (.onlyOmit 9 (.onlyOmit 9 (.split (.split (.graft 12 123 cap5Part74 cap5Part74_checked)
    (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 31 (.closed 33)))
    (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 26 (.closed 31)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))))))))
    (.onlyOmit 24 (.closed 24)))
    (.onlyOmit 19 (.closed 24))))))))
    (.onlyOmit 16 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 23 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 31 (.closed 30)))
    (.onlyOmit 27 (.closed 31))))))))))
    (.onlyOmit 23 (.closed 23))))))))))
    (.onlyOmit 11 (.graft 12 1147 cap5Part85 cap5Part85_checked)))))))

private def cap5Part86 : Certificate := cap5Part86Block.toCertificate

private theorem cap5Part86_checked : check 5 60 6 59 cap5Part86 = true :=
  checkFragment_sound cap5Part86Block 6 59 (by decide +kernel)

private def cap5Part87Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 8 27 cap5Part26 cap5Part26_checked)
    (.split (.onlyInclude (.onlyOmit 10 (.split (.graft 12 667 cap5Part28 cap5Part28_checked)
    (.onlyOmit 12 (.graft 13 2715 cap5Part29 cap5Part29_checked)))))
    (.graft 9 411 cap5Part40 cap5Part40_checked)))
    (.onlyOmit 7 (.split (.split (.graft 10 91 cap5Part45 cap5Part45_checked)
    (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.split (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 27)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 27))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.closed 24)))
    (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.closed 31)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 31))))))))
    (.onlyOmit 20 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))))))))))))
    (.onlyOmit 9 (.split (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 21 (.onlyOmit 19 (.onlyOmit 19 (.closed 21))))))))
    (.graft 13 4443 cap5Part46 cap5Part46_checked))
    (.onlyOmit 12 (.closed 14)))
    (.onlyOmit 11 (.split (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.closed 18)))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.closed 18))))))))))))
    (.graft 6 59 cap5Part86 cap5Part86_checked))

private def cap5Part87 : Certificate := cap5Part87Block.toCertificate

private theorem cap5Part87_checked : check 5 60 5 27 cap5Part87 = true :=
  checkFragment_sound cap5Part87Block 5 27 (by decide +kernel)

private def cap5Part88Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 24 (.split (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 22 (.closed 24))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 18 (.closed 18)))))
    (.onlyOmit 13 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.split (.closed 31)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 33))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))
    (.onlyOmit 22 (.onlyOmit 31 (.onlyOmit 29 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.closed 29))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.closed 26))))))))
    (.onlyOmit 18 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.closed 27))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.closed 20)))))
    (.onlyOmit 15 (.split (.onlyOmit 22 (.split (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 24 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))))))))

private def cap5Part88 : Certificate := cap5Part88Block.toCertificate

private theorem cap5Part88_checked : check 5 60 12 1319 cap5Part88 = true :=
  checkFragment_sound cap5Part88Block 12 1319 (by decide +kernel)

private def cap5Part89Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.closed 32))))
    (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 35)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 45 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 45 (.closed 42))))))))))))
    (.onlyOmit 26 (.onlyOmit 32 (.split (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.closed 29))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 35 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 35)))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 35))))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 22 (.onlyOmit 20 (.closed 20)))))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.closed 38))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))
    (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 36 (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 36)))))))))))
    (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyOmit 27 (.split (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 33)))))
    (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 33 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 30 (.closed 30))))))))))))))))))

private def cap5Part89 : Certificate := cap5Part89Block.toCertificate

private theorem cap5Part89_checked : check 5 60 12 679 cap5Part89 = true :=
  checkFragment_sound cap5Part89Block 12 679 (by decide +kernel)

private def cap5Part90Block : Fragment 5 60 :=
  (.split (.split (.graft 12 679 cap5Part89 cap5Part89_checked)
    (.onlyOmit 12 (.split (.onlyOmit 16 (.closed 16))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.closed 18)))))))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.closed 34)))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 33 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 33))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))))))
    (.onlyOmit 20 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 32 (.split (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))
    (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))
    (.onlyOmit 24 (.onlyOmit 32 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.closed 32))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 23))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.closed 29)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))))))))))))

private def cap5Part90 : Certificate := cap5Part90Block.toCertificate

private theorem cap5Part90_checked : check 5 60 10 679 cap5Part90 = true :=
  checkFragment_sound cap5Part90Block 10 679 (by decide +kernel)

private def cap5Part91Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.closed 25)))))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 27 (.split (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.closed 39)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))))))))
    (.onlyOmit 16 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.closed 26))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 47 (.onlyOmit 43 (.closed 43)))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31))))))))))
    (.onlyOmit 20 (.onlyOmit 26 (.split (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 34 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 23))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))))

private def cap5Part91 : Certificate := cap5Part91Block.toCertificate

private theorem cap5Part91_checked : check 5 60 15 2471 cap5Part91 = true :=
  checkFragment_sound cap5Part91Block 15 2471 (by decide +kernel)

private def cap5Part92Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.closed 46))))
    (.split (.onlyOmit 42 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 60 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 56)
    (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 52 (.closed 52)))))))))))))
    (.onlyOmit 40 (.onlyOmit 40 (.closed 42)))))
    (.onlyOmit 37 (.onlyOmit 38 (.closed 46)))))
    (.onlyOmit 35 (.split (.closed 42)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.closed 41)))))))
    (.onlyOmit 35 (.onlyOmit 35 (.closed 38))))
    (.onlyOmit 33 (.onlyOmit 42 (.onlyOmit 42 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 53 (.onlyOmit 46 (.closed 46))))))))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.split (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 56 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.split (.closed 52)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 48 (.closed 48)))))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.closed 38)))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 38)))))))
    (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.split (.split (.onlyOmit 46 (.split (.onlyOmit 46 (.onlyOmit 46 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.closed 50))))))
    (.onlyOmit 38 (.onlyOmit 39 (.closed 42)))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 42 (.closed 42)))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 42)))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 50 (.closed 46))))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 42 (.closed 42)))))))))))))

private def cap5Part92 : Certificate := cap5Part92Block.toCertificate

private theorem cap5Part92_checked : check 5 60 29 35784103 cap5Part92 = true :=
  checkFragment_sound cap5Part92Block 29 35784103 (by decide +kernel)

private def cap5Part93Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.split (.closed 38)
    (.onlyOmit 38 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 51))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.closed 37)))))))
    (.onlyOmit 29 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 33 (.split (.split (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 49 (.split (.closed 49)
    (.onlyOmit 42 (.onlyOmit 42 (.closed 45))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 42)))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyInclude (.onlyOmit 44 (.onlyOmit 45 (.closed 51)))))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.closed 35)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))
    (.onlyOmit 26 (.onlyOmit 27 (.split (.graft 29 35784103 cap5Part92 cap5Part92_checked)
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 31)))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 44 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 44)))))))))))))))))))))

private def cap5Part93 : Certificate := cap5Part93Block.toCertificate

private theorem cap5Part93_checked : check 5 60 23 2229671 cap5Part93 = true :=
  checkFragment_sound cap5Part93Block 23 2229671 (by decide +kernel)

private def cap5Part94Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))
    (.onlyOmit 29 (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 42 (.closed 40)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 27 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 39 (.closed 42))))
    (.onlyOmit 33 (.onlyOmit 33 (.closed 39))))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.closed 26))))
    (.onlyOmit 28 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 38 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 26 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 41 (.closed 41))))
    (.onlyOmit 32 (.onlyOmit 32 (.closed 40))))))))))))))))
    (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.graft 23 2229671 cap5Part93 cap5Part93_checked)))
    (.onlyOmit 22 (.onlyOmit 22 (.closed 25))))
    (.onlyOmit 27 (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 40 (.closed 38)))))))))))))))))

private def cap5Part94 : Certificate := cap5Part94Block.toCertificate

private theorem cap5Part94_checked : check 5 60 17 1447 cap5Part94 = true :=
  checkFragment_sound cap5Part94Block 17 1447 (by decide +kernel)

private def cap5Part95Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 13 (.onlyInclude (.onlyOmit 16 (.onlyOmit 16 (.closed 19)))))))
    (.split (.graft 12 1319 cap5Part88 cap5Part88_checked)
    (.onlyOmit 12 (.onlyOmit 13 (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.closed 19))))))))
    (.onlyOmit 10 (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 14 (.closed 17))))
    (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.closed 29)))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))))))))))))))
    (.split (.split (.split (.onlyInclude (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 34)))))
    (.onlyOmit 24 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.closed 26)))))))
    (.onlyOmit 18 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 25))))))))))
    (.split (.split (.onlyOmit 18 (.closed 18))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.closed 20)))))
    (.onlyOmit 15 (.onlyOmit 16 (.closed 18)))))))
    (.onlyOmit 12 (.onlyOmit 12 (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.closed 23)))))))))))))
    (.graft 10 679 cap5Part90 cap5Part90_checked))
    (.onlyOmit 9 (.split (.onlyInclude (.onlyOmit 12 (.onlyOmit 13 (.split (.graft 15 2471 cap5Part91 cap5Part91_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.closed 19)))))))
    (.onlyOmit 12 (.onlyOmit 12 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.graft 17 1447 cap5Part94 cap5Part94_checked)
    (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.closed 24))))))))))))))))

private def cap5Part95 : Certificate := cap5Part95Block.toCertificate

private theorem cap5Part95_checked : check 5 60 7 39 cap5Part95 = true :=
  checkFragment_sound cap5Part95Block 7 39 (by decide +kernel)

private def cap5Part96Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23)))))
    (.onlyOmit 23 (.split (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 34 (.closed 34)))))))))))))
    (.onlyOmit 17 (.split (.closed 21)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 33 (.closed 33))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 22 (.split (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 49 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.closed 49)))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))))))
    (.onlyOmit 31 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 33 (.onlyOmit 39 (.closed 37))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 39)))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 41 (.onlyOmit 41 (.closed 43)))
    (.onlyOmit 35 (.onlyOmit 41 (.closed 39))))))))))))))))))))))
    (.onlyOmit 16 (.split (.closed 20)
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 32 (.closed 29))))))))))))))

private def cap5Part96 : Certificate := cap5Part96Block.toCertificate

private theorem cap5Part96_checked : check 5 60 14 359 cap5Part96 = true :=
  checkFragment_sound cap5Part96Block 14 359 (by decide +kernel)

private def cap5Part97Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.graft 14 359 cap5Part96 cap5Part96_checked)
    (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 21 (.split (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 30 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 37)))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.closed 23)))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 32 (.closed 32)))))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.closed 20))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 19 (.closed 19))))))))
    (.onlyOmit 11 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 29))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 27))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.closed 24))))))))
    (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 27))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23)))))
    (.onlyOmit 18 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.closed 25))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 18 (.closed 18)))))
    (.onlyOmit 13 (.onlyOmit 14 (.split (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.closed 31))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))
    (.onlyOmit 22 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 29)))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.closed 20))))))))))

private def cap5Part97 : Certificate := cap5Part97Block.toCertificate

private theorem cap5Part97_checked : check 5 60 10 359 cap5Part97 = true :=
  checkFragment_sound cap5Part97Block 10 359 (by decide +kernel)

private def cap5Part98Block : Fragment 5 60 :=
  (.split (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.split (.closed 52)
    (.onlyOmit 52 (.onlyOmit 50 (.closed 50))))
    (.onlyOmit 42 (.onlyOmit 52 (.closed 50))))))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 52)))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))
    (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 51 (.closed 51))
    (.onlyOmit 51 (.onlyOmit 49 (.closed 49)))))))))))))
    (.onlyOmit 32 (.onlyOmit 39 (.closed 36)))))
    (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.closed 37)))))
    (.onlyOmit 37 (.split (.onlyOmit 40 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 50))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 50 (.onlyOmit 50 (.closed 52)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.closed 40)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.split (.onlyInclude (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 54)))))))))))))
    (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 34 (.onlyOmit 40 (.closed 38)))))
    (.onlyOmit 32 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 52)))))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))))))))))))

private def cap5Part98 : Certificate := cap5Part98Block.toCertificate

private theorem cap5Part98_checked : check 5 60 23 2622311 cap5Part98 = true :=
  checkFragment_sound cap5Part98Block 23 2622311 (by decide +kernel)

private def cap5Part99Block : Fragment 5 60 :=
  (.split (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 32 (.onlyOmit 38 (.closed 36)))))
    (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 49 (.closed 49))
    (.onlyOmit 40 (.onlyOmit 47 (.closed 47))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 49)))))))))))))
    (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 48 (.onlyInclude (.onlyOmit 48 (.onlyOmit 48 (.closed 46)))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.closed 38)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.closed 40))))
    (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 51)))))))))))))
    (.onlyOmit 31 (.onlyOmit 38 (.closed 38))))
    (.onlyOmit 30 (.onlyOmit 31 (.closed 38)))))))))))

private def cap5Part99 : Certificate := cap5Part99Block.toCertificate

private theorem cap5Part99_checked : check 5 60 22 1311591 cap5Part99 = true :=
  checkFragment_sound cap5Part99Block 22 1311591 (by decide +kernel)

private def cap5Part100Block : Fragment 5 60 :=
  (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.closed 48)))))))))))
    (.onlyOmit 37 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyOmit 48 (.onlyOmit 48 (.onlyInclude (.onlyOmit 48 (.onlyOmit 48 (.closed 46))))))
    (.onlyOmit 39 (.onlyOmit 40 (.closed 46))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 48 (.closed 48)))))))))))))
    (.onlyOmit 31 (.onlyOmit 38 (.closed 35)))))
    (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 30 (.onlyOmit 36 (.closed 34)))))
    (.onlyOmit 28 (.split (.closed 36)
    (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 46 (.onlyOmit 46 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.closed 44))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.closed 44))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 51)))))))))))))))))))))

private def cap5Part100 : Certificate := cap5Part100Block.toCertificate

private theorem cap5Part100_checked : check 5 60 22 656231 cap5Part100 = true :=
  checkFragment_sound cap5Part100Block 22 656231 (by decide +kernel)

private def cap5Part101Block : Fragment 5 60 :=
  (.split (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 46 (.closed 44)))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.closed 45)))))))))))
    (.onlyOmit 35 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 45 (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 45 (.onlyOmit 45 (.closed 43))))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 47 (.onlyOmit 45 (.onlyOmit 45 (.closed 47)))))))))))))
    (.onlyOmit 29 (.onlyOmit 36 (.closed 33)))))
    (.onlyOmit 27 (.onlyOmit 34 (.closed 34))))
    (.onlyOmit 26 (.onlyOmit 27 (.closed 34)))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.closed 37)))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.closed 38))))
    (.onlyOmit 38 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 47 (.onlyOmit 49 (.closed 47)))))))))))))
    (.onlyOmit 29 (.onlyOmit 36 (.closed 36))))
    (.onlyOmit 28 (.onlyOmit 29 (.closed 36)))))))))))

private def cap5Part101 : Certificate := cap5Part101Block.toCertificate

private theorem cap5Part101_checked : check 5 60 20 328551 cap5Part101 = true :=
  checkFragment_sound cap5Part101Block 20 328551 (by decide +kernel)

private def cap5Part102Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))
    (.onlyOmit 27 (.graft 23 2622311 cap5Part98 cap5Part98_checked)))
    (.onlyOmit 21 (.onlyOmit 28 (.closed 25)))))
    (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))
    (.onlyOmit 26 (.graft 22 1311591 cap5Part99 cap5Part99_checked)))
    (.onlyOmit 20 (.onlyOmit 27 (.closed 24)))))
    (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 25 (.split (.graft 22 656231 cap5Part100 cap5Part100_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 40 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 50 (.onlyOmit 50 (.closed 52)))))))))))))
    (.onlyOmit 36 (.onlyOmit 38 (.closed 38))))
    (.onlyOmit 30 (.split (.closed 38)
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 50)))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.closed 36)))))))))))))
    (.onlyOmit 19 (.onlyOmit 26 (.closed 23)))))
    (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 24 (.graft 20 328551 cap5Part101 cap5Part101_checked)))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.closed 24))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23))))))))

private def cap5Part102 : Certificate := cap5Part102Block.toCertificate

private theorem cap5Part102_checked : check 5 60 15 871 cap5Part102 = true :=
  checkFragment_sound cap5Part102Block 15 871 (by decide +kernel)

private def cap5Part103Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.split (.closed 29)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.closed 38)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 38 (.closed 33)))))))))))
    (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))))
    (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.split (.closed 28)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 37)))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.closed 24)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))))))))
    (.onlyOmit 16 (.onlyOmit 19 (.closed 19))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 40 (.split (.split (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 49 (.closed 44)))))))
    (.onlyOmit 36 (.onlyOmit 37 (.closed 39))))
    (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 46 (.onlyInclude (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 51 (.onlyOmit 55 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 51 (.closed 66)))))))))))
    (.onlyOmit 42 (.onlyOmit 55 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.closed 48))))))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.closed 44)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 40 (.closed 35)))))))
    (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 40))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))))))))

private def cap5Part103 : Certificate := cap5Part103Block.toCertificate

private theorem cap5Part103_checked : check 5 60 14 4503 cap5Part103 = true :=
  checkFragment_sound cap5Part103Block 14 4503 (by decide +kernel)

private def cap5Part104Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.closed 41)))))))
    (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))
    (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 40)))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.closed 30)))))))
    (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))))
    (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 30 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 39))))))))))))
    (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.split (.closed 25)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 35)))))))))))
    (.onlyOmit 17 (.onlyOmit 20 (.closed 20)))))))
    (.split (.graft 14 4503 cap5Part103 cap5Part103_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 20 (.split (.closed 20)
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 29))))))))))))))))
    (.onlyOmit 12 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 42 (.onlyOmit 37 (.closed 37)))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 32))))))
    (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 32)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.closed 45))))))))))))))
    (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 27)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 35 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 40 (.onlyOmit 35 (.closed 35))))))))))))))))))))))))

private def cap5Part104 : Certificate := cap5Part104Block.toCertificate

private theorem cap5Part104_checked : check 5 60 11 407 cap5Part104 = true :=
  checkFragment_sound cap5Part104Block 11 407 (by decide +kernel)

private def cap5Part105Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 29 (.split (.onlyOmit 29 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 28 (.split (.onlyOmit 28 (.split (.onlyOmit 28 (.closed 28))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.closed 31))))))))))))))
    (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 27 (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))
    (.onlyOmit 20 (.onlyOmit 27 (.split (.onlyOmit 27 (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 22))))))
    (.onlyOmit 17 (.onlyOmit 17 (.closed 19))))
    (.onlyOmit 15 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 31 (.closed 31)))))))))))
    (.onlyOmit 20 (.onlyOmit 25 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 22))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 25 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 22))))))))

private def cap5Part105 : Certificate := cap5Part105Block.toCertificate

private theorem cap5Part105_checked : check 5 60 14 2391 cap5Part105 = true :=
  checkFragment_sound cap5Part105Block 14 2391 (by decide +kernel)

private def cap5Part106Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 33))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.closed 21))))
    (.onlyOmit 17 (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 28 (.onlyOmit 28 (.closed 30))))))
    (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.split (.onlyInclude (.onlyOmit 41 (.onlyOmit 38 (.closed 38))))
    (.onlyOmit 49 (.onlyOmit 39 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 49 (.closed 59))))))))))))
    (.onlyOmit 33 (.onlyOmit 38 (.closed 39))))
    (.onlyOmit 32 (.onlyOmit 33 (.closed 38)))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))
    (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 39 (.closed 39))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.closed 31)))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 31))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))
    (.onlyOmit 16 (.onlyOmit 21 (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.split (.onlyOmit 29 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))))))
    (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 38 (.closed 38))))))))))
    (.onlyOmit 29 (.split (.closed 29)
    (.onlyOmit 26 (.onlyOmit 26 (.closed 28)))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))))))))))))

private def cap5Part106 : Certificate := cap5Part106Block.toCertificate

private theorem cap5Part106_checked : check 5 60 14 215 cap5Part106 = true :=
  checkFragment_sound cap5Part106Block 14 215 (by decide +kernel)

private def cap5Part107Block : Fragment 5 60 :=
  (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 47 (.closed 47)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.onlyOmit 46 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 46 (.closed 46)))))))))
    (.onlyOmit 38 (.onlyOmit 35 (.closed 35))))
    (.onlyOmit 31 (.onlyOmit 36 (.closed 37))))
    (.onlyOmit 30 (.onlyOmit 31 (.closed 36)))))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 36 (.onlyInclude (.onlyOmit 36 (.onlyOmit 35 (.closed 35)))))))))))))
    (.split (.onlyOmit 27 (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 53))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 35 (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.closed 34))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 39 (.closed 39)))))))))))))))))

private def cap5Part107 : Certificate := cap5Part107Block.toCertificate

private theorem cap5Part107_checked : check 5 60 17 24791 cap5Part107 = true :=
  checkFragment_sound cap5Part107Block 17 24791 (by decide +kernel)

private def cap5Part108Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 14 215 cap5Part106 cap5Part106_checked)
    (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 37)
    (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 45 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 45))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))))))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.closed 19))))
    (.onlyOmit 15 (.onlyOmit 20 (.graft 17 24791 cap5Part107 cap5Part107_checked)))))
    (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 27)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.closed 18))))))
    (.onlyOmit 13 (.onlyOmit 13 (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 43 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 43)))))))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 34 (.closed 34))))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 26 (.split (.closed 26)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 34 (.closed 30))))))))))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 33)))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 33)))))))))))))))))

private def cap5Part108 : Certificate := cap5Part108Block.toCertificate

private theorem cap5Part108_checked : check 5 60 11 215 cap5Part108 = true :=
  checkFragment_sound cap5Part108Block 11 215 (by decide +kernel)

private def cap5Part109Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 26))))))
    (.onlyOmit 21 (.onlyOmit 21 (.closed 23))))
    (.onlyOmit 19 (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))
    (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 44 (.closed 45))))
    (.onlyOmit 39 (.onlyOmit 39 (.closed 44)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.closed 33))))
    (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 44 (.onlyOmit 45 (.closed 44))))))))))))))
    (.onlyOmit 27 (.onlyOmit 35 (.closed 35))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 35 (.closed 38))))
    (.onlyOmit 30 (.onlyOmit 30 (.closed 35)))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.closed 25))))))
    (.onlyOmit 20 (.onlyOmit 20 (.closed 22))))
    (.onlyOmit 18 (.onlyOmit 23 (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 33 (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 36)))))))
    (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 44 (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 37 (.onlyOmit 44 (.closed 43)))))))))))))
    (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 30 (.onlyOmit 30 (.closed 32))))))
    (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 42 (.closed 45))))
    (.onlyOmit 37 (.onlyOmit 37 (.closed 42)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 26 (.closed 33)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 37 (.closed 37))))
    (.onlyOmit 29 (.onlyOmit 29 (.closed 36)))))))))))))))

private def cap5Part109 : Certificate := cap5Part109Block.toCertificate

private theorem cap5Part109_checked : check 5 60 16 727 cap5Part109 = true :=
  checkFragment_sound cap5Part109Block 16 727 (by decide +kernel)

private def cap5Part110Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.split (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 40 (.onlyOmit 40 (.closed 42)))))
    (.onlyOmit 37 (.onlyOmit 38 (.closed 40))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 50))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.closed 33))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 41 (.closed 41))))
    (.onlyOmit 38 (.onlyOmit 38 (.closed 45))))))))))))))
    (.onlyOmit 26 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 34 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 40)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 50 (.onlyOmit 44 (.closed 44))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 44 (.split (.closed 44)
    (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.closed 28))))
    (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.split (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 54 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 50))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.closed 37))))))
    (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))
    (.onlyOmit 30 (.onlyOmit 38 (.onlyOmit 38 (.split (.onlyOmit 38 (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.split (.closed 42)
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 54 (.onlyOmit 48 (.closed 48))))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 42 (.closed 42)))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 42))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 42 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 46)))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))

private def cap5Part110 : Certificate := cap5Part110Block.toCertificate

private theorem cap5Part110_checked : check 5 60 23 557783 cap5Part110 = true :=
  checkFragment_sound cap5Part110Block 23 557783 (by decide +kernel)

private def cap5Part111Block : Fragment 5 60 :=
  (.split (.split (.graft 11 215 cap5Part108 cap5Part108_checked)
    (.onlyOmit 11 (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 25)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyOmit 24 (.closed 24))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))))))
    (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.closed 24)))))))))
    (.onlyOmit 14 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.closed 16))))))
    (.onlyOmit 10 (.onlyOmit 11 (.onlyOmit 13 (.onlyOmit 13 (.split (.split (.graft 16 727 cap5Part109 cap5Part109_checked)
    (.onlyOmit 16 (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 24))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.graft 23 557783 cap5Part110 cap5Part110_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 28)))))))))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 24))))))
    (.onlyOmit 19 (.onlyOmit 19 (.closed 21))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.closed 23))))))))))))))

private def cap5Part111 : Certificate := cap5Part111Block.toCertificate

private theorem cap5Part111_checked : check 5 60 9 215 cap5Part111 = true :=
  checkFragment_sound cap5Part111Block 9 215 (by decide +kernel)

private def cap5Part112Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 11 (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 17 (.closed 17))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.closed 19)))))))))
    (.onlyOmit 11 (.onlyOmit 11 (.onlyInclude (.onlyOmit 13 (.onlyOmit 16 (.closed 16)))))))
    (.onlyOmit 9 (.split (.graft 11 407 cap5Part104 cap5Part104_checked)
    (.onlyOmit 11 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.closed 23))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.closed 28))))
    (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 41 (.closed 36))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 40 (.closed 35))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.closed 25))))))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 10 (.split (.split (.split (.onlyInclude (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 23 (.split (.onlyOmit 23 (.closed 23))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.closed 20))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 22 (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))))))))))
    (.onlyOmit 13 (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 21 (.closed 21))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 28 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28)))))))))))
    (.onlyOmit 16 (.onlyOmit 21 (.split (.onlyOmit 21 (.closed 21))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.closed 18))))))
    (.onlyOmit 13 (.onlyOmit 13 (.closed 15))))))
    (.onlyOmit 10 (.onlyOmit 10 (.onlyInclude (.onlyOmit 12 (.split (.graft 14 2391 cap5Part105 cap5Part105_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.closed 19)))))))))))
    (.onlyOmit 8 (.graft 9 215 cap5Part111 cap5Part111_checked))))

private def cap5Part112 : Certificate := cap5Part112Block.toCertificate

private theorem cap5Part112_checked : check 5 60 6 23 cap5Part112 = true :=
  checkFragment_sound cap5Part112Block 6 23 (by decide +kernel)

private def cap5Part113Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 38))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.closed 32)
    (.onlyOmit 32 (.onlyOmit 30 (.closed 30))))
    (.onlyOmit 26 (.onlyOmit 32 (.closed 30))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.closed 31))))
    (.onlyOmit 31 (.onlyOmit 39 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 44))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))))))
    (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))
    (.onlyOmit 25 (.onlyOmit 26 (.closed 29)))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 31 (.onlyOmit 29 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.closed 29)))))))))))
    (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 24))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 30)))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.closed 29)))))))))))))

private def cap5Part113 : Certificate := cap5Part113Block.toCertificate

private theorem cap5Part113_checked : check 5 60 16 10295 cap5Part113 = true :=
  checkFragment_sound cap5Part113Block 16 10295 (by decide +kernel)

private def cap5Part114Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 25))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.graft 16 10295 cap5Part113 cap5Part113_checked))))
    (.onlyOmit 13 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 23 (.split (.closed 23)
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 38)
    (.onlyOmit 37 (.onlyOmit 38 (.closed 37))))))))))
    (.onlyOmit 30 (.onlyOmit 29 (.closed 29))))
    (.onlyOmit 25 (.split (.closed 29)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 44 (.closed 38))))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 37 (.closed 37))))))))
    (.onlyOmit 37 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.closed 37)))))))))
    (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))
    (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 29 (.onlyOmit 28 (.closed 28)))))))))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 29 (.closed 29))))))))))))))

private def cap5Part114 : Certificate := cap5Part114Block.toCertificate

private theorem cap5Part114_checked : check 5 60 12 2103 cap5Part114 = true :=
  checkFragment_sound cap5Part114Block 12 2103 (by decide +kernel)

private def cap5Part115Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.onlyOmit 22 (.closed 22))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 35 (.closed 35))))))))))
    (.onlyOmit 29 (.onlyOmit 28 (.closed 28))))))))))
    (.onlyOmit 22 (.split (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 47))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 24 (.onlyOmit 27 (.closed 27))))))))))
    (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 44)
    (.onlyOmit 44 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 57)))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.closed 28))))
    (.onlyOmit 24 (.onlyOmit 35 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 35)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 52 (.closed 48)))))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 41 (.onlyOmit 41 (.closed 43))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 43)))))))))))))))))))))))

private def cap5Part115 : Certificate := cap5Part115Block.toCertificate

private theorem cap5Part115_checked : check 5 60 16 5175 cap5Part115 = true :=
  checkFragment_sound cap5Part115Block 16 5175 (by decide +kernel)

private def cap5Part116Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.closed 27))))
    (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.closed 33))))
    (.split (.split (.split (.onlyOmit 36 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 48 (.closed 42))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 42 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 39))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36))))))))
    (.onlyOmit 27 (.onlyOmit 30 (.closed 30))))
    (.onlyOmit 26 (.onlyOmit 27 (.closed 30))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 39))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 44 (.onlyOmit 38 (.closed 38)))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 43 (.closed 37)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 24 (.closed 24))))
    (.onlyOmit 20 (.onlyOmit 21 (.closed 24))))

private def cap5Part116 : Certificate := cap5Part116Block.toCertificate

private theorem cap5Part116_checked : check 5 60 19 37431 cap5Part116 = true :=
  checkFragment_sound cap5Part116Block 19 37431 (by decide +kernel)

private def cap5Part117Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 42)))))))))))))))
    (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40))))))))))))))
    (.onlyOmit 22 (.split (.closed 26)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.closed 34))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 36)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 35)))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))
    (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 46 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.closed 54))))))))))))))))))))))))))))))))

private def cap5Part117 : Certificate := cap5Part117Block.toCertificate

private theorem cap5Part117_checked : check 5 60 18 133687 cap5Part117 = true :=
  checkFragment_sound cap5Part117Block 18 133687 (by decide +kernel)

private def cap5Part118Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.graft 18 133687 cap5Part117 cap5Part117_checked))
    (.split (.onlyOmit 20 (.closed 20))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40)))))))))))))
    (.onlyOmit 27 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 33 (.closed 33))))))))))))))
    (.onlyOmit 16 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 48))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 36 (.closed 36))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 44))))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.closed 28))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 40)))))))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.split (.closed 31)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 39 (.closed 39))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.closed 25))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 31 (.closed 31))))))))))))))

private def cap5Part118 : Certificate := cap5Part118Block.toCertificate

private theorem cap5Part118_checked : check 5 60 14 2615 cap5Part118 = true :=
  checkFragment_sound cap5Part118Block 14 2615 (by decide +kernel)

private def cap5Part119Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 32 (.onlyOmit 31 (.closed 31)))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.closed 39))))))))))))))
    (.onlyOmit 26 (.onlyOmit 25 (.closed 25))))
    (.onlyOmit 21 (.split (.closed 25)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.closed 35))))
    (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 38 (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 45 (.onlyOmit 45 (.closed 51))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 51 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.closed 41))))))))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 28 (.onlyOmit 29 (.closed 31))))))))))))

private def cap5Part119 : Certificate := cap5Part119Block.toCertificate

private theorem cap5Part119_checked : check 5 60 19 67127 cap5Part119 = true :=
  checkFragment_sound cap5Part119Block 19 67127 (by decide +kernel)

private def cap5Part120Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.graft 19 67127 cap5Part119 cap5Part119_checked)
    (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 39)))))))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 45)))))))))))))
    (.onlyOmit 38 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 51))))))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.closed 25)))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 26 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 33 (.closed 33))))))))))))))
    (.split (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.closed 48)))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.closed 36))))))))
    (.onlyOmit 31 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.closed 43))))))))))))))
    (.onlyOmit 25 (.onlyOmit 24 (.closed 24)))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 25 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.closed 38))))))))))))))))))))

private def cap5Part120 : Certificate := cap5Part120Block.toCertificate

private theorem cap5Part120_checked : check 5 60 15 1591 cap5Part120 = true :=
  checkFragment_sound cap5Part120Block 15 1591 (by decide +kernel)

private def cap5Part121Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.graft 12 2103 cap5Part114 cap5Part114_checked))
    (.split (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.closed 23))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.graft 16 5175 cap5Part115 cap5Part115_checked)
    (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.closed 22))))))))))
    (.onlyOmit 12 (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.split (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 27 (.closed 27))))
    (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 41)))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.closed 46))))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 28 (.closed 28))))))))
    (.onlyOmit 21 (.split (.closed 21)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 34)))))))
    (.onlyOmit 28 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.closed 26))))))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.graft 19 37431 cap5Part116 cap5Part116_checked)
    (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyOmit 27 (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 39 (.onlyOmit 39 (.split (.closed 39)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 45))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 33 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 30)))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.graft 14 2615 cap5Part118 cap5Part118_checked))))
    (.onlyOmit 11 (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 14 (.graft 15 1591 cap5Part120 cap5Part120_checked)))))))

private def cap5Part121 : Certificate := cap5Part121Block.toCertificate

private theorem cap5Part121_checked : check 5 60 9 55 cap5Part121 = true :=
  checkFragment_sound cap5Part121Block 9 55 (by decide +kernel)

private def cap5Part122Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.closed 27))))
    (.onlyOmit 27 (.split (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 39))))))))))))))
    (.onlyOmit 22 (.onlyOmit 25 (.closed 25))))
    (.onlyOmit 21 (.onlyOmit 22 (.closed 25))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.closed 24)))))))
    (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.closed 25))))
    (.onlyOmit 25 (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 35))))))))))))))
    (.onlyOmit 20 (.onlyOmit 23 (.closed 23))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 23))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 32))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 37))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 31)))))))))))))

private def cap5Part122 : Certificate := cap5Part122Block.toCertificate

private theorem cap5Part122_checked : check 5 60 15 1335 cap5Part122 = true :=
  checkFragment_sound cap5Part122Block 15 1335 (by decide +kernel)

private def cap5Part123Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.closed 19))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 43 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 49 (.closed 49))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.closed 43))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))))))))))
    (.onlyOmit 14 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 34 (.closed 34))))
    (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 34 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 29 (.onlyOmit 34 (.closed 33)))))))))))
    (.onlyOmit 25 (.split (.closed 25)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))))
    (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 41)))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.closed 31)))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 31 (.closed 31))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 25)))))))))

private def cap5Part123 : Certificate := cap5Part123Block.toCertificate

private theorem cap5Part123_checked : check 5 60 13 4279 cap5Part123 = true :=
  checkFragment_sound cap5Part123Block 13 4279 (by decide +kernel)

private def cap5Part124Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.closed 24))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 36))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 44)))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.closed 30))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 43 (.split (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 51 (.onlyOmit 56 (.closed 51)))))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 56 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 48 (.closed 56))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 48 (.onlyOmit 53 (.onlyOmit 48 (.onlyOmit 48 (.split (.closed 48)
    (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 53 (.onlyOmit 61 (.closed 53)))))))))))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 48 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 43))))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 43 (.closed 35))))))))))))))))))

private def cap5Part124 : Certificate := cap5Part124Block.toCertificate

private theorem cap5Part124_checked : check 5 60 16 2231 cap5Part124 = true :=
  checkFragment_sound cap5Part124Block 16 2231 (by decide +kernel)

private def cap5Part125Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 16 2231 cap5Part124 cap5Part124_checked)
    (.onlyOmit 16 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.split (.closed 26)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.closed 34))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 43 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 43)))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 34 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.closed 22))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.split (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.closed 18))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 32 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 32)))))))))))))))

private def cap5Part125 : Certificate := cap5Part125Block.toCertificate

private theorem cap5Part125_checked : check 5 60 13 2231 cap5Part125 = true :=
  checkFragment_sound cap5Part125Block 13 2231 (by decide +kernel)

private def cap5Part126Block : Fragment 5 60 :=
  (.split (.split (.graft 9 55 cap5Part121 cap5Part121_checked)
    (.onlyOmit 9 (.split (.onlyInclude (.onlyOmit 12 (.onlyOmit 13 (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.closed 19)))))))
    (.onlyOmit 12 (.onlyOmit 12 (.split (.split (.graft 15 1335 cap5Part122 cap5Part122_checked)
    (.onlyOmit 15 (.onlyOmit 18 (.closed 18))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.closed 23)))))))))))))))
    (.onlyOmit 9 (.onlyOmit 9 (.split (.split (.split (.onlyInclude (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.closed 20))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 28 (.closed 28))))))))))
    (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.split (.closed 27)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 37 (.closed 35))))))))))))
    (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))
    (.onlyOmit 31 (.onlyOmit 31 (.closed 34)))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 36 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 34 (.onlyOmit 35 (.closed 34))))))))))))
    (.onlyOmit 21 (.onlyOmit 27 (.closed 27))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))))))))
    (.graft 13 4279 cap5Part123 cap5Part123_checked))
    (.onlyOmit 12 (.graft 13 2231 cap5Part125 cap5Part125_checked)))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.closed 17))))))))))

private def cap5Part126 : Certificate := cap5Part126Block.toCertificate

private theorem cap5Part126_checked : check 5 60 7 55 cap5Part126 = true :=
  checkFragment_sound cap5Part126Block 7 55 (by decide +kernel)

private def cap5Part127Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 33 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 33)))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.closed 25))))))
    (.onlyOmit 18 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 40 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.closed 37)))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 37)))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 21 (.split (.split (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 37 (.onlyOmit 34 (.onlyOmit 31 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 31)))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 33 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))))))))

private def cap5Part127 : Certificate := cap5Part127Block.toCertificate

private theorem cap5Part127_checked : check 5 60 17 18575 cap5Part127 = true :=
  checkFragment_sound cap5Part127Block 17 18575 (by decide +kernel)

private def cap5Part128Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 26)))))))))
    (.split (.split (.graft 17 18575 cap5Part127 cap5Part127_checked)
    (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 27)))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 30 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 33 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 33))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 26))))))))))
    (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 24)))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 20 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 35)))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 35)))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 32))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26)))))))))))

private def cap5Part128 : Certificate := cap5Part128Block.toCertificate

private theorem cap5Part128_checked : check 5 60 13 2191 cap5Part128 = true :=
  checkFragment_sound cap5Part128Block 13 2191 (by decide +kernel)

private def cap5Part129Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 40 (.split (.split (.closed 40)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 54))))))))))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 49 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 40)))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 31 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 46)))))))))))))))))
    (.onlyOmit 17 (.split (.split (.onlyOmit 23 (.closed 23))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.closed 26))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 23 (.closed 23)))))))
    (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 34 (.split (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 28 (.onlyOmit 25 (.onlyOmit 25 (.closed 25))))))))))

private def cap5Part129 : Certificate := cap5Part129Block.toCertificate

private theorem cap5Part129_checked : check 5 60 15 9359 cap5Part129 = true :=
  checkFragment_sound cap5Part129Block 15 9359 (by decide +kernel)

private def cap5Part130Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))))))
    (.split (.split (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.closed 25)))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 32)))))))))))))))))
    (.split (.graft 15 9359 cap5Part129 cap5Part129_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 40)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32))))))))))))))))))
    (.onlyOmit 13 (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.split (.closed 28)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 32)))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.closed 36)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 44 (.closed 36))))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyOmit 22 (.onlyOmit 22 (.closed 22)))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 25)))))))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))))))))))))

private def cap5Part130 : Certificate := cap5Part130Block.toCertificate

private theorem cap5Part130_checked : check 5 60 12 1167 cap5Part130 = true :=
  checkFragment_sound cap5Part130Block 12 1167 (by decide +kernel)

private def cap5Part131Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 38)))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 37))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 46 (.closed 38))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 42)))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 29)))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 46)))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 36 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 44 (.onlyOmit 36 (.closed 36)))))))))))))))))))

private def cap5Part131 : Certificate := cap5Part131Block.toCertificate

private theorem cap5Part131_checked : check 5 60 16 4751 cap5Part131 = true :=
  checkFragment_sound cap5Part131Block 16 4751 (by decide +kernel)

private def cap5Part132Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 16 4751 cap5Part131 cap5Part131_checked)
    (.onlyOmit 16 (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 35)))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 38)))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 30))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 27)))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyOmit 21 (.onlyOmit 21 (.closed 21)))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.closed 30)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 33))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))))))))))))))

private def cap5Part132 : Certificate := cap5Part132Block.toCertificate

private theorem cap5Part132_checked : check 5 60 13 4751 cap5Part132 = true :=
  checkFragment_sound cap5Part132Block 13 4751 (by decide +kernel)

private def cap5Part133Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.closed 44))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 41)))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.closed 41)))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 38)))))
    (.onlyOmit 31 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 41 (.closed 44))))))
    (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 36)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 43 (.onlyOmit 40 (.onlyOmit 43 (.split (.onlyOmit 43 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 40))))))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 41)))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 31)))))))))

private def cap5Part133 : Certificate := cap5Part133Block.toCertificate

private theorem cap5Part133_checked : check 5 60 22 150159 cap5Part133 = true :=
  checkFragment_sound cap5Part133Block 22 150159 (by decide +kernel)

private def cap5Part134Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.graft 13 2191 cap5Part128 cap5Part128_checked)
    (.onlyOmit 13 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.closed 23)))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))))))))))))))
    (.split (.graft 12 1167 cap5Part130 cap5Part130_checked)
    (.onlyOmit 12 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 26)))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 21 (.closed 21))))))))))
    (.onlyOmit 10 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))))))))))))))
    (.graft 13 4751 cap5Part132 cap5Part132_checked))
    (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 43))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 33 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.graft 22 150159 cap5Part133 cap5Part133_checked)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.closed 20)))))))))

private def cap5Part134 : Certificate := cap5Part134Block.toCertificate

private theorem cap5Part134_checked : check 5 60 9 143 cap5Part134 = true :=
  checkFragment_sound cap5Part134Block 9 143 (by decide +kernel)

private def cap5Part135Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 28 (.split (.split (.split (.onlyOmit 28 (.closed 28))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 28))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.closed 27))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 31))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.closed 26))))))))))
    (.onlyOmit 15 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 31 (.closed 31))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.closed 25))))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 28))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))))))))))))

private def cap5Part135 : Certificate := cap5Part135Block.toCertificate

private theorem cap5Part135_checked : check 5 60 14 2447 cap5Part135 = true :=
  checkFragment_sound cap5Part135Block 14 2447 (by decide +kernel)

private def cap5Part136Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.closed 29)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 28)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32))))))))))))))))))
    (.split (.split (.graft 14 2447 cap5Part135 cap5Part135_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 41)))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 41 (.split (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 27)))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 19 (.closed 19)))))))

private def cap5Part136 : Certificate := cap5Part136Block.toCertificate

private theorem cap5Part136_checked : check 5 60 11 399 cap5Part136 = true :=
  checkFragment_sound cap5Part136Block 11 399 (by decide +kernel)

private def cap5Part137Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.closed 27)))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.split (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 50 (.onlyOmit 58 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.closed 58))))))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 37))))))
    (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 55))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 50)))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 35)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 45)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 37))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 30)))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 29 (.split (.split (.closed 29)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 22 (.closed 22))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 25)))))))))

private def cap5Part137 : Certificate := cap5Part137Block.toCertificate

private theorem cap5Part137_checked : check 5 60 15 5199 cap5Part137 = true :=
  checkFragment_sound cap5Part137Block 15 5199 (by decide +kernel)

private def cap5Part138Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 44 (.split (.onlyOmit 44 (.split (.split (.closed 44)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 44)))))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.split (.closed 44)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 56 (.onlyOmit 52 (.onlyOmit 56 (.onlyOmit 64 (.onlyOmit 52 (.closed 52))))))))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 52 (.onlyOmit 48 (.onlyOmit 44 (.onlyOmit 48 (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 48))))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 25)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))))))

private def cap5Part138 : Certificate := cap5Part138Block.toCertificate

private theorem cap5Part138_checked : check 5 60 15 2639 cap5Part138 = true :=
  checkFragment_sound cap5Part138Block 15 2639 (by decide +kernel)

private def cap5Part139Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 30 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.closed 26))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.closed 22))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 36 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 32)))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 45)))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 36 (.split (.split (.onlyOmit 36 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 40 (.onlyOmit 44 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 29))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 25))))))))))))
    (.onlyOmit 12 (.split (.split (.graft 15 2639 cap5Part138 cap5Part138_checked)
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.closed 20))))))
    (.onlyOmit 14 (.onlyOmit 15 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 34 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 34)))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 33))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 33 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 32 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))))))))

private def cap5Part139 : Certificate := cap5Part139Block.toCertificate

private theorem cap5Part139_checked : check 5 60 11 591 cap5Part139 = true :=
  checkFragment_sound cap5Part139Block 11 591 (by decide +kernel)

private def cap5Part140Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 31 (.closed 31)))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 34 (.split (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 49 (.closed 49))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 34))))))))))))
    (.onlyOmit 20 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36)))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 39))))))))))))
    (.onlyOmit 25 (.split (.onlyOmit 33 (.split (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 43 (.onlyOmit 38 (.closed 38))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 33))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 35))))))))))))))

private def cap5Part140 : Certificate := cap5Part140Block.toCertificate

private theorem cap5Part140_checked : check 5 60 19 17999 cap5Part140 = true :=
  checkFragment_sound cap5Part140Block 19 17999 (by decide +kernel)

private def cap5Part141Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 27))))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 23 (.closed 23)))))))))
    (.onlyOmit 13 (.split (.graft 15 5199 cap5Part137 cap5Part137_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 27))))))))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24))))))))))))))
    (.split (.graft 11 591 cap5Part139 cap5Part139_checked)
    (.onlyOmit 11 (.onlyOmit 12 (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.graft 19 17999 cap5Part140 cap5Part140_checked)
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.closed 23))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.closed 19)))))))))

private def cap5Part141 : Certificate := cap5Part141Block.toCertificate

private theorem cap5Part141_checked : check 5 60 9 79 cap5Part141 = true :=
  checkFragment_sound cap5Part141Block 9 79 (by decide +kernel)

private def cap5Part142Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.closed 30)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 39))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 48 (.closed 44))))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 34)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 38))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 38 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 38 (.closed 38))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 34))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 30))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.closed 33)
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 54 (.closed 42)))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 37)))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36)))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.closed 37)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.closed 44)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 44 (.split (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 33))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))))))

private def cap5Part142 : Certificate := cap5Part142Block.toCertificate

private theorem cap5Part142_checked : check 5 60 16 8527 cap5Part142 = true :=
  checkFragment_sound cap5Part142Block 16 8527 (by decide +kernel)

private def cap5Part143Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 14 (.split (.graft 16 8527 cap5Part142 cap5Part142_checked)
    (.onlyOmit 16 (.split (.onlyOmit 21 (.onlyOmit 21 (.closed 21)))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.closed 23))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.closed 29)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 33))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 37 (.closed 33))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.closed 28)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 32))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 28))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 35 (.onlyOmit 31 (.onlyOmit 31 (.closed 31))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 31)))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 31))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 27)))))))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.closed 34)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 33)))))))))))))))))

private def cap5Part143 : Certificate := cap5Part143Block.toCertificate

private theorem cap5Part143_checked : check 5 60 11 335 cap5Part143 = true :=
  checkFragment_sound cap5Part143Block 11 335 (by decide +kernel)

private def cap5Part144Block : Fragment 5 60 :=
  (.split (.split (.graft 9 79 cap5Part141 cap5Part141_checked)
    (.onlyOmit 9 (.split (.graft 11 335 cap5Part143 cap5Part143_checked)
    (.onlyOmit 11 (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 33))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 23 (.onlyOmit 23 (.closed 23))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 18 (.onlyOmit 18 (.closed 18))))))))))
    (.onlyOmit 8 (.onlyOmit 9 (.split (.onlyInclude (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 26)))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 25 (.closed 25)))))))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 25)))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.closed 25)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.closed 24))))))))))))))))

private def cap5Part144 : Certificate := cap5Part144Block.toCertificate

private theorem cap5Part144_checked : check 5 60 7 79 cap5Part144 = true :=
  checkFragment_sound cap5Part144Block 7 79 (by decide +kernel)

private def cap5Part145Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 48 (.closed 47))))))))))))))))))
    (.onlyOmit 36 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 47 (.closed 41)))))))))))))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))))
    (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 46))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.closed 30)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))))))))
    (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 27)))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 39 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 50 (.closed 44))))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 50 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 50))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 36 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 48 (.closed 47))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 47 (.closed 41)))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))))))

private def cap5Part145 : Certificate := cap5Part145Block.toCertificate

private theorem cap5Part145_checked : check 5 60 18 34351 cap5Part145 = true :=
  checkFragment_sound cap5Part145Block 18 34351 (by decide +kernel)

private def cap5Part146Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 38 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.closed 50))))))))
    (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))))
    (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 49)))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 38 (.closed 37))))))))
    (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))))))))
    (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyOmit 37 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 43 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 49 (.closed 48))))))))))))))
    (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.closed 31)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 43)))))))))))))
    (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))))))))
    (.split (.split (.graft 18 34351 cap5Part145 cap5Part145_checked)
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 49 (.closed 43))))))))
    (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 49))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 25 (.split (.closed 25)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 37 (.closed 36)))))))))))))))))))

private def cap5Part146 : Certificate := cap5Part146Block.toCertificate

private theorem cap5Part146_checked : check 5 60 15 1583 cap5Part146 = true :=
  checkFragment_sound cap5Part146Block 15 1583 (by decide +kernel)

private def cap5Part147Block : Fragment 5 60 :=
  (.split (.split (.graft 15 1583 cap5Part146 cap5Part146_checked)
    (.onlyOmit 15 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 46 (.onlyOmit 46 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 52 (.onlyOmit 46 (.closed 46)))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))
    (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 46 (.closed 56)))))))))))))))))
    (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 34)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 44 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 50 (.onlyOmit 44 (.closed 44)))))))))))))))))))))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 38 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.closed 50))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 49)))))))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 31)))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyOmit 37 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 43 (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 49 (.closed 48))))))))))))))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.closed 25))))))))))))

private def cap5Part147 : Certificate := cap5Part147Block.toCertificate

private theorem cap5Part147_checked : check 5 60 13 1583 cap5Part147 = true :=
  checkFragment_sound cap5Part147Block 13 1583 (by decide +kernel)

private def cap5Part148Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.split (.onlyOmit 30 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.split (.onlyOmit 29 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 33 (.closed 33))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 29)))))))))))
    (.onlyOmit 17 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 37 (.onlyOmit 33 (.closed 33)))))))))))
    (.onlyOmit 21 (.split (.onlyOmit 28 (.split (.onlyOmit 28 (.closed 28))
    (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.closed 28)))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))))))

private def cap5Part148 : Certificate := cap5Part148Block.toCertificate

private theorem cap5Part148_checked : check 5 60 16 4399 cap5Part148 = true :=
  checkFragment_sound cap5Part148Block 16 4399 (by decide +kernel)

private def cap5Part149Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 35 (.split (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 35)))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))))))))))
    (.onlyOmit 20 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.onlyOmit 43 (.split (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 39 (.closed 39))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.closed 34)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 34)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 30)))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.closed 26)))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 32)))))))))))

private def cap5Part149 : Certificate := cap5Part149Block.toCertificate

private theorem cap5Part149_checked : check 5 60 17 35119 cap5Part149 = true :=
  checkFragment_sound cap5Part149Block 17 35119 (by decide +kernel)

private def cap5Part150Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 35 (.split (.split (.onlyOmit 35 (.split (.closed 35)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 39))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 34 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 44 (.closed 44)))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 34 (.split (.split (.onlyOmit 34 (.split (.closed 34)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.closed 38))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))
    (.onlyOmit 19 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 43 (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 38 (.onlyOmit 42 (.closed 38))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyOmit 32 (.split (.closed 32)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))))))))

private def cap5Part150 : Certificate := cap5Part150Block.toCertificate

private theorem cap5Part150_checked : check 5 60 18 17711 cap5Part150 = true :=
  checkFragment_sound cap5Part150Block 18 17711 (by decide +kernel)

private def cap5Part151Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 34)))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 54 (.closed 44))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.onlyOmit 43 (.closed 43)))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 33 (.split (.closed 33)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 43 (.closed 38))))))))))))
    (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42)))))))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 42)))))))))))))))))))))

private def cap5Part151 : Certificate := cap5Part151Block.toCertificate

private theorem cap5Part151_checked : check 5 60 14 815 cap5Part151 = true :=
  checkFragment_sound cap5Part151Block 14 815 (by decide +kernel)

private def cap5Part152Block : Fragment 5 60 :=
  (.split (.split (.graft 14 815 cap5Part151 cap5Part151_checked)
    (.onlyOmit 14 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 37)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))))))
    (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 31)))))))))))
    (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 28)))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 27 (.closed 27))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 30)))))))))))))))))

private def cap5Part152 : Certificate := cap5Part152Block.toCertificate

private theorem cap5Part152_checked : check 5 60 12 815 cap5Part152 = true :=
  checkFragment_sound cap5Part152Block 12 815 (by decide +kernel)

private def cap5Part153Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.split (.onlyInclude (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 24)))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 21 (.onlyOmit 21 (.closed 21)))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.closed 27)))))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.onlyInclude (.onlyOmit 16 (.onlyOmit 20 (.onlyOmit 20 (.closed 20)))))))))
    (.onlyOmit 11 (.onlyOmit 12 (.graft 13 1583 cap5Part147 cap5Part147_checked)))))
    (.split (.split (.split (.onlyInclude (.onlyOmit 13 (.split (.split (.graft 16 4399 cap5Part148 cap5Part148_checked)
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 20 (.closed 20)))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))))))))))
    (.onlyOmit 13 (.onlyOmit 13 (.split (.onlyInclude (.onlyOmit 16 (.graft 17 35119 cap5Part149 cap5Part149_checked)))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 19 (.closed 19))))))))
    (.onlyOmit 11 (.onlyOmit 13 (.onlyOmit 13 (.onlyInclude (.onlyOmit 15 (.split (.split (.graft 18 17711 cap5Part150 cap5Part150_checked)
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))))))))))))))))))
    (.onlyOmit 10 (.onlyOmit 11 (.graft 12 815 cap5Part152 cap5Part152_checked)))))

private def cap5Part153 : Certificate := cap5Part153Block.toCertificate

private theorem cap5Part153_checked : check 5 60 8 47 cap5Part153 = true :=
  checkFragment_sound cap5Part153Block 8 47 (by decide +kernel)

private def cap5Part154Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 23 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.split (.onlyOmit 38 (.split (.onlyOmit 38 (.onlyInclude (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 44 (.closed 50))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 38))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 35)))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.split (.split (.onlyOmit 56 (.split (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.closed 48)))))
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 52 (.onlyOmit 56 (.onlyOmit 52 (.onlyOmit 64 (.onlyOmit 52 (.onlyOmit 52 (.closed 52))))))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 46))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 44)))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 64 (.onlyOmit 48 (.onlyOmit 60 (.onlyOmit 48 (.onlyOmit 48 (.closed 48))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 29)))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 44 (.split (.split (.closed 44)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 44 (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 52 (.onlyOmit 56 (.onlyOmit 52 (.onlyOmit 64 (.closed 52))))))))))))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 38)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 52 (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 44 (.split (.closed 44)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 48 (.closed 48)))))))))))))))))))))))))))

private def cap5Part154 : Certificate := cap5Part154Block.toCertificate

private theorem cap5Part154_checked : check 5 60 20 66735 cap5Part154 = true :=
  checkFragment_sound cap5Part154Block 20 66735 (by decide +kernel)

private def cap5Part155Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 17 (.split (.split (.graft 20 66735 cap5Part154 cap5Part154_checked)
    (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.closed 23)))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))))))
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32)))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 32 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 26)))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23)))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyOmit 23 (.onlyOmit 23 (.closed 23)))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))))))

private def cap5Part155 : Certificate := cap5Part155Block.toCertificate

private theorem cap5Part155_checked : check 5 60 13 1199 cap5Part155 = true :=
  checkFragment_sound cap5Part155Block 13 1199 (by decide +kernel)

private def cap5Part156Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 12 (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.closed 30)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 33 (.split (.onlyOmit 33 (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 33)))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 31)))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 31)))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.closed 18)))))))
    (.onlyOmit 12 (.onlyOmit 12 (.graft 13 1199 cap5Part155 cap5Part155_checked))))
    (.onlyOmit 10 (.onlyOmit 12 (.onlyOmit 12 (.onlyInclude (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 22)))))))))))))

private def cap5Part156 : Certificate := cap5Part156Block.toCertificate

private theorem cap5Part156_checked : check 5 60 9 175 cap5Part156 = true :=
  checkFragment_sound cap5Part156Block 9 175 (by decide +kernel)

private def cap5Part157Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 28 (.split (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 35 (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 44))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.closed 37)
    (.onlyOmit 37 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))
    (.onlyOmit 30 (.onlyOmit 37 (.onlyOmit 35 (.closed 35))))))))))))
    (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.closed 34)))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))
    (.onlyOmit 36 (.onlyOmit 45 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.closed 51)))))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34)))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 36 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))))

private def cap5Part157 : Certificate := cap5Part157Block.toCertificate

private theorem cap5Part157_checked : check 5 60 21 41071 cap5Part157 = true :=
  checkFragment_sound cap5Part157Block 21 41071 (by decide +kernel)

private def cap5Part158Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 30))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 29))))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.graft 21 41071 cap5Part157 cap5Part157_checked)
    (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 44))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 35)))))
    (.onlyOmit 30 (.onlyOmit 44 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 44)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 33))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 35))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))))))))

private def cap5Part158 : Certificate := cap5Part158Block.toCertificate

private theorem cap5Part158_checked : check 5 60 15 8303 cap5Part158 = true :=
  checkFragment_sound cap5Part158Block 15 8303 (by decide +kernel)

private def cap5Part159Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 37)))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.split (.split (.split (.onlyOmit 44 (.closed 44))
    (.onlyOmit 38 (.onlyOmit 44 (.onlyOmit 43 (.closed 43)))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.split (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.closed 50)))))
    (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 50 (.onlyOmit 60 (.closed 50))))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 44)))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 54 (.closed 44))))))))))))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 49 (.onlyOmit 49 (.onlyInclude (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 65 (.closed 65)))))))))))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 59 (.closed 49))))))))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.closed 43)))))))))
    (.onlyOmit 43 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.onlyOmit 43 (.closed 43))
    (.onlyOmit 37 (.onlyOmit 43 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 49)))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 43 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 49 (.split (.onlyOmit 49 (.closed 49))
    (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 58 (.closed 59))))))))))))))))))))))))))
    (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 33)))))))))

private def cap5Part159 : Certificate := cap5Part159Block.toCertificate

private theorem cap5Part159_checked : check 5 60 23 1073263 cap5Part159 = true :=
  checkFragment_sound cap5Part159Block 23 1073263 (by decide +kernel)

private def cap5Part160Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.closed 70)))))))))
    (.split (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 54 (.closed 54))))))
    (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 54 (.onlyOmit 54 (.closed 58))))))))))
    (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 50 (.closed 50)))))
    (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 50 (.closed 50)))))
    (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 62)))))))))
    (.split (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 50 (.closed 50))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 50 (.split (.closed 50)
    (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.closed 58))))))))))))))))))
    (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.closed 42)))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 54)))))))))
    (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34)))))

private def cap5Part160 : Certificate := cap5Part160Block.toCertificate

private theorem cap5Part160_checked : check 5 60 29 8949871 cap5Part160 = true :=
  checkFragment_sound cap5Part160Block 29 8949871 (by decide +kernel)

private def cap5Part161Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.closed 32)))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 45)))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 36 (.onlyOmit 44 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 28))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 18 (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.graft 29 8949871 cap5Part160 cap5Part160_checked)
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 34)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 42 (.split (.split (.split (.split (.split (.closed 42)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyInclude (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 58 (.onlyOmit 58 (.onlyOmit 58 (.onlyOmit 58 (.closed 62)))))))))))))))))))))))))
    (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 50 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 50 (.onlyOmit 42 (.closed 42))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 38 (.closed 38)))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 27))))))))))))

private def cap5Part161 : Certificate := cap5Part161Block.toCertificate

private theorem cap5Part161_checked : check 5 60 15 4207 cap5Part161 = true :=
  checkFragment_sound cap5Part161Block 15 4207 (by decide +kernel)

private def cap5Part162Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.closed 61)))))))))))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 41 (.onlyOmit 41 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 51)
    (.onlyOmit 51 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 51 (.onlyOmit 51 (.closed 66))))))))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 41 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.closed 41)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 61 (.closed 56))))))))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.split (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 48 (.onlyOmit 48 (.closed 50)))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 50))))))))))))))))))))))))

private def cap5Part162 : Certificate := cap5Part162Block.toCertificate

private theorem cap5Part162_checked : check 5 60 21 544879 cap5Part162 = true :=
  checkFragment_sound cap5Part162Block 21 544879 (by decide +kernel)

private def cap5Part163Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))))))))))
    (.onlyOmit 26 (.split (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 41 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 47 (.closed 55)))))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))))))
    (.onlyOmit 20 (.graft 21 544879 cap5Part162 cap5Part162_checked)))
    (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 40))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 26))))))))

private def cap5Part163 : Certificate := cap5Part163Block.toCertificate

private theorem cap5Part163_checked : check 5 60 18 20591 cap5Part163 = true :=
  checkFragment_sound cap5Part163Block 18 20591 (by decide +kernel)

private def cap5Part164Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.graft 15 8303 cap5Part158 cap5Part158_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 27 (.split (.onlyOmit 27 (.closed 27))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.closed 44)
    (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))
    (.onlyOmit 29 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 51 (.closed 44))))))))))))))))))
    (.split (.split (.graft 23 1073263 cap5Part159 cap5Part159_checked)
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 42 (.closed 42)))))))))
    (.onlyOmit 34 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 34 (.closed 34)))))))))))))))))
    (.split (.split (.graft 15 4207 cap5Part161 cap5Part161_checked)
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.graft 18 20591 cap5Part163 cap5Part163_checked)))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.split (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))))
    (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 48))))))))
    (.onlyOmit 40 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 46 (.closed 54)))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 25 (.split (.onlyOmit 25 (.closed 25))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 40))))))))
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))))))))))))))))))

private def cap5Part164 : Certificate := cap5Part164Block.toCertificate

private theorem cap5Part164_checked : check 5 60 12 111 cap5Part164 = true :=
  checkFragment_sound cap5Part164Block 12 111 (by decide +kernel)

private def cap5Part165Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 26 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.split (.split (.split (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 40 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 50 (.onlyOmit 50 (.closed 57))))))))))
    (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.closed 47)))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 47 (.onlyOmit 47 (.closed 47)))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 40)))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 43))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 36)))))
    (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 40 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 54 (.onlyOmit 47 (.closed 47))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 40)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 47 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 52)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))

private def cap5Part165 : Certificate := cap5Part165Block.toCertificate

private theorem cap5Part165_checked : check 5 60 24 297071 cap5Part165 = true :=
  checkFragment_sound cap5Part165Block 24 297071 (by decide +kernel)

private def cap5Part166Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 51 (.closed 51))))))))
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 47 (.closed 47)))))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 33)))))
    (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 41 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.closed 41)))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.closed 37))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.graft 24 297071 cap5Part165 cap5Part165_checked)
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29)))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 47 (.onlyInclude (.onlyOmit 44 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 51 (.onlyOmit 51 (.closed 51))))))))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 37)))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 40 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))))))))))))

private def cap5Part166 : Certificate := cap5Part166Block.toCertificate

private theorem cap5Part166_checked : check 5 60 18 34927 cap5Part166 = true :=
  checkFragment_sound cap5Part166Block 18 34927 (by decide +kernel)

private def cap5Part167Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))
    (.split (.split (.split (.split (.onlyOmit 43 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 57 (.closed 50)))))))))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 43 (.onlyOmit 43 (.closed 43)))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.closed 50)))))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))))))
    (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 36)))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 39)))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 39 (.onlyOmit 39 (.onlyInclude (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 46 (.closed 46))))))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 46 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 43)))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 45 (.onlyOmit 52 (.closed 45)))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 38)))))))))))

private def cap5Part167 : Certificate := cap5Part167Block.toCertificate

private theorem cap5Part167_checked : check 5 60 27 33835119 cap5Part167 = true :=
  checkFragment_sound cap5Part167Block 27 33835119 (by decide +kernel)

private def cap5Part168Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 32)))))
    (.split (.graft 27 33835119 cap5Part167 cap5Part167_checked)
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 51 (.closed 44)))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.split (.split (.split (.onlyOmit 42 (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 49 (.onlyOmit 49 (.split (.closed 49)
    (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 56 (.onlyOmit 56 (.split (.closed 56)
    (.onlyOmit 55 (.onlyOmit 55 (.onlyOmit 55 (.onlyOmit 56 (.onlyOmit 63 (.onlyOmit 63 (.onlyOmit 83 (.closed 63)))))))))))))))))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 42)))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.closed 49)))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.closed 42))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32)))))))))

private def cap5Part168 : Certificate := cap5Part168Block.toCertificate

private theorem cap5Part168_checked : check 5 60 22 280687 cap5Part168 = true :=
  checkFragment_sound cap5Part168Block 22 280687 (by decide +kernel)

private def cap5Part169Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.split (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 47))))))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 49)))))))))))))))))
    (.split (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 47))))))))))))))))
    (.onlyOmit 26 (.split (.onlyOmit 31 (.closed 31))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 47)))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 33)))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 47))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 47)))))))))))))))))))

private def cap5Part169 : Certificate := cap5Part169Block.toCertificate

private theorem cap5Part169_checked : check 5 60 23 1058927 cap5Part169 = true :=
  checkFragment_sound cap5Part169Block 23 1058927 (by decide +kernel)

private def cap5Part170Block : Fragment 5 60 :=
  (.split (.onlyInclude (.split (.split (.graft 23 1058927 cap5Part169 cap5Part169_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 42))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 41))))))))
    (.onlyOmit 33 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))
    (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 47 (.onlyOmit 47 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 54 (.onlyInclude (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 55 (.onlyOmit 56 (.closed 63))))))))))))))))))))))))))))))))))))))
    (.split (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 40 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 47)))))))))))))))
    (.onlyOmit 32 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 39 (.closed 39))))))))))))))))

private def cap5Part170 : Certificate := cap5Part170Block.toCertificate

private theorem cap5Part170_checked : check 5 60 19 10351 cap5Part170 = true :=
  checkFragment_sound cap5Part170Block 19 10351 (by decide +kernel)

private def cap5Part171Block : Fragment 5 60 :=
  (.split (.split (.graft 19 10351 cap5Part170 cap5Part170_checked)
    (.onlyOmit 19 (.split (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 38 (.split (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.closed 57))))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 45 (.onlyOmit 43 (.closed 43))))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 52)))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 47))))))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 40)))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 47)))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 37 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.closed 46))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 37 (.closed 37))))))))))))))))

private def cap5Part171 : Certificate := cap5Part171Block.toCertificate

private theorem cap5Part171_checked : check 5 60 17 10351 cap5Part171 = true :=
  checkFragment_sound cap5Part171Block 17 10351 (by decide +kernel)

private def cap5Part172Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 45 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 45))))))))
    (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 38 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 45 (.closed 46))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))
    (.onlyOmit 25 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 45))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 51)))))))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 42)))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.split (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 54 (.closed 54))))))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 46)))))))))
    (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.closed 46))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 50 (.onlyOmit 42 (.closed 42)))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 46 (.closed 46))))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 45))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 37))))))))))))))

private def cap5Part172 : Certificate := cap5Part172Block.toCertificate

private theorem cap5Part172_checked : check 5 60 23 530543 cap5Part172 = true :=
  checkFragment_sound cap5Part172Block 23 530543 (by decide +kernel)

private def cap5Part173Block : Fragment 5 60 :=
  (.split (.split (.graft 23 530543 cap5Part172 cap5Part172_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 41)))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 45 (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 53 (.closed 60)))))))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.closed 45)))))))))
    (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 45))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.closed 37)))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 40 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 46)))))))))))))))
    (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.closed 53)))))))))))))))
    (.onlyOmit 45 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.onlyOmit 45 (.onlyInclude (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.onlyInclude (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 53 (.onlyOmit 54 (.closed 60))))))))))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.closed 30)))))))))

private def cap5Part173 : Certificate := cap5Part173Block.toCertificate

private theorem cap5Part173_checked : check 5 60 21 530543 cap5Part173 = true :=
  checkFragment_sound cap5Part173Block 21 530543 (by decide +kernel)

private def cap5Part174Block : Fragment 5 60 :=
  (.onlyOmit 14 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.split (.graft 21 530543 cap5Part173 cap5Part173_checked)
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 31 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 39 (.closed 39))))))))))))))))
    (.split (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 43 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 50 (.closed 57)))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.closed 43)))))))))
    (.onlyOmit 37 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 37 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.closed 51))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 30 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 37 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 44 (.closed 45)))))))))))))))))))))))))))

private def cap5Part174 : Certificate := cap5Part174Block.toCertificate

private theorem cap5Part174_checked : check 5 60 14 6255 cap5Part174 = true :=
  checkFragment_sound cap5Part174Block 14 6255 (by decide +kernel)

private def cap5Part175Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29)))))))))
    (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 30)))))
    (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 42))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.closed 28)))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30)))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 38))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 45 (.closed 45))))))))
    (.onlyOmit 38 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 44))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 37)))))))))))))))

private def cap5Part175 : Certificate := cap5Part175Block.toCertificate

private theorem cap5Part175_checked : check 5 60 18 5231 cap5Part175 = true :=
  checkFragment_sound cap5Part175Block 18 5231 (by decide +kernel)

private def cap5Part176Block : Fragment 5 60 :=
  (.split (.split (.graft 12 111 cap5Part164 cap5Part164_checked)
    (.split (.split (.split (.onlyInclude (.onlyOmit 16 (.onlyOmit 17 (.graft 18 34927 cap5Part166 cap5Part166_checked))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.split (.graft 22 280687 cap5Part168 cap5Part168_checked)
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 39 (.onlyOmit 39 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 46 (.split (.closed 46)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.closed 53)))))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 39 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 39))))))))))))))))))))
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.graft 17 10351 cap5Part171 cap5Part171_checked)))))
    (.onlyOmit 13 (.graft 14 6255 cap5Part174 cap5Part174_checked))))
    (.onlyOmit 11 (.split (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 24 (.closed 24)))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.closed 27))))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 23 (.closed 23)))))))))
    (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.graft 18 5231 cap5Part175 cap5Part175_checked)
    (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 28))))))))))))))))))

private def cap5Part176 : Certificate := cap5Part176Block.toCertificate

private theorem cap5Part176_checked : check 5 60 10 111 cap5Part176 = true :=
  checkFragment_sound cap5Part176Block 10 111 (by decide +kernel)

private def cap5Part177Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 43))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 51 (.onlyOmit 47 (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 47 (.closed 47)))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 27 (.split (.split (.split (.onlyOmit 40 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 40)))))))
    (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 48 (.onlyOmit 44 (.onlyOmit 40 (.closed 40))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 39))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 47 (.onlyOmit 43 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 43 (.closed 43)))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42))))))))))))))

private def cap5Part177 : Certificate := cap5Part177Block.toCertificate

private theorem cap5Part177_checked : check 5 60 25 4473375 cap5Part177 = true :=
  checkFragment_sound cap5Part177Block 25 4473375 (by decide +kernel)

private def cap5Part178Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 23 (.split (.graft 25 4473375 cap5Part177 cap5Part177_checked)
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 35))))))
    (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyOmit 39 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 43 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 43))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 39))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.closed 42))))))))))))))))))))

private def cap5Part178 : Certificate := cap5Part178Block.toCertificate

private theorem cap5Part178_checked : check 5 60 21 279071 cap5Part178 = true :=
  checkFragment_sound cap5Part178Block 21 279071 (by decide +kernel)

private def cap5Part179Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 41)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 26 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.split (.closed 46)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 57 (.split (.onlyOmit 46 (.closed 46))
    (.onlyOmit 42 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.closed 50))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 45)))))))))))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.closed 39)))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 46 (.split (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.closed 42))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 42)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 53 (.onlyOmit 46 (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 41)))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.closed 38)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42)))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 41))))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 41)))))))))

private def cap5Part179 : Certificate := cap5Part179Block.toCertificate

private theorem cap5Part179_checked : check 5 60 24 2245151 cap5Part179 = true :=
  checkFragment_sound cap5Part179Block 24 2245151 (by decide +kernel)

private def cap5Part180Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))
    (.split (.split (.graft 21 279071 cap5Part178 cap5Part178_checked)
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 34))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 38 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 38)))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyOmit 38 (.closed 38))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33))))))))))))
    (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 31))))))
    (.onlyOmit 23 (.onlyOmit 23 (.graft 24 2245151 cap5Part179 cap5Part179_checked))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 34))))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 44))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 41 (.closed 41))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 41)))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))))

private def cap5Part180 : Certificate := cap5Part180Block.toCertificate

private theorem cap5Part180_checked : check 5 60 17 16927 cap5Part180 = true :=
  checkFragment_sound cap5Part180Block 17 16927 (by decide +kernel)

private def cap5Part181Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40))))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 25 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 44)))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 44))))))
    (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.closed 38)))))))
    (.onlyOmit 29 (.onlyOmit 30 (.split (.split (.split (.split (.closed 44)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 48))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.closed 42)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyOmit 52 (.closed 48))
    (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.closed 44))))))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 44 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 40))))))))

private def cap5Part181 : Certificate := cap5Part181Block.toCertificate

private theorem cap5Part181_checked : check 5 60 24 1131039 cap5Part181 = true :=
  checkFragment_sound cap5Part181Block 24 1131039 (by decide +kernel)

private def cap5Part182Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.closed 51)))))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 40 (.onlyOmit 36 (.closed 36)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.closed 59)))))))))))))))))))))
    (.onlyOmit 22 (.split (.split (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 45))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 48 (.onlyOmit 44 (.closed 44)))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 50))))))
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 65 (.closed 55))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 37 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 37))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))))))))))))

private def cap5Part182 : Certificate := cap5Part182Block.toCertificate

private theorem cap5Part182_checked : check 5 60 20 139807 cap5Part182 = true :=
  checkFragment_sound cap5Part182Block 20 139807 (by decide +kernel)

private def cap5Part183Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.split (.split (.split (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))))))))))))
    (.split (.split (.graft 20 139807 cap5Part182 cap5Part182_checked)
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 48 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.closed 48)))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 36 (.onlyOmit 32 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 41))))))))))))))))))))))

private def cap5Part183 : Certificate := cap5Part183Block.toCertificate

private theorem cap5Part183_checked : check 5 60 17 8735 cap5Part183 = true :=
  checkFragment_sound cap5Part183Block 17 8735 (by decide +kernel)

private def cap5Part184Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.split (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 65 (.closed 54)))))))
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.split (.split (.closed 54)
    (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 54 (.onlyOmit 54 (.closed 59)))))))
    (.onlyOmit 49 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 52 (.closed 54)))))))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.split (.onlyOmit 59 (.closed 48))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.closed 51))))))))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.split (.split (.closed 48)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.closed 53)))))))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.closed 48))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 44)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 57))))))))))))))))

private def cap5Part184 : Certificate := cap5Part184Block.toCertificate

private theorem cap5Part184_checked : check 5 60 26 2171423 cap5Part184 = true :=
  checkFragment_sound cap5Part184Block 26 2171423 (by decide +kernel)

private def cap5Part185Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.graft 26 2171423 cap5Part184 cap5Part184_checked))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))
    (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 33)))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 43 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 43))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))))))))))))

private def cap5Part185 : Certificate := cap5Part185Block.toCertificate

private theorem cap5Part185_checked : check 5 60 18 74271 cap5Part185 = true :=
  checkFragment_sound cap5Part185Block 18 74271 (by decide +kernel)

private def cap5Part186Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 17 8735 cap5Part183 cap5Part183_checked)
    (.onlyOmit 17 (.graft 18 74271 cap5Part185 cap5Part185_checked)))
    (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 40))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.closed 45)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 55 (.closed 45))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyOmit 28 (.closed 28))
    (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 41))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.closed 41)))))))))))))))))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 27 (.closed 27)))))))))))

private def cap5Part186 : Certificate := cap5Part186Block.toCertificate

private theorem cap5Part186_checked : check 5 60 14 8735 cap5Part186 = true :=
  checkFragment_sound cap5Part186Block 14 8735 (by decide +kernel)

private def cap5Part187Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 49 (.split (.split (.closed 49)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.split (.onlyOmit 49 (.closed 49))
    (.onlyOmit 45 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.closed 66))))))))))))
    (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.split (.onlyOmit 60 (.onlyOmit 49 (.closed 49)))
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.closed 49))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.closed 49)))))))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 38 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 42)))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 38))))))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 38 (.closed 38)))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 57)))))))))))))))))))))

private def cap5Part187 : Certificate := cap5Part187Block.toCertificate

private theorem cap5Part187_checked : check 5 60 21 70175 cap5Part187 = true :=
  checkFragment_sound cap5Part187Block 21 70175 (by decide +kernel)

private def cap5Part188Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 57 (.onlyOmit 46 (.onlyOmit 46 (.closed 46))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.split (.onlyOmit 67 (.onlyOmit 57 (.onlyInclude (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 53 (.closed 57))))))))
    (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 67 (.onlyOmit 72 (.onlyOmit 57 (.closed 57))))))))))))))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyOmit 46 (.split (.split (.closed 46)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 42 (.closed 42))))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 42 (.closed 42))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.split (.split (.split (.closed 55)
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 51 (.closed 51)))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 50 (.onlyOmit 50 (.closed 50))))))))
    (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 65 (.onlyOmit 55 (.split (.closed 60)
    (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 55 (.closed 55)))))))))))))))))))))))))))))

private def cap5Part188 : Certificate := cap5Part188Block.toCertificate

private theorem cap5Part188_checked : check 5 60 25 1118751 cap5Part188 = true :=
  checkFragment_sound cap5Part188Block 25 1118751 (by decide +kernel)

private def cap5Part189Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 21 70175 cap5Part187 cap5Part187_checked)
    (.onlyOmit 21 (.split (.split (.split (.graft 25 1118751 cap5Part188 cap5Part188_checked)
    (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 42 (.split (.split (.closed 42)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 38))))))
    (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.split (.split (.split (.closed 41)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.closed 45)))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 41))))))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.closed 41)))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 45 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 61)))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 38)))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))))))))))

private def cap5Part189 : Certificate := cap5Part189Block.toCertificate

private theorem cap5Part189_checked : check 5 60 18 70175 cap5Part189 = true :=
  checkFragment_sound cap5Part189Block 18 70175 (by decide +kernel)

private def cap5Part190Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 45)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 55 (.closed 45))))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 44)))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 43 (.closed 43)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 42)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.closed 42)))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 34 (.split (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 34))))))))))))))

private def cap5Part190 : Certificate := cap5Part190Block.toCertificate

private theorem cap5Part190_checked : check 5 60 19 37407 cap5Part190 = true :=
  checkFragment_sound cap5Part190Block 19 37407 (by decide +kernel)

private def cap5Part191Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))))))))))))))))
    (.split (.graft 18 70175 cap5Part189 cap5Part189_checked)
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.split (.closed 39)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 49))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39))))))))))))))))))))))
    (.onlyOmit 16 (.split (.split (.graft 19 37407 cap5Part190 cap5Part190_checked)
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.closed 27)
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 40)))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 37))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 39))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.closed 39))))))))))))))))))))))))

private def cap5Part191 : Certificate := cap5Part191Block.toCertificate

private theorem cap5Part191_checked : check 5 60 15 4639 cap5Part191 = true :=
  checkFragment_sound cap5Part191Block 15 4639 (by decide +kernel)

private def cap5Part192Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.split (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.closed 56)))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 43 (.closed 43))))))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 43))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43)))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 39))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 43 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 47 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 37)))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.split (.split (.split (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.closed 51)))))))
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 47 (.closed 47))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 47))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 47 (.closed 47)))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 43))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 51 (.onlyOmit 47 (.closed 51)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.closed 36))))))))))))

private def cap5Part192 : Certificate := cap5Part192Block.toCertificate

private theorem cap5Part192_checked : check 5 60 22 283167 cap5Part192 = true :=
  checkFragment_sound cap5Part192Block 22 283167 (by decide +kernel)

private def cap5Part193Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.split (.graft 17 16927 cap5Part180 cap5Part180_checked)
    (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 30))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.graft 24 1131039 cap5Part181 cap5Part181_checked)))))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 33))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.closed 29))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))))))))))))))))
    (.graft 14 8735 cap5Part186 cap5Part186_checked))
    (.onlyOmit 13 (.split (.graft 15 4639 cap5Part191 cap5Part191_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 39))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.closed 43))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.graft 22 283167 cap5Part192 cap5Part192_checked)))))
    (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.closed 26)))))))))))

private def cap5Part193 : Certificate := cap5Part193Block.toCertificate

private theorem cap5Part193_checked : check 5 60 12 543 cap5Part193 = true :=
  checkFragment_sound cap5Part193Block 12 543 (by decide +kernel)

private def cap5Part194Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 46)))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 47))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 46 (.closed 46)))))))
    (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 57 (.closed 47))
    (.onlyOmit 42 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.closed 52)))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 36 (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 57)))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40)))))))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyOmit 45 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.closed 45)))))))
    (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 55 (.onlyOmit 45 (.closed 45)))))))))))))))))))))))

private def cap5Part194 : Certificate := cap5Part194Block.toCertificate

private theorem cap5Part194_checked : check 5 60 20 35359 cap5Part194 = true :=
  checkFragment_sound cap5Part194Block 20 35359 (by decide +kernel)

private def cap5Part195Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 44)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 65)))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 44 (.closed 44)))))))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 43 (.closed 43))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 38)))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))))))

private def cap5Part195 : Certificate := cap5Part195Block.toCertificate

private theorem cap5Part195_checked : check 5 60 21 559647 cap5Part195 = true :=
  checkFragment_sound cap5Part195Block 21 559647 (by decide +kernel)

private def cap5Part196Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyInclude (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 46)))))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.closed 43)))))))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.split (.split (.closed 51)
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 48 (.closed 48)))))))
    (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 61 (.split (.closed 56)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 51 (.closed 51))))))))))))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 37)))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 43)))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 39)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 46)))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 47))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 46 (.closed 46)))))))
    (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 57 (.closed 47))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.closed 52)))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 40)))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 36)))))))))))))))

private def cap5Part196 : Certificate := cap5Part196Block.toCertificate

private theorem cap5Part196_checked : check 5 60 21 297503 cap5Part196 = true :=
  checkFragment_sound cap5Part196Block 21 297503 (by decide +kernel)

private def cap5Part197Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 44 (.onlyOmit 44 (.closed 44))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 48 (.onlyOmit 52 (.onlyOmit 48 (.split (.onlyOmit 52 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 48 (.closed 48)))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 48 (.closed 48)))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.split (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 50 (.closed 50)))))))
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 62 (.split (.split (.onlyInclude (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 56 (.closed 56)))))))
    (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 62 (.onlyOmit 74 (.closed 62))))))))
    (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 54 (.onlyOmit 54 (.onlyOmit 54 (.closed 54))))))))))))))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.closed 48)))))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 52 (.split (.onlyOmit 56 (.split (.onlyOmit 56 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.closed 52)))))
    (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.closed 52)))))))
    (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 52 (.onlyOmit 52 (.closed 52))))))))))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42)))))))))))

private def cap5Part197 : Certificate := cap5Part197Block.toCertificate

private theorem cap5Part197_checked : check 5 60 28 4475423 cap5Part197 = true :=
  checkFragment_sound cap5Part197Block 28 4475423 (by decide +kernel)

private def cap5Part198Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.closed 67)))))))
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.closed 48)))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 54 (.split (.split (.closed 54)
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 60 (.split (.onlyOmit 66 (.closed 60))
    (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 51 (.closed 54)))))))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.closed 50)))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 48 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 48 (.closed 48)))))))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.closed 42)))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.graft 28 4475423 cap5Part197 cap5Part197_checked)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyOmit 40 (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 48 (.onlyOmit 44 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))))))))))))

private def cap5Part198 : Certificate := cap5Part198Block.toCertificate

private theorem cap5Part198_checked : check 5 60 22 281119 cap5Part198 = true :=
  checkFragment_sound cap5Part198Block 22 281119 (by decide +kernel)

private def cap5Part199Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 52)))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 37))))))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.closed 50)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 44)))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.closed 41)))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 31))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 48)))))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 38)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))))))))

private def cap5Part199 : Certificate := cap5Part199Block.toCertificate

private theorem cap5Part199_checked : check 5 60 21 150047 cap5Part199 = true :=
  checkFragment_sound cap5Part199Block 21 150047 (by decide +kernel)

private def cap5Part200Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))))))))))))))
    (.split (.split (.split (.split (.graft 20 35359 cap5Part194 cap5Part194_checked)
    (.onlyOmit 20 (.graft 21 559647 cap5Part195 cap5Part195_checked)))
    (.onlyOmit 19 (.onlyOmit 20 (.graft 21 297503 cap5Part196 cap5Part196_checked))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyOmit 26 (.closed 26))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 37))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.closed 37)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))
    (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 42))))))))))))))))))))))))
    (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.graft 22 281119 cap5Part198 cap5Part198_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.graft 21 150047 cap5Part199 cap5Part199_checked)))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.closed 25))))))))

private def cap5Part200 : Certificate := cap5Part200Block.toCertificate

private theorem cap5Part200_checked : check 5 60 14 2591 cap5Part200 = true :=
  checkFragment_sound cap5Part200Block 14 2591 (by decide +kernel)

private def cap5Part201Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 35 (.split (.split (.split (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 39)))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 39))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 35))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.closed 34))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.closed 39))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 33 (.closed 33))))))))))))
    (.onlyOmit 19 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 39 (.onlyOmit 39 (.closed 39)))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.closed 38))))))))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32)))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.closed 34))))))))))))))

private def cap5Part201 : Certificate := cap5Part201Block.toCertificate

private theorem cap5Part201_checked : check 5 60 18 17951 cap5Part201 = true :=
  checkFragment_sound cap5Part201Block 18 17951 (by decide +kernel)

private def cap5Part202Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.closed 36)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 41)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 35))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.closed 35)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 40))))))))))))))))))))))
    (.split (.split (.split (.graft 18 17951 cap5Part201 cap5Part201_checked)
    (.onlyOmit 18 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.closed 31))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 35))))))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 34))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 24 (.closed 24))))))))

private def cap5Part202 : Certificate := cap5Part202Block.toCertificate

private theorem cap5Part202_checked : check 5 60 14 1567 cap5Part202 = true :=
  checkFragment_sound cap5Part202Block 14 1567 (by decide +kernel)

private def cap5Part203Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 39)))))))))))
    (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 38 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 38)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))
    (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 38 (.onlyOmit 38 (.closed 38))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyOmit 35 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 35)))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 35))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 38 (.closed 35)))))))))))))

private def cap5Part203 : Certificate := cap5Part203Block.toCertificate

private theorem cap5Part203_checked : check 5 60 19 74015 cap5Part203 = true :=
  checkFragment_sound cap5Part203Block 19 74015 (by decide +kernel)

private def cap5Part204Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 17 (.split (.graft 19 74015 cap5Part203 cap5Part203_checked)
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32)))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 37)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 35))))))))))))))))))

private def cap5Part204 : Certificate := cap5Part204Block.toCertificate

private theorem cap5Part204_checked : check 5 60 15 8479 cap5Part204 = true :=
  checkFragment_sound cap5Part204Block 15 8479 (by decide +kernel)

private def cap5Part205Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.split (.split (.closed 52)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.closed 52))))))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 68 (.closed 52))))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.split (.split (.onlyOmit 57 (.split (.split (.closed 57)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.closed 52))))))
    (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 51 (.closed 51))))))))
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 57 (.onlyOmit 67 (.onlyOmit 62 (.split (.onlyOmit 57 (.closed 62))
    (.onlyOmit 49 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 56 (.closed 56))))))))))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 48))))))))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 38))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 33 (.closed 33)))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 36 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36)))))))))))

private def cap5Part205 : Certificate := cap5Part205Block.toCertificate

private theorem cap5Part205_checked : check 5 60 24 2134303 cap5Part205 = true :=
  checkFragment_sound cap5Part205Block 24 2134303 (by decide +kernel)

private def cap5Part206Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.closed 42))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 36)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 46)))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.closed 41)))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 40)))))))))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyOmit 33 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 36)))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 33)))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 36 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))))))))

private def cap5Part206 : Certificate := cap5Part206Block.toCertificate

private theorem cap5Part206_checked : check 5 60 21 299295 cap5Part206 = true :=
  checkFragment_sound cap5Part206Block 21 299295 (by decide +kernel)

private def cap5Part207Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.graft 24 2134303 cap5Part205 cap5Part205_checked))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 56)))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 45))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 55 (.closed 45))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 45))))))))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 37))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32))))))))))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.closed 27)))))))
    (.onlyOmit 19 (.onlyOmit 20 (.graft 21 299295 cap5Part206 cap5Part206_checked))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 50)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 39))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))))))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 29))))))))))

private def cap5Part207 : Certificate := cap5Part207Block.toCertificate

private theorem cap5Part207_checked : check 5 60 17 37151 cap5Part207 = true :=
  checkFragment_sound cap5Part207Block 17 37151 (by decide +kernel)

private def cap5Part208Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.closed 39)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 34))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 29))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 47 (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 52 (.closed 57)))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 38))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))))))))
    (.onlyOmit 16 (.graft 17 37151 cap5Part207 cap5Part207_checked)))
    (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 36)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 31)))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.closed 26))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 31))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 29 (.closed 29))))))))))))))

private def cap5Part208 : Certificate := cap5Part208Block.toCertificate

private theorem cap5Part208_checked : check 5 60 14 4383 cap5Part208 = true :=
  checkFragment_sound cap5Part208Block 14 4383 (by decide +kernel)

private def cap5Part209Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 40 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 52)))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 40))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 51 (.closed 51))))))
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 50))))))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.closed 45))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 40))))))))))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 37)))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 49 (.closed 59))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 44))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 39))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.closed 39)))))))))))))))

private def cap5Part209 : Certificate := cap5Part209Block.toCertificate

private theorem cap5Part209_checked : check 5 60 22 133407 cap5Part209 = true :=
  checkFragment_sound cap5Part209Block 22 133407 (by decide +kernel)

private def cap5Part210Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.graft 22 133407 cap5Part209 cap5Part209_checked)
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 57 (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 47 (.closed 47)))))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 43))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 38)))))))))))))))
    (.onlyOmit 21 (.split (.split (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.closed 37))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.closed 46)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 41)))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 36)))))))))))))))))))

private def cap5Part210 : Certificate := cap5Part210Block.toCertificate

private theorem cap5Part210_checked : check 5 60 16 2335 cap5Part210 = true :=
  checkFragment_sound cap5Part210Block 16 2335 (by decide +kernel)

private def cap5Part211Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.split (.onlyOmit 55 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 50)))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 65 (.onlyOmit 60 (.closed 55))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43)))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.split (.onlyOmit 54 (.closed 45))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 45))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 45 (.closed 45))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 44))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 43 (.closed 43)))))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.split (.onlyOmit 53 (.onlyInclude (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 50 (.closed 53)))))))
    (.onlyOmit 45 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 53 (.onlyOmit 53 (.closed 53))))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.split (.closed 53)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.closed 49))))))))))))))))))))))

private def cap5Part211 : Certificate := cap5Part211Block.toCertificate

private theorem cap5Part211_checked : check 5 60 24 1067295 cap5Part211 = true :=
  checkFragment_sound cap5Part211Block 24 1067295 (by decide +kernel)

private def cap5Part212Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.split (.graft 24 1067295 cap5Part211 cap5Part211_checked)
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 34 (.onlyOmit 31 (.onlyOmit 31 (.closed 31))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 43)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 42 (.closed 42)))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyOmit 52 (.onlyOmit 47 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.closed 47))))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 61 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.closed 47)))))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 37)))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.onlyOmit 42 (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 42)))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 51 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))))))))))))))))))))))

private def cap5Part212 : Certificate := cap5Part212Block.toCertificate

private theorem cap5Part212_checked : check 5 60 19 18719 cap5Part212 = true :=
  checkFragment_sound cap5Part212Block 19 18719 (by decide +kernel)

private def cap5Part213Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 19 18719 cap5Part212 cap5Part212_checked)
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 41 (.closed 41)))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 41)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 50 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyOmit 25 (.onlyOmit 25 (.closed 25)))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 37))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))))))))))))))))

private def cap5Part213 : Certificate := cap5Part213Block.toCertificate

private theorem cap5Part213_checked : check 5 60 16 18719 cap5Part213 = true :=
  checkFragment_sound cap5Part213Block 16 18719 (by decide +kernel)

private def cap5Part214Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 16 2335 cap5Part210 cap5Part210_checked)
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 40))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 45 (.onlyOmit 45 (.closed 45)))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 56)))))))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 45 (.split (.split (.closed 45)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 45 (.closed 45)))))))
    (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 50 (.onlyOmit 55 (.onlyOmit 45 (.closed 45)))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))))))))))))
    (.onlyOmit 15 (.graft 16 18719 cap5Part213 cap5Part213_checked)))
    (.onlyOmit 14 (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 40 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 52)))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 40))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 40))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))))))))

private def cap5Part214 : Certificate := cap5Part214Block.toCertificate

private theorem cap5Part214_checked : check 5 60 13 2335 cap5Part214 = true :=
  checkFragment_sound cap5Part214Block 13 2335 (by decide +kernel)

private def cap5Part215Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.closed 36)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 41)))))))
    (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 46 (.closed 41))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.closed 35)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 40)))))))
    (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 35))))))))))
    (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 44 (.onlyOmit 39 (.closed 39)))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 39)))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 39)))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 33))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 38))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.closed 43)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyOmit 33 (.closed 33))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 42)))))))))))))))))))))

private def cap5Part215 : Certificate := cap5Part215Block.toCertificate

private theorem cap5Part215_checked : check 5 60 14 1311 cap5Part215 = true :=
  checkFragment_sound cap5Part215Block 14 1311 (by decide +kernel)

private def cap5Part216Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 37))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))))
    (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 33))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.closed 29)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 32)))))))))))))))

private def cap5Part216 : Certificate := cap5Part216Block.toCertificate

private theorem cap5Part216_checked : check 5 60 16 9503 cap5Part216 = true :=
  checkFragment_sound cap5Part216Block 16 9503 (by decide +kernel)

private def cap5Part217Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.graft 15 8479 cap5Part204 cap5Part204_checked)
    (.onlyOmit 15 (.onlyOmit 16 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 31)))))))))))))))))
    (.split (.graft 14 4383 cap5Part208 cap5Part208_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.closed 30))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.closed 25)))))))))))
    (.onlyOmit 12 (.graft 13 2335 cap5Part214 cap5Part214_checked)))
    (.onlyOmit 11 (.onlyOmit 12 (.split (.graft 14 1311 cap5Part215 cap5Part215_checked)
    (.onlyOmit 14 (.split (.graft 16 9503 cap5Part216 cap5Part216_checked)
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.closed 23)))))))))))))
    (.onlyOmit 10 (.onlyOmit 11 (.onlyOmit 12 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.closed 32))))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 32))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.closed 31))))))))))))))))))))

private def cap5Part217 : Certificate := cap5Part217Block.toCertificate

private theorem cap5Part217_checked : check 5 60 9 287 cap5Part217 = true :=
  checkFragment_sound cap5Part217Block 9 287 (by decide +kernel)

private def cap5Part218Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.split (.split (.onlyOmit 43 (.split (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 45 (.onlyOmit 58 (.onlyOmit 67 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.onlyOmit 52 (.closed 67))))))))))))))))
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 43)))))))
    (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyInclude (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 49 (.onlyOmit 49 (.closed 64))))))))))))
    (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 58))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.closed 41))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.closed 45))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 35)))))))))))

private def cap5Part218 : Certificate := cap5Part218Block.toCertificate

private theorem cap5Part218_checked : check 5 60 23 1069215 cap5Part218 = true :=
  checkFragment_sound cap5Part218Block 23 1069215 (by decide +kernel)

private def cap5Part219Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 33))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 37)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 32))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 36))))))))))))))
    (.onlyOmit 16 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))))))))))
    (.onlyOmit 15 (.onlyOmit 16 (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.split (.graft 23 1069215 cap5Part218 cap5Part218_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 34 (.split (.split (.closed 34)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 26)))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29))))))))))))))

private def cap5Part219 : Certificate := cap5Part219Block.toCertificate

private theorem cap5Part219_checked : check 5 60 14 4255 cap5Part219 = true :=
  checkFragment_sound cap5Part219Block 14 4255 (by decide +kernel)

private def cap5Part220Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 52 (.closed 57)))))))))))
    (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.split (.onlyInclude (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.split (.onlyOmit 68 (.onlyInclude (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 52 (.onlyOmit 56 (.onlyOmit 56 (.closed 56))))))))
    (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 54 (.closed 54)))))))))))
    (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 62))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 48 (.closed 48)))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 56)))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 45 (.split (.split (.split (.closed 45)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 45))))))
    (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 45 (.closed 45)))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 45 (.onlyOmit 50 (.onlyOmit 55 (.onlyOmit 45 (.onlyOmit 45 (.closed 45))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 35))))))

private def cap5Part220 : Certificate := cap5Part220Block.toCertificate

private theorem cap5Part220_checked : check 5 60 28 34637983 cap5Part220 = true :=
  checkFragment_sound cap5Part220Block 28 34637983 (by decide +kernel)

private def cap5Part221Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 37 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 37)))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 40 (.closed 45))))))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 35 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.graft 28 34637983 cap5Part220 cap5Part220_checked))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 26 (.closed 26))))))))))
    (.onlyOmit 15 (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 18 (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 43)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.closed 35)))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))))))))))))))))

private def cap5Part221 : Certificate := cap5Part221Block.toCertificate

private theorem cap5Part221_checked : check 5 60 14 2207 cap5Part221 = true :=
  checkFragment_sound cap5Part221Block 14 2207 (by decide +kernel)

private def cap5Part222Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.split (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 63))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 45 (.closed 45)))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 43 (.split (.onlyOmit 51 (.onlyOmit 43 (.onlyOmit 43 (.closed 43))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 43 (.closed 43)))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.split (.closed 49)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 63 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.closed 63)))))))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 46 (.split (.split (.onlyOmit 46 (.closed 46))
    (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.closed 48)))))))
    (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 46 (.closed 46)))))))))))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 41))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.closed 49)))))))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 43 (.closed 43)))))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))))))))))))

private def cap5Part222 : Certificate := cap5Part222Block.toCertificate

private theorem cap5Part222_checked : check 5 60 22 534687 cap5Part222 = true :=
  checkFragment_sound cap5Part222Block 22 534687 (by decide +kernel)

private def cap5Part223Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.closed 41))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 34))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.closed 39)))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyOmit 49 (.onlyOmit 44 (.onlyOmit 49 (.split (.closed 44)
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 49))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.closed 42))))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.onlyOmit 39 (.split (.split (.closed 39)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 47)))))))
    (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 39)))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 44))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 37)))))))))))))))

private def cap5Part223 : Certificate := cap5Part223Block.toCertificate

private theorem cap5Part223_checked : check 5 60 21 272543 cap5Part223 = true :=
  checkFragment_sound cap5Part223Block 21 272543 (by decide +kernel)

private def cap5Part224Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.graft 22 534687 cap5Part222 cap5Part222_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 34)))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.graft 21 272543 cap5Part223 cap5Part223_checked))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 37))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 42)))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 45 (.closed 50))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 40))))))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 49)))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 37 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.closed 37)))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32)))))))))))))))

private def cap5Part224 : Certificate := cap5Part224Block.toCertificate

private theorem cap5Part224_checked : check 5 60 16 10399 cap5Part224 = true :=
  checkFragment_sound cap5Part224Block 16 10399 (by decide +kernel)

private def cap5Part225Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 43)))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 47 (.closed 47)))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 47))))))))))))))
    (.onlyOmit 30 (.split (.split (.onlyOmit 40 (.split (.split (.onlyOmit 40 (.closed 40))
    (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 52 (.onlyOmit 46 (.closed 46)))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 42 (.closed 42)))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 42))))))))))))))

private def cap5Part225 : Certificate := cap5Part225Block.toCertificate

private theorem cap5Part225_checked : check 5 60 25 8525983 cap5Part225 = true :=
  checkFragment_sound cap5Part225Block 25 8525983 (by decide +kernel)

private def cap5Part226Block : Fragment 5 60 :=
  (.onlyOmit 19 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyInclude (.onlyOmit 31 (.split (.split (.onlyOmit 41 (.split (.split (.onlyOmit 41 (.closed 41))
    (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.split (.onlyOmit 47 (.closed 47))
    (.onlyOmit 43 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.split (.onlyOmit 53 (.closed 53))
    (.onlyOmit 49 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 54 (.onlyOmit 59 (.closed 59)))))))))))))))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.closed 41)))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 41))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.closed 41)))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 41))))))))))))))
    (.onlyOmit 24 (.graft 25 8525983 cap5Part225 cap5Part225_checked)))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 32))))))))))))

private def cap5Part226 : Certificate := cap5Part226Block.toCertificate

private theorem cap5Part226_checked : check 5 60 19 137375 cap5Part226 = true :=
  checkFragment_sound cap5Part226Block 19 137375 (by decide +kernel)

private def cap5Part227Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 36 (.split (.split (.closed 36)
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 41)))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 46 (.closed 41))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 35 (.split (.split (.closed 35)
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 40)))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 39 (.split (.onlyOmit 44 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.closed 39))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.closed 30)))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 34 (.split (.split (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 39)))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 38 (.split (.split (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 43)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))))))))

private def cap5Part227 : Certificate := cap5Part227Block.toCertificate

private theorem cap5Part227_checked : check 5 60 19 33951 cap5Part227 = true :=
  checkFragment_sound cap5Part227Block 19 33951 (by decide +kernel)

private def cap5Part228Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 44 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 44))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 44 (.closed 44)))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 49 (.onlyOmit 54 (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 49)))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 43 (.closed 43))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.closed 43)))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 34)))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))

private def cap5Part228 : Certificate := cap5Part228Block.toCertificate

private theorem cap5Part228_checked : check 5 60 23 541855 cap5Part228 = true :=
  checkFragment_sound cap5Part228Block 23 541855 (by decide +kernel)

private def cap5Part229Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.split (.graft 23 541855 cap5Part228 cap5Part228_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29)))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 41))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 46))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 61 (.closed 51)))))))))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 41 (.split (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 41))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 33)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 40))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))))))

private def cap5Part229 : Certificate := cap5Part229Block.toCertificate

private theorem cap5Part229_checked : check 5 60 18 17567 cap5Part229 = true :=
  checkFragment_sound cap5Part229Block 18 17567 (by decide +kernel)

private def cap5Part230Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.split (.closed 41)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.closed 41)))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 41))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 50 (.closed 45))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 40)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 44 (.split (.split (.onlyOmit 44 (.onlyOmit 44 (.closed 44)))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.closed 52)))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.closed 44))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 44)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 44 (.closed 44))))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 48 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 44 (.closed 44)))))))))))))))))))))

private def cap5Part230 : Certificate := cap5Part230Block.toCertificate

private theorem cap5Part230_checked : check 5 60 22 271519 cap5Part230 = true :=
  checkFragment_sound cap5Part230Block 22 271519 (by decide +kernel)

private def cap5Part231Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 17 (.split (.graft 19 33951 cap5Part227 cap5Part227_checked)
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.closed 25)))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.graft 18 17567 cap5Part229 cap5Part229_checked)))))
    (.onlyOmit 14 (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.split (.graft 22 271519 cap5Part230 cap5Part230_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28)))))))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 40))))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.closed 37))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 27)))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 36))))))))))))))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 22 (.closed 22))))))))))

private def cap5Part231 : Certificate := cap5Part231Block.toCertificate

private theorem cap5Part231_checked : check 5 60 12 1183 cap5Part231 = true :=
  checkFragment_sound cap5Part231Block 12 1183 (by decide +kernel)

private def cap5Part232Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.split (.closed 45)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 55 (.closed 45))))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 44)))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 44))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 43 (.closed 43)))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 42)))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.closed 42))))))))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))))))

private def cap5Part232 : Certificate := cap5Part232Block.toCertificate

private theorem cap5Part232_checked : check 5 60 19 33439 cap5Part232 = true :=
  checkFragment_sound cap5Part232Block 19 33439 (by decide +kernel)

private def cap5Part233Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 42 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.closed 32)))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 44 (.closed 44)))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 52 (.onlyOmit 48 (.split (.onlyOmit 48 (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 48 (.onlyOmit 48 (.closed 48)))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 48))))))))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 40)))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.closed 36)))))))
    (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyOmit 40 (.split (.onlyOmit 40 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 40)))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 48 (.onlyOmit 44 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))))))))))))

private def cap5Part233 : Certificate := cap5Part233Block.toCertificate

private theorem cap5Part233_checked : check 5 60 22 279199 cap5Part233 = true :=
  checkFragment_sound cap5Part233Block 22 279199 (by decide +kernel)

private def cap5Part234Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 16 (.split (.split (.graft 19 33439 cap5Part232 cap5Part232_checked)
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 41))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 46))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 61 (.closed 51)))))))))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.graft 22 279199 cap5Part233 cap5Part233_checked)))))
    (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 31))))))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.closed 36)))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyOmit 30 (.closed 30))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34)))))))))))))))))))

private def cap5Part234 : Certificate := cap5Part234Block.toCertificate

private theorem cap5Part234_checked : check 5 60 13 671 cap5Part234 = true :=
  checkFragment_sound cap5Part234Block 13 671 (by decide +kernel)

private def cap5Part235Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.split (.graft 14 4255 cap5Part219 cap5Part219_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.closed 25))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 33))))))))))))))))))))
    (.split (.split (.graft 14 2207 cap5Part221 cap5Part221_checked)
    (.onlyOmit 14 (.onlyOmit 15 (.graft 16 10399 cap5Part224 cap5Part224_checked))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.graft 19 137375 cap5Part226 cap5Part226_checked)))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 23 (.closed 23)))))))))))
    (.onlyOmit 11 (.graft 12 1183 cap5Part231 cap5Part231_checked)))
    (.onlyOmit 10 (.onlyOmit 11 (.split (.graft 13 671 cap5Part234 cap5Part234_checked)
    (.onlyOmit 13 (.onlyOmit 16 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 29)))))))))))))))))))
    (.onlyOmit 9 (.onlyOmit 10 (.onlyOmit 11 (.split (.onlyInclude (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.closed 29)))))))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 29))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 20 (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.closed 28)))))))))))))))))))

private def cap5Part235 : Certificate := cap5Part235Block.toCertificate

private theorem cap5Part235_checked : check 5 60 8 159 cap5Part235 = true :=
  checkFragment_sound cap5Part235Block 8 159 (by decide +kernel)

private def cap5Part236Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 17 (.split (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 31 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 44)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 48))))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 29)))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.closed 26))))))
    (.onlyOmit 21 (.onlyOmit 21 (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.closed 34)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.closed 33)))))))))))))

private def cap5Part236 : Certificate := cap5Part236Block.toCertificate

private theorem cap5Part236_checked : check 5 60 15 2143 cap5Part236 = true :=
  checkFragment_sound cap5Part236Block 15 2143 (by decide +kernel)

private def cap5Part237Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 45 (.onlyInclude (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 52 (.closed 59)))))))))
    (.onlyOmit 39 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.closed 44)))))))))))
    (.split (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.closed 58)))))))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 45 (.closed 44)))))))))
    (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))))))
    (.split (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.split (.onlyOmit 44 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 51 (.onlyInclude (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 58 (.closed 57))))))))))))))))
    (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.closed 43))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.split (.closed 37)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 51)))))))))))))))
    (.onlyOmit 25 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))

private def cap5Part237 : Certificate := cap5Part237Block.toCertificate

private theorem cap5Part237_checked : check 5 60 24 530527 cap5Part237 = true :=
  checkFragment_sound cap5Part237Block 24 530527 (by decide +kernel)

private def cap5Part238Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyInclude (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 57 (.closed 56)))))))))))))))))))))
    (.onlyOmit 43 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 56 (.closed 49)))))))))))))))
    (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))))))
    (.split (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.closed 55)))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.split (.closed 36)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 42)))))))))))))))
    (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyInclude (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.split (.onlyOmit 57 (.closed 57))
    (.onlyOmit 45 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 57 (.onlyOmit 70 (.onlyOmit 57 (.closed 57))))))))))))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 49))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.split (.closed 43)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyInclude (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 57 (.closed 56)))))))))))))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 56 (.closed 49)))))))))))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 36))))))))))))))

private def cap5Part238 : Certificate := cap5Part238Block.toCertificate

private theorem cap5Part238_checked : check 5 60 22 268383 cap5Part238 = true :=
  checkFragment_sound cap5Part238Block 22 268383 (by decide +kernel)

private def cap5Part239Block : Fragment 5 60 :=
  (.split (.split (.graft 22 268383 cap5Part238 cap5Part238_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.closed 32))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.split (.onlyOmit 46 (.onlyInclude (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 59 (.closed 52)))))))))
    (.onlyOmit 40 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.closed 45))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 59 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.closed 59))))))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 39))))))
    (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.split (.onlyOmit 43 (.closed 43))
    (.onlyOmit 39 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyInclude (.onlyOmit 46 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 50 (.onlyOmit 57 (.closed 56)))))))))))))))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 56 (.closed 49)))))))))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36)))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.split (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 58 (.closed 51)))))))))
    (.onlyOmit 39 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.closed 58))))))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 43))))))))))))))))))))

private def cap5Part239 : Certificate := cap5Part239Block.toCertificate

private theorem cap5Part239_checked : check 5 60 20 268383 cap5Part239 = true :=
  checkFragment_sound cap5Part239Block 20 268383 (by decide +kernel)

private def cap5Part240Block : Fragment 5 60 :=
  (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.split (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 55 (.onlyOmit 55 (.onlyInclude (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 49 (.onlyOmit 62 (.onlyOmit 55 (.closed 55)))))))))))))))
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.closed 48))))))))
    (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.split (.closed 48)
    (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 55 (.closed 67))))))))))))))))))))
    (.split (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 41))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.closed 41)))))))))
    (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.split (.closed 41)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 53 (.onlyInclude (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 60 (.onlyOmit 53 (.closed 53))))))))))))))))))))))))))))))))

private def cap5Part240 : Certificate := cap5Part240Block.toCertificate

private theorem cap5Part240_checked : check 5 60 19 137311 cap5Part240 = true :=
  checkFragment_sound cap5Part240Block 19 137311 (by decide +kernel)

private def cap5Part241Block : Fragment 5 60 :=
  (.onlyOmit 22 (.onlyOmit 23 (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.split (.onlyOmit 45 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 52 (.closed 59)))))))))
    (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 44)))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyInclude (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.closed 58)))))))))))))))
    (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 37)))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 44 (.split (.closed 44)
    (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 45 (.closed 58))))))))))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.split (.onlyOmit 44 (.onlyInclude (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 51 (.onlyInclude (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 51 (.onlyOmit 58 (.closed 57))))))))))))))))
    (.onlyOmit 38 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 43))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))

private def cap5Part241 : Certificate := cap5Part241Block.toCertificate

private theorem cap5Part241_checked : check 5 60 22 596063 cap5Part241 = true :=
  checkFragment_sound cap5Part241Block 22 596063 (by decide +kernel)

private def cap5Part242Block : Fragment 5 60 :=
  (.split (.split (.split (.graft 15 2143 cap5Part236 cap5Part236_checked)
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 25))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 41)))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40)))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.closed 32)))))))))))))
    (.onlyOmit 14 (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.onlyInclude (.onlyOmit 19 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 24 (.closed 24)))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.graft 24 530527 cap5Part237 cap5Part237_checked))))))
    (.split (.graft 20 268383 cap5Part239 cap5Part239_checked)
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 44 (.closed 43))))))))))))))))))))))
    (.onlyOmit 18 (.graft 19 137311 cap5Part240 cap5Part240_checked)))
    (.onlyOmit 17 (.onlyOmit 18 (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 35 (.closed 35)))))))))))))))
    (.onlyOmit 20 (.onlyOmit 22 (.graft 22 596063 cap5Part241 cap5Part241_checked)))))))))))

private def cap5Part242 : Certificate := cap5Part242Block.toCertificate

private theorem cap5Part242_checked : check 5 60 12 2143 cap5Part242 = true :=
  checkFragment_sound cap5Part242Block 12 2143 (by decide +kernel)

private def cap5Part243Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.split (.split (.onlyOmit 37 (.split (.onlyOmit 37 (.closed 37))
    (.onlyOmit 33 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.closed 42)))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 37 (.closed 37))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 37))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.split (.split (.onlyOmit 36 (.split (.onlyOmit 36 (.closed 36))
    (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.closed 41)))))))))
    (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 32 (.closed 36)))))))))))))
    (.onlyOmit 21 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 42 (.onlyOmit 47 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 37))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 46 (.onlyOmit 41 (.closed 41)))))))))))))
    (.onlyOmit 26 (.split (.split (.onlyOmit 35 (.split (.onlyOmit 35 (.closed 35))
    (.onlyOmit 31 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 31 (.closed 35))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.split (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 38 (.onlyOmit 38 (.closed 38)))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 38)))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 37 (.closed 37)))))))))))))))

private def cap5Part243 : Certificate := cap5Part243Block.toCertificate

private theorem cap5Part243_checked : check 5 60 20 33887 cap5Part243 = true :=
  checkFragment_sound cap5Part243Block 20 33887 (by decide +kernel)

private def cap5Part244Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 38 (.split (.onlyOmit 50 (.onlyOmit 55 (.split (.split (.closed 50)
    (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.onlyOmit 50 (.closed 55)))))))))
    (.onlyOmit 43 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.closed 50))))))))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 43 (.closed 45)))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 41 (.closed 41))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 49 (.onlyOmit 54 (.split (.onlyInclude (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 49 (.closed 49))))))
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 49)))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.split (.split (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 43 (.closed 43))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43))))))
    (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 43 (.onlyOmit 43 (.closed 43)))))))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 45 (.onlyOmit 50 (.split (.split (.closed 45)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.closed 50)))))))))
    (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 43)))))))))))))))))

private def cap5Part244 : Certificate := cap5Part244Block.toCertificate

private theorem cap5Part244_checked : check 5 60 26 17319007 cap5Part244 = true :=
  checkFragment_sound cap5Part244Block 26 17319007 (by decide +kernel)

private def cap5Part245Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 45 (.split (.split (.split (.closed 45)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 45 (.closed 45))))))
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.closed 45))))))
    (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 45 (.onlyOmit 45 (.closed 45)))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 44 (.split (.split (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 44 (.closed 44))))))
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 44))))))
    (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 44 (.onlyOmit 44 (.closed 44))))))))))))))))))
    (.onlyOmit 25 (.graft 26 17319007 cap5Part244 cap5Part244_checked)))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 33))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 41 (.closed 41)))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))))))

private def cap5Part245 : Certificate := cap5Part245Block.toCertificate

private theorem cap5Part245_checked : check 5 60 22 541791 cap5Part245 = true :=
  checkFragment_sound cap5Part245Block 22 541791 (by decide +kernel)

private def cap5Part246Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 39 (.split (.onlyOmit 39 (.onlyOmit 39 (.closed 39)))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.split (.closed 51)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.closed 46)))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 50)))))))))))))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.split (.onlyInclude (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 41))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 44 (.split (.onlyOmit 44 (.onlyOmit 44 (.closed 44)))
    (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 49 (.closed 49)))))))))))))
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 39))))))
    (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.split (.split (.onlyOmit 49 (.onlyInclude (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 46)))))))
    (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 42 (.closed 44))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 59 (.onlyOmit 49 (.onlyOmit 54 (.closed 49)))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 36))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31))))))

private def cap5Part246 : Certificate := cap5Part246Block.toCertificate

private theorem cap5Part246_checked : check 5 60 25 4342879 cap5Part246 = true :=
  checkFragment_sound cap5Part246Block 25 4342879 (by decide +kernel)

private def cap5Part247Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 16 (.split (.split (.split (.graft 20 33887 cap5Part243 cap5Part243_checked)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 25 (.onlyOmit 25 (.closed 25))))))
    (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 25 (.split (.onlyOmit 33 (.split (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 38 (.closed 38)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 33 (.closed 33)))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))))))
    (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 32 (.split (.onlyOmit 32 (.closed 32))
    (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.closed 37)))))))))))))))))))))
    (.onlyOmit 16 (.onlyOmit 16 (.split (.split (.onlyInclude (.onlyOmit 20 (.split (.graft 22 541791 cap5Part245 cap5Part245_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 40 (.split (.split (.split (.closed 40)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 47)))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 40))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 40)))))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 24 (.onlyOmit 24 (.closed 24))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 24 (.graft 25 4342879 cap5Part246 cap5Part246_checked))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))))))))))

private def cap5Part247 : Certificate := cap5Part247Block.toCertificate

private theorem cap5Part247_checked : check 5 60 14 1119 cap5Part247 = true :=
  checkFragment_sound cap5Part247Block 14 1119 (by decide +kernel)

private def cap5Part248Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 31 (.onlyOmit 42 (.split (.split (.split (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 47 (.closed 47)))))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 42))))))
    (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 42))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 39)))))))))))))))
    (.onlyOmit 24 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 36 (.closed 36))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 47 (.split (.onlyOmit 52 (.split (.onlyOmit 47 (.onlyOmit 52 (.closed 47)))
    (.onlyOmit 41 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.closed 47)))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.closed 44)))))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.split (.split (.split (.closed 41)
    (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 41))))))
    (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 38))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.closed 33))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.closed 41)))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 31))))))))

private def cap5Part248 : Certificate := cap5Part248Block.toCertificate

private theorem cap5Part248_checked : check 5 60 23 271455 cap5Part248 = true :=
  checkFragment_sound cap5Part248Block 23 271455 (by decide +kernel)

private def cap5Part249Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 42 (.split (.split (.split (.onlyOmit 42 (.split (.closed 42)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 47 (.closed 47)))))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 42 (.closed 47)))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.closed 42))))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.split (.onlyInclude (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 41 (.split (.onlyOmit 41 (.closed 41))
    (.onlyOmit 37 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 48 (.split (.closed 48)
    (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 48 (.onlyOmit 48 (.onlyOmit 53 (.closed 53))))))))))))))))))))
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))
    (.onlyOmit 30 (.onlyOmit 41 (.split (.split (.split (.onlyOmit 41 (.split (.closed 41)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 46 (.closed 46)))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.closed 46)))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.closed 39))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 36 (.closed 41)))))))))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))))))

private def cap5Part249 : Certificate := cap5Part249Block.toCertificate

private theorem cap5Part249_checked : check 5 60 24 136287 cap5Part249 = true :=
  checkFragment_sound cap5Part249Block 24 136287 (by decide +kernel)

private def cap5Part250Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 52 (.onlyOmit 47 (.onlyOmit 52 (.closed 47))))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 39 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyOmit 51 (.closed 46))))))))))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 29 (.split (.split (.split (.onlyOmit 39 (.split (.closed 39)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 44 (.closed 44)))))))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 44)))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.closed 37))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 39)))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 47 (.onlyOmit 42 (.onlyOmit 47 (.closed 42))))))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.split (.onlyOmit 34 (.closed 34))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))))))))))))

private def cap5Part250 : Certificate := cap5Part250Block.toCertificate

private theorem cap5Part250_checked : check 5 60 24 4330591 cap5Part250 = true :=
  checkFragment_sound cap5Part250Block 24 4330591 (by decide +kernel)

private def cap5Part251Block : Fragment 5 60 :=
  (.split (.split (.graft 14 1119 cap5Part247 cap5Part247_checked)
    (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.split (.onlyInclude (.onlyOmit 19 (.split (.split (.split (.graft 23 271455 cap5Part248 cap5Part248_checked)
    (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 31 (.split (.onlyOmit 31 (.onlyOmit 31 (.closed 31)))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.split (.closed 39)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.closed 38)))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 23 (.onlyOmit 23 (.closed 23))))))))))
    (.onlyOmit 13 (.onlyOmit 14 (.onlyOmit 16 (.onlyOmit 16 (.onlyInclude (.onlyOmit 18 (.split (.split (.split (.split (.split (.graft 24 136287 cap5Part249 cap5Part249_checked)
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.closed 29))))))
    (.onlyOmit 23 (.graft 24 4330591 cap5Part250 cap5Part250_checked)))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.split (.onlyOmit 37 (.split (.closed 37)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 42 (.closed 42)))))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 42))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 41)))))))))))))))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.split (.onlyOmit 29 (.closed 29))
    (.onlyOmit 25 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 36 (.split (.closed 36)
    (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 41 (.onlyOmit 41 (.closed 41))))))))))))))))))))))))))))

private def cap5Part251 : Certificate := cap5Part251Block.toCertificate

private theorem cap5Part251_checked : check 5 60 12 1119 cap5Part251 = true :=
  checkFragment_sound cap5Part251Block 12 1119 (by decide +kernel)

private def cap5Part252Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.split (.onlyOmit 46 (.closed 46))
    (.onlyOmit 42 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 65 (.closed 53))))))))))))))))))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 41 (.onlyInclude (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 52 (.closed 52))))))))))))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 52 (.closed 46))))))))))))))
    (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.split (.onlyOmit 45 (.closed 45))
    (.onlyOmit 41 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 46 (.closed 51)))))))))))))))))))))))))
    (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.split (.onlyOmit 39 (.closed 39))
    (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 40 (.closed 51))))))))))))))))))))

private def cap5Part252 : Certificate := cap5Part252Block.toCertificate

private theorem cap5Part252_checked : check 5 60 22 134239 cap5Part252 = true :=
  checkFragment_sound cap5Part252Block 22 134239 (by decide +kernel)

private def cap5Part253Block : Fragment 5 60 :=
  (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 39)))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 45)))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.split (.onlyOmit 38 (.closed 38))
    (.onlyOmit 34 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 44)))))))))))))
    (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 38)))))))))))))
    (.onlyOmit 22 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 39 (.onlyOmit 39 (.closed 44))))))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 26 (.onlyOmit 26 (.closed 26))))))
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.closed 35))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.closed 29))))))))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 29 (.onlyOmit 29 (.closed 34)))))))))))))

private def cap5Part253 : Certificate := cap5Part253Block.toCertificate

private theorem cap5Part253_checked : check 5 60 18 68703 cap5Part253 = true :=
  checkFragment_sound cap5Part253Block 18 68703 (by decide +kernel)

private def cap5Part254Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 27 (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 39))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyOmit 43 (.split (.split (.closed 43)
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 43 (.closed 43))))))
    (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.closed 43)))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.closed 43))))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.closed 34)))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 38))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 42 (.split (.onlyInclude (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 42 (.closed 42))))))
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 42))))))))))))))))
    (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 32 (.onlyOmit 32 (.closed 32))))))))
    (.onlyOmit 23 (.onlyOmit 24 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 51 (.onlyOmit 47 (.split (.split (.closed 47)
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 47 (.closed 47))))))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 47 (.onlyOmit 47 (.closed 47))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 42)))))))))))
    (.onlyOmit 28 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 36 (.onlyOmit 36 (.closed 36))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 40 (.closed 40)))))))))))))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))))))

private def cap5Part254 : Certificate := cap5Part254Block.toCertificate

private theorem cap5Part254_checked : check 5 60 22 279135 cap5Part254 = true :=
  checkFragment_sound cap5Part254Block 22 279135 (by decide +kernel)

private def cap5Part255Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 22 (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 39 (.split (.split (.closed 55)
    (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.closed 50))))))
    (.onlyOmit 41 (.onlyOmit 43 (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 65 (.onlyOmit 55 (.closed 60)))))))))))))))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 33 (.split (.onlyOmit 33 (.onlyOmit 33 (.closed 33)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 37 (.closed 37))))))))))))
    (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29)))))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 38 (.closed 43))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 32 (.split (.onlyOmit 32 (.onlyOmit 32 (.closed 32)))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.closed 36))))))))))))))))
    (.onlyOmit 19 (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 22 (.onlyInclude (.onlyOmit 24 (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 27 (.onlyInclude (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.closed 41)))))))))))))))))))))

private def cap5Part255 : Certificate := cap5Part255Block.toCertificate

private theorem cap5Part255_checked : check 5 60 18 8799 cap5Part255 = true :=
  checkFragment_sound cap5Part255Block 18 8799 (by decide +kernel)

private def cap5Part256Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 15 (.split (.split (.split (.onlyInclude (.onlyOmit 20 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 23 (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 33)))))))))))
    (.onlyOmit 20 (.onlyOmit 20 (.split (.graft 22 279135 cap5Part254 cap5Part254_checked)
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 24 (.onlyOmit 27 (.closed 27)))))))))
    (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 23 (.closed 23))))))
    (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 30)))))))))))))
    (.onlyOmit 15 (.onlyOmit 15 (.split (.split (.graft 18 8799 cap5Part255 cap5Part255_checked)
    (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.onlyOmit 30 (.closed 30))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 42 (.onlyInclude (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 46 (.onlyOmit 47 (.closed 51)))))))))))))))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 40 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))))))))))))
    (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.onlyInclude (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.closed 59)))))))))))))))))))))
    (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.closed 30)))
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.closed 34))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))))))

private def cap5Part256 : Certificate := cap5Part256Block.toCertificate

private theorem cap5Part256_checked : check 5 60 13 607 cap5Part256 = true :=
  checkFragment_sound cap5Part256Block 13 607 (by decide +kernel)

private def cap5Part257Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 39 (.split (.onlyOmit 39 (.onlyOmit 39 (.closed 39)))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 46 (.onlyInclude (.onlyOmit 42 (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 50 (.closed 50)))))))))))))))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.closed 35))))))
    (.onlyOmit 29 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 32 (.onlyInclude (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 39)))))))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 39 (.split (.split (.onlyOmit 39 (.onlyInclude (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 39 (.onlyOmit 43 (.closed 43)))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 36 (.closed 39))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 39 (.onlyOmit 39 (.closed 39))))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 37))))))))))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 36 (.split (.onlyOmit 36 (.onlyOmit 36 (.closed 36)))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 43 (.closed 47))))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyInclude (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.closed 36)))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.split (.onlyOmit 36 (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 36 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.closed 36)))))))))))
    (.onlyOmit 24 (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 32)))))))))))

private def cap5Part257 : Certificate := cap5Part257Block.toCertificate

private theorem cap5Part257_checked : check 5 60 20 70239 cap5Part257 = true :=
  checkFragment_sound cap5Part257Block 20 70239 (by decide +kernel)

private def cap5Part258Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.graft 12 2143 cap5Part242 cap5Part242_checked))
    (.split (.graft 12 1119 cap5Part251 cap5Part251_checked)
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 14 (.split (.split (.split (.onlyInclude (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.onlyInclude (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 41)))))))))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 28 (.onlyOmit 28 (.closed 28))))))))))
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.graft 22 134239 cap5Part252 cap5Part252_checked))))))
    (.onlyOmit 17 (.graft 18 68703 cap5Part253 cap5Part253_checked)))
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.split (.onlyInclude (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 38))))))))
    (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 33 (.onlyOmit 33 (.closed 33))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 33 (.closed 37)))))))))))))))))))))))))
    (.onlyOmit 10 (.split (.split (.graft 13 607 cap5Part256 cap5Part256_checked)
    (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 36 (.onlyOmit 36 (.closed 39)))))))))))))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.split (.graft 20 70239 cap5Part257 cap5Part257_checked)
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 28)))))))))))))))
    (.onlyOmit 12 (.onlyOmit 13 (.onlyOmit 15 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 25 (.closed 27))))))))))))))))))

private def cap5Part258 : Certificate := cap5Part258Block.toCertificate

private theorem cap5Part258_checked : check 5 60 9 95 cap5Part258 = true :=
  checkFragment_sound cap5Part258Block 9 95 (by decide +kernel)

private def cap5Part259Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 31 (.closed 31))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 31 (.closed 35)))))))))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.onlyOmit 21 (.onlyOmit 21 (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 30 (.closed 30)))))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.split (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.closed 35))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyInclude (.onlyOmit 32 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 35 (.closed 39)))))))))))
    (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 38 (.split (.onlyOmit 38 (.split (.closed 38)
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.closed 41)))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 38)))))))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))))))))

private def cap5Part259 : Certificate := cap5Part259Block.toCertificate

private theorem cap5Part259_checked : check 5 60 16 8543 cap5Part259 = true :=
  checkFragment_sound cap5Part259Block 16 8543 (by decide +kernel)

private def cap5Part260Block : Fragment 5 60 :=
  (.split (.split (.split (.onlyInclude (.onlyOmit 30 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.closed 37))))
    (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 44 (.onlyInclude (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 47 (.closed 47))))))))))))))))))
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.split (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 47 (.closed 47))))))
    (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyInclude (.onlyOmit 46 (.onlyOmit 47 (.onlyOmit 48 (.onlyOmit 49 (.closed 72)))))))))))
    (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.closed 47))))))))
    (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 44))))))
    (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 49 (.split (.onlyOmit 49 (.onlyOmit 59 (.onlyOmit 49 (.closed 49))))
    (.onlyOmit 43 (.onlyOmit 44 (.onlyOmit 45 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 49 (.onlyOmit 54 (.closed 54)))))))))))))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 39 (.onlyOmit 40 (.closed 42))))))))))
    (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.closed 37))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 30 (.onlyOmit 30 (.closed 34))))))

private def cap5Part260 : Certificate := cap5Part260Block.toCertificate

private theorem cap5Part260_checked : check 5 60 26 4231519 cap5Part260 = true :=
  checkFragment_sound cap5Part260Block 26 4231519 (by decide +kernel)

private def cap5Part261Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 23 (.split (.split (.graft 26 4231519 cap5Part260 cap5Part260_checked)
    (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 37 (.split (.onlyOmit 37 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40)))))))))
    (.onlyOmit 31 (.onlyOmit 33 (.onlyOmit 33 (.onlyOmit 34 (.closed 37)))))))))))
    (.onlyOmit 25 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 30))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.split (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.split (.split (.split (.split (.split (.onlyInclude (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.closed 40))))))
    (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.onlyInclude (.onlyOmit 39 (.onlyOmit 40 (.onlyOmit 41 (.onlyOmit 45 (.closed 45)))))))))))
    (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.closed 40))))))))
    (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 35 (.onlyOmit 35 (.closed 37))))))
    (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.split (.split (.split (.onlyOmit 45 (.split (.closed 45)
    (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 42 (.onlyOmit 42 (.closed 45)))))))
    (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 40 (.onlyOmit 40 (.closed 42))))))
    (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.onlyOmit 45 (.onlyOmit 55 (.onlyOmit 45 (.onlyOmit 45 (.onlyOmit 45 (.closed 45))))))))))
    (.onlyOmit 35 (.onlyOmit 36 (.onlyOmit 37 (.onlyOmit 38 (.closed 40))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 32 (.onlyOmit 33 (.closed 35))))))))))
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.closed 32))))))))))

private def cap5Part261 : Certificate := cap5Part261Block.toCertificate

private theorem cap5Part261_checked : check 5 60 20 37215 cap5Part261 = true :=
  checkFragment_sound cap5Part261Block 20 37215 (by decide +kernel)

private def cap5Part262Block : Fragment 5 60 :=
  (.split (.onlyInclude (.onlyOmit 25 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.onlyInclude (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 35 (.onlyOmit 35 (.onlyOmit 35 (.onlyInclude (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.split (.onlyOmit 53 (.onlyInclude (.onlyOmit 44 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 47 (.split (.onlyOmit 53 (.closed 53))
    (.onlyOmit 49 (.onlyOmit 51 (.onlyOmit 51 (.onlyOmit 53 (.onlyOmit 53 (.onlyOmit 54 (.closed 72))))))))))))))
    (.onlyOmit 42 (.onlyOmit 44 (.onlyOmit 44 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 47 (.onlyOmit 65 (.onlyOmit 53 (.closed 53)))))))))))))))))))))))))))
    (.onlyOmit 25 (.onlyOmit 25 (.split (.split (.split (.split (.onlyInclude (.onlyOmit 31 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.onlyInclude (.onlyOmit 36 (.onlyOmit 38 (.onlyOmit 38 (.onlyOmit 41 (.onlyOmit 41 (.onlyOmit 41 (.onlyInclude (.onlyOmit 43 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 46 (.onlyOmit 53 (.onlyOmit 65 (.closed 53))))))))))))))))))))
    (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 40 (.split (.onlyOmit 40 (.split (.closed 40)
    (.onlyOmit 37 (.onlyOmit 37 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 40 (.onlyOmit 52 (.closed 46)))))))))
    (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 37 (.onlyOmit 37 (.closed 40))))))))))
    (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyOmit 34 (.closed 34))))))
    (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 31 (.onlyOmit 31 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 38 (.closed 38)))))))))))
    (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 34 (.onlyOmit 34 (.onlyOmit 34 (.closed 34)))))))))))

private def cap5Part262 : Certificate := cap5Part262Block.toCertificate

private theorem cap5Part262_checked : check 5 60 23 133471 cap5Part262 = true :=
  checkFragment_sound cap5Part262Block 23 133471 (by decide +kernel)

private def cap5Part263Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.onlyOmit 14 (.split (.graft 16 8543 cap5Part259 cap5Part259_checked)
    (.onlyOmit 16 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.closed 21))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.split (.onlyInclude (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.split (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 39 (.onlyInclude (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 35 (.onlyOmit 39 (.closed 39)))))))))))
    (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.closed 34))))))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.closed 29))))))))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.split (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.split (.onlyInclude (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.onlyOmit 37 (.closed 37))))))
    (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 33 (.onlyOmit 34 (.closed 38))))))))))
    (.onlyOmit 27 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.closed 33)))))))))))))))
    (.onlyOmit 16 (.onlyOmit 18 (.onlyOmit 18 (.split (.graft 20 37215 cap5Part261 cap5Part261_checked)
    (.onlyOmit 20 (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 27 (.onlyOmit 27 (.closed 27)))))))))))))))
    (.onlyOmit 12 (.onlyOmit 14 (.onlyOmit 14 (.split (.split (.split (.onlyInclude (.onlyOmit 19 (.split (.split (.split (.onlyInclude (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 29 (.closed 29))))))
    (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 26 (.onlyOmit 26 (.onlyInclude (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 33 (.closed 33)))))))))))
    (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 29 (.onlyOmit 29 (.onlyOmit 29 (.closed 29))))))))
    (.onlyOmit 21 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.closed 26))))))))
    (.onlyOmit 19 (.onlyOmit 19 (.split (.split (.split (.graft 23 133471 cap5Part262 cap5Part262_checked)
    (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyOmit 28 (.closed 28))))))
    (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 25 (.onlyOmit 25 (.onlyInclude (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 29 (.onlyOmit 32 (.closed 32)))))))))))
    (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 28 (.onlyOmit 28 (.onlyOmit 28 (.closed 28)))))))))))
    (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.split (.onlyInclude (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyOmit 27 (.closed 27))))))
    (.onlyOmit 22 (.onlyOmit 22 (.onlyOmit 24 (.onlyOmit 24 (.onlyInclude (.onlyOmit 26 (.onlyOmit 27 (.onlyOmit 28 (.onlyOmit 31 (.closed 31)))))))))))))))
    (.onlyOmit 17 (.onlyOmit 17 (.onlyOmit 19 (.onlyOmit 19 (.onlyInclude (.onlyOmit 21 (.onlyOmit 23 (.onlyOmit 23 (.onlyOmit 26 (.closed 26)))))))))))))))

private def cap5Part263 : Certificate := cap5Part263Block.toCertificate

private theorem cap5Part263_checked : check 5 60 11 351 cap5Part263 = true :=
  checkFragment_sound cap5Part263Block 11 351 (by decide +kernel)

private def cap5Part264Block : Fragment 5 60 :=
  (.split (.split (.onlyInclude (.split (.graft 7 39 cap5Part95 cap5Part95_checked)
    (.onlyOmit 7 (.split (.onlyInclude (.onlyOmit 11 (.onlyOmit 11 (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.onlyInclude (.onlyOmit 18 (.onlyOmit 18 (.split (.closed 22)
    (.onlyOmit 21 (.onlyOmit 21 (.onlyOmit 22 (.closed 25)))))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.split (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.closed 21))))
    (.onlyOmit 17 (.onlyOmit 17 (.split (.closed 21)
    (.onlyOmit 20 (.onlyOmit 20 (.onlyOmit 21 (.closed 24))))))))))))))
    (.split (.graft 10 359 cap5Part97 cap5Part97_checked)
    (.onlyOmit 10 (.onlyOmit 11 (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 14 (.graft 15 871 cap5Part102 cap5Part102_checked)))))))))))
    (.split (.graft 6 23 cap5Part112 cap5Part112_checked)
    (.onlyOmit 6 (.graft 7 55 cap5Part126 cap5Part126_checked))))
    (.split (.split (.split (.onlyInclude (.split (.graft 9 143 cap5Part134 cap5Part134_checked)
    (.onlyOmit 9 (.onlyOmit 10 (.graft 11 399 cap5Part136 cap5Part136_checked)))))
    (.graft 7 79 cap5Part144 cap5Part144_checked))
    (.split (.split (.graft 8 47 cap5Part153 cap5Part153_checked)
    (.onlyOmit 8 (.graft 9 175 cap5Part156 cap5Part156_checked)))
    (.onlyOmit 7 (.onlyOmit 8 (.split (.graft 10 111 cap5Part176 cap5Part176_checked)
    (.onlyOmit 11 (.onlyOmit 11 (.split (.onlyInclude (.onlyOmit 14 (.onlyOmit 15 (.split (.onlyInclude (.onlyOmit 18 (.onlyOmit 19 (.onlyOmit 22 (.closed 22)))))
    (.onlyOmit 18 (.onlyOmit 18 (.onlyOmit 19 (.closed 22))))))))
    (.onlyOmit 14 (.onlyOmit 14 (.onlyOmit 15 (.onlyInclude (.onlyOmit 17 (.onlyOmit 18 (.onlyOmit 21 (.closed 21))))))))))))))))
    (.onlyOmit 5 (.split (.split (.split (.onlyInclude (.split (.split (.graft 12 543 cap5Part193 cap5Part193_checked)
    (.onlyOmit 12 (.onlyOmit 13 (.graft 14 2591 cap5Part200 cap5Part200_checked))))
    (.onlyOmit 11 (.onlyOmit 12 (.onlyOmit 13 (.graft 14 1567 cap5Part202 cap5Part202_checked))))))
    (.graft 9 287 cap5Part217 cap5Part217_checked))
    (.graft 8 159 cap5Part235 cap5Part235_checked))
    (.onlyOmit 7 (.split (.graft 9 95 cap5Part258 cap5Part258_checked)
    (.onlyOmit 9 (.onlyOmit 10 (.graft 11 351 cap5Part263 cap5Part263_checked)))))))))

private def cap5Part264 : Certificate := cap5Part264Block.toCertificate

private theorem cap5Part264_checked : check 5 60 3 7 cap5Part264 = true :=
  checkFragment_sound cap5Part264Block 3 7 (by decide +kernel)

private def cap5Root : Fragment 5 60 :=
  (.onlyInclude (.split (.onlyInclude (.split (.onlyInclude (.split (.onlyInclude (.onlyOmit 8 (.onlyInclude (.onlyOmit 10 (.closed 12)))))
    (.split (.split (.split (.graft 10 107 cap5Part2 cap5Part2_checked)
    (.graft 10 619 cap5Part3 cap5Part3_checked))
    (.onlyOmit 9 (.onlyOmit 11 (.onlyOmit 11 (.split (.graft 13 363 cap5Part8 cap5Part8_checked)
    (.onlyOmit 13 (.split (.graft 15 4459 cap5Part10 cap5Part10_checked)
    (.onlyOmit 15 (.onlyOmit 17 (.onlyOmit 17 (.split (.onlyOmit 20 (.onlyOmit 20 (.onlyInclude (.onlyOmit 22 (.closed 26)))))
    (.onlyOmit 19 (.onlyOmit 20 (.onlyOmit 26 (.split (.onlyOmit 26 (.split (.closed 26)
    (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.split (.onlyOmit 30 (.onlyOmit 30 (.closed 32)))
    (.onlyOmit 29 (.onlyOmit 30 (.onlyOmit 32 (.onlyOmit 32 (.onlyOmit 36 (.onlyOmit 42 (.closed 36)))))))))))))
    (.onlyOmit 23 (.onlyOmit 30 (.onlyOmit 26 (.onlyOmit 26 (.onlyOmit 30 (.split (.closed 30)
    (.onlyOmit 30 (.onlyOmit 30 (.onlyOmit 34 (.onlyOmit 40 (.onlyOmit 34 (.onlyOmit 34 (.closed 36))))))))))))))))))))))))))))
    (.onlyOmit 8 (.graft 9 235 cap5Part22 cap5Part22_checked)))))
    (.graft 5 27 cap5Part87 cap5Part87_checked)))
    (.graft 3 7 cap5Part264 cap5Part264_checked)))

/-- Reified from `cap_5_certificate.json`: 33,595 nodes.
SHA-256: `c012ff8b0609eab32775fe410a5f560217d03cdf9d24c43ad08b0c5fb92e8bde`. -/
def cap5Certificate : Certificate := cap5Root.toCertificate

/-- Kernel computation of the complete cap-5 tree, in proof-carrying blocks. -/
theorem cap5_checked : check 5 60 1 1 cap5Certificate = true :=
  checkFragment_sound cap5Root 1 1 (by decide +kernel)

/-- **Partial finite result, not Erdős–Turán:** coverage of `0..60`
forces some global ordered representation count to exceed 5. -/
theorem cap5_obstruction (A : Set ℕ) (hcov : ∀ n ≤ 60, n ∈ A + A) :
    ∃ n, 5 < sumRep A n :=
  obstruction_of_check 5 60 cap5Certificate cap5_checked A hcov

#print axioms cap5_checked
#print axioms cap5_obstruction
/- END GENERATED FINITE CERTIFICATES -/

end Erdos28.FiniteCertificate

/-
## Verification

From `/workspace/leanproject`:

```
lake env lean -DwarningAsError=true Submission/FiniteCertificate.lean
```

The axiom audits below and after each finite result are part of that compilation.
Their lists are contained in `{propext, Classical.choice, Quot.sound}`.
The generator is optional: all certificate data are already present in this file.
See `Submission/FiniteCertificate.md` for rebuilding and regression-test commands.
-/

#print axioms Erdos28.FiniteCertificate.repCount_eq_sumRep
#print axioms Erdos28.FiniteCertificate.sumRep_mono
#print axioms Erdos28.FiniteCertificate.sumRep_pos_iff
#print axioms Erdos28.FiniteCertificate.maskSet_include
#print axioms Erdos28.FiniteCertificate.Matches.subset
#print axioms Erdos28.FiniteCertificate.Matches.omit
#print axioms Erdos28.FiniteCertificate.Matches.include
#print axioms Erdos28.FiniteCertificate.matches_root
#print axioms Erdos28.FiniteCertificate.omit_count_pos
#print axioms Erdos28.FiniteCertificate.count_le_of_matches
#print axioms Erdos28.FiniteCertificate.check_sound
#print axioms Erdos28.FiniteCertificate.obstruction_of_check

#print axioms Erdos28.FiniteCertificate.checkFragment_sound
