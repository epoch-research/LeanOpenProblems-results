import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Logic.Relation
import Mathlib.Tactic.IntervalCases

/-!
# A kernel-reducible checker for the supplied black wall

Coordinates in this file are the `w` coordinates of `z = 1 + (1 + i) * w`.
Blackness is exactly the ten congruence tests supplied with `black_wall.json`.
No primality search, external evaluation, or facts about arbitrary step bounds
are used here.

A certificate contains one ASCII byte per vertex: `48 + 4 * label + direction`.
Thus the alphabet is the forty characters from `0` through `W`, inclusive.
Directions 0, 1, 2, 3 mean east, north, west, south. An `n`-edge certificate
has exactly `n + 1` bytes. The last byte's label IS checked; its direction is
NOT followed. Chunks overlap at their single common endpoint.
-/

namespace Erdos952.WallData

/-- The exact modular predicate associated to each of the ten divisor labels.
Labels outside `0,...,9` are rejected. -/
def LabelBlack (x y : ℤ) : ℕ → Prop
  | 0 => (1 + x - y) % 3 = 0 ∧ (x + y) % 3 = 0
  | 1 => (1 - x - 3 * y) % 5 = 0
  | 2 => (1 + 3 * x + y) % 5 = 0
  | 3 => (1 + 6 * x + 4 * y) % 13 = 0
  | 4 => (1 - 4 * x - 6 * y) % 13 = 0
  | 5 => (1 - 3 * x - 5 * y) % 17 = 0
  | 6 => (1 + 5 * x + 3 * y) % 17 = 0
  | 7 => (1 + 13 * x + 11 * y) % 29 = 0
  | 8 => (1 - 11 * x - 13 * y) % 29 = 0
  | 9 => (1 - 5 * x - 7 * y) % 37 = 0
  | _ => False

/-- Blackness in the `w` lattice, not a primality assertion about `w`. -/
def Black (w : GaussianInt) : Prop := ∃ label : ℕ, LabelBlack w.re w.im label

/-- A black nearest-neighbor edge in the `w` lattice. -/
def BlackStep (p q : GaussianInt) : Prop := Black p ∧ Black q ∧ (q - p).norm = 1

/-- An exact-length finite path, including blackness of a zero-edge path's vertex.
This is a proposition: certificate checking never constructs a list of positions. -/
inductive BlackPath : ℕ → GaussianInt → GaussianInt → Prop
  | single {p : GaussianInt} : Black p → BlackPath 0 p p
  | cons {n : ℕ} {p q r : GaussianInt} :
      BlackStep p q → BlackPath n q r → BlackPath (n + 1) p r

namespace BlackPath

theorem black_start {n : ℕ} {p q : GaussianInt} (h : BlackPath n p q) : Black p := by
  cases h with
  | single hb => exact hb
  | cons hs _ => exact hs.1

theorem black_end {n : ℕ} {p q : GaussianInt} (h : BlackPath n p q) : Black q := by
  induction h with
  | single hb => exact hb
  | cons _ _ ih => exact ih

/-- Concatenation adds the edge counts, without adding an edge at the shared vertex. -/
theorem append {m n : ℕ} {p q r : GaussianInt}
    (h : BlackPath m p q) (k : BlackPath n q r) : BlackPath (m + n) p r := by
  induction h with
  | single _ => simpa using k
  | cons hs _ ih => simpa [Nat.succ_add] using BlackPath.cons hs (ih k)

/-- Forgetting the length gives the requested reflexive-transitive closure. -/
theorem toRTC {n : ℕ} {p q : GaussianInt} (h : BlackPath n p q) :
    Relation.ReflTransGen BlackStep p q := by
  induction h with
  | single _ => exact .refl
  | cons hs _ ih => exact ih.head hs

end BlackPath

/-- Boolean versions of the ten exact integer congruence tests. -/
def labelCheck (x y : ℤ) : ℕ → Bool
  | 0 => ((1 + x - y) % 3 == 0) && ((x + y) % 3 == 0)
  | 1 => (1 - x - 3 * y) % 5 == 0
  | 2 => (1 + 3 * x + y) % 5 == 0
  | 3 => (1 + 6 * x + 4 * y) % 13 == 0
  | 4 => (1 - 4 * x - 6 * y) % 13 == 0
  | 5 => (1 - 3 * x - 5 * y) % 17 == 0
  | 6 => (1 + 5 * x + 3 * y) % 17 == 0
  | 7 => (1 + 13 * x + 11 * y) % 29 == 0
  | 8 => (1 - 11 * x - 13 * y) % 29 == 0
  | 9 => (1 - 5 * x - 7 * y) % 37 == 0
  | _ => false

theorem labelCheck_sound (x y : ℤ) (label : ℕ)
    (h : labelCheck x y label = true) : LabelBlack x y label := by
  unfold labelCheck at h
  split at h <;> simp_all [LabelBlack]

/-- Decode the forty-character alphabet. The range check is separate. -/
def code (c : UInt8) : ℕ := c.toNat - 48

/-- Check the byte range and the supplied label at the current vertex. -/
def vertexCheck (c : UInt8) (p : GaussianInt) : Bool :=
  (48 ≤ c.toNat && c.toNat < 88) && labelCheck p.re p.im (code c / 4)

theorem vertexCheck_sound {c : UInt8} {p : GaussianInt}
    (h : vertexCheck c p = true) : Black p := by
  exact ⟨code c / 4, labelCheck_sound _ _ _ (Bool.and_eq_true_iff.mp h).2⟩

/-- Move one unit in one of the four directions. Only inputs below four are used. -/
def move (p : GaussianInt) : ℕ → GaussianInt
  | 0 => ⟨p.re + 1, p.im⟩
  | 1 => ⟨p.re, p.im + 1⟩
  | 2 => ⟨p.re - 1, p.im⟩
  | _ => ⟨p.re, p.im - 1⟩

theorem move_norm (p : GaussianInt) (d : ℕ) (hd : d < 4) :
    (move p d - p).norm = 1 := by
  interval_cases d <;> simp [move, Zsqrtd.norm]

/-- The generic recursive checker. The natural number counts EDGES.
In the zero-edge case there must be exactly one remaining vertex byte. -/
def checkBytes (target : GaussianInt) : ℕ → List UInt8 → GaussianInt → Bool
  | 0, [c], p => vertexCheck c p && (p.re == target.re && p.im == target.im)
  | n + 1, c :: cs, p =>
      vertexCheck c p && checkBytes target n cs (move p (code c % 4))
  | _, _, _ => false

/-- Every accepting byte certificate gives a black path of exactly the claimed length. -/
theorem checkBytes_sound (target : GaussianInt) (n : ℕ) (cs : List UInt8)
    (p : GaussianInt) (h : checkBytes target n cs p = true) : BlackPath n p target := by
  induction n generalizing cs p with
  | zero =>
      cases cs with
      | nil => simp [checkBytes] at h
      | cons c cs =>
          cases cs with
          | nil =>
              simp only [checkBytes, Bool.and_eq_true, beq_iff_eq] at h
              have hp : p = target := Zsqrtd.ext h.2.1 h.2.2
              subst target
              exact .single (vertexCheck_sound h.1)
          | cons d ds => simp [checkBytes] at h
  | succ n ih =>
      cases cs with
      | nil => simp [checkBytes] at h
      | cons c cs =>
          have hh := Bool.and_eq_true_iff.mp h
          have ht := ih cs (move p (code c % 4)) hh.2
          exact .cons ⟨vertexCheck_sound hh.1, ht.black_start,
            move_norm p _ (Nat.mod_lt _ (by decide))⟩ ht

/-- Check a compact ASCII certificate using only kernel-reducible definitions. -/
def checkChunk (n : ℕ) (data : String) (start finish : GaussianInt) : Bool :=
  checkBytes finish n data.toByteArray.data.toList start

/-- The only certificate interface needed by generated chunks. -/
theorem checkChunk_sound {n : ℕ} {data : String} {start finish : GaussianInt}
    (h : checkChunk n data start finish = true) : BlackPath n start finish :=
  checkBytes_sound finish n data.toByteArray.data.toList start h

/-- A direct RTC interface, for clients that do not need exact edge counts. -/
theorem checkChunk_rtc {n : ℕ} {data : String} {start finish : GaussianInt}
    (h : checkChunk n data start finish = true) :
    Relation.ReflTransGen (fun p q : GaussianInt => Black p ∧ Black q ∧ (q - p).norm = 1)
      start finish :=
  (checkChunk_sound h).toRTC

end Erdos952.WallData
