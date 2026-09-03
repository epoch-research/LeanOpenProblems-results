import Submission.PeriodicBarrier

/-! Soundness of bit-mask certificates for periodic barriers. -/

namespace Erdos952Investigation.BitsetBarrier

set_option maxHeartbeats 0

/-- All cyclic neighbors of a bit; extra high bits are harmless. -/
def dilate (M s : ℕ) : ℕ :=
  s ||| (s <<< 1) ||| (s >>> 1) ||| (s >>> (M - 1)) ||| (s <<< (M - 1))

def CloseIndex (M i j : ℕ) : Prop :=
  i = j ∨ j = i + 1 ∨ i = j + 1 ∨ (i = M - 1 ∧ j = 0) ∨ (i = 0 ∧ j = M - 1)

lemma dilate_mem {M s i j : ℕ} (hs : s.testBit i = true) (h : CloseIndex M i j) :
    (dilate M s).testBit j = true := by
  rcases h with rfl | rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp_all [dilate, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.add_comm]

lemma closeIndex_symm {M i j : ℕ} (h : CloseIndex M i j) : CloseIndex M j i := by
  unfold CloseIndex at *
  omega

lemma close_mod_succ (M : ℕ) (hM : 0 < M) (v : ℤ) :
    CloseIndex M (v % (M : ℤ)).toNat ((v + 1) % (M : ℤ)).toNat := by
  have hm : (0 : ℤ) < M := by exact_mod_cast hM
  have hv0 := Int.emod_nonneg v (ne_of_gt hm)
  have hv1 := Int.emod_lt_of_pos v hm
  have he : (v + 1) % (M : ℤ) = (v % (M : ℤ) + 1) % (M : ℤ) := (Int.emod_add_emod v M 1).symm
  by_cases ht : v % (M : ℤ) + 1 = M
  · rw [he, ht, Int.emod_self]
    apply Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    constructor <;> omega
  · have hv2 : v % (M : ℤ) + 1 < M := by omega
    rw [he, Int.emod_eq_of_lt (by omega) hv2]
    exact Or.inr (Or.inl (by omega))

lemma close_mod (M : ℕ) (hM : 0 < M) (v w : ℤ) (h : |w - v| ≤ 1) :
    CloseIndex M (v % (M : ℤ)).toNat (w % (M : ℤ)).toNat := by
  have hcases : w = v ∨ w = v + 1 ∨ v = w + 1 := by have := abs_le.mp h; omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact close_mod_succ M hM v
  · exact closeIndex_symm (close_mod_succ M hM w)

def rowNeighbors (S : ℕ → ℕ) (r : ℕ) : ℕ :=
  (if r = 0 then 0 else S (r - 1)) ||| S r ||| S (r + 1)

lemma rowNeighbors_mem {S : ℕ → ℕ} {i r c : ℕ} (h : (S i).testBit c = true)
    (hir : i ≤ r + 1) (hri : r ≤ i + 1) : (rowNeighbors S r).testBit c = true := by
  have hcases : i = r ∨ i = r + 1 ∨ r = i + 1 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    simp_all [rowNeighbors, Nat.testBit_lor]

lemma covered_mem {M a s t i j : ℕ}
    (hcover : (dilate M s &&& a) ||| t = t)
    (hs : s.testBit i = true) (ha : a.testBit j = true) (hij : CloseIndex M i j) :
    t.testBit j = true := by
  have hd := dilate_mem hs hij
  have he := congrArg (fun n : ℕ => n.testBit j) hcover
  simpa only [Nat.testBit_lor, Nat.testBit_land, hd, ha, Bool.and_self,
    Bool.true_or] using he.symm

def bitset_barrier {A : ℤ × ℤ → Prop} (M H : ℕ) (hM : 0 < M) (hH : 0 < H)
    (bits S : ℕ → ℕ)
    (hzero : ∀ r, H ≤ r → S r = 0)
    (hallowed : ∀ r : ℕ, r ≤ H → ∀ c : ℤ,
      A ((r : ℤ), c) → (bits r).testBit (c % (M : ℤ)).toNat = true)
    (hstart : bits 0 ||| S 0 = S 0)
    (hcover : ∀ r, r ≤ H →
      (dilate M (rowNeighbors S r) &&& bits r) ||| S r = S r) :
    PeriodicBarrier.Barrier A := by
  refine ⟨H, Int.natCast_nonneg H,
    {z | 0 ≤ z.1 ∧ (S z.1.toNat).testBit (z.2 % (M : ℤ)).toNat = true}, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨by simp, ?_⟩
    have hb := hallowed 0 (Nat.zero_le H) c hc
    have he := congrArg (fun n : ℕ => n.testBit (c % (M : ℤ)).toNat) hstart
    simpa only [Nat.testBit_lor, hb, Bool.true_or] using he.symm
  · intro z hz
    have hn : z.1.toNat < H := by
      by_contra h
      have he := hzero z.1.toNat (by omega)
      have ht := hz.2
      rw [he, Nat.zero_testBit] at ht
      contradiction
    have ht := Int.toNat_of_nonneg hz.1
    omega
  · intro z hz w _ hw hs hw0
    refine ⟨hw0, ?_⟩
    have hn : z.1.toNat < H := by
      by_contra h
      have he := hzero z.1.toNat (by omega)
      have ht := hz.2
      rw [he, Nat.zero_testBit] at ht
      contradiction
    have hdiff := abs_le.mp hs.1
    have hwr : w.1.toNat ≤ H := by omega
    have hb : (bits w.1.toNat).testBit (w.2 % (M : ℤ)).toNat = true := by
      apply hallowed _ hwr _
      simpa only [Int.toNat_of_nonneg hw0] using hw
    apply covered_mem (hcover _ hwr) (rowNeighbors_mem hz.2 (by omega) (by omega)) hb
    exact close_mod M hM _ _ hs.2

#print axioms bitset_barrier

end Erdos952Investigation.BitsetBarrier
