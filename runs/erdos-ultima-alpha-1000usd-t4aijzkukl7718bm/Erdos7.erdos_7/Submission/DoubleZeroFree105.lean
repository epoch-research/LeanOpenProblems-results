import FormalConjecturesUtil

/-!
An obstruction to a STRONGER proposed Fourier construction, not to covering
systems. One cannot choose one annihilated frequency for every nontrivial
divisor of105 while forbidding all nonempty coefficient-0/1/2 zero sums.
-/
namespace Erdos7DoubleZeroFree105
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000

def combo {R : Type*} [Semiring R] {n : ℕ} (v : Fin n → R) (c : Fin n → Fin 3) : R :=
  ∑ i, (c i).val * v i

def Nonzero {n : ℕ} (c : Fin n → Fin 3) : Prop := ∃ i, c i ≠ 0

lemma map_combo {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {n : ℕ} (v : Fin n → R) (c : Fin n → Fin 3) :
    f (combo v c) = combo (fun i => f (v i)) c := by
  simp [combo]

lemma combo_cons {R : Type*} [Semiring R] {n : ℕ} (a : R) (v : Fin n → R)
    (t : Fin 3) (c : Fin n → Fin 3) :
    combo (Fin.cons a v) (Fin.cons t c) = (t.val : R)*a + combo v c := by
  simp [combo, Fin.sum_univ_succ]

lemma zero_entry {R : Type*} [Semiring R] {n : ℕ} (v : Fin n → R)
    (i : Fin n) (hi : v i = 0) : ∃ c : Fin n → Fin 3, Nonzero c ∧ combo v c = 0 := by
  classical
  refine ⟨Pi.single i 1, ⟨i, by simp⟩, ?_⟩
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [Pi.single_apply, hji]

/-- A saturated kernel permits lifting a nonempty short zero sum. -/
lemma lift_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a : R) (hsat : ∀ z, f z = 0 → ∃ t : Fin 3, (t.val : R)*a = z)
    {n : ℕ} (v : Fin n → R) (c : Fin n → Fin 3)
    (hn : Nonzero c) (hc : combo (fun i => f (v i)) c = 0) :
    ∃ d : Fin (n+1) → Fin 3, Nonzero d ∧ combo (Fin.cons a v) d = 0 := by
  have hz : f (-combo v c) = 0 := by rw [map_neg, map_combo, hc, neg_zero]
  obtain ⟨t,ht⟩ := hsat (-combo v c) hz
  refine ⟨Fin.cons t c, ?_, ?_⟩
  · obtain ⟨i,hi⟩ := hn
    exact ⟨i.succ, by simpa using hi⟩
  · rw [combo_cons, ht, neg_add_cancel]

lemma lift_two {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : R) (hsat : ∀ z, f z = 0 →
      ∃ t u : Fin 3, (t.val : R)*a + (u.val : R)*b = z)
    {n : ℕ} (v : Fin n → R) (c : Fin n → Fin 3)
    (hn : Nonzero c) (hc : combo (fun i => f (v i)) c = 0) :
    ∃ d : Fin (n+2) → Fin 3, Nonzero d ∧ combo (Fin.cons a (Fin.cons b v)) d = 0 := by
  have hz : f (-combo v c) = 0 := by rw [map_neg, map_combo, hc, neg_zero]
  obtain ⟨t,u,htu⟩ := hsat (-combo v c) hz
  refine ⟨Fin.cons t (Fin.cons u c), ?_, ?_⟩
  · obtain ⟨i,hi⟩ := hn
    exact ⟨i.succ.succ, by simpa using hi⟩
  · rw [combo_cons, combo_cons, ← add_assoc, htu, neg_add_cancel]

def down35 : ZMod 105 →+* ZMod 35 := ZMod.castHom (by decide : 35 ∣ 105) (ZMod 35)
def down7 : ZMod 35 →+* ZMod 7 := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)

lemma kernel35 : ∀ z : ZMod 105, down35 z = 0 → (3 : ZMod 105)*z = 0 := by decide +kernel
lemma kernel7 : ∀ z : ZMod 35, down7 z = 0 → (5 : ZMod 35)*z = 0 := by decide +kernel
lemma torsion_five : ∀ z : ZMod 105, (5 : ZMod 105)*z = 0 →
    (5 : ZMod 35)*down35 z = 0 := by decide +kernel
lemma torsion_fifteen : ∀ z : ZMod 105, (15 : ZMod 105)*z = 0 →
    (5 : ZMod 35)*down35 z = 0 := by decide +kernel

/-- A nonzero order-three element saturates its three-element subgroup. -/
lemma saturate3 : ∀ a : ZMod 105, (3 : ZMod 105)*a = 0 → a ≠ 0 →
    ∀ z : ZMod 105, (3 : ZMod 105)*z = 0 →
      ∃ t : Fin 3, (t.val : ZMod 105)*a = z := by decide +kernel

/-- Two nonzero order-five elements, each with coefficients0,1,2, saturate
that five-element subgroup. This is a tiny Cauchy-Davenport instance. -/
lemma saturate5 : ∀ a b : ZMod 35,
    (5 : ZMod 35)*a = 0 → (5 : ZMod 35)*b = 0 → a ≠ 0 → b ≠ 0 →
    ∀ z : ZMod 35, (5 : ZMod 35)*z = 0 →
      ∃ t u : Fin 3, (t.val : ZMod 35)*a + (u.val : ZMod 35)*b = z := by decide +kernel

/-- Eight copies of four elements in the group of order7 have a nonempty
zero-sum subcollection. Counts of each original element are at most two. -/
lemma four_in_seven : ∀ v : Fin 4 → ZMod 7,
    ∃ c : Fin 4 → Fin 3, Nonzero c ∧ combo v c = 0 := by
  unfold Nonzero combo
  decide +kernel

lemma six_in_thirty_five (v : Fin 6 → ZMod 35)
    (h0 : (5 : ZMod 35)*v 0 = 0) (h1 : (5 : ZMod 35)*v 1 = 0) :
    ∃ c : Fin 6 → Fin 3, Nonzero c ∧ combo v c = 0 := by
  by_cases hz0 : v 0 = 0
  · exact zero_entry v 0 hz0
  by_cases hz1 : v 1 = 0
  · exact zero_entry v 1 hz1
  let w : Fin 4 → ZMod 35 := Fin.tail (Fin.tail v)
  obtain ⟨c,hn,hc⟩ := four_in_seven (fun i => down7 (w i))
  have hsat : ∀ z, down7 z = 0 → ∃ t u : Fin 3,
      (t.val : ZMod 35)*v 0 + (u.val : ZMod 35)*v 1 = z := by
    intro z hz
    exact saturate5 (v 0) (v 1) h0 h1 hz0 hz1 z (kernel7 z hz)
  have h := lift_two down7 (v 0) (v 1) hsat w c hn hc
  simpa only [w, Fin.cons_self_tail] using h

/-- Only the first three annihilator constraints are needed. -/
theorem seven_in_105 (v : Fin 7 → ZMod 105)
    (h0 : (3 : ZMod 105)*v 0 = 0) (h1 : (5 : ZMod 105)*v 1 = 0)
    (h2 : (15 : ZMod 105)*v 2 = 0) :
    ∃ c : Fin 7 → Fin 3, Nonzero c ∧ combo v c = 0 := by
  by_cases hz0 : v 0 = 0
  · exact zero_entry v 0 hz0
  let w : Fin 6 → ZMod 105 := Fin.tail v
  obtain ⟨c,hn,hc⟩ := six_in_thirty_five (fun i => down35 (w i))
    (by simpa [w] using torsion_five (v 1) h1)
    (by simpa [w] using torsion_fifteen (v 2) h2)
  have hsat : ∀ z, down35 z = 0 → ∃ t : Fin 3, (t.val : ZMod 105)*v 0 = z := by
    intro z hz
    exact saturate3 (v 0) h0 hz0 z (kernel35 z hz)
  have h := lift_one down35 (v 0) hsat w c hn hc
  simpa only [w, Fin.cons_self_tail] using h

def modulus : Fin 7 → ℕ := ![3,5,15,7,21,35,105]

/-- This refutes only the coefficient-0/1/2 strengthening of a proposed
frequency construction. Ordinary zero-sum-free selection uses coefficients
0/1 only and is NOT refuted by this theorem. -/
theorem not_double_zero_free : ¬ ∃ k : Fin 7 → ZMod 105,
    (∀ i, (modulus i : ZMod 105)*k i = 0) ∧
    (∀ c : Fin 7 → Fin 3, combo k c = 0 → ∀ i, c i = 0) := by
  rintro ⟨k,hm,hf⟩
  obtain ⟨c,⟨i,hi⟩,hc⟩ := seven_in_105 k
    (by simpa [modulus] using hm 0)
    (by simpa [modulus] using hm 1)
    (by simpa [modulus] using hm 2)
  exact hi (hf c hc i)

#print axioms saturate5
#print axioms four_in_seven
#print axioms seven_in_105
#print axioms not_double_zero_free
end Erdos7DoubleZeroFree105
