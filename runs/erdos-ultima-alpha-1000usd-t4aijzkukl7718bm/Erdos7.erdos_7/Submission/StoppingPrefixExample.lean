import Submission.StoppingPolicyArithmetic

/-! A divisor-closed odd partial family with private points, terminal full
ternary stopping closure, and a common top collision fiber. Integer2 is a hole.
Thus these single-coordinate obstructions alone do not imply a cover. -/
namespace Erdos7StoppingPrefixExample
open Erdos7StoppingPrefixClosure Erdos7StoppingPrefixArithmetic
open Erdos7StoppingDigitRestriction Erdos7StoppingPolicyArithmetic
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

def modulus : Fin 8 → ℕ := ![3,9,5,15,45,7,21,63]
def residueN : Fin 8 → ℕ := ![0,1,0,1,22,0,8,16]
def residue (i : Fin 8) : ℤ := residueN i
def privatePoint : Fin 8 → ℤ := ![3,19,5,31,22,7,8,79]
def primes : Fin 3 → ℕ := ![3,5,7]
def caps : Fin 3 → ℕ := ![2,1,1]
def exponents : Fin 8 → Fin 3 → ℕ :=
  ![![1,0,0],![2,0,0],![0,1,0],![1,1,0],![2,1,0],![0,0,1],![1,0,1],![2,0,1]]
instance (i : Fin 3) : NeZero (primes i) := ⟨by fin_cases i <;> decide⟩

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 315) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) ∧
    (∀ i, modulus i = ∏ j, primes j ^ exponents i j) := by
  decide +kernel

lemma bounded_divisor_data : ∀ i : Fin 8, ∀ d : Fin 64,
    1 < d.val → d.val ∣ modulus i → ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 8) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1<d) :
    ∃ j, modulus j=d := by
  have hm : ∀ i : Fin 8, modulus i < 64 := by decide +kernel
  have hp : 0 < modulus i := lt_trans (by omega : 0<1) (arithmetic_data.2.1 i).1
  have hle := Nat.le_of_dvd hp hd
  have hmi := hm i
  exact bounded_divisor_data i ⟨d,by omega⟩ h1 hd

abbrev Mark := Block primes caps 0 exponents residue
abbrev F := Frozen (show 0 < caps 0 by decide) Mark

lemma root_block : ∀ r : Fin 3,
    Mark ({root (show 0 < caps 0 by decide)} : Set (Node (caps 0) (Fin (primes 0))))
      (root (show 0 < caps 0 by decide)) r := by
  intro r
  fin_cases r
  · refine ⟨(0 : Fin 8),by decide,?_,by decide,Or.inl (by decide)⟩
    exact node_zero _ _
  · refine ⟨(3 : Fin 8),by decide,?_,by decide,Or.inr ⟨(2 : Fin 8),by decide,
      by decide,by decide,?_⟩⟩
    · exact node_zero _ _
    · exact node_zero _ _
  · refine ⟨(6 : Fin 8),by decide,?_,by decide,Or.inr ⟨(5 : Fin 8),by decide,
      by decide,by decide,?_⟩⟩
    · exact node_zero _ _
    · exact node_zero _ _

/-- Root forcing reaches all three last-depth prefixes. -/
theorem frozen_eq_univ : F = Set.univ := by
  ext u
  simp only [Set.mem_univ,iff_true]
  have hclosed := frozen_closed (show 0 < caps 0 by decide) Mark
    (fun hBC => block_mono primes caps 0 exponents residue hBC)
  have hroot : root (show 0 < caps 0 by decide) ∈ F := hclosed.1
  have hsub : ({root (show 0 < caps 0 by decide)} : Set (Node (caps 0) (Fin (primes 0)))) ⊆ F := by
    intro v hv
    have hv' : v = root (show 0 < caps 0 by decide) := hv
    rwa [hv']
  have hblock : ∀ r, Mark F (root (show 0 < caps 0 by decide)) r :=
    fun r => block_mono primes caps 0 exponents residue hsub (root_block r)
  rcases u with ⟨t,v⟩
  change Fin 2 at t
  fin_cases t
  · have hv : (⟨(0 : Fin 2),v⟩ : Node 2 (Fin 3)) = root (by decide) := by
      apply congrArg (fun w : Fin 0 → Fin 3 => (⟨(0 : Fin 2),w⟩ : Node 2 (Fin 3)))
      funext j
      exact j.elim0
    change (⟨(0 : Fin 2),v⟩ : Node 2 (Fin 3)) ∈ F
    rw [hv]
    exact hroot
  · let x : Fin 2 → Fin 3 := ![v 0,0]
    have hv : node x (1 : Fin 2) = (⟨(1 : Fin 2),v⟩ : Node 2 (Fin 3)) := by
      apply congrArg (fun w : Fin 1 → Fin 3 => (⟨(1 : Fin 2),w⟩ : Node 2 (Fin 3)))
      funext j
      fin_cases j
      rfl
    have hzero : node x (0 : Fin 2) = root (show 0 < caps 0 by decide) := node_zero _ _
    have hh := hclosed.2 x (0 : Fin 2) (by decide)
      (by rw [hzero]; exact hroot) (fun r => by rw [hzero]; exact hblock r)
    change node x (1 : Fin 2) ∈ F at hh
    rw [hv] at hh
    exact hh

lemma full_terminal : Terminal (show 0 < caps 0 by decide) Mark Set.univ := by
  refine ⟨(![1,0] : Fin 2 → Fin 3),Set.mem_univ _,?_⟩
  intro r
  fin_cases r
  · refine ⟨(1 : Fin 8),by decide,?_,by decide,
      Or.inr ⟨(0 : Fin 8),by decide,by decide,by decide,Set.mem_univ _⟩⟩
    apply node_agree
    intro j hj
    change j.val < 1 at hj
    fin_cases j <;> first | decide | norm_num at hj
  · refine ⟨(4 : Fin 8),by decide,?_,by decide,
      Or.inr ⟨(3 : Fin 8),by decide,by decide,by decide,Set.mem_univ _⟩⟩
    apply node_agree
    intro j hj
    change j.val < 1 at hj
    fin_cases j <;> first | decide | norm_num at hj
  · refine ⟨(7 : Fin 8),by decide,?_,by decide,
      Or.inr ⟨(6 : Fin 8),by decide,by decide,by decide,Set.mem_univ _⟩⟩
    apply node_agree
    intro j hj
    change j.val < 1 at hj
    fin_cases j <;> first | decide | norm_num at hj

theorem frozen_terminal : Terminal (show 0 < caps 0 by decide) Mark F := by
  rw [frozen_eq_univ]
  exact full_terminal

def upper : Fin 3 → Fin 8 := ![1,4,7]
def lower : Fin 3 → Fin 8 := ![0,3,6]

/-- This is one literal projected integer, not separately chosen residues. -/
theorem common_fiber_data : ∀ r : Fin 3,
    exponents (upper r) 0 = 2 ∧ exponents (lower r) 0 = 1 ∧
    modulus (upper r) = 3*modulus (lower r) ∧
    residueN (upper r)%3=1 ∧ residueN (upper r)/3%3=r.val ∧
    (modulus (lower r) : ℤ) ∣ 37-residue (upper r) ∧
    ¬ (modulus (lower r) : ℤ) ∣ 37-residue (lower r) := by
  decide +kernel

/-- Even the full class of predictable stopping policies cannot make a
strict nonunit ternary image of this partial family. -/
theorem no_ternary_safe_stopping (T : (Fin 2 → Fin 3) → Fin 2)
    (V : (Fin 2 → Fin 3) → Fin 3) (hT : Predictable T) (hV : PredictableValue T V) :
    ¬ StrictImage primes caps 0 exponents residue T V := by
  intro hS
  have hei : Function.Injective exponents := by
    intro k l hkl
    apply arithmetic_data.1
    rw [arithmetic_data.2.2.2.2 k,arithmetic_data.2.2.2.2 l,hkl]
  have he0 : ∀ k, ∃ i, exponents k i ≠ 0 := by decide +kernel
  exact (exists_strict_image_iff primes caps 0 exponents residue hei he0 (by decide)).mp
    ⟨T,V,hT,hV,hS⟩ frozen_terminal

theorem not_cover : ¬ ∀ x : ℤ, ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  intro hc
  obtain ⟨i,hi⟩ := hc 2
  exact arithmetic_data.2.2.2.1 i hi

#print axioms no_ternary_safe_stopping
#print axioms not_cover

#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms frozen_eq_univ
#print axioms frozen_terminal
#print axioms common_fiber_data
end Erdos7StoppingPrefixExample
