import Submission.AdaptiveTailClosure

/-! An odd, divisor-closed partial arithmetic family with private points.
Both fixed tail deletions force modulus collisions, even with prefix-dependent
values. A branch-dependent choice of deletion position has no collision.
Integer2 is uncovered. This example is NOT an odd covering system. -/
namespace Erdos7AdaptiveTailExample
open Erdos7AdaptiveTailClosure
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

def modulus : Fin 24 → ℕ := ![3,9,27,5,15,45,7,21,63,11,33,99,13,39,117,351,17,51,153,459,19,57,171,513]
def residueN : Fin 24 → ℕ := ![0,8,4,0,11,1,0,8,22,0,23,34,0,1,14,326,0,1,86,443,0,1,77,20]
def residue (i : Fin 24) : ℤ := residueN i
def exponent : Fin 24 → ℕ := ![1,2,3,0,1,2,0,1,2,0,1,2,0,1,2,3,0,1,2,3,0,1,2,3]
def privatePoint : Fin 24 → ℤ := ![17782767,33948917,25865842,26189165,34918886,21985966,12471032,6235517,17551822,11904167,27776387,5143777,16787927,17285347,25368422,30218267,20540522,40985947,5420417,39369332,25270247,21526507,29609582,5360357]

theorem arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 43648605) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) := by
  decide +kernel

lemma bounded_divisor_data :
    ∀ i : Fin 24, ∀ d : Fin 514, 1 < d.val → d.val ∣ modulus i →
      ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 24) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1<d) :
    ∃ j, modulus j=d := by
  have hm : ∀ i : Fin 24, modulus i < 514 := by decide +kernel
  have hmi := hm i
  have hp : 0 < modulus i := lt_trans (by omega : 0<1) (arithmetic_data.2.1 i).1
  have hle := Nat.le_of_dvd hp hd
  exact bounded_divisor_data i ⟨d,by omega⟩ h1 hd

def digit (i : Fin 24) (t : ℕ) : ℕ := residueN i / 3^t % 3

def first (i : Fin 24) : Fin 3 := ⟨residueN i%3,Nat.mod_lt _ (by decide)⟩
def firstTwo (i : Fin 24) : Fin 9 := ⟨residueN i%9,Nat.mod_lt _ (by decide)⟩

def middleUpper (c : Fin 3) : Fin 24 := ⟨3+3*c.val+2,by omega⟩
def middleLower (c : Fin 3) : Fin 24 := ⟨3+3*c.val+1,by omega⟩
def topUpper (c : Fin 3) : Fin 24 := ⟨12+4*c.val+3,by omega⟩
def topLower (c : Fin 3) : Fin 24 := ⟨12+4*c.val+2,by omega⟩

def fixedModulus (t : ℕ) (i : Fin 24) : ℕ :=
  if t < exponent i then modulus i/3 else modulus i

def middleActive (f : Fin 3 → Fin 3) (i : Fin 24) : Prop :=
  exponent i ≤ 1 ∨ digit i 1 = (f (first i)).val

def topActive (f : Fin 9 → Fin 3) (i : Fin 24) : Prop :=
  exponent i ≤ 2 ∨ digit i 2 = (f (firstTwo i)).val

lemma middle_data : ∀ c : Fin 3,
    middleUpper c ≠ middleLower c ∧
    exponent (middleUpper c)=2 ∧ exponent (middleLower c)=1 ∧
    first (middleUpper c)=1 ∧ digit (middleUpper c) 1=c.val ∧
    fixedModulus 1 (middleUpper c)=fixedModulus 1 (middleLower c) := by
  decide +kernel

lemma top_data : ∀ c : Fin 3,
    topUpper c ≠ topLower c ∧
    exponent (topUpper c)=3 ∧ exponent (topLower c)=2 ∧
    firstTwo (topUpper c)=2 ∧ digit (topUpper c) 2=c.val ∧
    fixedModulus 2 (topUpper c)=fixedModulus 2 (topLower c) := by
  decide +kernel

/-- No prefix-dependent value selection at the middle fixed position preserves
modulus distinctness. -/
theorem every_middle_choice_collides (f : Fin 3 → Fin 3) :
    ∃ k l, k ≠ l ∧ middleActive f k ∧ middleActive f l ∧
      fixedModulus 1 k = fixedModulus 1 l := by
  obtain ⟨hne,hku,hkl,hf,hd,hm⟩ := middle_data (f 1)
  refine ⟨middleUpper (f 1),middleLower (f 1),hne,Or.inr ?_,Or.inl ?_,hm⟩
  · rw [hf,hd]
  · omega

/-- The analogous obstruction also holds for the highest fixed position. -/
theorem every_top_choice_collides (f : Fin 9 → Fin 3) :
    ∃ k l, k ≠ l ∧ topActive f k ∧ topActive f l ∧
      fixedModulus 2 k = fixedModulus 2 l := by
  obtain ⟨hne,hku,hkl,hf,hd,hm⟩ := top_data (f 2)
  refine ⟨topUpper (f 2),topLower (f 2),hne,Or.inr ?_,Or.inl ?_,hm⟩
  · rw [hf,hd]
  · omega

def position (i : Fin 24) : ℕ := if first i = 2 then 1 else 2

def adaptiveActive (i : Fin 24) : Prop :=
  exponent i ≤ position i ∨ digit i (position i) = (if position i=1 then 0 else 1)
instance (i : Fin 24) : Decidable (adaptiveActive i) := inferInstanceAs (Decidable (_ ∨ _))

def adaptiveModulus (i : Fin 24) : ℕ := fixedModulus (position i) i

/-- In contrast, one explicit adaptive policy leaves nineteen nontrivial,
odd, pairwise distinct projected moduli. -/
theorem adaptive_safe :
    (∀ i, adaptiveActive i → 1 < adaptiveModulus i ∧ Odd (adaptiveModulus i)) ∧
    (∀ i j, adaptiveActive i → adaptiveActive j →
      adaptiveModulus i=adaptiveModulus j → i=j) ∧
    (Finset.univ.filter adaptiveActive).card = 19 := by
  decide +kernel

/-- These marks use actual modulus companions and actual ternary residues. -/
def Middle (u v : Fin 3) : Prop :=
  ∃ k l : Fin 24, exponent k=2 ∧ exponent l=1 ∧ modulus k=3*modulus l ∧
    first k=u ∧ digit k 1=v.val

def Upper (u v r w : Fin 3) : Prop :=
  ∃ k l : Fin 24, exponent k=3 ∧ exponent l=2 ∧ modulus k=3*modulus l ∧
    first k=u ∧ digit k 1=v.val ∧ digit k 2=r.val ∧ first l=w

instance (u v : Fin 3) : Decidable (Middle u v) := inferInstanceAs (Decidable (∃ _ _, _))
instance (u v r w : Fin 3) : Decidable (Upper u v r w) := inferInstanceAs (Decidable (∃ _ _, _))

lemma middle_one : ∀ v : Fin 3, Middle 1 v := by decide +kernel
lemma singleton_closed : Closed Middle Upper ({1} : Set (Fin 3)) := by
  unfold Closed Blocked
  decide +kernel
lemma singleton_nonterminal : ¬ Terminal Upper ({1} : Set (Fin 3)) := by
  unfold Terminal
  decide +kernel

theorem frozen_eq : Frozen Middle Upper = ({1} : Set (Fin 3)) := by
  apply Set.Subset.antisymm
  · exact frozen_le Middle Upper singleton_closed
  · intro u hu
    have hu' : u=1 := hu
    subst u
    exact frozen_closed Middle Upper 1 (fun v => Or.inl (middle_one v))

theorem frozen_nonterminal : ¬ Terminal Upper (Frozen Middle Upper) := by
  rw [frozen_eq]
  exact singleton_nonterminal

#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms every_middle_choice_collides
#print axioms every_top_choice_collides
#print axioms adaptive_safe
#print axioms frozen_eq
#print axioms frozen_nonterminal
end Erdos7AdaptiveTailExample
