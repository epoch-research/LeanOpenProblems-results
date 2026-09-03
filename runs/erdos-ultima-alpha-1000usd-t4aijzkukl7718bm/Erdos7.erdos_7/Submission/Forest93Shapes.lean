import Submission.Forest93Certificate

/-! Encoding the complete finite exponent rectangle for the forest certificate. -/
namespace Erdos7Forest93Shapes
open scoped BigOperators
open Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option autoImplicit false

abbrev Pattern := Fin 3 × (Fin 7 → Fin 2)
def encode (v : Pattern) : ℕ := v.1.val*128+(∑ j,(v.2 j).val*2^(6-j.val))
lemma encode_lt : ∀ v,encode v < 384 := by decide +kernel
def index (v : Pattern) : Index := ⟨encode v,encode_lt v⟩
def decode (i : Index) : Pattern :=
  (⟨i.val/128,by have := i.isLt; omega⟩,
    fun j => ⟨i.val/2^(6-j.val)%2,Nat.mod_lt _ (by decide)⟩)
lemma decode_index : ∀ v,decode (index v) = v := by decide +kernel
lemma index_decode : ∀ i,index (decode i) = i := by decide +kernel

def exponent (i : Index) : Fin 8 → ℕ := Fin.cases (decode i).1.val (fun j => ((decode i).2 j).val)
def primes : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
def caps : Fin 8 → ℕ := ![2,1,1,1,1,1,1,1]
def support (i : Index) : Finset (Fin 8) := Finset.univ.filter (fun j => exponent i j ≠ 0)
def mixed (i : Index) : Prop := 2 ≤ (support i).card
instance (i : Index) : Decidable (mixed i) := inferInstanceAs (Decidable (2 ≤ (support i).card))
def modulus (i : Index) : ℕ := ∏ j,primes j^exponent i j

def sectionNum (i : Index) (j : Fin 8) : ℕ := if j = 0 ∧ exponent i j = 1 then 3 else 1
def sectionDen (i : Index) (j : Fin 8) : ℕ :=
  if exponent i j = 0 then 1 else if j = 0 then 5 else primes j-1
def sectionBound (i : Index) (j : Fin 8) : ℚ := sectionNum i j/sectionDen i j

lemma exponent_le : ∀ i j,exponent i j ≤ caps j := by decide +kernel
lemma sectionDen_pos : ∀ i j,0 < sectionDen i j := by decide +kernel
lemma weight_cross : ∀ i,weightNum i*(∏ j,sectionDen i j) =
    if mixed i then denominator*(∏ j,sectionNum i j) else 0 := by decide +kernel
lemma ordinary_disjoint : ∀ e : ordinary,∀ j,
    exponent e.val.1 j = 0 ∨ exponent e.val.2 j = 0 := by decide +kernel
lemma pivot_exponents : exponent 192 = ![1,1,0,0,0,0,0,0] ∧
    exponent 160 = ![1,0,1,0,0,0,0,0] := by decide +kernel
lemma pivot_moduli : modulus 192 = 15 ∧ modulus 160 = 21 := by decide +kernel
lemma pivot_weights : weight 192 = 3/20 ∧ weight 160 = 1/10 := by decide +kernel
lemma prime_properties : Function.Injective primes ∧ ∀ j,(primes j).Prime ∧ Odd (primes j) := by
  decide +kernel

lemma weight_product (i : Index) (hi : mixed i) : weight i = ∏ j,sectionBound i j := by
  have hh := weight_cross i
  rw [if_pos hi] at hh
  have hd : (∏ j,(sectionDen i j:ℚ)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact_mod_cast sectionDen_pos i j
  have hq : (weightNum i:ℚ)*(∏ j,(sectionDen i j:ℚ)) =
      (denominator:ℚ)*(∏ j,(sectionNum i j:ℚ)) := by exact_mod_cast hh
  unfold weight sectionBound
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff denominator_ne hd).mpr
  nlinarith

lemma weight_zero (i : Index) (hi : ¬mixed i) : weight i = 0 := by
  have hh := weight_cross i
  rw [if_neg hi] at hh
  have hd : 0 < ∏ j,sectionDen i j := Finset.prod_pos (fun j _ => sectionDen_pos i j)
  have hn : weightNum i = 0 := (Nat.mul_eq_zero.mp hh).resolve_right (ne_of_gt hd)
  simp [weight,hn]

lemma exponent_index (v : Pattern) : exponent (index v) = Fin.cases v.1.val (fun j => (v.2 j).val) := by
  unfold exponent
  rw [decode_index]

#print axioms weight_product
#print axioms ordinary_disjoint
#print axioms decode_index
end Erdos7Forest93Shapes
