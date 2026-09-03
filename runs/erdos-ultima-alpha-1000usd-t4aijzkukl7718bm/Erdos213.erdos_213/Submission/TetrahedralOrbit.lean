import Mathlib.Tactic

/-! Exact tetrahedral-orbit formulas and the diagonal coplanarity obstruction.
This file does not assert an admissible non-diagonal arithmetic parameter. -/

set_option Elab.async false

namespace Erdos213.TetrahedralOrbit

def point {R : Type*} [CommRing R] (a b c : R) : Fin 12 → Fin 3 → R :=
  ![![a,b,c],![a,-b,-c],![-a,b,-c],![-a,-b,c],![b,c,a],![b,-c,-a],![-b,c,-a],![-b,-c,a],![c,a,b],![c,-a,-b],![-c,a,-b],![-c,-a,b]]

def chordSq {R : Type*} [CommRing R] (a b c : R) (i j : Fin 12) : R :=
  (point a b c i 0-point a b c j 0)^2 +
  (point a b c i 1-point a b c j 1)^2 +
  (point a b c i 2-point a b c j 2)^2

def values (a b c : ℚ) : Fin 7 → ℚ :=
  ![(a^2+b^2)/2,(a^2+c^2)/2,(b^2+c^2)/2,
    a^2+b^2+c^2-a*b-a*c-b*c,
    a^2+b^2+c^2-a*b+a*c+b*c,
    a^2+b^2+c^2+a*b-a*c+b*c,
    a^2+b^2+c^2+a*b+a*c-b*c]

def valueIndex : Fin 12 → Fin 12 → Fin 7 :=
  ![![0,2,1,0,3,4,6,5,3,5,4,6],![2,0,0,1,4,3,5,6,5,3,6,4],![1,0,0,2,6,5,3,4,4,6,3,5],![0,1,2,0,5,6,4,3,6,4,5,3],![3,4,6,5,0,1,0,2,3,6,5,4],![4,3,5,6,1,0,2,0,6,3,4,5],![6,5,3,4,0,2,0,1,5,4,3,6],![5,6,4,3,2,0,1,0,4,5,6,3],![3,5,4,6,3,6,5,4,0,0,2,1],![5,3,6,4,6,3,4,5,0,0,1,2],![4,6,3,5,5,4,3,6,2,1,0,0],![6,4,5,3,4,5,6,3,1,2,0,0]]

def valueMultiplier : Fin 12 → Fin 12 → ℚ :=
  ![![0,4,4,4,1,1,1,1,1,1,1,1],![4,0,4,4,1,1,1,1,1,1,1,1],![4,4,0,4,1,1,1,1,1,1,1,1],![4,4,4,0,1,1,1,1,1,1,1,1],![1,1,1,1,0,4,4,4,1,1,1,1],![1,1,1,1,4,0,4,4,1,1,1,1],![1,1,1,1,4,4,0,4,1,1,1,1],![1,1,1,1,4,4,4,0,1,1,1,1],![1,1,1,1,1,1,1,1,0,4,4,4],![1,1,1,1,1,1,1,1,4,0,4,4],![1,1,1,1,1,1,1,1,4,4,0,4],![1,1,1,1,1,1,1,1,4,4,4,0]]

set_option maxHeartbeats 2000000 in
private lemma chord_formula_0 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 0 j/2 = valueMultiplier 0 j * values a b c (valueIndex 0 j) := by
  fin_cases j
  · change (((a)-(a))^2+((b)-(b))^2+((c)-(c))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((a)-(a))^2+((b)-(-b))^2+((c)-(-c))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((a)-(-a))^2+((b)-(b))^2+((c)-(-c))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((a)-(-a))^2+((b)-(-b))^2+((c)-(c))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((a)-(b))^2+((b)-(c))^2+((c)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((a)-(b))^2+((b)-(-c))^2+((c)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((a)-(-b))^2+((b)-(c))^2+((c)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((a)-(-b))^2+((b)-(-c))^2+((c)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((a)-(c))^2+((b)-(a))^2+((c)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((a)-(c))^2+((b)-(-a))^2+((c)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((a)-(-c))^2+((b)-(a))^2+((c)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((a)-(-c))^2+((b)-(-a))^2+((c)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_1 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 1 j/2 = valueMultiplier 1 j * values a b c (valueIndex 1 j) := by
  fin_cases j
  · change (((a)-(a))^2+((-b)-(b))^2+((-c)-(c))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((a)-(a))^2+((-b)-(-b))^2+((-c)-(-c))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((a)-(-a))^2+((-b)-(b))^2+((-c)-(-c))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((a)-(-a))^2+((-b)-(-b))^2+((-c)-(c))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((a)-(b))^2+((-b)-(c))^2+((-c)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((a)-(b))^2+((-b)-(-c))^2+((-c)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((a)-(-b))^2+((-b)-(c))^2+((-c)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((a)-(-b))^2+((-b)-(-c))^2+((-c)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((a)-(c))^2+((-b)-(a))^2+((-c)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((a)-(c))^2+((-b)-(-a))^2+((-c)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((a)-(-c))^2+((-b)-(a))^2+((-c)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((a)-(-c))^2+((-b)-(-a))^2+((-c)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_2 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 2 j/2 = valueMultiplier 2 j * values a b c (valueIndex 2 j) := by
  fin_cases j
  · change (((-a)-(a))^2+((b)-(b))^2+((-c)-(c))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-a)-(a))^2+((b)-(-b))^2+((-c)-(-c))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((-a)-(-a))^2+((b)-(b))^2+((-c)-(-c))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((-a)-(-a))^2+((b)-(-b))^2+((-c)-(c))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-a)-(b))^2+((b)-(c))^2+((-c)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-a)-(b))^2+((b)-(-c))^2+((-c)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-a)-(-b))^2+((b)-(c))^2+((-c)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-a)-(-b))^2+((b)-(-c))^2+((-c)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-a)-(c))^2+((b)-(a))^2+((-c)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-a)-(c))^2+((b)-(-a))^2+((-c)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-a)-(-c))^2+((b)-(a))^2+((-c)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-a)-(-c))^2+((b)-(-a))^2+((-c)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_3 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 3 j/2 = valueMultiplier 3 j * values a b c (valueIndex 3 j) := by
  fin_cases j
  · change (((-a)-(a))^2+((-b)-(b))^2+((c)-(c))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((-a)-(a))^2+((-b)-(-b))^2+((c)-(-c))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-a)-(-a))^2+((-b)-(b))^2+((c)-(-c))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-a)-(-a))^2+((-b)-(-b))^2+((c)-(c))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((-a)-(b))^2+((-b)-(c))^2+((c)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-a)-(b))^2+((-b)-(-c))^2+((c)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-a)-(-b))^2+((-b)-(c))^2+((c)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-a)-(-b))^2+((-b)-(-c))^2+((c)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-a)-(c))^2+((-b)-(a))^2+((c)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-a)-(c))^2+((-b)-(-a))^2+((c)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-a)-(-c))^2+((-b)-(a))^2+((c)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-a)-(-c))^2+((-b)-(-a))^2+((c)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_4 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 4 j/2 = valueMultiplier 4 j * values a b c (valueIndex 4 j) := by
  fin_cases j
  · change (((b)-(a))^2+((c)-(b))^2+((a)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((b)-(a))^2+((c)-(-b))^2+((a)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((b)-(-a))^2+((c)-(b))^2+((a)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((b)-(-a))^2+((c)-(-b))^2+((a)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((b)-(b))^2+((c)-(c))^2+((a)-(a))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((b)-(b))^2+((c)-(-c))^2+((a)-(-a))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((b)-(-b))^2+((c)-(c))^2+((a)-(-a))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((b)-(-b))^2+((c)-(-c))^2+((a)-(a))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((b)-(c))^2+((c)-(a))^2+((a)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((b)-(c))^2+((c)-(-a))^2+((a)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((b)-(-c))^2+((c)-(a))^2+((a)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((b)-(-c))^2+((c)-(-a))^2+((a)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_5 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 5 j/2 = valueMultiplier 5 j * values a b c (valueIndex 5 j) := by
  fin_cases j
  · change (((b)-(a))^2+((-c)-(b))^2+((-a)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((b)-(a))^2+((-c)-(-b))^2+((-a)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((b)-(-a))^2+((-c)-(b))^2+((-a)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((b)-(-a))^2+((-c)-(-b))^2+((-a)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((b)-(b))^2+((-c)-(c))^2+((-a)-(a))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((b)-(b))^2+((-c)-(-c))^2+((-a)-(-a))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((b)-(-b))^2+((-c)-(c))^2+((-a)-(-a))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((b)-(-b))^2+((-c)-(-c))^2+((-a)-(a))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((b)-(c))^2+((-c)-(a))^2+((-a)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((b)-(c))^2+((-c)-(-a))^2+((-a)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((b)-(-c))^2+((-c)-(a))^2+((-a)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((b)-(-c))^2+((-c)-(-a))^2+((-a)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_6 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 6 j/2 = valueMultiplier 6 j * values a b c (valueIndex 6 j) := by
  fin_cases j
  · change (((-b)-(a))^2+((c)-(b))^2+((-a)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-b)-(a))^2+((c)-(-b))^2+((-a)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-b)-(-a))^2+((c)-(b))^2+((-a)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-b)-(-a))^2+((c)-(-b))^2+((-a)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-b)-(b))^2+((c)-(c))^2+((-a)-(a))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((-b)-(b))^2+((c)-(-c))^2+((-a)-(-a))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-b)-(-b))^2+((c)-(c))^2+((-a)-(-a))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((-b)-(-b))^2+((c)-(-c))^2+((-a)-(a))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-b)-(c))^2+((c)-(a))^2+((-a)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-b)-(c))^2+((c)-(-a))^2+((-a)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-b)-(-c))^2+((c)-(a))^2+((-a)-(-b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-b)-(-c))^2+((c)-(-a))^2+((-a)-(b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_7 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 7 j/2 = valueMultiplier 7 j * values a b c (valueIndex 7 j) := by
  fin_cases j
  · change (((-b)-(a))^2+((-c)-(b))^2+((a)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-b)-(a))^2+((-c)-(-b))^2+((a)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-b)-(-a))^2+((-c)-(b))^2+((a)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-b)-(-a))^2+((-c)-(-b))^2+((a)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-b)-(b))^2+((-c)-(c))^2+((a)-(a))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-b)-(b))^2+((-c)-(-c))^2+((a)-(-a))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((-b)-(-b))^2+((-c)-(c))^2+((a)-(-a))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-b)-(-b))^2+((-c)-(-c))^2+((a)-(a))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((-b)-(c))^2+((-c)-(a))^2+((a)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-b)-(c))^2+((-c)-(-a))^2+((a)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-b)-(-c))^2+((-c)-(a))^2+((a)-(-b))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-b)-(-c))^2+((-c)-(-a))^2+((a)-(b))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_8 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 8 j/2 = valueMultiplier 8 j * values a b c (valueIndex 8 j) := by
  fin_cases j
  · change (((c)-(a))^2+((a)-(b))^2+((b)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((c)-(a))^2+((a)-(-b))^2+((b)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((c)-(-a))^2+((a)-(b))^2+((b)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((c)-(-a))^2+((a)-(-b))^2+((b)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((c)-(b))^2+((a)-(c))^2+((b)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((c)-(b))^2+((a)-(-c))^2+((b)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((c)-(-b))^2+((a)-(c))^2+((b)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((c)-(-b))^2+((a)-(-c))^2+((b)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((c)-(c))^2+((a)-(a))^2+((b)-(b))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((c)-(c))^2+((a)-(-a))^2+((b)-(-b))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((c)-(-c))^2+((a)-(a))^2+((b)-(-b))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((c)-(-c))^2+((a)-(-a))^2+((b)-(b))^2)/2 = 4*((a^2+c^2)/2)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_9 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 9 j/2 = valueMultiplier 9 j * values a b c (valueIndex 9 j) := by
  fin_cases j
  · change (((c)-(a))^2+((-a)-(b))^2+((-b)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((c)-(a))^2+((-a)-(-b))^2+((-b)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((c)-(-a))^2+((-a)-(b))^2+((-b)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((c)-(-a))^2+((-a)-(-b))^2+((-b)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((c)-(b))^2+((-a)-(c))^2+((-b)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((c)-(b))^2+((-a)-(-c))^2+((-b)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((c)-(-b))^2+((-a)-(c))^2+((-b)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((c)-(-b))^2+((-a)-(-c))^2+((-b)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((c)-(c))^2+((-a)-(a))^2+((-b)-(b))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((c)-(c))^2+((-a)-(-a))^2+((-b)-(-b))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((c)-(-c))^2+((-a)-(a))^2+((-b)-(-b))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((c)-(-c))^2+((-a)-(-a))^2+((-b)-(b))^2)/2 = 4*((b^2+c^2)/2)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_10 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 10 j/2 = valueMultiplier 10 j * values a b c (valueIndex 10 j) := by
  fin_cases j
  · change (((-c)-(a))^2+((a)-(b))^2+((-b)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-c)-(a))^2+((a)-(-b))^2+((-b)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-c)-(-a))^2+((a)-(b))^2+((-b)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-c)-(-a))^2+((a)-(-b))^2+((-b)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-c)-(b))^2+((a)-(c))^2+((-b)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-c)-(b))^2+((a)-(-c))^2+((-b)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-c)-(-b))^2+((a)-(c))^2+((-b)-(-a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-c)-(-b))^2+((a)-(-c))^2+((-b)-(a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-c)-(c))^2+((a)-(a))^2+((-b)-(b))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-c)-(c))^2+((a)-(-a))^2+((-b)-(-b))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-c)-(-c))^2+((a)-(a))^2+((-b)-(-b))^2)/2 = 0*((a^2+b^2)/2)
    ring
  · change (((-c)-(-c))^2+((a)-(-a))^2+((-b)-(b))^2)/2 = 4*((a^2+b^2)/2)
    ring

set_option maxHeartbeats 2000000 in
private lemma chord_formula_11 (a b c : ℚ) (j : Fin 12) :
    chordSq a b c 11 j/2 = valueMultiplier 11 j * values a b c (valueIndex 11 j) := by
  fin_cases j
  · change (((-c)-(a))^2+((-a)-(b))^2+((b)-(c))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-c)-(a))^2+((-a)-(-b))^2+((b)-(-c))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-c)-(-a))^2+((-a)-(b))^2+((b)-(-c))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-c)-(-a))^2+((-a)-(-b))^2+((b)-(c))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-c)-(b))^2+((-a)-(c))^2+((b)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b+a*c+b*c)
    ring
  · change (((-c)-(b))^2+((-a)-(-c))^2+((b)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b-a*c+b*c)
    ring
  · change (((-c)-(-b))^2+((-a)-(c))^2+((b)-(-a))^2)/2 = 1*(a^2+b^2+c^2+a*b+a*c-b*c)
    ring
  · change (((-c)-(-b))^2+((-a)-(-c))^2+((b)-(a))^2)/2 = 1*(a^2+b^2+c^2-a*b-a*c-b*c)
    ring
  · change (((-c)-(c))^2+((-a)-(a))^2+((b)-(b))^2)/2 = 4*((a^2+c^2)/2)
    ring
  · change (((-c)-(c))^2+((-a)-(-a))^2+((b)-(-b))^2)/2 = 4*((b^2+c^2)/2)
    ring
  · change (((-c)-(-c))^2+((-a)-(a))^2+((b)-(-b))^2)/2 = 4*((a^2+b^2)/2)
    ring
  · change (((-c)-(-c))^2+((-a)-(-a))^2+((b)-(b))^2)/2 = 0*((a^2+b^2)/2)
    ring

lemma chord_formula (a b c : ℚ) (i j : Fin 12) :
    chordSq a b c i j/2 = valueMultiplier i j * values a b c (valueIndex i j) := by
  fin_cases i
  · exact chord_formula_0 a b c j
  · exact chord_formula_1 a b c j
  · exact chord_formula_2 a b c j
  · exact chord_formula_3 a b c j
  · exact chord_formula_4 a b c j
  · exact chord_formula_5 a b c j
  · exact chord_formula_6 a b c j
  · exact chord_formula_7 a b c j
  · exact chord_formula_8 a b c j
  · exact chord_formula_9 a b c j
  · exact chord_formula_10 a b c j
  · exact chord_formula_11 a b c j

lemma all_chords_square (a b c : ℚ) (h : ∀ k, IsSquare (values a b c k)) :
    ∀ i j, IsSquare (chordSq a b c i j/2) := by
  intro i j
  rw [chord_formula]
  apply IsSquare.mul
  · have hm : ∀ i j, valueMultiplier i j = 0 ∨ valueMultiplier i j = 1 ∨
          valueMultiplier i j = 4 := by decide
    rcases hm i j with h0 | h1 | h4
    · rw [h0]; exact ⟨0, by norm_num⟩
    · rw [h1]; exact ⟨1, by norm_num⟩
    · rw [h4]; exact ⟨2, by norm_num⟩
  · exact h _

def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def planeDet {R : Type*} [CommRing R] (a b c : R) (i j k l : Fin 12) : R :=
  let p := point a b c
  det3 (p j 0-p i 0) (p j 1-p i 1) (p j 2-p i 2)
    (p k 0-p i 0) (p k 1-p i 1) (p k 2-p i 2)
    (p l 0-p i 0) (p l 1-p i 1) (p l 2-p i 2)

def badQuad : Fin 78 → Fin 4 → Fin 12 :=
  ![![0,1,4,5],![0,1,8,11],![0,1,9,10],![0,2,4,7],![0,2,5,6],![0,2,8,10],![0,3,4,6],![0,3,4,10],![0,3,4,11],![0,3,5,7],![0,3,5,8],![0,3,5,9],![0,3,6,10],![0,3,6,11],![0,3,7,8],![0,3,7,9],![0,3,8,9],![0,3,10,11],![0,4,6,10],![0,4,6,11],![0,4,10,11],![0,5,7,8],![0,5,7,9],![0,5,8,9],![0,6,10,11],![0,7,8,9],![1,2,4,6],![1,2,4,8],![1,2,4,9],![1,2,5,7],![1,2,5,10],![1,2,5,11],![1,2,6,8],![1,2,6,9],![1,2,7,10],![1,2,7,11],![1,2,8,9],![1,2,10,11],![1,3,4,7],![1,3,5,6],![1,3,9,11],![1,4,6,8],![1,4,6,9],![1,4,8,9],![1,5,7,10],![1,5,7,11],![1,5,10,11],![1,6,8,9],![1,7,10,11],![2,3,6,7],![2,3,8,11],![2,3,9,10],![2,4,6,8],![2,4,6,9],![2,4,8,9],![2,5,7,10],![2,5,7,11],![2,5,10,11],![2,6,8,9],![2,7,10,11],![3,4,6,10],![3,4,6,11],![3,4,10,11],![3,5,7,8],![3,5,7,9],![3,5,8,9],![3,6,10,11],![3,7,8,9],![4,5,8,10],![4,5,9,11],![4,6,8,9],![4,6,10,11],![4,7,8,11],![5,6,9,10],![5,7,8,9],![5,7,10,11],![6,7,8,10],![6,7,9,11]]

set_option maxHeartbeats 3000000 in
lemma diagonal_forced {R : Type*} [CommRing R] (a c : R) (k : Fin 78) :
    planeDet a a c (badQuad k 0) (badQuad k 1) (badQuad k 2) (badQuad k 3) = 0 := by
  fin_cases k
  · change ((a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((-c)-(a)))-((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((a)-(a)))+((-c)-(c))*(((a)-(a))*((-c)-(a))-((c)-(a))*((a)-(a)))=0
    ring
  · change ((a)-(a))*(((a)-(a))*((a)-(c))-((a)-(c))*((-a)-(a)))-((-a)-(a))*(((c)-(a))*((a)-(c))-((a)-(c))*((-c)-(a)))+((-c)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((-a)-(a))*((-a)-(c))-((-a)-(c))*((a)-(a)))-((-a)-(a))*(((c)-(a))*((-a)-(c))-((-a)-(c))*((-c)-(a)))+((-c)-(c))*(((c)-(a))*((a)-(a))-((-a)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((a)-(c))-((a)-(c))*((-c)-(a)))-((a)-(a))*(((a)-(a))*((a)-(c))-((a)-(c))*((-a)-(a)))+((-c)-(c))*(((a)-(a))*((-c)-(a))-((c)-(a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((-a)-(c))-((-a)-(c))*((c)-(a)))-((a)-(a))*(((a)-(a))*((-a)-(c))-((-a)-(c))*((-a)-(a)))+((-c)-(c))*(((a)-(a))*((c)-(a))-((-c)-(a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((a)-(a)))-((a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((-c)-(a)))+((-c)-(c))*(((c)-(a))*((a)-(a))-((a)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))-((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))+((c)-(c))*(((a)-(a))*((c)-(a))-((c)-(a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((a)-(a)))-((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((-c)-(a)))+((c)-(c))*(((a)-(a))*((a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((a)-(c))-((a)-(c))*((-a)-(a)))-((-a)-(a))*(((a)-(a))*((a)-(c))-((a)-(c))*((-c)-(a)))+((c)-(c))*(((a)-(a))*((-a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))-((-a)-(a))*(((a)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))+((c)-(c))*(((a)-(a))*((-c)-(a))-((-c)-(a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((a)-(c))-((-a)-(c))*((a)-(a)))-((-a)-(a))*(((a)-(a))*((a)-(c))-((-a)-(c))*((c)-(a)))+((c)-(c))*(((a)-(a))*((a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((-a)-(c))-((-a)-(c))*((-a)-(a)))-((-a)-(a))*(((a)-(a))*((-a)-(c))-((-a)-(c))*((c)-(a)))+((c)-(c))*(((a)-(a))*((-a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((-a)-(c))-((-a)-(c))*((a)-(a)))-((-a)-(a))*(((-a)-(a))*((-a)-(c))-((-a)-(c))*((-c)-(a)))+((c)-(c))*(((-a)-(a))*((a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))-((-a)-(a))*(((-a)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))+((c)-(c))*(((-a)-(a))*((-a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((a)-(c))-((a)-(c))*((a)-(a)))-((-a)-(a))*(((-a)-(a))*((a)-(c))-((a)-(c))*((c)-(a)))+((c)-(c))*(((-a)-(a))*((a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))-((-a)-(a))*(((-a)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))+((c)-(c))*(((-a)-(a))*((-a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))-((-a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))+((c)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))-((-a)-(a))*(((-c)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))+((c)-(c))*(((-c)-(a))*((-a)-(a))-((a)-(a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((c)-(a))*((-a)-(c))-((-a)-(c))*((a)-(a)))-((c)-(a))*(((-a)-(a))*((-a)-(c))-((-a)-(c))*((-c)-(a)))+((a)-(c))*(((-a)-(a))*((a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((c)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))-((c)-(a))*(((-a)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))+((a)-(c))*(((-a)-(a))*((-a)-(a))-((c)-(a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((a)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))-((c)-(a))*(((-c)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))+((a)-(c))*(((-c)-(a))*((-a)-(a))-((a)-(a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((-c)-(a))*((a)-(c))-((a)-(c))*((a)-(a)))-((-c)-(a))*(((-a)-(a))*((a)-(c))-((a)-(c))*((c)-(a)))+((-a)-(c))*(((-a)-(a))*((a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((a)-(a))*(((-c)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))-((-c)-(a))*(((-a)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))+((-a)-(c))*(((-a)-(a))*((-a)-(a))-((-c)-(a))*((c)-(a)))=0
    ring
  · change ((a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))-((-c)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))+((-a)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(a))*((a)-(c))-((-a)-(c))*((-a)-(a)))-((c)-(a))*(((-c)-(a))*((a)-(c))-((-a)-(c))*((-c)-(a)))+((-a)-(c))*(((-c)-(a))*((-a)-(a))-((a)-(a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(a))*((-a)-(c))-((a)-(c))*((-a)-(a)))-((-c)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))+((a)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((-a)-(-c))-((a)-(-c))*((c)-(-a)))-((a)-(-a))*(((a)-(a))*((-a)-(-c))-((a)-(-c))*((-a)-(a)))+((-c)-(-c))*(((a)-(a))*((c)-(-a))-((c)-(-a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((a)-(-c))-((a)-(-c))*((a)-(-a)))-((a)-(-a))*(((a)-(a))*((a)-(-c))-((a)-(-c))*((c)-(a)))+((-c)-(-c))*(((a)-(a))*((a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((-a)-(-c))-((a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((a)-(a))*((-a)-(-c))-((a)-(-c))*((c)-(a)))+((-c)-(-c))*(((a)-(a))*((-a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((a)-(-c))-((-a)-(-c))*((-c)-(-a)))-((a)-(-a))*(((a)-(a))*((a)-(-c))-((-a)-(-c))*((-a)-(a)))+((-c)-(-c))*(((a)-(a))*((-c)-(-a))-((-c)-(-a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((-a)-(-c))-((-a)-(-c))*((a)-(-a)))-((a)-(-a))*(((a)-(a))*((-a)-(-c))-((-a)-(-c))*((-c)-(a)))+((-c)-(-c))*(((a)-(a))*((a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((a)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))+((-c)-(-c))*(((a)-(a))*((-a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((a)-(-c))-((-a)-(-c))*((a)-(-a)))-((a)-(-a))*(((-a)-(a))*((a)-(-c))-((-a)-(-c))*((c)-(a)))+((-c)-(-c))*(((-a)-(a))*((a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((-a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((-a)-(a))*((-a)-(-c))-((-a)-(-c))*((c)-(a)))+((-c)-(-c))*(((-a)-(a))*((-a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((-a)-(-c))-((a)-(-c))*((a)-(-a)))-((a)-(-a))*(((-a)-(a))*((-a)-(-c))-((a)-(-c))*((-c)-(a)))+((-c)-(-c))*(((-a)-(a))*((a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((a)-(-c))-((a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((-a)-(a))*((a)-(-c))-((a)-(-c))*((-c)-(a)))+((-c)-(-c))*(((-a)-(a))*((-a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-a))*((-a)-(-c))-((a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((c)-(a))*((-a)-(-c))-((a)-(-c))*((c)-(a)))+((-c)-(-c))*(((c)-(a))*((-a)-(-a))-((a)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((a)-(-a))*(((-c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))+((-c)-(-c))*(((-c)-(a))*((-a)-(-a))-((a)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((c)-(-a))*((a)-(-c))-((a)-(-c))*((-c)-(-a)))-((-a)-(-a))*(((a)-(a))*((a)-(-c))-((a)-(-c))*((-a)-(a)))+((c)-(-c))*(((a)-(a))*((-c)-(-a))-((c)-(-a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((-c)-(-a))*((-a)-(-c))-((-a)-(-c))*((c)-(-a)))-((-a)-(-a))*(((a)-(a))*((-a)-(-c))-((-a)-(-c))*((-a)-(a)))+((c)-(-c))*(((a)-(a))*((c)-(-a))-((-c)-(-a))*((-a)-(a)))=0
    ring
  · change ((-a)-(a))*(((-a)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((-a)-(-a))*(((c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))+((c)-(-c))*(((c)-(a))*((-a)-(-a))-((-a)-(-a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((c)-(-a))*((a)-(-c))-((-a)-(-c))*((a)-(-a)))-((c)-(-a))*(((-a)-(a))*((a)-(-c))-((-a)-(-c))*((c)-(a)))+((a)-(-c))*(((-a)-(a))*((a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((a)-(a))*(((c)-(-a))*((-a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((c)-(-a))*(((-a)-(a))*((-a)-(-c))-((-a)-(-c))*((c)-(a)))+((a)-(-c))*(((-a)-(a))*((-a)-(-a))-((c)-(-a))*((c)-(a)))=0
    ring
  · change ((a)-(a))*(((a)-(-a))*((-a)-(-c))-((a)-(-c))*((-a)-(-a)))-((c)-(-a))*(((c)-(a))*((-a)-(-c))-((a)-(-c))*((c)-(a)))+((a)-(-c))*(((c)-(a))*((-a)-(-a))-((a)-(-a))*((c)-(a)))=0
    ring
  · change ((a)-(a))*(((-c)-(-a))*((-a)-(-c))-((a)-(-c))*((a)-(-a)))-((-c)-(-a))*(((-a)-(a))*((-a)-(-c))-((a)-(-c))*((-c)-(a)))+((-a)-(-c))*(((-a)-(a))*((a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((-c)-(-a))*((a)-(-c))-((a)-(-c))*((-a)-(-a)))-((-c)-(-a))*(((-a)-(a))*((a)-(-c))-((a)-(-c))*((-c)-(a)))+((-a)-(-c))*(((-a)-(a))*((-a)-(-a))-((-c)-(-a))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((a)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((-c)-(-a))*(((-c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))+((-a)-(-c))*(((-c)-(a))*((-a)-(-a))-((a)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-a))*((-a)-(-c))-((a)-(-c))*((-a)-(-a)))-((c)-(-a))*(((c)-(a))*((-a)-(-c))-((a)-(-c))*((c)-(a)))+((-a)-(-c))*(((c)-(a))*((-a)-(-a))-((a)-(-a))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))-((-c)-(-a))*(((-c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))+((a)-(-c))*(((-c)-(a))*((-a)-(-a))-((a)-(-a))*((-c)-(a)))=0
    ring
  · change ((-a)-(-a))*(((c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))-((-a)-(a))*(((-a)-(-a))*((a)-(-c))-((-a)-(-c))*((-a)-(-a)))+((c)-(-c))*(((-a)-(-a))*((-c)-(a))-((c)-(a))*((-a)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(a))*((a)-(-c))-((a)-(-c))*((-a)-(a)))-((-a)-(a))*(((c)-(-a))*((a)-(-c))-((a)-(-c))*((-c)-(-a)))+((c)-(-c))*(((c)-(-a))*((-a)-(a))-((a)-(a))*((-c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((-a)-(a))*((-a)-(-c))-((-a)-(-c))*((a)-(a)))-((-a)-(a))*(((c)-(-a))*((-a)-(-c))-((-a)-(-c))*((-c)-(-a)))+((c)-(-c))*(((c)-(-a))*((a)-(a))-((-a)-(a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((c)-(a))*((a)-(-c))-((-a)-(-c))*((a)-(a)))-((c)-(a))*(((-a)-(-a))*((a)-(-c))-((-a)-(-c))*((c)-(-a)))+((a)-(-c))*(((-a)-(-a))*((a)-(a))-((c)-(a))*((c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((c)-(a))*((-a)-(-c))-((-a)-(-c))*((-a)-(a)))-((c)-(a))*(((-a)-(-a))*((-a)-(-c))-((-a)-(-c))*((c)-(-a)))+((a)-(-c))*(((-a)-(-a))*((-a)-(a))-((c)-(a))*((c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((a)-(a))*((-a)-(-c))-((a)-(-c))*((-a)-(a)))-((c)-(a))*(((c)-(-a))*((-a)-(-c))-((a)-(-c))*((c)-(-a)))+((a)-(-c))*(((c)-(-a))*((-a)-(a))-((a)-(a))*((c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((-c)-(a))*((-a)-(-c))-((a)-(-c))*((a)-(a)))-((-c)-(a))*(((-a)-(-a))*((-a)-(-c))-((a)-(-c))*((-c)-(-a)))+((-a)-(-c))*(((-a)-(-a))*((a)-(a))-((-c)-(a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((-c)-(a))*((a)-(-c))-((a)-(-c))*((-a)-(a)))-((-c)-(a))*(((-a)-(-a))*((a)-(-c))-((a)-(-c))*((-c)-(-a)))+((-a)-(-c))*(((-a)-(-a))*((-a)-(a))-((-c)-(a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((a)-(a))*((a)-(-c))-((-a)-(-c))*((-a)-(a)))-((-c)-(a))*(((-c)-(-a))*((a)-(-c))-((-a)-(-c))*((-c)-(-a)))+((-a)-(-c))*(((-c)-(-a))*((-a)-(a))-((a)-(a))*((-c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(a))*((-a)-(-c))-((a)-(-c))*((-a)-(a)))-((c)-(a))*(((c)-(-a))*((-a)-(-c))-((a)-(-c))*((c)-(-a)))+((-a)-(-c))*(((c)-(-a))*((-a)-(a))-((a)-(a))*((c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(a))*((a)-(-c))-((-a)-(-c))*((-a)-(a)))-((-c)-(a))*(((-c)-(-a))*((a)-(-c))-((-a)-(-c))*((-c)-(-a)))+((a)-(-c))*(((-c)-(-a))*((-a)-(a))-((a)-(a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((c)-(-a))*((-a)-(c))-((-a)-(c))*((a)-(-a)))-((c)-(-a))*(((-a)-(-a))*((-a)-(c))-((-a)-(c))*((-c)-(-a)))+((a)-(c))*(((-a)-(-a))*((a)-(-a))-((c)-(-a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((c)-(-a))*((a)-(c))-((-a)-(c))*((-a)-(-a)))-((c)-(-a))*(((-a)-(-a))*((a)-(c))-((-a)-(c))*((-c)-(-a)))+((a)-(c))*(((-a)-(-a))*((-a)-(-a))-((c)-(-a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((a)-(-a))*((a)-(c))-((-a)-(c))*((-a)-(-a)))-((c)-(-a))*(((-c)-(-a))*((a)-(c))-((-a)-(c))*((-c)-(-a)))+((a)-(c))*(((-c)-(-a))*((-a)-(-a))-((a)-(-a))*((-c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((-c)-(-a))*((a)-(c))-((a)-(c))*((a)-(-a)))-((-c)-(-a))*(((-a)-(-a))*((a)-(c))-((a)-(c))*((c)-(-a)))+((-a)-(c))*(((-a)-(-a))*((a)-(-a))-((-c)-(-a))*((c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((-c)-(-a))*((-a)-(c))-((a)-(c))*((-a)-(-a)))-((-c)-(-a))*(((-a)-(-a))*((-a)-(c))-((a)-(c))*((c)-(-a)))+((-a)-(c))*(((-a)-(-a))*((-a)-(-a))-((-c)-(-a))*((c)-(-a)))=0
    ring
  · change ((a)-(-a))*(((a)-(-a))*((-a)-(c))-((a)-(c))*((-a)-(-a)))-((-c)-(-a))*(((c)-(-a))*((-a)-(c))-((a)-(c))*((c)-(-a)))+((-a)-(c))*(((c)-(-a))*((-a)-(-a))-((a)-(-a))*((c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(-a))*((a)-(c))-((-a)-(c))*((-a)-(-a)))-((c)-(-a))*(((-c)-(-a))*((a)-(c))-((-a)-(c))*((-c)-(-a)))+((-a)-(c))*(((-c)-(-a))*((-a)-(-a))-((a)-(-a))*((-c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(-a))*((-a)-(c))-((a)-(c))*((-a)-(-a)))-((-c)-(-a))*(((c)-(-a))*((-a)-(c))-((a)-(c))*((c)-(-a)))+((a)-(c))*(((c)-(-a))*((-a)-(-a))-((a)-(-a))*((c)-(-a)))=0
    ring
  · change ((a)-(a))*(((a)-(c))*((-a)-(a))-((a)-(a))*((a)-(c)))-((-c)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((-c)-(a)))+((-a)-(a))*(((c)-(a))*((a)-(c))-((a)-(c))*((-c)-(a)))=0
    ring
  · change ((a)-(a))*(((-a)-(c))*((a)-(a))-((-a)-(a))*((-a)-(c)))-((-c)-(c))*(((c)-(a))*((a)-(a))-((-a)-(a))*((-c)-(a)))+((-a)-(a))*(((c)-(a))*((-a)-(c))-((-a)-(c))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(c))*((-a)-(a))-((a)-(a))*((-a)-(c)))-((c)-(c))*(((c)-(a))*((-a)-(a))-((a)-(a))*((c)-(a)))+((-a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(c))*((a)-(a))-((-a)-(a))*((-a)-(c)))-((c)-(c))*(((-c)-(a))*((a)-(a))-((-a)-(a))*((-c)-(a)))+((-a)-(a))*(((-c)-(a))*((-a)-(c))-((a)-(c))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(c))*((a)-(a))-((a)-(a))*((-a)-(c)))-((-c)-(c))*(((c)-(a))*((a)-(a))-((a)-(a))*((-c)-(a)))+((a)-(a))*(((c)-(a))*((-a)-(c))-((a)-(c))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((-a)-(-c))*((-a)-(-a))-((-a)-(-a))*((a)-(-c)))-((c)-(-c))*(((c)-(a))*((-a)-(-a))-((-a)-(-a))*((-c)-(a)))+((-a)-(-a))*(((c)-(a))*((a)-(-c))-((-a)-(-c))*((-c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-c))*((-a)-(-a))-((a)-(-a))*((-a)-(-c)))-((-c)-(-c))*(((c)-(a))*((-a)-(-a))-((a)-(-a))*((c)-(a)))+((a)-(-a))*(((c)-(a))*((-a)-(-c))-((a)-(-c))*((c)-(a)))=0
    ring
  · change ((-a)-(a))*(((a)-(-c))*((a)-(-a))-((-a)-(-a))*((-a)-(-c)))-((-c)-(-c))*(((-c)-(a))*((a)-(-a))-((-a)-(-a))*((-c)-(a)))+((a)-(-a))*(((-c)-(a))*((-a)-(-c))-((a)-(-c))*((-c)-(a)))=0
    ring
  · change ((-a)-(-a))*(((a)-(c))*((-a)-(-a))-((a)-(-a))*((a)-(c)))-((-c)-(c))*(((c)-(-a))*((-a)-(-a))-((a)-(-a))*((-c)-(-a)))+((a)-(-a))*(((c)-(-a))*((a)-(c))-((a)-(c))*((-c)-(-a)))=0
    ring
  · change ((-a)-(-a))*(((-a)-(c))*((a)-(-a))-((-a)-(-a))*((-a)-(c)))-((-c)-(c))*(((c)-(-a))*((a)-(-a))-((-a)-(-a))*((-c)-(-a)))+((a)-(-a))*(((c)-(-a))*((-a)-(c))-((-a)-(c))*((-c)-(-a)))=0
    ring

lemma badQuad_injective (k : Fin 78) : Function.Injective (badQuad k) := by
  fin_cases k <;> decide

set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
set_option maxHeartbeats 2000000

private lemma bool_cert (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) :
    (if b0 then (1 : BitVec 8) else 0) + (if b1 then (1 : BitVec 8) else 0) + (if b2 then (1 : BitVec 8) else 0) + (if b3 then (1 : BitVec 8) else 0) + (if b4 then (1 : BitVec 8) else 0) + (if b5 then (1 : BitVec 8) else 0) + (if b6 then (1 : BitVec 8) else 0) + (if b7 then (1 : BitVec 8) else 0) + (if b8 then (1 : BitVec 8) else 0) + (if b9 then (1 : BitVec 8) else 0) + (if b10 then (1 : BitVec 8) else 0) + (if b11 then (1 : BitVec 8) else 0) = 7 →
      (b0 = true ∧ b1 = true ∧ b4 = true ∧ b5 = true) ∨
      (b0 = true ∧ b1 = true ∧ b8 = true ∧ b11 = true) ∨
      (b0 = true ∧ b1 = true ∧ b9 = true ∧ b10 = true) ∨
      (b0 = true ∧ b2 = true ∧ b4 = true ∧ b7 = true) ∨
      (b0 = true ∧ b2 = true ∧ b5 = true ∧ b6 = true) ∨
      (b0 = true ∧ b2 = true ∧ b8 = true ∧ b10 = true) ∨
      (b0 = true ∧ b3 = true ∧ b4 = true ∧ b6 = true) ∨
      (b0 = true ∧ b3 = true ∧ b4 = true ∧ b10 = true) ∨
      (b0 = true ∧ b3 = true ∧ b4 = true ∧ b11 = true) ∨
      (b0 = true ∧ b3 = true ∧ b5 = true ∧ b7 = true) ∨
      (b0 = true ∧ b3 = true ∧ b5 = true ∧ b8 = true) ∨
      (b0 = true ∧ b3 = true ∧ b5 = true ∧ b9 = true) ∨
      (b0 = true ∧ b3 = true ∧ b6 = true ∧ b10 = true) ∨
      (b0 = true ∧ b3 = true ∧ b6 = true ∧ b11 = true) ∨
      (b0 = true ∧ b3 = true ∧ b7 = true ∧ b8 = true) ∨
      (b0 = true ∧ b3 = true ∧ b7 = true ∧ b9 = true) ∨
      (b0 = true ∧ b3 = true ∧ b8 = true ∧ b9 = true) ∨
      (b0 = true ∧ b3 = true ∧ b10 = true ∧ b11 = true) ∨
      (b0 = true ∧ b4 = true ∧ b6 = true ∧ b10 = true) ∨
      (b0 = true ∧ b4 = true ∧ b6 = true ∧ b11 = true) ∨
      (b0 = true ∧ b4 = true ∧ b10 = true ∧ b11 = true) ∨
      (b0 = true ∧ b5 = true ∧ b7 = true ∧ b8 = true) ∨
      (b0 = true ∧ b5 = true ∧ b7 = true ∧ b9 = true) ∨
      (b0 = true ∧ b5 = true ∧ b8 = true ∧ b9 = true) ∨
      (b0 = true ∧ b6 = true ∧ b10 = true ∧ b11 = true) ∨
      (b0 = true ∧ b7 = true ∧ b8 = true ∧ b9 = true) ∨
      (b1 = true ∧ b2 = true ∧ b4 = true ∧ b6 = true) ∨
      (b1 = true ∧ b2 = true ∧ b4 = true ∧ b8 = true) ∨
      (b1 = true ∧ b2 = true ∧ b4 = true ∧ b9 = true) ∨
      (b1 = true ∧ b2 = true ∧ b5 = true ∧ b7 = true) ∨
      (b1 = true ∧ b2 = true ∧ b5 = true ∧ b10 = true) ∨
      (b1 = true ∧ b2 = true ∧ b5 = true ∧ b11 = true) ∨
      (b1 = true ∧ b2 = true ∧ b6 = true ∧ b8 = true) ∨
      (b1 = true ∧ b2 = true ∧ b6 = true ∧ b9 = true) ∨
      (b1 = true ∧ b2 = true ∧ b7 = true ∧ b10 = true) ∨
      (b1 = true ∧ b2 = true ∧ b7 = true ∧ b11 = true) ∨
      (b1 = true ∧ b2 = true ∧ b8 = true ∧ b9 = true) ∨
      (b1 = true ∧ b2 = true ∧ b10 = true ∧ b11 = true) ∨
      (b1 = true ∧ b3 = true ∧ b4 = true ∧ b7 = true) ∨
      (b1 = true ∧ b3 = true ∧ b5 = true ∧ b6 = true) ∨
      (b1 = true ∧ b3 = true ∧ b9 = true ∧ b11 = true) ∨
      (b1 = true ∧ b4 = true ∧ b6 = true ∧ b8 = true) ∨
      (b1 = true ∧ b4 = true ∧ b6 = true ∧ b9 = true) ∨
      (b1 = true ∧ b4 = true ∧ b8 = true ∧ b9 = true) ∨
      (b1 = true ∧ b5 = true ∧ b7 = true ∧ b10 = true) ∨
      (b1 = true ∧ b5 = true ∧ b7 = true ∧ b11 = true) ∨
      (b1 = true ∧ b5 = true ∧ b10 = true ∧ b11 = true) ∨
      (b1 = true ∧ b6 = true ∧ b8 = true ∧ b9 = true) ∨
      (b1 = true ∧ b7 = true ∧ b10 = true ∧ b11 = true) ∨
      (b2 = true ∧ b3 = true ∧ b6 = true ∧ b7 = true) ∨
      (b2 = true ∧ b3 = true ∧ b8 = true ∧ b11 = true) ∨
      (b2 = true ∧ b3 = true ∧ b9 = true ∧ b10 = true) ∨
      (b2 = true ∧ b4 = true ∧ b6 = true ∧ b8 = true) ∨
      (b2 = true ∧ b4 = true ∧ b6 = true ∧ b9 = true) ∨
      (b2 = true ∧ b4 = true ∧ b8 = true ∧ b9 = true) ∨
      (b2 = true ∧ b5 = true ∧ b7 = true ∧ b10 = true) ∨
      (b2 = true ∧ b5 = true ∧ b7 = true ∧ b11 = true) ∨
      (b2 = true ∧ b5 = true ∧ b10 = true ∧ b11 = true) ∨
      (b2 = true ∧ b6 = true ∧ b8 = true ∧ b9 = true) ∨
      (b2 = true ∧ b7 = true ∧ b10 = true ∧ b11 = true) ∨
      (b3 = true ∧ b4 = true ∧ b6 = true ∧ b10 = true) ∨
      (b3 = true ∧ b4 = true ∧ b6 = true ∧ b11 = true) ∨
      (b3 = true ∧ b4 = true ∧ b10 = true ∧ b11 = true) ∨
      (b3 = true ∧ b5 = true ∧ b7 = true ∧ b8 = true) ∨
      (b3 = true ∧ b5 = true ∧ b7 = true ∧ b9 = true) ∨
      (b3 = true ∧ b5 = true ∧ b8 = true ∧ b9 = true) ∨
      (b3 = true ∧ b6 = true ∧ b10 = true ∧ b11 = true) ∨
      (b3 = true ∧ b7 = true ∧ b8 = true ∧ b9 = true) ∨
      (b4 = true ∧ b5 = true ∧ b8 = true ∧ b10 = true) ∨
      (b4 = true ∧ b5 = true ∧ b9 = true ∧ b11 = true) ∨
      (b4 = true ∧ b6 = true ∧ b8 = true ∧ b9 = true) ∨
      (b4 = true ∧ b6 = true ∧ b10 = true ∧ b11 = true) ∨
      (b4 = true ∧ b7 = true ∧ b8 = true ∧ b11 = true) ∨
      (b5 = true ∧ b6 = true ∧ b9 = true ∧ b10 = true) ∨
      (b5 = true ∧ b7 = true ∧ b8 = true ∧ b9 = true) ∨
      (b5 = true ∧ b7 = true ∧ b10 = true ∧ b11 = true) ∨
      (b6 = true ∧ b7 = true ∧ b8 = true ∧ b10 = true) ∨
      (b6 = true ∧ b7 = true ∧ b9 = true ∧ b11 = true) := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  decide +kernel

lemma seven_labels_forced_of_card (T : Finset (Fin 12)) (hT : T.card = 7) :
    ∃ k : Fin 78, ∀ i : Fin 4, badQuad k i ∈ T := by
  have hs : (∑ i : Fin 12, if i ∈ T then (1 : ℕ) else 0) = 7 := by
    rw [Finset.sum_boole]
    simpa using hT
  simp only [Fin.sum_univ_succ] at hs
  have hv := congrArg (BitVec.ofNat 8) hs
  simp only [BitVec.ofNat_add, apply_ite] at hv
  have hb := bool_cert (decide ((0 : Fin 12) ∈ T)) (decide ((1 : Fin 12) ∈ T)) (decide ((2 : Fin 12) ∈ T)) (decide ((3 : Fin 12) ∈ T)) (decide ((4 : Fin 12) ∈ T)) (decide ((5 : Fin 12) ∈ T)) (decide ((6 : Fin 12) ∈ T)) (decide ((7 : Fin 12) ∈ T)) (decide ((8 : Fin 12) ∈ T)) (decide ((9 : Fin 12) ∈ T)) (decide ((10 : Fin 12) ∈ T)) (decide ((11 : Fin 12) ∈ T))
  simp only [decide_eq_true_eq] at hb
  have hh := hb (by simpa only [BitVec.add_assoc, BitVec.add_zero, Fin.sum_univ_zero, BitVec.ofNat_eq_ofNat, ite_true, ite_false, decide_eq_true_eq] using hv)
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h0.1
    · change (1 : Fin 12) ∈ T
      exact h0.2.1
    · change (4 : Fin 12) ∈ T
      exact h0.2.2.1
    · change (5 : Fin 12) ∈ T
      exact h0.2.2.2
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h1.1
    · change (1 : Fin 12) ∈ T
      exact h1.2.1
    · change (8 : Fin 12) ∈ T
      exact h1.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h1.2.2.2
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h2.1
    · change (1 : Fin 12) ∈ T
      exact h2.2.1
    · change (9 : Fin 12) ∈ T
      exact h2.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h2.2.2.2
  · refine ⟨3, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h3.1
    · change (2 : Fin 12) ∈ T
      exact h3.2.1
    · change (4 : Fin 12) ∈ T
      exact h3.2.2.1
    · change (7 : Fin 12) ∈ T
      exact h3.2.2.2
  · refine ⟨4, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h4.1
    · change (2 : Fin 12) ∈ T
      exact h4.2.1
    · change (5 : Fin 12) ∈ T
      exact h4.2.2.1
    · change (6 : Fin 12) ∈ T
      exact h4.2.2.2
  · refine ⟨5, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h5.1
    · change (2 : Fin 12) ∈ T
      exact h5.2.1
    · change (8 : Fin 12) ∈ T
      exact h5.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h5.2.2.2
  · refine ⟨6, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h6.1
    · change (3 : Fin 12) ∈ T
      exact h6.2.1
    · change (4 : Fin 12) ∈ T
      exact h6.2.2.1
    · change (6 : Fin 12) ∈ T
      exact h6.2.2.2
  · refine ⟨7, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h7.1
    · change (3 : Fin 12) ∈ T
      exact h7.2.1
    · change (4 : Fin 12) ∈ T
      exact h7.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h7.2.2.2
  · refine ⟨8, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h8.1
    · change (3 : Fin 12) ∈ T
      exact h8.2.1
    · change (4 : Fin 12) ∈ T
      exact h8.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h8.2.2.2
  · refine ⟨9, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h9.1
    · change (3 : Fin 12) ∈ T
      exact h9.2.1
    · change (5 : Fin 12) ∈ T
      exact h9.2.2.1
    · change (7 : Fin 12) ∈ T
      exact h9.2.2.2
  · refine ⟨10, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h10.1
    · change (3 : Fin 12) ∈ T
      exact h10.2.1
    · change (5 : Fin 12) ∈ T
      exact h10.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h10.2.2.2
  · refine ⟨11, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h11.1
    · change (3 : Fin 12) ∈ T
      exact h11.2.1
    · change (5 : Fin 12) ∈ T
      exact h11.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h11.2.2.2
  · refine ⟨12, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h12.1
    · change (3 : Fin 12) ∈ T
      exact h12.2.1
    · change (6 : Fin 12) ∈ T
      exact h12.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h12.2.2.2
  · refine ⟨13, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h13.1
    · change (3 : Fin 12) ∈ T
      exact h13.2.1
    · change (6 : Fin 12) ∈ T
      exact h13.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h13.2.2.2
  · refine ⟨14, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h14.1
    · change (3 : Fin 12) ∈ T
      exact h14.2.1
    · change (7 : Fin 12) ∈ T
      exact h14.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h14.2.2.2
  · refine ⟨15, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h15.1
    · change (3 : Fin 12) ∈ T
      exact h15.2.1
    · change (7 : Fin 12) ∈ T
      exact h15.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h15.2.2.2
  · refine ⟨16, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h16.1
    · change (3 : Fin 12) ∈ T
      exact h16.2.1
    · change (8 : Fin 12) ∈ T
      exact h16.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h16.2.2.2
  · refine ⟨17, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h17.1
    · change (3 : Fin 12) ∈ T
      exact h17.2.1
    · change (10 : Fin 12) ∈ T
      exact h17.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h17.2.2.2
  · refine ⟨18, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h18.1
    · change (4 : Fin 12) ∈ T
      exact h18.2.1
    · change (6 : Fin 12) ∈ T
      exact h18.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h18.2.2.2
  · refine ⟨19, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h19.1
    · change (4 : Fin 12) ∈ T
      exact h19.2.1
    · change (6 : Fin 12) ∈ T
      exact h19.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h19.2.2.2
  · refine ⟨20, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h20.1
    · change (4 : Fin 12) ∈ T
      exact h20.2.1
    · change (10 : Fin 12) ∈ T
      exact h20.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h20.2.2.2
  · refine ⟨21, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h21.1
    · change (5 : Fin 12) ∈ T
      exact h21.2.1
    · change (7 : Fin 12) ∈ T
      exact h21.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h21.2.2.2
  · refine ⟨22, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h22.1
    · change (5 : Fin 12) ∈ T
      exact h22.2.1
    · change (7 : Fin 12) ∈ T
      exact h22.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h22.2.2.2
  · refine ⟨23, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h23.1
    · change (5 : Fin 12) ∈ T
      exact h23.2.1
    · change (8 : Fin 12) ∈ T
      exact h23.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h23.2.2.2
  · refine ⟨24, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h24.1
    · change (6 : Fin 12) ∈ T
      exact h24.2.1
    · change (10 : Fin 12) ∈ T
      exact h24.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h24.2.2.2
  · refine ⟨25, ?_⟩
    intro i
    fin_cases i
    · change (0 : Fin 12) ∈ T
      exact h25.1
    · change (7 : Fin 12) ∈ T
      exact h25.2.1
    · change (8 : Fin 12) ∈ T
      exact h25.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h25.2.2.2
  · refine ⟨26, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h26.1
    · change (2 : Fin 12) ∈ T
      exact h26.2.1
    · change (4 : Fin 12) ∈ T
      exact h26.2.2.1
    · change (6 : Fin 12) ∈ T
      exact h26.2.2.2
  · refine ⟨27, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h27.1
    · change (2 : Fin 12) ∈ T
      exact h27.2.1
    · change (4 : Fin 12) ∈ T
      exact h27.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h27.2.2.2
  · refine ⟨28, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h28.1
    · change (2 : Fin 12) ∈ T
      exact h28.2.1
    · change (4 : Fin 12) ∈ T
      exact h28.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h28.2.2.2
  · refine ⟨29, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h29.1
    · change (2 : Fin 12) ∈ T
      exact h29.2.1
    · change (5 : Fin 12) ∈ T
      exact h29.2.2.1
    · change (7 : Fin 12) ∈ T
      exact h29.2.2.2
  · refine ⟨30, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h30.1
    · change (2 : Fin 12) ∈ T
      exact h30.2.1
    · change (5 : Fin 12) ∈ T
      exact h30.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h30.2.2.2
  · refine ⟨31, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h31.1
    · change (2 : Fin 12) ∈ T
      exact h31.2.1
    · change (5 : Fin 12) ∈ T
      exact h31.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h31.2.2.2
  · refine ⟨32, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h32.1
    · change (2 : Fin 12) ∈ T
      exact h32.2.1
    · change (6 : Fin 12) ∈ T
      exact h32.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h32.2.2.2
  · refine ⟨33, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h33.1
    · change (2 : Fin 12) ∈ T
      exact h33.2.1
    · change (6 : Fin 12) ∈ T
      exact h33.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h33.2.2.2
  · refine ⟨34, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h34.1
    · change (2 : Fin 12) ∈ T
      exact h34.2.1
    · change (7 : Fin 12) ∈ T
      exact h34.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h34.2.2.2
  · refine ⟨35, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h35.1
    · change (2 : Fin 12) ∈ T
      exact h35.2.1
    · change (7 : Fin 12) ∈ T
      exact h35.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h35.2.2.2
  · refine ⟨36, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h36.1
    · change (2 : Fin 12) ∈ T
      exact h36.2.1
    · change (8 : Fin 12) ∈ T
      exact h36.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h36.2.2.2
  · refine ⟨37, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h37.1
    · change (2 : Fin 12) ∈ T
      exact h37.2.1
    · change (10 : Fin 12) ∈ T
      exact h37.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h37.2.2.2
  · refine ⟨38, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h38.1
    · change (3 : Fin 12) ∈ T
      exact h38.2.1
    · change (4 : Fin 12) ∈ T
      exact h38.2.2.1
    · change (7 : Fin 12) ∈ T
      exact h38.2.2.2
  · refine ⟨39, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h39.1
    · change (3 : Fin 12) ∈ T
      exact h39.2.1
    · change (5 : Fin 12) ∈ T
      exact h39.2.2.1
    · change (6 : Fin 12) ∈ T
      exact h39.2.2.2
  · refine ⟨40, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h40.1
    · change (3 : Fin 12) ∈ T
      exact h40.2.1
    · change (9 : Fin 12) ∈ T
      exact h40.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h40.2.2.2
  · refine ⟨41, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h41.1
    · change (4 : Fin 12) ∈ T
      exact h41.2.1
    · change (6 : Fin 12) ∈ T
      exact h41.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h41.2.2.2
  · refine ⟨42, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h42.1
    · change (4 : Fin 12) ∈ T
      exact h42.2.1
    · change (6 : Fin 12) ∈ T
      exact h42.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h42.2.2.2
  · refine ⟨43, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h43.1
    · change (4 : Fin 12) ∈ T
      exact h43.2.1
    · change (8 : Fin 12) ∈ T
      exact h43.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h43.2.2.2
  · refine ⟨44, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h44.1
    · change (5 : Fin 12) ∈ T
      exact h44.2.1
    · change (7 : Fin 12) ∈ T
      exact h44.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h44.2.2.2
  · refine ⟨45, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h45.1
    · change (5 : Fin 12) ∈ T
      exact h45.2.1
    · change (7 : Fin 12) ∈ T
      exact h45.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h45.2.2.2
  · refine ⟨46, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h46.1
    · change (5 : Fin 12) ∈ T
      exact h46.2.1
    · change (10 : Fin 12) ∈ T
      exact h46.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h46.2.2.2
  · refine ⟨47, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h47.1
    · change (6 : Fin 12) ∈ T
      exact h47.2.1
    · change (8 : Fin 12) ∈ T
      exact h47.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h47.2.2.2
  · refine ⟨48, ?_⟩
    intro i
    fin_cases i
    · change (1 : Fin 12) ∈ T
      exact h48.1
    · change (7 : Fin 12) ∈ T
      exact h48.2.1
    · change (10 : Fin 12) ∈ T
      exact h48.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h48.2.2.2
  · refine ⟨49, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h49.1
    · change (3 : Fin 12) ∈ T
      exact h49.2.1
    · change (6 : Fin 12) ∈ T
      exact h49.2.2.1
    · change (7 : Fin 12) ∈ T
      exact h49.2.2.2
  · refine ⟨50, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h50.1
    · change (3 : Fin 12) ∈ T
      exact h50.2.1
    · change (8 : Fin 12) ∈ T
      exact h50.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h50.2.2.2
  · refine ⟨51, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h51.1
    · change (3 : Fin 12) ∈ T
      exact h51.2.1
    · change (9 : Fin 12) ∈ T
      exact h51.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h51.2.2.2
  · refine ⟨52, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h52.1
    · change (4 : Fin 12) ∈ T
      exact h52.2.1
    · change (6 : Fin 12) ∈ T
      exact h52.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h52.2.2.2
  · refine ⟨53, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h53.1
    · change (4 : Fin 12) ∈ T
      exact h53.2.1
    · change (6 : Fin 12) ∈ T
      exact h53.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h53.2.2.2
  · refine ⟨54, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h54.1
    · change (4 : Fin 12) ∈ T
      exact h54.2.1
    · change (8 : Fin 12) ∈ T
      exact h54.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h54.2.2.2
  · refine ⟨55, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h55.1
    · change (5 : Fin 12) ∈ T
      exact h55.2.1
    · change (7 : Fin 12) ∈ T
      exact h55.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h55.2.2.2
  · refine ⟨56, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h56.1
    · change (5 : Fin 12) ∈ T
      exact h56.2.1
    · change (7 : Fin 12) ∈ T
      exact h56.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h56.2.2.2
  · refine ⟨57, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h57.1
    · change (5 : Fin 12) ∈ T
      exact h57.2.1
    · change (10 : Fin 12) ∈ T
      exact h57.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h57.2.2.2
  · refine ⟨58, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h58.1
    · change (6 : Fin 12) ∈ T
      exact h58.2.1
    · change (8 : Fin 12) ∈ T
      exact h58.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h58.2.2.2
  · refine ⟨59, ?_⟩
    intro i
    fin_cases i
    · change (2 : Fin 12) ∈ T
      exact h59.1
    · change (7 : Fin 12) ∈ T
      exact h59.2.1
    · change (10 : Fin 12) ∈ T
      exact h59.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h59.2.2.2
  · refine ⟨60, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h60.1
    · change (4 : Fin 12) ∈ T
      exact h60.2.1
    · change (6 : Fin 12) ∈ T
      exact h60.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h60.2.2.2
  · refine ⟨61, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h61.1
    · change (4 : Fin 12) ∈ T
      exact h61.2.1
    · change (6 : Fin 12) ∈ T
      exact h61.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h61.2.2.2
  · refine ⟨62, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h62.1
    · change (4 : Fin 12) ∈ T
      exact h62.2.1
    · change (10 : Fin 12) ∈ T
      exact h62.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h62.2.2.2
  · refine ⟨63, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h63.1
    · change (5 : Fin 12) ∈ T
      exact h63.2.1
    · change (7 : Fin 12) ∈ T
      exact h63.2.2.1
    · change (8 : Fin 12) ∈ T
      exact h63.2.2.2
  · refine ⟨64, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h64.1
    · change (5 : Fin 12) ∈ T
      exact h64.2.1
    · change (7 : Fin 12) ∈ T
      exact h64.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h64.2.2.2
  · refine ⟨65, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h65.1
    · change (5 : Fin 12) ∈ T
      exact h65.2.1
    · change (8 : Fin 12) ∈ T
      exact h65.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h65.2.2.2
  · refine ⟨66, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h66.1
    · change (6 : Fin 12) ∈ T
      exact h66.2.1
    · change (10 : Fin 12) ∈ T
      exact h66.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h66.2.2.2
  · refine ⟨67, ?_⟩
    intro i
    fin_cases i
    · change (3 : Fin 12) ∈ T
      exact h67.1
    · change (7 : Fin 12) ∈ T
      exact h67.2.1
    · change (8 : Fin 12) ∈ T
      exact h67.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h67.2.2.2
  · refine ⟨68, ?_⟩
    intro i
    fin_cases i
    · change (4 : Fin 12) ∈ T
      exact h68.1
    · change (5 : Fin 12) ∈ T
      exact h68.2.1
    · change (8 : Fin 12) ∈ T
      exact h68.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h68.2.2.2
  · refine ⟨69, ?_⟩
    intro i
    fin_cases i
    · change (4 : Fin 12) ∈ T
      exact h69.1
    · change (5 : Fin 12) ∈ T
      exact h69.2.1
    · change (9 : Fin 12) ∈ T
      exact h69.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h69.2.2.2
  · refine ⟨70, ?_⟩
    intro i
    fin_cases i
    · change (4 : Fin 12) ∈ T
      exact h70.1
    · change (6 : Fin 12) ∈ T
      exact h70.2.1
    · change (8 : Fin 12) ∈ T
      exact h70.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h70.2.2.2
  · refine ⟨71, ?_⟩
    intro i
    fin_cases i
    · change (4 : Fin 12) ∈ T
      exact h71.1
    · change (6 : Fin 12) ∈ T
      exact h71.2.1
    · change (10 : Fin 12) ∈ T
      exact h71.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h71.2.2.2
  · refine ⟨72, ?_⟩
    intro i
    fin_cases i
    · change (4 : Fin 12) ∈ T
      exact h72.1
    · change (7 : Fin 12) ∈ T
      exact h72.2.1
    · change (8 : Fin 12) ∈ T
      exact h72.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h72.2.2.2
  · refine ⟨73, ?_⟩
    intro i
    fin_cases i
    · change (5 : Fin 12) ∈ T
      exact h73.1
    · change (6 : Fin 12) ∈ T
      exact h73.2.1
    · change (9 : Fin 12) ∈ T
      exact h73.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h73.2.2.2
  · refine ⟨74, ?_⟩
    intro i
    fin_cases i
    · change (5 : Fin 12) ∈ T
      exact h74.1
    · change (7 : Fin 12) ∈ T
      exact h74.2.1
    · change (8 : Fin 12) ∈ T
      exact h74.2.2.1
    · change (9 : Fin 12) ∈ T
      exact h74.2.2.2
  · refine ⟨75, ?_⟩
    intro i
    fin_cases i
    · change (5 : Fin 12) ∈ T
      exact h75.1
    · change (7 : Fin 12) ∈ T
      exact h75.2.1
    · change (10 : Fin 12) ∈ T
      exact h75.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h75.2.2.2
  · refine ⟨76, ?_⟩
    intro i
    fin_cases i
    · change (6 : Fin 12) ∈ T
      exact h76.1
    · change (7 : Fin 12) ∈ T
      exact h76.2.1
    · change (8 : Fin 12) ∈ T
      exact h76.2.2.1
    · change (10 : Fin 12) ∈ T
      exact h76.2.2.2
  · refine ⟨77, ?_⟩
    intro i
    fin_cases i
    · change (6 : Fin 12) ∈ T
      exact h77.1
    · change (7 : Fin 12) ∈ T
      exact h77.2.1
    · change (9 : Fin 12) ∈ T
      exact h77.2.2.1
    · change (11 : Fin 12) ∈ T
      exact h77.2.2.2
lemma seven_labels_forced :
    ∀ T ∈ (Finset.univ : Finset (Fin 12)).powersetCard 7,
      ∃ k : Fin 78, ∀ i : Fin 4, badQuad k i ∈ T := by
  intro T hT
  exact seven_labels_forced_of_card T (Finset.mem_powersetCard.mp hT).2

lemma seven_labels_coplanar {R : Type*} [CommRing R] (a c : R)
    (T : Finset (Fin 12)) (hT : T.card = 7) :
    ∃ q : Fin 4 → Fin 12, Function.Injective q ∧ (∀ i, q i ∈ T) ∧
      planeDet a a c (q 0) (q 1) (q 2) (q 3) = 0 := by
  obtain ⟨k,hk⟩ := seven_labels_forced T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hT⟩)
  exact ⟨badQuad k,badQuad_injective k,hk,diagonal_forced a c k⟩

lemma diagonal_parameter :
    ∀ k : Fin 7, IsSquare (values 1 1 (23/7) k) := by
  intro k
  fin_cases k
  · exact ⟨1, by norm_num [values]⟩
  · exact ⟨17/7, by norm_num [values]⟩
  · exact ⟨17/7, by norm_num [values]⟩
  · exact ⟨16/7, by norm_num [values]⟩
  · exact ⟨30/7, by norm_num [values]⟩
  · exact ⟨26/7, by norm_num [values]⟩
  · exact ⟨26/7, by norm_num [values]⟩

lemma sphere_equation {R : Type*} [CommRing R] (a b c : R) (i : Fin 12) :
    (point a b c i 0)^2+(point a b c i 1)^2+(point a b c i 2)^2 = a^2+b^2+c^2 := by
  fin_cases i
  · change (a)^2+(b)^2+(c)^2 = a^2+b^2+c^2
    ring
  · change (a)^2+(-b)^2+(-c)^2 = a^2+b^2+c^2
    ring
  · change (-a)^2+(b)^2+(-c)^2 = a^2+b^2+c^2
    ring
  · change (-a)^2+(-b)^2+(c)^2 = a^2+b^2+c^2
    ring
  · change (b)^2+(c)^2+(a)^2 = a^2+b^2+c^2
    ring
  · change (b)^2+(-c)^2+(-a)^2 = a^2+b^2+c^2
    ring
  · change (-b)^2+(c)^2+(-a)^2 = a^2+b^2+c^2
    ring
  · change (-b)^2+(-c)^2+(a)^2 = a^2+b^2+c^2
    ring
  · change (c)^2+(a)^2+(b)^2 = a^2+b^2+c^2
    ring
  · change (c)^2+(-a)^2+(-b)^2 = a^2+b^2+c^2
    ring
  · change (-c)^2+(a)^2+(-b)^2 = a^2+b^2+c^2
    ring
  · change (-c)^2+(-a)^2+(b)^2 = a^2+b^2+c^2
    ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A geometric-only parameter: no arithmetic square condition is claimed. -/
lemma geometric_example : ∀ i j k l : Fin 12, i < j → j < k → k < l →
    planeDet (2 : ℤ) 3 5 i j k l ≠ 0 := by
  decide +kernel

#print axioms geometric_example
#print axioms all_chords_square
#print axioms seven_labels_coplanar
#print axioms diagonal_parameter
end Erdos213.TetrahedralOrbit
