import FormalConjecturesUtil

/-! An explicit eight-element field, used for kernel-checked matrix certificates. -/
namespace Erdos714BinaryEight
structure K where
  code : Fin 8
  deriving DecidableEq, Fintype

def elt (n : Fin 8) : K := ⟨n⟩
def addTable : Fin 8 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![1,0,3,2,5,4,7,6],![2,3,0,1,6,7,4,5],![3,2,1,0,7,6,5,4],![4,5,6,7,0,1,2,3],![5,4,7,6,1,0,3,2],![6,7,4,5,2,3,0,1],![7,6,5,4,3,2,1,0]]
def mulTable : Fin 8 → Fin 8 → Fin 8 := ![![0,0,0,0,0,0,0,0],![0,1,2,3,4,5,6,7],![0,2,4,6,3,1,7,5],![0,3,6,5,7,4,1,2],![0,4,3,7,6,2,5,1],![0,5,1,4,2,7,3,6],![0,6,7,1,5,3,2,4],![0,7,5,2,1,6,4,3]]
def invTable : Fin 8 → Fin 8 := ![0,1,5,6,7,2,3,4]
instance : Zero K := ⟨elt 0⟩
instance : One K := ⟨elt 1⟩
def rawAdd (a b : Fin 8) : Fin 8 := ⟨Nat.xor a.val b.val % 8, Nat.mod_lt _ (by decide)⟩
def rawMul (a b : Fin 8) : Fin 8 :=
  let p := Nat.xor (Nat.xor (if b.val % 2=1 then a.val else 0)
    (if b.val / 2 % 2=1 then a.val*2 else 0)) (if b.val / 4=1 then a.val*4 else 0)
  let p := if 16≤p then Nat.xor p 22 else p
  let p := if 8≤p then Nat.xor p 11 else p
  ⟨p % 8,Nat.mod_lt _ (by decide)⟩
instance : Add K := ⟨fun a b => elt (rawAdd a.code b.code)⟩
instance : Mul K := ⟨fun a b => elt (rawMul a.code b.code)⟩
instance : Neg K := ⟨id⟩
instance : Inv K := ⟨fun a => elt (invTable a.code)⟩
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
instance : CommRing K where
  add := fun a b => elt (rawAdd a.code b.code)
  mul := fun a b => elt (rawMul a.code b.code)
  zero := elt 0
  one := elt 1
  neg := id
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by decide +kernel
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  add_comm := by decide +kernel
  neg_add_cancel := by decide +kernel
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  mul_comm := by decide +kernel
  left_distrib := by decide +kernel
  right_distrib := by decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
instance : Field K where
  inv := fun a => elt (invTable a.code)
  mul_inv_cancel := by decide +kernel
  inv_zero := by decide +kernel
  exists_pair_ne := ⟨elt 0,elt 1,by decide⟩
  nnqsmul := _
  nnqsmul_def := by intros; rfl
  qsmul := _
  qsmul_def := by intros; rfl
lemma card : Fintype.card K=8 := by decide
lemma generator_equation : (elt 2)^3+elt 2+1=0 := by decide
end Erdos714BinaryEight
#print axioms Erdos714BinaryEight.instFieldK
