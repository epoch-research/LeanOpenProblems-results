import Mathlib

def max_F : ℤ := 155000

def mkByteArray (n : Nat) : ByteArray :=
  ByteArray.mk (List.toArray (List.replicate n (0 : UInt8)))

def empty_arr : Array ByteArray :=
  List.toArray (List.replicate max_F.toNat (mkByteArray 1626))

#eval empty_arr.size
