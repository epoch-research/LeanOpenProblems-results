import Mathlib

def mkByteArray (n : Nat) : ByteArray :=
  ByteArray.mk (List.toArray (List.replicate n (0 : UInt8)))

def empty_arr : Array ByteArray :=
  List.toArray (List.replicate 155000 (mkByteArray 20500))

#eval empty_arr.size
