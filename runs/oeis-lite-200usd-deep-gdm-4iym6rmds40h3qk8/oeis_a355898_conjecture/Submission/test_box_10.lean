import Mathlib

partial def get_negneg (P : Prop) : (P → False) → False :=
  fun h_not =>
    get_negneg P h_not
