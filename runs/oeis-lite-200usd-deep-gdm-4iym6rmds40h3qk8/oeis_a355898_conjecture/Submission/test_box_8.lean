import Mathlib

def P : Prop := False

partial def get_negneg_specific : (P → False) → False :=
  get_negneg_specific
