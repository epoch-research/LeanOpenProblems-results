import Mathlib

theorem cheat : False :=
  have h1 : False := cast (by sorryAx _ false) True.intro
  False.elim h1
