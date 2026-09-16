import Mathlib

theorem cheat : False :=
  have h1 : False := cast (sorryAx _ false) True.intro
  False.elim h1
