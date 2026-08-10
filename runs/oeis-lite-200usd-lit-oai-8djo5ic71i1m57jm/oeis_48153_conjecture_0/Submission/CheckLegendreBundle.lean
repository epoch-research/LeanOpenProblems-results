import FormalConjectures.Util.ProblemImports
#check legendreSym
#check legendreSym.toMonoidHom
#check legendreSym.mulChar
#check (legendreSym 7 : ℤ → ℤ)
#check (legendreSym 7 : MulChar (ZMod 7) ℤ)
#check quadraticChar (ZMod 7)
#check (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)
