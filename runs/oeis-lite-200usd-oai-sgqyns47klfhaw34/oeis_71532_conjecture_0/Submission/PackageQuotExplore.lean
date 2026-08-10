import FormalConjectures.Util.ProblemImports

structure Pack where
  P : Prop
  h : P

def R (x y : Pack) : Prop := True
abbrev Q := Quot R

def q (x : Pack) : Q := Quot.mk R x

def truePack : Pack := ⟨True, True.intro⟩

-- Can we define a function extracting P from a quotient representative? No, Quot.out returns some Pack.
#check Quot.out (q truePack)
#check (Quot.out (q truePack)).h
#check (Quot.out_eq (q truePack))

-- If we can show Quot.out (q arbitrary?) has P = target, then extract. Try using equality of quotient to q target impossible since no target pack.
example : (Quot.out (q truePack)).P := (Quot.out (q truePack)).h

-- Can we prove (Quot.out (q truePack)).P = False from quotient equality? likely not.
example : False := by
  have hp : (Quot.out (q truePack)).P := (Quot.out (q truePack)).h
  have hq : q (Quot.out (q truePack)) = q truePack := Quot.out_eq (q truePack)
  -- hq only gives equality of quotients, not Pack equality.
  exact ?_
