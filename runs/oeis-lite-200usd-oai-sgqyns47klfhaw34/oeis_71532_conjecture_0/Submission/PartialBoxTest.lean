import FormalConjectures.Util.ProblemImports

inductive Box (P : Prop) where
  | mk : Box P

partial def outBox (P : Prop) (b : Box P) : P := outBox P b
#print axioms outBox

inductive EBox (P : Prop) where

partial def outEBox (P : Prop) (b : EBox P) : P := nomatch b
#print axioms outEBox

partial def mkEBox (P : Prop) : EBox P := mkEBox P
#print axioms mkEBox

example (P : Prop) : P := outEBox P (mkEBox P)
