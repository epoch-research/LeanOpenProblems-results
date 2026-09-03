import Submission.DoublePetersenGraph
open SimpleGraph
#check @Walk.cons
#check @Walk.isCycle_def
#check @Walk.isTrail_def
open Erdos184Work.DoublePetersenGraph Erdos184Work
example (e : Fin 15) : graph.Adj (.inl (PetersenBase.src e)) (.inr (e,false)) := Or.inl rfl
example (e : Fin 15) : graph.Walk (.inl (PetersenBase.src e)) (.inl (PetersenBase.src e)) :=
  .cons (show graph.Adj (.inl (PetersenBase.src e)) (.inr (e,false)) from Or.inl rfl)
  (.cons (show graph.Adj (.inr (e,false)) (.inl (PetersenBase.dst e)) from Or.inr rfl)
  (.cons (show graph.Adj (.inl (PetersenBase.dst e)) (.inr (e,true)) from Or.inr rfl)
  (.cons (show graph.Adj (.inr (e,true)) (.inl (PetersenBase.src e)) from Or.inl rfl) .nil)))
