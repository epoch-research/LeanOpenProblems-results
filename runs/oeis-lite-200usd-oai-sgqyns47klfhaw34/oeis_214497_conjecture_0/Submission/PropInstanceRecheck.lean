import FormalConjectures.Util.ProblemImports
#set_option synthInstance.maxHeartbeats 100000 in
#synth Nontrivial Prop
#set_option synthInstance.maxHeartbeats 100000 in
#synth Subsingleton Prop
#check Fintype.card_prop
#check prop_complete
#check Classical.propComplete
example : Fintype.card Prop = 2 := Fintype.card_prop
example : Nontrivial Prop := inferInstance
-- if Subsingleton Prop existed, this would close
example : ¬ Subsingleton Prop := by
  intro h
  have htf : (True : Prop) = False := Subsingleton.elim _ _
  exact true_ne_false htf
