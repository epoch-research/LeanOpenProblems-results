import FormalConjectures.Util.ProblemImports

set_option google.answer "always_true"

structure MyThm : Prop where
  proof : 0 = 1

def my_thm_inst : MyThm := answer(sorry)
