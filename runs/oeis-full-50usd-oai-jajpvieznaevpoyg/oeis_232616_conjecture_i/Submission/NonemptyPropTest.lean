import FormalConjectures.Util.ProblemImports
open Classical
example : False := Classical.choice (inferInstance : Nonempty False)
