import FormalConjectures.Util.ProblemImports

#check Computability.FinEncoding
#check finEncodingListBool
#check finEncodingListBoolProdListBool
#synth Computability.FinEncoding (List Bool)
#synth Computability.FinEncoding (List Bool × List Bool)
#synth Fintype (List Bool)
#synth Finite (List Bool)
#check Fintype.ofFinite (α := List Bool)
