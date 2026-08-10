import FormalConjectures.Util.ProblemImports

def test : IO Unit := do
  try
    let entries ← System.FilePath.readDir "."
    pure ()
  catch _ =>
    pure ()










