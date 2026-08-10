import FormalConjectures.Util.ProblemImports
namespace BoundTest
def N : Nat := 201886 * 3 ^ 39101 - 1
theorem hbound : N + 1 < 2 ^ 70000 := by native_decide
end BoundTest
