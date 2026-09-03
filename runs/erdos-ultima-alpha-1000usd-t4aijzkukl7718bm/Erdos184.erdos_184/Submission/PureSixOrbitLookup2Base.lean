import Submission.PureSixOrbitLookup2Defs000
import Mathlib.Data.Fin.Basic
namespace Erdos184Work.PureSixOrbitLookup2
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Representatives := Fin 10
def representativeKey (r : Representatives) : ℕ := (if r.val < 5 then (if r.val < 2 then (if r.val < 1 then 766166303 else 832521503) else (if r.val < 3 then 1077466343 else (if r.val < 4 then 1118938335 else 1118938338))) else (if r.val < 7 then (if r.val < 6 then 1118938340 else 1118938343) else (if r.val < 8 then 1118938364 else (if r.val < 9 then 1118938401 else 1118938402))))
def groupOfCode (c : ℕ) : Fin 64 := ⟨c % 64,Nat.mod_lt _ (by decide)⟩
def representativeOfCode (c : ℕ) : Representatives := ⟨c / 64 % 10,Nat.mod_lt _ (by decide)⟩
def table : Table ℕ := (.branch 1822424396 block0 block1)
end Erdos184Work.PureSixOrbitLookup2
