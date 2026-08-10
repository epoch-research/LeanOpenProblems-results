import FormalConjectures.Util.ProblemImports

namespace WrapNatNumeralInspect
inductive WNat where | mk : Nat → WNat
instance : Zero WNat := ⟨WNat.mk 0⟩
instance : One WNat := ⟨WNat.mk 0⟩
instance : Mul WNat := ⟨fun _ _ => WNat.mk 0⟩
#check (0 : WNat)
#check (1 : WNat)
#check (show (0 : WNat) = (One.one : WNat) from rfl)
#check (show (0 : WNat) = 1 from rfl)
set_option pp.all true in
#check (show (0 : WNat) = 1 from rfl)
end WrapNatNumeralInspect
