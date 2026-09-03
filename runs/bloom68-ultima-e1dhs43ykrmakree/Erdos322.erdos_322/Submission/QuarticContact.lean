import Mathlib

namespace QuarticContact

/-- Exact polynomial identity for the contact construction. This does not
assert multiplicity of representations at any fixed target. -/
theorem contact_identity (p q r : ℤ) :
    let J := 2 * (p ^ 4 + q ^ 4 + r ^ 4) +
      3 * (p ^ 2 * q ^ 2 + p ^ 2 * r ^ 2 + q ^ 2 * r ^ 2)
    (-J + 6 * p * q * r * (p + r - q)) ^ 4 +
      (-J + 6 * p * q * r * (p + q - r)) ^ 4 +
      (-J + 6 * p * q * r * (q + r - p)) ^ 4 +
      (-J + 6 * p * q * r * (-p - q - r)) ^ 4 =
    (2 * J ^ 2 + 216 * p ^ 2 * q ^ 2 * r ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2)) ^ 2 := by
  dsimp
  ring

/-- The centered contact surface has the explicit cubic and quartic terms. -/
theorem contact_expansion (p q r t : ℤ) :
    let J := 2 * (p ^ 4 + q ^ 4 + r ^ 4) +
      3 * (p ^ 2 * q ^ 2 + p ^ 2 * r ^ 2 + q ^ 2 * r ^ 2)
    (1 + t * (p + r - q)) ^ 4 +
      (1 + t * (p + q - r)) ^ 4 +
      (1 + t * (q + r - p)) ^ 4 +
      (1 + t * (-p - q - r)) ^ 4 =
    (2 + 6 * (p ^ 2 + q ^ 2 + r ^ 2) * t ^ 2) ^ 2 -
      96 * p * q * r * t ^ 3 - 16 * J * t ^ 4 := by
  dsimp
  ring

end QuarticContact

#print axioms QuarticContact.contact_identity
#print axioms QuarticContact.contact_expansion
