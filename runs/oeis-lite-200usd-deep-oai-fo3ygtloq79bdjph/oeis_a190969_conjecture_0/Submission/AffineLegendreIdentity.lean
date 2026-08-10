import FormalConjectures.Util.ProblemImports

open MvPolynomial

noncomputable section

/-- Denominator-cleared two-variable polynomial certificate for the affine change from
`x^3 - 35x + 98` to the Legendre cubic with
`r0=(7-s)/2`, `a=(s-21)/2`, and `λ=(1-3s)/32`.
Here `S` represents `s`, `Y` represents the Legendre coordinate,
`U=7-S=2*r0`, `V=S-21=2*a`, `W=1-3S=32*λ`, and `Z=U+VY=2*(r0+aY)`.
The identity is exactly
`256*(f(Z/2) - (V/2)^3*Y*(Y-1)*(Y-W/32))`
expanded and factored by `S^2+7`. -/
lemma affine_legendre_cleared_identity :
    let S := (X 0 : MvPolynomial (Fin 2) ℤ)
    let Y := (X 1 : MvPolynomial (Fin 2) ℤ)
    let U := (7 : MvPolynomial (Fin 2) ℤ) - S
    let V := S - 21
    let W := (1 : MvPolynomial (Fin 2) ℤ) - 3 * S
    let Z := U + V * Y
    (32 * Z ^ 3 - 4480 * Z + 25088) - V ^ 3 * Y * (Y - 1) * (32 * Y - W) =
      - (Y - 1) * V * (S ^ 2 + 7) * (3 * Y * S - 63 * Y - 32) := by
  ring

end
