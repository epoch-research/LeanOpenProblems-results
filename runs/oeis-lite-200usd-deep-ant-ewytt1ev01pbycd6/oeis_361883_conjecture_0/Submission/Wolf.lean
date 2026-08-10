import FormalConjectures.Util.ProblemImports

open Finset

/-- In a finite cyclic group inside a commutative ring, if `g` is a generator and
`g^2 - 1` is a unit, then the sum of the squares of all elements is `0`.
We prove the abstract statement: sum over a cyclic group `G` (as units of a comm ring `R`)
of `(x:R)^2 = 0` provided a generator `g` has `(g:R)^2 - 1` a unit. -/
lemma sum_units_sq_zero (n : ℕ) [NeZero n] (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) :
    ∑ x : (ZMod n)ˣ, ((x : ZMod n) ^ 2) = 0 := by
  set R := ZMod n
  set Sig := ∑ x : Rˣ, ((x : R) ^ 2) with hSig
  set u : Rˣ := ZMod.unitOfCoprime 2 h2 with hu
  have hval : (u : R) = (2 : R) := by rw [hu]; exact ZMod.coe_unitOfCoprime 2 h2
  -- multiplication by u permutes the units, so ∑ (u*x)^2 = ∑ x^2
  have hperm : ∑ x : Rˣ, ((↑(u * x) : R) ^ 2) = Sig := by
    rw [hSig]
    exact Equiv.sum_comp (Equiv.mulLeft u) (fun x : Rˣ => ((x : R) ^ 2))
  -- but ∑ (u*x)^2 = (↑u)^2 * ∑ x^2
  have hexp : ∑ x : Rˣ, ((↑(u * x) : R) ^ 2) = (↑u : R) ^ 2 * Sig := by
    rw [hSig, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Units.val_mul, mul_pow]
  have hkey : ((↑u : R) ^ 2 - 1) * Sig = 0 := by
    have h : (↑u : R) ^ 2 * Sig = Sig := by rw [← hexp, hperm]
    linear_combination h
  -- (↑u)^2 - 1 = 3, a unit
  have h3eq : (↑u : R) ^ 2 - 1 = 3 := by rw [hval]; ring
  rw [h3eq] at hkey
  -- 3 is a unit in R
  have h3unit : IsUnit (3 : R) :=
    ⟨ZMod.unitOfCoprime 3 h3, by rw [ZMod.coe_unitOfCoprime]; norm_num⟩
  obtain ⟨v, hv⟩ := h3unit
  calc Sig = (↑v⁻¹ : R) * ((3 : R) * Sig) := by rw [← mul_assoc, ← hv]; simp
    _ = 0 := by rw [hkey]; ring
