import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

inductive IsBad : ℕ → Prop where
  | below_112 : ∀ x, x < 112 → IsBad x
  | step : ∀ x, IsBad (A006368_map x) → IsBad x

theorem not_IsBad_144 (y : ℕ) (h_bad : IsBad y) : y = 144 → False := by
  induction h_bad with
  | below_112 z hz =>
    intro h
    omega
  | step z hz_bad ih =>
    intro h
    -- wait, here we have h : z = 144.
    -- So A006368_map z = 216.
    -- But ih is: A006368_map z = 144 → False.
    -- Since A006368_map z is 216, ih does NOT apply to 216!
    -- So we get stuck!
    sorry
