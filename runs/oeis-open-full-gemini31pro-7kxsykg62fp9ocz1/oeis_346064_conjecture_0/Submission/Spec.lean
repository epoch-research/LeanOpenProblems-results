import FormalConjectures.Util.ProblemImports

open Nat Finset List

noncomputable def A346064 (n : ℕ) : ℕ :=
  if n < 10 then 0 else
  let D := Nat.digits 10 n
  let L := D.length

  let indices := Finset.range L
  let all_digits := Finset.range 10

  let index_pairs : Finset (ℕ × ℕ) :=
    (indices.product indices).filter (fun p => p.fst < p.snd)

  let transformed_numbers : Finset ℕ := index_pairs.biUnion fun ⟨i, j⟩ =>
    let d_i_orig := D[i]!
    let d_j_orig := D[j]!

    let allowed_replacements_r := all_digits.filter (fun r => r ≠ d_i_orig)
    let allowed_replacements_s := all_digits.filter (fun s => s ≠ d_j_orig)

    Finset.image (fun ⟨r, s⟩ =>
      let D' := D.set i r
      let D'' := D'.set j s
      Nat.ofDigits 10 D''
    ) (Finset.product allowed_replacements_r allowed_replacements_s)

  (transformed_numbers.filter Nat.Prime).card

theorem oeis_346064_conjecture_0 : ∀ n, 10 ≤ n → A346064 n > 0 := by
  sorry

theorem oeis_346064_conjecture_0.disproof : ¬ (type_of% @oeis_346064_conjecture_0) := by
  sorry
