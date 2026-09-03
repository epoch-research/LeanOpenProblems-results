import FormalConjecturesUtil

/-! Avoiding primitive quadruples alone does not give Sidon cubes.
This is an auxiliary limitation, not a disproof of the conjecture in `Spec.lean`. -/

namespace Erdos1206

lemma positive_density_without_primitive_quadruples_not_cube_sidon :
    ∃ A : Set ℕ, 0 < A.lowerDensity ∧
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        Nat.gcd (Nat.gcd a b) (Nat.gcd c d) ≠ 1) ∧
      ¬ IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  let A : Set ℕ := {n | Even n}
  refine ⟨A, ?_, ?_, ?_⟩
  · have hd : A.lowerDensity = (1 : ℝ) / 2 := Nat.hasDensity_even.liminf_eq
    rw [hd]
    norm_num
  · intro a ha b hb c hc d hd heq
    have h₂ : 2 ∣ Nat.gcd (Nat.gcd a b) (Nat.gcd c d) :=
      Nat.dvd_gcd (Nat.dvd_gcd (even_iff_two_dvd.mp ha) (even_iff_two_dvd.mp hb))
        (Nat.dvd_gcd (even_iff_two_dvd.mp hc) (even_iff_two_dvd.mp hd))
    rw [heq] at h₂
    norm_num at h₂
  · intro hs
    have hm (n : ℕ) (hn : Even n) : n ^ 3 ∈ (fun a : ℕ => a ^ 3) '' A :=
      ⟨n, hn, rfl⟩
    have h := hs _ (hm 2 (by decide)) _ (hm 18 (by decide))
      _ (hm 24 (by decide)) _ (hm 20 (by decide)) (by norm_num)
    norm_num at h

end Erdos1206
