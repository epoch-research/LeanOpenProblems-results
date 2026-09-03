import Submission.PrimeCountingLower

/-! Every prime-class cover has a replacement using polynomially bounded primes.
This preserves arbitrary overlaps; it does not turn a cover into an exact cover. -/
namespace Erdos970.BoundedPrimeCover
open Finset

/-- Primes at least m hit at most one point of [0,m), so replace them with
distinct enumerated primes whose indices are between m and m+k. -/
theorem normalize {P : Finset ℕ} {r : ℕ → ℕ} {m k : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hk : P.card ≤ k)
    (hc : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    ∃ Q : Finset ℕ, ∃ s : ℕ → ℕ,
      (∀ q ∈ Q, q.Prime) ∧ Q.card ≤ k ∧
      (∀ q ∈ Q, q ≤ 256 * (m + k + 1) ^ 2) ∧
      (∀ x < m, ∃ q ∈ Q, x ≡ s q [MOD q]) := by
  classical
  let e := P.equivFin
  let f : P → ℕ := fun p => if p.val < m then p.val else Nat.nth Nat.Prime (m + (e p).val)
  have hfsmall (p : P) (hp : p.val < m) : f p = p.val := by simp [f, hp]
  have hfbig (p : P) (hp : ¬p.val < m) : m ≤ f p := by
    have h := Nat.add_two_le_nth_prime (m + (e p).val)
    dsimp [f]; rw [if_neg hp]; omega
  have hinj : Function.Injective f := by
    intro p q hpq
    by_cases hp : p.val < m <;> by_cases hq : q.val < m
    · apply Subtype.ext
      simpa [f, hp, hq] using hpq
    · have := hfbig q hq
      rw [← hpq, hfsmall p hp] at this
      omega
    · have := hfbig p hp
      rw [hpq, hfsmall q hq] at this
      omega
    · have he : Nat.nth Nat.Prime (m + (e p).val) = Nat.nth Nat.Prime (m + (e q).val) := by
        simpa [f, hp, hq] using hpq
      have he' := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective he
      apply e.injective
      apply Fin.ext
      omega
  let Q := univ.image f
  let s := Function.extend f (fun p : P => r p.val % p.val) (fun _ => 0)
  have hs (p : P) : s (f p) = r p.val % p.val := hinj.extend_apply _ _ p
  refine ⟨Q, s, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, _, rfl⟩ := mem_image.mp hq
    dsimp [f]
    split_ifs
    · exact hP p.val p.property
    · exact Nat.prime_nth_prime _
  · have hh : Q.card ≤ P.card := by
      exact card_image_le.trans_eq (by simp)
    exact hh.trans hk
  · intro q hq
    obtain ⟨p, _, rfl⟩ := mem_image.mp hq
    by_cases hp : p.val < m
    · rw [hfsmall p hp]
      have hmul : m + k + 1 ≤ (m + k + 1) ^ 2 := Nat.le_self_pow (by omega) _
      nlinarith
    · have hi : (e p).val < P.card := (e p).isLt
      have hle : m + (e p).val + 1 ≤ m + k + 1 := by omega
      have hh := PrimeCountingLower.nth_prime_quadratic (m + (e p).val)
      have hn : Nat.nth Nat.Prime (m + (e p).val) ≤ 256 * (m + (e p).val + 1) ^ 2 := by
        exact_mod_cast hh
      have hb := hn.trans (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hle 2))
      simpa [f, hp] using hb
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := hc x hx
    let p' : P := ⟨p, hp⟩
    refine ⟨f p', mem_image.mpr ⟨p', mem_univ _, rfl⟩, ?_⟩
    rw [hs]
    by_cases hpm : p < m
    · rw [hfsmall p' hpm]
      simpa only [Nat.ModEq, Nat.mod_mod] using hxp
    · have hxeq : x = r p % p := by
        change x % p = r p % p at hxp
        rwa [Nat.mod_eq_of_lt (by omega)] at hxp
      change x ≡ r p % p [MOD f p']
      rw [← hxeq]

#print axioms normalize
end Erdos970.BoundedPrimeCover
