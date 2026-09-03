import Submission.TypeIIBounds

/-!
# A character-dependent prefix in a rectangular bilinear mean

Only a logarithmic Fourier-completion loss is paid when each primitive
character chooses its own initial cutoff on the first side.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma rectangular_prefix_factorization {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A B : Finset ℕ) (a b : ℕ → ℂ) (T : ℕ) :
    (∑ m ∈ A, ∑ n ∈ B, if m ≤ T then
      (a m*b n)*χ ((m*n : ℕ) : ZMod q) else 0) =
      (∑ m ∈ A with m ≤ T, a m*χ (m : ZMod q))*
        (∑ n ∈ B, b n*χ (n : ZMod q)) := by
  rw [sum_filter,sum_mul]
  apply sum_congr rfl
  intro m hm
  by_cases hmT : m ≤ T
  · simp only [if_pos hmT,mul_sum,Nat.cast_mul,map_mul]
    exact sum_congr rfl (fun n hn => by ring)
  · simp [hmT]

/-- The cutoff is allowed to depend on the character, not just on the modulus. -/
theorem adaptive_prefix_bilinear_large_sieve_nat
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℕ) (a b : ℕ → ℂ) (X Y : ℕ)
    (hA : ∀ n ∈ A, n ≤ X) (hB : ∀ n ∈ B, n ≤ Y)
    (T : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hT : ∀ q ∈ M, ∀ χ ∈ C q, T q χ ≤ X) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      ‖∑ m ∈ A with m ≤ T q χ, a m*χ (m : ZMod (q : ℕ))‖*
        ‖∑ n ∈ B, b n*χ (n : ZMod (q : ℕ))‖) ≤
      (2+Real.log ((X : ℝ)+2))*Real.sqrt
        ((2*(Q : ℝ)^2+4*(2*Real.pi*X+1))*(2*(Q : ℝ)^2+4*(2*Real.pi*Y+1))*
          (∑ n ∈ A, ‖a n‖^2)*(∑ n ∈ B, ‖b n‖^2)) := by
  let W := X+2
  letI : NeZero W := ⟨by dsimp [W]; omega⟩
  let e : ℕ ↪ ℤ := ⟨fun n => n, Nat.cast_injective⟩
  have hh := adaptive_interval_cutoff_large_sieve (show 2 ≤ W by dsimp [W]; omega)
    M Q hQ hM C hC (A.map e) (B.map e) (fun z => a z.toNat) (fun z => b z.toNat)
    X Y (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_ ?_
    (fun z => (z.toNat : ZMod W)) (fun _ => 0) (fun q χ => T q χ+1)
    (fun q hq χ hχ => by have := hT q hq χ hχ; dsimp [W]; omega)
  · simp only [sum_map,e,Function.Embedding.coeFn_mk,Int.toNat_natCast,
      ← Nat.cast_mul,Int.cast_natCast,add_zero] at hh
    have he : (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
        ‖∑ m ∈ A, ∑ n ∈ B, if (m : ZMod W).val < T q χ+1 then
          (a m*b n)*χ ((m*n : ℕ) : ZMod (q : ℕ)) else 0‖) =
        ∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
          ‖∑ m ∈ A with m ≤ T q χ, a m*χ (m : ZMod (q : ℕ))‖*
            ‖∑ n ∈ B, b n*χ (n : ZMod (q : ℕ))‖ := by
      apply sum_congr rfl
      intro q hq
      congr 1
      apply sum_congr rfl
      intro χ hχ
      rw [← norm_mul,← rectangular_prefix_factorization]
      congr 1
      apply sum_congr rfl
      intro m hm
      rw [ZMod.val_natCast_of_lt (show m < W by have := hA m hm; dsimp [W]; omega)]
      simp only [Nat.lt_succ_iff]
    rw [he] at hh
    simpa only [W,Nat.cast_add,Nat.cast_ofNat] using hh
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := mem_map.mp hz
    simpa only [e,Function.Embedding.coeFn_mk,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      using (Nat.cast_le (α := ℝ)).mpr (hA n hn)
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := mem_map.mp hz
    simpa only [e,Function.Embedding.coeFn_mk,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      using (Nat.cast_le (α := ℝ)).mpr (hB n hn)

end Erdos821.AnalyticSieve
