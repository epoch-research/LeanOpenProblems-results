import Submission.AffineQuadraticImageMass

/-! Distinct-value reciprocal divergence survives arbitrary pointwise
selection among finitely many positive nondegenerate affine quadratics. -/
namespace Erdos1206.AffineQuadraticSelectionMass
open Finset Filter AffineQuadraticImageMass FiniteImageEnergy QuadraticImageMass
open scoped Classical Topology

theorem selected_values_not_summable {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b c : ι → ℕ) (M v w : ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i) (hM : 0 < M)
    (hd : ∀ i, 4*(a i:ℤ)*c i-(b i:ℤ)^2 ≠ 0)
    (P : ℕ × ℕ → Prop) (sel : ℕ × ℕ → ι)
    (hpos : ∀ x, P x → 0 < eval (a (sel x)) (b (sel x)) (c (sel x)) M v w x)
    (hmany : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
      (((range N) ×ˢ (range N)).filter P).card) :
    ¬ Summable (fun n : ℕ => if n∈(fun x =>
      eval (a (sel x)) (b (sel x)) (c (sel x)) M v w x) '' {x | P x}
      then (1:ℝ)/n else 0) := by
  let J := shift M v w
  let E (i : ι) := (100*(BinaryQuadraticEnergy.coeffBound (a i) (b i) (c i)+1)+9)*(2^J)^2
  let K := ∑i : ι, heightBound (a i) (b i) (c i) M v w
  let C := Fintype.card ι * ∑i : ι, E i
  have hK : 0 < K := by
    apply sum_pos (fun i _ => ?_) univ_nonempty
    dsimp [heightBound,shift]
    have := ha i
    positivity
  have hC : 0 < C := by
    apply Nat.mul_pos Fintype.card_pos
    apply sum_pos (fun i _ => ?_) univ_nonempty
    dsimp [E]
    exact Nat.mul_pos (by omega) (pow_pos (pow_pos (by decide) _) _)
  apply QuadraticImageMass.distinct_values_not_summable P
    (fun x => eval (a (sel x)) (b (sel x)) (c (sel x)) M v w x)
    K C (J+2) hK hC hpos
  · intro x
    exact eval_lower _ _ _ _ _ _ (ha _) (hc _) hM x
  · intro k x hx
    have hh : heightBound (a (sel x)) (b (sel x)) (c (sel x)) M v w ≤ K :=
      single_le_sum (f := fun i => heightBound (a i) (b i) (c i) M v w)
        (fun i _ => Nat.zero_le _) (mem_univ (sel x))
    exact (eval_upper _ _ _ _ _ _ _ hx).trans (Nat.mul_le_mul_right _ hh)
  · intro k
    calc
      _ ≤ Fintype.card ι * ∑i : ι,
          (equalPairs (grid k) (eval (a i) (b i) (c i) M v w)).card :=
        selector_energy (grid k) (fun i => eval (a i) (b i) (c i) M v w) sel
      _ ≤ Fintype.card ι * ∑i : ι, E i*(k+(J+2))*(2^k)^2 := by
        apply Nat.mul_le_mul_left
        exact sum_le_sum (fun i _ => equal_pairs_card_bound _ _ _ _ _ _ k hM (hd i))
      _ = C*(k+(J+2))*(2^k)^2 := by dsimp [C]; simp only [← sum_mul]; ring
  · have hh := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).eventually hmany
    simpa only [grid,Nat.cast_pow,Nat.cast_ofNat] using hh

#print axioms selected_values_not_summable
end Erdos1206.AffineQuadraticSelectionMass
