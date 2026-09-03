import Submission.PowerTwoNormObstruction
import Submission.FinitePrimeSegments

/-! A uniform finite prime-path length bound for the restricted similarity
step families. This does not bound paths mixing different similarity factors. -/
namespace Erdos952Investigation.UniformSimilaritySegments
open FinitePrimeSegments SimilarityStepObstruction PowerTwoNormObstruction
set_option maxHeartbeats 0

noncomputable def lengthBound : ℕ := segmentBound 13 4225

lemma exception_card_le : (exceptionSet 13).card ≤ 729 := by
  classical
  let S := (Finset.Icc (-13 : ℤ) 13).product (Finset.Icc (-13 : ℤ) 13)
  have hsub : (exceptionSet 13).image (fun z => (z.re,z.im)) ⊆ S := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    have hn := (mem_exceptionSet 13 z).mp hz
    rw [gaussian_norm_sq] at hn
    norm_num at hn
    have hr : -13 ≤ z.re ∧ z.re ≤ 13 := by
      constructor <;> nlinarith [sq_nonneg z.im]
    have hi : -13 ≤ z.im ∧ z.im ≤ 13 := by
      constructor <;> nlinarith [sq_nonneg z.re]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr,Finset.mem_Icc.mpr hi⟩
  have hc := Finset.card_le_card hsub
  have hf : Function.Injective (fun z : GaussianInt => (z.re,z.im)) := by
    intro z w he
    exact Zsqrtd.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
  rw [Finset.card_image_of_injective _ hf] at hc
  norm_num [S] at hc
  exact hc

lemma lengthBound_le : lengthBound ≤ 3084980 := by
  dsimp [lengthBound,segmentBound]
  have hh := exception_card_le
  omega

/-- The same bound works for every starting point and every common step
factor coprime in norm to65. No infinite sequence hypothesis is used. -/
theorem no_long_similar_prime_segment (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Set.InjOn x (Set.Iic lengthBound))
    (hp : ∀ n ≤ lengthBound, Prime (x n)) :
    ¬ ∀ n < lengthBound, ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  intro hs
  obtain ⟨b,hb⟩ := exists_block_avoiding (exceptionSet 13) 4225 x
    (fun _ hi _ hj he => hx (Set.mem_Iio.mp hi).le (Set.mem_Iio.mp hj).le he)
  let K := b.val*4226
  have hidx (i : Fin 4226) : K+i.val < lengthBound :=
    block_index_lt (exceptionSet 13).card 4225 b i
  have hlarge (i : Fin 4226) : 169 < (x (K+i.val)).norm := by
    have hn := hb i
    change x (K+i.val) ∉ exceptionSet 13 at hn
    rw [mem_exceptionSet] at hn
    norm_num at hn
    exact hn
  apply no_unit_multiple_allowed_segment g hg (fun n => x (K+n))
  · intro i hi j hj he
    change i ≤ 4225 at hi
    change j ≤ 4225 at hj
    exact Nat.add_left_cancel (hx (hidx ⟨i,by omega⟩).le (hidx ⟨j,by omega⟩).le he)
  · intro i hi
    exact NormEightOnly.prime_allowed (hp (K+i) (hidx ⟨i,by omega⟩).le)
      (hlarge ⟨i,by omega⟩)
  · intro i hi
    simpa only [Nat.add_assoc] using hs (K+i) (hidx ⟨i,by omega⟩)

/-- An explicit integer bound, uniform over the entire restricted similarity
family. It says nothing about arbitrary changes of the common factor. -/
theorem no_3084980_similar_prime_steps (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Set.InjOn x (Set.Iic 3084980))
    (hp : ∀ n ≤ 3084980, Prime (x n)) :
    ¬ ∀ n < 3084980, ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  intro hs
  apply no_long_similar_prime_segment g hg x
    (fun i hi j hj he => hx (hi.trans lengthBound_le) (hj.trans lengthBound_le) he)
    (fun n hn => hp n (hn.trans lengthBound_le))
  exact fun n hn => hs n (hn.trans_le lengthBound_le)

/-- A single finite length bound works for every exponent in the constant
power-of-two squared-norm restriction. -/
theorem no_3084980_constant_power_two_steps (k : ℕ) (x : ℕ → GaussianInt)
    (hx : Set.InjOn x (Set.Iic 3084980)) (hp : ∀ n ≤ 3084980, Prime (x n)) :
    ¬ ∀ n < 3084980, (x (n+1)-x n).norm = (2 : ℤ)^k := by
  intro hs
  apply no_3084980_similar_prime_steps (ramified^k) (ramified_power_coprime k) x hx hp
  exact fun n hn => norm_two_power_factorization k _ (hs n hn)

#print axioms no_long_similar_prime_segment
#print axioms no_3084980_similar_prime_steps
#print axioms no_3084980_constant_power_two_steps
end Erdos952Investigation.UniformSimilaritySegments
