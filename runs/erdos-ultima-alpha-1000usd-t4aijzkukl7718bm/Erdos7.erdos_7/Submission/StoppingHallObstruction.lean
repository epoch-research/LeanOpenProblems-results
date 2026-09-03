import Submission.StoppingDigitRestriction
import Submission.DivisorAssignment

/-! Every predictable one-digit restriction of a minimum-period odd cover
has a genuine Hall deficiency among its nontrivial divisor resources. -/
namespace Erdos7StoppingHallObstruction
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7StoppingDigitRestriction Erdos7DivisorAssignment
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Stronger than a repeated-modulus obstruction: some active subfamily has
more members than the union of ALL its available nontrivial divisor moduli. -/
theorem minimal_period_hall_deficiency {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))
    (hT : Predictable T) (V : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀))
    (hV : PredictableValue T V) :
    ∃ s : Finset {k // active p E i₀ T V (e k) (a k)},
      (s.biUnion (fun k =>
        (∏ i, p i ^ eraseExponent i₀
          (T (zmodDigits (p i₀) (E i₀) (a k.val))).val (e k.val) i).divisors.erase 1)).card
        < s.card := by
  classical
  let S (k : κ) := T (zmodDigits (p i₀) (E i₀) (a k))
  let I := {k // active p E i₀ T V (e k) (a k)}
  let n (k : I) := ∏ i, p i ^ eraseExponent i₀ (S k.val).val (e k.val) i
  let E' := Function.update E i₀ (E i₀-1)
  let N := ∏ i, p i ^ E' i
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,_,hcover⟩ := simultaneous_stopping_restriction p E i₀ T hT
    (fun i => (hp i).1.pos) hcp e he a hc
  have hE' (i : ι) : E' i ≤ E i := by
    by_cases hi : i=i₀
    · subst i; simp [E']
    · simp [E',hi]
  have hnew (k : I) (i : ι) : eraseExponent i₀ (S k.val).val (e k.val) i ≤ E' i := by
    by_cases hi : i=i₀
    · subst i
      simp only [eraseExponent_self,E',Function.update_self]
      unfold eraseLevel
      have hh := he k.val i₀
      have ht := (S k.val).isLt
      split_ifs <;> omega
    · simpa only [eraseExponent_of_ne _ _ _ hi,E',Function.update_of_ne hi] using he k.val i
  have hN : 0 < N := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hodd : Odd N := Finset.prod_induction (fun i => p i ^ E' i) Odd
    (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hp i).2.pow)
  have hlt : N < ∏ i, p i ^ E i := by
    apply Finset.prod_lt_prod (fun i _ => pow_pos (hp i).1.pos _)
      (fun i _ => Nat.pow_le_pow_right (hp i).1.pos (hE' i))
    refine ⟨i₀,Finset.mem_univ _,?_⟩
    simp only [E',Function.update_self]
    apply Nat.pow_lt_pow_right (hp i₀).1.one_lt
    have ht := (T (fun _ => 0)).isLt
    omega
  have hn (k : I) : 0 < n k := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hd (k : I) : n k ∣ N := Finset.prod_dvd_prod_of_dvd _ _
    (fun i _ => pow_dvd_pow (p i) (hnew k i))
  have hcov : ∀ x : ℤ, ∃ k : I, (n k : ℤ) ∣ x-b k.val := by
    intro x
    obtain ⟨k,hk,hdiv⟩ := hcover V hV x
    exact ⟨⟨k,hk⟩,hdiv⟩
  by_contra! hHall
  apply hmin N hlt
  exact cover_of_hall n (fun k : I => b k.val) hn N K hN hodd hd
    ((Fintype.card_subtype_le _).trans hcard) hcov hHall

#print axioms minimal_period_hall_deficiency
end Erdos7StoppingHallObstruction
