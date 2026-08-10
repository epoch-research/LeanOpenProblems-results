import FormalConjectures.Util.ProblemImports
import Submission.TryAZero
import Submission.TryCentral

open Nat Finset Matrix

def cZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)

lemma cZ_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hpodd : p ≠ 2) (hr : r < p) :
    cZ p (p + r) = 0 := by
  classical
  have hp_odd_nat : Odd p := hp.odd_of_ne_two hpodd
  have hnegp : (-1 : ZMod p) ^ p = -1 := by
    rcases hp_odd_nat with ⟨m, hm⟩
    rw [hm]
    simp [pow_succ, pow_mul]
  let T : ℕ → ℕ → ZMod p := fun n k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)
  unfold cZ
  rw [show p + r + 1 = p + (r + 1) by omega]
  rw [Finset.sum_range_add (fun k => T (p+r) k) p (r+1)]
  let f : ℕ → ZMod p := fun k =>
    ((-1 : ZMod p) ^ k) * ((choose r k : ZMod p) ^ 2) * (choose (2*k) k : ZMod p) * (choose (2*(p+(r-k))) (p+(r-k)) : ZMod p)
  have hlower : (∑ x ∈ range p, T (p+r) x) = ∑ x ∈ range p, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p := by simpa using hx
    have hch := choose_p_add_cast_zmod p r x hp hr (by omega)
    by_cases hxr : x ≤ r
    · have hsub : p + r - x = p + (r - x) := by omega
      simp [T, f, hxlt, hch, hsub]
    · have hz : Nat.choose r x = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hxr)
      simp [T, f, hxlt, hch, hz]
  have hupper : (∑ x ∈ range (r + 1), T (p+r) (p+x)) = - (∑ x ∈ range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ r := by simpa [Finset.mem_range] using hx
    have hch := choose_p_add_cast_zmod p r (p+x) hp hr (by omega)
    have hnlt : ¬ p + x < p := by omega
    have hsub1 : p + x - p = x := by omega
    have hsub2 : p + r - (p + x) = r - x := by omega
    have hcentral := central_pair_eq_zmod p x (r-x) hp (by omega) (by omega)
    simp [T, f, hch, hnlt, hsub1, hsub2, pow_add, hnegp]
    calc
      (-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2 * ↑((2 * (p + x)).choose (p + x)) * ↑((2 * (r - x)).choose (r - x))
          = ((-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2) * (↑((2 * (p + x)).choose (p + x)) * ↑((2 * (r - x)).choose (r - x))) := by ring
      _ = ((-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2) * (↑((2 * x).choose x) * ↑((2 * (p + (r - x))).choose (p + (r - x)))) := by rw [← hcentral]
      _ = (-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2 * ↑((2 * x).choose x) * ↑((2 * (p + (r - x))).choose (p + (r - x))) := by ring
  rw [hlower, hupper]
  have htail : (∑ x ∈ range p, f x) = ∑ x ∈ range (r+1), f x := by
    symm
    rw [← Finset.sum_range_add_sum_Ico (f := f) (m := r+1) (n := p) (by omega)]
    suffices (∑ k ∈ Ico (r + 1) p, f k) = 0 by simp [this]
    apply Finset.sum_eq_zero
    intro x hx
    have hxr : r < x := by
      have hx' : r + 1 ≤ x ∧ x < p := by simpa [Finset.mem_Ico] using hx
      omega
    simp [f, Nat.choose_eq_zero_of_lt hxr]
  rw [htail]
  abel
