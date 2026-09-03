import FormalConjecturesUtil

/-! Soundness of exact finite integer-cut certificates. No witness for the
original missing-digit conjecture is asserted here. -/
namespace Erdos406IntegerCuts
open Finset

variable {M N : ℕ}

def dot (a r : Fin N → ℤ) : ℤ := ∑ j, a j * r j

def Valid (A : Fin M → Fin N → ℤ) (b : Fin M → ℤ) (r : Fin N → ℤ) : Prop :=
  ∀ i, dot (A i) r ≤ b i

lemma combine (A : Fin M → Fin N → ℤ) (b w : Fin M → ℤ) (r : Fin N → ℤ)
    (hw : ∀ i, 0 ≤ w i) (h : Valid A b r) :
    dot (fun j => ∑ i, w i * A i j) r ≤ ∑ i, w i * b i := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    mul_le_mul_of_nonneg_left (h i) (hw i))
  have he : (∑ i, w i * dot (A i) r) = dot (fun j => ∑ i, w i * A i j) r := by
    simp only [dot, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rwa [he] at hh

lemma cut (A : Fin M → Fin N → ℤ) (b w : Fin M → ℤ) (r : Fin N → ℤ)
    (t : Fin M) (s K : ℤ) (hw : ∀ i, 0 ≤ w i) (hs : 0 < s)
    (he : ∀ j, (∑ i, w i * A i j) = s * A t j)
    (hk : (∑ i, w i * b i) < s * (K + 1)) (h : Valid A b r) :
    dot (A t) r ≤ K := by
  have hh := combine A b w r hw h
  have hid : dot (fun j => ∑ i, w i * A i j) r = s * dot (A t) r := by
    simp only [dot, he, Finset.mul_sum, mul_assoc]
  rw [hid] at hh
  by_contra hn
  have ha : K + 1 ≤ dot (A t) r := by omega
  have hb := mul_le_mul_of_nonneg_left ha hs.le
  omega

lemma cut_update (A : Fin M → Fin N → ℤ) (b w : Fin M → ℤ) (r : Fin N → ℤ)
    (t : Fin M) (s K : ℤ) (hw : ∀ i, 0 ≤ w i) (hs : 0 < s)
    (he : ∀ j, (∑ i, w i * A i j) = s * A t j)
    (hk : (∑ i, w i * b i) < s * (K + 1)) (h : Valid A b r) :
    Valid A (Function.update b t K) r := by
  intro i
  by_cases hi : i = t
  · subst i
    simpa using cut A b w r t s K hw hs he hk h
  · simpa [Function.update_of_ne hi] using h i

lemma contradiction (A : Fin M → Fin N → ℤ) (b w : Fin M → ℤ) (r : Fin N → ℤ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ j, (∑ i, w i * A i j) = 0)
    (hk : (∑ i, w i * b i) < 0) (h : Valid A b r) : False := by
  have hh := combine A b w r hw h
  have hz : dot (fun j => ∑ i, w i * A i j) r = 0 := by simp [dot, he]
  rw [hz] at hh
  omega

#print axioms cut_update
#print axioms contradiction
end Erdos406IntegerCuts

namespace Erdos406IntegerCuts
variable {M N L : ℕ}

lemma selected_cut (A : Fin M → Fin N → ℤ) (b : Fin M → ℤ)
    (rows : Fin L → Fin M) (w : Fin L → ℤ) (r : Fin N → ℤ)
    (t : Fin M) (s K : ℤ) (hw : ∀ i, 0 ≤ w i) (hs : 0 < s)
    (he : ∀ j, (∑ i, w i * A (rows i) j) = s * A t j)
    (hk : (∑ i, w i * b (rows i)) < s * (K + 1)) (h : Valid A b r) :
    dot (A t) r ≤ K := by
  have hh := combine (fun i => A (rows i)) (fun i => b (rows i)) w r hw
    (fun i => h (rows i))
  dsimp only at hh
  have hid : dot (fun j => ∑ i, w i * A (rows i) j) r = s * dot (A t) r := by
    simp only [dot, he, Finset.mul_sum, mul_assoc]
  rw [hid] at hh
  by_contra hn
  have ha : K + 1 ≤ dot (A t) r := by omega
  have hb := mul_le_mul_of_nonneg_left ha hs.le
  omega

lemma selected_cut_update (A : Fin M → Fin N → ℤ) (b : Fin M → ℤ)
    (rows : Fin L → Fin M) (w : Fin L → ℤ) (r : Fin N → ℤ)
    (t : Fin M) (s K : ℤ) (hw : ∀ i, 0 ≤ w i) (hs : 0 < s)
    (he : ∀ j, (∑ i, w i * A (rows i) j) = s * A t j)
    (hk : (∑ i, w i * b (rows i)) < s * (K + 1)) (h : Valid A b r) :
    Valid A (Function.update b t K) r := by
  intro i
  by_cases hi : i = t
  · subst i
    simpa using selected_cut A b rows w r t s K hw hs he hk h
  · simpa [Function.update_of_ne hi] using h i

lemma selected_contradiction (A : Fin M → Fin N → ℤ) (b : Fin M → ℤ)
    (rows : Fin L → Fin M) (w : Fin L → ℤ) (r : Fin N → ℤ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ j, (∑ i, w i * A (rows i) j) = 0)
    (hk : (∑ i, w i * b (rows i)) < 0) (h : Valid A b r) : False := by
  have hh := combine (fun i => A (rows i)) (fun i => b (rows i)) w r hw
    (fun i => h (rows i))
  dsimp only at hh
  have hz : dot (fun j => ∑ i, w i * A (rows i) j) r = 0 := by simp [dot, he]
  rw [hz] at hh
  omega

#print axioms selected_cut_update
#print axioms selected_contradiction
end Erdos406IntegerCuts
