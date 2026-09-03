import FormalConjecturesUtil

/-!
Square-sum collision chains in every residue class.  The resulting upper
bound concerns FULL arithmetic progressions, not arbitrary subsets of the
squares and not the sparse translated intersections in Erdős 773.
-/
namespace Erdos773.ShiftedProgressionCollision

open Finset

set_option maxHeartbeats 1000000

/-- The first index in a collision; the last is `start q r (t+1)`. -/
def start (q r t : ℕ) : ℕ :=
  2 * q * t ^ 2 + (6 * q + 2 * r + 1) * t + 3 * q + 2 * r + 2

def middle₁ (q r t : ℕ) : ℕ := start q r t + 2 * (q * t) + 4 * q + 1

def middle₂ (q r t : ℕ) : ℕ := start q r t + 2 * (q * t) + 6 * q + 2 * r

lemma start_succ (q r t : ℕ) :
    start q r (t + 1) = start q r t + 4 * (q * t) + 8 * q + 2 * r + 1 := by
  simp only [start]
  ring

lemma start_add_two (q r t : ℕ) :
    start q r (t + 2) = start q r t + 8 * (q * t) + 20 * q + 4 * r + 2 := by
  simp only [start]
  ring

lemma ordered (q r t : ℕ) (hq : 0 < q) :
    start q r t < middle₁ q r t ∧ middle₁ q r t < middle₂ q r t ∧
      middle₂ q r t < start q r (t + 1) := by
  rw [start_succ]
  simp only [middle₁, middle₂]
  omega

/-- An exact identity for every modulus and residue; no primality or unit condition. -/
theorem collision (q r t : ℕ) :
    (q * start q r t + r) ^ 2 + (q * start q r (t + 1) + r) ^ 2 =
      (q * middle₁ q r t + r) ^ 2 + (q * middle₂ q r t + r) ^ 2 := by
  simp only [start, middle₁, middle₂]
  ring

lemma square_affine_injective (q r : ℕ) (hq : 0 < q) :
    Function.Injective (fun n : ℕ => (q * n + r) ^ 2) := by
  intro a b hab
  have h := Nat.pow_left_injective (by decide : 2 ≠ 0) hab
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel h)

/-- A full Sidon index interval cannot contain two consecutive chain endpoints. -/
lemma endpoint_excluded (q r s H t : ℕ) (hq : 0 < q)
    (hs : s ≤ start q r t)
    (hSidon : IsSidon (((Finset.Icc s (s + H)).image
      (fun n => (q * n + r) ^ 2)) : Set ℕ)) :
    s + H < start q r (t + 1) := by
  by_contra! hend
  obtain ⟨hab, hbc, hcd⟩ := ordered q r t hq
  have hmem {n : ℕ} (hlo : start q r t ≤ n) (hhi : n ≤ start q r (t + 1)) :
      (q * n + r) ^ 2 ∈ (((Finset.Icc s (s + H)).image
        (fun n => (q * n + r) ^ 2)) : Set ℕ) := by
    change (q * n + r) ^ 2 ∈ (Finset.Icc s (s + H)).image (fun n : ℕ => (q * n + r) ^ 2)
    exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hs.trans hlo, hhi.trans hend⟩, rfl⟩
  have h := hSidon ((q * start q r t + r) ^ 2)
    (hmem le_rfl (by omega)) ((q * middle₁ q r t + r) ^ 2)
    (hmem hab.le (by omega)) ((q * start q r (t + 1) + r) ^ 2)
    (hmem (by omega) le_rfl) ((q * middle₂ q r t + r) ^ 2)
    (hmem (by omega) hcd.le) (collision q r t)
  rcases h with h | h
  · exact (ne_of_lt hab) (square_affine_injective q r hq h.1)
  · exact (ne_of_lt (hab.trans hbc)) (square_affine_injective q r hq h.1)

lemma index_le_start (q r t : ℕ) : t ≤ start q r t := by
  have h := Nat.le_mul_of_pos_left t (by omega : 0 < 6 * q + 2 * r + 1)
  dsimp only [start]
  omega

lemma start_one_bound {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    start q r 1 ≤ 18 * q := by
  simp only [start, one_pow, mul_one]
  omega

lemma square_parameter_bound {q r t N : ℕ}
    (h : q * start q r t + r ≤ N) : 2 * (q * t) ^ 2 ≤ N := by
  have ht : 2 * q * t ^ 2 ≤ start q r t := by
    dsimp only [start]
    omega
  have hh := Nat.mul_le_mul_left q ht
  nlinarith only [h, hh]

/-- Full shifted progressions have a uniform square-root length ceiling in the
actual root height.  This does not apply to partial index sets. -/
theorem full_shifted_index_bound (N q r s H : ℕ) (hq : 0 < q) (hr : r < q)
    (hN : q * (s + H) + r ≤ N)
    (hSidon : IsSidon (((Finset.Icc s (s + H)).image
      (fun n => (q * n + r) ^ 2)) : Set ℕ)) :
    H ^ 2 ≤ 1600 * N := by
  have hqH : q * H ≤ N := by nlinarith only [hN]
  by_cases hHq : H ≤ q
  · have hsq := Nat.mul_le_mul_right H hHq
    nlinarith only [hsq, hqH]
  have hqN : q ^ 2 ≤ N := by
    have hsq := Nat.mul_le_mul_left q (show q ≤ H by omega)
    nlinarith only [hsq, hqH]
  have hex : ∃ t, s ≤ start q r t := ⟨s, index_le_start q r s⟩
  let t := Nat.find hex
  have hst : s ≤ start q r t := Nat.find_spec hex
  have hend := endpoint_excluded q r s H t hq hst hSidon
  by_cases ht : t = 0
  · rw [ht, zero_add] at hend
    have hb := start_one_bound hq hr
    have hH : H ≤ 18 * q := by omega
    have hsquare := Nat.pow_le_pow_left hH 2
    nlinarith only [hsquare, hqN]
  · let u := t - 1
    have htu : t = u + 1 := by dsimp only [u]; omega
    have hu : start q r u < s := by
      have hmin := Nat.find_min hex (show u < Nat.find hex by change u < t; omega)
      omega
    have hprev : q * start q r u + r ≤ N := by
      have hm := Nat.mul_le_mul_left q hu.le
      nlinarith only [hm, hN]
    have hparam := square_parameter_bound hprev
    have hgap : H ≤ 8 * (q * u) + 26 * q := by
      rw [htu, show u + 1 + 1 = u + 2 by omega, start_add_two] at hend
      omega
    have hsquare := Nat.pow_le_pow_left hgap 2
    have hcauchy : (8 * (q * u) + 26 * q) ^ 2 ≤
        128 * (q * u) ^ 2 + 1352 * q ^ 2 := by
      have h := sq_nonneg ((8 * (q * u) : ℤ) - 26 * q)
      have hh : ((8 * (q * u) + 26 * q : ℕ) : ℤ) ^ 2 ≤
          128 * ((q * u : ℕ) : ℤ) ^ 2 + 1352 * (q : ℤ) ^ 2 := by
        push_cast at h ⊢
        nlinarith only [h]
      exact_mod_cast hh
    nlinarith only [hsquare, hcauchy, hparam, hqN]


lemma translated_image (q r s H : ℕ) :
    ((Finset.Icc s (s + H)).image (fun n => (q * n + r) ^ 2)) =
      ((range (H + 1)).image (fun i => (q * s + r + q * i) ^ 2)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn' := Finset.mem_Icc.mp hn
    refine Finset.mem_image.mpr ⟨n - s, Finset.mem_range.mpr (by omega), ?_⟩
    have he : n = s + (n - s) := by omega
    congr 1
    nlinarith only [congrArg (q * ·) he]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨s + i, Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hi
      omega⟩, ?_⟩
    congr 1
    ring

/-- The start can be arbitrary, not just a canonical residue below the step. -/
theorem progression_sidon_bound (N a q H : ℕ) (hq : 0 < q)
    (hN : a + q * H ≤ N)
    (hSidon : IsSidon (((range (H + 1)).image
      (fun i => (a + q * i) ^ 2)) : Set ℕ)) :
    H ^ 2 ≤ 1600 * N := by
  have ha : q * (a / q) + a % q = a := by
    simpa only [add_comm] using Nat.mod_add_div a q
  apply full_shifted_index_bound N q (a % q) (a / q) H hq (Nat.mod_lt a hq)
  · calc
      _ = a + q * H := by rw [mul_add, add_right_comm, ha]
      _ ≤ N := hN
  · simpa only [translated_image, ha] using hSidon

/-- A version in terms of the starting root and the step, with no height parameter. -/
theorem progression_start_bound (a q H : ℕ) (hq : 0 < q)
    (hSidon : IsSidon (((range (H + 1)).image
      (fun i => (a + q * i) ^ 2)) : Set ℕ)) :
    H ^ 2 ≤ 3200 * a + 2560000 * q ^ 2 := by
  have h := progression_sidon_bound (a + q * H) a q H hq le_rfl hSidon
  have hh : (H : ℤ) ^ 2 ≤ 1600 * ((a : ℤ) + q * H) := by exact_mod_cast h
  have hs := sq_nonneg ((H : ℤ) - 1600 * q)
  have hb : (H : ℤ) ^ 2 ≤ 3200 * a + 2560000 * (q : ℤ) ^ 2 := by
    nlinarith only [hh, hs]
  exact_mod_cast hb

/-- The number of square values in the whole progression has the same bound. -/
theorem progression_card_bound (N a q H : ℕ) (hq : 0 < q)
    (hN : a + q * H ≤ N)
    (hSidon : IsSidon (((range (H + 1)).image
      (fun i => (a + q * i) ^ 2)) : Set ℕ)) :
    (((range (H + 1)).image (fun i => (a + q * i) ^ 2)).card) ^ 2 ≤ 3200 * N + 2 := by
  have hinj : Function.Injective (fun i => (a + q * i) ^ 2) := by
    simpa only [add_comm a] using square_affine_injective q a hq
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have h := progression_sidon_bound N a q H hq hN hSidon
  have hh : (H : ℤ) ^ 2 ≤ 1600 * N := by exact_mod_cast h
  have hs := sq_nonneg ((H : ℤ) - 1)
  have hb : ((H : ℤ) + 1) ^ 2 ≤ 3200 * N + 2 := by nlinarith only [hh, hs]
  exact_mod_cast hb

#print axioms progression_sidon_bound
#print axioms progression_start_bound
#print axioms progression_card_bound

#print axioms collision
#print axioms endpoint_excluded
#print axioms full_shifted_index_bound

end Erdos773.ShiftedProgressionCollision
