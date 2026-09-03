import FormalConjecturesUtil

/-! A probabilistic construction for general atomic boxes. The coordinate
alphabets need not come from distinct primes. This is not an odd arithmetic
covering system. -/
namespace Erdos7GenericBoxRandomCover
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 4000000

section RandomChoice
variable {X K : Type*} [Fintype X] [Fintype K]
variable (B : K → Type*) [∀ k, Fintype (B k)]

/-- Pick one value in each alphabet so that every row agrees with at least
one picked value. The hypothesis is the elementary union bound. -/
theorem exists_hit_each_row (f : X → (k : K) → B k)
    (h : Fintype.card X * (∏ k, (Fintype.card (B k) - 1)) <
      ∏ k, Fintype.card (B k)) :
    ∃ b : (k : K) → B k, ∀ x, ∃ k, b k = f x k := by
  classical
  let bad (x : X) : Finset ((k : K) → B k) :=
    Fintype.piFinset (fun k => (univ : Finset (B k)).erase (f x k))
  have hbad (x : X) : (bad x).card = ∏ k, (Fintype.card (B k) - 1) := by
    simp [bad, Fintype.card_piFinset]
  have hcard : (univ.biUnion bad).card < Fintype.card ((k : K) → B k) := by
    calc
      (univ.biUnion bad).card ≤ ∑ x, (bad x).card := card_biUnion_le
      _ = Fintype.card X * (∏ k, (Fintype.card (B k) - 1)) := by simp [hbad]
      _ < ∏ k, Fintype.card (B k) := h
      _ = Fintype.card ((k : K) → B k) := Fintype.card_pi.symm
  obtain ⟨b, hb, hn⟩ := exists_mem_notMem_of_card_lt_card
    (show (univ.biUnion bad).card < (univ : Finset ((k : K) → B k)).card by simpa using hcard)
  refine ⟨b, fun x => ?_⟩
  by_contra! hx
  apply hn
  exact mem_biUnion.mpr ⟨x, mem_univ _, Fintype.mem_piFinset.mpr
    (fun k => mem_erase.mpr ⟨hx k, mem_univ _⟩)⟩

/-- Real-valued version of the same union bound. -/
theorem exists_hit_each_row_of_real (f : X → (k : K) → B k)
    (hB : ∀ k, 0 < Fintype.card (B k))
    (h : (Fintype.card X : ℝ) *
      (∏ k, (1 - 1 / (Fintype.card (B k) : ℝ))) < 1) :
    ∃ b : (k : K) → B k, ∀ x, ∃ k, b k = f x k := by
  apply exists_hit_each_row B f
  have hd : 0 < ∏ k, (Fintype.card (B k) : ℝ) :=
    prod_pos (fun k _ => by exact_mod_cast hB k)
  have hid (k : K) :
      1 - 1 / (Fintype.card (B k) : ℝ) =
        ((Fintype.card (B k) - 1 : ℕ) : ℝ) / Fintype.card (B k) := by
    rw [Nat.cast_sub (hB k), Nat.cast_one]
    have hn : (Fintype.card (B k) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hB k))
    field_simp [hn]
  simp_rw [hid] at h
  rw [prod_div_distrib, ← mul_div_assoc] at h
  have hh := (div_lt_one hd).mp h
  exact_mod_cast hh

/-- The exponential estimate for the probability that a row is missed. -/
theorem exists_hit_each_row_of_exp (f : X → (k : K) → B k)
    (hB : ∀ k, 0 < Fintype.card (B k)) (c : ℝ)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp c)
    (hc : c < ∑ k, 1 / (Fintype.card (B k) : ℝ)) :
    ∃ b : (k : K) → B k, ∀ x, ∃ k, b k = f x k := by
  apply exists_hit_each_row_of_real B f hB
  have hf (k : K) : 0 ≤ 1 - 1 / (Fintype.card (B k) : ℝ) := by
    have hh : (1 : ℝ) ≤ Fintype.card (B k) := by exact_mod_cast hB k
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hh |>.trans_eq (by norm_num))
  have he : (∏ k, (1 - 1 / (Fintype.card (B k) : ℝ))) ≤
      Real.exp (-(∑ k, 1 / (Fintype.card (B k) : ℝ))) := by
    calc
      _ ≤ ∏ k, Real.exp (-(1 / (Fintype.card (B k) : ℝ))) := by
        apply prod_le_prod (fun k _ => hf k)
        intro k _
        simpa only [neg_add_eq_sub, add_comm] using
          Real.add_one_le_exp (-(1 / (Fintype.card (B k) : ℝ)))
      _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]
  calc
    _ ≤ Real.exp c * Real.exp (-(∑ k, 1 / (Fintype.card (B k) : ℝ))) :=
      mul_le_mul hX he (prod_nonneg (fun k _ => hf k)) (Real.exp_pos _).le
    _ = Real.exp (c - ∑ k, 1 / (Fintype.card (B k) : ℝ)) := by rw [← Real.exp_add]; congr 1
    _ < 1 := by rw [Real.exp_lt_one_iff]; linarith
end RandomChoice

/-- An elementary probabilistic existence criterion for one atomic box per
support of a fixed size. All alphabets here have the same size. -/
theorem exists_fixed_size_box_cover (n q k : ℕ) (hq : 0 < q) (c : ℝ)
    (hX : (q : ℝ)^n ≤ Real.exp c)
    (hvolume : c < (n.choose k : ℝ) / (q : ℝ)^k) :
    ∃ a : {s : Finset (Fin n) // s.card = k} → Fin n → Fin q,
      ∀ x : Fin n → Fin q, ∃ s, ∀ i ∈ s.val, x i = a s i := by
  classical
  let K := {s : Finset (Fin n) // s.card = k}
  let B (s : K) := s.val → Fin q
  have hc (s : K) : Fintype.card (B s) = q^k := by
    simp only [B, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, s.property]
  have hb : ∀ s, 0 < Fintype.card (B s) := by
    intro s
    rw [hc]
    exact pow_pos hq _
  have hx : (Fintype.card (Fin n → Fin q) : ℝ) ≤ Real.exp c := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hX
  have hv : c < ∑ s : K, 1 / (Fintype.card (B s) : ℝ) := by
    simp only [hc, Nat.cast_pow, sum_const, card_univ, nsmul_eq_mul]
    have hk : Fintype.card K = n.choose k := by simp [K]
    rw [hk, mul_one_div]
    exact hvolume
  obtain ⟨b, hb⟩ := exists_hit_each_row_of_exp B
    (fun (x : Fin n → Fin q) (s : K) (i : s.val) => x i) hb c hx hv
  let a (s : K) (i : Fin n) : Fin q :=
    if hi : i ∈ s.val then b s ⟨i, hi⟩ else ⟨0, hq⟩
  refine ⟨a, fun x => ?_⟩
  obtain ⟨s, hs⟩ := hb x
  refine ⟨s, fun i hi => ?_⟩
  simp only [a, dif_pos hi]
  exact (congrFun hs ⟨i, hi⟩).symm

#print axioms exists_hit_each_row
#print axioms exists_hit_each_row_of_exp
#print axioms exists_fixed_size_box_cover
end Erdos7GenericBoxRandomCover
