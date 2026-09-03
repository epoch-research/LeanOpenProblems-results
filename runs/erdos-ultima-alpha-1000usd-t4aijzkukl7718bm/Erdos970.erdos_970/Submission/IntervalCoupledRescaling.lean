import Submission.IntervalRecursiveSieve

/-! Simultaneous, correlated rescaling of all residue classes. All rows are
translates of a single earlier sieve configuration. This file makes no claim
about a uniform quadratic length. -/
namespace Erdos970.IntervalRescaling

/-- An earlier sieve in a translated natural interval. -/
def shiftedCount (p s : ℕ → ℕ) (k a m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun t => ∀ j < k, ¬a + t ≡ s j [MOD p j])).card

/-- The earlier survivors in one residue class of an additional modulus. -/
def rowCount (p r : ℕ → ℕ) (k d m a : ℕ) : ℕ :=
  ((Finset.range m).filter (fun x => x ≡ a [MOD d] ∧
    ∀ j < k, ¬x ≡ r j [MOD p j])).card

/-- A common inverse exists even without pairwise coprimality among the earlier
moduli; only the additional modulus must be coprime to each of them. -/
theorem exists_common_inverse (p : ℕ → ℕ) (k d : ℕ)
    (hp : ∀ j < k, 0 < p j) (hc : ∀ j < k, d.Coprime (p j)) :
    ∃ v : ℕ, ∀ j < k, d * v ≡ 1 [MOD p j] := by
  let N := ∏ j ∈ Finset.range k, p j
  have hN : 0 < N := Finset.prod_pos (fun j hj => hp j (Finset.mem_range.mp hj))
  have hdN : d.Coprime N := Nat.coprime_prod_right_iff.mpr
    (fun j hj => hc j (Finset.mem_range.mp hj))
  obtain ⟨v, hv⟩ := exists_affine_residue 0 d N 1 hN hdN
  have hvN : d * v ≡ 1 [MOD N] := by
    simpa only [Nat.zero_add] using (hv v).mpr (Nat.ModEq.refl v)
  refine ⟨v, fun j hj => ?_⟩
  exact hvN.of_dvd (Finset.dvd_prod_of_mem (fun j => p j) (Finset.mem_range.mpr hj))

lemma affine_modEq_iff_common_inverse (d v q r a t : ℕ)
    (hc : d.Coprime q) (hv : d * v ≡ 1 [MOD q]) :
    a + d * t ≡ r [MOD q] ↔ v * a + t ≡ v * r [MOD q] := by
  have ha : d * (v * a + t) ≡ a + d * t [MOD q] := by
    have h := (hv.mul_right a).add_right (d * t)
    simpa only [one_mul, Nat.mul_add, Nat.mul_assoc] using h
  have hr : d * (v * r) ≡ r [MOD q] := by
    simpa only [one_mul, Nat.mul_assoc] using hv.mul_right r
  constructor
  · intro h
    exact Nat.ModEq.cancel_left_of_coprime hc.symm (ha.trans (h.trans hr.symm))
  · intro h
    exact ha.symm.trans ((h.mul_left d).trans hr)

/-- Crucially, the residue vector `fun j => v * r j` is independent of the row
`a`. The only row-dependent parameter is the common translation `v * a`. -/
theorem rowCount_rescale_common (p r : ℕ → ℕ) (k d v m a : ℕ)
    (hd : 0 < d) (ha : a < d)
    (hc : ∀ j < k, d.Coprime (p j))
    (hv : ∀ j < k, d * v ≡ 1 [MOD p j]) :
    rowCount p r k d m a =
      shiftedCount p (fun j => v * r j) k (v * a) (progressionLength m d a hd) := by
  classical
  have he : (Finset.range m).filter (fun x => x ≡ a [MOD d] ∧
        ∀ j < k, ¬x ≡ r j [MOD p j]) =
      ((Finset.range (progressionLength m d a hd)).filter
        (fun t => ∀ j < k, ¬v * a + t ≡ v * r j [MOD p j])).image
          (fun t => a + d * t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hxm, hxa, hxs⟩
      have hmem : x ∈ (Finset.range m).filter (fun x => x ≡ a [MOD d]) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxm, hxa⟩
      rw [residueClass_eq_image m d a hd, Nat.mod_eq_of_lt ha] at hmem
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmem
      refine ⟨t, ⟨Finset.mem_range.mp ht, ?_⟩, rfl⟩
      intro j hj hjt
      exact hxs j hj ((affine_modEq_iff_common_inverse d v (p j) (r j) a t
        (hc j hj) (hv j hj)).mpr hjt)
    · rintro ⟨t, ⟨ht, hts⟩, rfl⟩
      refine ⟨(lt_progressionLength_iff m d a hd t).mp ht, ?_, ?_⟩
      · simp [Nat.ModEq]
      · intro j hj hjt
        exact hts j hj ((affine_modEq_iff_common_inverse d v (p j) (r j) a t
          (hc j hj) (hv j hj)).mp hjt)
  unfold rowCount shiftedCount
  rw [he, Finset.card_image_of_injective]
  intro t u htu
  exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel htu)

/-- A full cover by the old classes and one additional class is equivalent to
vanishing of every other row. -/
theorem count_succ_zero_iff_rows_zero (p r : ℕ → ℕ) (k m : ℕ) (hd : 0 < p k) :
    count p r (k + 1) m = 0 ↔
      ∀ a < p k, a ≠ r k % p k → rowCount p r k (p k) m a = 0 := by
  classical
  constructor
  · intro hz a ha hne
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨hxm, hxa, hxs⟩ := Finset.mem_filter.mp hx
    have hxr : ¬x ≡ r k [MOD p k] := by
      intro hxr
      apply hne
      change x % p k = a % p k at hxa
      change x % p k = r k % p k at hxr
      simpa only [Nat.mod_eq_of_lt ha] using hxa.symm.trans hxr
    have hx' : x ∈ (Finset.range m).filter
        (fun x => ∀ j < k + 1, ¬x ≡ r j [MOD p j]) := by
      refine Finset.mem_filter.mpr ⟨hxm, ?_⟩
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact hxs j hj
      · exact hxr
    have he := Finset.card_eq_zero.mp hz
    rw [he] at hx'
    exact Finset.notMem_empty x hx'
  · intro hz
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨hxm, hxs⟩ := Finset.mem_filter.mp hx
    have hne : x % p k ≠ r k % p k := hxs k (by omega)
    have hrz := hz (x % p k) (Nat.mod_lt x hd) hne
    have hx' : x ∈ (Finset.range m).filter (fun x' =>
        x' ≡ x % p k [MOD p k] ∧ ∀ j < k, ¬x' ≡ r j [MOD p j]) := by
      refine Finset.mem_filter.mpr ⟨hxm, ?_, fun j hj => hxs j (by omega)⟩
      simp [Nat.ModEq]
    have he := Finset.card_eq_zero.mp hrz
    rw [he] at hx'
    exact Finset.notMem_empty x hx'

/-- The full-cover test retains the common configuration across all rescaled
rows. It is stronger data than separate universal bounds for each row. -/
theorem count_succ_zero_iff_coupled_rows_zero (p r : ℕ → ℕ) (k v m : ℕ)
    (hd : 0 < p k) (hc : ∀ j < k, (p k).Coprime (p j))
    (hv : ∀ j < k, p k * v ≡ 1 [MOD p j]) :
    count p r (k + 1) m = 0 ↔
      ∀ a < p k, a ≠ r k % p k →
        shiftedCount p (fun j => v * r j) k (v * a)
          (progressionLength m (p k) a hd) = 0 := by
  rw [count_succ_zero_iff_rows_zero p r k m hd]
  constructor <;> intro h a ha hne
  · rw [← rowCount_rescale_common p r k (p k) v m a hd ha hc hv]
    exact h a ha hne
  · rw [rowCount_rescale_common p r k (p k) v m a hd ha hc hv]
    exact h a ha hne

#print axioms exists_common_inverse
#print axioms rowCount_rescale_common
#print axioms count_succ_zero_iff_coupled_rows_zero
end Erdos970.IntervalRescaling
