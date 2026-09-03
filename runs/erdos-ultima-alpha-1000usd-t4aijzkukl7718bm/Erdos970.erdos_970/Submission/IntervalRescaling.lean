import Submission.RoundedSieve

/-! A residue class inside an interval is a consecutive progression. Restricting
other coprime residue conditions to it gives another interval sieve problem. -/
namespace Erdos970.IntervalRescaling
open BlockSieve.SievePolynomial

/-- The first index of a progression lying outside the interval. -/
noncomputable def progressionLength (m p a : ℕ) (hp : 0 < p) : ℕ :=
  Nat.find (show ∃ c, m ≤ a + p * c from ⟨m, by nlinarith⟩)

theorem lt_progressionLength_iff (m p a : ℕ) (hp : 0 < p) (j : ℕ) :
    j < progressionLength m p a hp ↔ a + p * j < m := by
  unfold progressionLength
  constructor
  · intro hj
    exact Nat.lt_of_not_ge (Nat.find_min (show ∃ c, m ≤ a + p * c from
      ⟨m, by nlinarith⟩) hj)
  · intro hj
    have hc := Nat.find_spec (show ∃ c, m ≤ a + p * c from ⟨m, by nlinarith⟩)
    by_contra h
    have hmul := Nat.mul_le_mul_left p (Nat.le_of_not_gt h)
    omega

theorem residueClass_eq_image (m p r : ℕ) (hp : 0 < p) :
    (Finset.range m).filter (fun x => x ≡ r [MOD p]) =
      (Finset.range (progressionLength m p (r % p) hp)).image (fun j => r % p + p * j) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hxm, hxr⟩
    have hxmod : x % p = r % p := hxr
    have hx : r % p + p * (x / p) = x := by
      simpa only [hxmod] using Nat.mod_add_div x p
    exact ⟨x / p, (lt_progressionLength_iff m p (r % p) hp _).mpr (by omega), hx⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(lt_progressionLength_iff m p (r % p) hp j).mp hj, ?_⟩
    simp [Nat.ModEq]

theorem progressionLength_eq_card (m p r : ℕ) (hp : 0 < p) :
    progressionLength m p (r % p) hp =
      ((Finset.range m).filter (fun x => x ≡ r [MOD p])).card := by
  rw [residueClass_eq_image m p r hp, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have : p * i = p * j := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_left hp this

theorem progressionLength_bounds (m p r : ℕ) (hp : 0 < p) :
    m / p ≤ progressionLength m p (r % p) hp ∧
      progressionLength m p (r % p) hp ≤ ceilQuotient m p := by
  rw [progressionLength_eq_card]
  exact residue_count_bounds m p r hp

/-- Coprimality allows any affine pullback of a residue condition. -/
theorem exists_affine_residue (a p q r : ℕ) (hq : 0 < q) (hpq : p.Coprime q) :
    ∃ s : ℕ, ∀ j : ℕ, a + p * j ≡ r [MOD q] ↔ j ≡ s [MOD q] := by
  let b := r + (q - 1) * a
  let c := Nat.chineseRemainder hpq 0 b
  have hpc : p ∣ c.val := Nat.modEq_zero_iff_dvd.mp c.property.1
  have hmul : p * (c.val / p) = c.val := Nat.mul_div_cancel' hpc
  have hbase : a + p * (c.val / p) ≡ r [MOD q] := by
    rw [hmul]
    have h := c.property.2.add_left a
    have he : a + b = r + q * a := by dsimp [b]; nlinarith [Nat.sub_add_cancel hq]
    rw [he] at h
    simpa [Nat.ModEq] using h
  refine ⟨c.val / p, fun j => ?_⟩
  constructor
  · intro h
    exact Nat.ModEq.cancel_left_of_coprime hpq.symm
      (Nat.ModEq.add_left_cancel' a (h.trans hbase.symm))
  · intro h
    exact ((h.mul_left p).add_left a).trans hbase

/-- The number surviving the first `k` indexed residue conditions. -/
def count (p r : ℕ → ℕ) (k m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun x => ∀ j < k, ¬x ≡ r j [MOD p j])).card

/-- The number whose first forbidden residue has index `i`. -/
def firstHitCount (p r : ℕ → ℕ) (i m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun x => x ≡ r i [MOD p i] ∧
    ∀ j < i, ¬x ≡ r j [MOD p j])).card

theorem count_mono_length (p r : ℕ → ℕ) (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    count p r k m ≤ count p r k n := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    ((Finset.mem_range.mp (Finset.mem_filter.mp hx).1).trans_le hmn),
    (Finset.mem_filter.mp hx).2⟩

/-- An exact first-hit intersection is a sieve of the same earlier moduli on a
new consecutive interval; its length is between the floor and ceiling quotients. -/
theorem firstHitCount_rescale (p r : ℕ → ℕ) (i m : ℕ)
    (hp : 0 < p i) (hq : ∀ j < i, 0 < p j)
    (hcop : ∀ j < i, (p i).Coprime (p j)) :
    ∃ c : ℕ, ∃ s : ℕ → ℕ, m / p i ≤ c ∧ c ≤ ceilQuotient m (p i) ∧
      firstHitCount p r i m = count p s i c := by
  classical
  let a := r i % p i
  let c := progressionLength m (p i) a hp
  have hex (j : Fin i) : ∃ s : ℕ,
      ∀ t : ℕ, a + p i * t ≡ r j [MOD p j] ↔ t ≡ s [MOD p j] :=
    exists_affine_residue a (p i) (p j) (r j) (hq j j.isLt) (hcop j j.isLt)
  choose s₀ hs₀ using hex
  let s (j : ℕ) := if h : j < i then s₀ ⟨j, h⟩ else 0
  have hs (j : ℕ) (hj : j < i) (t : ℕ) :
      a + p i * t ≡ r j [MOD p j] ↔ t ≡ s j [MOD p j] := by
    simpa only [s, dif_pos hj] using hs₀ ⟨j, hj⟩ t
  obtain ⟨hcl, hcu⟩ := progressionLength_bounds m (p i) (r i) hp
  refine ⟨c, s, hcl, hcu, ?_⟩
  have he : (Finset.range m).filter (fun x => x ≡ r i [MOD p i] ∧
      ∀ j < i, ¬x ≡ r j [MOD p j]) =
      ((Finset.range c).filter (fun t => ∀ j < i, ¬t ≡ s j [MOD p j])).image
        (fun t => a + p i * t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hxm, hxi, hxj⟩
      have hxmem : x ∈ (Finset.range m).filter (fun x => x ≡ r i [MOD p i]) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxm, hxi⟩
      rw [residueClass_eq_image m (p i) (r i) hp] at hxmem
      obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hxmem
      refine ⟨t, ⟨Finset.mem_range.mp ht, fun j hj hbad => hxj j hj ?_⟩, htx⟩
      rw [← htx]
      exact (hs j hj t).mpr hbad
    · rintro ⟨t, ⟨ht, hts⟩, rfl⟩
      refine ⟨(lt_progressionLength_iff m (p i) a hp t).mp ht, ?_, ?_⟩
      · simp [a, Nat.ModEq]
      · intro j hj hbad
        exact hts j hj ((hs j hj t).mp hbad)
  unfold firstHitCount count
  rw [he, Finset.card_image_of_injective]
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel hxy)

#print axioms firstHitCount_rescale
end Erdos970.IntervalRescaling
