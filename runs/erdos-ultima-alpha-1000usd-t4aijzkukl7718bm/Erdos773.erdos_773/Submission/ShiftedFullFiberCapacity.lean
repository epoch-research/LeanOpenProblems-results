import Submission.ShiftedFiberOverlap
import Submission.PrimePowerFullFiberBound

/-!
Capacity of square-Sidon unions of full, arbitrarily shifted residue fibers.
These results do not apply to arbitrary partial fibers.
-/
namespace Erdos773.ShiftedFullFiberCapacity

open Finset ShiftedFiberOverlap MatchedResidueLifting

set_option maxHeartbeats 2000000

def roots (q H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ) : Finset ℕ :=
  (R ×ˢ range (H + 1)).image (fun z => q * (starts z.1 + z.2) + z.1)

lemma square_mem {q H r i : ℕ} {R : Finset ℕ} {starts : ℕ → ℕ}
    (hr : r ∈ R) (hi : starts r ≤ i) (hiH : i ≤ starts r + H) :
    (q * i + r) ^ 2 ∈ (roots q H R starts).image (fun n => n ^ 2) := by
  apply Finset.mem_image.mpr
  refine ⟨q * i + r, Finset.mem_image.mpr ⟨(r, i - starts r), ?_, ?_⟩, rfl⟩
  · exact Finset.mem_product.mpr ⟨hr, Finset.mem_range.mpr (by omega)⟩
  · dsimp only
    congr 2
    omega

lemma roots_card (q H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hq : 0 < q) (hR : ∀ r ∈ R, r < q) :
    (roots q H R starts).card = R.card * (H + 1) := by
  rw [roots, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range]
  rintro ⟨r, i⟩ hri ⟨s, j⟩ hsj he
  dsimp only at he
  have hr := (Finset.mem_product.mp hri).1
  have hs := (Finset.mem_product.mp hsj).1
  have hm := congrArg (fun n : ℕ => n % q) he
  have hrs : r = s := by
    simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_eq_of_lt (hR r hr), Nat.mod_eq_of_lt (hR s hs)] using hm
  subst s
  have hh := Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel he)
  exact Prod.ext rfl (by omega)

/-- Sidonness makes the two-coordinate key injective, including within one label. -/
lemma key_injective (q H L : ℕ) (R U : Finset ℕ) (starts : ℕ → ℕ)
    (hq : 0 < q) (hL : 0 < L) (hHL : 10 * L ≤ H)
    (hR : ∀ r ∈ R, r < q) (hU : U ⊆ Finset.Icc L (2 * L))
    (hgap : ∀ u ∈ U, q.Coprime u)
    (hS : IsSidon (((roots q H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    Set.InjOn (key q L starts) ((R ×ˢ U : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨r, u⟩ hru ⟨s, v⟩ hsv he
  obtain ⟨hr, hu⟩ := Finset.mem_product.mp hru
  obtain ⟨hs, hv⟩ := Finset.mem_product.mp hsv
  dsimp only at hr hu hs hv
  obtain ⟨a, c, ha, haH, hc, hcH, hcol⟩ := key_collision hq hL
    (hU hu) (hU hv) (hgap v hv) (hR r hr) (hR s hs) he
  have hu0 : 0 < u := hL.trans_le (Finset.mem_Icc.mp (hU hu)).1
  have hv0 : 0 < v := hL.trans_le (Finset.mem_Icc.mp (hU hv)).1
  have hmem₁ := square_mem (q := q) hr ha (show a ≤ starts r + H by omega)
  have hmem₂ := square_mem (q := q) hr (show starts r ≤ a + 2 * u by omega)
    (show a + 2 * u ≤ starts r + H by omega)
  have hmem₃ := square_mem (q := q) hs hc (show c ≤ starts s + H by omega)
  have hmem₄ := square_mem (q := q) hs (show starts s ≤ c + 2 * v by omega)
    (show c + 2 * v ≤ starts s + H by omega)
  have hlt₁ : (q * a + r) ^ 2 < (q * (a + 2 * u) + r) ^ 2 := by
    apply Nat.pow_lt_pow_left _ (by decide : 2 ≠ 0)
    nlinarith
  have hlt₂ : (q * c + s) ^ 2 < (q * (c + 2 * v) + s) ^ 2 := by
    apply Nat.pow_lt_pow_left _ (by decide : 2 ≠ 0)
    nlinarith
  obtain ⟨hlo, hhi⟩ := PartialResidueFibers.endpoints_unique hS
    hmem₁ hmem₂ hmem₃ hmem₄ hlt₁ hlt₂ (by omega)
  have hlo' := Nat.pow_left_injective (by decide : 2 ≠ 0) hlo
  have hhi' := Nat.pow_left_injective (by decide : 2 ≠ 0) hhi
  have hm := congrArg (fun n : ℕ => n % q) hlo'
  have hrs : r = s := by
    simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_eq_of_lt (hR r hr), Nat.mod_eq_of_lt (hR s hs)] using hm
  subst s
  have hac := Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hlo')
  have hends := Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hhi')
  exact Prod.ext rfl (by omega)

/-- Counting keys retains the location information missing from the prefix hash. -/
theorem gap_capacity (N q H L : ℕ) (R U : Finset ℕ) (starts : ℕ → ℕ)
    (hq : 0 < q) (hL : 0 < L) (hHL : 10 * L ≤ H)
    (hR : ∀ r ∈ R, r < q) (hU : U ⊆ Finset.Icc L (2 * L))
    (hgap : ∀ u ∈ U, q.Coprime u)
    (hheight : ∀ r ∈ R, q * (starts r + H) + r ≤ N)
    (hS : IsSidon (((roots q H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    R.card * U.card ≤ q * (2 * L * N / (q * L ^ 2) + 1) := by
  have hc := Finset.card_le_card_of_injOn (s := R ×ˢ U)
    (t := range q ×ˢ range (2 * L * N / (q * L ^ 2) + 1)) (key q L starts) (by
      rintro ⟨r, u⟩ hru
      obtain ⟨hr, hu⟩ := Finset.mem_product.mp hru
      have hu2 := (Finset.mem_Icc.mp (hU hu)).2
      have hcenter : center q L r (starts r) ≤ N := by
        dsimp only [center]
        have hh := Nat.mul_le_mul_left q (show starts r + 5 * L ≤ starts r + H by omega)
        nlinarith only [hh, hheight r hr]
      have hprod : u * center q L r (starts r) ≤ 2 * L * N :=
        Nat.mul_le_mul hu2 hcenter
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), Finset.mem_range.mpr ?_⟩
      have hd : u * center q L r (starts r) / (q * L ^ 2) ≤
          2 * L * N / (q * L ^ 2) := Nat.div_le_div_right hprod
      change u * center q L r (starts r) / (q * L ^ 2) < _
      omega)
    (key_injective q H L R U starts hq hL hHL hR hU hgap hS)
  simpa only [Finset.card_product, Finset.card_range] using hc

/-- The geometric capacity, with the division and extra terminal bin accounted for. -/
theorem scaled_gap_capacity (N q H L : ℕ) (R U : Finset ℕ) (starts : ℕ → ℕ)
    (hq : 0 < q) (hL : 0 < L) (hHL : 10 * L ≤ H)
    (hR : ∀ r ∈ R, r < q) (hU : U ⊆ Finset.Icc L (2 * L))
    (hgap : ∀ u ∈ U, q.Coprime u)
    (hheight : ∀ r ∈ R, q * (starts r + H) + r ≤ N)
    (hS : IsSidon (((roots q H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    R.card * U.card * L ≤ 2 * N + q * L := by
  have hc := gap_capacity N q H L R U starts hq hL hHL hR hU hgap hheight hS
  let T := 2 * L * N / (q * L ^ 2)
  have hd : q * L ^ 2 * T ≤ 2 * L * N := Nat.mul_div_le _ _
  have hd' : q * L * T ≤ 2 * N := by
    have hh : L * (q * L * T) ≤ L * (2 * N) := by nlinarith only [hd]
    exact Nat.le_of_mul_le_mul_left hh hL
  have hm := Nat.mul_le_mul_right L hc
  change R.card * U.card ≤ q * (T + 1) at hc
  change R.card * U.card * L ≤ q * (T + 1) * L at hm
  nlinarith only [hm, hd']


/-- For prime powers, unit gaps have positive density in every interval.
There is NO upper restriction on H, and no unit condition on the labels. -/
theorem prime_power_capacity (p k N H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hp : p.Prime) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + H) + r ≤ N)
    (hS : IsSidon (((roots (p ^ k) H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    R.card * H ^ 2 ≤ 2400 * N := by
  by_cases hne : R.Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hq : 0 < p ^ k := Nat.pow_pos hp.pos
    have hqH : p ^ k * H ≤ N := by
      calc
        _ ≤ p ^ k * (starts r + H) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ ≤ p ^ k * (starts r + H) + r := Nat.le_add_right _ _
        _ ≤ N := hheight r hr
    have hRc := PrimePowerFullFiberBound.labels_card (p ^ k) R hR
    by_cases hsmall : H < 10
    · have hRH : R.card * H ≤ p ^ k * H := Nat.mul_le_mul_right H hRc
      have hh := Nat.mul_le_mul_right H (hRH.trans hqH)
      have hNH := Nat.mul_le_mul_left N (show H ≤ 10 by omega)
      nlinarith only [hh, hNH]
    · let L := H / 10
      have hL : 0 < L := by dsimp only [L]; omega
      have hHL : 10 * L ≤ H := Nat.mul_div_le H 10
      have hHLarge : H ≤ 20 * L := by dsimp only [L]; omega
      obtain ⟨U, hU, hgap, hcard⟩ := PrimePowerFullFiberBound.unit_gaps p k L hp
      have hc := scaled_gap_capacity N (p ^ k) H L R U starts hq hL hHL hR
        hU hgap hheight hS
      have hqL : p ^ k * L ≤ N :=
        (Nat.mul_le_mul_left _ (show L ≤ H by omega)).trans hqH
      have hUL : L ≤ 2 * U.card := by rw [hcard]; omega
      have hmul := Nat.mul_le_mul_left (R.card * L) hUL
      have hcap : R.card * L ^ 2 ≤ 6 * N := by nlinarith only [hmul, hc, hqL]
      have hsquare := Nat.mul_le_mul_left R.card (Nat.pow_le_pow_left hHLarge 2)
      nlinarith only [hsquare, hcap]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- A two-thirds ceiling for whole shifted-fiber unions.  The declared height
must be at least the modulus. This qualification matters for zero-length fibers. -/
theorem prime_power_card_bound (p k N H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + H) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots (p ^ k) H R starts).card ^ 3 ≤ 20000 * N ^ 2 := by
  have hq : 0 < p ^ k := Nat.pow_pos hp.pos
  rw [roots_card _ _ _ _ hq hR]
  by_cases hne : R.Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hqH : p ^ k * (H + 1) ≤ 2 * N := by
      nlinarith only [hheight r hr, hqN]
    have hcap := prime_power_capacity p k N H R starts hp hR hheight hS
    have hRc := (PrimePowerFullFiberBound.labels_card (p ^ k) R hR).trans hqN
    have hMcard := pairMatching_card (p ^ k) R hq hM
    have hsq : (H + 1) ^ 2 ≤ 2 * H ^ 2 + 2 := by
      have hh := sq_nonneg ((H : ℤ) - 1)
      have hh' : ((H : ℤ) + 1) ^ 2 ≤ 2 * (H : ℤ) ^ 2 + 2 := by nlinarith only [hh]
      exact_mod_cast hh'
    have hmass : R.card * (H + 1) ^ 2 ≤ 4802 * N := by
      have hh := Nat.mul_le_mul_left R.card hsq
      nlinarith only [hh, hcap, hRc]
    calc
      _ = R.card ^ 2 * (R.card * (H + 1) ^ 2) * (H + 1) := by ring
      _ ≤ (2 * p ^ k) * (4802 * N) * (H + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hMcard hmass)
      _ = 9604 * N * (p ^ k * (H + 1)) := by ring
      _ ≤ 9604 * N * (2 * N) := Nat.mul_le_mul_left _ hqH
      _ ≤ 20000 * N ^ 2 := by nlinarith only [Nat.zero_le (N ^ 2)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- If the fibers have positive length, the modulus-height qualification follows
automatically from containment (or the union is empty). -/
theorem positive_length_card_bound (p k N H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hp : p.Prime) (hH : 0 < H) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + H) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    (roots (p ^ k) H R starts).card ^ 3 ≤ 20000 * N ^ 2 := by
  by_cases hne : R.Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hqN : p ^ k ≤ N := by
      have hh := Nat.mul_le_mul_left (p ^ k) (show 1 ≤ starts r + H by omega)
      nlinarith only [hh, hheight r hr]
    exact prime_power_card_bound p k N H R starts hp hqN hR hheight hM hS
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp [roots]

theorem prime_power_real_bound (p k N H : ℕ) (R : Finset ℕ) (starts : ℕ → ℕ)
    (hp : p.Prime) (hqN : p ^ k ≤ N) (hR : ∀ r ∈ R, r < p ^ k)
    (hheight : ∀ r ∈ R, p ^ k * (starts r + H) + r ≤ N)
    (hM : PairMatching (p ^ k) R)
    (hS : IsSidon (((roots (p ^ k) H R starts).image (fun n => n ^ 2)) : Set ℕ)) :
    ((roots (p ^ k) H R starts).card : ℝ) ≤ 28 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hc : ((roots (p ^ k) H R starts).card : ℝ) ^ 3 ≤ 20000 * (N : ℝ) ^ 2 := by
    exact_mod_cast prime_power_card_bound p k N H R starts hp hqN hR hheight hM hS
  have hpow : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ 20000 * (N : ℝ) ^ 2 := hc
    _ ≤ 21952 * (N : ℝ) ^ 2 := by nlinarith only [sq_nonneg (N : ℝ)]
    _ = (28 * (N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by rw [mul_pow, hpow]; norm_num

#print axioms roots_card
#print axioms prime_power_capacity
#print axioms prime_power_card_bound
#print axioms positive_length_card_bound
#print axioms prime_power_real_bound

#print axioms key_injective
#print axioms gap_capacity
#print axioms scaled_gap_capacity

end Erdos773.ShiftedFullFiberCapacity
