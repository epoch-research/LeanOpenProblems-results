import Submission.FullFiberOverlap
import Submission.FullResidueFiberBound

/-!
A two-thirds cardinality ceiling for Sidon unions of full canonical unit
fibers over a prime-power modulus. This is a bound on that restricted family,
not on arbitrary partial fibers or the original square-Sidon maximum.
-/
namespace Erdos773.PrimePowerFullFiberBound
open Finset MatchedResidueLifting
set_option maxHeartbeats 2000000

lemma square_mem {q H r i : ℕ} {R : Finset ℕ} (hr : r∈R) (hi : i≤H) :
    (q*i+r)^2 ∈ (roots q H R).image (fun n => n^2) := by
  apply mem_image.mpr
  refine ⟨q*i+r, ?_, rfl⟩
  exact mem_image.mpr ⟨(r,i), mem_product.mpr
    ⟨hr, mem_Icc.mpr ⟨Nat.zero_le _,hi⟩⟩, rfl⟩

/-- Actual Sidonness forbids a modular match of unit gaps between distinct
full fibers: the match produces all four required endpoints. -/
theorem gap_capacity (q H L : ℕ) (R U : Finset ℕ) (hq : 0<q) (hL : 0<L)
    (hHL : 10*L≤H) (hHq : H≤q)
    (hR : ∀ r∈R, r<q) (hunit : ∀ r∈R, q.Coprime r)
    (hU : U⊆Icc L (2*L)) (hgap : ∀ u∈U, q.Coprime u)
    (hS : IsSidon (((roots q H R).image (fun n => n^2)) : Set ℕ)) :
    R.card*U.card≤q := by
  have hc : (R ×ˢ U).card ≤ (range q).card := by
    apply card_le_card_of_injOn (fun z : ℕ × ℕ => z.1*z.2%q)
    · intro z hz
      exact mem_range.mpr (Nat.mod_lt _ hq)
    · rintro ⟨r,u⟩ hru ⟨s,v⟩ hsv he
      obtain ⟨hr,hu⟩ := mem_product.mp hru
      obtain ⟨hs,hv⟩ := mem_product.mp hsv
      change r*u ≡ s*v [MOD q] at he
      have hu' := mem_Icc.mp (hU hu)
      have hv' := mem_Icc.mp (hU hv)
      by_cases hrs : r=s
      · subst s
        have hh := he.cancel_left_of_coprime (hunit r hr)
        exact Prod.ext rfl (hh.eq_of_lt_of_lt (by omega) (by omega))
      · exfalso
        obtain ⟨a,c,ha,hc,heq⟩ := FullFiberOverlap.small_gap_collision hL
          (hU hu) (hU hv) (hgap v hv) (hR r hr) (hR s hs) he
        have haH := ha.trans hHL
        have hcH := hc.trans hHL
        have hmemA := square_mem (q:=q) hr haH
        have hmemB := square_mem (q:=q) hs (show c≤H by omega)
        have hmemC := square_mem (q:=q) hr (show a≤H by omega)
        have hmemD := square_mem (q:=q) hs hcH
        rcases hS _ hmemA _ hmemC _ hmemB _ hmemD heq with hh | hh
        · have hh' := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh.1
          nlinarith
        · have hh' := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh.1
          have hm := congrArg (fun n : ℕ => n%q) hh'
          have hrs' : r=s := by
            simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
              Nat.mod_eq_of_lt (hR r hr), Nat.mod_eq_of_lt (hR s hs)] using hm
          exact hrs hrs'
  simpa only [card_product, card_range] using hc

/-- At least one element of each consecutive pair is prime to p. -/
def selectedGap (p L i : ℕ) : ℕ :=
  if p ∣ L+2*i then L+2*i+1 else L+2*i

lemma selectedGap_bounds (p L i : ℕ) :
    L+2*i≤selectedGap p L i ∧ selectedGap p L i≤L+2*i+1 := by
  unfold selectedGap
  split_ifs <;> omega

lemma selectedGap_unit (p k L i : ℕ) (hp : p.Prime) :
    (p^k).Coprime (selectedGap p L i) := by
  apply Nat.Coprime.pow_left
  apply hp.coprime_iff_not_dvd.mpr
  unfold selectedGap
  split_ifs with h
  · intro hh
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hh)
  · exact h

/-- A short interval contains a half-sized explicitly chosen set of unit gaps
for every prime-power modulus. -/
theorem unit_gaps (p k L : ℕ) (hp : p.Prime) :
    ∃ U : Finset ℕ, U⊆Icc L (2*L) ∧
      (∀ u∈U, (p^k).Coprime u) ∧ U.card=(L+1)/2 := by
  let U := (range ((L+1)/2)).image (selectedGap p L)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    have hi' := mem_range.mp hi
    have hb := selectedGap_bounds p L i
    apply mem_Icc.mpr
    omega
  · intro u hu
    obtain ⟨i,_,rfl⟩ := mem_image.mp hu
    exact selectedGap_unit p k L i hp
  · rw [card_image_of_injective, card_range]
    intro i j he
    have hi := selectedGap_bounds p L i
    have hj := selectedGap_bounds p L j
    omega

lemma labels_card (q : ℕ) (R : Finset ℕ) (hR : ∀ r∈R, r<q) : R.card≤q := by
  have hh : R⊆range q := fun r hr => mem_range.mpr (hR r hr)
  simpa only [card_range] using card_le_card hh

/-- For full prefixes of length at most the modulus, actual Sidonness gives
an index-capacity bound. No modular pair-matching assumption is needed here. -/
theorem short_capacity (p k H : ℕ) (R : Finset ℕ) (hp : p.Prime)
    (hH : H≤p^k) (hR : ∀ r∈R, r<p^k)
    (hunit : ∀ r∈R, (p^k).Coprime r)
    (hS : IsSidon (((roots (p^k) H R).image (fun n => n^2)) : Set ℕ)) :
    R.card*H≤40*p^k := by
  by_cases hsmall : H<20
  · have hr := labels_card (p^k) R hR
    have hh := Nat.mul_le_mul hr (show H≤40 by omega)
    simpa only [mul_comm] using hh
  · let L := H/10
    obtain ⟨U,hU,hgap,hcard⟩ := unit_gaps p k L hp
    have hL : 0<L := by dsimp [L]; omega
    have hHL : 10*L≤H := Nat.mul_div_le H 10
    have hcap := gap_capacity (p^k) H L R U (Nat.pow_pos hp.pos) hL
      hHL hH hR hunit hU hgap hS
    have hHU : H≤40*U.card := by
      rw [hcard]
      dsimp [L]
      omega
    calc
      R.card*H ≤ R.card*(40*U.card) := Nat.mul_le_mul_left _ hHU
      _ = 40*(R.card*U.card) := by ring
      _ ≤ 40*p^k := Nat.mul_le_mul_left 40 hcap

lemma roots_mono {q H K : ℕ} {R : Finset ℕ} (hHK : H≤K) :
    roots q H R⊆roots q K R := by
  apply image_subset_image
  intro z hz
  obtain ⟨hr,hi⟩ := mem_product.mp hz
  exact mem_product.mpr ⟨hr, mem_Icc.mpr
    ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans hHK⟩⟩

/-- Long prefixes are reduced by truncation, and the explicit within-fiber
collision bounds how far a nonempty full fiber can extend. -/
theorem full_capacity (p k H : ℕ) (R : Finset ℕ) (hp : p.Prime)
    (hR : ∀ r∈R, r<p^k) (hunit : ∀ r∈R, (p^k).Coprime r)
    (hS : IsSidon (((roots (p^k) H R).image (fun n => n^2)) : Set ℕ)) :
    R.card*(H+1)≤600*p^k := by
  have hq : 0<p^k := Nat.pow_pos hp.pos
  by_cases hH : H≤p^k
  · have hc := short_capacity p k H R hp hH hR hunit hS
    have hr := labels_card (p^k) R hR
    nlinarith only [hc,hr,hq]
  · by_cases hne : R.Nonempty
    · have hS' : IsSidon (((roots (p^k) (p^k) R).image (fun n => n^2)) : Set ℕ) :=
        Set.IsSidon.subset hS (image_subset_image (roots_mono (by omega)))
      have hc := short_capacity p k (p^k) R hp le_rfl hR hunit hS'
      have hr : R.card≤40 := Nat.le_of_mul_le_mul_right hc hq
      have hh := FullResidueFiberBound.full_fiber_length_bound (p^k) H R hq hR hne hS
      calc
        R.card*(H+1) ≤ 40*(15*p^k) := Nat.mul_le_mul hr (by omega)
        _ = 600*p^k := by ring
    · have he := not_nonempty_iff_eq_empty.mp hne
      simp [he]

/-- A genuine two-thirds bound for this restricted Sidon construction, with
an arbitrary prime power, canonical unit labels, and equal full-prefix lengths.
It does not apply to arbitrary subsets of squares. -/
theorem full_fiber_card_bound (p k H : ℕ) (R : Finset ℕ) (hp : p.Prime)
    (hR : ∀ r∈R, r<p^k) (hunit : ∀ r∈R, (p^k).Coprime r)
    (hM : PairMatching (p^k) R)
    (hS : IsSidon (((roots (p^k) H R).image (fun n => n^2)) : Set ℕ)) :
    (roots (p^k) H R).card^3 ≤ 1200*((p^k)*(H+1))^2 := by
  have hq : 0<p^k := Nat.pow_pos hp.pos
  have hm := full_capacity p k H R hp hR hunit hS
  have hr := pairMatching_card (p^k) R hq hM
  rw [roots_card (p^k) H R hq hR]
  calc
    _ = R.card^2*(H+1)^2*(R.card*(H+1)) := by ring
    _ ≤ (2*p^k)*(H+1)^2*(600*p^k) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hr) hm
    _ = 1200*((p^k)*(H+1))^2 := by ring

theorem full_fiber_real_bound (p k H : ℕ) (R : Finset ℕ) (hp : p.Prime)
    (hR : ∀ r∈R, r<p^k) (hunit : ∀ r∈R, (p^k).Coprime r)
    (hM : PairMatching (p^k) R)
    (hS : IsSidon (((roots (p^k) H R).image (fun n => n^2)) : Set ℕ)) :
    ((roots (p^k) H R).card : ℝ) ≤ 11*((p^k*(H+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hc : (((roots (p^k) H R).card : ℝ))^3 ≤
      1200*((p^k*(H+1) : ℕ) : ℝ)^2 := by
    exact_mod_cast full_fiber_card_bound p k H R hp hR hunit hM hS
  have he : (11*((p^k*(H+1) : ℕ) : ℝ)^(2/3 : ℝ))^3 =
      1331*((p^k*(H+1) : ℕ) : ℝ)^2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  apply (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp
  rw [he]
  nlinarith only [hc, sq_nonneg (((p^k*(H+1) : ℕ) : ℝ))]

/-- The same restricted-family bound, counting square values rather than roots. -/
theorem full_value_real_bound (p k H : ℕ) (R : Finset ℕ) (hp : p.Prime)
    (hR : ∀ r∈R, r<p^k) (hunit : ∀ r∈R, (p^k).Coprime r)
    (hM : PairMatching (p^k) R)
    (hS : IsSidon (((roots (p^k) H R).image (fun n => n^2)) : Set ℕ)) :
    (((roots (p^k) H R).image (fun n => n^2)).card : ℝ) ≤
      11*((p^k*(H+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  rw [card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))]
  exact full_fiber_real_bound p k H R hp hR hunit hM hS

#print axioms gap_capacity
#print axioms unit_gaps
#print axioms short_capacity
#print axioms full_capacity
#print axioms full_fiber_card_bound
#print axioms full_fiber_real_bound
#print axioms full_value_real_bound
end Erdos773.PrimePowerFullFiberBound
