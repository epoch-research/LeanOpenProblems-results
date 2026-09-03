import Submission.Spec
import Submission.QuarticPrimeClassification
import Submission.LocalPowerRoots
import Submission.QuarticReduction

/-! Exact strictness of quartic count scaling away from the exceptional primes.
These statements do not assert polynomial-sized peaks or iterative amplification. -/

noncomputable section
namespace Erdos322Research.QuarticStrictPrimeScaling

private abbrev Rep (n : ℕ) :=
  {a : Fin 4 → Fin (n+1) // ∑ i, (a i : ℕ)^4 = n}

private theorem card_rep (n : ℕ) : Fintype.card (Rep n) = Erdos322.representationCount 4 n := by
  simp [Rep, Fintype.card_subtype, Erdos322.representationCount]

private def scale (p n : ℕ) (a : Rep n) : Rep (p^4*n) :=
  ⟨fun i ↦ ⟨p*(a.val i : ℕ), by
    have ha : (a.val i : ℕ) ≤ n := Nat.le_of_lt_succ (a.val i).isLt
    have hp : p ≤ p^4 := Nat.le_pow (by decide)
    exact Nat.lt_succ_of_le (Nat.mul_le_mul hp ha)⟩, by
    simp only [mul_pow, ← Finset.mul_sum, a.property]⟩

private theorem scale_injective (p n : ℕ) (hp : 0 < p) :
    Function.Injective (scale p n) := by
  intro a b he
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrArg (fun a : Rep (p^4*n) ↦ (a.val i : ℕ)) he
  exact Nat.eq_of_mul_eq_mul_left hp hi

/-- A representation with a coordinate not divisible by the scale is outside
its scaling image and therefore forces a strict inequality of full counts. -/
theorem strict_of_extra_representation (p n : ℕ) (hp : 0 < p)
    (a : Fin 4 → ℕ) (ha : ∑ i, a i^4 = p^4*n) (hfirst : ¬p ∣ a 0) :
    Erdos322.representationCount 4 n < Erdos322.representationCount 4 (p^4*n) := by
  let b : Rep (p^4*n) := ⟨fun i ↦ ⟨a i, by
    have hb := Finset.single_le_sum (f := fun j : Fin 4 ↦ a j^4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hc : a i ≤ a i^4 := Nat.le_pow (by decide)
    rw [ha] at hb
    exact Nat.lt_succ_of_le (hc.trans hb)⟩, ha⟩
  have hns : ¬Function.Surjective (scale p n) := by
    intro hs
    obtain ⟨c, hc⟩ := hs b
    apply hfirst
    have he := congrArg (fun a : Rep (p^4*n) ↦ (a.val 0 : ℕ)) hc
    change p*(c.val 0 : ℕ) = a 0 at he
    exact he ▸ dvd_mul_right p (c.val 0 : ℕ)
  have hc := Fintype.card_lt_of_injective_not_surjective (scale p n)
    (scale_injective p n hp) hns
  simpa only [card_rep] using hc

/-- Every nonexceptional prime admits a quartic zero modulo any positive power,
with its first coordinate not divisible by that prime. -/
theorem exists_lifted_zero (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ a : Fin 4 → ℕ, p^(e+1) ∣ ∑ i, a i^4 ∧ ¬p ∣ a 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hk : ¬p ∣ 4 := by
    intro hd
    have he : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hd)
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp he |>.resolve_left hp.ne_one)
  obtain ⟨a,b,c,d,ha,hs⟩ := QuarticPrimeClassification.exists_nontrivial_fourth_sum
    (K := ZMod p) (by simpa only [ZMod.card] using hp5)
  let v : ZMod (p^(e+1)) := -((b.val : ZMod (p^(e+1)))^4+
    (c.val : ZMod (p^(e+1)))^4+(d.val : ZMod (p^(e+1)))^4)
  have hv : LocalPowerRoots.reduction p e v = a^4 := by
    simp only [v, map_neg, map_add, map_pow, LocalPowerRoots.reduction_natCast,
      ZMod.natCast_zmod_val]
    linear_combination -hs
  obtain ⟨x,hx,hpow⟩ := LocalPowerRoots.exists_pow_root p e 4 hk a ha v hv
  refine ⟨![x.val,b.val,c.val,d.val], ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Nat.cast_add, Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [hpow]
    dsimp [v]
    ring
  · intro hd
    apply ha
    have he : (x.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [← LocalPowerRoots.reduction_natCast p e, ZMod.natCast_zmod_val, hx] at he
    exact he

/-- For every prime other than 2 and 5, strict count growth occurs on infinitely
many fourth-power-scaled targets. This gives additive, not power-sized, growth. -/
theorem infinitely_many_strict_scalings (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    {n : ℕ | Erdos322.representationCount 4 n <
      Erdos322.representationCount 4 (p^4*n)}.Infinite := by
  have hp : p.Prime := Fact.out
  obtain ⟨a,ha,ha0⟩ := exists_lifted_zero p 3 hp2 hp5
  obtain ⟨n,hn⟩ := ha
  have hnpos : 0 < n := by
    have ha0pos : 0 < a 0 := Nat.pos_of_ne_zero (fun he ↦ ha0 (he ▸ dvd_zero p))
    have hb := Finset.single_le_sum (f := fun i : Fin 4 ↦ a i^4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ 0)
    have hc : 0 < a 0^4 := pow_pos ha0pos _
    change (∑ i, a i^4) = p^4*n at hn
    have he : 0 < p^4*n := by rw [← hn]; exact hc.trans_le hb
    by_contra hn0
    have hz : n = 0 := by omega
    rw [hz, mul_zero] at he
    omega
  let N : ℕ → ℕ := fun m ↦ n*(p*m+1)^4
  have hinj : Function.Injective N := by
    intro x y he
    have hpw : (p*x+1)^4 = (p*y+1)^4 := Nat.eq_of_mul_eq_mul_left hnpos he
    have hxy := Nat.pow_left_injective (by decide : 4 ≠ 0) hpw
    have hm : p*x = p*y := by omega
    exact Nat.eq_of_mul_eq_mul_left hp.pos hm
  apply (Set.infinite_range_of_injective hinj).mono
  rintro t ⟨m,rfl⟩
  apply strict_of_extra_representation p (N m) hp.pos (fun i ↦ (p*m+1)*a i)
  · simp only [mul_pow, ← Finset.mul_sum, hn]
    dsimp [N]
    ring
  · intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · have he : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_right p m)).mpr hd
      exact hp.not_dvd_one he
    · exact ha0 hd

/-- Exactly 2 and 5 have count-preserving fourth-power scaling at every target. -/
theorem count_preserving_prime_iff (p : ℕ) [Fact p.Prime] :
    (∀ n : ℕ, Erdos322.representationCount 4 (p^4*n) = Erdos322.representationCount 4 n) ↔
      p = 2 ∨ p = 5 := by
  constructor
  · intro he
    by_contra hn
    push_neg at hn
    obtain ⟨n,hn'⟩ := (infinitely_many_strict_scalings p hn.1 hn.2).nonempty
    change Erdos322.representationCount 4 n < Erdos322.representationCount 4 (p^4*n) at hn'
    rw [he] at hn'
    exact (lt_irrefl _ hn')
  · rintro (rfl | rfl) n
    · simpa only [Erdos322.representationCount, Erdos322Research.representationCount,
        show (2 : ℕ)^4 = 16 by norm_num] using Erdos322Research.quartic_count_scale_two n
    · simpa only [Erdos322.representationCount, Erdos322Research.representationCount,
        show (5 : ℕ)^4 = 625 by norm_num] using Erdos322Research.quartic_count_scale_five n

/-- Positive fourth-power scaling never decreases the full representation count. -/
theorem count_scale_mono (m n : ℕ) (hm : 0 < m) :
    Erdos322.representationCount 4 n ≤ Erdos322.representationCount 4 (m^4*n) := by
  have he := Fintype.card_le_of_injective (scale m n) (scale_injective m n hm)
  simpa only [card_rep] using he

/-- Every positive scale with a nonexceptional prime factor has strict count
increases at infinitely many targets. -/
theorem infinitely_many_strict_composite_scalings (m p : ℕ) (hm : 0 < m)
    [Fact p.Prime] (hpm : p ∣ m) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    {n : ℕ | Erdos322.representationCount 4 n <
      Erdos322.representationCount 4 (m^4*n)}.Infinite := by
  obtain ⟨q,hq⟩ := hpm
  have hqpos : 0 < q := by
    by_contra he
    have hz : q = 0 := by omega
    simp [hz] at hq
    omega
  apply (infinitely_many_strict_scalings p hp2 hp5).mono
  intro n hn
  change Erdos322.representationCount 4 n < Erdos322.representationCount 4 (m^4*n)
  change Erdos322.representationCount 4 n < Erdos322.representationCount 4 (p^4*n) at hn
  apply hn.trans_le
  convert count_scale_mono q (p^4*n) hqpos using 1
  rw [hq]
  congr 1
  ring

/-- Full count-preserving scales are precisely the positive integers whose
prime divisors all belong to `{2,5}`. -/
theorem count_preserving_scale_iff (m : ℕ) (hm : 0 < m) :
    (∀ n : ℕ, Erdos322.representationCount 4 (m^4*n) = Erdos322.representationCount 4 n) ↔
      ∀ p : ℕ, p.Prime → p ∣ m → p = 2 ∨ p = 5 := by
  constructor
  · intro he p hp hpm
    letI : Fact p.Prime := ⟨hp⟩
    by_contra hn
    push_neg at hn
    obtain ⟨n,hn'⟩ := (infinitely_many_strict_composite_scalings m p hm hpm hn.1 hn.2).nonempty
    change Erdos322.representationCount 4 n < Erdos322.representationCount 4 (m^4*n) at hn'
    rw [he] at hn'
    exact lt_irrefl _ hn'
  · induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hpr n
      by_cases hm1 : m = 1
      · simp [hm1]
      · let p := m.minFac
        have hp : p.Prime := Nat.minFac_prime hm1
        have hpm : p ∣ m := Nat.minFac_dvd m
        obtain ⟨q,hq⟩ := hpm
        have hqpos : 0 < q := by
          by_contra he
          have hz : q = 0 := by omega
          simp [hz] at hq
          omega
        have hqlt : q < m := by
          have hp2 := hp.two_le
          rw [hq]
          nlinarith
        have hqr : ∀ r : ℕ, r.Prime → r ∣ q → r = 2 ∨ r = 5 := by
          intro r hr hd
          apply hpr r hr
          rw [hq]
          exact dvd_mul_of_dvd_right hd p
        have hsmall := ih q hqlt hqpos hqr n
        letI : Fact p.Prime := ⟨hp⟩
        have hlarge := (count_preserving_prime_iff p).mpr (hpr p hp ⟨q,hq⟩) (q^4*n)
        calc
          Erdos322.representationCount 4 (m^4*n) =
              Erdos322.representationCount 4 (p^4*(q^4*n)) := by rw [hq]; congr 1; ring
          _ = Erdos322.representationCount 4 (q^4*n) := hlarge
          _ = Erdos322.representationCount 4 n := hsmall

end Erdos322Research.QuarticStrictPrimeScaling
