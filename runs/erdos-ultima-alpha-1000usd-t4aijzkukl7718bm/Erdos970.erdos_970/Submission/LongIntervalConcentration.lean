import Submission.ConstructiveCover
import Submission.OptimalCoverCore

/-! Relative concentration with a universal additive error fails even on intervals
arbitrarily longer than the square of the number of sieving primes. This is an
obstruction to a counting estimate, not a disproof of Erdős 970. -/
namespace Erdos970.LongIntervalConcentration
open OptimalCoverCore

lemma totient_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).totient = ∏ p ∈ P, (p - 1) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hpp := hP p (Finset.mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hpp (hP' q hq)).mpr
      rintro rfl
      exact hp hq
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hco,
      Nat.totient_prime hpp, ih hP']

lemma zero_survivors_eq (m : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    survivors m P (fun _ => 0) =
      (Finset.range m).filter (fun i => (∏ p ∈ P, p).Coprime i) := by
  classical
  apply Finset.filter_congr
  intro i hi
  rw [Nat.coprime_prod_left_iff]
  apply forall₂_congr
  intro p hp
  rw [(hP p hp).coprime_iff_not_dvd]
  simp only [Nat.modEq_zero_iff_dvd]

/-- A complete-period estimate, with an error of at most one period. -/
lemma zero_survivors_scaled_le (m : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p) * (survivors m P (fun _ => 0)).card ≤
      (∏ p ∈ P, (p - 1)) * (m + ∏ p ∈ P, p) := by
  classical
  let N := ∏ p ∈ P, p
  have hN : 0 < N := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hc := Nat.Ico_filter_coprime_le 0 m hN.ne'
  simp only [Nat.zero_add, Nat.Ico_zero_eq_range] at hc
  dsimp only [N] at hc
  rw [← zero_survivors_eq m P hP, totient_prime_product P hP] at hc
  have hmul := Nat.mul_le_mul_left N hc
  have hdiv := Nat.div_mul_le_self m N
  have hdiv' := Nat.mul_le_mul_left (∏ p ∈ P, (p - 1)) hdiv
  dsimp only [N] at hmul hdiv'
  nlinarith only [hmul, hdiv']

/-- If all old primes exceed `T`, every one of `p,2p,...,T*p` survives them. -/
lemma many_removed (T p : ℕ) (P : Finset ℕ) (hp : p.Prime)
    (hP : ∀ q ∈ P, q.Prime ∧ T < q ∧ q < p) :
    T ≤ ((survivors ((T + 1) * p) P (fun _ => 0)).filter
      (fun i => i ≡ 0 [MOD p])).card := by
  classical
  have hinj : Function.Injective (fun j : ℕ => (j + 1) * p) := by
    intro i j hij
    have := Nat.eq_of_mul_eq_mul_right hp.pos hij
    omega
  have hsub : (Finset.range T).image (fun j => (j + 1) * p) ⊆
      (survivors ((T + 1) * p) P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p]) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjT := Finset.mem_range.mp hj
    refine Finset.mem_filter.mpr ⟨mem_survivors _ _ _ _ |>.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mul_lt_mul_of_pos_right (by omega) hp.pos
    · intro q hq hbad
      have hd : q ∣ (j + 1) * p := Nat.modEq_zero_iff_dvd.mp hbad
      rcases (hP q hq).1.dvd_mul.mp hd with hd | hd
      · have := Nat.le_of_dvd (by omega : 0 < j + 1) hd
        have := (hP q hq).2.1
        omega
      · have he : q = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hP q hq).1.ne_one
        have := (hP q hq).2.2
        omega
    · exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p (j + 1))
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_range] using
    Finset.card_le_card hsub

/-- No universal relative concentration factor plus constant error works, even
when the interval is arbitrarily long and exceeds any prescribed quadratic threshold. -/
theorem unbounded_additive_concentration (A B C M : ℕ) :
    ∃ (P : Finset ℕ) (p m : ℕ),
      (∀ q ∈ P, q.Prime ∧ q < p) ∧ p.Prime ∧
      M ≤ m ∧ C * (P.card + 1) ^ 2 ≤ m ∧
      B * (survivors m P (fun _ => 0)).card + A * p <
        p * ((survivors m P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p])).card := by
  classical
  let T := A + 2
  obtain ⟨P, hP, hden⟩ := ConstructiveCover.exists_prime_tail_density T (2 * (B + 1) * (T + 1))
  let N := ∏ q ∈ P, q
  let F := ∏ q ∈ P, (q - 1)
  have hN : 0 < N := Finset.prod_pos (fun q hq => (hP q hq).1.pos)
  obtain ⟨p, hpbig, hp⟩ := Nat.exists_infinite_primes
    (P.sup id + 2 * (B + 1) * F + C * (P.card + 1) ^ 2 + M + 1)
  have hqp (q : ℕ) (hq : q ∈ P) : q < p := by
    have hqle : q ≤ P.sup id := Finset.le_sup (f := id) hq
    omega
  let m := (T + 1) * p
  have hpm : p ≤ m := by dsimp [m]; nlinarith
  have hC : C * (P.card + 1) ^ 2 ≤ m := by omega
  have hM : M ≤ m := by omega
  have hsmall : B * (survivors m P (fun _ => 0)).card ≤ p := by
    have hcount := zero_survivors_scaled_le m P (fun q hq => (hP q hq).1)
    change N * (survivors m P (fun _ => 0)).card ≤ F * (m + N) at hcount
    change 2 * (B + 1) * (T + 1) * F ≤ N at hden
    have hBF : 2 * B * F ≤ p := by nlinarith
    have hd : 2 * B * (T + 1) * F ≤ N := by nlinarith
    have hd' := Nat.mul_le_mul_right p hd
    have hBF' := Nat.mul_le_mul_right N hBF
    have hcount' := Nat.mul_le_mul_left (2 * B) hcount
    dsimp only [m] at hcount'
    nlinarith
  have hremoved := many_removed T p P hp (fun q hq => ⟨(hP q hq).1, (hP q hq).2, hqp q hq⟩)
  refine ⟨P, p, m, (fun q hq => ⟨(hP q hq).1, hqp q hq⟩), hp, hM, hC, ?_⟩
  change T ≤ ((survivors m P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p])).card at hremoved
  have := Nat.mul_le_mul_left p hremoved
  have := hp.pos
  dsimp only [T] at *
  nlinarith

/-- Even allowing arbitrary real constants and restricting to quadratic-length
intervals does not repair the relative-plus-constant estimate. -/
theorem not_uniform_relative_estimate (C : ℕ) :
    ¬∃ A B : ℝ, ∀ (P : Finset ℕ) (p m : ℕ),
      (∀ q ∈ P, q.Prime ∧ q < p) → p.Prime →
      C * (P.card + 1) ^ 2 ≤ m →
      (((survivors m P (fun _ => 0)).filter
        (fun i => i ≡ 0 [MOD p])).card : ℝ) ≤
          B * (survivors m P (fun _ => 0)).card / p + A := by
  rintro ⟨A, B, h⟩
  obtain ⟨a, ha⟩ := exists_nat_gt A
  obtain ⟨b, hb⟩ := exists_nat_gt B
  obtain ⟨P, p, m, hP, hp, hM, hC, hbad⟩ := unbounded_additive_concentration a b C 0
  have hu := h P p m hP hp hC
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hm := mul_le_mul_of_nonneg_right hu hpR.le
  rw [add_mul, div_mul_cancel₀ _ hpR.ne'] at hm
  have hbadR : (b : ℝ) * (survivors m P (fun _ => 0)).card + (a : ℝ) * p <
      (p : ℝ) * ((survivors m P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p])).card := by
    exact_mod_cast hbad
  have hA := mul_le_mul_of_nonneg_right ha.le hpR.le
  have hB := mul_le_mul_of_nonneg_right hb.le
    (Nat.cast_nonneg (survivors m P (fun _ => 0)).card)
  nlinarith only [hm, hbadR, hA, hB]

#print axioms unbounded_additive_concentration
#print axioms not_uniform_relative_estimate
end Erdos970.LongIntervalConcentration
