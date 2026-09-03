import Submission.SquarefreeInput

/-!
# Fibers of fixed iterates of Euler's totient

The exact fiber recurrence is a sum, not a preservation theorem for maximal
multiplicity exponents. These auxiliary results do not settle Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821
namespace IteratedTotient

lemma finite_fiber (k n : ℕ) : {m : ℕ | (Nat.totient^[k]) m = n}.Finite := by
  induction k with
  | zero => simp
  | succ k ih =>
    have H := ih.preimage' (f := Nat.totient) (fun j _ => finite_totient_fiber j)
    simpa only [Set.preimage_setOf_eq, Function.iterate_succ_apply] using H

noncomputable def fiber (k n : ℕ) : Finset ℕ := (finite_fiber k n).toFinset

@[simp] lemma mem_fiber (k n m : ℕ) : m ∈ fiber k n ↔ (Nat.totient^[k]) m = n :=
  (finite_fiber k n).mem_toFinset

noncomputable def multiplicity (k n : ℕ) : ℕ :=
  {m : ℕ | (Nat.totient^[k]) m = n}.ncard

@[simp] lemma card_fiber (k n : ℕ) : (fiber k n).card = multiplicity k n :=
  (Set.ncard_eq_toFinset_card _ (finite_fiber k n)).symm

@[simp] lemma fiber_zero (n : ℕ) : fiber 0 n = {n} := by
  ext m
  simp

@[simp] lemma multiplicity_zero (n : ℕ) : multiplicity 0 n = 1 := by
  rw [← card_fiber, fiber_zero, Finset.card_singleton]

@[simp] lemma multiplicity_one (n : ℕ) : multiplicity 1 n = g n := by
  simp only [multiplicity, Function.iterate_one, g]

lemma fiber_succ (k n : ℕ) : fiber (k+1) n = (fiber 1 n).biUnion (fiber k) := by
  ext m
  simp only [mem_fiber, Finset.mem_biUnion, Function.iterate_succ_apply']
  constructor
  · intro h
    exact ⟨(Nat.totient^[k]) m, h, rfl⟩
  · rintro ⟨j, hj, hm⟩
    exact hm ▸ hj

lemma fibers_pairwise_disjoint (k : ℕ) : Pairwise (fun a b => Disjoint (fiber k a) (fiber k b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro m hm hmb
  exact hab ((mem_fiber k a m).mp hm |>.symm.trans ((mem_fiber k b m).mp hmb))

/-- An exact recurrence. Different intermediate outputs have disjoint fibers. -/
theorem multiplicity_succ (k n : ℕ) :
    multiplicity (k+1) n = ∑ m ∈ fiber 1 n, multiplicity k m := by
  rw [← card_fiber, fiber_succ, Finset.card_biUnion]
  · simp only [card_fiber]
  · intro a _ b _ hab
    exact fibers_pairwise_disjoint k hab

lemma iterate_le (k m : ℕ) : (Nat.totient^[k]) m ≤ m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (Nat.totient_le _).trans ih

lemma output_le_of_mem {k n m : ℕ} (hm : m ∈ fiber k n) : n ≤ m := by
  rw [← mem_fiber k n m |>.mp hm]
  exact iterate_le k m

/-- In every large one-step fiber, all inputs are within an arbitrary fixed
positive power loss of their common output. -/
lemma eventually_input_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, Nat.totient m = n →
      (m : ℝ) ≤ (n : ℝ)^(1+ε) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkR : 0 < (k : ℝ) := (div_pos (by norm_num) hε).trans hk
  have hkN : 0 < k := by exact_mod_cast hkR
  have hkε : 2 < (k : ℝ)*ε := (div_lt_iff₀ hε).mp hk
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop (((2^(k+1)).factorial)^k)] with n hn hC m hm
  have hp : m^k ≤ n^(k+2) := by
    calc
      m^k ≤ ((2^(k+1)).factorial)^k * n^(k+1) := by
        simpa only [hm] using input_pow_le_totient_pow m k hkN
      _ ≤ n * n^(k+1) := Nat.mul_le_mul_right _ hC
      _ = n^(k+2) := (pow_succ' n (k+1)).symm
  have hpR : (m : ℝ)^k ≤ (n : ℝ)^(k+2) := by exact_mod_cast hp
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : (n : ℝ)^(k+2) ≤ ((n : ℝ)^(1+ε))^k := by
    rw [← Real.rpow_natCast (n : ℝ) (k+2),
      ← Real.rpow_natCast ((n : ℝ)^(1+ε)) k,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    apply Real.rpow_le_rpow_of_exponent_le hnR
    push_cast
    nlinarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg m)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hkN.ne').mp (hpR.trans hb)

/-- The same input-size conclusion holds for every fixed number of iterates. -/
lemma eventually_iterated_input_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ fiber k n, (m : ℝ) ≤ (n : ℝ)^(1+ε) := by
  induction k generalizing ε with
  | zero =>
    filter_upwards [eventually_ge_atTop 1] with n hn m hm
    have hmn : m = n := by simpa using hm
    subst m
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n)
        (show (1 : ℝ) ≤ 1+ε by linarith)
  | succ k ih =>
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ih (ε/2) (half_pos hε))
    have he : 0 < ε/(2+ε) := div_pos hε (by linarith)
    filter_upwards [eventually_input_le_rpow (ε/(2+ε)) he,
      eventually_ge_atTop N, eventually_ge_atTop 1] with n hn hnN hn1 m hm
    let j := (Nat.totient^[k]) m
    have hj : Nat.totient j = n := by
      simpa only [Function.iterate_succ_apply'] using (mem_fiber (k+1) n m).mp hm
    have hnj : n ≤ j := hj ▸ Nat.totient_le j
    have hmj : m ∈ fiber k j := (mem_fiber k j m).mpr rfl
    have hmB := hN j (hnN.trans hnj) m hmj
    have hjB := hn j hj
    calc
      (m : ℝ) ≤ (j : ℝ)^(1+ε/2) := hmB
      _ ≤ ((n : ℝ)^(1+ε/(2+ε)))^(1+ε/2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg j) hjB (by linarith)
      _ = (n : ℝ)^(1+ε) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        field_simp
        ring

/-- Counting the bounded inputs gives the universal exponent ceiling one for
any fixed iterate, independently of a conjectural bound on g. -/
theorem eventually_multiplicity_le_one_add (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (multiplicity k n : ℝ) ≤ (n : ℝ)^(1+ε) := by
  filter_upwards [eventually_iterated_input_le_rpow k ε hε,
    eventually_ge_atTop 1] with n hn hn1
  by_cases hF : (fiber k n).Nonempty
  · let M := (fiber k n).max' hF
    have hM : M ∈ fiber k n := Finset.max'_mem _ hF
    have hsub : fiber k n ⊆ Finset.Icc 1 M := by
      intro m hm
      exact Finset.mem_Icc.mpr ⟨hn1.trans (output_le_of_mem hm), Finset.le_max' _ m hm⟩
    have hcard : multiplicity k n ≤ M := by
      simpa only [card_fiber, Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (by exact_mod_cast hcard : (multiplicity k n : ℝ) ≤ M).trans (hn M hM)
  · have hm : multiplicity k n = 0 := by
      rw [← card_fiber, Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty]
    rw [hm, Nat.cast_zero]
    positivity

/-- A single application of the recurrence adds the two available power
bounds, with an arbitrarily small loss for the intermediate input size. -/
lemma eventually_multiplicity_succ_le (k : ℕ) (a b ε : ℝ)
    (hb : 0 ≤ b) (hε : 0 < ε)
    (Ha : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^a)
    (Hb : ∀ᶠ n : ℕ in atTop, (multiplicity k n : ℝ) ≤ (n : ℝ)^b) :
    ∀ᶠ n : ℕ in atTop, (multiplicity (k+1) n : ℝ) ≤ (n : ℝ)^(a+b+ε) := by
  let η := ε/(b+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hid : η*(b+1) = ε := by dsimp [η]; field_simp
  have hηb : η*b ≤ ε := by nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp Hb
  filter_upwards [Ha, eventually_input_le_rpow η hη,
    eventually_ge_atTop N, eventually_ge_atTop 1] with n hnA hnB hnN hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hpoint (m : ℕ) (hm : m ∈ fiber 1 n) :
      (multiplicity k m : ℝ) ≤ (n : ℝ)^((1+η)*b) := by
    have hφ : Nat.totient m = n := by simpa only [mem_fiber, Function.iterate_one] using hm
    calc
      (multiplicity k m : ℝ) ≤ (m : ℝ)^b := hN m (hnN.trans (output_le_of_mem hm))
      _ ≤ ((n : ℝ)^(1+η))^b :=
        Real.rpow_le_rpow (Nat.cast_nonneg m) (hnB m hφ) hb
      _ = (n : ℝ)^((1+η)*b) := (Real.rpow_mul hnpos.le _ _).symm
  have hsum : (multiplicity (k+1) n : ℝ) ≤ (g n : ℝ)*(n : ℝ)^((1+η)*b) := by
    rw [multiplicity_succ, Nat.cast_sum]
    calc
      (∑ m ∈ fiber 1 n, (multiplicity k m : ℝ)) ≤
          ∑ _m ∈ fiber 1 n, (n : ℝ)^((1+η)*b) := Finset.sum_le_sum hpoint
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, card_fiber, multiplicity_one]
  calc
    (multiplicity (k+1) n : ℝ) ≤ (g n : ℝ)*(n : ℝ)^((1+η)*b) := hsum
    _ ≤ (n : ℝ)^a*(n : ℝ)^((1+η)*b) :=
      mul_le_mul_of_nonneg_right hnA (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ)^(a+(1+η)*b) := (Real.rpow_add hnpos _ _).symm
    _ ≤ (n : ℝ)^(a+b+ε) := Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith)

/-- A hypothetical exponent a for g gives exponent k*a, not exponent a,
by the elementary iteration argument. The independent ceiling one above
may give the stronger bound when k*a exceeds one. -/
theorem eventually_multiplicity_le_mul_exponent (a : ℝ) (ha : 0 ≤ a)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^a)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (multiplicity k n : ℝ) ≤ (n : ℝ)^((k : ℝ)*a+ε) := by
  induction k generalizing ε with
  | zero =>
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [multiplicity_zero, Nat.cast_one, Nat.cast_zero, zero_mul, zero_add]
    exact Real.one_le_rpow (by exact_mod_cast hn) hε.le
  | succ k ih =>
    have hb : 0 ≤ (k : ℝ)*a+ε/2 := by positivity
    have HH := eventually_multiplicity_succ_le k a ((k : ℝ)*a+ε/2) (ε/2)
      hb (half_pos hε) H (ih (ε/2) (half_pos hε))
    have he : a+((k : ℝ)*a+ε/2)+ε/2 = ((k+1 : ℕ) : ℝ)*a+ε := by
      push_cast
      ring
    simpa only [he] using HH

/-- In particular, an iterated lower bound only contradicts a one-step upper
exponent a through this argument when its exponent exceeds k*a. -/
theorem finite_large_iterated_fibers_of_power_bound (a b : ℝ) (ha : 0 ≤ a)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^a)
    (k : ℕ) (hb : (k : ℝ)*a < b) :
    {n : ℕ | (n : ℝ)^b < (multiplicity k n : ℝ)}.Finite := by
  have HH := eventually_multiplicity_le_mul_exponent a ha H k
    (b-(k : ℝ)*a) (sub_pos.mpr hb)
  have he : (k : ℝ)*a+(b-(k : ℝ)*a) = b := by ring
  rw [he] at HH
  obtain ⟨N, hN⟩ := eventually_atTop.mp HH
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra hh
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt hh))) hn

noncomputable def restrictedSecondMultiplicity (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  ((fiber 2 n).filter (fun m => P (Nat.totient m))).card

/-- Restricting the middle value restricts the same disjoint fiber sum. -/
lemma restricted_second_eq_sum (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    restrictedSecondMultiplicity P n = ∑ m ∈ (fiber 1 n).filter P, g m := by
  have he : (fiber 2 n).filter (fun m => P (Nat.totient m)) =
      ((fiber 1 n).filter P).biUnion (fiber 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, mem_fiber,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
    constructor
    · rintro ⟨hx, hP⟩
      exact ⟨Nat.totient x, ⟨hx, hP⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hP⟩, hx⟩
      exact ⟨hx ▸ hj, hx ▸ hP⟩
  unfold restrictedSecondMultiplicity
  rw [he, Finset.card_biUnion]
  · simp only [card_fiber, multiplicity_one]
  · intro a _ b _ hab
    exact fibers_pairwise_disjoint 1 hab

/-- If g is subpower on the permitted middle values, those values contribute
at most a subpower factor times their number in the first fiber. -/
theorem eventually_restricted_second_le (P : ℕ → Prop) [DecidablePred P]
    (H : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop, P m → (g m : ℝ) ≤ (m : ℝ)^δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (restrictedSecondMultiplicity P n : ℝ) ≤
        (((fiber 1 n).filter P).card : ℝ)*(n : ℝ)^ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (H (ε/2) (half_pos hε))
  filter_upwards [eventually_input_le_rpow 1 (by norm_num),
    eventually_ge_atTop N] with n hn hnN
  rw [restricted_second_eq_sum, Nat.cast_sum]
  calc
    (∑ m ∈ (fiber 1 n).filter P, (g m : ℝ)) ≤
        ∑ _m ∈ (fiber 1 n).filter P, (n : ℝ)^ε := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hmF, hmP⟩ := Finset.mem_filter.mp hm
      have hφ : Nat.totient m = n := by simpa only [mem_fiber, Function.iterate_one] using hmF
      calc
        (g m : ℝ) ≤ (m : ℝ)^(ε/2) := hN m (hnN.trans (output_le_of_mem hmF)) hmP
        _ ≤ ((n : ℝ)^(1+(1 : ℝ)))^(ε/2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (hn m hφ) (half_pos hε).le
        _ = (n : ℝ)^ε := by
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1
          ring
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Bounded 2-adic valuation of the middle value cannot amplify a
multiplicity exponent by a fixed positive amount. -/
theorem eventually_bounded_valuation_second_le (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (restrictedSecondMultiplicity (fun m => m.factorization 2 ≤ K) n : ℝ) ≤
        (((fiber 1 n).filter (fun m => m.factorization 2 ≤ K)).card : ℝ)*(n : ℝ)^ε :=
  eventually_restricted_second_le _
    (fun δ hδ => eventually_g_le_rpow_of_two_valuation_le K δ hδ) ε hε

/-- Squarefree middle values are one important special case: their total
contribution is at most gSquarefree(n) times an arbitrarily small power. -/
theorem eventually_squarefree_second_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (restrictedSecondMultiplicity Squarefree n : ℝ) ≤ (gSquarefree n : ℝ)*(n : ℝ)^ε := by
  have H : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Squarefree m → (g m : ℝ) ≤ (m : ℝ)^δ := by
    intro δ hδ
    filter_upwards [eventually_g_le_rpow_of_two_valuation_le 1 δ hδ] with m hm hSq
    exact hm (hSq.natFactorization_le_one 2)
  have hc (n : ℕ) : ((fiber 1 n).filter Squarefree).card = gSquarefree n := by
    have he : (↑((fiber 1 n).filter Squarefree) : Set ℕ) =
        {m : ℕ | Squarefree m ∧ Nat.totient m = n} := by
      ext m
      simp only [Finset.mem_coe, Finset.mem_filter, mem_fiber, Function.iterate_one,
        Set.mem_setOf_eq, and_comm]
    rw [← Set.ncard_coe_finset, he]
    rfl
  simpa only [hc] using eventually_restricted_second_le Squarefree H ε hε

end IteratedTotient
end Erdos821
