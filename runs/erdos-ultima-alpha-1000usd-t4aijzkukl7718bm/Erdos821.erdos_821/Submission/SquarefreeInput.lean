import Submission.Valuation

/-!
# Reduction to squarefree preimages

This file reduces Erdős 821 to the same conjecture restricted to squarefree
inputs. It does not prove or disprove either conjecture.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

noncomputable def gSquarefree (n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ totient m = n}.ncard

lemma finite_squarefree_totient_fiber (n : ℕ) :
    {m : ℕ | Squarefree m ∧ totient m = n}.Finite :=
  (finite_totient_fiber n).subset (fun _ hm => hm.2)

lemma gSquarefree_le_g (n : ℕ) : gSquarefree n ≤ g n :=
  Set.ncard_le_ncard (fun _ hm => hm.2) (finite_totient_fiber n)

lemma squarefree_prod_of_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hprime : p.Prime := hS p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp]
    apply (Nat.squarefree_mul ?_).mpr ⟨hprime.squarefree, ih hrest⟩
    apply Nat.Coprime.prod_right
    intro q hq
    apply hprime.coprime_iff_not_dvd.mpr
    intro hd
    have heq : q = p := ((hrest q hq).dvd_iff_eq hprime.ne_one).mp hd
    exact hp (heq ▸ hq)

/-- The radical map is injective on every fixed totient fiber. -/
lemma radical_injOn_totient_fiber (n : ℕ) :
    Set.InjOn (fun m : ℕ => ∏ p ∈ m.primeFactors, p) {m : ℕ | totient m = n} := by
  intro a ha b hb hab
  apply eq_of_totient_eq_of_primeFactors_eq (ha.trans hb.symm)
  have h := congrArg Nat.primeFactors hab
  simpa only [Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)] using h

/-- Stripping prime powers maps a fixed fiber injectively into squarefree
fibers indexed by divisors of the original output. -/
lemma g_le_sum_gSquarefree_divisors (n : ℕ) (hn : 0 < n) :
    g n ≤ ∑ d ∈ n.divisors, gSquarefree d := by
  let F := (finite_totient_fiber n).toFinset
  let R := F.image (fun m : ℕ => ∏ p ∈ m.primeFactors, p)
  have hF (m : ℕ) : m ∈ F ↔ totient m = n :=
    (finite_totient_fiber n).mem_toFinset
  have hR (m : ℕ) (hm : m ∈ R) : Squarefree m ∧ totient m ∣ n := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    refine ⟨squarefree_prod_of_primes _ (fun _ hp => Nat.prime_of_mem_primeFactors hp), ?_⟩
    rw [← (hF a).mp ha]
    exact Nat.totient_dvd_of_dvd (Nat.prod_primeFactors_dvd a)
  have hcard : R.card = g n := by
    rw [show R = F.image (fun m : ℕ => ∏ p ∈ m.primeFactors, p) from rfl,
      Finset.card_image_of_injOn]
    · exact (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
    · intro a ha b hb hab
      exact radical_injOn_totient_fiber n ((hF a).mp ha) ((hF b).mp hb) hab
  have hmaps : Set.MapsTo totient (R : Set ℕ) (n.divisors : Set ℕ) := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(hR m hm).2, hn.ne'⟩
  rw [← hcard, Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro d hd
  have hsub : (R.filter (fun m => totient m = d) : Set ℕ) ⊆
      {m : ℕ | Squarefree m ∧ totient m = d} := by
    intro m hm
    obtain ⟨hmR, hmd⟩ := Finset.mem_filter.mp hm
    exact ⟨(hR m hmR).1, hmd⟩
  have h := Set.ncard_le_ncard hsub (finite_squarefree_totient_fiber d)
  simpa only [Set.ncard_coe_finset, gSquarefree] using h

lemma exists_divisor_large_gSquarefree (n : ℕ) (hn : 0 < n) :
    ∃ d ∈ n.divisors, g n ≤ n.divisors.card * gSquarefree d := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image n.divisors gSquarefree
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩⟩
  refine ⟨d, hd, (g_le_sum_gSquarefree_divisors n hn).trans ?_⟩
  calc
    (∑ c ∈ n.divisors, gSquarefree c) ≤ ∑ _c ∈ n.divisors, gSquarefree d :=
      Finset.sum_le_sum hmax
    _ = _ := by simp

/-- Positive multiplicity exponents transfer to squarefree inputs with an
arbitrarily small loss. The selected squarefree output divides the old one. -/
lemma infinite_gSquarefree_gt_of_infinite_g_gt (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (H : {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (α + β)}.Infinite) :
    {n : ℕ | 0 < n ∧ (gSquarefree n : ℝ) > (n : ℝ) ^ α}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let C := (Finset.range (N + 1)).sup gSquarefree
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ (n.divisors.card : ℝ) ≤ (n : ℝ) ^ β ∧ (C : ℝ) < (n : ℝ) ^ α := by
    filter_upwards [eventually_ge_atTop 1, eventually_card_divisors_le_rpow β hβ,
      hlim.eventually (eventually_gt_atTop (C : ℝ))] with n hn hτ hC
    exact ⟨hn, hτ, hC⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  obtain ⟨n, hng, hnM⟩ := H.exists_gt M
  obtain ⟨hn, hτ, hC⟩ := hM n hnM.le
  have hnpos : 0 < n := by omega
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨d, hd, hdg⟩ := exists_divisor_large_gSquarefree n hnpos
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdle : d ≤ n := Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)
  have hbig : (n : ℝ) ^ α < (gSquarefree d : ℝ) := by
    have hprod : (n : ℝ) ^ β * (n : ℝ) ^ α <
        (n : ℝ) ^ β * (gSquarefree d : ℝ) := by
      calc
        (n : ℝ) ^ β * (n : ℝ) ^ α = (n : ℝ) ^ (α + β) := by
          rw [Real.rpow_add hnRpos]; ring
        _ < (g n : ℝ) := hng
        _ ≤ (n.divisors.card : ℝ) * (gSquarefree d : ℝ) := by exact_mod_cast hdg
        _ ≤ _ := mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg _)
    exact (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hnRpos β)).mp hprod
  refine ⟨d, ⟨hdpos, ?_⟩, ?_⟩
  · exact (Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast hdle) hα.le).trans_lt hbig
  · by_contra h
    have hdmem : d ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hgC : (gSquarefree d : ℝ) ≤ C := by
      exact_mod_cast (Finset.le_sup (f := gSquarefree) hdmem)
    exact (not_lt_of_ge hgC) (hC.trans hbig)

/-- The squarefree-input version is exactly equivalent to the original
conjecture, not merely a sufficient condition. -/
lemma erdos_821_iff_squarefree_inputs :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ ε > (0 : ℝ),
        {n : ℕ | (gSquarefree n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  constructor
  · intro H ε hε
    let e : ℝ := min ε (1 / 2)
    have he : 0 < e := lt_min hε (by norm_num)
    have hehalf : e ≤ 1 / 2 := min_le_right _ _
    have heε : e ≤ ε := min_le_left _ _
    have hα : 0 < 1 - e := by linarith
    have hβ : 0 < e / 2 := half_pos he
    have hH : {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((1 - e) + e / 2)}.Infinite := by
      have hexp : (1 - e) + e / 2 = 1 - e / 2 := by ring
      rw [hexp]
      exact H (e / 2) hβ
    have hsf := infinite_gSquarefree_gt_of_infinite_g_gt (1 - e) (e / 2) hα hβ hH
    apply hsf.mono
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    exact (Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ε ≤ 1 - e)).trans_lt hn.2
  · intro H ε hε
    apply (H ε hε).mono
    intro n hn
    have hg : (gSquarefree n : ℝ) ≤ (g n : ℝ) := by exact_mod_cast gSquarefree_le_g n
    exact hn.trans_le hg

#print axioms g_le_sum_gSquarefree_divisors
#print axioms exists_divisor_large_gSquarefree
#print axioms infinite_gSquarefree_gt_of_infinite_g_gt
#print axioms erdos_821_iff_squarefree_inputs

end Erdos821
