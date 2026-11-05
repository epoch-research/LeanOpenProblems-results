import Submission.FiberBounds
import Submission.PrimaryFibers

/-!
# Inactive target primes and a screened family of zero totient fibers

These are unconditional partial results, not a proof or disproof of Erdős 821.
This file does not import `Submission.Spec` or use either conjectural declaration.

A target prime `q` with `q - 1 ∤ n` cannot occur in any input of the fiber at `n`.
Its full target valuation must therefore be supplied by predecessors of selected
support primes. A unique admissible predecessor parent is mandatory, and deleting
mandatory support primes gives a sharper Boolean support bound.

For a target `2 ^ K * q` with an inactive odd prime `q`, every input decomposes
as `(2 ^ i * q + 1) * a`, with an actual prime first factor and `totient a = 2 ^ (K-i)`.
This gives a quadratic bound in `K`, using the previously proved pure-two bound.
Finally Dirichlet's theorem and a factorial congruence screen give infinitely
many zero fibers at each fixed two-adic valuation. An infinite family of zero
fibers is not the eventual upper bound needed to disprove the endpoint.
-/

namespace Erdos821ValuationCore

open Nat Finset

set_option maxHeartbeats 1000000

/-- An inactive target prime cannot divide a preimage. -/
theorem inactive_prime_not_dvd_input {m n q : ℕ}
    (hm : Nat.totient m = n) (hq : q.Prime) (hinactive : ¬ q - 1 ∣ n) :
    ¬ q ∣ m := by
  intro hqm
  apply hinactive
  have h := Nat.totient_dvd_of_dvd hqm
  simpa only [Nat.totient_prime hq, hm] using h

/-- A target prime absent from the input must divide a selected predecessor. -/
theorem prime_predecessor_witness {m n q : ℕ}
    (hm : Nat.totient m = n) (hq : q.Prime) (hqn : q ∣ n) (hqm : ¬ q ∣ m) :
    ∃ p ∈ m.primeFactors, q ∣ p - 1 := by
  have hqquot : ¬ q ∣ m / Erdos821Aux.rad m := by
    intro h
    exact hqm (h.trans (Nat.div_dvd_of_dvd (Erdos821Aux.rad_dvd m)))
  have hqprod : q ∣ ∏ p ∈ m.primeFactors, (p - 1) := by
    have h := hqn
    rw [← hm, Erdos821Aux.totient_eq_div_rad_mul_totient_rad,
      Erdos821Aux.totient_rad] at h
    exact (hq.dvd_mul.mp h).resolve_left hqquot
  exact (hq.prime.dvd_finset_prod_iff (fun p : ℕ => p - 1)).mp hqprod

/-- Exact valuation conservation on inactive prime coordinates. -/
theorem inactive_prime_valuation {m n q : ℕ} (hn : 0 < n)
    (hm : Nat.totient m = n) (hq : q.Prime) (hinactive : ¬ q - 1 ∣ n) :
    n.factorization q = ∑ p ∈ m.primeFactors, (p - 1).factorization q := by
  have hmpos : 0 < m := Nat.totient_pos.mp (by rwa [hm])
  have hrpos : 0 < Erdos821Aux.rad m :=
    Nat.pos_of_ne_zero (Erdos821Aux.squarefree_rad m).ne_zero
  have hquotpos : 0 < m / Erdos821Aux.rad m :=
    Nat.div_pos (Nat.le_of_dvd hmpos (Erdos821Aux.rad_dvd m)) hrpos
  have hqquot : ¬ q ∣ m / Erdos821Aux.rad m := by
    intro h
    exact inactive_prime_not_dvd_input hm hq hinactive
      (h.trans (Nat.div_dvd_of_dvd (Erdos821Aux.rad_dvd m)))
  rw [← hm, Erdos821Aux.totient_eq_div_rad_mul_totient_rad,
    Nat.factorization_mul hquotpos.ne' (Nat.totient_pos.mpr hrpos).ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqquot, zero_add,
    Erdos821Aux.totient_rad]
  exact Nat.factorization_prod_apply (fun p hp =>
    (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).ne')

/-- A unique admissible parent of an inactive coordinate is in every support. -/
theorem forced_candidate_mem {m n q r : ℕ}
    (hm : Nat.totient m = n) (hq : q.Prime) (hqn : q ∣ n)
    (hinactive : ¬ q - 1 ∣ n)
    (hunique : ∀ p : ℕ, p.Prime → p - 1 ∣ n → q ∣ p - 1 → p = r) :
    r ∈ m.primeFactors := by
  obtain ⟨p, hp, hqp⟩ := prime_predecessor_witness hm hq hqn
    (inactive_prime_not_dvd_input hm hq hinactive)
  obtain ⟨hprime, hpred⟩ := Erdos821Aux.prime_factor_candidate hm hp
  rwa [hunique p hprime hpred hqp] at hp

/-- If an inactive target coordinate has no admissible parent, the fiber is empty. -/
theorem fiberCard_eq_zero_of_no_parent {n q : ℕ}
    (hq : q.Prime) (hqn : q ∣ n) (hinactive : ¬ q - 1 ∣ n)
    (hno : ∀ p : ℕ, p.Prime → p - 1 ∣ n → ¬ q ∣ p - 1) :
    Erdos821Aux.fiberCard n = 0 := by
  have hempty : {m : ℕ | Nat.totient m = n} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨p, hp, hqp⟩ := prime_predecessor_witness hm hq hqn
      (inactive_prime_not_dvd_input hm hq hinactive)
    obtain ⟨hprime, hpred⟩ := Erdos821Aux.prime_factor_candidate hm hp
    exact hno p hprime hpred hqp
  simp only [Erdos821Aux.fiberCard, hempty, Set.ncard_empty]

/-- Mandatory support primes carry no free Boolean entropy. -/
theorem fiberCard_le_two_pow_unforced (n : ℕ) (P R : Finset ℕ)
    (hcover : ∀ m : ℕ, Nat.totient m = n → m.primeFactors ⊆ P)
    (hforced : ∀ m : ℕ, Nat.totient m = n → R ⊆ m.primeFactors) :
    Erdos821Aux.fiberCard n ≤ 2 ^ (P \ R).card := by
  classical
  let F := (Erdos821Aux.totient_fiber_finite n).toFinset
  have hF : ∀ m ∈ F, Nat.totient m = n := by
    intro m hm
    exact (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite n)).mp hm
  have hcard : F.card = Erdos821Aux.fiberCard n :=
    (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite n)).symm
  have hinj : Set.InjOn (fun m : ℕ => m.primeFactors \ R) F := by
    intro a ha b hb hab
    apply Erdos821Aux.eq_of_primeFactors_eq_of_totient_eq
    · ext p
      by_cases hp : p ∈ R
      · exact iff_of_true (hforced a (hF a ha) hp) (hforced b (hF b hb) hp)
      · have h := Finset.ext_iff.mp hab p
        simpa only [Finset.mem_sdiff, hp, not_false_eq_true, and_true] using h
    · exact (hF a ha).trans (hF b hb).symm
  have hsubset : F.image (fun m : ℕ => m.primeFactors \ R) ⊆ (P \ R).powerset := by
    intro S hS
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_powerset.mpr
    exact Finset.sdiff_subset_sdiff (hcover m (hF m hm)) (Finset.Subset.refl R)
  calc
    Erdos821Aux.fiberCard n = F.card := hcard.symm
    _ = (F.image (fun m : ℕ => m.primeFactors \ R)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P \ R).powerset.card := Finset.card_le_card hsubset
    _ = 2 ^ (P \ R).card := Finset.card_powerset _

/-- The predecessor of a `q`-parent in a two-prime target has the required shape. -/
theorem predecessor_eq_pow_two_mul_q {p q K : ℕ} (hq : 0 < q)
    (hpred : p - 1 ∣ 2 ^ K * q) (hqp : q ∣ p - 1) :
    ∃ i ≤ K, p - 1 = 2 ^ i * q := by
  obtain ⟨d, hd⟩ := hqp
  have hdvd : d ∣ 2 ^ K := Nat.dvd_of_mul_dvd_mul_left hq (by
    simpa only [hd, Nat.mul_comm] using hpred)
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨i, hi, by simpa only [Nat.mul_comm] using hd⟩

/-- Exact decomposition of every input at a two-prime target with an inactive odd prime.
The displayed first factor is required to be an actual prime. -/
theorem two_pow_mul_prime_decomposition {m q K : ℕ}
    (hm : Nat.totient m = 2 ^ K * q) (hq : q.Prime) (hq2 : q ≠ 2)
    (hinactive : ¬ q - 1 ∣ 2 ^ K * q) :
    ∃ i a : ℕ, 1 ≤ i ∧ i ≤ K ∧ (2 ^ i * q + 1).Prime ∧
      Nat.totient a = 2 ^ (K - i) ∧ m = (2 ^ i * q + 1) * a := by
  obtain ⟨p, hpm, hqp⟩ := prime_predecessor_witness hm hq
    (Nat.dvd_mul_left q (2 ^ K)) (inactive_prime_not_dvd_input hm hq hinactive)
  obtain ⟨hp, hpredvd⟩ := Erdos821Aux.prime_factor_candidate hm hpm
  obtain ⟨i, hi, hpred⟩ := predecessor_eq_pow_two_mul_q hq.pos hpredvd hqp
  have hpow : 1 ≤ 2 ^ i := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) i)
  have hqp_le : q ≤ p - 1 := by
    rw [hpred]
    simpa only [one_mul] using Nat.mul_le_mul_right q hpow
  have hpgtq : q < p := by have := hp.two_le; omega
  have hp2 : p ≠ 2 := by have := hq.two_le; omega
  have hi1 : 1 ≤ i := by
    by_contra h
    have hi0 : i = 0 := by omega
    have h2 := (hp.even_sub_one hp2).two_dvd
    rw [hpred, hi0, pow_zero, one_mul] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2).symm
  have hpn : ¬ p ∣ 2 ^ K * q := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · have heq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h)
      exact hp2 heq
    · have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
      omega
  have hpdiv : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hp2ndvd : ¬ p ^ 2 ∣ m := by
    intro h
    have hphi : p ∣ Nat.totient (p ^ 2) := by
      rw [Nat.totient_prime_pow_succ hp 1]
      simp only [pow_one]
      exact Nat.dvd_mul_right _ _
    exact hpn (by simpa only [hm] using hphi.trans (Nat.totient_dvd_of_dvd h))
  have hcop : Nat.Coprime p (m / p) := hp.coprime_iff_not_dvd.mpr (by
    intro h
    apply hp2ndvd
    simpa only [pow_two] using Nat.mul_dvd_of_dvd_div hpdiv h)
  have hpval : p = 2 ^ i * q + 1 := by have := hp.one_lt; omega
  have hphi_eq : (2 ^ i * q) * Nat.totient (m / p) = 2 ^ K * q := by
    calc
      (2 ^ i * q) * Nat.totient (m / p) = (p - 1) * Nat.totient (m / p) := by
        rw [hpred]
      _ = Nat.totient (p * (m / p)) := by
        rw [Nat.totient_mul hcop, Nat.totient_prime hp]
      _ = 2 ^ K * q := by rw [Nat.mul_div_cancel' hpdiv, hm]
  have hphi_two : 2 ^ i * Nat.totient (m / p) = 2 ^ K :=
    Nat.eq_of_mul_eq_mul_right hq.pos (by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hphi_eq)
  have hphi_a : Nat.totient (m / p) = 2 ^ (K - i) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) i)
    calc
      2 ^ i * Nat.totient (m / p) = 2 ^ K := hphi_two
      _ = 2 ^ i * 2 ^ (K - i) := by
        simpa only [Nat.mul_comm] using (Nat.pow_sub_mul_pow 2 hi).symm
  refine ⟨i, m / p, hi1, hi, hpval ▸ hp, hphi_a, ?_⟩
  rw [← hpval]
  exact (Nat.mul_div_cancel' hpdiv).symm

/-- An odd prime does not divide a power of two. -/
theorem odd_prime_not_dvd_two_pow {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (J : ℕ) :
    ¬ q ∣ 2 ^ J := by
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))

/-- A shifted `q`-parent prime is coprime to every pure-two preimage. -/
theorem shifted_prime_coprime_of_totient_two_pow {q i J a : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hp : (2 ^ i * q + 1).Prime)
    (ha : Nat.totient a = 2 ^ J) : Nat.Coprime (2 ^ i * q + 1) a := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have hcost : 2 ^ i * q ∣ 2 ^ J := by
    simpa only [Nat.totient_prime hp, Nat.add_sub_cancel, ha] using
      Nat.totient_dvd_of_dvd h
  exact odd_prime_not_dvd_two_pow hq hq2 J ((Nat.dvd_mul_left q (2 ^ i)).trans hcost)

/-- The converse to the inactive-prime decomposition, with the prime gate retained. -/
theorem two_pow_mul_prime_preimage {q K i a : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hi : i ≤ K) (hp : (2 ^ i * q + 1).Prime)
    (ha : Nat.totient a = 2 ^ (K - i)) :
    Nat.totient ((2 ^ i * q + 1) * a) = 2 ^ K * q := by
  rw [Nat.totient_mul (shifted_prime_coprime_of_totient_two_pow hq hq2 hp ha),
    Nat.totient_prime hp, Nat.add_sub_cancel, ha]
  calc
    (2 ^ i * q) * 2 ^ (K - i) = (2 ^ (K - i) * 2 ^ i) * q := by ring
    _ = 2 ^ K * q := by rw [Nat.pow_sub_mul_pow 2 hi]

/-- Distinct predecessor costs yield disjoint pure-two extensions. -/
theorem eq_cost_of_shifted_prime_products {q K i j a b : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hpi : (2 ^ i * q + 1).Prime) (hpj : (2 ^ j * q + 1).Prime)
    (hb : Nat.totient b = 2 ^ (K - j))
    (hprod : (2 ^ i * q + 1) * a = (2 ^ j * q + 1) * b) : i = j := by
  have hdiv : 2 ^ i * q + 1 ∣ (2 ^ j * q + 1) * b := by
    rw [← hprod]
    exact Nat.dvd_mul_right _ _
  rcases hpi.dvd_mul.mp hdiv with h | h
  · have heq := (Nat.prime_dvd_prime_iff_eq hpi hpj).mp h
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact Nat.eq_of_mul_eq_mul_right hq.pos (Nat.add_right_cancel heq)
  · exact ((hpi.coprime_iff_not_dvd.mp
      (shifted_prime_coprime_of_totient_two_pow hq hq2 hpi hb)) h).elim

/-- Exact full-fiber convolution at an inactive odd target prime.
Primality of each shifted factor is explicit; it is not replaced by a sieve screen. -/
theorem fiberCard_two_pow_mul_prime_eq_sum {q K : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hinactive : ¬ q - 1 ∣ 2 ^ K * q) :
    Erdos821Aux.fiberCard (2 ^ K * q) =
      ∑ i ∈ Finset.Icc 1 K, if (2 ^ i * q + 1).Prime then
        Erdos821Aux.fiberCard (2 ^ (K - i)) else 0 := by
  classical
  let F := (Erdos821Aux.totient_fiber_finite (2 ^ K * q)).toFinset
  let I := (Finset.Icc 1 K).filter (fun i => (2 ^ i * q + 1).Prime)
  let T : ℕ → Finset ℕ := fun i =>
    ((Erdos821Aux.totient_fiber_finite (2 ^ (K - i))).toFinset).image
      (fun a => (2 ^ i * q + 1) * a)
  have hF : ∀ m ∈ F, Nat.totient m = 2 ^ K * q := by
    intro m hm
    exact (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite (2 ^ K * q))).mp hm
  have hFcard : F.card = Erdos821Aux.fiberCard (2 ^ K * q) :=
    (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite _)).symm
  have hTmem : ∀ i m : ℕ, m ∈ T i →
      ∃ a : ℕ, Nat.totient a = 2 ^ (K - i) ∧ (2 ^ i * q + 1) * a = m := by
    intro i m hm
    obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hm
    exact ⟨a, (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite _)).mp ha, ham⟩
  have hFeq : F = I.biUnion T := by
    apply Finset.Subset.antisymm
    · intro m hm
      obtain ⟨i, a, hi1, hiK, hp, ha, hma⟩ :=
        two_pow_mul_prime_decomposition (hF m hm) hq hq2 hinactive
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, hiK⟩, hp⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨a, (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite _)).mpr ha,
        hma.symm⟩
    · intro m hm
      obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨a, ha, ham⟩ := hTmem i m hmi
      obtain ⟨hiIcc, hpi⟩ := Finset.mem_filter.mp hi
      have hiK := (Finset.mem_Icc.mp hiIcc).2
      apply (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite _)).mpr
      rw [← ham]
      exact two_pow_mul_prime_preimage hq hq2 hiK hpi ha
  have hdisjoint : (I : Set ℕ).PairwiseDisjoint T := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro m hmi hmj
    obtain ⟨a, _, ham⟩ := hTmem i m hmi
    obtain ⟨b, hb, hbm⟩ := hTmem j m hmj
    have hi' : i ∈ Finset.Icc 1 K ∧ (2 ^ i * q + 1).Prime := by
      simpa only [I, Finset.mem_coe, Finset.mem_filter] using hi
    have hj' : j ∈ Finset.Icc 1 K ∧ (2 ^ j * q + 1).Prime := by
      simpa only [I, Finset.mem_coe, Finset.mem_filter] using hj
    exact hij (eq_cost_of_shifted_prime_products (K := K) (i := i) (j := j)
      hq hq2 hi'.2 hj'.2 hb (ham.trans hbm.symm))
  have hTcard : ∀ i : ℕ, (T i).card = Erdos821Aux.fiberCard (2 ^ (K - i)) := by
    intro i
    calc
      (T i).card = ((Erdos821Aux.totient_fiber_finite (2 ^ (K - i))).toFinset).card := by
        apply Finset.card_image_of_injective
        intro a b h
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h
      _ = Erdos821Aux.fiberCard (2 ^ (K - i)) :=
        (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite _)).symm
  calc
    Erdos821Aux.fiberCard (2 ^ K * q) = F.card := hFcard.symm
    _ = (I.biUnion T).card := congrArg Finset.card hFeq
    _ = ∑ i ∈ I, (T i).card := Finset.card_biUnion hdisjoint
    _ = ∑ i ∈ I, Erdos821Aux.fiberCard (2 ^ (K - i)) :=
      Finset.sum_congr rfl (fun i _ => hTcard i)
    _ = ∑ i ∈ Finset.Icc 1 K, if (2 ^ i * q + 1).Prime then
        Erdos821Aux.fiberCard (2 ^ (K - i)) else 0 := by
      dsimp only [I]
      exact Finset.sum_filter _ _

private theorem two_mul_sum_Icc_cost (K : ℕ) :
    2 * (∑ i ∈ Finset.Icc 1 K, (K - i + 2)) = K * (K + 3) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hshift : (∑ i ∈ Finset.Icc 1 K, (K + 1 - i + 2)) =
        (∑ i ∈ Finset.Icc 1 K, (K - i + 2)) + K := by
      calc
        (∑ i ∈ Finset.Icc 1 K, (K + 1 - i + 2)) =
            ∑ i ∈ Finset.Icc 1 K, ((K - i + 2) + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiK := (Finset.mem_Icc.mp hi).2
          omega
        _ = (∑ i ∈ Finset.Icc 1 K, (K - i + 2)) + K := by
          rw [Finset.sum_add_distrib]
          simp
    change 2 * (∑ i ∈ Finset.Icc 1 (K + 1), (K + 1 - i + 2)) =
      (K + 1) * (K + 1 + 3)
    rw [Finset.sum_Icc_succ_top (by omega), hshift]
    simp only [Nat.sub_self, zero_add]
    nlinarith [ih]

/-- Sharp quadratic cap coming from the exact convolution and the pure-two bound. -/
theorem fiberCard_two_pow_mul_prime_le_sharp {q K : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hinactive : ¬ q - 1 ∣ 2 ^ K * q) :
    Erdos821Aux.fiberCard (2 ^ K * q) ≤ K * (K + 3) / 2 := by
  classical
  have hsum : (∑ i ∈ Finset.Icc 1 K,
      if (2 ^ i * q + 1).Prime then Erdos821Aux.fiberCard (2 ^ (K - i)) else 0) ≤
      ∑ i ∈ Finset.Icc 1 K, (K - i + 2) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact Erdos821Fresh.fiberCard_two_pow_le _
    · exact Nat.zero_le _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).mpr
  calc
    Erdos821Aux.fiberCard (2 ^ K * q) * 2 =
        2 * (∑ i ∈ Finset.Icc 1 K, if (2 ^ i * q + 1).Prime then
          Erdos821Aux.fiberCard (2 ^ (K - i)) else 0) := by
      rw [fiberCard_two_pow_mul_prime_eq_sum hq hq2 hinactive, Nat.mul_comm]
    _ ≤ 2 * (∑ i ∈ Finset.Icc 1 K, (K - i + 2)) := Nat.mul_le_mul_left 2 hsum
    _ = K * (K + 3) := two_mul_sum_Icc_cost K

/-- A uniform quadratic upper bound for the inactive one-odd-prime family. -/
theorem fiberCard_two_pow_mul_prime_le {q K : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hinactive : ¬ q - 1 ∣ 2 ^ K * q) :
    Erdos821Aux.fiberCard (2 ^ K * q) ≤ K * (K + 2) := by
  classical
  let F := (Erdos821Aux.totient_fiber_finite (2 ^ K * q)).toFinset
  let T : ℕ → Finset ℕ := fun i =>

    ((Erdos821Aux.totient_fiber_finite (2 ^ (K - i))).toFinset).image
      (fun a => (2 ^ i * q + 1) * a)
  have hF : ∀ m ∈ F, Nat.totient m = 2 ^ K * q := by
    intro m hm
    exact (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite (2 ^ K * q))).mp hm
  have hcard : F.card = Erdos821Aux.fiberCard (2 ^ K * q) :=
    (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite (2 ^ K * q))).symm
  have hsubset : F ⊆ (Finset.Icc 1 K).biUnion T := by
    intro m hm
    obtain ⟨i, a, hi1, hiK, _, ha, hma⟩ :=
      two_pow_mul_prime_decomposition (hF m hm) hq hq2 hinactive
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_Icc.mpr ⟨hi1, hiK⟩, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨a, (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite _)).mpr ha,
      hma.symm⟩
  have hT : ∀ i : ℕ, (T i).card ≤ K + 2 := by
    intro i
    calc
      (T i).card ≤ ((Erdos821Aux.totient_fiber_finite (2 ^ (K - i))).toFinset).card :=
        Finset.card_image_le
      _ = Erdos821Aux.fiberCard (2 ^ (K - i)) :=
        (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite _)).symm
      _ ≤ (K - i) + 2 := Erdos821Fresh.fiberCard_two_pow_le _
      _ ≤ K + 2 := Nat.add_le_add_right (Nat.sub_le _ _) _
  calc
    Erdos821Aux.fiberCard (2 ^ K * q) = F.card := hcard.symm
    _ ≤ ((Finset.Icc 1 K).biUnion T).card := Finset.card_le_card hsubset
    _ ≤ ∑ i ∈ Finset.Icc 1 K, (T i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.Icc 1 K, (K + 2) := Finset.sum_le_sum (fun i _ => hT i)
    _ = K * (K + 2) := by simp

/-- An odd target other than one has an empty fiber. -/
theorem fiberCard_eq_zero_of_odd {n : ℕ} (hn : Odd n) (hn1 : n ≠ 1) :
    Erdos821Aux.fiberCard n = 0 := by
  have hempty : {m : ℕ | Nat.totient m = n} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hphi : Odd (Nat.totient m) := hm.symm ▸ hn
    exact hn1 (hm.symm.trans (Nat.odd_totient_iff_eq_one.mp hphi))
  simp only [Erdos821Aux.fiberCard, hempty, Set.ncard_empty]

/-- A factorial congruence screen blocks every possible predecessor parent.
This asserts zero fibers for specified targets, not the negation of Erdős 821. -/
theorem screened_fiberCard_eq_zero (K : ℕ) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hscreen : (2 ^ K + 1).factorial ∣ q - 1) :
    Erdos821Aux.fiberCard (2 ^ K * q) = 0 := by
  by_cases hK0 : K = 0
  · simp only [hK0, pow_zero, one_mul]
    exact fiberCard_eq_zero_of_odd (hq.odd_of_ne_two (by omega)) hq.ne_one
  have hK1 : 1 ≤ K := by omega
  have h2pow : 2 ≤ 2 ^ K := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hK1
  have h3D : 3 ∣ (2 ^ K + 1).factorial :=
    Nat.dvd_factorial (by decide) (by omega)
  have h3q : 3 ∣ q - 1 := h3D.trans hscreen
  have h3n : ¬ 3 ∣ 2 ^ K * q := by
    intro h
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h with h | h
    · have h32 := (by decide : Nat.Prime 3).dvd_of_dvd_pow h
      norm_num at h32
    · have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hq).mp h
      omega
  have hinactive : ¬ q - 1 ∣ 2 ^ K * q := fun h => h3n (h3q.trans h)
  apply fiberCard_eq_zero_of_no_parent hq (Nat.dvd_mul_left q (2 ^ K)) hinactive
  intro p hp hpredvd hqp
  obtain ⟨i, hi, hpred⟩ := predecessor_eq_pow_two_mul_q hq.pos hpredvd hqp
  have hpow : 0 < 2 ^ i := pow_pos (by decide) _
  have hqone : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hpval : p = 2 ^ i * q + 1 := by have := hp.one_lt; omega
  have hdiD : 2 ^ i + 1 ∣ (2 ^ K + 1).factorial :=
    Nat.dvd_factorial (by omega)
      (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hi) 1)
  have hdiq : 2 ^ i + 1 ∣ q - 1 := hdiD.trans hscreen
  have hpval' : p = 2 ^ i * (q - 1) + (2 ^ i + 1) := by
    nlinarith [hpval, hqone]
  have hdip : 2 ^ i + 1 ∣ p := by
    rw [hpval']
    exact dvd_add (Nat.dvd_mul_left_of_dvd hdiq (2 ^ i)) (dvd_refl _)
  rcases hp.eq_one_or_self_of_dvd (2 ^ i + 1) hdip with h | h
  · omega
  · nlinarith [hpval]

/-- At every two-adic valuation there are infinitely many zero-fiber targets.
The construction uses actual primes supplied by Dirichlet's theorem. -/
theorem infinite_zero_fibers_at_two_adic_valuation (K : ℕ) :
    {n : ℕ | 0 < n ∧ n.factorization 2 = K ∧ Erdos821Aux.fiberCard n = 0}.Infinite := by
  classical
  let D := (2 ^ K + 1).factorial
  let P : Set ℕ := {q : ℕ | q.Prime ∧ q ≡ 1 [MOD D]} \ Set.Iic 3
  have hP : P.Infinite :=
    (Nat.infinite_setOf_prime_and_modEq (Nat.factorial_ne_zero _)
      (Nat.coprime_one_left D)).diff (Set.finite_Iic 3)
  have hinj : Set.InjOn (fun q : ℕ => 2 ^ K * q) P := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) K) h
  apply (Set.Infinite.image hinj hP).mono
  rintro n ⟨q, hqP, rfl⟩
  obtain ⟨⟨hq, hmod⟩, hq3⟩ := hqP
  have hqgt3 : 3 < q := lt_of_not_ge hq3
  have hscreen : (2 ^ K + 1).factorial ∣ q - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mp hmod.symm
  have h2q : ¬ 2 ∣ q := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h
    omega
  refine ⟨Nat.mul_pos (pow_pos (by decide) _) hq.pos, ?_,
    screened_fiberCard_eq_zero K hq hqgt3 hscreen⟩
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hq.ne_zero,
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd h2q, add_zero]

/-- The rational valuation vector of a candidate predecessor. -/
def predecessorVector (p : ℕ) : ℕ → ℚ := fun q => ((p - 1).factorization q : ℚ)

/-- Linear combinations cannot introduce a new prime-factor coordinate. -/
theorem predecessor_support_subset_of_span (P B : Finset ℕ)
    (hspan : ∀ p ∈ P, predecessorVector p ∈
      Submodule.span ℚ (predecessorVector '' (B : Set ℕ))) :
    ∀ p ∈ P, (p - 1).primeFactors ⊆ B.biUnion (fun b => (b - 1).primeFactors) := by
  classical
  intro p hp q hq
  by_contra hqnot
  let e : (ℕ → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj q
  have hle : Submodule.span ℚ (predecessorVector '' (B : Set ℕ)) ≤ e.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨b, hb, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hqb : q ∉ (b - 1).primeFactors := by
      intro h
      exact hqnot (Finset.mem_biUnion.mpr ⟨b, hb, h⟩)
    have hz : (b - 1).factorization q = 0 := Finsupp.notMem_support_iff.mp (by
      simpa only [Nat.support_factorization] using hqb)
    change ((b - 1).factorization q : ℚ) = 0
    rw [hz, Nat.cast_zero]
  have hz := LinearMap.mem_ker.mp (hle (hspan p hp))
  change ((p - 1).factorization q : ℚ) = 0 at hz
  have hneq : (p - 1).factorization q ≠ 0 := Finsupp.mem_support_iff.mp (by
    simpa only [Nat.support_factorization] using hq)
  exact hneq (by exact_mod_cast hz)

end Erdos821ValuationCore

#print axioms Erdos821ValuationCore.inactive_prime_not_dvd_input
#print axioms Erdos821ValuationCore.prime_predecessor_witness
#print axioms Erdos821ValuationCore.inactive_prime_valuation
#print axioms Erdos821ValuationCore.forced_candidate_mem
#print axioms Erdos821ValuationCore.fiberCard_eq_zero_of_no_parent
#print axioms Erdos821ValuationCore.fiberCard_le_two_pow_unforced
#print axioms Erdos821ValuationCore.predecessor_eq_pow_two_mul_q
#print axioms Erdos821ValuationCore.two_pow_mul_prime_decomposition
#print axioms Erdos821ValuationCore.fiberCard_two_pow_mul_prime_le
#print axioms Erdos821ValuationCore.fiberCard_eq_zero_of_odd
#print axioms Erdos821ValuationCore.screened_fiberCard_eq_zero
#print axioms Erdos821ValuationCore.infinite_zero_fibers_at_two_adic_valuation

#print axioms Erdos821ValuationCore.odd_prime_not_dvd_two_pow
#print axioms Erdos821ValuationCore.shifted_prime_coprime_of_totient_two_pow
#print axioms Erdos821ValuationCore.two_pow_mul_prime_preimage
#print axioms Erdos821ValuationCore.eq_cost_of_shifted_prime_products
#print axioms Erdos821ValuationCore.fiberCard_two_pow_mul_prime_eq_sum

#print axioms Erdos821ValuationCore.fiberCard_two_pow_mul_prime_le_sharp
#print axioms Erdos821ValuationCore.predecessorVector
#print axioms Erdos821ValuationCore.predecessor_support_subset_of_span
