import FormalConjecturesUtil
import Submission.FiniteBrun
import Submission.PeriodicDensity

/-! Chinese-remainder counting and a finite Brun sieve for prime moduli.
This supplies finite counting errors, not signed prime-factor cancellation. -/

namespace Erdos371ResidueSieve

open Finset Erdos371FiniteBrun

attribute [local instance] Classical.propDecidable

noncomputable def modulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

lemma modulus_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : 0 < modulus s :=
  Finset.prod_pos (fun p hp => (hs p hp).pos)

lemma modEq_modulus {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {n m : ℕ}
    (h : ∀ p ∈ s, Nat.ModEq p n m) : Nat.ModEq (modulus s) n m := by
  induction s using Finset.induction_on with
  | empty => change n % 1 = m % 1; omega
  | @insert p s hp ih =>
    have hsp : p.Prime := hs p (Finset.mem_insert_self _ _)
    have hss : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (modulus s) := Nat.coprime_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes hsp (hss q hq)).mpr (fun he => hp (he ▸ hq)))
    rw [modulus, Finset.prod_insert hp]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨h p (Finset.mem_insert_self _ _), ih hss (fun q hq => h q (Finset.mem_insert_of_mem hq))⟩

noncomputable def residueEvent (R : ℕ → Finset ℕ) (p n : ℕ) : Prop := n % p ∈ R p

noncomputable def roots (s : Finset ℕ) (R : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range (modulus s)).filter fun n => ∀ p ∈ s, residueEvent R p n

/-- CRT counts the allowed residue combinations exactly over one full period. -/
lemma roots_card {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ s, R p ⊆ Finset.range p) :
    (roots s R).card = ∏ p ∈ s, (R p).card := by
  rw [← Finset.card_pi]
  apply Finset.card_bij (fun n (_ : n ∈ roots s R) p (_ : p ∈ s) => n % p)
  · intro n hn
    apply Finset.mem_pi.mpr
    intro p hp
    exact (Finset.mem_filter.mp hn).2 p hp
  · intro n hn m hm he
    have hn0 := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hm0 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    have hh := modEq_modulus hs (n := n) (m := m) (fun p hp => by
      exact congrArg (fun f : (p : ℕ) → p ∈ s → ℕ => f p hp) he)
    change n % modulus s = m % modulus s at hh
    simpa [Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hm0] using hh
  · intro f hf
    let a : ℕ → ℕ := fun p => if hp : p ∈ s then f p hp else 0
    have hs0 : ∀ p ∈ s, id p ≠ 0 := fun p hp => (hs p hp).ne_zero
    have hcop : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) := by
      intro p hp q hq hpq
      exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
    let n := Nat.chineseRemainderOfFinset a id s hs0 hcop
    have hn0 : (n:ℕ) < modulus s := Nat.chineseRemainderOfFinset_lt_prod a id hs0 hcop
    have hnmod (p : ℕ) (hp : p ∈ s) : (n:ℕ) % p = f p hp := by
      have hh := n.property p hp
      have hfR := Finset.mem_pi.mp hf p hp
      have hfp : f p hp < p := Finset.mem_range.mp (hR p hp hfR)
      change (n:ℕ) % p = a p % p at hh
      simpa [a, hp, Nat.mod_eq_of_lt hfp] using hh
    have hn : (n:ℕ) ∈ roots s R := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hn0, ?_⟩
      intro p hp
      change (n:ℕ) % p ∈ R p
      rw [hnmod p hp]
      exact Finset.mem_pi.mp hf p hp
    refine ⟨n, hn, ?_⟩
    funext p hp
    exact hnmod p hp

lemma joint_periodic (s : Finset ℕ) (R : ℕ → Finset ℕ) (n : ℕ) :
    (∀ p ∈ s, residueEvent R p (n + modulus s)) ↔ ∀ p ∈ s, residueEvent R p n := by
  have hm (p : ℕ) (hp : p ∈ s) : (n+modulus s) % p = n % p := by
    have hd : p ∣ modulus s := Finset.dvd_prod_of_mem id hp
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
  simp only [residueEvent]
  exact forall_congr' (fun p => forall_congr' (fun hp => by rw [hm p hp]))

/-- For any periodic predicate, the full-period root count also bounds the
absolute counting error on an initial interval. -/
lemma periodic_count_error (b : ℕ → Prop) [DecidablePred b] {Q : ℕ} (hQ : 0 < Q)
    (hb : ∀ n, b (n+Q) ↔ b n) (N : ℕ) :
    |(((Finset.range N).filter b).card:ℝ) -
      (N:ℝ)/Q * ((Finset.range Q).filter b).card| ≤ ((Finset.range Q).filter b).card := by
  have hh := Erdos371Exploration.periodic_count_remainder b hb N
  have hr : ((Finset.range (N%Q)).filter b).card ≤ ((Finset.range Q).filter b).card :=
    Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.range_mono (Nat.mod_lt N hQ).le))
  have hrem : (0:ℝ) ≤ ((N%Q:ℕ):ℝ) := Nat.cast_nonneg _
  have hremle : ((N%Q:ℕ):ℝ) ≤ Q := Nat.cast_le.mpr (Nat.mod_lt N hQ).le
  have hq : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hd : (Q:ℝ)*(N/Q:ℕ) + (N%Q:ℕ) = N := by exact_mod_cast Nat.div_add_mod N Q
  have hfrac : (N:ℝ)/Q = (N/Q:ℕ) + (N%Q:ℕ)/(Q:ℝ) := by
    apply (div_eq_iff hq.ne').mpr
    field_simp
    nlinarith
  have hrat0 : (0:ℝ) ≤ (N%Q:ℕ)/(Q:ℝ) := by positivity
  have hrat1 : ((N%Q:ℕ):ℝ)/(Q:ℝ) ≤ 1 := (div_le_iff₀ hq).mpr (by simpa using hremle)
  have hC0 : (0:ℝ) ≤ ((Finset.range Q).filter b).card := Nat.cast_nonneg _
  have hD0 : (0:ℝ) ≤ ((Finset.range (N%Q)).filter b).card := Nat.cast_nonneg _
  have hDle : (((Finset.range (N%Q)).filter b).card:ℝ) ≤ ((Finset.range Q).filter b).card :=
    Nat.cast_le.mpr hr
  rw [hh, hfrac, abs_le]
  push_cast
  constructor <;> nlinarith

noncomputable def localDensity (R : ℕ → Finset ℕ) (p : ℕ) : ℝ := (R p).card / (p:ℝ)

lemma joint_count_error {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ s, R p ⊆ Finset.range p) (N : ℕ) :
    |jointCount (Finset.range N) (residueEvent R) s -
      (N:ℝ)*(∏ p ∈ s, localDensity R p)| ≤ ∏ p ∈ s, ((R p).card:ℝ) := by
  have hh := periodic_count_error (fun n => ∀ p ∈ s, residueEvent R p n)
    (modulus_pos hs) (joint_periodic s R) N
  change |jointCount (Finset.range N) (residueEvent R) s - (N:ℝ)/modulus s * (roots s R).card| ≤
    (roots s R).card at hh
  rw [roots_card hs R hR] at hh
  push_cast at hh
  have he : (∏ p ∈ s, localDensity R p) = (∏ p ∈ s, ((R p).card:ℝ))/(modulus s:ℝ) := by
    simp [localDensity, modulus, Finset.prod_div_distrib]
  rw [he]
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hh

/-- An unconditional finite upper sieve for sets of at most two forbidden
residues at each prime modulus. -/
theorem residue_sieve_upper {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (R : ℕ → Finset ℕ) (hR : ∀ p ∈ s, R p ⊆ Finset.range p)
    (hR2 : ∀ p ∈ s, (R p).card ≤ 2) (N : ℕ)
    {r : ℕ} (hr : 0 < r) (hlarge : 4*(∑ p ∈ s, localDensity R p)^2 ≤ (r:ℝ)) :
    (survivors (Finset.range N) s (residueEvent R)).card ≤
      (N:ℝ)*((∏ p ∈ s, (1-localDensity R p)) + (1/4:ℝ)^r) +
        (2*r+1:ℕ) * (2*(max 1 s.card):ℝ)^(2*r) := by
  have hν : ∀ p ∈ s, 0 ≤ localDensity R p ∧ localDensity R p ≤ 1 := by
    intro p hp
    have hp' : (0:ℝ) < p := Nat.cast_pos.mpr (hs p hp).pos
    refine ⟨by unfold localDensity; positivity, ?_⟩
    unfold localDensity
    apply (div_le_iff₀ hp').mpr
    have hh : (R p).card ≤ p := by simpa using Finset.card_le_card (hR p hp)
    simpa using (Nat.cast_le.mpr hh : ((R p).card:ℝ) ≤ p)
  apply finite_brun_upper_two_roots (Finset.range N) s (residueEvent R)
    (localDensity R) N hν (Nat.cast_nonneg _) hr hlarge
  intro t hts htcard
  have he := joint_count_error (fun p hp => hs p (hts hp)) R (fun p hp => hR p (hts hp)) N
  apply he.trans
  calc
    _ ≤ ∏ _p ∈ t, (2:ℝ) := Finset.prod_le_prod (fun _ _ => by positivity)
      (fun p hp => by exact_mod_cast hR2 p (hts hp))
    _ = _ := by simp

end Erdos371ResidueSieve

#print axioms Erdos371ResidueSieve.roots_card
#print axioms Erdos371ResidueSieve.residue_sieve_upper
