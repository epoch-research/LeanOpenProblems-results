import FormalConjecturesUtil
import Submission.FactorwisePairingObstruction
import Submission.MonotoneAdditiveReversal

/-! Threshold-count dominance gives a termwise factor certificate. Combining
this with the product-gap obstruction rules out dense injective pairings
based on simultaneous dominance at every prime threshold. -/

namespace Erdos371ThresholdPairingObstruction

open Finset Filter Erdos371FactorwisePairingObstruction
open scoped Topology

def tailCount (l : List ℕ) (t : ℕ) : ℕ :=
  (l.filter fun a => decide (t ≤ a)).length

@[simp] lemma tailCount_nil (t : ℕ) : tailCount [] t = 0 := by simp [tailCount]

lemma tailCount_cons (a : ℕ) (l : List ℕ) (t : ℕ) :
    tailCount (a::l) t = (if t ≤ a then 1 else 0)+tailCount l t := by
  by_cases h : t ≤ a <;> simp [tailCount,h,Nat.add_comm]

lemma tailCount_zero {l : List ℕ} {t : ℕ} (h : ∀ a ∈ l, a < t) : tailCount l t = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [tailCount_cons, if_neg (by have := h a (by simp); omega), zero_add]
      exact ih (fun b hb => h b (by simp [hb]))

lemma ones_coupling (v : List ℕ) (hv : ∀ a ∈ v, 0 < a) :
    ∃ b : List ℕ, List.Forall₂ (fun a b => 0 < b ∧ b ≤ a) v b ∧ b.prod = 1 := by
  induction v with
  | nil => exact ⟨[], List.Forall₂.nil, rfl⟩
  | cons a v ih =>
      obtain ⟨b,hb,hprod⟩ := ih (fun c hc => hv c (by simp [hc]))
      refine ⟨1::b,List.Forall₂.cons ⟨by omega, hv a (by simp)⟩ hb,?_⟩
      simpa using hprod

lemma sorted_coupling {u v : List ℕ}
    (hu : u.Pairwise (· ≥ ·)) (hv : v.Pairwise (· ≥ ·))
    (hup : ∀ a ∈ u, 0 < a) (hvp : ∀ a ∈ v, 0 < a)
    (h : ∀ t, tailCount u t ≤ tailCount v t) :
    ∃ b : List ℕ, List.Forall₂ (fun a b => 0 < b ∧ b ≤ a) v b ∧ b.prod = u.prod := by
  induction u generalizing v with
  | nil => exact ones_coupling v hvp
  | cons a u ih =>
      cases v with
      | nil =>
          have hh := h a
          rw [tailCount_cons, if_pos le_rfl, tailCount_nil] at hh
          omega
      | cons c v =>
          have hau := (List.pairwise_cons.mp hu).1
          have hcv := (List.pairwise_cons.mp hv).1
          have hac : a ≤ c := by
            by_contra hlt
            have he : tailCount (c::v) a = 0 := tailCount_zero (by
              intro d hd
              rcases List.mem_cons.mp hd with rfl | hd
              · omega
              · have := hcv d hd; omega)
            have hh := h a
            rw [he,tailCount_cons,if_pos le_rfl] at hh
            omega
          have ht : ∀ t, tailCount u t ≤ tailCount v t := by
            intro t
            by_cases hta : t ≤ a
            · have htc : t ≤ c := hta.trans hac
              have hh := h t
              rw [tailCount_cons,tailCount_cons,if_pos hta,if_pos htc] at hh
              omega
            · rw [tailCount_zero (by intro d hd; have := hau d hd; omega)]
              exact Nat.zero_le _
          obtain ⟨b,hb,hprod⟩ := ih (List.pairwise_cons.mp hu).2 (List.pairwise_cons.mp hv).2
            (fun d hd => hup d (by simp [hd])) (fun d hd => hvp d (by simp [hd])) ht
          exact ⟨a::b,List.Forall₂.cons ⟨hup a (by simp),hac⟩ hb,by simp [hprod]⟩

/-- A first-order dominance statement for finite integer multisets. -/
theorem coupling_of_tail_counts {u v : List ℕ}
    (hu : ∀ a ∈ u, 0 < a) (hv : ∀ a ∈ v, 0 < a)
    (h : ∀ t, tailCount u t ≤ tailCount v t) :
    ∃ b : List ℕ, List.Forall₂ (fun a b => 0 < b ∧ b ≤ a) v b ∧ b.prod = u.prod := by
  let us := u.insertionSort (· ≥ ·)
  let vs := v.insertionSort (· ≥ ·)
  have hup : us.Perm u := List.perm_insertionSort _ _
  have hvp : vs.Perm v := List.perm_insertionSort _ _
  have ht : ∀ t, tailCount us t ≤ tailCount vs t := by
    intro t
    have he₁ : tailCount us t = tailCount u t := (hup.filter _).length_eq
    have he₂ : tailCount vs t = tailCount v t := (hvp.filter _).length_eq
    rw [he₁,he₂]
    exact h t
  obtain ⟨b,hb,hprod⟩ := sorted_coupling
    (List.pairwise_insertionSort _ u) (List.pairwise_insertionSort _ v)
    (fun a ha => hu a (hup.mem_iff.mp ha)) (fun a ha => hv a (hvp.mem_iff.mp ha)) ht
  obtain ⟨c,hc,hcb⟩ := List.perm_comp_forall₂ hvp.symm hb
  exact ⟨c,hc,hcb.prod_eq.trans (hprod.trans hup.prod_eq)⟩

def threshold (t n : ℕ) : ℕ := tailCount n.primeFactorsList t

def compatible (n m : ℕ) : Prop :=
  ∀ t, threshold t n+threshold t m ≤ threshold t (n+1)+threshold t (m+1)

lemma compatible_factorPairing {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : compatible n m) : factorPairing n m := by
  have hp (k : ℕ) : ∀ a ∈ k.primeFactorsList, 0 < a :=
    fun a ha => (Nat.prime_of_mem_primeFactorsList ha).pos
  obtain ⟨b,hb,hprod⟩ := coupling_of_tail_counts
    (u := n.primeFactorsList ++ m.primeFactorsList)
    (v := (n+1).primeFactorsList ++ (m+1).primeFactorsList)
    (by intro a ha; rcases List.mem_append.mp ha with ha | ha; exact hp n a ha; exact hp m a ha)
    (by intro a ha; rcases List.mem_append.mp ha with ha | ha; exact hp (n+1) a ha; exact hp (m+1) a ha)
    (by intro t; simpa [tailCount,List.filter_append,threshold] using h t)
  refine ⟨b,hb,?_⟩
  simpa only [List.prod_append,Nat.prod_primeFactorsList hn.ne',Nat.prod_primeFactorsList hm.ne'] using hprod

/-- Arbitrary cutoff-dependent injective pairings by simultaneous threshold
dominance cannot cover a positive-density population. -/
theorem threshold_matching_proportion_tendsto_zero (S : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ)
    (hS : ∀ N, S N ⊆ range N) (hf : ∀ N n, n ∈ S N → f N n < N)
    (hinj : ∀ N, Set.InjOn (f N) (S N))
    (hpair : ∀ N n, n ∈ S N → 0 < n ∧ 0 < f N n ∧ compatible n (f N n)) :
    Tendsto (fun N : ℕ => ((S N).card : ℝ)/N) atTop (𝓝 0) := by
  apply matching_proportion_tendsto_zero S f hS hf hinj
  intro N n hn
  obtain ⟨hpos,hpos',hcomp⟩ := hpair N n hn
  exact compatible_factorPairing hpos hpos' hcomp


lemma threshold_mul (t : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    threshold t (a*b) = threshold t a+threshold t b := by
  have hp := ((Nat.perm_primeFactorsList_mul ha hb).filter (fun p => decide (t ≤ p))).length_eq
  simpa only [threshold,tailCount,List.filter_append,List.length_append] using hp

def stepHeight (t B n : ℕ) : ℕ := n.primeFactorsList.length+B*threshold t n

lemma stepHeight_mul (t B : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    stepHeight t B (a*b) = stepHeight t B a+stepHeight t B b := by
  have hp := (Nat.perm_primeFactorsList_mul ha hb).length_eq
  simp only [List.length_append] at hp
  unfold stepHeight
  rw [hp,threshold_mul t ha hb]
  ring

lemma stepHeight_prime (t B : ℕ) {p : ℕ} (hp : p.Prime) :
    stepHeight t B p = 1+B*(if t ≤ p then 1 else 0) := by
  by_cases htp : t ≤ p <;> simp [stepHeight,threshold,tailCount,Nat.primeFactorsList_prime hp,htp]

lemma stepHeight_admissible (N t B : ℕ) :
    Erdos371MonotoneAdditiveReversal.admissible N (fun n => (stepHeight t B n : ℝ)) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [stepHeight,threshold,tailCount]
  · intro a b ha hb
    dsimp only
    rw [stepHeight_mul t B ha hb,Nat.cast_add]
  · intro p hp hpN
    dsimp only
    rw [stepHeight_prime t B hp]
    positivity
  · intro p q hp hq hpq hqN
    apply Nat.cast_le.mpr
    rw [stepHeight_prime t B hp,stepHeight_prime t B hq]
    by_cases htp : t ≤ p
    · simp [htp,htp.trans hpq]
    · simp [htp]

/-- The common equal-coefficient certificate used in the proposed pairing:
the two increments have nonnegative sum for every admissible prime weight. -/
def sumCompatible (N n m : ℕ) : Prop :=
  ∀ f : ℕ → ℝ, Erdos371MonotoneAdditiveReversal.admissible N f →
    f n+f m ≤ f (n+1)+f (m+1)

lemma sumCompatible_implies_threshold {N n m : ℕ} (h : sumCompatible N n m) :
    compatible n m := by
  intro t
  let B := (n+1).primeFactorsList.length+(m+1).primeFactorsList.length+1
  have hh := h (fun k => (stepHeight t B k : ℝ)) (stepHeight_admissible N t B)
  dsimp only at hh
  change (stepHeight t B n : ℝ)+(stepHeight t B m : ℝ) ≤
    (stepHeight t B (n+1) : ℝ)+(stepHeight t B (m+1) : ℝ) at hh
  have hh' : stepHeight t B n+stepHeight t B m ≤
      stepHeight t B (n+1)+stepHeight t B (m+1) := by exact_mod_cast hh
  unfold stepHeight at hh'
  by_contra hlt
  have ht : threshold t (n+1)+threshold t (m+1)+1 ≤ threshold t n+threshold t m := by omega
  have hm := Nat.mul_le_mul_left B ht
  dsimp only [B] at hh' hm
  nlinarith

/-- Hence even cutoff-dependent equal-coefficient sum certificates, valid
uniformly over the admissible class, can match only o(N) inputs. -/
theorem uniform_sum_matching_proportion_tendsto_zero (S : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ)
    (hS : ∀ N, S N ⊆ range N) (hf : ∀ N n, n ∈ S N → f N n < N)
    (hinj : ∀ N, Set.InjOn (f N) (S N))
    (hpair : ∀ N n, n ∈ S N → 0 < n ∧ 0 < f N n ∧ sumCompatible N n (f N n)) :
    Tendsto (fun N : ℕ => ((S N).card : ℝ)/N) atTop (𝓝 0) := by
  apply threshold_matching_proportion_tendsto_zero S f hS hf hinj
  intro N n hn
  obtain ⟨hpos,hpos',hcomp⟩ := hpair N n hn
  exact ⟨hpos,hpos',sumCompatible_implies_threshold hcomp⟩

end Erdos371ThresholdPairingObstruction

#print axioms Erdos371ThresholdPairingObstruction.coupling_of_tail_counts
#print axioms Erdos371ThresholdPairingObstruction.threshold_matching_proportion_tendsto_zero

#print axioms Erdos371ThresholdPairingObstruction.uniform_sum_matching_proportion_tendsto_zero
