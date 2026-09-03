import FormalConjecturesUtil
import Submission.CoreGraphReversal
import Submission.PeriodicDensity

/-! A bounded binary digit-reversal height with biased ascents and exact
invariance under doubling. This is a model for testing a proposed strategy,
not the largest-prime-factor function and not a disproof of Erdős 371.
No ratio-separation theorem for a power amplification is asserted here. -/

namespace Erdos371BinaryReversalHeight

open Finset Filter Erdos371CoreGraphReversal
open scoped Topology

/-- Reverse the binary digits across the radix point. -/
def rev : ℕ → ℚ :=
  Nat.evenOddRec 0 (fun _ x => x/2) (fun _ x => (1+x)/2)

@[simp] lemma rev_zero : rev 0=0 := by simp [rev]
@[simp] lemma rev_even (n : ℕ) : rev (2*n)=rev n/2 := by
  unfold rev
  rw [Nat.evenOddRec_even _ _ _ (by norm_num)]
@[simp] lemma rev_odd (n : ℕ) : rev (2*n+1)=(1+rev n)/2 := by
  unfold rev
  rw [Nat.evenOddRec_odd _ _ _ (by norm_num)]

lemma rev_bounds (n : ℕ) : 0≤rev n ∧ rev n<1 := by
  induction n using Nat.evenOddRec with
  | h0 => norm_num
  | h_even n ih => rw [rev_even]; constructor <;> linarith [ih.1,ih.2]
  | h_odd n ih => rw [rev_odd]; constructor <;> linarith [ih.1,ih.2]

lemma rev_pos {n : ℕ} (hn : 0<n) : 0<rev n := by
  induction n using Nat.evenOddRec with
  | h0 => omega
  | h_even n ih => rw [rev_even]; exact div_pos (ih (by omega)) (by norm_num)
  | h_odd n ih => rw [rev_odd]; linarith [(rev_bounds n).1]

def height (n : ℕ) : ℚ := rev (oddCore n)

lemma height_bounds (n : ℕ) : 0≤height n ∧ height n<1 := rev_bounds _

lemma height_le_input (n : ℕ) : height n≤(n : ℚ) := by
  by_cases hn : n=0
  · simp [hn,height,oddCore]
  · have hn1 : (1 : ℚ)≤n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    exact (height_bounds n).2.le.trans hn1

@[simp] lemma height_even (n : ℕ) : height (2*n)=height n := by
  unfold height oddCore
  simpa using congrArg rev (Nat.ordCompl_self_pow_mul n 1 Nat.prime_two)

@[simp] lemma height_odd (n : ℕ) : height (2*n+1)=rev (2*n+1) := by
  unfold height
  rw [oddCore_eq_of_odd]
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]

lemma residue_one_ascent {k : ℕ} (hk : 0<k) : height (4*k+1)<height (4*k+2) := by
  have h₁ : 4*k+1=2*(2*k)+1 := by omega
  have h₂ : 4*k+2=2*(2*k+1) := by omega
  rw [h₁,h₂,height_odd,height_even,height_odd,rev_odd,rev_even,rev_odd]
  linarith [rev_pos hk]

lemma residue_two_ascent (k : ℕ) : height (4*k+2)<height (4*k+3) := by
  have h₁ : 4*k+2=2*(2*k+1) := by omega
  have h₂ : 4*k+3=2*(2*k+1)+1 := by omega
  rw [h₁,h₂]
  simp only [height_even,height_odd,rev_odd]
  linarith [(rev_bounds k).2]

lemma residue_four_ascent (k : ℕ) : height (32*k+4)<height (32*k+5) := by
  have h₁ : 32*k+4=2*(2*(2*(2*(2*k))+1)) := by omega
  have h₂ : 32*k+5=2*(2*(2*(2*(2*k))+1))+1 := by omega
  rw [h₁,h₂]
  simp only [height_even,height_odd,rev_even,rev_odd]
  linarith [(rev_bounds k).1,(rev_bounds k).2]

lemma residue_twenty_seven_ascent (k : ℕ) : height (32*k+27)<height (32*k+28) := by
  have h₁ : 32*k+27=2*(2*(2*(2*(2*k+1)+1))+1)+1 := by omega
  have h₂ : 32*k+28=2*(2*(2*(2*(2*k+1)+1)+1)) := by omega
  rw [h₁,h₂]
  simp only [height_even,height_odd,rev_even,rev_odd]
  linarith [(rev_bounds k).1,(rev_bounds k).2]

def easy (n : ℕ) : Prop := n%4=1 ∨ n%4=2 ∨ n%32=4 ∨ n%32=27
instance (n : ℕ) : Decidable (easy n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

lemma easy_periodic (n : ℕ) : easy (n+32) ↔ easy n := by simp [easy,Nat.add_mod]

lemma easy_ascent {n : ℕ} (hn : easy n) (hne : n≠1) : height n<height (n+1) := by
  rcases hn with h | h | h | h
  · have he : n=4*(n/4)+1 := by omega
    have hk : 0<n/4 := by omega
    have hh := residue_one_ascent hk
    simpa [← he,show 4*(n/4)+2=n+1 by omega] using hh
  · have he : n=4*(n/4)+2 := by omega
    have hh := residue_two_ascent (n/4)
    simpa [← he,show 4*(n/4)+3=n+1 by omega] using hh
  · have he : n=32*(n/32)+4 := by omega
    have hh := residue_four_ascent (n/32)
    simpa [← he,show 32*(n/32)+5=n+1 by omega] using hh
  · have he : n=32*(n/32)+27 := by omega
    have hh := residue_twenty_seven_ascent (n/32)
    simpa [← he,show 32*(n/32)+28=n+1 by omega] using hh

lemma easy_count (N : ℕ) : ((range (32*N)).filter easy).card=18*N := by
  have h := Erdos371Exploration.periodic_count_blocks easy easy_periodic 0 N
  have h32 : ((range 32).filter easy).card=18 := by decide +kernel
  simpa [h32,Nat.mul_comm] using h

lemma ascent_count_lower (N : ℕ) :
    17*N≤((range (32*N)).filter (fun n => height n<height (n+1))).card := by
  have hs : (range (32*N)).filter easy ⊆
      insert 1 ((range (32*N)).filter (fun n => height n<height (n+1))) := by
    intro n hn
    obtain ⟨hnN,hne⟩ := mem_filter.mp hn
    by_cases h : n=1
    · simp [h]
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hnN,easy_ascent hne h⟩)
  have hc := (card_le_card hs).trans (card_insert_le _ _)
  rw [easy_count] at hc
  omega

/-- This bounded height is not balanced. It is not `Nat.maxPrimeFac`, and
this theorem makes no assertion about a size-dependent power amplification. -/
theorem height_not_density_half :
    ¬{n | height n<height (n+1)}.HasDensity (1/2) := by
  intro h
  have ht : Tendsto (fun N : ℕ => 32*(N+1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hh := h.comp ht
  have hlo (N : ℕ) : (17/32 : ℝ)≤
      {n | height n<height (n+1)}.partialDensity Set.univ (32*(N+1)) := by
    rw [Erdos371Exploration.partialDensity_eq_count]
    have hpos : (0 : ℝ)<(32*(N+1) : ℕ) := by positivity
    apply (le_div_iff₀ hpos).mpr
    have hc : (17 : ℝ)*(N+1)≤
        (((range (32*(N+1))).filter (fun n => height n<height (n+1))).card : ℝ) := by
      exact_mod_cast ascent_count_lower (N+1)
    push_cast
    linarith
  have he : (17/32 : ℝ)≤1/2 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hh (Eventually.of_forall hlo)
  norm_num at he

end Erdos371BinaryReversalHeight

#print axioms Erdos371BinaryReversalHeight.height_not_density_half

#print axioms Erdos371BinaryReversalHeight.height_le_input
#print axioms Erdos371BinaryReversalHeight.height_even
