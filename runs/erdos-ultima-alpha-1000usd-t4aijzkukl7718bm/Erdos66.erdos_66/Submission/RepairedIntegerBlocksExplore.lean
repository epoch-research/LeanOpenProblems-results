import Submission.RepairedPlaneProfileExplore
import Submission.AggregateUpperTransferExplore

/-! Actual finite natural-number sets with no exceptional targets in the
useful interval. The prime may be any odd prime above the coarse cutoff. -/
namespace Erdos66RepairedIntegerBlocks
open Filter AdditiveCombinatorics Erdos66TripleDeletionParameters Erdos66RepairedPlaneProfile
  Erdos66CurveFamilyPacket Erdos66AggregateUpperTransfer Erdos66AggregateCyclicThickening
  Erdos66CyclicThickening Erdos66OuterCarryProfile Erdos66IntegerBlock
open scoped Topology Classical
set_option maxHeartbeats 2400000

lemma natural_block_digits (M J n : ℕ) [NeZero M] [NeZero J] :
    ∃ (z : ZMod M) (r : Fin J), n=(n/(M*J))*(M*J)+(blockDigit M J z r).val := by
  obtain ⟨⟨z,r⟩,he⟩ := (blockEquiv M J).surjective (n : ZMod (M*J))
  change blockDigit M J z r=(n : ZMod (M*J)) at he
  refine ⟨z,r,?_⟩
  rw [he,ZMod.val_natCast,Nat.mul_comm (n/(M*J)) (M*J)]
  exact (Nat.div_add_mod n (M*J)).symm

/-- The global upper estimate includes targets below and above the useful
interval. In particular, the old coarse exception set has disappeared. -/
theorem eventually_repaired_integer_blocks (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1)
    (K J : ℕ) [NeZero K] [NeZero J] :
    ∀ᶠ m : ℝ in atTop, ∀ (p : ℕ) [Fact p.Prime], p≠2 → 8*(length m+1)+16<p →
      ∃ A : Set ℕ, A.Finite ∧ A ⊆ Set.Iio ((length m+1)*(((p*K)^2)*J)) ∧
        (∀ n, (sumRep A n : ℝ) ≤ ((J : ℝ)+1)*((K : ℝ)^2+2*K)*(1+4*ε)*m^3) ∧
        (∀ n, (start m ε+1)*(((p*K)^2)*J) ≤ n → n < (length m+1)*(((p*K)^2)*J) →
          |(sumRep A n : ℝ)-J*(K : ℝ)^2*m^3| ≤
            (((J : ℝ)+1)*((K : ℝ)^2*(5*ε)+2*K*(1+5*ε))+(K : ℝ)^2)*m^3) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_repaired_plane_profiles ε hε hε1] with m hm hp'
  intro p hp hp2 hpL
  obtain ⟨B,hBsup,hBshape,hBu,hBflat⟩ := hp' p hp2 hpL
  let M := ((p*K)^2)*J
  let C := fun i ↦ outerLift ((p*K)^2) J (thickenedSet p K (B i))
  let A := blockSet M C
  have hCs (i : ℕ) (hi : length m < i) : C i=∅ := by
    simp [C,outerLift,thickenedSet,hBsup i hi]
  have hs : A ⊆ Set.Iio ((length m+1)*M) := blockSet_support M (length m) C hCs
  have hU : 0 ≤ (1+4*ε)*m^3 := by positivity
  have hu (q : ℕ) (z : ZMod ((p*K)^2)) (r : Fin J) :
      (sumRep A (q*M+(blockDigit ((p*K)^2) J z r).val) : ℝ) ≤
        ((J : ℝ)+1)*((K : ℝ)^2+2*K)*(1+4*ε)*m^3 := by
    have hh := plane_to_integer_upper p K J B ((1+4*ε)*m^3) hU (fun q t s ↦ hBu q (t,s)) q z r
    change (sumRep A (q*M+(blockDigit ((p*K)^2) J z r).val) : ℝ) ≤ _ at hh
    nlinarith only [hh]
  have hf (q : ℕ) (hq₀ : start m ε+1 ≤ q) (hq : q ≤ length m)
      (z : ZMod ((p*K)^2)) (r : Fin J) :
      |(sumRep A (q*M+(blockDigit ((p*K)^2) J z r).val) : ℝ)-J*(K : ℝ)^2*m^3| ≤
        (((J : ℝ)+1)*((K : ℝ)^2*(5*ε)+2*K*(1+5*ε))+(K : ℝ)^2)*m^3 := by
    have hh := plane_to_integer_aggregate_error p K J B q (by omega) (m^3) (5*ε*m^3)
      (fun t s ↦ (hBflat q (by omega) hq (t,s)).le)
      (fun t s ↦ (hBflat (q-1) (by omega) (by omega) (t,s)).le) z r
    change |(sumRep A (q*M+(blockDigit ((p*K)^2) J z r).val) : ℝ)-J*(K : ℝ)^2*m^3| ≤ _ at hh
    nlinarith only [hh]
  refine ⟨A,(Set.finite_Iio _).subset hs,hs,?_,?_⟩
  · intro n
    obtain ⟨z,r,hn⟩ := natural_block_digits ((p*K)^2) J n
    have hh := hu (n/M) z r
    rw [←hn] at hh
    exact hh
  · intro n hn₀ hn
    have hq₀ : start m ε+1 ≤ n/M := (Nat.le_div_iff_mul_le (NeZero.pos M)).mpr hn₀
    have hq : n/M ≤ length m := by
      have hh := (Nat.div_lt_iff_lt_mul (NeZero.pos M)).mpr hn
      omega
    obtain ⟨z,r,he⟩ := natural_block_digits ((p*K)^2) J n
    have hh := hf (n/M) hq₀ hq z r
    rw [←he] at hh
    exact hh

end Erdos66RepairedIntegerBlocks
