import Submission.PeriodicParameterSieve

/-! A quantitative version of the parameter sieve, retaining the chosen
Euler-product lower bound in the eventual parameter density. -/
namespace Erdos1206.QuantitativeParameterSieve
open Finset Filter CoprimeBoxCRT PeriodicParameterSieve
open scoped Classical
set_option maxHeartbeats 1000000

/-- A positive Euler product and an eventually negligible tail give positive
parameter density. Moduli need only be pairwise coprime at distinct primes. -/
theorem density_of_product_lower (m : ℕ → ℕ)
    (G : (p : ℕ) → Finset (ZMod (m p) × ZMod (m p)))
    (hm : ∀ p, p.Prime → 0 < m p)
    (hc : ∀ p q, p.Prime → q.Prime → p≠q → (m p).Coprime (m q))
    (δ : ℝ) (hδ : 0 < δ)
    (hprod : ∀ S : Finset ℕ, (∀ p∈S, p.Prime) →
      δ ≤ ∏p∈S,localDensity m G p)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∀ᶠ N : ℕ in atTop,
      ((tail m G H N).card:ℝ) ≤ ε*(N:ℝ)^2) :
    ∀ᶠ N : ℕ in atTop,
      (δ/2)*(N:ℝ)^2 ≤ (good m G N).card := by
  obtain ⟨H,hH⟩ := htail (δ/4) (by positivity)
  let S := (range (H+1)).filter Nat.Prime
  have hS (p : ℕ) (hp : p∈S) : p.Prime := (mem_filter.mp hp).2
  let d : ℝ := ∏p∈S,(m p:ℝ)
  have hd : 0 ≤ d := prod_nonneg (fun p _ => Nat.cast_nonneg _)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (4*(1+3*d)/δ+d+1)
  filter_upwards [hH,eventually_ge_atTop N₀] with N htailN hN₀N
  have hN : 4*(1+3*d)/δ+d+1 < (N:ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN₀N)
  have hN0 : (0:ℝ) < N := lt_trans (by positivity) hN
  have hdN : d ≤ (N:ℝ) := by
    have hh : 0 ≤ 4*(1+3*d)/δ := by positivity
    linarith
  have hδN : 4*(1+3*d) < δ*(N:ℝ) := by
    have hh : 4*(1+3*d)/δ < (N:ℝ) := by linarith
    exact (div_lt_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  let T := (range N ×ˢ range N).filter (fun x =>
    ∀ p∈S, ((x.1:ZMod (m p)),(x.2:ZMod (m p)))∈G p)
  have hcount : δ*(N:ℝ)^2 ≤ (T.card:ℝ)+3*(N:ℝ)*d := by
    have he := (abs_le.mp (joint_box_discrepancy m S
      (fun p hp => hm p (hS p hp))
      (fun p hp q hq hpq => hc p q (hS p hp) (hS q hq) hpq) G N)).1
    have hp := mul_le_mul_of_nonneg_left (hprod S hS) (sq_nonneg (N:ℝ))
    have hd2 := mul_le_mul_of_nonneg_left hdN hd
    change -(2*(N:ℝ)*d+d^2) ≤ (T.card:ℝ)-(N:ℝ)^2*∏p∈S,localDensity m G p at he
    nlinarith only [he,hp,hd2]
  have hcover : T ⊆ ({0} ×ˢ range N) ∪ tail m G H N ∪ good m G N := by
    intro x hx
    obtain ⟨hxbox,hxhead⟩ := mem_filter.mp hx
    by_cases hx0 : x.1=0
    · exact mem_union_left _ (mem_union_left _
        (mem_product.mpr ⟨mem_singleton.mpr hx0,(mem_product.mp hxbox).2⟩))
    · have hxpos := Nat.pos_of_ne_zero hx0
      by_cases hgood : ∀ p, p.Prime → ((x.1:ZMod (m p)),(x.2:ZMod (m p)))∈G p
      · exact mem_union_right _ (mem_filter.mpr ⟨hxbox,hxpos,hgood⟩)
      · push_neg at hgood
        obtain ⟨p,hp,hbad⟩ := hgood
        have hpH : H < p := by
          by_contra! hpH
          exact hbad (hxhead p (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩))
        exact mem_union_left _ (mem_union_right _
          (mem_filter.mpr ⟨hxbox,hxpos,p,hp,hpH,hbad⟩))
  have hcard : T.card ≤ N+(tail m G H N).card+(good m G N).card := by
    calc
      _ ≤ (({0} ×ˢ range N) ∪ tail m G H N ∪ good m G N).card := card_le_card hcover
      _ ≤ (({0} ×ˢ range N) ∪ tail m G H N).card+(good m G N).card := card_union_le _ _
      _ ≤ (({0} ×ˢ range N).card+(tail m G H N).card)+(good m G N).card :=
        Nat.add_le_add_right (card_union_le _ _) _
      _ = _ := by simp
  have hcardR : (T.card:ℝ) ≤ (N:ℝ)+(tail m G H N).card+(good m G N).card := by
    exact_mod_cast hcard
  have hmul := mul_lt_mul_of_pos_right hδN hN0
  nlinarith only [hcount,hcardR,htailN,hmul]


#print axioms density_of_product_lower
end Erdos1206.QuantitativeParameterSieve
