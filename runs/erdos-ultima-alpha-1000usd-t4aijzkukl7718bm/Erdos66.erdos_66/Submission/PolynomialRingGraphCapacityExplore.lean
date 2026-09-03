import Submission.PolynomialSquareZeroFiberExplore
import Submission.RadixPlaneSumSupportExplore

/-! A logarithmic sum cap permits only a vanishing fraction of a polynomial
graph modulo a large square. Arbitrary deletions and translations are allowed. -/
namespace Erdos66PolynomialRingGraphCapacity
open AdditiveCombinatorics Erdos66PolynomialSquareZeroFiber Erdos66RadixPlaneSumSupport Erdos66Carry
open scoped Classical
set_option maxHeartbeats 2500000

variable (q : ℕ) [NeZero q]

noncomputable def encodeGraph (P : Polynomial (ZMod (q^2))) (a : ℕ) (x : ZMod (q^2)) : ℕ :=
  a+digitEncode (q^2) (graph q P x)

lemma encodeGraph_injective (P : Polynomial (ZMod (q^2))) (a : ℕ) :
    Function.Injective (encodeGraph q P a) := by
  intro x y h
  have hh : digitEncode (q^2) (graph q P x) = digitEncode (q^2) (graph q P y) := by
    unfold encodeGraph at h
    omega
  exact congrArg Prod.fst (digitEncode_injective (q^2) hh)

lemma encodeGraph_location (P : Polynomial (ZMod (q^2))) (a : ℕ) (x : ZMod (q^2)) :
    a ≤ encodeGraph q P a x ∧ encodeGraph q P a x < a+q^4 := by
  have hh := digitEncode_lt (q^2) (graph q P x)
  have he : (q^2)^2 = q^4 := by ring
  rw [he] at hh
  unfold encodeGraph
  omega

lemma fiber_sum_support (P : Polynomial (ZMod (q^2))) (a : ℕ)
    (B : Finset (ZMod (q^2))) (r : Fin q) :
    (((fiber q B r).product (fiber q B r)).image
      (fun p ↦ encodeGraph q P a p.1+encodeGraph q P a p.2)).card ≤ 4*q := by
  let T := (Finset.univ : Finset (Fin q)).image (fun i ↦ tangentSum q P r (sumValue q r i))
  have hT : ∀ x ∈ fiber q B r, ∀ y ∈ fiber q B r, graph q P x+graph q P y ∈ T := by
    intro x hx y hy
    obtain ⟨i,hi⟩ := within_fiber_sum_values q P r x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  have hh := lifted_sum_support_bound (q^2) (fiber q B r) (graph q P) T hT a
  have hc : T.card ≤ q := by
    exact (Finset.card_image_le).trans (by simp only [Finset.card_univ,Fintype.card_fin]; rfl)
  exact hh.trans (Nat.mul_le_mul_left 4 hc)

lemma fiber_card_square_bound (P : Polynomial (ZMod (q^2))) (a : ℕ)
    (B : Finset (ZMod (q^2))) (A : Set ℕ) (hB : ∀ x ∈ B, encodeGraph q P a x ∈ A)
    (V : ℝ) (hV : 0 ≤ V)
    (hcap : ∀ n, 2*a ≤ n → n < 2*(a+q^4) → (sumRep A n : ℝ) ≤ V)
    (r : Fin q) : ((fiber q B r).card : ℝ)^2 ≤ 4*q*V := by
  apply encoded_pair_mass_bound (fiber q B r) (encodeGraph q P a)
    (encodeGraph_injective q P a).injOn A (fun x hx ↦ hB x (Finset.mem_filter.mp hx).1)
    V hV _ (4*q) (fiber_sum_support q P a B r) |>.trans_eq ?_
  · intro x hx y hy
    have hx := encodeGraph_location q P a x
    have hy := encodeGraph_location q P a y
    exact hcap _ (by omega) (by omega)
  · push_cast
    ring

lemma largest_fiber (B : Finset (ZMod (q^2))) :
    ∃ r : Fin q, B.card ≤ q*(fiber q B r).card := by
  have hn : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,NeZero.pos q⟩,Finset.mem_univ _⟩
  obtain ⟨r,hr,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
    (fun r ↦ (fiber q B r).card) hn
  refine ⟨r,?_⟩
  have he : B.card = ∑ r : Fin q, (fiber q B r).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun x _ ↦ Finset.mem_univ (residue q x))
  rw [he]
  calc
    _ ≤ ∑ _r : Fin q, (fiber q B r).card := Finset.sum_le_sum (fun i hi ↦ hmax i hi)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

/-- A subset of the translated graph of ANY polynomial over `ZMod (q^2)`
has squared cardinality at most `4*q^3*V` under the actual integer sum cap V.
There is no degree bound, whole-graph retention, or reflection hypothesis. -/
theorem polynomial_graph_capacity (P : Polynomial (ZMod (q^2))) (a : ℕ)
    (B : Finset (ZMod (q^2))) (A : Set ℕ) (hB : ∀ x ∈ B, encodeGraph q P a x ∈ A)
    (V : ℝ) (hV : 0 ≤ V)
    (hcap : ∀ n, 2*a ≤ n → n < 2*(a+q^4) → (sumRep A n : ℝ) ≤ V) :
    (B.card : ℝ)^2 ≤ 4*(q : ℝ)^3*V := by
  obtain ⟨r,hr⟩ := largest_fiber q B
  have hr' : (B.card : ℝ) ≤ q*(fiber q B r).card := by exact_mod_cast hr
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) B.card) hr' 2
  have hf := fiber_card_square_bound q P a B A hB V hV hcap r
  have hh := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ (q : ℝ)^2 by positivity)
  nlinarith only [hs,hh]

/-- Specialization to a global logarithmic envelope. -/
theorem polynomial_graph_log_capacity (P : Polynomial (ZMod (q^2))) (a : ℕ)
    (B : Finset (ZMod (q^2))) (A : Set ℕ) (hB : ∀ x ∈ B, encodeGraph q P a x ∈ A)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) :
    (B.card : ℝ)^2 ≤ 4*(q : ℝ)^3*(K+C*Real.log (2*((a : ℝ)+q^4)+2)) := by
  have hlog : 0 ≤ Real.log (2*((a : ℝ)+(q : ℝ)^4)+2) := by
    apply Real.log_nonneg
    have hh : (0 : ℝ) ≤ (a : ℝ)+(q : ℝ)^4 := by positivity
    linarith
  apply polynomial_graph_capacity q P a B A hB _ (add_nonneg hK (mul_nonneg hC hlog))
  intro n hn0 hn1
  have hln := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)+2)
    (show (n : ℝ)+2 ≤ 2*((a : ℝ)+(q : ℝ)^4)+2 by exact_mod_cast (show n+2 ≤ 2*(a+q^4)+2 by omega))
  exact (henv n).trans (add_le_add_right (mul_le_mul_of_nonneg_left hln hC) K)

end Erdos66PolynomialRingGraphCapacity
