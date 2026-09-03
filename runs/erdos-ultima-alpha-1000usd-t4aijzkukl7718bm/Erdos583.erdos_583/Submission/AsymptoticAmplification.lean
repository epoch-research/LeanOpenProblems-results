import Submission.AdditiveAmplification

/-! Arbitrarily accurate linear bounds suffice for the exact conjecture.
No such approximation theorem is assumed or proved unconditionally here. -/
namespace Erdos583AsymptoticAmplificationDevelopment
open SimpleGraph Erdos583Work Erdos583Work.StarCopyAmplification
open Erdos583AdditiveAmplificationDevelopment
open scoped Classical
universe uAsymptotic
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma reduce_odd_linear_offset (a : ℚ) (ha : a ≤ 1) (c : ℕ)
    (hbound : ∀ {W : Type uAsymptotic} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        (D.card : ℚ) ≤ a*Fintype.card W+(c+3 : ℕ))
    {V : Type uAsymptotic} [Fintype V] (G : SimpleGraph V)
    (_ho : Odd (Fintype.card V)) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (D.card : ℚ) ≤ a*Fintype.card V+(c+2 : ℕ) := by
  let u : V := Classical.choice hG.nonempty
  obtain ⟨D,hD,hDc⟩ := hbound (fourHub G u) (fourHub_odd (V := V)) (fourHub_connected G u hG)
  obtain ⟨E,hE,hEc⟩ := fourHub_project G u hD
  have hEc' : (4 : ℚ)*E.card ≤ D.card+2 := by exact_mod_cast hEc
  rw [fourHub_card] at hDc
  push_cast at hDc ⊢
  have hc : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  refine ⟨E,hE,?_⟩
  nlinarith

lemma odd_linear_offset_two (a : ℚ) (ha : a ≤ 1) (c : ℕ)
    (hbound : ∀ {W : Type uAsymptotic} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        (D.card : ℚ) ≤ a*Fintype.card W+(c+2 : ℕ))
    {V : Type uAsymptotic} [Fintype V] (G : SimpleGraph V)
    (ho : Odd (Fintype.card V)) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (D.card : ℚ) ≤ a*Fintype.card V+2 := by
  induction c with
  | zero => simpa using hbound G ho hG
  | succ c ih =>
    apply ih
    intro W _ J hJo hJ
    apply reduce_odd_linear_offset a ha c (G := J) (hG := hJ) (_ho := hJo)
    intro X _ K hKo hK
    simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hbound K hKo hK

lemma odd_linear_bound_offset_two (a : ℚ) (ha : a ≤ 1) (c : ℕ)
    (hbound : ∀ {W : Type uAsymptotic} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        (D.card : ℚ) ≤ a*Fintype.card W+c)
    {V : Type uAsymptotic} [Fintype V] (G : SimpleGraph V)
    (ho : Odd (Fintype.card V)) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (D.card : ℚ) ≤ a*Fintype.card V+2 := by
  apply odd_linear_offset_two a ha c (G := G) (ho := ho) (hG := hG)
  intro W _ J hJo hJ
  obtain ⟨D,hD,hDc⟩ := hbound J hJo hJ
  refine ⟨D,hD,?_⟩
  push_cast
  linarith

/-- The exact conjecture follows from arbitrarily good leading coefficients,
even if each coefficient requires its own arbitrary uniform additive term. -/
lemma gallai_of_arbitrarily_good_linear_bounds
    (happrox : ∀ ε : ℚ, 0 < ε → ∃ c : ℕ,
      ∀ {W : Type uAsymptotic} [Fintype W] (G : SimpleGraph W),
        Odd (Fintype.card W) → G.Connected →
        ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
          (D.card : ℚ) ≤ (1/2+ε)*Fintype.card W+c)
    {V : Type uAsymptotic} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  apply gallai_of_uniform_odd_additive_bound 2 (G := G) (hG := hG)
  intro W _ J hJo hJ
  let n := Fintype.card W
  let ε : ℚ := 1/(2*(n : ℚ)+2)
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℚ) < 2*n+2 := by positivity
  have he : 0 < ε := by dsimp [ε]; positivity
  have hemul : ε*(2*(n : ℚ)+2)=1 := div_mul_cancel₀ 1 (ne_of_gt hd)
  have ha : (1/2 : ℚ)+ε ≤ 1 := by nlinarith
  have hen : ε*(n : ℚ) ≤ 1/2 := by nlinarith
  obtain ⟨c,hc⟩ := happrox ε he
  obtain ⟨D,hD,hDc⟩ := odd_linear_bound_offset_two (1/2+ε) ha c hc J hJo hJ
  have hceil : 2*⌈(Fintype.card W : ℚ)/2⌉₊=n+1 := by
    rw [BridgeGlue.ceil_half]
    obtain ⟨m,hm⟩ := hJo
    dsimp [n]
    omega
  have hceil' : (2 : ℚ)*⌈(Fintype.card W : ℚ)/2⌉₊=(n : ℚ)+1 := by exact_mod_cast hceil
  have hDc' : (D.card : ℚ) ≤ (⌈(Fintype.card W : ℚ)/2⌉₊ : ℚ)+2 := by
    change (D.card : ℚ) ≤ (1/2+ε)*n+2 at hDc
    nlinarith
  exact ⟨D,hD,by exact_mod_cast hDc'⟩

lemma normal_partition_card_le_vertices {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card V := by
  classical
  obtain ⟨D,hD,hDn,hDb⟩ := PendantCompletion.exists_normal_decomposition G
  have hsum := hD.sum_endpointMultiplicity hDn
  have hle : (∑ x, endpointMultiplicity D x) ≤ ∑ _x : V, (2 : ℕ) :=
    Finset.sum_le_sum (fun x _ ↦ (hDb x).1)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hle
  exact ⟨D,hD,by omega⟩

/-- Even a merely asymptotic leading coefficient one half, restricted to
connected graphs of odd order, would imply the exact bound for every order. -/
lemma gallai_of_asymptotic_odd_bound
    (happrox : ∀ ε : ℚ, 0 < ε → ∃ N : ℕ,
      ∀ {W : Type uAsymptotic} [Fintype W] (G : SimpleGraph W),
        Odd (Fintype.card W) → G.Connected → N ≤ Fintype.card W →
        ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
          (D.card : ℚ) ≤ (1/2+ε)*Fintype.card W)
    {V : Type uAsymptotic} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  apply gallai_of_arbitrarily_good_linear_bounds (G := G) (hG := hG)
  intro ε he
  obtain ⟨N,hN⟩ := happrox ε he
  refine ⟨N,?_⟩
  intro W _ J hJo hJ
  by_cases hn : N ≤ Fintype.card W
  · obtain ⟨D,hD,hDc⟩ := hN J hJo hJ hn
    have hNp : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    exact ⟨D,hD,by linarith⟩
  · obtain ⟨D,hD,hDc⟩ := normal_partition_card_le_vertices J
    have hDN : (D.card : ℚ) ≤ N := by exact_mod_cast (show D.card ≤ N by omega)
    have hp : (0 : ℚ) ≤ (1/2+ε)*Fintype.card W := by positivity
    exact ⟨D,hD,by linarith⟩

end Erdos583AsymptoticAmplificationDevelopment
