import Submission.PredecessorPacketRepairExplore

/-! The existing finite predecessor selector, with its support information
retained for passage to locally finite repair sequences. -/
namespace Erdos66LocatedPredecessorPacket
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66NaturalSidonExtraction
  Erdos66FiniteSwapAlgebra Erdos66NaturalSymmetricPacket Erdos66PredecessorCell
  Erdos66UniformSelection Erdos66CellSidonSelection Erdos66Counting
  Erdos66PredecessorPacketRepair
open scoped Classical
set_option maxHeartbeats 2600000
variable {α : Type*} [Fintype α] [Nonempty α]

theorem exists_predecessor_packet_repair_located (A : Finset ℕ) (n : ℕ) (x : α → ℕ)
    (hx : Function.Injective x) (hhalf : ∀ a, 2*x a < n)
    (hmem : ∀ b a, predecessor (A : Set ℕ) (endpoint n x b a) ∈ A)
    (H : ℕ)
    (hfiber : ∀ b r,
      (Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (endpoint n x b a) = r)).card ≤ H)
    (hsep : ∀ a, Function.Injective (fun b ↦ predecessor (A : Set ℕ) (endpoint n x b a)))
    (m : ℕ) (T : Finset ℕ) (K₀ K R t : ℝ)
    (hB : ((badChoices A n x).card : ℝ) ≤ K₀)
    (hS : ∀ z ∈ T, ((swapHits A n x z).card : ℝ) ≤ K) (ht : 0 < t)
    (hsmall : ((m : ℝ)^4 + 4*m^2*H + m*K₀) / Fintype.card α +
      T.card * Real.exp ((m : ℝ)*Real.exp t*K/Fintype.card α-t*R) < 1) :
    ∃ D F : Finset ℕ, D ⊆ A ∧ Disjoint A F ∧ D.card = 2*m ∧ F.card = 2*m ∧
      (∀ N, -1 ≤ (count (swapped A D F : Set ℕ) N : ℝ)-count (A : Set ℕ) N ∧
        (count (swapped A D F : Set ℕ) N : ℝ)-count (A : Set ℕ) N ≤ 0) ∧
      sumRep (swapped A D F : Set ℕ) n = sumRep (A : Set ℕ) n+2*m ∧
      (∀ z, z ≠ n → sumRep (F : Set ℕ) z ≤ 6) ∧
      D = F.image (predecessor (A : Set ℕ)) ∧
      (∀ u ∈ F, ∃ b a, u = endpoint n x b a) ∧
      ∀ z ∈ T, z ≠ n →
        |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z| < 4*R+6 := by
  let cell : Bool → α → ℕ := fun b a ↦ predecessor (A : Set ℕ) (endpoint n x b a)
  have hxZ : Function.Injective (fun a ↦ (x a : ℤ)) := by
    intro a b he
    dsimp only at he
    exact hx (by exact_mod_cast he)
  have hsmall' : ((Fintype.card (Fin m) : ℝ)^4 +
      (Fintype.card (Fin m) : ℝ)^2 * (Fintype.card Bool : ℝ)^2 * H +
        Fintype.card (Fin m) * (badChoices A n x).card) / Fintype.card α +
        T.card * Real.exp ((Fintype.card (Fin m) : ℝ)*Real.exp t*K/Fintype.card α-t*R) < 1 := by
    simp only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat]
    have hb := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (α := ℝ) m)
    have hc : (m : ℝ)^4 + m^2*(2:ℝ)^2*H + m*(badChoices A n x).card ≤
        m^4 + 4*m^2*H + m*K₀ := by nlinarith only [hb]
    have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    linarith only [hh, hsmall]
  obtain ⟨ω, hω, havoid, hcell, hsidon, hhits⟩ :=
    exists_cell_sidon_avoid_and_hits (ι := Fin m) (fun a ↦ (x a : ℤ)) hxZ cell H (by
        intro b r
        convert hfiber b r using 1
        congr 2) hsep
      (badChoices A n x) T (swapHits A n x) K R t hS ht hsmall'
  let E : Finset ℕ := Finset.univ.image (fun i ↦ x (ω i))
  let F : Finset ℕ := natPacket n E
  let D : Finset ℕ := F.image (predecessor (A : Set ℕ))
  have hEhalf : ∀ a ∈ E, 2*a < n := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hhalf _
  have hEn : ∀ a ∈ E, a ≤ n := fun a ha ↦ by have := hEhalf a ha; omega
  have hEsidon : NatSidon E := by
    intro a ha b hb c hc d hd he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
    rcases hsidon i j k l (by exact_mod_cast he) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  have hEcard : E.card = m := by
    have hinj : Function.Injective (fun i ↦ x (ω i)) := hx.comp hω
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hFcard : F.card = 2*m := by rw [natPacket_card n E hEhalf, hEcard]
  have hFimage : Finset.univ.image (fun p : Fin m × Bool ↦ endpoint n x p.2 (ω p.1)) = F :=
    endpoint_image n x ω
  have hFmem : ∀ u ∈ F, predecessor (A : Set ℕ) u ∈ (A : Set ℕ) := by
    intro u hu
    rw [← hFimage] at hu
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp hu
    exact hmem b (ω i)
  have hFnew : ∀ u ∈ F, u ∉ (A : Set ℕ) := by
    intro u hu hA
    rw [← hFimage] at hu
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp hu
    exact havoid i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Or.inl hA⟩)
  have hinj : Set.InjOn (predecessor (A : Set ℕ)) (F : Set ℕ) := by
    intro u hu v hv he
    rw [← hFimage] at hu hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hv
    have hpq : p = q := hcell he
    rw [hpq]
  have hDsub : D ⊆ A := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hFmem v hv
  have hdis : Disjoint A F := Finset.disjoint_left.mpr (fun u hu hv ↦ hFnew u hv hu)
  have hDcard : D.card = 2*m := by rw [Finset.card_image_of_injOn hinj, hFcard]
  have hDA : pairs D A n = 0 := by
    apply pairs_eq_zero_of_no_partner
    intro u hu hun huA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [← hFimage] at hv
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp hv
    exact havoid i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Or.inr ⟨hun, huA⟩⟩)
  have htarget : sumRep (swapped A D F : Set ℕ) n = sumRep (A : Set ℕ) n+2*m := by
    rw [swapped_symmetric_target A D E n hDsub hEn hdis hDA, hFcard]
  have hself : ∀ z, z ≠ n → sumRep (F : Set ℕ) z ≤ 6 :=
    natPacket_off_center E hEsidon n hEhalf
  refine ⟨D, F, hDsub, hdis, hDcard, hFcard, ?_, htarget, hself, rfl, ?_, ?_⟩
  · intro N
    rw [swapped_coe]
    exact predecessor_swap_prefix (A : Set ℕ) F hFmem hFnew hinj N
  · intro u hu
    rw [← hFimage] at hu
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨b, ω i, rfl⟩
  · intro z hz hzn
    have hnew : (pairs F A z : ℝ) ≤ 2*hits (swapHits A n x z) ω := by
      rw [← hFimage]
      have hh := image_pairs_le_hits (fun i b ↦ endpoint n x b (ω i)) A z ω (swapHits A n x z)
        (fun i b h1 h2 ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Or.inl ⟨h1,h2⟩⟩)
      simpa only [Fintype.card_bool, Nat.cast_ofNat] using hh
    have hDimage : Finset.univ.image (fun p : Fin m × Bool ↦ cell p.2 (ω p.1)) = D := by
      dsimp only [D]
      rw [← hFimage, Finset.image_image]
      rfl
    have hdel : (pairs D A z : ℝ) ≤ 2*hits (swapHits A n x z) ω := by
      rw [← hDimage]
      have hh := image_pairs_le_hits (fun i b ↦ cell b (ω i)) A z ω (swapHits A n x z)
        (fun i b h1 h2 ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Or.inr ⟨h1,h2⟩⟩)
      simpa only [Fintype.card_bool, Nat.cast_ofNat] using hh
    have hu := sumRep_swapped_upper A D F hdis z
    have hl := sumRep_swapped_lower A D F hDsub z
    have hu' : (sumRep (swapped A D F : Set ℕ) z : ℝ) ≤
        sumRep (A : Set ℕ) z + 2*pairs F A z + sumRep (F : Set ℕ) z := by exact_mod_cast hu
    have hl' : (sumRep (A : Set ℕ) z : ℝ) ≤
        sumRep (swapped A D F : Set ℕ) z + 2*pairs D A z := by exact_mod_cast hl
    have hs : (sumRep (F : Set ℕ) z : ℝ) ≤ 6 := by exact_mod_cast hself z hzn
    have hh := hhits z hz
    rw [abs_lt]
    constructor <;> linarith

end Erdos66LocatedPredecessorPacket
