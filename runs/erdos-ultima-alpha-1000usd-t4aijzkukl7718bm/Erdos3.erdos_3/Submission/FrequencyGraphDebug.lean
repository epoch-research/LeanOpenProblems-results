import Submission.SpectralGraphEnergy
import Submission.BalogSzemerediGowers

/-! Frequency graphs, their exact additive energies, and extraction of a
small-difference frequency graph from large U³. -/
namespace Erdos3FrequencyGraph
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3SpectralGraphEnergy
  Erdos3BalogSzemerediGowers
open scoped BigOperators Classical Pointwise Combinatorics.Additive
set_option maxHeartbeats 3500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def frequencyGraph (H : Finset G) (ξ : G → AddChar G ℂ) : Finset (G × AddChar G ℂ) :=
  H.image (fun h ↦ (h,ξ h))

lemma mem_frequencyGraph (H : Finset G) (ξ : G → AddChar G ℂ) (p : G × AddChar G ℂ) :
    p ∈ frequencyGraph H ξ ↔ p.1 ∈ H ∧ p.2 = ξ p.1 := by
  constructor
  · intro hp
    obtain ⟨h,hh,rfl⟩ := mem_image.mp hp
    exact ⟨hh,rfl⟩
  · rintro ⟨hp,hξ⟩
    exact mem_image.mpr ⟨p.1,hp,Prod.ext rfl hξ.symm⟩

lemma card_frequencyGraph (H : Finset G) (ξ : G → AddChar G ℂ) :
    (frequencyGraph H ξ).card = H.card :=
  card_image_of_injective _ (fun _ _ hh ↦ congrArg Prod.fst hh)

noncomputable def parallelogramParameters (H : Finset G) (ξ : G → AddChar G ℂ) : Finset (G × G × G) :=
  univ.filter (fun p ↦ p.1 ∈ H ∧ p.2.1 ∈ H ∧ p.1-p.2.2 ∈ H ∧ p.2.1-p.2.2 ∈ H ∧
    ξ p.1*ξ (p.2.1-p.2.2) = ξ p.2.1*ξ (p.1-p.2.2))

lemma graphEnergy_eq_card_parameters (H : Finset G) (ξ : G → AddChar G ℂ) :
    graphEnergy H ξ = ((parallelogramParameters H ξ).card : ℝ)/(Fintype.card G : ℝ)^3 := by
  have hp : graphEnergy H ξ =
      𝔼 p : G × G × G, if p ∈ parallelogramParameters H ξ then (1 : ℝ) else 0 := by
    rw [expect_pair]
    simp_rw [expect_pair]
    unfold graphEnergy
    apply expect_congr rfl
    intro h _
    apply expect_congr rfl
    intro k _
    apply expect_congr rfl
    intro t _
    simp only [parallelogramParameters,mem_filter,mem_univ,true_and]
  rw [hp]
  simp [Fintype.expect_eq_sum_div_card,pow_succ,mul_assoc]

lemma card_parameters_eq_energy (H : Finset G) (ξ : G → AddChar G ℂ) :
    (parallelogramParameters H ξ).card = E[frequencyGraph H ξ] := by
  let φ : G → G × AddChar G ℂ := fun h ↦ (h,ξ h)
  let enc : (G × G × G) → ((G × AddChar G ℂ) × (G × AddChar G ℂ)) ×
      (G × AddChar G ℂ) × (G × AddChar G ℂ) :=
    fun p ↦ ((φ p.1,φ p.2.1),φ (p.2.1-p.2.2),φ (p.1-p.2.2))
  unfold Finset.addEnergy
  apply card_bij (fun p _ ↦ enc p)
  · intro p hp
    have hh : p.1 ∈ H ∧ p.2.1 ∈ H ∧ p.1-p.2.2 ∈ H ∧ p.2.1-p.2.2 ∈ H ∧
        ξ p.1*ξ (p.2.1-p.2.2) = ξ p.2.1*ξ (p.1-p.2.2) := by
      simpa only [parallelogramParameters,mem_filter,mem_univ,true_and] using hp
    have hmem (h : G) (hh : h ∈ H) : φ h ∈ frequencyGraph H ξ :=
      mem_image.mpr ⟨h,hh,rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨hmem _ hh.1,hmem _ hh.2.1⟩,
      mem_product.mpr ⟨hmem _ hh.2.2.2.1,hmem _ hh.2.2.1⟩⟩,?_⟩
    apply Prod.ext
    · change p.1+(p.2.1-p.2.2) = p.2.1+(p.1-p.2.2)
      abel
    · exact hh.2.2.2.2
  · intro p _ q _ he
    have hh : p.1 = q.1 := congrArg (fun r ↦ r.1.1.1) he
    have hk : p.2.1 = q.2.1 := congrArg (fun r ↦ r.1.2.1) he
    have ht : p.2.2 = q.2.2 := by
      have he' : p.1-p.2.2 = q.1-q.2.2 := congrArg (fun r ↦ r.2.2.1) he
      rw [hh] at he'
      exact sub_right_injective he'
    exact Prod.ext hh (Prod.ext hk ht)
  · intro q hq
    obtain ⟨hm,he⟩ := mem_filter.mp hq
    obtain ⟨hab,hcd⟩ := mem_product.mp hm
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    obtain ⟨hc,hd⟩ := mem_product.mp hcd
    obtain ⟨ha1,ha2⟩ := (mem_frequencyGraph H ξ _).mp ha
    obtain ⟨hb1,hb2⟩ := (mem_frequencyGraph H ξ _).mp hb
    obtain ⟨hc1,hc2⟩ := (mem_frequencyGraph H ξ _).mp hc
    obtain ⟨hd1,hd2⟩ := (mem_frequencyGraph H ξ _).mp hd
    have he1 : q.1.1.1+q.2.1.1 = q.1.2.1+q.2.2.1 := congrArg Prod.fst he
    have he2 : ξ q.1.1.1*ξ q.2.1.1 = ξ q.1.2.1*ξ q.2.2.1 := by
      have he' := congrArg Prod.snd he
      change q.1.1.2*q.2.1.2 = q.1.2.2*q.2.2.2 at he'
      simpa only [ha2,hb2,hc2,hd2] using he'
    let p : G × G × G := (q.1.1.1,q.1.2.1,q.1.1.1-q.2.2.1)
    have hp1 : p.1-p.2.2 = q.2.2.1 := by dsimp [p]; abel
    have hp2 : p.2.1-p.2.2 = q.2.1.1 := by
      dsimp [p]
      have he' : q.2.1.1 = q.1.2.1+q.2.2.1-q.1.1.1 :=
        eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he1)
      rw [he']
      abel
    have hpm : p ∈ parallelogramParameters H ξ := by
      simp only [parallelogramParameters,mem_filter,mem_univ,true_and]
      exact ⟨ha1,hb1,hp1 ▸ hd1,hp2 ▸ hc1,by simpa only [hp1,hp2] using he2⟩
    refine ⟨p,hpm,?_⟩
    dsimp [enc]
    apply Prod.ext
    · exact Prod.ext (Prod.ext rfl ha2.symm) (Prod.ext rfl hb2.symm)
    · apply Prod.ext
      · exact Prod.ext hp2 (by simpa only [φ,hp2] using hc2.symm)
      · exact Prod.ext hp1 (by simpa only [φ,hp1] using hd2.symm)

/-- The normalized energy used in derivative extraction is exactly the usual
additive energy divided by |G|³, not by the size of the graph. -/
theorem graphEnergy_eq_addEnergy (H : Finset G) (ξ : G → AddChar G ℂ) :
    graphEnergy H ξ = (E[frequencyGraph H ξ] : ℝ)/(Fintype.card G : ℝ)^3 := by
  rw [graphEnergy_eq_card_parameters,card_parameters_eq_energy]

/-- Large U³ has a polynomially large derivative-frequency graph with a
polynomially bounded difference set. This is not yet its linearization or
integration into a quadratic phase. -/
theorem large_U3_small_difference_graph (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
      δ^5/256*(Fintype.card G : ℝ) ≤ H.card ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (derivative f h) (ξ h)‖^2) ∧
      δ^36*((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ) ≤
        (2 : ℝ)^57*(Fintype.card G : ℝ) := by
  trace "start"
  obtain ⟨H₀,ξ,hH₀,hcoef,henergy⟩ := large_U3_spectral_graph f hf hδ.le hU
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hH₀pos : H₀.Nonempty := by
    apply card_pos.mp
    have hh : (0 : ℝ) < H₀.card := lt_of_lt_of_le (by positivity) hH₀
    exact_mod_cast hh
  trace "nonempty done"
  let Γ := frequencyGraph H₀ ξ
  have hΓ : Γ.Nonempty := image_nonempty.mpr hH₀pos
  have hcΓ : Γ.card = H₀.card := card_frequencyGraph H₀ ξ
  have hΓle : (Γ.card : ℝ) ≤ Fintype.card G := by
    rw [hcΓ]
    exact_mod_cast card_le_univ H₀
  have hE : (δ/2)^4*(Γ.card : ℝ)^3 ≤ (E[Γ] : ℝ) := by
    rw [graphEnergy_eq_addEnergy] at henergy
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < (Fintype.card G : ℝ)^3)).mp henergy
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Γ.card) hΓle 3
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans he
  trace "energy done"
  obtain ⟨B,hBΓ,hBcard,hBdiff⟩ := balog_szemeredi_gowers Γ hΓ (by positivity : 0 < (δ/2)^4) hE
  trace "BSG done"
  let H := H₀.filter (fun h ↦ (h,ξ h) ∈ B)
  have hgraph : frequencyGraph H ξ = B := by
    ext p
    rw [mem_frequencyGraph]
    constructor
    · rintro ⟨hp,hpξ⟩
      have hb := (mem_filter.mp hp).2
      have he : (p.1,ξ p.1) = p := Prod.ext rfl hpξ.symm
      rwa [he] at hb
    · intro hp
      obtain ⟨hpH,hpξ⟩ := (mem_frequencyGraph H₀ ξ p).mp (hBΓ hp)
      refine ⟨mem_filter.mpr ⟨hpH,?_⟩,hpξ⟩
      have he : (p.1,ξ p.1) = p := Prod.ext rfl hpξ.symm
      rwa [he]
  trace "graph done"
  have hcH : H.card = B.card := by rw [← card_frequencyGraph H ξ,hgraph]
  refine ⟨H,ξ,?_,?_,?_⟩
  · rw [hcH]
    rw [hcΓ] at hBcard
    have hh := mul_le_mul_of_nonneg_left hH₀ (by positivity : 0 ≤ (δ/2)^4/8)
    trace "size calc"
    nlinarith only [hh,hBcard]
  · intro h hh
    exact hcoef h (mem_filter.mp hh).1
  · rw [hgraph]
    have hh : ((δ/2)^4)^9*((B-B).card : ℝ) ≤ 2097152*(Fintype.card G : ℝ) :=
      hBdiff.trans (mul_le_mul_of_nonneg_left hΓle (by norm_num))
    trace "diff calc"
    norm_num [← pow_mul,div_pow] at hh ⊢
    trace "diff norm done"
    nlinarith only [hh]

#print axioms graphEnergy_eq_addEnergy
#print axioms large_U3_small_difference_graph
end Erdos3FrequencyGraph
