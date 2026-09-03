import Submission.UniformWidthPacketsExplore
import Submission.NaturalRepairBridgeExplore
import Submission.NatPairAlgebraExplore

/-! A natural-number interface for jointly selected labelled packets. The
labels remain available for attaching the two balanced curve types. -/
namespace Erdos66NaturalLabeledPackets
open AdditiveCombinatorics Erdos66MultiPacket Erdos66MultiPacketSelection
  Erdos66UniformWidthPackets Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def intImage (D : Finset ℕ) : Finset ℤ := D.image Nat.cast

lemma mem_intImage {D : Finset ℕ} {a : ℕ} : (a : ℤ)∈intImage D ↔ a∈D := by
  simp [intImage]

lemma intImage_nonneg {D : Finset ℕ} {a : ℤ} (ha : a∈intImage D) : 0 ≤ a := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  positivity

lemma intImage_pairCount (D E : Finset ℕ) (q : ℕ) :
    pairCount (intImage D) (intImage E) (q : ℤ)=Erdos66NatPairAlgebra.pairs D E q := by
  rw [pairCount,Erdos66NatPairAlgebra.pairs_eq_filter]
  apply Finset.card_bij (fun a _ ↦ a.toNat)
  · intro a ha
    obtain ⟨ha,hb⟩ := Finset.mem_filter.mp ha
    obtain ⟨b,hbD,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c,hcE,hc⟩ := Finset.mem_image.mp hb
    have he : b+c=q := by omega
    exact Finset.mem_filter.mpr ⟨by simpa using hbD,by omega,by simpa [show q-b=c by omega] using hcE⟩
  · intro a ha b hb he
    have ha0 := intImage_nonneg (Finset.mem_filter.mp ha).1
    have hb0 := intImage_nonneg (Finset.mem_filter.mp hb).1
    omega
  · intro a ha
    obtain ⟨haD,haq,hb⟩ := Finset.mem_filter.mp ha
    refine ⟨(a : ℤ),Finset.mem_filter.mpr ⟨mem_intImage.mpr haD,?_⟩,by simp⟩
    rw [←Int.ofNat_sub haq]
    exact mem_intImage.mpr hb

lemma intImage_uniform (D : Finset ℕ) (V : ℝ)
    (hD : ∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ V) :
    ∀ z : ℤ, (pairCount (intImage D) (intImage D) z : ℝ) ≤ V := by
  intro z
  have hV : 0 ≤ V := (Nat.cast_nonneg (α := ℝ) (sumRep (D : Set ℕ) 0)).trans (hD 0)
  by_cases hz : 0 ≤ z
  · have hh := intImage_pairCount D D z.toNat
    rw [Int.toNat_of_nonneg hz,Erdos66NatPairAlgebra.pairs_self] at hh
    rw [hh]
    exact hD z.toNat
  · have he : pairCount (intImage D) (intImage D) z=0 := by
      rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      intro a ha hb
      have ha0 := intImage_nonneg ha
      have hb0 := intImage_nonneg hb
      omega
    rw [he,Nat.cast_zero]
    exact hV

lemma pairs_zero_above (D E : Finset ℕ) (L q : ℕ)
    (hD : ∀ a∈D, a ≤ L) (hE : ∀ a∈E, a ≤ L) (hq : 2*L<q) :
    Erdos66NatPairAlgebra.pairs D E q=0 := by
  rw [Erdos66NatPairAlgebra.pairs_eq_filter,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro a ha hb
  have h₁ := hD a ha
  have h₂ := hE (q-a) hb.2
  omega

/-- Global labelled Sidon control and global mixed control, with all new
points in the same finite natural interval as the old set. -/
theorem exists_natural_labeled_packets (D : Finset ℕ) (L W : ℕ) (hW : 0<W)
    (hD : D ⊆ Finset.range (L+1)) (V : ℝ)
    (hu : ∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ V) (n : ι → ℕ)
    (hn : ∀ i, 12*W+48 ≤ n i ∧ n i ≤ L) (R t : ℝ) (hR : 0<R) (ht : 0<t)
    (hsmall : ((2*(Fintype.card ι : ℝ))^2+(2*(Fintype.card ι : ℝ))^4)/W+
      (Fintype.card ι : ℝ)*(2*Real.sqrt (2*(W : ℝ)*V))/W+
      (2*(L : ℝ)+1)*Real.exp (Real.exp t*((Fintype.card ι : ℝ)*(2*Real.sqrt (2*(W : ℝ)*V))/W)-t*R) < 1) :
    ∃ d : Label ι → ℕ, Function.Injective d ∧
      (∀ u, d u ≤ L ∧ d u∉D) ∧
      (∀ i, d (i,false)+d (i,true)=n i) ∧
      (∀ u v w s : Label ι, ¬Designated u v → ¬Designated w s →
        d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w)) ∧
      (∀ q, (Erdos66NatPairAlgebra.pairs (Finset.univ.image d) D q : ℝ) < 2*R) := by
  let N : ι → ℤ := fun i ↦ (n i : ℤ)
  let a : ι → ℤ := fun i ↦ (n i/3 : ℕ)
  let T : Finset ℤ := Finset.Icc 0 (2*(L : ℤ))
  have hT : (T.card : ℝ)=2*(L : ℝ)+1 := by
    have hh : T.card=2*L+1 := by dsimp [T]; rw [Int.card_Icc]; omega
    rw [hh]; push_cast; ring
  have hsmall' := hsmall
  rw [←hT] at hsmall'
  obtain ⟨ω,hinj,havoid,hunique,hmixed⟩ := exists_uniform_width_packets (intImage D) V
    (intImage_uniform D V hu) N a W hW T R t ht hsmall'
  let x : ι → ℤ := fun i ↦ a i+(ω i).val
  have hp (u : Label ι) : 0 ≤ point N x u ∧ point N x u ≤ (L : ℤ) := by
    obtain ⟨i,b⟩ := u
    have hn' := hn i
    have hi := (ω i).isLt
    have ha : n i/3+(ω i).val ≤ n i := by omega
    have ha' : ((n i/3 : ℕ) : ℤ)+(ω i).val ≤ (n i : ℤ) := by exact_mod_cast ha
    cases b <;> simp only [point,Bool.false_eq_true,if_false,if_true,N,x,a] <;> constructor <;> omega
  let d : Label ι → ℕ := fun u ↦ (point N x u).toNat
  have hd (u : Label ι) : (d u : ℤ)=point N x u := Int.toNat_of_nonneg (hp u).1
  have hdL (u : Label ι) : d u ≤ L := by
    have hh := (hp u).2
    rw [←hd u] at hh
    exact_mod_cast hh
  have hdAvoid (u : Label ι) : d u∉D := by
    intro hu
    have hh : point N x u∈intImage D := by rw [←hd u]; exact mem_intImage.mpr hu
    obtain ⟨i,b⟩ := u
    cases b
    · exact (havoid i).1 hh
    · exact (havoid i).2 hh
  have hdi : Function.Injective d := by
    intro u v he
    apply hinj
    rw [←hd u,←hd v,he]
  have himage : intImage (Finset.univ.image d)=packet N x := by
    unfold intImage packet
    rw [Finset.image_image]
    apply Finset.image_congr
    intro u hu
    exact hd u
  refine ⟨d,hdi,(fun u ↦ ⟨hdL u,hdAvoid u⟩),?_,?_,?_⟩
  · intro i
    have hh := point_designated N x (u := (i,false)) (v := (i,true)) (by simp [Designated])
    rw [←hd (i,false),←hd (i,true)] at hh
    dsimp only [N,Prod.fst] at hh
    exact_mod_cast hh
  · intro u v w s huv hws he
    apply hunique u v w s huv hws
    have hh : (d u : ℤ)+d v=(d w : ℤ)+d s := by exact_mod_cast he
    simpa only [hd] using hh
  · intro q
    by_cases hq : q ≤ 2*L
    · have hqT : (q : ℤ)∈T := by dsimp [T]; simp only [Finset.mem_Icc]; constructor <;> omega
      have hh := hmixed (q : ℤ) hqT
      rw [←himage,intImage_pairCount] at hh
      exact hh
    · rw [pairs_zero_above _ D L q (by
        intro a ha
        obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
        exact hdL u) (fun a ha ↦ by have hh := Finset.mem_range.mp (hD ha); omega) (by omega),Nat.cast_zero]
      linarith

end Erdos66NaturalLabeledPackets
