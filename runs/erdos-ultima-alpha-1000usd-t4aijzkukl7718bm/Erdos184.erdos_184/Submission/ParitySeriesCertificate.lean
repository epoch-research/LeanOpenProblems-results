import Submission.LabelKernelSubdivision
import Submission.FiberSupportTransport

/-! Polynomial-size certificates for exact series expansion between labelled
kernels. Private-vertex links force each fiber to be selected all-or-none;
endpoint parity then identifies the coarse even-support code. -/
open scoped Classical
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {E F W X : Type*} [DecidableEq E] [DecidableEq F]
    [DecidableEq W] [DecidableEq X] [Fintype F]

def parity (src dst : E → W) (s : Finset E) (w : W) : ZMod 2 :=
  ∑ e ∈ s, if src e = w ∨ dst e = w then 1 else 0

lemma parity_eq_card (src dst : E → W) (s : Finset E) (w : W) :
    parity src dst s w = ((s.filter (fun e => src e = w ∨ dst e = w)).card : ZMod 2) :=
  Finset.sum_boole _ _

lemma valid_iff_parity (src dst : E → W) (s : Finset E) :
    (code src dst).valid s ↔ ∀ w, parity src dst s w = 0 := by
  simp only [code,valid,parity_eq_card,ZMod.natCast_eq_zero_iff_even]

structure SeriesCertificate (src dst : E → W) (fineSrc fineDst : F → X) where
  fiber : F → E
  representative : E → F
  fiber_representative : ∀ e, fiber (representative e) = e
  vertex : W ↪ X
  rank : F → ℕ
  parent : F → F
  descent : ∀ f, f = representative (fiber f) ∨
    rank (parent f) < rank f ∧ fiber (parent f) = fiber f ∧
      ∃ x, Finset.univ.filter (fun g => fineSrc g = x ∨ fineDst g = x) = {f,parent f}
  boundary : ∀ e x,
    parity fineSrc fineDst (Finset.univ.filter (fun f => fiber f = e)) x =
      if vertex (src e) = x ∨ vertex (dst e) = x then 1 else 0

namespace SeriesCertificate
variable {src dst : E → W} {fineSrc fineDst : F → X}
    (C : SeriesCertificate src dst fineSrc fineDst)

lemma private_match {t : Finset F} (ht : (code fineSrc fineDst).valid t)
    {f g : F} {x : X}
    (hx : Finset.univ.filter (fun h => fineSrc h = x ∨ fineDst h = x) = {f,g}) :
    f ∈ t ↔ g ∈ t := by
  have hf : t.filter (fun h => fineSrc h = x ∨ fineDst h = x) =
      ({f,g} : Finset F).filter (fun h => h ∈ t) := by
    ext h
    have hh : (fineSrc h = x ∨ fineDst h = x) ↔ h ∈ ({f,g} : Finset F) := by
      rw [← hx]
      simp
    simp only [Finset.mem_filter,hh]
    exact and_comm
  have he := ht x
  rw [hf] at he
  by_cases h0 : f ∈ t <;> by_cases h1 : g ∈ t <;>
    simp [Finset.filter_insert,Finset.filter_singleton,h0,h1] at he ⊢

lemma mem_iff_representative {t : Finset F} (ht : (code fineSrc fineDst).valid t) (f : F) :
    f ∈ t ↔ C.representative (C.fiber f) ∈ t := by
  have main : ∀ r : ℕ, ∀ f : F, C.rank f = r →
      (f ∈ t ↔ C.representative (C.fiber f) ∈ t) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro f hr
      rcases C.descent f with he | ⟨hlt,hfiber,x,hx⟩
      · exact Iff.of_eq (congrArg (fun f => f ∈ t) he)
      · have hm : f ∈ t ↔ C.parent f ∈ t := private_match ht hx
        have hp := ih (C.rank (C.parent f)) (hlt.trans_eq hr) (C.parent f) rfl
        rw [hfiber] at hp
        exact hm.trans hp
  exact main (C.rank f) f rfl

lemma saturated {t : Finset F} (ht : (code fineSrc fineDst).valid t)
    (f g : F) (hfg : C.fiber f = C.fiber g) : f ∈ t ↔ g ∈ t := by
  rw [C.mem_iff_representative ht f,C.mem_iff_representative ht g,hfg]

lemma parity_expand (s : Finset E) (x : X) :
    parity fineSrc fineDst (Fiber.expand C.fiber s) x =
      ∑ e ∈ s, if C.vertex (src e) = x ∨ C.vertex (dst e) = x then (1 : ZMod 2) else 0 := by
  change (∑ f ∈ Finset.univ.filter (fun f => C.fiber f ∈ s),
    if fineSrc f = x ∨ fineDst f = x then (1 : ZMod 2) else 0) = _
  rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ s C.fiber]
  exact Finset.sum_congr rfl (fun e _ => C.boundary e x)

lemma valid_expansion_iff (s : Finset E) :
    (code fineSrc fineDst).valid (Fiber.expand C.fiber s) ↔ (code src dst).valid s := by
  rw [valid_iff_parity,valid_iff_parity]
  constructor
  · intro h w
    have hw := h (C.vertex w)
    rw [C.parity_expand] at hw
    simpa only [C.vertex.injective.eq_iff] using hw
  · intro h x
    rw [C.parity_expand]
    by_cases hx : ∃ w, C.vertex w = x
    · obtain ⟨w,rfl⟩ := hx
      simpa only [C.vertex.injective.eq_iff] using h w
    · apply Finset.sum_eq_zero
      intro e _
      apply if_neg
      rintro (he | he)
      · exact hx ⟨src e,he⟩
      · exact hx ⟨dst e,he⟩

noncomputable def transport : SupportTransport (code src dst) (code fineSrc fineDst) :=
  Fiber.transport C.fiber (code src dst) (code fineSrc fineDst)
    (fun e => ⟨C.representative e,C.fiber_representative e⟩)
    C.valid_expansion_iff (fun _ ht => C.saturated ht)

lemma expand_univ [Fintype E] : C.transport.expand Finset.univ = Finset.univ := by
  ext f
  exact by simp [transport,Fiber.transport,Fiber.expand]

include C in
lemma partition_spectrum_iff [Fintype E] (P : ℕ → Prop) :
    (∃ D, Partition (code fineSrc fineDst) Finset.univ D ∧ P D.card) ↔
      (∃ D, Partition (code src dst) Finset.univ D ∧ P D.card) := by
  have h := C.transport.exists_partition_card_iff Finset.univ P
  rwa [C.expand_univ] at h

include C in
lemma minimalCore_iff [Fintype E] (k : ℕ) :
    MinimalCore (code fineSrc fineDst) Finset.univ k ↔ MinimalCore (code src dst) Finset.univ k := by
  have h := C.transport.minimalCore_iff Finset.univ k
  rwa [C.expand_univ] at h

lemma expand_colors [Fintype E] {K : Type*} [DecidableEq K]
    (color : E → K) (fineColor : F → K) (hc : ∀ f, color (C.fiber f) = fineColor f)
    (A : Finset K) :
    C.transport.expand (Finset.univ.filter (fun e => color e ∈ A)) =
      Finset.univ.filter (fun f => fineColor f ∈ A) := by
  ext f
  change (f ∈ Fiber.expand C.fiber _) ↔ _
  simp only [Fiber.mem_expand,Finset.mem_filter,Finset.mem_univ,true_and,hc]

include C in
lemma partition_spectrum_colors_iff [Fintype E] {K : Type*} [DecidableEq K]
    (color : E → K) (fineColor : F → K) (hc : ∀ f, color (C.fiber f) = fineColor f)
    (A : Finset K) (P : ℕ → Prop) :
    (∃ D, Partition (code fineSrc fineDst) (Finset.univ.filter (fun f => fineColor f ∈ A)) D ∧ P D.card) ↔
      (∃ D, Partition (code src dst) (Finset.univ.filter (fun e => color e ∈ A)) D ∧ P D.card) := by
  have h := C.transport.exists_partition_card_iff (Finset.univ.filter (fun e => color e ∈ A)) P
  rwa [C.expand_colors color fineColor hc A] at h

#print axioms transport
#print axioms partition_spectrum_iff
#print axioms minimalCore_iff
end SeriesCertificate
end Erdos184Work.LabelKernel
