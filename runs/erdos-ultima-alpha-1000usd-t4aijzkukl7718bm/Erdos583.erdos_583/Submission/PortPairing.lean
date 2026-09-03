import Submission.Work

/-! Separating two pairings by label-preserving port switches. -/
namespace Erdos583PortPairingDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

noncomputable def badPorts {P : Type*} [Fintype P] (F J : Equiv.Perm P) : Finset P := by
  classical
  exact Finset.univ.filter (fun p ↦ J p=F p)

@[simp] lemma mem_badPorts {P : Type*} [Fintype P] (F J : Equiv.Perm P) (p : P) :
    p ∈ badPorts F J ↔ J p=F p := by
  classical
  simp [badPorts]

/-- Switching one end of a common pair with a third port destroys that common
pair and creates no new common pairs. The third port must not be its partner. -/
lemma switch_bad_pair {P : Type*} [Fintype P] [DecidableEq P]
    (F J : Equiv.Perm P) (hF : Function.Involutive F) (hJ : Function.Involutive J)
    (hFn : ∀ p, F p ≠ p) (hJn : ∀ p, J p ≠ p)
    (p t : P) (htp : t ≠ p) (htq : t ≠ F p) (hp : J p=F p) :
    badPorts F ((Equiv.swap p t)*J*(Equiv.swap p t)) ⊂ badPorts F J := by
  classical
  let q := F p
  let r := J t
  let τ := Equiv.swap p t
  let K := τ*J*τ
  have hqp : q ≠ p := hFn p
  have hqt : q ≠ t := htq.symm
  have hrp : r ≠ p := by
    intro hh
    have h := congrArg J hh
    rw [hJ t,hp] at h
    exact htq h
  have hrt : r ≠ t := hJn t
  have hrq : r ≠ q := by
    intro hh
    apply htp
    exact J.injective (hh.trans hp.symm)
  have hJq : J q=p := by change J (F p)=p; rw [←hp]; exact hJ p
  have hJr : J r=t := hJ t
  have hτp : τ p=t := Equiv.swap_apply_left _ _
  have hτt : τ t=p := Equiv.swap_apply_right _ _
  have hτq : τ q=q := Equiv.swap_apply_of_ne_of_ne hqp hqt
  have hτr : τ r=r := Equiv.swap_apply_of_ne_of_ne hrp hrt
  have hJp : J p=q := hp
  have hJt : J t=r := rfl
  have hKp : K p=r := by change τ (J (τ p))=r; rw [hτp,hJt,hτr]
  have hKt : K t=q := by change τ (J (τ t))=q; rw [hτt,hJp,hτq]
  have hKq : K q=t := by change τ (J (τ q))=t; rw [hτq,hJq,hτp]
  have hKr : K r=p := by change τ (J (τ r))=p; rw [hτr,hJr,hτt]
  have hnp : K p ≠ F p := by rw [hKp]; exact hrq
  have hnt : K t ≠ F t := by
    rw [hKt]
    intro hh
    exact htp (F.injective hh.symm)
  have hnq : K q ≠ F q := by
    rw [hKq]
    change t ≠ F (F p)
    rw [hF p]
    exact htp
  have hnr : K r ≠ F r := by
    rw [hKr]
    intro hh
    have he := congrArg F hh
    rw [hF r] at he
    exact hrq he.symm
  have hsub : badPorts F K ⊆ badPorts F J := by
    intro w hw
    have hw' := (mem_badPorts F K w).mp hw
    have hwp : w ≠ p := by rintro rfl; exact hnp hw'
    have hwt : w ≠ t := by rintro rfl; exact hnt hw'
    have hwq : w ≠ q := by rintro rfl; exact hnq hw'
    have hwr : w ≠ r := by rintro rfl; exact hnr hw'
    have hJwp : J w ≠ p := by
      intro hh
      have h := congrArg J hh
      rw [hJ w,hp] at h
      exact hwq h
    have hJwt : J w ≠ t := by
      intro hh
      have h := congrArg J hh
      rw [hJ w] at h
      exact hwr h
    have he : K w=J w := by simp only [K,τ,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hwp hwt,Equiv.swap_apply_of_ne_of_ne hJwp hJwt]
    apply (mem_badPorts F J w).mpr
    rwa [he] at hw'
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  have hpmem : p ∈ badPorts F K := he.symm ▸ (mem_badPorts F J p).mpr hp
  exact hnp ((mem_badPorts F K p).mp hpmem)

/-- Two pairings can be separated by permuting ports within label classes,
provided every pair of the fixed pairing has different labels and at least
one of those two label classes has another port. -/
lemma separate_pairings {P V : Type*} [Fintype P]
    (F J : Equiv.Perm P) (hF : Function.Involutive F) (hJ : Function.Involutive J)
    (hFn : ∀ p, F p ≠ p) (hJn : ∀ p, J p ≠ p)
    (label : P → V) (hlabels : ∀ p, label (F p) ≠ label p)
    (hroom : ∀ p, (∃ t, t ≠ p ∧ label t=label p) ∨
      (∃ t, t ≠ F p ∧ label t=label (F p))) :
    ∃ σ : Equiv.Perm P, (∀ p, label (σ p)=label p) ∧
      ∀ p, (σ*J*σ⁻¹) p ≠ F p := by
  classical
  let L : Finset (Equiv.Perm P) := Finset.univ.filter (fun σ ↦ ∀ p, label (σ p)=label p)
  have hL : L.Nonempty := ⟨1,by simp [L]⟩
  obtain ⟨σ,hσ,hmin⟩ := L.exists_min_image (fun σ ↦ (badPorts F (σ*J*σ⁻¹)).card) hL
  have hσlabel : ∀ p, label (σ p)=label p := (Finset.mem_filter.mp hσ).2
  let K := σ*J*σ⁻¹
  have hK : Function.Involutive K := by
    intro p
    change σ (J (σ.symm (σ (J (σ.symm p)))))=p
    rw [Equiv.symm_apply_apply,hJ,Equiv.apply_symm_apply]
  have hKn (p : P) : K p ≠ p := by
    intro hp
    have he := congrArg (fun x ↦ σ⁻¹ x) hp
    change σ.symm (σ (J (σ.symm p)))=σ.symm p at he
    rw [Equiv.symm_apply_apply] at he
    exact hJn _ he
  have hbad (p t : P) (hp : K p=F p) (ht : t ≠ p) (hlt : label t=label p) : False := by
    have htq : t ≠ F p := by
      rintro rfl
      exact hlabels p hlt
    let τ := Equiv.swap p t
    let σ' := τ*σ
    have hσ' : σ' ∈ L := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro w
      change label (τ (σ w))=label w
      rw [Equiv.apply_swap_eq_self hlt.symm (σ w),hσlabel]
    have hident : σ'*J*σ'⁻¹ = τ*K*τ := by
      dsimp [σ',K]
      rw [mul_inv_rev,show τ⁻¹=τ from Equiv.swap_inv _ _]
      simp only [mul_assoc]
    have hltcard := Finset.card_lt_card (switch_bad_pair F K hF hK hFn hKn p t ht htq hp)
    have hbound := hmin σ' hσ'
    rw [hident] at hbound
    change (badPorts F K).card ≤ (badPorts F (Equiv.swap p t*K*Equiv.swap p t)).card at hbound
    exact (Nat.not_lt_of_ge hbound) hltcard
  refine ⟨σ,hσlabel,?_⟩
  intro p hp
  change K p=F p at hp
  rcases hroom p with ⟨t,ht,hlt⟩ | ⟨t,ht,hlt⟩
  · exact hbad p t hp ht hlt
  · have hq : K (F p)=F (F p) := by
      calc
        K (F p)=K (K p) := congrArg K hp.symm
        _ = p := hK p
        _ = F (F p) := (hF p).symm
    exact hbad (F p) t hq ht hlt

/-- An injective assignment of vertex labels to incident boundary objects rules
out a fixed pair whose two label classes are both singletons. -/
lemma room_of_incident_matching {P V B : Type*}
    (F : P → P) (label : P → V) (owner : P → B)
    (howner : ∀ p, owner (F p)=owner p)
    (hlabels : ∀ p, label (F p) ≠ label p)
    (m : V → B) (hm : Function.Injective m)
    (hincident : ∀ v, ∃ t, owner t=m v ∧ label t=v) (p : P) :
    (∃ t, t ≠ p ∧ label t=label p) ∨
      (∃ t, t ≠ F p ∧ label t=label (F p)) := by
  classical
  by_cases hp : ∃ t, t ≠ p ∧ label t=label p
  · exact Or.inl hp
  obtain ⟨s,hsOwner,hsLabel⟩ := hincident (label p)
  have hs : s=p := by
    by_contra hne
    exact hp ⟨s,hne,hsLabel⟩
  obtain ⟨t,htOwner,htLabel⟩ := hincident (label (F p))
  refine Or.inr ⟨t,?_,htLabel⟩
  intro ht
  rw [hs] at hsOwner
  have he : m (label (F p))=m (label p) :=
    htOwner.symm.trans ((congrArg owner ht).trans ((howner p).trans hsOwner))
  exact hlabels p (hm he)

lemma separate_pairings_of_matching {P V B : Type*} [Fintype P]
    (F J : Equiv.Perm P) (hF : Function.Involutive F) (hJ : Function.Involutive J)
    (hFn : ∀ p, F p ≠ p) (hJn : ∀ p, J p ≠ p)
    (label : P → V) (owner : P → B)
    (howner : ∀ p, owner (F p)=owner p)
    (hlabels : ∀ p, label (F p) ≠ label p)
    (m : V → B) (hm : Function.Injective m)
    (hincident : ∀ v, ∃ t, owner t=m v ∧ label t=v) :
    ∃ σ : Equiv.Perm P, (∀ p, label (σ p)=label p) ∧
      ∀ p, (σ*J*σ⁻¹) p ≠ F p :=
  separate_pairings F J hF hJ hFn hJn label hlabels
    (room_of_incident_matching F label owner howner hlabels m hm hincident)

end Erdos583PortPairingDevelopment
