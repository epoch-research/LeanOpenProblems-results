import Submission.SidonSelectionExplore
import Submission.NatPairAlgebraExplore

/-! Extracting a small Sidon subset from an arbitrary large finite set. -/
namespace Erdos66NaturalSidonExtraction
open AdditiveCombinatorics Erdos66SidonSelection Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 1200000

def NatSidon (A : Finset ℕ) : Prop :=
  ∀ a∈A, ∀ b∈A, ∀ c∈A, ∀ d∈A, a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

lemma natSidon_rep_le_two {A : Finset ℕ} (hA : NatSidon A) (n : ℕ) :
    sumRep (A : Set ℕ) n≤2 := by
  rw [←pairs_self,pairs_eq_filter]
  let F := A.filter (fun a ↦ a≤n ∧ n-a∈A)
  change F.card≤2
  by_cases hF : F.Nonempty
  · obtain ⟨a,ha⟩ := hF
    obtain ⟨haA,han,hna⟩ := Finset.mem_filter.mp ha
    have hsub : F⊆{a,n-a} := by
      intro b hb
      obtain ⟨hbA,hbn,hnb⟩ := Finset.mem_filter.mp hb
      have hh := hA b hbA (n-b) hnb a haA (n-a) hna (by omega)
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]

theorem exists_natSidon_subset (E : Finset ℕ) (m : ℕ) (hcard : m^4<E.card) :
    ∃ F : Finset ℕ, F⊆E ∧ F.card=m ∧ NatSidon F := by
  have hE : E.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty E := ⟨⟨hE.choose,hE.choose_spec⟩⟩
  let x : E→ℤ := fun a ↦ (a.val : ℤ)
  have hx : Function.Injective x := by
    intro a b he
    apply Subtype.ext
    dsimp [x] at he
    exact_mod_cast he
  have hsmall : ((Fintype.card (Fin m) : ℝ)^4+Fintype.card (Fin m)*(∅ : Finset E).card)/Fintype.card E +
      (∅ : Finset Unit).card*Real.exp ((Fintype.card (Fin m) : ℝ)*Real.exp 1*0/Fintype.card E-1*0)<1 := by
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero,zero_mul,add_zero,
      Fintype.card_fin,Fintype.card_coe]
    apply (div_lt_one (by exact_mod_cast (show 0<E.card by omega))).mpr
    exact_mod_cast hcard
  obtain ⟨ω,hω,_,hsidon,_⟩ := exists_sidon_avoid_and_hits (ι := Fin m)
    x hx ∅ (∅ : Finset Unit) (fun _ ↦ (∅ : Finset E)) 0 0 1 (by simp) (by norm_num) hsmall
  let F := Finset.univ.image (fun i : Fin m ↦ (ω i).val)
  have hωval : Function.Injective (fun i : Fin m ↦ (ω i).val) :=
    Subtype.val_injective.comp hω
  refine ⟨F,?_,?_,?_⟩
  · intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact (ω i).property
  · dsimp [F]
    rw [Finset.card_image_of_injective _ hωval,Finset.card_univ,Fintype.card_fin]
  · intro a ha b hb c hc d hd he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hd
    have hh := hsidon i j k l (by dsimp [x]; exact_mod_cast he)
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

noncomputable def natReflect (t : ℕ) (E : Finset ℕ) : Finset ℕ :=
  E.image (fun a ↦ t-a)

lemma natReflect_sidon {E : Finset ℕ} (hE : NatSidon E) (t : ℕ)
    (ht : ∀a∈E, a≤t) : NatSidon (natReflect t E) := by
  intro a ha b hb c hc d hd he
  simp only [natReflect,Finset.mem_image] at ha hb hc hd
  obtain ⟨a,haE,rfl⟩ := ha
  obtain ⟨b,hbE,rfl⟩ := hb
  obtain ⟨c,hcE,rfl⟩ := hc
  obtain ⟨d,hdE,rfl⟩ := hd
  have ha' := ht a haE
  have hb' := ht b hbE
  have hc' := ht c hcE
  have hd' := ht d hdE
  have hh := hE a haE b hbE c hcE d hdE (by omega)
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

lemma natReflect_mixed (E : Finset ℕ) (t : ℕ) (ht : ∀a∈E, a≤t) :
    pairs E (natReflect t E) t=E.card := by
  rw [pairs_eq_filter]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro a ha
  exact ⟨ht a ha,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩

end Erdos66NaturalSidonExtraction
