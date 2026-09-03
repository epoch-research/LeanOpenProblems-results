import Submission.SeriesSupportTransport

/-! Support transport along nonempty coordinate fibers. Saturation of valid
supports is the precise condition needed for exact circuit-partition transport. -/
open scoped Classical
namespace Erdos184Serial.Fiber
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {E F : Type*} [DecidableEq E] [DecidableEq F] [Fintype F]
variable (q : F → E)

def expand (s : Finset E) : Finset F := Finset.univ.filter (fun f => q f ∈ s)

@[simp] lemma mem_expand (s : Finset E) (f : F) : f ∈ expand q s ↔ q f ∈ s := by simp [expand]

noncomputable def transport (C : Code E) (B : Code F)
    (hq : Function.Surjective q)
    (hv : ∀ s, B.valid (expand q s) ↔ C.valid s)
    (hsat : ∀ t, B.valid t → ∀ f g, q f = q g → (f ∈ t ↔ g ∈ t)) :
    SupportTransport C B where
  expand := expand q
  empty := by ext f; simp
  union s t := by ext f; simp
  subset s t := by
    constructor
    · intro h e he
      obtain ⟨f,rfl⟩ := hq e
      exact (mem_expand q t f).mp (h ((mem_expand q s f).mpr he))
    · intro h f hf
      exact (mem_expand q t f).mpr (h ((mem_expand q s f).mp hf))
  disjoint s t := by
    simp only [Finset.disjoint_left,mem_expand]
    constructor
    · intro h e hs ht
      obtain ⟨f,rfl⟩ := hq e
      exact h hs ht
    · intro h f hs ht
      exact h hs ht
  valid := hv
  lift _ t _ ht := by
    refine ⟨t.image q,?_⟩
    ext f
    simp only [mem_expand,Finset.mem_image]
    constructor
    · rintro ⟨g,hg,he⟩
      exact (hsat t ht g f he).mp hg
    · intro hf
      exact ⟨f,hf,rfl⟩

#print axioms transport
end Erdos184Serial.Fiber
