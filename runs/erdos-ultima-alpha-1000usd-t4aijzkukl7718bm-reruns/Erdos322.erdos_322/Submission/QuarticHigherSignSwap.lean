import Submission.QuarticHuaBox

/-! The second-moment sign-swapping identity does not extend to all higher
moments. This is an obstruction to that proof step, not to the conjecture. -/
namespace Erdos322Research.QuarticHigherSignSwap

open QuarticHuaBox
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The collision moment of a map on a finite domain. -/
def finiteMoment {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) (q : ℕ) : ℕ :=
  ∑ t ∈ S.image f, ((S.filter (fun a => f a=t)).card)^q

lemma finiteMoment_two {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) : finiteMoment S f 2=FiniteCollisionEnergy.energy S f := by
  classical
  symm
  unfold finiteMoment
  convert FiniteCollisionEnergy.energy_eq_sum S f (S.image f)
    (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) using 1
  congr 1
  funext t
  congr 2
  ext a
  simp only [Finset.mem_filter]

/-- The sign-swap identity remains valid at order two, for every box. -/
theorem second_moment_sign_swap (B : ℕ) :
    finiteMoment Finset.univ (@quadValue B) 2=
      finiteMoment Finset.univ (@signedValue B) 2 := by
  rw [finiteMoment_two,finiteMoment_two,signed_energy_eq]
  rfl

theorem positive_sixth_moment : finiteMoment Finset.univ (@quadValue 4) 6 = 227263876 := by
  decide

theorem signed_sixth_moment : finiteMoment Finset.univ (@signedValue 4) 6 = 208277476 := by
  decide

/-- Even the comparison in the proposed direction fails, not only equality. -/
theorem sixth_moment_sign_swap_fails :
    ¬ finiteMoment Finset.univ (@quadValue 4) 6 ≤
      finiteMoment Finset.univ (@signedValue 4) 6 := by
  rw [positive_sixth_moment,signed_sixth_moment]
  omega

end Erdos322Research.QuarticHigherSignSwap
