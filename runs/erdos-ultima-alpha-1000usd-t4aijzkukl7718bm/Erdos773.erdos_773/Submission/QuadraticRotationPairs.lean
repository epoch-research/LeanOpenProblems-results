import Submission.QuadraticRotationTrade

/-! Complete classification of formal pair-square sums in the 3-4-5 trade. -/
namespace Erdos773.QuadraticRotationTrade
open Finset MvPolynomial
set_option maxHeartbeats 2500000
noncomputable section

lemma core_injective {n : ℕ} {a b : Fin n} (h : value (.core a)=value (.core b)) : a=b := by
  have hh := core_pair (a := a) (b := a) (c := b) (d := b) (by rw [h])
  tauto

lemma plus_pair {n : ℕ} {a b c d : Edge n}
    (h : value (.plus a)+value (.plus b)=value (.plus c)+value (.plus d)) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply delta_pair
  intro x
  have hh := congrArg (probe x) h
  simp only [probe_add, probe_plus] at hh
  linarith only [hh]

lemma minus_pair {n : ℕ} {a b c d : Edge n}
    (h : value (.minus a)+value (.minus b)=value (.minus c)+value (.minus d)) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply delta_pair
  intro x
  have hh := congrArg (probe x) h
  simp only [probe_add, probe_minus] at hh
  linarith only [hh]

lemma core_plus {n : ℕ} {a c : Fin n} {b d : Edge n}
    (h : value (.core a)+value (.plus b)=value (.core c)+value (.plus d)) :
    a=c ∧ b=d := by
  have he : b=d := by
    apply delta_injective
    intro x
    have hh := congrArg (probe x) h
    simp only [probe_add, probe_plus, probe_core] at hh
    linarith only [hh]
  subst d
  exact ⟨core_injective (add_right_cancel h), rfl⟩

lemma core_minus {n : ℕ} {a c : Fin n} {b d : Edge n}
    (h : value (.core a)+value (.minus b)=value (.core c)+value (.minus d)) :
    a=c ∧ b=d := by
  have he : b=d := by
    apply delta_injective
    intro x
    have hh := congrArg (probe x) h
    simp only [probe_add, probe_minus, probe_core] at hh
    linarith only [hh]
  subst d
  exact ⟨core_injective (add_right_cancel h), rfl⟩

lemma edge_core_pair {n : ℕ} {e f : Edge n}
    (h : value (.core e.val.1)+value (.core e.val.2)=
      value (.core f.val.1)+value (.core f.val.2)) : e=f := by
  rcases core_pair h with ⟨h₁,h₂⟩ | hs
  · exact Subtype.ext (Prod.ext h₁ h₂)
  · exact (edge_swap_impossible e f hs).elim

lemma plus_minus {n : ℕ} {a b c d : Edge n}
    (h : value (.plus a)+value (.minus b)=value (.plus c)+value (.minus d)) :
    a=c ∧ b=d := by
  have hh : ∀ x, delta x a-delta x b=delta x c-delta x d := by
    intro x
    have ht := congrArg (probe x) h
    simp only [probe_add, probe_minus, probe_plus] at ht
    linarith only [ht]
  rcases delta_difference hh with hd | ⟨hab,hcd⟩
  · exact hd
  · subst b
    subst d
    rw [trade, trade] at h
    exact ⟨edge_core_pair h, edge_core_pair h⟩

lemma core_trade {n : ℕ} {a b : Fin n} {c d : Edge n}
    (h : value (.core a)+value (.core b)=value (.plus c)+value (.minus d)) :
    c=d ∧ ((a=c.val.1 ∧ b=c.val.2) ∨ (a=c.val.2 ∧ b=c.val.1)) := by
  have he : c=d := by
    apply delta_injective
    intro x
    have hh := congrArg (probe x) h
    simp only [probe_add, probe_plus, probe_minus, probe_core] at hh
    linarith only [hh]
  subst d
  exact ⟨rfl, core_pair (by rwa [trade] at h)⟩

/-- Replace each private complementary pair by its two core endpoints. -/
def normal {n : ℕ} (u v : Root n) : Finset (Root n) :=
  match u,v with
  | .plus e, .minus f => if e=f then {.core e.val.1, .core e.val.2} else {u,v}
  | .minus f, .plus e => if e=f then {.core e.val.1, .core e.val.2} else {u,v}
  | _,_ => {u,v}

lemma normal_symm {n : ℕ} (u v : Root n) : normal u v=normal v u := by
  cases u <;> cases v <;> simp [normal, pair_comm]

lemma norm_core_pair {n : ℕ} {a b c d : Fin n}
    (h : value (.core a)+value (.core b)=value (.core c)+value (.core d)) :
    normal (.core a) (.core b)=normal (.core c) (.core d) := by
  rcases core_pair h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [normal, pair_comm]

lemma norm_plus_pair {n : ℕ} {a b c d : Edge n}
    (h : value (.plus a)+value (.plus b)=value (.plus c)+value (.plus d)) :
    normal (.plus a) (.plus b)=normal (.plus c) (.plus d) := by
  rcases plus_pair h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [normal, pair_comm]

lemma norm_minus_pair {n : ℕ} {a b c d : Edge n}
    (h : value (.minus a)+value (.minus b)=value (.minus c)+value (.minus d)) :
    normal (.minus a) (.minus b)=normal (.minus c) (.minus d) := by
  rcases minus_pair h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [normal, pair_comm]

lemma norm_core_plus {n : ℕ} {a c : Fin n} {b d : Edge n}
    (h : value (.core a)+value (.plus b)=value (.core c)+value (.plus d)) :
    normal (.core a) (.plus b)=normal (.core c) (.plus d) := by
  obtain ⟨rfl,rfl⟩ := core_plus h
  rfl

lemma norm_core_minus {n : ℕ} {a c : Fin n} {b d : Edge n}
    (h : value (.core a)+value (.minus b)=value (.core c)+value (.minus d)) :
    normal (.core a) (.minus b)=normal (.core c) (.minus d) := by
  obtain ⟨rfl,rfl⟩ := core_minus h
  rfl

lemma norm_plus_minus {n : ℕ} {a b c d : Edge n}
    (h : value (.plus a)+value (.minus b)=value (.plus c)+value (.minus d)) :
    normal (.plus a) (.minus b)=normal (.plus c) (.minus d) := by
  obtain ⟨rfl,rfl⟩ := plus_minus h
  rfl

lemma norm_core_trade {n : ℕ} {a b : Fin n} {c d : Edge n}
    (h : value (.core a)+value (.core b)=value (.plus c)+value (.minus d)) :
    normal (.core a) (.core b)=normal (.plus c) (.minus d) := by
  obtain ⟨rfl, hh⟩ := core_trade h
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [normal, pair_comm]

def support {n : ℕ} (e : Edge n) : Finset (Root n) :=
  {.core e.val.1, .core e.val.2, .plus e, .minus e}

lemma support_card {n : ℕ} (e : Edge n) : (support e).card=4 := by
  simp [support, ne_of_lt e.property]

/-- Every nontrivial formal square-sum relation is one prescribed rotation trade. -/
theorem pair_classification {n : ℕ} {u v w z : Root n}
    (h : value u+value v=value w+value z) :
    ((u=w ∧ v=z) ∨ (u=z ∧ v=w)) ∨ ∃ e : Edge n, {u,v,w,z}=support e := by
  cases u <;> cases v <;> cases w <;> cases z
  case core.core.core.core a b c d =>
    have hh : value (.core a)+value (.core b)=value (.core c)+value (.core d) := by simpa only [add_comm] using h
    rcases core_pair hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals subst_vars; simp
  case core.core.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.core.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.core.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.core.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.core.plus.minus a b c d =>
    have hh : value (.core a)+value (.core b)=value (.plus c)+value (.minus d) := by simpa only [add_comm] using h
    obtain ⟨he,hc⟩ := core_trade hh
    rcases hc with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals
      refine Or.inr ⟨c, ?_⟩
      ext x
      simp only [support, he, h₁, h₂, mem_insert, mem_singleton]
      all_goals tauto
  case core.core.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.core.minus.plus a b c d =>
    have hh : value (.core a)+value (.core b)=value (.plus d)+value (.minus c) := by simpa only [add_comm] using h
    obtain ⟨he,hc⟩ := core_trade hh
    rcases hc with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals
      refine Or.inr ⟨d, ?_⟩
      ext x
      simp only [support, he, h₁, h₂, mem_insert, mem_singleton]
      all_goals tauto
  case core.core.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.core.plus a b c d =>
    have hh : value (.core a)+value (.plus b)=value (.core c)+value (.plus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_plus hh
    all_goals subst_vars; simp
  case core.plus.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.plus.core a b c d =>
    have hh : value (.core a)+value (.plus b)=value (.core d)+value (.plus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_plus hh
    all_goals subst_vars; simp
  case core.plus.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.plus.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.core.minus a b c d =>
    have hh : value (.core a)+value (.minus b)=value (.core c)+value (.minus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_minus hh
    all_goals subst_vars; simp
  case core.minus.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.minus.core a b c d =>
    have hh : value (.core a)+value (.minus b)=value (.core d)+value (.minus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_minus hh
    all_goals subst_vars; simp
  case core.minus.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case core.minus.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.core.plus a b c d =>
    have hh : value (.core b)+value (.plus a)=value (.core c)+value (.plus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_plus hh
    all_goals subst_vars; simp
  case plus.core.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.plus.core a b c d =>
    have hh : value (.core b)+value (.plus a)=value (.core d)+value (.plus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_plus hh
    all_goals subst_vars; simp
  case plus.core.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.core.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.plus.plus a b c d =>
    have hh : value (.plus a)+value (.plus b)=value (.plus c)+value (.plus d) := by simpa only [add_comm] using h
    rcases plus_pair hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals subst_vars; simp
  case plus.plus.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.plus.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.core.core a b c d =>
    have hh : value (.core c)+value (.core d)=value (.plus a)+value (.minus b) := by simpa only [add_comm] using h.symm
    obtain ⟨he,hc⟩ := core_trade hh
    rcases hc with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals
      refine Or.inr ⟨a, ?_⟩
      ext x
      simp only [support, he, h₁, h₂, mem_insert, mem_singleton]
      all_goals tauto
  case plus.minus.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.plus.minus a b c d =>
    have hh : value (.plus a)+value (.minus b)=value (.plus c)+value (.minus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := plus_minus hh
    all_goals subst_vars; simp
  case plus.minus.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case plus.minus.minus.plus a b c d =>
    have hh : value (.plus a)+value (.minus b)=value (.plus d)+value (.minus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := plus_minus hh
    all_goals subst_vars; simp
  case plus.minus.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.core.minus a b c d =>
    have hh : value (.core b)+value (.minus a)=value (.core c)+value (.minus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_minus hh
    all_goals subst_vars; simp
  case minus.core.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.minus.core a b c d =>
    have hh : value (.core b)+value (.minus a)=value (.core d)+value (.minus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := core_minus hh
    all_goals subst_vars; simp
  case minus.core.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.core.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.core.core a b c d =>
    have hh : value (.core c)+value (.core d)=value (.plus b)+value (.minus a) := by simpa only [add_comm] using h.symm
    obtain ⟨he,hc⟩ := core_trade hh
    rcases hc with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals
      refine Or.inr ⟨b, ?_⟩
      ext x
      simp only [support, he, h₁, h₂, mem_insert, mem_singleton]
      all_goals tauto
  case minus.plus.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.plus.minus a b c d =>
    have hh : value (.plus b)+value (.minus a)=value (.plus c)+value (.minus d) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := plus_minus hh
    all_goals subst_vars; simp
  case minus.plus.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.plus.minus.plus a b c d =>
    have hh : value (.plus b)+value (.minus a)=value (.plus d)+value (.minus c) := by simpa only [add_comm] using h
    obtain ⟨h₁,h₂⟩ := plus_minus hh
    all_goals subst_vars; simp
  case minus.plus.minus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.core.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.core.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.core.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.plus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.plus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.plus.minus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.minus.core a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.minus.plus a b c d =>
    have ht := congrArg (eval (fun _ => (1:ℚ))) h
    norm_num at ht
  case minus.minus.minus.minus a b c d =>
    have hh : value (.minus a)+value (.minus b)=value (.minus c)+value (.minus d) := by simpa only [add_comm] using h
    rcases minus_pair hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    all_goals subst_vars; simp

lemma value_injective {n : ℕ} : Function.Injective (value (n := n)) := by
  intro u v h
  rcases pair_classification (u := u) (v := u) (w := v) (z := v)
    (by rw [h]) with hh | ⟨e, he⟩
  · tauto
  · have hc : ({u,u,v,v} : Finset (Root n)).card ≤ 2 := by
      simpa using card_le_two (a := u) (b := v)
    rw [he, support_card] at hc
    omega

#print axioms support_card
#print axioms pair_classification
#print axioms value_injective
#print axioms plus_minus
#print axioms core_trade
end
end Erdos773.QuadraticRotationTrade
