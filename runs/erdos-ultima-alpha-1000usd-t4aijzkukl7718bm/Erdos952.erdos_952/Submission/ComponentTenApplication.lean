import Submission.ComponentTen

/-! Consequences of the fixed-seed certificate at squared jump bound 10.
None of these assert a certificate for every jump bound. -/
namespace Erdos952Investigation
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma component10_walk_stays (x : ℕ → GaussianInt) (h0 : x 0 = 3)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < 10) :
    ∀ n, InComponent10 (x n) := by
  intro n
  induction n with
  | zero => simpa only [h0] using three_inComponent10
  | succ n ih => exact inComponent10_closed ih (h (n+1)).1 (h n).2

theorem no_injective_component10_walk :
    ¬ ∃ x : ℕ → GaussianInt, x 0 = 3 ∧ Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < 10 := by
  rintro ⟨x,h0,hx,h⟩
  apply Set.infinite_range_of_injective hx
  apply inComponent10_finite.subset
  rintro z ⟨n,rfl⟩
  exact component10_walk_stays x h0 h n

theorem step_bound_gt_ten_from_three (x : ℕ → GaussianInt) (C : ℤ)
    (h0 : x 0 = 3) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) : 10 < C := by
  by_contra hn
  apply no_injective_component10_walk
  exact ⟨x,h0,hx,fun n => ⟨(h n).1,lt_of_lt_of_le (h n).2 (le_of_not_gt hn)⟩⟩

theorem component_certificate_le_ten (C : ℤ) (hC : C ≤ 10) :
    ∃ S : Finset GaussianInt, MoatCertificate C S := by
  obtain ⟨S,hS⟩ := component10_certificate
  refine ⟨S,hS.1,?_⟩
  intro z hz w hw
  exact hS.2 z hz w ⟨hw.1,hw.2.1,hw.2.2.1,lt_of_lt_of_le hw.2.2.2 hC⟩

def component10Point : (Fin 169 × Fin 169) ↪ GaussianInt where
  toFun r := ⟨(r.1 : ℤ)-84,(r.2 : ℤ)-84⟩
  inj' := by
    intro r s he
    have hr := congrArg Zsqrtd.re he
    have hi := congrArg Zsqrtd.im he
    change (r.1 : ℤ)-84 = (s.1 : ℤ)-84 at hr
    change (r.2 : ℤ)-84 = (s.2 : ℤ)-84 at hi
    exact Prod.ext (Fin.ext (Int.natCast_inj.mp (sub_left_injective hr)))
      (Fin.ext (Int.natCast_inj.mp (sub_left_injective hi)))

def certificate10 : Finset GaussianInt :=
  (Finset.univ.filter (fun r : Fin 169 × Fin 169 =>
    InComponent10 (component10Point r))).map component10Point

lemma mem_certificate10_iff (z : GaussianInt) :
    z ∈ certificate10 ↔ InComponent10 z := by
  simp only [certificate10,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact hr
  · intro hz
    obtain ⟨hr0,hr1,hi0,hi1⟩ := inComponent10_coordinate_bound hz
    let r : Fin 169 := ⟨(z.re+84).toNat,by omega⟩
    let s : Fin 169 := ⟨(z.im+84).toNat,by omega⟩
    have he : component10Point (r,s) = z := by
      apply Zsqrtd.ext
      · change ((z.re+84).toNat : ℤ)-84 = z.re
        omega
      · change ((z.im+84).toNat : ℤ)-84 = z.im
        omega
    exact ⟨(r,s),he.symm ▸ hz,he⟩

theorem certificate10_verified : MoatCertificate 10 certificate10 := by
  refine ⟨(mem_certificate10_iff _).mpr three_inComponent10,?_⟩
  intro z hz w hw
  exact (mem_certificate10_iff _).mpr
    (inComponent10_closed ((mem_certificate10_iff _).mp hz) hw.2.1 hw.2.2.2)

#print axioms no_injective_component10_walk
#print axioms step_bound_gt_ten_from_three
#print axioms component_certificate_le_ten
#print axioms certificate10_verified
end Erdos952Investigation
