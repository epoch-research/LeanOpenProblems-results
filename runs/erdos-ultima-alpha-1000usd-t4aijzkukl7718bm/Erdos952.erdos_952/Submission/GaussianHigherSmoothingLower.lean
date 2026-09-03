import Submission.GaussianIteratedSmoothing
import Submission.GaussianSmoothedPathCounts

/-! A lower bound for smoothing with two additional independent finite
samples. A finite bucket partition yields a polynomial, rather than
exponential, loss when the number of buckets is polynomial. The concrete
bucket partition must be supplied by the application. -/
namespace Erdos952Investigation.GaussianHigherSmoothingLower
open GaussianIdealBoxCounts GaussianIteratedSmoothing FiniteSampleSmoothing
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

abbrev SameCell {Ω I : Type*} (c : Ω → I) := {s : Ω × Ω // c s.1 = c s.2}

def sameCellEquiv {Ω I : Type*} (c : Ω → I) :
    SameCell c ≃ Σ i : I, {s : Ω // c s = i} × {s : Ω // c s = i} where
  toFun s := ⟨c s.val.1,⟨s.val.1,rfl⟩,⟨s.val.2,s.property.symm⟩⟩
  invFun s := ⟨(s.2.1.val,s.2.2.val),s.2.1.property.trans s.2.2.property.symm⟩
  left_inv s := rfl
  right_inv s := by
    rcases s with ⟨i,⟨u,hu⟩,⟨v,hv⟩⟩
    subst i
    rfl

/-- At least a 1/|I| fraction of ordered sample pairs have equal buckets. -/
theorem sameCell_card {Ω I : Type*} [Fintype Ω] [Fintype I] (c : Ω → I) :
    (Fintype.card Ω)^2 ≤ Fintype.card I*Nat.card (SameCell c) := by
  have hm := Nat.card_congr (Equiv.sigmaFiberEquiv c)
  rw [Nat.card_sigma,Nat.card_eq_fintype_card] at hm
  have hc : Nat.card (SameCell c) = ∑ i : I, (Nat.card {s : Ω // c s = i})^2 := by
    rw [Nat.card_congr (sameCellEquiv c),Nat.card_sigma]
    simp only [Nat.card_prod,pow_two]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun _ => (1 : ℕ)) (fun i => Nat.card {s : Ω // c s = i})
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hm,← hc] using hh

abbrev KernelSample (Ω : Type*) (a : GaussianInt) (R : ℕ) :=
  (Box a R × Box 0 R) × (Ω × Ω)

def kernelValue {Ω : Type*} (f : Ω → GaussianInt) (a : GaussianInt) (R : ℕ)
    (s : KernelSample Ω a R) : GaussianInt :=
  s.1.1.val-s.1.2.val+f s.2.1-f s.2.2

def kernelCount {Ω : Type*} [Fintype Ω] (f : Ω → GaussianInt)
    (p : GaussianInt → Prop) (a : GaussianInt) (R : ℕ) : ℝ :=
  (Nat.card {s : KernelSample Ω a R // p (kernelValue f a R s)} : ℝ)/
    ((R : ℝ)^2*(Fintype.card Ω : ℝ)^2)

/-- Smoothing by differences of independent samples loses at most the
number of buckets, provided a bucket has coordinate diameter at most T. -/
theorem enclosed_finset_le_kernel {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (f : Ω → GaussianInt) (c : Ω → I) (E : Finset GaussianInt) (p : GaussianInt → Prop)
    (a : GaussianInt) (T : ℕ) (hT : 0 < T)
    (hp : ∀ z ∈ E, p z)
    (hbox : ∀ z ∈ E, |z.re-a.re| ≤ (T : ℤ) ∧ |z.im-a.im| ≤ (T : ℤ))
    (hcell : ∀ s t, c s = c t →
      |(f s).re-(f t).re| ≤ (T : ℤ) ∧ |(f s).im-(f t).im| ≤ (T : ℤ)) :
    (E.card : ℝ) ≤ 25*(Fintype.card I : ℝ)*kernelCount f p a (5*T) := by
  let H : GaussianInt := ⟨2*T,2*T⟩
  let F : (E × Box 0 T) × SameCell c →
      {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} := fun q =>
    ⟨((⟨q.1.1.val-f q.2.val.1+f q.2.val.2+H+q.1.2.val,by
      have hz := hbox q.1.1.val q.1.1.property
      have hc := hcell q.2.val.1 q.2.val.2 q.2.property
      have hzr := abs_le.mp hz.1
      have hzi := abs_le.mp hz.2
      have hcr := abs_le.mp hc.1
      have hci := abs_le.mp hc.2
      have hw := q.1.2.property
      dsimp [InBox] at hw
      dsimp [InBox,H]
      omega⟩,
      ⟨H+q.1.2.val,by
      have hw := q.1.2.property
      dsimp [InBox] at hw
      dsimp [InBox,H]
      omega⟩),q.2.val),by
      change p (q.1.1.val-f q.2.val.1+f q.2.val.2+H+q.1.2.val-
        (H+q.1.2.val)+f q.2.val.1-f q.2.val.2)
      have he : q.1.1.val-f q.2.val.1+f q.2.val.2+H+q.1.2.val-
          (H+q.1.2.val)+f q.2.val.1-f q.2.val.2 = q.1.1.val := by abel
      rw [he]
      exact hp q.1.1.val q.1.1.property⟩
  have hF : Function.Injective F := by
    intro u v he
    have hz := congrArg (fun s : {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} =>
      kernelValue f a (5*T) s.val) he
    have hw := congrArg (fun s : {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} =>
      s.val.1.2.val) he
    have hc := congrArg (fun s : {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} =>
      s.val.2) he
    change u.2.val = v.2.val at hc
    change H+u.1.2.val = H+v.1.2.val at hw
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        dsimp [F,kernelValue] at hz
        linear_combination hz
      · exact Subtype.ext (add_left_cancel hw)
    · exact Subtype.ext hc
  have hcount := Nat.card_le_card_of_injective F hF
  have hE : Nat.card E = E.card := by simp
  rw [Nat.card_prod,Nat.card_prod,hE,box_card] at hcount
  have hcoll := sameCell_card c
  have hn : E.card*T^2*(Fintype.card Ω)^2 ≤
      Fintype.card I*Nat.card {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} := by
    calc
      _ ≤ E.card*T^2*(Fintype.card I*Nat.card (SameCell c)) := Nat.mul_le_mul_left _ hcoll
      _ = Fintype.card I*(E.card*T^2*Nat.card (SameCell c)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hcount
  have hn' : (E.card : ℝ)*((T : ℝ)^2*(Fintype.card Ω : ℝ)^2) ≤
      (Fintype.card I : ℝ)*(Nat.card {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} : ℝ) := by
    exact_mod_cast (by simpa only [mul_assoc] using hn)
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hden : 0 < (T : ℝ)^2*(Fintype.card Ω : ℝ)^2 := by positivity
  have he : 25*(Fintype.card I : ℝ)*kernelCount f p a (5*T) =
      ((Fintype.card I : ℝ)*(Nat.card {s : KernelSample Ω a (5*T) // p (kernelValue f a (5*T) s)} : ℝ))/
        ((T : ℝ)^2*(Fintype.card Ω : ℝ)^2) := by
    dsimp [kernelCount]
    push_cast
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ hden).mpr hn'

#print axioms sameCell_card
#print axioms enclosed_finset_le_kernel
end
end Erdos952Investigation.GaussianHigherSmoothingLower
