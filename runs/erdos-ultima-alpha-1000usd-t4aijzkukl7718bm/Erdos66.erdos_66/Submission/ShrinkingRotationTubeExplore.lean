import Submission.RotationMassLogBoundExplore
import Submission.PatternInsertionDominationExplore
import Submission.DiscreteRotationMassExplore

/-! A single shrinking rotation window has large representation spikes.
This is a restricted construction obstruction, not a disproof of Erdős 66. -/
namespace Erdos66ShrinkingRotationTube
open AdditiveCombinatorics Erdos66RotationFloorPerturbation
  Erdos66RotationMassLogBound Erdos66PatternInsertionDomination
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def tube (α : ℝ) (p : ℕ → ℝ) : Set ℕ :=
  {n | Int.fract ((n : ℝ)*α) ≤ p n}

lemma floor_window (x θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((⌊x⌋-⌊x-θ⌋ : ℤ) : ℝ) = if Int.fract x < θ then 1 else 0 := by
  have hx := Int.fract_nonneg x
  have hx1 := Int.fract_lt_one x
  have he : x-θ=(⌊x⌋ : ℝ)+(Int.fract x-θ) := by
    have := Int.floor_add_fract x
    linarith
  rw [he,Int.floor_intCast_add]
  by_cases h : Int.fract x < θ
  · have hf : ⌊Int.fract x-θ⌋=(-1 : ℤ) := Int.floor_eq_iff.mpr (by
      norm_num
      constructor <;> linarith)
    simp [hf,h]
  · have hf : ⌊Int.fract x-θ⌋=(0 : ℤ) := Int.floor_eq_iff.mpr (by
      norm_num
      constructor <;> linarith)
    simp [hf,h]

lemma rotationSum_eq_card (α x θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (N : ℕ) :
    rotationSum α x θ N =
      (((Finset.range N).filter (fun k : ℕ ↦ Int.fract (x+(k : ℝ)*α)<θ)).card : ℝ) := by
  simp only [rotationSum,floor_window _ _ hθ hθ1]
  simp

lemma fract_add_small (x y : ℝ) (hy : 0 ≤ y) (hxy : Int.fract x+y<1) :
    Int.fract (x+y)=Int.fract x+y := by
  apply Int.fract_eq_iff.mpr
  refine ⟨add_nonneg (Int.fract_nonneg x) hy,hxy,⌊x⌋,?_⟩
  have := Int.self_sub_fract x
  linarith

lemma fract_sub_ordered (x y : ℝ) (hyx : Int.fract y ≤ Int.fract x) :
    Int.fract (x-y)=Int.fract x-Int.fract y := by
  apply Int.fract_eq_iff.mpr
  refine ⟨sub_nonneg.mpr hyx,?_,⌊x⌋-⌊y⌋,?_⟩
  · linarith [Int.fract_lt_one x,Int.fract_nonneg y]
  · push_cast
    linarith [Int.self_sub_fract x,Int.self_sub_fract y]

/-- A target lying halfway inside the common window admits every endpoint
in the lower half of that window as a representation. -/
lemma tube_rep_lower (α : ℝ) (p : ℕ → ℝ) (n : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : ∀ k ≤ n, θ ≤ p k)
    (hnlo : θ/2 ≤ Int.fract ((n : ℝ)*α))
    (hnhi : Int.fract ((n : ℝ)*α) ≤ θ) :
    rotationSum α 0 (θ/2) (n+1) ≤ (sumRep (tube α p) n : ℝ) := by
  rw [rotationSum_eq_card α 0 (θ/2) (by linarith) (by linarith)]
  rw [← repEndpoints_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a ha
  obtain ⟨haN,haf⟩ := Finset.mem_filter.mp ha
  have ha : a ≤ n := by have := Finset.mem_range.mp haN; omega
  simp only [zero_add] at haf
  have hdiff : Int.fract (((n-a : ℕ) : ℝ)*α)=
      Int.fract ((n : ℝ)*α)-Int.fract ((a : ℝ)*α) := by
    rw [Nat.cast_sub ha,sub_mul]
    exact fract_sub_ordered _ _ (by linarith)
  change a ∈ (Finset.range (n+1)).filter _
  refine Finset.mem_filter.mpr ⟨haN,?_⟩
  change Int.fract ((a : ℝ)*α) ≤ p a ∧
    Int.fract (((n-a : ℕ) : ℝ)*α) ≤ p (n-a)
  constructor
  · linarith [hp a ha]
  · rw [hdiff]
    linarith [hp (n-a) (Nat.sub_le _ _),Int.fract_nonneg ((a : ℝ)*α)]

/-- An unconditional finite spike bound for the slope sqrt(2). The common
window can be chosen after the horizon. -/
theorem exists_finite_tube_spike (p : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (θ : ℝ) (hθ : 0<θ) (hθ1 : θ ≤ 1)
    (hp : ∀ k ≤ 2*N, θ ≤ p k)
    (hmass : 30+50*Real.log ((N : ℝ)*θ/2+1)<(N : ℝ)*θ/2) :
    ∃ n : ℕ, N ≤ n ∧ n<2*N ∧
      (N : ℝ)*θ/2-(30+50*Real.log (2*(N : ℝ)*θ+1)) ≤
        (sumRep (tube (Real.sqrt 2) p) n : ℝ) := by
  have hrot := rotation_mass_log_bound (Real.sqrt 2) N (by simp) N le_rfl
    ((N : ℝ)*Real.sqrt 2-θ/2) (θ/2) (by positivity)
  have hpos : 0 < rotationSum (Real.sqrt 2) ((N : ℝ)*Real.sqrt 2-θ/2) (θ/2) N := by
    have := (abs_le.mp hrot).1
    rw [mul_div_assoc] at hmass
    linarith
  rw [rotationSum_eq_card _ _ _ (by positivity) (by linarith)] at hpos
  have hcard : 0 < ((Finset.range N).filter (fun k : ℕ ↦
      Int.fract ((N : ℝ)*Real.sqrt 2-θ/2+(k : ℝ)*Real.sqrt 2)<θ/2)).card := by
    exact_mod_cast hpos
  obtain ⟨k,hk⟩ := Finset.card_pos.mp hcard
  obtain ⟨hkN,hkf⟩ := Finset.mem_filter.mp hk
  have hklt := Finset.mem_range.mp hkN
  let n := N+k
  have hnlo : N ≤ n := by omega
  have hnhi : n<2*N := by omega
  have hphase : Int.fract ((n : ℝ)*Real.sqrt 2)=
      Int.fract ((N : ℝ)*Real.sqrt 2-θ/2+(k : ℝ)*Real.sqrt 2)+θ/2 := by
    have he : (n : ℝ)*Real.sqrt 2=
        ((N : ℝ)*Real.sqrt 2-θ/2+(k : ℝ)*Real.sqrt 2)+θ/2 := by
      dsimp [n]
      push_cast
      ring
    rw [he]
    exact fract_add_small _ _ (by positivity) (by linarith)
  have hrep := tube_rep_lower (Real.sqrt 2) p n θ hθ.le hθ1
    (fun a ha ↦ hp a (by omega)) (by rw [hphase]; linarith [Int.fract_nonneg ((N : ℝ)*Real.sqrt 2-θ/2+(k : ℝ)*Real.sqrt 2)])
    (by rw [hphase]; linarith)
  have hrot' := rotation_mass_log_bound (Real.sqrt 2) (n+1) (by simp) (n+1) le_rfl
    0 (θ/2) (by positivity)
  have hlog : Real.log (((n+1 : ℕ) : ℝ)*(θ/2)+1) ≤
      Real.log (2*(N : ℝ)*θ+1) := by
    apply Real.log_le_log (by positivity)
    have hnR : (n : ℝ)+1 ≤ 2*(N : ℝ) := by exact_mod_cast (show n+1 ≤ 2*N by omega)
    push_cast
    nlinarith
  have hNR : (N : ℝ) ≤ n := by exact_mod_cast hnlo
  refine ⟨n,hnlo,hnhi,?_⟩
  have hh := (abs_le.mp hrot').1
  push_cast at hh hlog
  nlinarith

/-- Once the common window has sufficiently large expected mass, its
representation spike is a fixed fraction of that mass. -/
theorem exists_uniform_spike_threshold :
    ∃ T : ℝ, 0<T ∧ ∀ (p : ℕ → ℝ) (N : ℕ), 1 ≤ N →
      ∀ θ : ℝ, 0<θ → θ ≤ 1 → (∀ k ≤ 2*N, θ ≤ p k) →
      2*T ≤ (N : ℝ)*θ →
      ∃ n : ℕ, N ≤ n ∧ n<2*N ∧
        (N : ℝ)*θ/4 ≤ (sumRep (tube (Real.sqrt 2) p) n : ℝ) := by
  obtain ⟨T,hT,hbound⟩ :=
    Erdos66DiscreteRotationMass.exists_mass_error_threshold (1/16) (by norm_num)
  refine ⟨T,hT,?_⟩
  intro p N hN θ hθ hθ1 hp hmass
  have hx : T ≤ (N : ℝ)*θ/2 := by linarith
  have hsmall := hbound _ hx
  have hbig := hbound (2*(N : ℝ)*θ) (by nlinarith)
  obtain ⟨n,hnlo,hnhi,hnrep⟩ := exists_finite_tube_spike p N hN θ hθ hθ1 hp
    (by nlinarith)
  exact ⟨n,hnlo,hnhi,by nlinarith⟩

end Erdos66ShrinkingRotationTube
