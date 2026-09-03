import Submission.GaussianFactorResidues
import Submission.ParityTriangleCount

/-! Finite Gaussian-direction witnesses and a sharp partner-fiber cardinality bound. -/
namespace Erdos773.GaussianIncidentEncoding
open Finset GaussianCollisionFactorization GaussianQuadrantFactor GaussianFactorResidues
set_option maxHeartbeats 2000000
noncomputable section

def gauss (a b : ℕ) : G := ⟨a,b⟩
def normSq (p : ℕ × ℕ) := p.1^2+p.2^2

lemma norm_gauss (a b : ℕ) : (gauss a b).norm=((a^2+b^2:ℕ):ℤ) := by
  classical
  dsimp [gauss]
  rw [Zsqrtd.norm_def]
  push_cast
  ring

lemma gauss_ne_zero {a b : ℕ} (ha : 0<a) : gauss a b ≠ 0 := by
  classical
  intro he
  have hh := congrArg Zsqrtd.re he
  simp [gauss] at hh
  omega

def directions (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (2*N)) ×ˢ (Icc 0 (2*N))).filter (fun p =>
    p.1.Coprime p.2 ∧ p.1%2 ≠ p.2%2 ∧ normSq p ≤ 2*N)

def partners (a N : ℕ) (p : ℕ × ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter (fun b => gauss p.1 p.2 ∣ gauss a b)

lemma mem_directions {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    0<p.1 ∧ p.1.Coprime p.2 ∧ p.1%2 ≠ p.2%2 ∧ normSq p ≤ 2*N := by
  classical
  obtain ⟨hm,hcop,hpar,hN⟩ := mem_filter.mp hp
  simp only [mem_product,mem_Icc] at hm
  exact ⟨by omega,hcop,hpar,hN⟩

lemma direction_coprime {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    IsCoprime (gauss p.1 p.2).re (gauss p.1 p.2).im := by
  classical
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa [gauss] using (mem_directions hp).2.1

lemma partner_mem_modEq {a N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N)
    {b c : ℕ} (hb : b ∈ partners a N p) (hc : c ∈ partners a N p) :
    b ≡ c [MOD normSq p] := by
  classical
  obtain ⟨g,hg⟩ := (mem_filter.mp hb).2
  obtain ⟨g',hg'⟩ := (mem_filter.mp hc).2
  have hb' : gauss a b=g*gauss p.1 p.2 := by simpa only [mul_comm] using hg
  have hc' : gauss a c=g'*gauss p.1 p.2 := by simpa only [mul_comm] using hg'
  have hh := partner_congruence (direction_coprime hp) hc' hb'
  rw [norm_gauss] at hh
  apply Int.natCast_modEq_iff.mp
  exact Int.modEq_iff_dvd.mpr hh

/-- Each fixed Gaussian direction allows at most N/q+1 partners, where q
    is its norm. This is an actual finite cardinality bound. -/
theorem partners_card {a N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    ((partners a N p).card:ℝ)  ≤  (N:ℝ)/normSq p+1 := by
  classical
  have hq : 0<normSq p := by
    classical
    have hu := (mem_directions hp).1
    dsimp [normSq]
    positivity
  rcases (partners a N p).eq_empty_or_nonempty with he | hne
  · rw [he,card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨b,hb⟩ := hne
    have hh := ParityTriangleCount.residue_interval_card_bound (partners a N p)
      0 (N:ℝ) (normSq p) (b%normSq p) hq (by positivity) (fun c hc => ?_)
    · simpa only [sub_zero] using hh
    · refine ⟨partner_mem_modEq hp hc hb,by positivity,?_⟩
      exact_mod_cast (mem_Icc.mp (mem_filter.mp hc).1).2

lemma squareCoords_ordered_injective {c d e f : ℕ} (hcd : c ≤ d) (hef : e ≤ f)
    (he : squareCoords (gauss c d)=squareCoords (gauss e f)) : c=e ∧ d=f := by
  classical
  change ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ)={(e:ℤ)^2,(f:ℤ)^2} at he
  have hcd' : (c:ℤ)^2 ≤ (d:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left hcd 2
  have hef' : (e:ℤ)^2 ≤ (f:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left hef 2
  have hc : (c:ℤ)^2=(e:ℤ)^2 := by
    classical
    have hc : (c:ℤ)^2 ∈ ({(e:ℤ)^2,(f:ℤ)^2}:Finset ℤ) := he ▸ (by simp)
    have he' : (e:ℤ)^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hc he'
    omega
  have hd : (d:ℤ)^2=(f:ℤ)^2 := by
    classical
    have hd : (d:ℤ)^2 ∈ ({(e:ℤ)^2,(f:ℤ)^2}:Finset ℤ) := he ▸ (by simp)
    have hf : (f:ℤ)^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hd hf
    omega
  constructor
  · exact_mod_cast (sq_eq_sq₀ (by positivity : (0:ℤ) ≤ c) (by positivity : (0:ℤ) ≤ e)).mp hc
  · exact_mod_cast (sq_eq_sq₀ (by positivity : (0:ℤ) ≤ d) (by positivity : (0:ℤ) ≤ f)).mp hd

/-- Every bounded equal-square-sum relation has a finite direction witness.
    The norm bound is at most 2N, including all rounding and unit effects. -/
theorem exists_direction {a b c d N : ℕ} (ha : 0<a) (haN : a ≤ N) (hbN : b ≤ N)
    (he : a^2+b^2=c^2+d^2) :
    ∃ p ∈ directions N, ∃ g : G, gauss a b=g*gauss p.1 p.2 ∧
      squareCoords (gauss c d)=squareCoords (g*star (gauss p.1 p.2)) := by
  classical
  have hnorm : (gauss a b).norm=(gauss c d).norm := by rw [norm_gauss,norm_gauss,he]
  obtain ⟨g,h,hz,hr,hi,hcop,hpar,hsmall,hw⟩ := quadrant_factor (gauss_ne_zero ha) hnorm
  let u := h.re.toNat
  let v := h.im.toNat
  have hu : (u:ℤ)=h.re := Int.toNat_of_nonneg hr.le
  have hv : (v:ℤ)=h.im := Int.toNat_of_nonneg hi
  have hh : gauss u v=h := by ext <;> assumption
  have hu0 : 0<u := by exact_mod_cast (hu ▸ hr)
  have hc : u.Coprime v := by
    classical
    have ht := Int.isCoprime_iff_nat_coprime.mp hcop
    rw [← hu,← hv] at ht
    simpa using ht
  have hp : u%2 ≠ v%2 := by
    classical
    rw [← hu,← hv] at hpar
    exact_mod_cast hpar
  have hnormN := norm_height haN hbN hsmall
  have hq : normSq (u,v) ≤ 2*N := by
    classical
    rw [← hh,norm_gauss] at hnormN
    exact_mod_cast hnormN
  have huN : u ≤ 2*N := by dsimp [normSq] at hq; nlinarith
  have hvN : v ≤ 2*N := by dsimp [normSq] at hq; nlinarith
  refine ⟨(u,v),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,huN⟩,
    mem_Icc.mpr ⟨Nat.zero_le _,hvN⟩⟩,hc,hp,hq⟩,g,?_,?_⟩
  · simpa only [hh] using hz
  · simpa only [hh] using hw

#print axioms partners_card
#print axioms squareCoords_ordered_injective
#print axioms exists_direction
end
end Erdos773.GaussianIncidentEncoding
