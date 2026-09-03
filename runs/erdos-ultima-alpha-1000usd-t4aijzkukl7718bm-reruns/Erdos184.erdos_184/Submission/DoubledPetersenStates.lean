import Submission.DoubledPetersenTours

/-! Completeness certificate for the binary even edge states of Petersen. -/
namespace Erdos184
namespace DoubledPetersenCertificate

def incident : Fin 10 → Fin 3 → Fin 15 :=
  ![![0,1,2],![0,3,4],![3,5,6],![5,7,8],![1,7,9],![2,10,11],![4,12,13],![6,10,14],![8,11,12],![9,13,14]]

def cycleMask : Fin 57 → ℕ :=
  ![171,15021,18093,2349,20267,13099,29997,1101,3531,15947,16971,19405,29131,30797,5493,21363,4499,22421,6165,7411,24083,8723,9973,11157,24819,26997,25621,28051,6334,25790,1254,30950,2438,5598,30086,11070,9822,14182,14854,23134,19302,17926,8888,24248,27960,4408,12248,7256,21464,24664,16096,17120,3424,29024,13184,20352,31744]

def twoFactorMask : Fin 6 → ℕ :=
  ![12147,14285,22334,23285,27102,31915]

def bit (m : ℕ) (e : Fin 15) : ℕ := m / 2 ^ e.val % 2

def maskDegree (m : ℕ) (v : Fin 10) : ℕ :=
  bit m (incident v 0) + bit m (incident v 1) + bit m (incident v 2)

def EvenMask (m : ℕ) : Prop := ∀ v : Fin 10, maskDegree m v % 2 = 0

lemma incident_complete (v : Fin 10) (e : Fin 15) :
    (∃ i : Fin 3, incident v i = e) ↔ v = (ends e).1 ∨ v = (ends e).2 := by
  revert v e; decide

lemma incident_injective (v : Fin 10) : Function.Injective (incident v) := by
  revert v; decide

lemma cycleMask_digits (i : Fin 57) (e : Fin 15) :
    bit (cycleMask i) e = digit ⟨i.val,by omega⟩ e := by revert i e; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma evenMask_checked : ∀ a : Fin 128, ∀ b : Fin 256,
    EvenMask (a.val * 256 + b.val) →
      a.val * 256 + b.val = 0 ∨
      (∃ i : Fin 57, a.val * 256 + b.val = cycleMask i) ∨
      (∃ i : Fin 6, a.val * 256 + b.val = twoFactorMask i) := by
  unfold EvenMask
  decide +kernel

lemma evenMask_classification (m : ℕ) (hm : m < 32768) (he : EvenMask m) :
    m = 0 ∨ (∃ i : Fin 57, m = cycleMask i) ∨
      (∃ i : Fin 6, m = twoFactorMask i) := by
  have ha : m / 256 < 128 := by omega
  have hb : m % 256 < 256 := Nat.mod_lt _ (by decide)
  have heq : m / 256 * 256 + m % 256 = m := by omega
  simpa only [heq] using evenMask_checked ⟨m/256,ha⟩ ⟨m%256,hb⟩ (by simpa only [heq] using he)

end DoubledPetersenCertificate
end Erdos184
