import Submission.SixRepresentativeCertificates2_000

namespace Erdos184Work.SixRepresentativeCertificates2
open PureSixRowModel2 LabelKernel Erdos184Serial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificates (r : Representatives) : Certificate r := by
  fin_cases r
  · exact certificate0
  · exact certificate1
  · exact certificate2
  · exact certificate3
  · exact certificate4
  · exact certificate5
  · exact certificate6
  · exact certificate7
  · exact certificate8
  · exact certificate9
lemma exists_two_of_upper (r : Representatives)
    (hu : ∀ P, Partition (code (src (unkey (representativeKey r)))
      (dst (unkey (representativeKey r)))) Finset.univ P → P.card ≤ 6) :
    r ∈ good ∧ ∃ P, Partition (code (src (unkey (representativeKey r)))
      (dst (unkey (representativeKey r)))) Finset.univ P ∧ P.card = 2 := by
  obtain ⟨D,hd,hs⟩ := certificates r
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition hd
  have hh := hu P hP
  have hz : D.size ≤ 6 := by omega
  obtain ⟨he,hg⟩ := hs hz
  exact ⟨hg,P,hP,hcP.trans he⟩
#print axioms exists_two_of_upper
end Erdos184Work.SixRepresentativeCertificates2
