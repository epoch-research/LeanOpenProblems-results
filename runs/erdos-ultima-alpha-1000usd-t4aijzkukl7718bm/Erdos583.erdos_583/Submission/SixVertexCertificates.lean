import Submission.SixVertexCheck0
import Submission.SixVertexCheck1
import Submission.SixVertexCheck2
import Submission.SixVertexCheck3
import Submission.SixVertexCheck4
import Submission.SixVertexCheck5
import Submission.SixVertexCheck6
import Submission.SixVertexCheck7
import Submission.SixVertexCheck8
import Submission.SixVertexCheck9
import Submission.SixVertexCheck10
import Submission.SixVertexCheck11
import Submission.SixVertexCheck12
import Submission.SixVertexCheck13
import Submission.SixVertexCheck14
import Submission.SixVertexCheck15
import Submission.SixVertexCheck16
import Submission.SixVertexCheck17
import Submission.SixVertexCheck18
import Submission.SixVertexCheck19
import Submission.SixVertexCheck20
import Submission.SixVertexCheck21
import Submission.SixVertexCheck22
import Submission.SixVertexCheck23
import Submission.SixVertexCheck24
import Submission.SixVertexCheck25
import Submission.SixVertexCheck26
import Submission.SixVertexCheck27
import Submission.SixVertexCheck28
import Submission.SixVertexCheck29
import Submission.SixVertexCheck30
import Submission.SixVertexCheck31

/-! Complete finite residual certificate and its path-decomposition consequence. -/
namespace Erdos583SixVertexCertificatesDevelopment
open SimpleGraph Erdos583Work Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma checked_blocks (h : Fin 128) : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (h.val*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (h.val*256+l.val))) (certificate (h.val*256+l.val)) := by
  fin_cases h
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact checked_9
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
  · exact checked_17
  · exact checked_18
  · exact checked_19
  · exact checked_20
  · exact checked_21
  · exact checked_22
  · exact checked_23
  · exact checked_24
  · exact checked_25
  · exact checked_26
  · exact checked_27
  · exact checked_28
  · exact checked_29
  · exact checked_30
  · exact checked_31
  · exact checked_32
  · exact checked_33
  · exact checked_34
  · exact checked_35
  · exact checked_36
  · exact checked_37
  · exact checked_38
  · exact checked_39
  · exact checked_40
  · exact checked_41
  · exact checked_42
  · exact checked_43
  · exact checked_44
  · exact checked_45
  · exact checked_46
  · exact checked_47
  · exact checked_48
  · exact checked_49
  · exact checked_50
  · exact checked_51
  · exact checked_52
  · exact checked_53
  · exact checked_54
  · exact checked_55
  · exact checked_56
  · exact checked_57
  · exact checked_58
  · exact checked_59
  · exact checked_60
  · exact checked_61
  · exact checked_62
  · exact checked_63
  · exact checked_64
  · exact checked_65
  · exact checked_66
  · exact checked_67
  · exact checked_68
  · exact checked_69
  · exact checked_70
  · exact checked_71
  · exact checked_72
  · exact checked_73
  · exact checked_74
  · exact checked_75
  · exact checked_76
  · exact checked_77
  · exact checked_78
  · exact checked_79
  · exact checked_80
  · exact checked_81
  · exact checked_82
  · exact checked_83
  · exact checked_84
  · exact checked_85
  · exact checked_86
  · exact checked_87
  · exact checked_88
  · exact checked_89
  · exact checked_90
  · exact checked_91
  · exact checked_92
  · exact checked_93
  · exact checked_94
  · exact checked_95
  · exact checked_96
  · exact checked_97
  · exact checked_98
  · exact checked_99
  · exact checked_100
  · exact checked_101
  · exact checked_102
  · exact checked_103
  · exact checked_104
  · exact checked_105
  · exact checked_106
  · exact checked_107
  · exact checked_108
  · exact checked_109
  · exact checked_110
  · exact checked_111
  · exact checked_112
  · exact checked_113
  · exact checked_114
  · exact checked_115
  · exact checked_116
  · exact checked_117
  · exact checked_118
  · exact checked_119
  · exact checked_120
  · exact checked_121
  · exact checked_122
  · exact checked_123
  · exact checked_124
  · exact checked_125
  · exact checked_126
  · exact checked_127

lemma checked (c : BitVec 15) (h : Residual c) :
    Valid (graph c) (certificate c.toNat) := by
  let hi : Fin 128 := ⟨c.toNat/256,by have := c.isLt; omega⟩
  let lo : Fin 256 := ⟨c.toNat%256,Nat.mod_lt _ (by decide)⟩
  have he : hi.val*256+lo.val=c.toNat := by dsimp [hi,lo]; omega
  have hc : BitVec.ofNat 15 c.toNat=c := by simp
  have hh := checked_blocks hi lo
  rw [he,hc] at hh
  exact hh h

lemma residual_partition (G : SimpleGraph (Fin 6))
    (hd : ∀ v, Nat.card (G.neighborSet v)=2 ∨ Nat.card (G.neighborSet v)=4)
    (ht : ∀ v a b, Nat.card (G.neighborSet v)=2 → G.Adj v a →
      G.Adj v b → a ≠ b → G.Adj a b)
    (hn : ∀ v w, G.Adj v w →
      ¬(Nat.card (G.neighborSet v)=2 ∧ Nat.card (G.neighborSet w)=2)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 := by
  obtain ⟨c,rfl⟩ := graph_surjective G
  apply valid_partition (checked c _)
  simpa only [Residual,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
    And.intro hd (And.intro ht hn)

end Erdos583SixVertexCertificatesDevelopment
