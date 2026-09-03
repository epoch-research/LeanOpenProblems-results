import Submission.NearbyCovarianceBlocks

/-! Assembly of independently kernel-checked finite cover counts. Classical
outer filters prevent accidental evaluation of the entire long period while
the short-block certificates remain fully computable. -/
namespace Erdos970.GapAverages.NearbyExample
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option Elab.async false

lemma card_filter_range_blocks (p : ℕ → Prop) [DecidablePred p] (n m r : ℕ) :
    ((range (n*m+r)).filter p).card =
      (∑ b ∈ range m, ((range n).filter (fun a => p (n*b+a))).card) +
        ((range r).filter (fun a => p (n*m+a))).card := by
  rw [card_filter,sum_range_add,sum_blocks]
  simp only [sum_boole,Nat.cast_id]

noncomputable def classicalCount (n b : ℕ) : ℕ :=
  (@Finset.filter ℕ (fun a => CyclicSieve.natCount primes 7 (b+a) = 0)
    (fun _ => Classical.propDecidable _) (range n)).card

noncomputable def coverCount (n : ℕ) : ℕ :=
  (@Finset.filter ℕ (fun a => CyclicSieve.natCount primes 7 a = 0)
    (fun _ => Classical.propDecidable _) (range n)).card

lemma classicalCount_eq (n b : ℕ) : classicalCount n b =
    ((range n).filter (fun a => CyclicSieve.natCount primes 7 (b+a) = 0)).card := by
  unfold classicalCount
  congr 2

lemma classical_block (b : ℕ) : classicalCount 100 (100*b) = blockCount b := by
  exact classicalCount_eq 100 (100*b)

lemma cover_count_certificate : coverCount 15015 = 36 := by
  classical
  have hc := @card_filter_range_blocks (fun a => CyclicSieve.natCount primes 7 a = 0)
    (fun _ => Classical.propDecidable _) 100 150 15
  change coverCount 15015 =
    (∑ b ∈ range 150, classicalCount 100 (100*b)) + classicalCount 15 15000 at hc
  rw [hc]
  have hl : classicalCount 15 15000 = 0 := (classicalCount_eq 15 15000).trans last_block
  rw [hl]
  let f : ℕ → ℕ := fun b => ([1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1] : List ℕ).getD b 0
  have he : (∑ b ∈ range 150, classicalCount 100 (100*b)) = ∑ b ∈ range 150, f b := by
    apply sum_congr rfl
    intro b hb
    rw [classical_block]
    have hb' : b < 150 := mem_range.mp hb
    interval_cases b
    · exact block_000
    · exact block_001
    · exact block_002
    · exact block_003
    · exact block_004
    · exact block_005
    · exact block_006
    · exact block_007
    · exact block_008
    · exact block_009
    · exact block_010
    · exact block_011
    · exact block_012
    · exact block_013
    · exact block_014
    · exact block_015
    · exact block_016
    · exact block_017
    · exact block_018
    · exact block_019
    · exact block_020
    · exact block_021
    · exact block_022
    · exact block_023
    · exact block_024
    · exact block_025
    · exact block_026
    · exact block_027
    · exact block_028
    · exact block_029
    · exact block_030
    · exact block_031
    · exact block_032
    · exact block_033
    · exact block_034
    · exact block_035
    · exact block_036
    · exact block_037
    · exact block_038
    · exact block_039
    · exact block_040
    · exact block_041
    · exact block_042
    · exact block_043
    · exact block_044
    · exact block_045
    · exact block_046
    · exact block_047
    · exact block_048
    · exact block_049
    · exact block_050
    · exact block_051
    · exact block_052
    · exact block_053
    · exact block_054
    · exact block_055
    · exact block_056
    · exact block_057
    · exact block_058
    · exact block_059
    · exact block_060
    · exact block_061
    · exact block_062
    · exact block_063
    · exact block_064
    · exact block_065
    · exact block_066
    · exact block_067
    · exact block_068
    · exact block_069
    · exact block_070
    · exact block_071
    · exact block_072
    · exact block_073
    · exact block_074
    · exact block_075
    · exact block_076
    · exact block_077
    · exact block_078
    · exact block_079
    · exact block_080
    · exact block_081
    · exact block_082
    · exact block_083
    · exact block_084
    · exact block_085
    · exact block_086
    · exact block_087
    · exact block_088
    · exact block_089
    · exact block_090
    · exact block_091
    · exact block_092
    · exact block_093
    · exact block_094
    · exact block_095
    · exact block_096
    · exact block_097
    · exact block_098
    · exact block_099
    · exact block_100
    · exact block_101
    · exact block_102
    · exact block_103
    · exact block_104
    · exact block_105
    · exact block_106
    · exact block_107
    · exact block_108
    · exact block_109
    · exact block_110
    · exact block_111
    · exact block_112
    · exact block_113
    · exact block_114
    · exact block_115
    · exact block_116
    · exact block_117
    · exact block_118
    · exact block_119
    · exact block_120
    · exact block_121
    · exact block_122
    · exact block_123
    · exact block_124
    · exact block_125
    · exact block_126
    · exact block_127
    · exact block_128
    · exact block_129
    · exact block_130
    · exact block_131
    · exact block_132
    · exact block_133
    · exact block_134
    · exact block_135
    · exact block_136
    · exact block_137
    · exact block_138
    · exact block_139
    · exact block_140
    · exact block_141
    · exact block_142
    · exact block_143
    · exact block_144
    · exact block_145
    · exact block_146
    · exact block_147
    · exact block_148
    · exact block_149
  rw [he]
  change (∑ b ∈ range 150, f b) + 0 = 36
  decide +kernel

#print axioms cover_count_certificate
end Erdos970.GapAverages.NearbyExample
