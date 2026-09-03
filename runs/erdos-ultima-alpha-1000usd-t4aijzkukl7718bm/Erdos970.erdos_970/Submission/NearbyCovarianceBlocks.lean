import Submission.CyclicSieveCount

/-! A finite, kernel-checked cover-count certificate for five odd primes.
The count is split into short blocks to bound kernel reduction memory. -/
namespace Erdos970.GapAverages.NearbyExample
open Finset ParityDiscrepancy
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

def primes : Finset ℕ := {3,5,7,11,13}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]
lemma prime_product : primeProduct primes = 15015 := by norm_num [primeProduct,primes]

def blockCount (b : ℕ) : ℕ :=
  ((range 100).filter (fun a => CyclicSieve.natCount primes 7 (100*b+a) = 0)).card

lemma block_000 : blockCount 0 = 1 := by decide +kernel
lemma block_001 : blockCount 1 = 0 := by decide +kernel
lemma block_002 : blockCount 2 = 0 := by decide +kernel
lemma block_003 : blockCount 3 = 0 := by decide +kernel
lemma block_004 : blockCount 4 = 0 := by decide +kernel
lemma block_005 : blockCount 5 = 0 := by decide +kernel
lemma block_006 : blockCount 6 = 0 := by decide +kernel
lemma block_007 : blockCount 7 = 0 := by decide +kernel
lemma block_008 : blockCount 8 = 2 := by decide +kernel
lemma block_009 : blockCount 9 = 0 := by decide +kernel
lemma block_010 : blockCount 10 = 0 := by decide +kernel
lemma block_011 : blockCount 11 = 0 := by decide +kernel
lemma block_012 : blockCount 12 = 0 := by decide +kernel
lemma block_013 : blockCount 13 = 0 := by decide +kernel
lemma block_014 : blockCount 14 = 0 := by decide +kernel
lemma block_015 : blockCount 15 = 0 := by decide +kernel
lemma block_016 : blockCount 16 = 0 := by decide +kernel
lemma block_017 : blockCount 17 = 0 := by decide +kernel
lemma block_018 : blockCount 18 = 0 := by decide +kernel
lemma block_019 : blockCount 19 = 1 := by decide +kernel
lemma block_020 : blockCount 20 = 0 := by decide +kernel
lemma block_021 : blockCount 21 = 0 := by decide +kernel
lemma block_022 : blockCount 22 = 0 := by decide +kernel
lemma block_023 : blockCount 23 = 0 := by decide +kernel
lemma block_024 : blockCount 24 = 0 := by decide +kernel
lemma block_025 : blockCount 25 = 0 := by decide +kernel
lemma block_026 : blockCount 26 = 0 := by decide +kernel
lemma block_027 : blockCount 27 = 4 := by decide +kernel
lemma block_028 : blockCount 28 = 0 := by decide +kernel
lemma block_029 : blockCount 29 = 2 := by decide +kernel
lemma block_030 : blockCount 30 = 0 := by decide +kernel
lemma block_031 : blockCount 31 = 0 := by decide +kernel
lemma block_032 : blockCount 32 = 0 := by decide +kernel
lemma block_033 : blockCount 33 = 0 := by decide +kernel
lemma block_034 : blockCount 34 = 0 := by decide +kernel
lemma block_035 : blockCount 35 = 0 := by decide +kernel
lemma block_036 : blockCount 36 = 0 := by decide +kernel
lemma block_037 : blockCount 37 = 0 := by decide +kernel
lemma block_038 : blockCount 38 = 2 := by decide +kernel
lemma block_039 : blockCount 39 = 0 := by decide +kernel
lemma block_040 : blockCount 40 = 0 := by decide +kernel
lemma block_041 : blockCount 41 = 0 := by decide +kernel
lemma block_042 : blockCount 42 = 0 := by decide +kernel
lemma block_043 : blockCount 43 = 0 := by decide +kernel
lemma block_044 : blockCount 44 = 0 := by decide +kernel
lemma block_045 : blockCount 45 = 0 := by decide +kernel
lemma block_046 : blockCount 46 = 2 := by decide +kernel
lemma block_047 : blockCount 47 = 0 := by decide +kernel
lemma block_048 : blockCount 48 = 0 := by decide +kernel
lemma block_049 : blockCount 49 = 0 := by decide +kernel
lemma block_050 : blockCount 50 = 0 := by decide +kernel
lemma block_051 : blockCount 51 = 0 := by decide +kernel
lemma block_052 : blockCount 52 = 0 := by decide +kernel
lemma block_053 : blockCount 53 = 0 := by decide +kernel
lemma block_054 : blockCount 54 = 1 := by decide +kernel
lemma block_055 : blockCount 55 = 0 := by decide +kernel
lemma block_056 : blockCount 56 = 0 := by decide +kernel
lemma block_057 : blockCount 57 = 0 := by decide +kernel
lemma block_058 : blockCount 58 = 0 := by decide +kernel
lemma block_059 : blockCount 59 = 0 := by decide +kernel
lemma block_060 : blockCount 60 = 0 := by decide +kernel
lemma block_061 : blockCount 61 = 0 := by decide +kernel
lemma block_062 : blockCount 62 = 0 := by decide +kernel
lemma block_063 : blockCount 63 = 0 := by decide +kernel
lemma block_064 : blockCount 64 = 2 := by decide +kernel
lemma block_065 : blockCount 65 = 0 := by decide +kernel
lemma block_066 : blockCount 66 = 0 := by decide +kernel
lemma block_067 : blockCount 67 = 0 := by decide +kernel
lemma block_068 : blockCount 68 = 0 := by decide +kernel
lemma block_069 : blockCount 69 = 0 := by decide +kernel
lemma block_070 : blockCount 70 = 0 := by decide +kernel
lemma block_071 : blockCount 71 = 0 := by decide +kernel
lemma block_072 : blockCount 72 = 0 := by decide +kernel
lemma block_073 : blockCount 73 = 0 := by decide +kernel
lemma block_074 : blockCount 74 = 1 := by decide +kernel
lemma block_075 : blockCount 75 = 1 := by decide +kernel
lemma block_076 : blockCount 76 = 0 := by decide +kernel
lemma block_077 : blockCount 77 = 0 := by decide +kernel
lemma block_078 : blockCount 78 = 0 := by decide +kernel
lemma block_079 : blockCount 79 = 0 := by decide +kernel
lemma block_080 : blockCount 80 = 0 := by decide +kernel
lemma block_081 : blockCount 81 = 0 := by decide +kernel
lemma block_082 : blockCount 82 = 0 := by decide +kernel
lemma block_083 : blockCount 83 = 0 := by decide +kernel
lemma block_084 : blockCount 84 = 0 := by decide +kernel
lemma block_085 : blockCount 85 = 1 := by decide +kernel
lemma block_086 : blockCount 86 = 1 := by decide +kernel
lemma block_087 : blockCount 87 = 0 := by decide +kernel
lemma block_088 : blockCount 88 = 0 := by decide +kernel
lemma block_089 : blockCount 89 = 0 := by decide +kernel
lemma block_090 : blockCount 90 = 0 := by decide +kernel
lemma block_091 : blockCount 91 = 0 := by decide +kernel
lemma block_092 : blockCount 92 = 0 := by decide +kernel
lemma block_093 : blockCount 93 = 0 := by decide +kernel
lemma block_094 : blockCount 94 = 0 := by decide +kernel
lemma block_095 : blockCount 95 = 1 := by decide +kernel
lemma block_096 : blockCount 96 = 0 := by decide +kernel
lemma block_097 : blockCount 97 = 0 := by decide +kernel
lemma block_098 : blockCount 98 = 0 := by decide +kernel
lemma block_099 : blockCount 99 = 0 := by decide +kernel
lemma block_100 : blockCount 100 = 0 := by decide +kernel
lemma block_101 : blockCount 101 = 0 := by decide +kernel
lemma block_102 : blockCount 102 = 0 := by decide +kernel
lemma block_103 : blockCount 103 = 2 := by decide +kernel
lemma block_104 : blockCount 104 = 0 := by decide +kernel
lemma block_105 : blockCount 105 = 0 := by decide +kernel
lemma block_106 : blockCount 106 = 0 := by decide +kernel
lemma block_107 : blockCount 107 = 0 := by decide +kernel
lemma block_108 : blockCount 108 = 0 := by decide +kernel
lemma block_109 : blockCount 109 = 0 := by decide +kernel
lemma block_110 : blockCount 110 = 0 := by decide +kernel
lemma block_111 : blockCount 111 = 1 := by decide +kernel
lemma block_112 : blockCount 112 = 1 := by decide +kernel
lemma block_113 : blockCount 113 = 0 := by decide +kernel
lemma block_114 : blockCount 114 = 0 := by decide +kernel
lemma block_115 : blockCount 115 = 0 := by decide +kernel
lemma block_116 : blockCount 116 = 0 := by decide +kernel
lemma block_117 : blockCount 117 = 0 := by decide +kernel
lemma block_118 : blockCount 118 = 0 := by decide +kernel
lemma block_119 : blockCount 119 = 0 := by decide +kernel
lemma block_120 : blockCount 120 = 2 := by decide +kernel
lemma block_121 : blockCount 121 = 0 := by decide +kernel
lemma block_122 : blockCount 122 = 4 := by decide +kernel
lemma block_123 : blockCount 123 = 0 := by decide +kernel
lemma block_124 : blockCount 124 = 0 := by decide +kernel
lemma block_125 : blockCount 125 = 0 := by decide +kernel
lemma block_126 : blockCount 126 = 0 := by decide +kernel
lemma block_127 : blockCount 127 = 0 := by decide +kernel
lemma block_128 : blockCount 128 = 0 := by decide +kernel
lemma block_129 : blockCount 129 = 0 := by decide +kernel
lemma block_130 : blockCount 130 = 1 := by decide +kernel
lemma block_131 : blockCount 131 = 0 := by decide +kernel
lemma block_132 : blockCount 132 = 0 := by decide +kernel
lemma block_133 : blockCount 133 = 0 := by decide +kernel
lemma block_134 : blockCount 134 = 0 := by decide +kernel
lemma block_135 : blockCount 135 = 0 := by decide +kernel
lemma block_136 : blockCount 136 = 0 := by decide +kernel
lemma block_137 : blockCount 137 = 0 := by decide +kernel
lemma block_138 : blockCount 138 = 0 := by decide +kernel
lemma block_139 : blockCount 139 = 0 := by decide +kernel
lemma block_140 : blockCount 140 = 0 := by decide +kernel
lemma block_141 : blockCount 141 = 2 := by decide +kernel
lemma block_142 : blockCount 142 = 0 := by decide +kernel
lemma block_143 : blockCount 143 = 0 := by decide +kernel
lemma block_144 : blockCount 144 = 0 := by decide +kernel
lemma block_145 : blockCount 145 = 0 := by decide +kernel
lemma block_146 : blockCount 146 = 0 := by decide +kernel
lemma block_147 : blockCount 147 = 0 := by decide +kernel
lemma block_148 : blockCount 148 = 0 := by decide +kernel
lemma block_149 : blockCount 149 = 1 := by decide +kernel

lemma last_block :
    ((range 15).filter (fun a => CyclicSieve.natCount primes 7 (15000+a) = 0)).card = 0 := by
  decide +kernel

lemma sum_blocks {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n m : ℕ) :
    (∑ a ∈ range (n*m), f a) = ∑ b ∈ range m, ∑ a ∈ range n, f (n*b+a) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]

end Erdos970.GapAverages.NearbyExample
