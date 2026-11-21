import MixedCircleRow9_001
import MixedCircleRow9_002
import MixedCircleRow9_003
import MixedCircleRow9_004
import MixedCircleRow9_005
import MixedCircleRow9_006
import MixedCircleRow9_007
import MixedCircleRow9_008
import MixedCircleRow9_009
import MixedCircleRow9_010
import MixedCircleRow9_011
import MixedCircleRow9_012
import MixedCircleRow9_013
import MixedCircleRow9_014
import MixedCircleRow9_015
import MixedCircleRow9_016
import MixedCircleRow9_017
import MixedCircleRow9_018
import MixedCircleRow9_019
import MixedCircleRow9_020
import MixedCircleRow9_021
import MixedCircleRow9_022
import MixedCircleRow9_023
import MixedCircleRow9_024
import MixedCircleRow9_025
import MixedCircleRow9_026
import MixedCircleRow9_027
import MixedCircleRow9_028
import MixedCircleRow9_029
import MixedCircleRow9_030
import MixedCircleRow9_031
import MixedCircleRow9_032
import MixedCircleRow9_033
import MixedCircleRow9_034
import MixedCircleRow9_035
import MixedCircleRow9_036
import MixedCircleRow9_037
import MixedCircleRow9_038
import MixedCircleRow9_039
import MixedCircleRow9_040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificates9 : List CircleCertificate := [certificate_9_1, certificate_9_2, certificate_9_3, certificate_9_4, certificate_9_5, certificate_9_6, certificate_9_7, certificate_9_8, certificate_9_9, certificate_9_10, certificate_9_11, certificate_9_12, certificate_9_13, certificate_9_14, certificate_9_15, certificate_9_16, certificate_9_17, certificate_9_18, certificate_9_19, certificate_9_20, certificate_9_21, certificate_9_22, certificate_9_23, certificate_9_24, certificate_9_25, certificate_9_26, certificate_9_27, certificate_9_28, certificate_9_29, certificate_9_30, certificate_9_31, certificate_9_32, certificate_9_33, certificate_9_34, certificate_9_35, certificate_9_36, certificate_9_37, certificate_9_38, certificate_9_39, certificate_9_40]

theorem certificates9_valid : ∀ c ∈ certificates9, c.Valid 80 9 := by
  intro c hc
  simp only [certificates9, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_9_1_valid
  · exact certificate_9_2_valid
  · exact certificate_9_3_valid
  · exact certificate_9_4_valid
  · exact certificate_9_5_valid
  · exact certificate_9_6_valid
  · exact certificate_9_7_valid
  · exact certificate_9_8_valid
  · exact certificate_9_9_valid
  · exact certificate_9_10_valid
  · exact certificate_9_11_valid
  · exact certificate_9_12_valid
  · exact certificate_9_13_valid
  · exact certificate_9_14_valid
  · exact certificate_9_15_valid
  · exact certificate_9_16_valid
  · exact certificate_9_17_valid
  · exact certificate_9_18_valid
  · exact certificate_9_19_valid
  · exact certificate_9_20_valid
  · exact certificate_9_21_valid
  · exact certificate_9_22_valid
  · exact certificate_9_23_valid
  · exact certificate_9_24_valid
  · exact certificate_9_25_valid
  · exact certificate_9_26_valid
  · exact certificate_9_27_valid
  · exact certificate_9_28_valid
  · exact certificate_9_29_valid
  · exact certificate_9_30_valid
  · exact certificate_9_31_valid
  · exact certificate_9_32_valid
  · exact certificate_9_33_valid
  · exact certificate_9_34_valid
  · exact certificate_9_35_valid
  · exact certificate_9_36_valid
  · exact certificate_9_37_valid
  · exact certificate_9_38_valid
  · exact certificate_9_39_valid
  · exact certificate_9_40_valid

theorem certificates9_coverage :
    ∀ d ∈ Finset.Ico 1 (80 / 2 + 1), ∃ c ∈ certificates9, c.failed = {0, d} := by decide +kernel

#print axioms certificates9_valid
#print axioms certificates9_coverage
end QuorumAudit.MixedCircle
