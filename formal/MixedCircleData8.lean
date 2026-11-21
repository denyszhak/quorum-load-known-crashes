import MixedCircleRow8_001
import MixedCircleRow8_002
import MixedCircleRow8_003
import MixedCircleRow8_004
import MixedCircleRow8_005
import MixedCircleRow8_006
import MixedCircleRow8_007
import MixedCircleRow8_008
import MixedCircleRow8_009
import MixedCircleRow8_010
import MixedCircleRow8_011
import MixedCircleRow8_012
import MixedCircleRow8_013
import MixedCircleRow8_014
import MixedCircleRow8_015
import MixedCircleRow8_016
import MixedCircleRow8_017
import MixedCircleRow8_018
import MixedCircleRow8_019
import MixedCircleRow8_020
import MixedCircleRow8_021
import MixedCircleRow8_022
import MixedCircleRow8_023
import MixedCircleRow8_024
import MixedCircleRow8_025
import MixedCircleRow8_026
import MixedCircleRow8_027
import MixedCircleRow8_028
import MixedCircleRow8_029
import MixedCircleRow8_030
import MixedCircleRow8_031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificates8 : List CircleCertificate := [certificate_8_1, certificate_8_2, certificate_8_3, certificate_8_4, certificate_8_5, certificate_8_6, certificate_8_7, certificate_8_8, certificate_8_9, certificate_8_10, certificate_8_11, certificate_8_12, certificate_8_13, certificate_8_14, certificate_8_15, certificate_8_16, certificate_8_17, certificate_8_18, certificate_8_19, certificate_8_20, certificate_8_21, certificate_8_22, certificate_8_23, certificate_8_24, certificate_8_25, certificate_8_26, certificate_8_27, certificate_8_28, certificate_8_29, certificate_8_30, certificate_8_31]

theorem certificates8_valid : ∀ c ∈ certificates8, c.Valid 63 8 := by
  intro c hc
  simp only [certificates8, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_8_1_valid
  · exact certificate_8_2_valid
  · exact certificate_8_3_valid
  · exact certificate_8_4_valid
  · exact certificate_8_5_valid
  · exact certificate_8_6_valid
  · exact certificate_8_7_valid
  · exact certificate_8_8_valid
  · exact certificate_8_9_valid
  · exact certificate_8_10_valid
  · exact certificate_8_11_valid
  · exact certificate_8_12_valid
  · exact certificate_8_13_valid
  · exact certificate_8_14_valid
  · exact certificate_8_15_valid
  · exact certificate_8_16_valid
  · exact certificate_8_17_valid
  · exact certificate_8_18_valid
  · exact certificate_8_19_valid
  · exact certificate_8_20_valid
  · exact certificate_8_21_valid
  · exact certificate_8_22_valid
  · exact certificate_8_23_valid
  · exact certificate_8_24_valid
  · exact certificate_8_25_valid
  · exact certificate_8_26_valid
  · exact certificate_8_27_valid
  · exact certificate_8_28_valid
  · exact certificate_8_29_valid
  · exact certificate_8_30_valid
  · exact certificate_8_31_valid

theorem certificates8_coverage :
    ∀ d ∈ Finset.Ico 1 (63 / 2 + 1), ∃ c ∈ certificates8, c.failed = {0, d} := by decide +kernel

#print axioms certificates8_valid
#print axioms certificates8_coverage
end QuorumAudit.MixedCircle
