import MixedCircleRow7_001
import MixedCircleRow7_002
import MixedCircleRow7_003
import MixedCircleRow7_004
import MixedCircleRow7_005
import MixedCircleRow7_006
import MixedCircleRow7_007
import MixedCircleRow7_008
import MixedCircleRow7_009
import MixedCircleRow7_010
import MixedCircleRow7_011
import MixedCircleRow7_012
import MixedCircleRow7_013
import MixedCircleRow7_014
import MixedCircleRow7_015
import MixedCircleRow7_016
import MixedCircleRow7_017
import MixedCircleRow7_018
import MixedCircleRow7_019
import MixedCircleRow7_020
import MixedCircleRow7_021
import MixedCircleRow7_022
import MixedCircleRow7_023
import MixedCircleRow7_024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificates7 : List CircleCertificate := [certificate_7_1, certificate_7_2, certificate_7_3, certificate_7_4, certificate_7_5, certificate_7_6, certificate_7_7, certificate_7_8, certificate_7_9, certificate_7_10, certificate_7_11, certificate_7_12, certificate_7_13, certificate_7_14, certificate_7_15, certificate_7_16, certificate_7_17, certificate_7_18, certificate_7_19, certificate_7_20, certificate_7_21, certificate_7_22, certificate_7_23, certificate_7_24]

theorem certificates7_valid : ∀ c ∈ certificates7, c.Valid 48 7 := by
  intro c hc
  simp only [certificates7, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_7_1_valid
  · exact certificate_7_2_valid
  · exact certificate_7_3_valid
  · exact certificate_7_4_valid
  · exact certificate_7_5_valid
  · exact certificate_7_6_valid
  · exact certificate_7_7_valid
  · exact certificate_7_8_valid
  · exact certificate_7_9_valid
  · exact certificate_7_10_valid
  · exact certificate_7_11_valid
  · exact certificate_7_12_valid
  · exact certificate_7_13_valid
  · exact certificate_7_14_valid
  · exact certificate_7_15_valid
  · exact certificate_7_16_valid
  · exact certificate_7_17_valid
  · exact certificate_7_18_valid
  · exact certificate_7_19_valid
  · exact certificate_7_20_valid
  · exact certificate_7_21_valid
  · exact certificate_7_22_valid
  · exact certificate_7_23_valid
  · exact certificate_7_24_valid

theorem certificates7_coverage :
    ∀ d ∈ Finset.Ico 1 (48 / 2 + 1), ∃ c ∈ certificates7, c.failed = {0, d} := by decide +kernel

#print axioms certificates7_valid
#print axioms certificates7_coverage
end QuorumAudit.MixedCircle
