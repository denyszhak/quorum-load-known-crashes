import MixedCircleRow6_001
import MixedCircleRow6_002
import MixedCircleRow6_003
import MixedCircleRow6_004
import MixedCircleRow6_005
import MixedCircleRow6_006
import MixedCircleRow6_007
import MixedCircleRow6_008
import MixedCircleRow6_009
import MixedCircleRow6_010
import MixedCircleRow6_011
import MixedCircleRow6_012
import MixedCircleRow6_013
import MixedCircleRow6_014
import MixedCircleRow6_015
import MixedCircleRow6_016
import MixedCircleRow6_017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificates6 : List CircleCertificate := [certificate_6_1, certificate_6_2, certificate_6_3, certificate_6_4, certificate_6_5, certificate_6_6, certificate_6_7, certificate_6_8, certificate_6_9, certificate_6_10, certificate_6_11, certificate_6_12, certificate_6_13, certificate_6_14, certificate_6_15, certificate_6_16, certificate_6_17]

theorem certificates6_valid : ∀ c ∈ certificates6, c.Valid 35 6 := by
  intro c hc
  simp only [certificates6, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_6_1_valid
  · exact certificate_6_2_valid
  · exact certificate_6_3_valid
  · exact certificate_6_4_valid
  · exact certificate_6_5_valid
  · exact certificate_6_6_valid
  · exact certificate_6_7_valid
  · exact certificate_6_8_valid
  · exact certificate_6_9_valid
  · exact certificate_6_10_valid
  · exact certificate_6_11_valid
  · exact certificate_6_12_valid
  · exact certificate_6_13_valid
  · exact certificate_6_14_valid
  · exact certificate_6_15_valid
  · exact certificate_6_16_valid
  · exact certificate_6_17_valid

theorem certificates6_coverage :
    ∀ d ∈ Finset.Ico 1 (35 / 2 + 1), ∃ c ∈ certificates6, c.failed = {0, d} := by decide +kernel

#print axioms certificates6_valid
#print axioms certificates6_coverage
end QuorumAudit.MixedCircle
