import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_7 : CircleCertificate := {
  failed := {0, 7},
  read := ⟨[
    ({1, 2, 3, 4, 5}, 1),
    ({8, 9, 10, 11, 12}, 1),
    ({13, 14, 15, 16, 17}, 1),
    ({18, 19, 20, 21, 22}, 1)], 4⟩,
  write := ⟨[
    ({1, 5, 9, 13, 17, 21}, 1),
    ({2, 6, 10, 14, 18, 22}, 1),
    ({3, 6, 11, 15, 19, 23}, 1),
    ({4, 8, 12, 16, 20, 23}, 1)], 4⟩ }

theorem certificate_5_7_valid : certificate_5_7.Valid 24 5 := by decide +kernel

#print axioms certificate_5_7_valid
end QuorumAudit.MixedCircle
