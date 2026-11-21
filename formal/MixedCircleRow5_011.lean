import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_11 : CircleCertificate := {
  failed := {0, 11},
  read := ⟨[
    ({1, 2, 3, 4, 5}, 1),
    ({6, 7, 8, 9, 10}, 1),
    ({13, 14, 15, 16, 17}, 1),
    ({18, 19, 20, 21, 22}, 1)], 4⟩,
  write := ⟨[
    ({1, 5, 9, 13, 17, 21}, 1),
    ({2, 6, 10, 14, 18, 22}, 1),
    ({3, 7, 12, 15, 19, 23}, 1),
    ({4, 8, 12, 16, 20, 23}, 1)], 4⟩ }

theorem certificate_5_11_valid : certificate_5_11.Valid 24 5 := by decide +kernel

#print axioms certificate_5_11_valid
end QuorumAudit.MixedCircle
