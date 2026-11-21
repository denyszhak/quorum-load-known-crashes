import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_3 : CircleCertificate := {
  failed := {0, 3},
  read := ⟨[
    ({5, 6, 7, 8, 9}, 4),
    ({10, 11, 12, 13, 14}, 3),
    ({15, 16, 17, 18, 19}, 2),
    ({8, 9, 10, 11, 12}, 2),
    ({13, 14, 15, 16, 17}, 3),
    ({18, 19, 20, 21, 22}, 4)], 18⟩,
  write := ⟨[
    ({2, 5, 9, 14, 19, 23}, 3),
    ({2, 5, 10, 15, 20, 23}, 2),
    ({2, 6, 10, 15, 20, 23}, 2),
    ({2, 6, 11, 16, 20, 23}, 1),
    ({2, 6, 11, 16, 21, 23}, 1),
    ({1, 4, 6, 11, 16, 21}, 1),
    ({1, 4, 7, 11, 16, 21}, 1),
    ({1, 4, 7, 12, 17, 21}, 2),
    ({1, 4, 7, 12, 17, 22}, 2),
    ({1, 4, 8, 13, 18, 22}, 3)], 18⟩ }

theorem certificate_5_3_valid : certificate_5_3.Valid 24 5 := by decide +kernel

#print axioms certificate_5_3_valid
end QuorumAudit.MixedCircle
