import MixedCircleFinite

namespace QuorumAudit.MixedCircle
open Finset

def zeroScaleCertificate : CircleCertificate :=
  { certificate_5_1 with read := { certificate_5_1.read with scale := 0 } }

def overloadedCertificate : CircleCertificate :=
  { certificate_5_1 with write := ⟨[({2, 4, 8, 13, 18, 22}, 1)], 1⟩ }

theorem rejects_zero_scale : ¬ zeroScaleCertificate.Valid 24 5 := by decide +kernel
theorem rejects_overloaded_routing : ¬ overloadedCertificate.Valid 24 5 := by decide +kernel

theorem surviving_reads_are_not_enough :
    let w : Finset ℕ := {6, 10, 14, 18, 22}
    w.card = 5 ∧ w ⊆ range 24 \ {0, 5} ∧
    (∀ s ∈ range 24, Disjoint (natArc 24 5 s) {0, 5} → (natArc 24 5 s ∩ w).Nonempty) ∧
    ¬ (∀ s ∈ range 24, (natArc 24 5 s ∩ w).Nonempty) := by decide +kernel

#print axioms rejects_zero_scale
#print axioms rejects_overloaded_routing
#print axioms surviving_reads_are_not_enough
end QuorumAudit.MixedCircle
