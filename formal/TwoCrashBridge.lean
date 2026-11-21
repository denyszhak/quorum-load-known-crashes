import TwoCrashBases
import TwoCrashSymmetry
import TwoCrashControls
import UniversalLowerBound

namespace QuorumAudit.TwoCrash
noncomputable section
open Finset

/-- No certificate validity or routing premise remains: all fifty actual
bases have checked routings, and all their circle rotations use the same
fixed families. This theorem does not assert arbitrary-size insertion. -/
theorem every_base_rotation_routes (g : Gadget) (hg : g∈bases)
    [NeZero (nodes g)] (d : ZMod (nodes g)) (a : ℝ)
    (ha : 0≤a) (haReg : a≤critical (rankParameter g)) :
    ∃ r : Routing (reads (nodes g) (rankParameter g)) (range (nodes g))
        ((failures g).image (rotation (nodes g) d)),
    ∃ w : Routing (writes (nodes g)) (range (nodes g))
        ((failures g).image (rotation (nodes g) d)),
      ∀ i∈range (nodes g), combined r w a i≤target (rankParameter g) a := by
  obtain ⟨r,w,hload⟩ := every_base_routes g hg a ha haReg
  exact rotation_routes (nodes g) (rankParameter g) d (failures g)
    (all_bases_semantic g hg).2.2.2.1 r w a (target (rankParameter g) a) hload

#print axioms universal_two_crash_lower_bound
#print axioms upper_routing_from_witnesses
#print axioms all_bases_semantic
#print axioms semantic_base_for_every_pair
#print axioms every_base_routes
#print axioms every_base_rotation_routes
#print axioms rotation_routes
#print axioms zero_scale_rejected
#print axioms missing_read_rejected
#print axioms wrong_read_size_rejected
#print axioms foreign_server_rejected
#print axioms empty_uniform_rejected
#print axioms empty_critical_rejected
#print axioms failed_read_rejected
#print axioms altered_weight_rejected
end
end QuorumAudit.TwoCrash
