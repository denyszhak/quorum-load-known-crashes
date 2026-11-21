import FullRangeOrder
import FullRangeProactive

/-!
Concrete controls for the sections "Every read fraction" and "Unknown
failures": the worked example of the manuscript (two crashes, 100 servers,
equal read and write fractions) and one exact proactive optimum.
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset Circle

/-- The manuscript's example: known-failure load at most `0.1187`. -/
theorem example_known :
    Feasible (univ : Finset (ZMod 100)) 2 (1 / 2) (1187 / 10000) := by
  obtain ⟨had, hroutes⟩ := prop_tiles (n := 100) 2 11 (by norm_num) (by norm_num) (by norm_num)
    (1 / 2) (by norm_num) (by norm_num)
  have hN : cdiv (100 - 2 - 2 * (11 - 1)) 11 = 8 := by decide
  have hq : cdiv (100 - 2) (11 - 2) = 11 := by decide
  rw [hN, hq] at hroutes
  rw [hq] at had
  refine feasible_mono ?_ ⟨_, _, had, hroutes⟩
  norm_num

/-- The manuscript's example: every proactive design has load above
    `0.2236`. -/
theorem example_proactive (L : ℝ)
    (h : ProactiveFeasible (univ : Finset (ZMod 100)) 2 (1 / 2) L) : 2236 / 10000 < L := by
  obtain ⟨hL, _, h2⟩ := proactive_lower (univ : Finset (ZMod 100)) 2
    (by rw [card_univ, ZMod.card]; norm_num) (1 / 2) L (by norm_num) (by norm_num) h
  rw [card_univ, ZMod.card] at h2
  norm_num at h2
  by_contra hn
  have hle : L ≤ 2236 / 10000 := not_lt.mp hn
  have : L ^ 2 ≤ (2236 / 10000) ^ 2 := pow_le_pow_left₀ hL.le hle 2
  norm_num at this
  linarith

/-- One exact proactive optimum: one crash, twelve servers, equal
    fractions. The optimum is `1/2 = sqrt(3/12)`. -/
theorem example_proactive_exact (L : ℝ) :
    ProactiveFeasible (univ : Finset (ZMod 12)) 1 (1 / 2) L ↔ 1 / 2 ≤ L := by
  have h := proactive_exact (n := 12) 1 6 (by norm_num) (by decide) L
  norm_num at h
  exact h

/-- The contact-set condition is not vacuous: two disjoint contact sets
    are not resilient for any admissible pair, even with no crashes. -/
theorem example_contacts :
    ¬ ∃ R W : Finset (Finset (ZMod 4)), Admissible R W univ 0 ∧
        (∀ A ∈ ({{0, 1}} : Finset (Finset (ZMod 4))), Resilient R 0 A) ∧
        (∀ B ∈ ({{2, 3}} : Finset (Finset (ZMod 4))), Resilient W 0 B) := by
  rw [contacts_iff _ _ _ 0 (fun _ _ => subset_univ _) (fun _ _ => subset_univ _)
    (singleton_nonempty _) (singleton_nonempty _)]
  intro h
  have := h {0, 1} (mem_singleton_self _) {2, 3} (mem_singleton_self _)
  revert this
  decide

#print axioms example_known
#print axioms example_proactive
#print axioms example_proactive_exact
#print axioms example_contacts
end
end QuorumAudit.Paper
