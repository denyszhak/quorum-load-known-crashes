import MixedCircleTransport
import MixedCircleData5
import MixedCircleData6
import MixedCircleData7
import MixedCircleData8
import MixedCircleData9

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
variable {n : ℕ} [NeZero n]

theorem finite_interval_upper (r : ℕ) (hr : 5 ≤ r) (hr9 : r ≤ 9)
    (hn : n + 1 = r * r) (F : Finset (ZMod n)) (hF : F.card ≤ 2) :
    ∃ read : Routing (reads n r) univ F,
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2 := by
  have cases : r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have he : n = 24 := by omega
    subst n
    exact all_failures_upper_of_certificates 5 (by decide) hn certificates5
      certificates5_valid certificates5_coverage F hF
  · have he : n = 35 := by omega
    subst n
    exact all_failures_upper_of_certificates 6 (by decide) hn certificates6
      certificates6_valid certificates6_coverage F hF
  · have he : n = 48 := by omega
    subst n
    exact all_failures_upper_of_certificates 7 (by decide) hn certificates7
      certificates7_valid certificates7_coverage F hF
  · have he : n = 63 := by omega
    subst n
    exact all_failures_upper_of_certificates 8 (by decide) hn certificates8
      certificates8_valid certificates8_coverage F hF
  · have he : n = 80 := by omega
    subst n
    exact all_failures_upper_of_certificates 9 (by decide) hn certificates9
      certificates9_valid certificates9_coverage F hF

theorem finite_balanced_interval_exact (r : ℕ) (hr : 5 ≤ r) (hr9 : r ≤ 9)
    (hn : n + 1 = r * r) :
    (∀ q ∈ reads n r, ∀ w ∈ mixedWrites n r, (q ∩ w).Nonempty) ∧
    (∀ F : Finset (ZMod n), F.card ≤ 2 →
      ∃ read : Routing (reads n r) univ F,
      ∃ write : Routing (mixedWrites n r) univ F,
        ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2) ∧
    (∀ W : Finset (Finset (ZMod n)), ∀ L : ℝ,
      (∀ q ∈ reads n r, ∀ w ∈ W, (q ∩ w).Nonempty) →
      (∀ F : Finset (ZMod n), F.card ≤ 2 →
        ∃ read : Routing (reads n r) univ F,
        ∃ write : Routing W univ F,
          ∀ i ∈ univ \ F, combined read write (1 / 2) i ≤ L) → cap r / 2 ≤ L) := by
  exact ⟨mixed_safe r, finite_interval_upper r hr hr9 hn,
    fun W L hs h => balanced_fixed_read_lower r hr hn W L hs h⟩

#print axioms finite_interval_upper
#print axioms finite_balanced_interval_exact
end
end QuorumAudit.MixedCircle
