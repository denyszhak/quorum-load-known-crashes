import SemanticBounds

namespace QuorumAudit
noncomputable section
variable {ι : Type*} [DecidableEq ι]

/-- An unrestricted lower bound around balanced workloads. A three-node
    read or write forces all opposite accesses through one surviving node.
    If neither exists, both phases contact at least four surviving nodes. -/
theorem universal_rank_four_two_crash_lower_bound
    (n : Nat) (hn : 10 ≤ n) (U : Finset ι) (hU : U.card = n)
    (R W : Finset (Finset ι))
    (hRsub : ∀ r ∈ R, r ⊆ U) (hWsub : ∀ w ∈ W, w ⊆ U)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (hRavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ r ∈ R, Disjoint r F)
    (hWavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ w ∈ W, Disjoint w F)
    (readRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing R U F)
    (writeRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing W U F)
    (a L : ℝ) (halower : 4 / ((n : ℝ) - 2) ≤ a)
    (haupper : a ≤ 1 - 4 / ((n : ℝ) - 2))
    (hL : ∀ F (hF : F ⊆ U) (hcard : F.card = 2),
      ∀ i ∈ U \ F, combined (readRoutes F hF hcard) (writeRoutes F hF hcard) a i ≤ L) :
    4 / ((n : ℝ) - 2) ≤ L := by
  have hnR : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have hb : 0 < 4 / ((n : ℝ) - 2) := div_pos (by norm_num) hd
  have ha : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hRrank : ∀ r ∈ R, 3 ≤ r.card :=
    quorum_minimum_rank R W U 2 hRsub hsafe hWavail
  have hsafeSwap : ∀ w ∈ W, ∀ r ∈ R, (w ∩ r).Nonempty := by
    intro w hw r hr
    simpa [Finset.inter_comm] using hsafe r hr w hw
  have hWrank : ∀ w ∈ W, 3 ≤ w.card :=
    quorum_minimum_rank W R U 2 hWsub hsafeSwap hRavail
  by_cases hsmallR : ∃ r ∈ R, r.card ≤ 3
  · obtain ⟨r, hr, hrsmall⟩ := hsmallR
    have hr3 : r.card = 3 := by have := hRrank r hr; omega
    obtain ⟨F, hFr, hFcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ r.card by omega)
    have hFU : F ⊆ U := Finset.Subset.trans hFr (hRsub r hr)
    have hmass := small_read_mass_branch (readRoutes F hFU hFcard)
      (writeRoutes F hFU hFcard) r a L (hRsub r hr) ha ha1
      (hsafe r hr) (hL F hFU hFcard)
    have hc : (r \ F).card = 1 := by
      rw [Finset.card_sdiff_of_subset hFr, hr3, hFcard]
    simp only [hc, Nat.cast_one, one_mul] at hmass
    linarith
  by_cases hsmallW : ∃ w ∈ W, w.card ≤ 3
  · obtain ⟨w, hw, hwsmall⟩ := hsmallW
    have hw3 : w.card = 3 := by have := hWrank w hw; omega
    obtain ⟨F, hFw, hFcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ w.card by omega)
    have hFU : F ⊆ U := Finset.Subset.trans hFw (hWsub w hw)
    have hLswap : ∀ i ∈ U \ F,
        combined (writeRoutes F hFU hFcard) (readRoutes F hFU hFcard) (1 - a) i ≤ L := by
      intro i hi
      have heq : combined (writeRoutes F hFU hFcard) (readRoutes F hFU hFcard) (1 - a) i =
          combined (readRoutes F hFU hFcard) (writeRoutes F hFU hFcard) a i := by
        unfold combined
        ring
      rw [heq]
      exact hL F hFU hFcard i hi
    have hmass := small_read_mass_branch (writeRoutes F hFU hFcard)
      (readRoutes F hFU hFcard) w (1 - a) L (hWsub w hw)
      (by linarith : 0 ≤ 1 - a) (by linarith : 1 - a ≤ 1)
      (hsafeSwap w hw) hLswap
    have hc : (w \ F).card = 1 := by
      rw [Finset.card_sdiff_of_subset hFw, hw3, hFcard]
    simp only [hc, Nat.cast_one, one_mul] at hmass
    linarith
  · obtain ⟨F, hFU, hFcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ U.card by omega)
    have hRlarge : ∀ r ∈ R, (4 : ℝ) ≤ (r.card : ℝ) := by
      intro r hr
      have h4 : 4 ≤ r.card := by
        have hnot : ¬ r.card ≤ 3 := fun h => hsmallR ⟨r, hr, h⟩
        omega
      exact_mod_cast h4
    have hWlarge : ∀ w ∈ W, (4 : ℝ) ≤ (w.card : ℝ) := by
      intro w hw
      have h4 : 4 ≤ w.card := by
        have hnot : ¬ w.card ≤ 3 := fun h => hsmallW ⟨w, hw, h⟩
        omega
      exact_mod_cast h4
    have hmass := survivor_average_branch (readRoutes F hFU hFcard)
      (writeRoutes F hFU hFcard) a 4 4 L ha ha1 hRlarge hWlarge (hL F hFU hFcard)
    have hc : ((U \ F).card : ℝ) = (n : ℝ) - 2 := by
      rw [Finset.card_sdiff_of_subset hFU, hU, hFcard]
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      norm_num
    rw [hc] at hmass
    apply (div_le_iff₀ hd).mpr
    nlinarith

#print axioms universal_rank_four_two_crash_lower_bound
end
end QuorumAudit
