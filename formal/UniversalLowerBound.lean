import SemanticBounds

namespace QuorumAudit
noncomputable section
variable {ι : Type*} [DecidableEq ι]

/-- Universal two-crash lower bound for ANY fixed cross-intersecting families
    on 3k+2 nodes, and ANY failure-dependent normalized nonnegative routing.
    This proves optimality from first principles; it does not construct the
    progression-family upper bound. Same-phase intersection is not assumed. -/
theorem universal_two_crash_lower_bound
    (k : Nat) (hk : 3 ≤ k) (U : Finset ι) (hU : U.card = 3 * k + 2)
    (R W : Finset (Finset ι))
    (hRsub : ∀ r ∈ R, r ⊆ U) (hWsub : ∀ w ∈ W, w ⊆ U)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (hRavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ r ∈ R, Disjoint r F)
    (hWavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ w ∈ W, Disjoint w F)
    (readRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing R U F)
    (writeRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing W U F)
    (a L : ℝ) (ha : 0 ≤ a) (hareg : a ≤ critical k)
    (hL : ∀ F (hF : F ⊆ U) (hcard : F.card = 2),
      ∀ i ∈ U \ F, combined (readRoutes F hF hcard) (writeRoutes F hF hcard) a i ≤ L) :
    target k a ≤ L := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ha1 : a < 1 := lt_of_le_of_lt hareg (critical_less_one k hkR)
  have hRrank : ∀ r ∈ R, 3 ≤ r.card :=
    quorum_minimum_rank R W U 2 hRsub hsafe hWavail
  have hWrank : ∀ w ∈ W, 3 ≤ w.card := by
    apply quorum_minimum_rank W R U 2 hWsub _ hRavail
    intro w hw r hr
    simpa [Finset.inter_comm] using hsafe r hr w hw
  apply dichotomy_implies_bound k a L hkR hareg
  by_cases hsmall : ∃ r ∈ R, r.card ≤ k + 1
  · obtain ⟨r, hr, hrsmall⟩ := hsmall
    obtain ⟨F, hFr, hFcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ r.card by have := hRrank r hr; omega)
    have hFU : F ⊆ U := Finset.Subset.trans hFr (hRsub r hr)
    have hmass := small_read_mass_branch (readRoutes F hFU hFcard)
      (writeRoutes F hFU hFcard) r a L (hRsub r hr) ha (le_of_lt ha1)
      (hsafe r hr) (hL F hFU hFcard)
    have hc : (r \ F).card ≤ k - 1 := by
      rw [Finset.card_sdiff_of_subset hFr, hFcard]
      omega
    have hcR : ((r \ F).card : ℝ) ≤ (k : ℝ) - 1 := by
      have hcast : ((r \ F).card : ℝ) ≤ ((k - 1 : Nat) : ℝ) := by exact_mod_cast hc
      have hsub : ((k - 1 : Nat) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        simp
      rwa [hsub] at hcast
    have hLpos : 0 < L := by
      have hcard0 : 0 ≤ ((r \ F).card : ℝ) := Nat.cast_nonneg _
      by_contra h
      have hn : ((r \ F).card : ℝ) * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcard0 (le_of_not_gt h)
      linarith
    left
    apply (div_le_iff₀ (by linarith : 0 < (k : ℝ) - 1)).mpr
    simpa [mul_comm] using le_trans hmass (mul_le_mul_of_nonneg_right hcR (le_of_lt hLpos))
  · obtain ⟨F, hFU, hFcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ U.card by omega)
    have hRlarge : ∀ r ∈ R, (k : ℝ) + 2 ≤ (r.card : ℝ) := by
      intro r hr
      have hn : k + 2 ≤ r.card := by
        have hnot : ¬ r.card ≤ k + 1 := fun h => hsmall ⟨r, hr, h⟩
        omega
      exact_mod_cast hn
    have hWlarge : ∀ w ∈ W, (3 : ℝ) ≤ (w.card : ℝ) := by
      intro w hw
      exact_mod_cast hWrank w hw
    have hmass := survivor_average_branch (readRoutes F hFU hFcard)
      (writeRoutes F hFU hFcard) a ((k : ℝ) + 2) 3 L ha (le_of_lt ha1)
      hRlarge hWlarge (hL F hFU hFcard)
    have hc : (U \ F).card = 3 * k := by
      rw [Finset.card_sdiff_of_subset hFU, hU, hFcard]
      omega
    have hcR : ((U \ F).card : ℝ) = 3 * (k : ℝ) := by exact_mod_cast hc
    rw [hcR] at hmass
    right
    unfold target
    apply (div_le_iff₀ (by linarith : 0 < 3 * (k : ℝ))).mpr
    nlinarith

#print axioms universal_two_crash_lower_bound
end
end QuorumAudit
