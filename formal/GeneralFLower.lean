import SemanticBounds

namespace QuorumAudit.GeneralF
noncomputable section
variable {ι : Type*} [DecidableEq ι]

def value (f k : ℕ) (a : ℝ) : ℝ :=
  ((f : ℝ) + 1 + ((k : ℝ) - 1) * a) / (((f : ℝ) + 1) * k - f)

def endpoint (f k : ℕ) : ℝ :=
  1 / (((k : ℝ) - 1) * ((k : ℝ) + f) + 1)

theorem endpoint_lt_one (f k : ℕ) (hf : 1 ≤ f) (hk : 2 ≤ k) : endpoint f k < 1 := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < k - 1 := by linarith
  unfold endpoint
  apply (div_lt_one (by positivity : 0 < ((k : ℝ) - 1) * (k + f) + 1)).mpr
  nlinarith

theorem small_read_comparison (f k : ℕ) (hf : 1 ≤ f) (hk : 2 ≤ k)
    (a : ℝ) (ha : a ≤ endpoint f k) : value f k a ≤ (1 - a) / ((k : ℝ) - 1) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < k - 1 := by linarith
  have hm : 0 < ((f : ℝ) + 1) * k - f := by nlinarith
  have hD : 0 < ((k : ℝ) - 1) * (k + f) + 1 := by positivity
  have hab := (le_div_iff₀ hD).mp ha
  unfold value
  apply (div_le_div_iff₀ hm (by linarith : 0 < (k : ℝ) - 1)).mpr
  nlinarith [hab]

theorem universal_lower_bound
    (f k : ℕ) (hf : 1 ≤ f) (hk : 2 ≤ k)
    (U : Finset ι) (hU : U.card = (f + 1) * k)
    (R W : Finset (Finset ι))
    (hRsub : ∀ r ∈ R, r ⊆ U) (hWsub : ∀ w ∈ W, w ⊆ U)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (hRavail : ∀ F ⊆ U, F.card ≤ f → ∃ r ∈ R, Disjoint r F)
    (hWavail : ∀ F ⊆ U, F.card ≤ f → ∃ w ∈ W, Disjoint w F)
    (readRoutes : ∀ F, F ⊆ U → F.card = f → Routing R U F)
    (writeRoutes : ∀ F, F ⊆ U → F.card = f → Routing W U F)
    (a L : ℝ) (ha : 0 ≤ a) (hareg : a ≤ endpoint f k)
    (hL : ∀ F (hF : F ⊆ U) (hcard : F.card = f),
      ∀ i ∈ U \ F, combined (readRoutes F hF hcard) (writeRoutes F hF hcard) a i ≤ L) :
    value f k a ≤ L := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have ha1 : a < 1 := lt_of_le_of_lt hareg (endpoint_lt_one f k hf hk)
  have hRrank := quorum_minimum_rank R W U f hRsub hsafe hWavail
  have hWrank : ∀ w ∈ W, f + 1 ≤ w.card := by
    apply quorum_minimum_rank W R U f hWsub _ hRavail
    intro w hw r hr
    simpa [Finset.inter_comm] using hsafe r hr w hw
  by_cases hsmall : ∃ r ∈ R, r.card ≤ k + f - 1
  · obtain ⟨r, hr, hrsmall⟩ := hsmall
    obtain ⟨F, hFr, hFc⟩ := Finset.exists_subset_card_eq (show f ≤ r.card by have := hRrank r hr; omega)
    have hFU : F ⊆ U := hFr.trans (hRsub r hr)
    have hmass := small_read_mass_branch (readRoutes F hFU hFc) (writeRoutes F hFU hFc)
      r a L (hRsub r hr) ha (le_of_lt ha1) (hsafe r hr) (hL F hFU hFc)
    have hc : (r \ F).card ≤ k - 1 := by
      rw [Finset.card_sdiff_of_subset hFr, hFc]
      omega
    have hcR : ((r \ F).card : ℝ) ≤ (k : ℝ) - 1 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hc
      rwa [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at h
    have hLp : 0 < L := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (r \ F).card (α := ℝ)) (le_of_not_gt hn)
      linarith
    apply le_trans (small_read_comparison f k hf hk a hareg)
    apply (div_le_iff₀ (by linarith : 0 < (k : ℝ) - 1)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcR (le_of_lt hLp)]
  · have hfU : f ≤ U.card := by rw [hU]; nlinarith
    obtain ⟨F, hFU, hFc⟩ := Finset.exists_subset_card_eq hfU
    have hRlarge : ∀ r ∈ R, (k : ℝ) + f ≤ (r.card : ℝ) := by
      intro r hr
      have hn : k + f ≤ r.card := by
        have : ¬ r.card ≤ k + f - 1 := fun h => hsmall ⟨r, hr, h⟩
        omega
      exact_mod_cast hn
    have hWlarge : ∀ w ∈ W, (f : ℝ) + 1 ≤ (w.card : ℝ) := by
      intro w hw
      exact_mod_cast hWrank w hw
    have hmass := survivor_average_branch (readRoutes F hFU hFc) (writeRoutes F hFU hFc)
      a ((k : ℝ) + f) ((f : ℝ) + 1) L ha (le_of_lt ha1) hRlarge hWlarge (hL F hFU hFc)
    have hc : ((U \ F).card : ℝ) = ((f : ℝ) + 1) * k - f := by
      have hfU' : f ≤ (f + 1) * k := by omega
      rw [Finset.card_sdiff_of_subset hFU, hU, hFc, Nat.cast_sub hfU']
      push_cast
      ring
    rw [hc] at hmass
    unfold value
    apply (div_le_iff₀ (by nlinarith : 0 < ((f : ℝ) + 1) * k - f)).mpr
    nlinarith

#print axioms universal_lower_bound
end
end QuorumAudit.GeneralF
