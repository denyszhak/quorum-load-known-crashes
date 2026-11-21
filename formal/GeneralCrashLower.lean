import SemanticBounds
set_option maxHeartbeats 1000000

namespace QuorumAudit.GeneralCrash
noncomputable section
variable {ι : Type*} [DecidableEq ι]

theorem universal_dichotomy
    (f ρ : ℕ) (hf : 1 ≤ f) (hρ : f + 2 ≤ ρ)
    (U : Finset ι) (hU : 2 * f + 1 ≤ U.card)
    (R W : Finset (Finset ι))
    (hRsub : ∀ r ∈ R, r ⊆ U) (hWsub : ∀ w ∈ W, w ⊆ U)
    (hsafe : ∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty)
    (hRavail : ∀ F ⊆ U, F.card ≤ f → ∃ r ∈ R, Disjoint r F)
    (hWavail : ∀ F ⊆ U, F.card ≤ f → ∃ w ∈ W, Disjoint w F)
    (readRoutes : ∀ F, F ⊆ U → F.card = f → Routing R U F)
    (writeRoutes : ∀ F, F ⊆ U → F.card = f → Routing W U F)
    (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hL : ∀ F (hF : F ⊆ U) (hc : F.card = f),
      ∀ i ∈ U \ F, combined (readRoutes F hF hc) (writeRoutes F hF hc) a i ≤ L) :
    (1 - a) / ((ρ : ℝ) - 1 - f) ≤ L ∨
      ((ρ : ℝ) * a + ((f : ℝ) + 1) * (1 - a)) / ((U.card : ℝ) - f) ≤ L := by
  have hRrank := quorum_minimum_rank R W U f hRsub hsafe hWavail
  have hWrank : ∀ w ∈ W, f + 1 ≤ w.card := by
    apply quorum_minimum_rank W R U f hWsub _ hRavail
    intro w hw r hr
    simpa [Finset.inter_comm] using hsafe r hr w hw
  by_cases hsmall : ∃ r ∈ R, r.card ≤ ρ - 1
  · obtain ⟨r, hr, hrsmall⟩ := hsmall
    obtain ⟨F, hFr, hFc⟩ := Finset.exists_subset_card_eq (show f ≤ r.card by have := hRrank r hr; omega)
    have hFU := hFr.trans (hRsub r hr)
    let rr := readRoutes F hFU hFc
    let wr := writeRoutes F hFU hFc
    have hmass := small_read_mass_branch rr wr r a L (hRsub r hr) ha ha1 (hsafe r hr) (hL F hFU hFc)
    have hsurv : 0 < (U \ F).card := by
      rw [Finset.card_sdiff_of_subset hFU, hFc]
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hsurv
    have hLp : 0 ≤ L := by
      apply le_trans _ (hL F hFU hFc i hi)
      exact add_nonneg (mul_nonneg ha (incidence_nonnegative _ _ rr.nonnegative i))
        (mul_nonneg (by linarith) (incidence_nonnegative _ _ wr.nonnegative i))
    have hc : (r \ F).card ≤ ρ - 1 - f := by
      rw [Finset.card_sdiff_of_subset hFr, hFc]
      omega
    have hcR : ((r \ F).card : ℝ) ≤ (ρ : ℝ) - 1 - f := by
      have h := (Nat.cast_le (α := ℝ)).mpr hc
      rwa [Nat.cast_sub (by omega : f ≤ ρ - 1), Nat.cast_sub (by omega : 1 ≤ ρ), Nat.cast_one] at h
    have hρR : (f : ℝ) + 2 ≤ ρ := by exact_mod_cast hρ
    left
    apply (div_le_iff₀ (by linarith : 0 < (ρ : ℝ) - 1 - f)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcR hLp]
  · obtain ⟨F, hFU, hFc⟩ := Finset.exists_subset_card_eq (show f ≤ U.card by omega)
    have hRlarge : ∀ r ∈ R, (ρ : ℝ) ≤ r.card := by
      intro r hr
      have hn : ρ ≤ r.card := by
        have : ¬ r.card ≤ ρ - 1 := fun h => hsmall ⟨r, hr, h⟩
        omega
      exact_mod_cast hn
    have hWlarge : ∀ w ∈ W, (f : ℝ) + 1 ≤ w.card := by
      intro w hw
      exact_mod_cast hWrank w hw
    have hmass := survivor_average_branch (readRoutes F hFU hFc) (writeRoutes F hFU hFc)
      a ρ ((f : ℝ) + 1) L ha ha1 hRlarge hWlarge (hL F hFU hFc)
    have hc : ((U \ F).card : ℝ) = (U.card : ℝ) - f := by
      rw [Finset.card_sdiff_of_subset hFU, hFc, Nat.cast_sub (by omega : f ≤ U.card)]
    have hU' : (2 : ℝ) * f + 1 ≤ U.card := by exact_mod_cast hU
    right
    apply (div_le_iff₀ (by linarith : 0 < (U.card : ℝ) - f)).mpr
    rw [hc] at hmass
    nlinarith [hmass]

def twoCrashValue (k r : ℕ) (a : ℝ) : ℝ :=
  (3 + ((k : ℝ) - 1) * a) / (3 * (k : ℝ) + r - 2)

def twoCrashEndpoint (k r : ℕ) : ℝ :=
  ((r : ℝ) + 1) / ((k : ℝ) * k + k + r - 1)

theorem universal_two_crash_all_n
    (k r : ℕ) (hk : 3 ≤ k) (hr : r ≤ 2)
    (U : Finset ι) (hU : U.card = 3 * k + r)
    (R W : Finset (Finset ι))
    (hRsub : ∀ s ∈ R, s ⊆ U) (hWsub : ∀ w ∈ W, w ⊆ U)
    (hsafe : ∀ s ∈ R, ∀ w ∈ W, (s ∩ w).Nonempty)
    (hRavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ s ∈ R, Disjoint s F)
    (hWavail : ∀ F ⊆ U, F.card ≤ 2 → ∃ w ∈ W, Disjoint w F)
    (readRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing R U F)
    (writeRoutes : ∀ F, F ⊆ U → F.card = 2 → Routing W U F)
    (a L : ℝ) (ha : 0 ≤ a) (hareg : a ≤ twoCrashEndpoint k r)
    (hL : ∀ F (hF : F ⊆ U) (hc : F.card = 2),
      ∀ i ∈ U \ F, combined (readRoutes F hF hc) (writeRoutes F hF hc) a i ≤ L) :
    twoCrashValue k r a ≤ L := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (r : ℝ) ≤ 2 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hD : 0 < (k : ℝ) * k + k + r - 1 := by nlinarith
  have hreg := (le_div_iff₀ hD).mp hareg
  have ha1 : a ≤ 1 := by
    apply le_trans hareg
    apply (div_le_one hD).mpr
    nlinarith
  have huR : (U.card : ℝ) = 3 * (k : ℝ) + r := by exact_mod_cast hU
  have hsmall : twoCrashValue k r a ≤ (1 - a) / ((k : ℝ) - 1) := by
    unfold twoCrashValue
    apply (div_le_div_iff₀ (by nlinarith : 0 < 3 * (k : ℝ) + r - 2) (by linarith : 0 < (k : ℝ) - 1)).mpr
    nlinarith [hreg]
  have h := universal_dichotomy 2 (k + 2) (by decide) (by omega) U (by omega) R W
    hRsub hWsub hsafe hRavail hWavail readRoutes writeRoutes a L ha ha1 hL
  rcases h with h | h
  · apply le_trans hsmall
    convert h using 1
    push_cast
    ring
  · convert h using 1
    simp only [huR, Nat.cast_add, Nat.cast_ofNat, twoCrashValue]
    ring

#print axioms universal_dichotomy
#print axioms universal_two_crash_all_n
end
end QuorumAudit.GeneralCrash
