import GeneralFAttainment

namespace QuorumAudit.GeneralF
noncomputable section
open Finset
open Circle

theorem value_nonnegative (f k : ℕ) (hf : 1 ≤ f) (hk : 2 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ value f k a := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold value
  apply div_nonneg _ (by nlinarith)
  nlinarith

theorem interval_construction_attains (f k : ℕ) (hf : 1 ≤ f) (hk : f * f + 1 ≤ k)
    (n : ℕ) [NeZero n] (hn : n = (f + 1) * k)
    (F : Finset (ZMod n)) (hFc : F.card ≤ f)
    (a : ℝ) (ha : 0 ≤ a) (hareg : a ≤ endpoint f k) :
    ∃ read : Routing (reads n (k + f)) univ F,
    ∃ write : Routing (rankedWrites n (k + f) (f + 1)) univ F,
      ∀ i ∈ univ \ F, combined read write a i ≤ value f k a := by
  have hk2 : 2 ≤ k := by nlinarith
  have hfU : f ≤ (univ : Finset (ZMod n)).card := by
    simp only [card_univ, ZMod.card]
    nlinarith
  obtain ⟨G, hFG, _hGU, hGc⟩ := exists_subsuperset_card_eq (subset_univ F) hFc hfU
  obtain ⟨r, w, hl⟩ := exact_failures_attain f k hf hk n hn G hGc a ha hareg
  refine ⟨unpad_routing r hFG, unpad_routing w hFG, ?_⟩
  intro i _hi
  change combined r w a i ≤ value f k a
  by_cases hiG : i ∈ univ \ G
  · exact le_of_eq (hl i hiG)
  · unfold combined
    rw [routing_incidence_outside r i hiG, routing_incidence_outside w i hiG]
    simpa using value_nonnegative f k hf hk2 a ha

theorem routing_has_live_quorum {ι : Type*} [DecidableEq ι]
    {R : Finset (Finset ι)} {U F : Finset ι}
    (r : Routing R U F) : ∃ q ∈ R, Disjoint q F := by
  rcases eq_empty_or_nonempty r.quorums with he | ⟨q, hq⟩
  · have hm := r.normalized
    simp only [he, sum_empty] at hm
    norm_num at hm
  · refine ⟨q, r.subset hq, disjoint_left.mpr ?_⟩
    intro i hi hF
    exact (mem_sdiff.mp (r.live q hq hi)).2 hF

def LoadFeasible (f n : ℕ) [NeZero n] (a L : ℝ) : Prop :=
  ∃ R W : Finset (Finset (ZMod n)),
    (∀ r ∈ R, ∀ w ∈ W, (r ∩ w).Nonempty) ∧
    ∀ F : Finset (ZMod n), F.card ≤ f →
      ∃ r : Routing R univ F, ∃ w : Routing W univ F,
        ∀ i ∈ univ \ F, combined r w a i ≤ L

theorem arbitrary_f_exact_optimum (f k : ℕ) (hf : 1 ≤ f) (hk : f * f + 1 ≤ k)
    (n : ℕ) [NeZero n] (hn : n = (f + 1) * k)
    (a L : ℝ) (ha : 0 ≤ a) (hareg : a ≤ endpoint f k) :
    LoadFeasible f n a L ↔ value f k a ≤ L := by
  constructor
  · rintro ⟨R, W, hsafe, hroutes⟩
    have hk2 : 2 ≤ k := by nlinarith
    have hRavail : ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f → ∃ r ∈ R, Disjoint r F := by
      intro F _ hFc
      obtain ⟨r, _, _⟩ := hroutes F hFc
      exact routing_has_live_quorum r
    have hWavail : ∀ F ⊆ (univ : Finset (ZMod n)), F.card ≤ f → ∃ w ∈ W, Disjoint w F := by
      intro F _ hFc
      obtain ⟨_, w, _⟩ := hroutes F hFc
      exact routing_has_live_quorum w
    let rr := fun F (_ : F ⊆ (univ : Finset (ZMod n))) (hc : F.card = f) =>
      (hroutes F (le_of_eq hc)).choose
    let wr := fun F (_ : F ⊆ (univ : Finset (ZMod n))) (hc : F.card = f) =>
      (hroutes F (le_of_eq hc)).choose_spec.choose
    apply universal_lower_bound f k hf hk2 univ (by simpa using hn) R W
      (fun _ _ => subset_univ _) (fun _ _ => subset_univ _) hsafe hRavail hWavail rr wr a L ha hareg
    intro F hF hc i hi
    exact (hroutes F (le_of_eq hc)).choose_spec.choose_spec i hi
  · intro hL
    refine ⟨reads n (k + f), rankedWrites n (k + f) (f + 1), ranked_safe _ _, ?_⟩
    intro F hFc
    obtain ⟨r, w, hl⟩ := interval_construction_attains f k hf hk n hn F hFc a ha hareg
    exact ⟨r, w, fun i hi => le_trans (hl i hi) hL⟩

#print axioms interval_construction_attains
#print axioms arbitrary_f_exact_optimum
end
end QuorumAudit.GeneralF
