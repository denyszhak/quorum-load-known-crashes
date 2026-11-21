import PaperModel

/-!
Lower bounds and the contact-set lemma for the sections "Every read
fraction" and "Unknown failures" of the manuscript.

Square roots are avoided. A bound `2 * sqrt t ≤ L` of the manuscript is
stated as `0 < L` together with `4 * t ≤ L ^ 2`, which is equivalent.
-/

set_option maxHeartbeats 1000000

namespace QuorumAudit.Paper
noncomputable section
open Finset
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-! ### Symmetry (Proposition `prop:symmetry`) -/

theorem admissible_swap {R W : Finset (Finset ι)} {V : Finset ι} {f : ℕ}
    (h : Admissible R W V f) : Admissible W R V f := by
  obtain ⟨hR, hW, hRn, hWn, hs, hav⟩ := h
  refine ⟨hW, hR, hWn, hRn, ?_, fun F hF hc => ⟨(hav F hF hc).2, (hav F hF hc).1⟩⟩
  intro w hw r hr
  rw [inter_comm]
  exact hs r hr w hw

theorem routes_swap {R W : Finset (Finset ι)} {V F : Finset ι} {a L : ℝ}
    (h : RoutesAt R W V F a L) : RoutesAt W R V F (1 - a) L := by
  obtain ⟨p, q, hp, hq, hload⟩ := h
  refine ⟨q, p, hq, hp, ?_⟩
  intro i hi
  have e : (1 : ℝ) - (1 - a) = a := by ring
  rw [e]
  linarith [hload i hi]

/-- The feasible loads at read fraction `a` and at `1 - a` coincide. -/
theorem feasible_symmetry (V : Finset ι) (f : ℕ) (a L : ℝ) :
    Feasible V f a L ↔ Feasible V f (1 - a) L := by
  have one : ∀ b : ℝ, Feasible V f b L → Feasible V f (1 - b) L := by
    rintro b ⟨R, W, had, hroutes⟩
    exact ⟨W, R, admissible_swap had, fun F hF hc => routes_swap (hroutes F hF hc)⟩
  refine ⟨one a, fun h => ?_⟩
  have h2 := one (1 - a) h
  have e : (1 : ℝ) - (1 - a) = a := by ring
  rwa [e] at h2

/-! ### The product bound -/

/-- Expected size of the common part of two independently drawn sets. -/
theorem product_incidence (S : Finset ι) (P Q : Finset (Finset ι)) (p q : Finset ι → ℝ) :
    ∑ i ∈ S, incidence P p i * incidence Q q i =
      ∑ r ∈ P, ∑ w ∈ Q, ((S ∩ (r ∩ w)).card : ℝ) * (p r * q w) := by
  unfold incidence
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hterm : ∀ i ∈ S, (if i ∈ r then p r else 0) * (if i ∈ w then q w else 0) =
      if i ∈ r ∩ w then p r * q w else 0 := by
    intro i _
    by_cases hr : i ∈ r <;> by_cases hw : i ∈ w <;> simp [hr, hw]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]

theorem product_bound (S : Finset ι) (P Q : Finset (Finset ι)) (p q : Finset ι → ℝ) (c : ℕ)
    (hp : ∀ r ∈ P, 0 ≤ p r) (hq : ∀ w ∈ Q, 0 ≤ q w)
    (hpn : ∑ r ∈ P, p r = 1) (hqn : ∑ w ∈ Q, q w = 1)
    (hmeet : ∀ r ∈ P, ∀ w ∈ Q, c ≤ (S ∩ (r ∩ w)).card) :
    (c : ℝ) ≤ ∑ i ∈ S, incidence P p i * incidence Q q i := by
  rw [product_incidence]
  have hone : ∑ r ∈ P, ∑ w ∈ Q, p r * q w = 1 := by
    rw [← Finset.sum_mul_sum, hpn, hqn, mul_one]
  calc
    (c : ℝ) = (c : ℝ) * ∑ r ∈ P, ∑ w ∈ Q, p r * q w := by rw [hone, mul_one]
    _ = ∑ r ∈ P, ∑ w ∈ Q, (c : ℝ) * (p r * q w) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmeet r hr w hw)
        (mul_nonneg (hp r hr) (hq w hw))

omit [DecidableEq ι] in
/-- The arithmetic--geometric step: bounded load at every point of `S`
    bounds the sum of products of the two inclusion probabilities. -/
theorem amgm_load (S : Finset ι) (x y : ι → ℝ) (a L c : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ S, 0 ≤ y i)
    (hc : c ≤ ∑ i ∈ S, x i * y i)
    (hL : ∀ i ∈ S, a * x i + (1 - a) * y i ≤ L) :
    4 * a * (1 - a) * c ≤ (S.card : ℝ) * L ^ 2 := by
  have hb : 0 ≤ 1 - a := by linarith
  have hterm : ∀ i ∈ S, 4 * a * (1 - a) * (x i * y i) ≤ L ^ 2 := by
    intro i hi
    have h0 : 0 ≤ a * x i + (1 - a) * y i :=
      add_nonneg (mul_nonneg ha (hx i hi)) (mul_nonneg hb (hy i hi))
    have h1 : (a * x i + (1 - a) * y i) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h0 (hL i hi) 2
    nlinarith [sq_nonneg (a * x i - (1 - a) * y i)]
  calc
    4 * a * (1 - a) * c ≤ 4 * a * (1 - a) * ∑ i ∈ S, x i * y i :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = ∑ i ∈ S, 4 * a * (1 - a) * (x i * y i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _i ∈ S, L ^ 2 := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * L ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Known failures (Proposition `prop:amgm`) -/

theorem live_available {A : Finset (Finset ι)} {V : Finset ι} {f : ℕ}
    (h : ∀ F ⊆ V, F.card ≤ f → (liveQuorums A V F).Nonempty) :
    ∀ F ⊆ V, F.card ≤ f → ∃ q ∈ A, Disjoint q F := by
  intro F hF hc
  obtain ⟨q, hq⟩ := h F hF hc
  obtain ⟨hqA, hlive⟩ := mem_filter.mp hq
  exact ⟨q, hqA, disjoint_left.mpr (fun i hi hiF => (mem_sdiff.mp (hlive hi)).2 hiF)⟩

/-- Both terms of the lower bound, for one failed set of size exactly `f`. -/
theorem known_lower_at {R W : Finset (Finset ι)} {V : Finset ι} {f : ℕ}
    (had : Admissible R W V f) (F : Finset ι) (hF : F ⊆ V) (hc : F.card = f)
    (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hroute : RoutesAt R W V F a L) :
    (f : ℝ) + 1 ≤ ((V.card : ℝ) - f) * L ∧
      4 * a * (1 - a) ≤ ((V.card : ℝ) - f) * L ^ 2 := by
  obtain ⟨hR, hW, _, _, hs, hav⟩ := had
  obtain ⟨p, q, ⟨hp, hpn⟩, ⟨hq, hqn⟩, hload⟩ := hroute
  have hs' : ∀ w ∈ W, ∀ r ∈ R, (w ∩ r).Nonempty := by
    intro w hw r hr
    rw [inter_comm]
    exact hs r hr w hw
  have hRrank := quorum_minimum_rank R W V f hR hs
    (live_available (fun F hF hc => (hav F hF hc).2))
  have hWrank := quorum_minimum_rank W R V f hW hs'
    (live_available (fun F hF hc => (hav F hF hc).1))
  have hcard : ((V \ F).card : ℝ) = (V.card : ℝ) - f := by
    rw [Finset.card_sdiff_of_subset hF, Nat.cast_sub (Finset.card_le_card hF), hc]
  have hliveR : ∀ r ∈ liveQuorums R V F, r ∈ R ∧ r ⊆ V \ F := fun r hr => mem_filter.mp hr
  have hliveW : ∀ w ∈ liveQuorums W V F, w ∈ W ∧ w ⊆ V \ F := fun w hw => mem_filter.mp hw
  have hx : ∀ i, 0 ≤ incidence (liveQuorums R V F) p i := incidence_nonnegative _ _ hp
  have hy : ∀ i, 0 ≤ incidence (liveQuorums W V F) q i := incidence_nonnegative _ _ hq
  have hload' : ∀ i ∈ V \ F, a * incidence (liveQuorums R V F) p i +
      (1 - a) * incidence (liveQuorums W V F) q i ≤ L := hload
  constructor
  · have hRm : ((f : ℝ) + 1) ≤ ∑ i ∈ V \ F, incidence (liveQuorums R V F) p i := by
      apply intersection_mass_bound _ _ _ _ hp hpn
      intro r hr
      rw [Finset.inter_eq_right.mpr (hliveR r hr).2]
      exact_mod_cast hRrank r (hliveR r hr).1
    have hWm : ((f : ℝ) + 1) ≤ ∑ i ∈ V \ F, incidence (liveQuorums W V F) q i := by
      apply intersection_mass_bound _ _ _ _ hq hqn
      intro w hw
      rw [Finset.inter_eq_right.mpr (hliveW w hw).2]
      exact_mod_cast hWrank w (hliveW w hw).1
    have hsum : ∑ i ∈ V \ F, (a * incidence (liveQuorums R V F) p i +
        (1 - a) * incidence (liveQuorums W V F) q i) ≤ ∑ _i ∈ V \ F, L :=
      Finset.sum_le_sum hload'
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, hcard] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hRm ha,
      mul_le_mul_of_nonneg_left hWm (by linarith : (0 : ℝ) ≤ 1 - a)]
  · have hprod := product_bound (V \ F) (liveQuorums R V F) (liveQuorums W V F) p q 1
      hp hq hpn hqn (by
        intro r hr w hw
        obtain ⟨i, hi⟩ := hs r (hliveR r hr).1 w (hliveW w hw).1
        exact Finset.card_pos.mpr
          ⟨i, mem_inter.mpr ⟨(hliveR r hr).2 (mem_inter.mp hi).1, hi⟩⟩)
    have h := amgm_load (V \ F) _ _ a L 1 ha ha1 (fun i _ => hx i) (fun i _ => hy i)
      (by exact_mod_cast hprod) hload'
    rw [hcard] at h
    linarith

/-- Proposition `prop:amgm`: with `m = n - f`, every feasible load `L` is
    positive, at least `(f+1)/m`, and satisfies `4a(1-a)/m ≤ L^2`, that is,
    `L ≥ max{(f+1)/m, 2 sqrt(a(1-a)/m)}`. -/
theorem known_lower (V : Finset ι) (f : ℕ) (hV : f < V.card) (a L : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : Feasible V f a L) :
    0 < L ∧ ((f : ℝ) + 1) / ((V.card : ℝ) - f) ≤ L ∧
      4 * a * (1 - a) / ((V.card : ℝ) - f) ≤ L ^ 2 := by
  obtain ⟨R, W, had, hroutes⟩ := h
  obtain ⟨F, hF, hc⟩ := Finset.exists_subset_card_eq hV.le
  obtain ⟨h1, h2⟩ := known_lower_at had F hF hc a L ha ha1 (hroutes F hF hc.le)
  have hm : (0 : ℝ) < (V.card : ℝ) - f := by
    have : (f : ℝ) < V.card := by exact_mod_cast hV
    linarith
  have hL : 0 < L := by
    by_contra hn
    have : ((V.card : ℝ) - f) * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.mp hn)
    have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
    linarith
  refine ⟨hL, ?_, ?_⟩
  · rw [div_le_iff₀ hm]
    linarith
  · rw [div_le_iff₀ hm]
    linarith

/-! ### Unknown failures (Lemma `lem:contacts`, Theorem `thm:proactive`(1)) -/

/-- A contact set is `f`-resilient for a family when, after deleting any
    `f` servers, it still contains a member of the family. -/
def Resilient (A : Finset (Finset ι)) (f : ℕ) (C : Finset ι) : Prop :=
  ∀ S : Finset ι, S.card ≤ f → ∃ q ∈ A, q ⊆ C \ S

def trimmed (𝒜 : Finset (Finset ι)) (f : ℕ) : Finset (Finset ι) :=
  𝒜.biUnion (fun A => (A.powerset.filter (fun S => S.card ≤ f)).image (fun S => A \ S))

theorem mem_trimmed {𝒜 : Finset (Finset ι)} {f : ℕ} {q : Finset ι} :
    q ∈ trimmed 𝒜 f ↔ ∃ A ∈ 𝒜, ∃ S ⊆ A, S.card ≤ f ∧ q = A \ S := by
  simp only [trimmed, mem_biUnion, mem_image, mem_filter, mem_powerset]
  constructor
  · rintro ⟨A, hA, S, ⟨hS, hc⟩, rfl⟩
    exact ⟨A, hA, S, hS, hc, rfl⟩
  · rintro ⟨A, hA, S, hS, hc, rfl⟩
    exact ⟨A, hA, S, ⟨hS, hc⟩, rfl⟩

theorem trimmed_resilient {𝒜 : Finset (Finset ι)} {f : ℕ} {A : Finset ι} (hA : A ∈ 𝒜) :
    Resilient (trimmed 𝒜 f) f A := by
  intro S hS
  refine ⟨A \ (A ∩ S), mem_trimmed.mpr ⟨A, hA, A ∩ S, inter_subset_left,
    (card_le_card inter_subset_right).trans hS, rfl⟩, ?_⟩
  intro i hi
  obtain ⟨hiA, hn⟩ := mem_sdiff.mp hi
  exact mem_sdiff.mpr ⟨hiA, fun hiS => hn (mem_inter.mpr ⟨hiA, hiS⟩)⟩

/-- Lemma `lem:contacts`. -/
theorem contacts_iff (𝒜 ℬ : Finset (Finset ι)) (V : Finset ι) (f : ℕ)
    (h𝒜 : ∀ A ∈ 𝒜, A ⊆ V) (hℬ : ∀ B ∈ ℬ, B ⊆ V) (hn𝒜 : 𝒜.Nonempty) (hnℬ : ℬ.Nonempty) :
    (∃ R W : Finset (Finset ι), Admissible R W V f ∧
        (∀ A ∈ 𝒜, Resilient R f A) ∧ (∀ B ∈ ℬ, Resilient W f B)) ↔
      ∀ A ∈ 𝒜, ∀ B ∈ ℬ, 2 * f + 1 ≤ (A ∩ B).card := by
  constructor
  · rintro ⟨R, W, had, hRes, hWes⟩ A hA B hB
    by_contra hsmall
    obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq
      (show min f (A ∩ B).card ≤ (A ∩ B).card from min_le_right _ _)
    have hP1 : P.card ≤ f := hPc ▸ min_le_left _ _
    have hP2 : ((A ∩ B) \ P).card ≤ f := by
      rw [Finset.card_sdiff_of_subset hP, hPc]
      omega
    obtain ⟨r, hr, hrsub⟩ := hRes A hA P hP1
    obtain ⟨w, hw, hwsub⟩ := hWes B hB ((A ∩ B) \ P) hP2
    obtain ⟨i, hi⟩ := had.2.2.2.2.1 r hr w hw
    obtain ⟨hir, hiw⟩ := mem_inter.mp hi
    obtain ⟨hiA, hiP⟩ := mem_sdiff.mp (hrsub hir)
    obtain ⟨hiB, hiQ⟩ := mem_sdiff.mp (hwsub hiw)
    exact hiQ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hiA, hiB⟩, hiP⟩)
  · intro hmeet
    refine ⟨trimmed 𝒜 f, trimmed ℬ f, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun A hA => trimmed_resilient hA, fun B hB => trimmed_resilient hB⟩
    · intro r hr
      obtain ⟨A, hA, S, _, _, rfl⟩ := mem_trimmed.mp hr
      exact sdiff_subset.trans (h𝒜 A hA)
    · intro w hw
      obtain ⟨B, hB, S, _, _, rfl⟩ := mem_trimmed.mp hw
      exact sdiff_subset.trans (hℬ B hB)
    · obtain ⟨A, hA⟩ := hn𝒜
      exact ⟨A \ ∅, mem_trimmed.mpr ⟨A, hA, ∅, empty_subset _, by simp, rfl⟩⟩
    · obtain ⟨B, hB⟩ := hnℬ
      exact ⟨B \ ∅, mem_trimmed.mpr ⟨B, hB, ∅, empty_subset _, by simp, rfl⟩⟩
    · intro r hr w hw
      obtain ⟨A, hA, S, _, hSc, rfl⟩ := mem_trimmed.mp hr
      obtain ⟨B, hB, T, _, hTc, rfl⟩ := mem_trimmed.mp hw
      have hsub : (A ∩ B) \ (S ∪ T) ⊆ (A \ S) ∩ (B \ T) := by
        intro i hi
        obtain ⟨hAB, hn⟩ := mem_sdiff.mp hi
        obtain ⟨hiA, hiB⟩ := mem_inter.mp hAB
        exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨hiA, fun h => hn (mem_union_left _ h)⟩,
          mem_sdiff.mpr ⟨hiB, fun h => hn (mem_union_right _ h)⟩⟩
      have hcard : 0 < ((A ∩ B) \ (S ∪ T)).card := by
        have h1 := Finset.le_card_sdiff (S ∪ T) (A ∩ B)
        have h2 := Finset.card_union_le S T
        have h3 := hmeet A hA B hB
        omega
      exact (Finset.card_pos.mp hcard).mono hsub
    · intro F _ hFc
      have live : ∀ 𝒞 : Finset (Finset ι), (∀ C ∈ 𝒞, C ⊆ V) → 𝒞.Nonempty →
          (liveQuorums (trimmed 𝒞 f) V F).Nonempty := by
        intro 𝒞 h𝒞 ⟨C, hC⟩
        refine ⟨C \ (C ∩ F), mem_filter.mpr ⟨mem_trimmed.mpr ⟨C, hC, C ∩ F, inter_subset_left,
          (card_le_card inter_subset_right).trans hFc, rfl⟩, ?_⟩⟩
        intro i hi
        obtain ⟨hiC, hn⟩ := mem_sdiff.mp hi
        exact mem_sdiff.mpr ⟨h𝒞 C hC hiC, fun hiF => hn (mem_inter.mpr ⟨hiC, hiF⟩)⟩
      exact ⟨live 𝒜 h𝒜 hn𝒜, live ℬ hℬ hnℬ⟩

/-- Contact routes chosen before the failures: distributions on the two
    contact families with load at most `L` at every server. -/
def ProactiveRoutes (𝒜 ℬ : Finset (Finset ι)) (V : Finset ι) (a L : ℝ) : Prop :=
  ∃ p q : Finset ι → ℝ,
    (∀ A ∈ 𝒜, 0 ≤ p A) ∧ ∑ A ∈ 𝒜, p A = 1 ∧ (∀ B ∈ ℬ, 0 ≤ q B) ∧ ∑ B ∈ ℬ, q B = 1 ∧
    ∀ i ∈ V, a * incidence 𝒜 p i + (1 - a) * incidence ℬ q i ≤ L

/-- Load `L` is attainable by `f`-resilient contact sets. -/
def ProactiveFeasible (V : Finset ι) (f : ℕ) (a L : ℝ) : Prop :=
  ∃ 𝒜 ℬ : Finset (Finset ι), (∀ A ∈ 𝒜, A ⊆ V) ∧ (∀ B ∈ ℬ, B ⊆ V) ∧
    (∀ A ∈ 𝒜, ∀ B ∈ ℬ, 2 * f + 1 ≤ (A ∩ B).card) ∧ ProactiveRoutes 𝒜 ℬ V a L

theorem routes_nonempty {𝒜 ℬ : Finset (Finset ι)} {V : Finset ι} {a L : ℝ}
    (h : ProactiveRoutes 𝒜 ℬ V a L) : 𝒜.Nonempty ∧ ℬ.Nonempty := by
  obtain ⟨p, q, _, hpn, _, hqn, _⟩ := h
  constructor
  · by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn] at hpn
  · by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn] at hqn

/-- The intersection condition is the same as resilience for some
    admissible pair, so `ProactiveFeasible` is the model of the manuscript. -/
theorem proactive_feasible_iff (V : Finset ι) (f : ℕ) (a L : ℝ) :
    ProactiveFeasible V f a L ↔
      ∃ 𝒜 ℬ : Finset (Finset ι), (∀ A ∈ 𝒜, A ⊆ V) ∧ (∀ B ∈ ℬ, B ⊆ V) ∧
        (∃ R W : Finset (Finset ι), Admissible R W V f ∧
          (∀ A ∈ 𝒜, Resilient R f A) ∧ (∀ B ∈ ℬ, Resilient W f B)) ∧
        ProactiveRoutes 𝒜 ℬ V a L := by
  constructor
  · rintro ⟨𝒜, ℬ, h𝒜, hℬ, hmeet, hr⟩
    obtain ⟨hn𝒜, hnℬ⟩ := routes_nonempty hr
    exact ⟨𝒜, ℬ, h𝒜, hℬ, (contacts_iff 𝒜 ℬ V f h𝒜 hℬ hn𝒜 hnℬ).mpr hmeet, hr⟩
  · rintro ⟨𝒜, ℬ, h𝒜, hℬ, hres, hr⟩
    obtain ⟨hn𝒜, hnℬ⟩ := routes_nonempty hr
    exact ⟨𝒜, ℬ, h𝒜, hℬ, (contacts_iff 𝒜 ℬ V f h𝒜 hℬ hn𝒜 hnℬ).mp hres, hr⟩

/-- Theorem `thm:proactive`(1): with `d = 2f+1`, every load attainable by
    `f`-resilient contact sets is positive, at least `d/n`, and satisfies
    `4 d a(1-a)/n ≤ L^2`, that is, `L ≥ max{d/n, 2 sqrt(d a(1-a)/n)}`. -/
theorem proactive_lower (V : Finset ι) (f : ℕ) (hV : 0 < V.card) (a L : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : ProactiveFeasible V f a L) :
    0 < L ∧ (2 * (f : ℝ) + 1) / V.card ≤ L ∧
      4 * (2 * (f : ℝ) + 1) * (a * (1 - a)) / V.card ≤ L ^ 2 := by
  obtain ⟨𝒜, ℬ, h𝒜, hℬ, hmeet, hr⟩ := h
  obtain ⟨⟨A0, hA0⟩, ⟨B0, hB0⟩⟩ := routes_nonempty hr
  obtain ⟨p, q, hp, hpn, hq, hqn, hload⟩ := hr
  have hn : (0 : ℝ) < V.card := by exact_mod_cast hV
  have hcast : ((2 * f + 1 : ℕ) : ℝ) = 2 * (f : ℝ) + 1 := by push_cast; ring
  have hAm : (2 * (f : ℝ) + 1) ≤ ∑ i ∈ V, incidence 𝒜 p i := by
    apply intersection_mass_bound _ _ _ _ hp hpn
    intro A hA
    rw [Finset.inter_eq_right.mpr (h𝒜 A hA), ← hcast]
    exact_mod_cast (hmeet A hA B0 hB0).trans (card_le_card inter_subset_left)
  have hBm : (2 * (f : ℝ) + 1) ≤ ∑ i ∈ V, incidence ℬ q i := by
    apply intersection_mass_bound _ _ _ _ hq hqn
    intro B hB
    rw [Finset.inter_eq_right.mpr (hℬ B hB), ← hcast]
    exact_mod_cast (hmeet A0 hA0 B hB).trans (card_le_card inter_subset_right)
  have hsum : ∑ i ∈ V, (a * incidence 𝒜 p i + (1 - a) * incidence ℬ q i) ≤ ∑ _i ∈ V, L :=
    Finset.sum_le_sum hload
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have h1 : 2 * (f : ℝ) + 1 ≤ (V.card : ℝ) * L := by
    nlinarith [mul_le_mul_of_nonneg_left hAm ha,
      mul_le_mul_of_nonneg_left hBm (by linarith : (0 : ℝ) ≤ 1 - a)]
  have hprod := product_bound V 𝒜 ℬ p q (2 * f + 1) hp hq hpn hqn (by
    intro A hA B hB
    rw [Finset.inter_eq_right.mpr (inter_subset_left.trans (h𝒜 A hA))]
    exact hmeet A hA B hB)
  have h2 := amgm_load V _ _ a L _ ha ha1 (fun i _ => incidence_nonnegative _ _ hp i)
    (fun i _ => incidence_nonnegative _ _ hq i) hprod hload
  rw [hcast] at h2
  have hL : 0 < L := by
    by_contra hneg
    have : (V.card : ℝ) * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn.le (not_lt.mp hneg)
    have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
    linarith
  refine ⟨hL, ?_, ?_⟩
  · rw [div_le_iff₀ hn]
    linarith
  · rw [div_le_iff₀ hn]
    linarith

#print axioms feasible_symmetry
#print axioms known_lower_at
#print axioms known_lower
#print axioms contacts_iff
#print axioms proactive_feasible_iff
#print axioms proactive_lower
end
end QuorumAudit.Paper
