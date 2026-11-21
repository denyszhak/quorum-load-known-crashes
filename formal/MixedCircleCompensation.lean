import MixedCircleCertificates
import GeneralFWeights

set_option maxHeartbeats 4000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def widenRoute {ι : Type*} [DecidableEq ι] {A B : Finset (Finset ι)} {U F : Finset ι}
    (route : Routing A U F) (hAB : A ⊆ B) : Routing B U F where
  quorums := route.quorums
  subset := route.subset.trans hAB
  live := route.live
  p := route.p
  nonnegative := route.nonnegative
  normalized := route.normalized

theorem failed_incidence_zero {ι : Type*} [DecidableEq ι]
    {R : Finset (Finset ι)} {U F : Finset ι} (route : Routing R U F) (i : ι) (hi : i ∈ F) :
    incidence route.quorums route.p i = 0 := by
  apply sum_eq_zero
  intro q hq
  exact ite_eq_right (fun hiq => (mem_sdiff.mp (route.live q hq hiq)).2 hi)

theorem read_incidence_total (r : ℕ) (hrn : r ≤ n) (F : Finset (ZMod n))
    (read : Routing (reads n r) univ F) :
    (∑ i : ZMod n, incidence read.quorums read.p i) = (r : ℝ) := by
  rw [sum_incidence]
  have he : ∀ q ∈ read.quorums, ((univ ∩ q).card : ℝ) * read.p q = (r : ℝ) * read.p q := by
    intro q hq
    obtain ⟨s, _, rfl⟩ := mem_image.mp (read.subset hq)
    simp [arc_card r hrn s]
  rw [sum_congr rfl he, ← mul_sum, read.normalized, mul_one]

theorem compensation_attains (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (F : Finset (ZMod n)) (hF : F.card = 2)
    (read : Routing (reads n r) univ F) (X : ZMod n → ℕ)
    (h μ C : ℕ) (hp : 0 < h)
    (hread : ∀ i, incidence read.quorums read.p i = (X i : ℝ) / h)
    (hmix : (μ : ℝ) = mixture r * h) (hcap : (C : ℝ) = cap r * h)
    (q : Finset (ZMod n)) (hq : q ∈ rankedWrites n r r) (hqlive : q ⊆ univ \ F)
    (hpoint : ∀ i ∈ univ \ F, incidence read.quorums read.p i ≤ ((r : ℝ) + 1) / den r)
    (hwindow : ∀ s : ZMod n,
      (∑ i ∈ arc r s, incidence read.quorums read.p i) +
      mixture r * ((arc r s ∩ q).card : ℝ) + (1 - mixture r) ≤
      cap r * ((arc r s \ F).card : ℝ)) :
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i ∈ univ \ F, combined read write (1 / 2) i = cap r / 2 := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hd := den_pos r hrR
  have hpR : (0 : ℝ) < h := by exact_mod_cast hp
  have hne : (h : ℝ) ≠ 0 := ne_of_gt hpR
  obtain ⟨hm0, hm1, hc0⟩ := parameters r hrR
  have hμlt : μ < h := by
    have hh : (μ : ℝ) < h := by nlinarith
    exact_mod_cast hh
  let hz := h - μ
  have hzp : 0 < hz := by dsimp [hz]; omega
  letI : NeZero hz := ⟨ne_of_gt hzp⟩
  have hzR : (hz : ℝ) = (1 - mixture r) * h := by
    dsimp [hz]
    rw [Nat.cast_sub (by omega : μ ≤ h), hmix]
    ring
  let Y : ZMod n → ℕ := fun i => if i ∈ q then μ else 0
  let z : ZMod n → ℕ := fun i => if i ∈ F then 0 else C - (X i + Y i)
  have hYfrac : ∀ i, (Y i : ℝ) / h ≤ mixture r := by
    intro i
    dsimp [Y]
    split_ifs
    · rw [hmix]
      field_simp
      exact le_refl _
    · simpa using hm0
  have hbound : ∀ i ∉ F, X i + Y i ≤ C := by
    intro i hiF
    have hpt := hpoint i (mem_sdiff.mpr ⟨mem_univ _, hiF⟩)
    rw [hread] at hpt
    have hres := residual_positive r ((X i : ℝ) / h) ((Y i : ℝ) / h) hrR hpt (hYfrac i)
    have hxy : ((X i + Y i : ℕ) : ℝ) / h ≤ cap r := by
      push_cast
      rw [add_div]
      have : (0 : ℝ) ≤ 3 / den r := div_nonneg (by norm_num) (le_of_lt hd)
      linarith
    have hh := (div_le_iff₀ hpR).mp hxy
    rw [← hcap] at hh
    exact_mod_cast hh
  have hXzero : ∀ i ∈ F, X i = 0 := by
    intro i hi
    have hh := failed_incidence_zero read i hi
    rw [hread] at hh
    have hreal : (X i : ℝ) = 0 := (div_eq_zero_iff).mp hh |>.resolve_right hne
    exact_mod_cast hreal
  have hYzero : ∀ i ∈ F, Y i = 0 := by
    intro i hi
    have hiq : i ∉ q := fun h => (mem_sdiff.mp (hqlive h)).2 hi
    simp [Y, hiq]
  have hnode : ∀ i, X i + Y i + z i = GeneralF.uniformWeight F C i := by
    intro i
    by_cases hi : i ∈ F
    · simp [z, hi, hXzero i hi, hYzero i hi, GeneralF.uniformWeight]
    · have hb := hbound i hi
      simp only [z, ite_eq_right hi, GeneralF.uniformWeight]
      omega
  have hYsum : ∀ A : Finset (ZMod n), (∑ i ∈ A, Y i) = (A ∩ q).card * μ := by
    intro A
    dsimp [Y]
    rw [← sum_filter, filter_mem_eq_inter]
    simp
  have hlocalsum : ∀ A : Finset (ZMod n),
      (∑ i ∈ A, X i) + (∑ i ∈ A, Y i) + (∑ i ∈ A, z i) = (A \ F).card * C := by
    intro A
    have hs : A.sum (fun i => X i + Y i + z i) = A.sum (GeneralF.uniformWeight F C) :=
      sum_congr rfl (fun i _ => hnode i)
    rw [sum_add_distrib, sum_add_distrib, GeneralF.uniform_sum] at hs
    exact hs
  have hrn : r ≤ n := by nlinarith
  have hXsum : (∑ i : ZMod n, X i) = r * h := by
    have hs := read_incidence_total r hrn F read
    simp only [hread, ← sum_div] at hs
    have hs' : ((∑ i : ZMod n, X i) : ℝ) / h = (r : ℝ) := by
      simpa only [Nat.cast_sum] using hs
    have hh := (div_eq_iff hne).mp hs'
    exact_mod_cast hh
  have hqcard : q.card = r := (mem_filter.mp hq).2
  have hglobal := hlocalsum univ
  have hlc : ((univ : Finset (ZMod n)) \ F).card = n - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card, hF]
  rw [hXsum, hYsum, univ_inter, hqcard, hlc] at hglobal
  have hmR := residual_mass r hrR
  have hmass : (((r : ℝ) ^ 2 - 3) * C - r * h - r * μ) = (r + 1) * hz := by
    calc
      _ = (((r : ℝ) ^ 2 - 3) * cap r - r - r * mixture r) * h := by
        rw [hcap, hmix]; ring
      _ = ((r + 1) * (1 - mixture r)) * h := by rw [hmR]
      _ = _ := by rw [hzR]; ring
  have hnR : (n : ℝ) + 1 = (r : ℝ) * r := by exact_mod_cast hn
  have hglobalR : (r : ℝ) * h + r * μ + (∑ i : ZMod n, (z i : ℝ)) = ((n : ℝ) - 2) * C := by
    have hh := congrArg (fun a : ℕ => (a : ℝ)) hglobal
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_sub (by nlinarith : 2 ≤ n), Nat.cast_ofNat] using hh
  have hzTotal : (∑ i : ZMod n, z i) = (r + 1) * hz := by
    have hh : (∑ i : ZMod n, (z i : ℝ)) = ((r : ℝ) + 1) * hz := by nlinarith
    exact_mod_cast hh
  have hCz : C ≤ hz := by
    have hh := mul_le_mul_of_nonneg_right hc0 (le_of_lt hpR)
    rw [← hcap, ← hzR] at hh
    exact_mod_cast hh
  have hzBound : ∀ i, z i ≤ hz := by
    intro i
    dsimp [z]
    split_ifs <;> omega
  have hzZero : ∀ i ∈ F, z i = 0 := by intro i hi; simp [z, hi]
  have hzWindow : ∀ s : ZMod n, hz ≤ ∑ i ∈ arc r s, z i := by
    intro s
    let A := arc r s
    have hs := hlocalsum A
    rw [hYsum] at hs
    have hsR : (∑ i ∈ A, (X i : ℝ)) + ((A ∩ q).card : ℝ) * μ +
        (∑ i ∈ A, (z i : ℝ)) = ((A \ F).card : ℝ) * C := by exact_mod_cast hs
    have hw := hwindow s
    have hXlocal : (∑ i ∈ A, incidence read.quorums read.p i) = (∑ i ∈ A, (X i : ℝ)) / h := by
      simp only [hread, sum_div]
    change (∑ i ∈ A, incidence read.quorums read.p i) + mixture r * ((A ∩ q).card : ℝ) +
      (1 - mixture r) ≤ cap r * ((A \ F).card : ℝ) at hw
    rw [hXlocal] at hw
    have hwm := mul_le_mul_of_nonneg_right hw (le_of_lt hpR)
    have heL : (((∑ i ∈ A, (X i : ℝ)) / h + mixture r * ((A ∩ q).card : ℝ) +
        (1 - mixture r)) * h) =
        (∑ i ∈ A, (X i : ℝ)) + ((A ∩ q).card : ℝ) * μ + hz := by
      rw [hmix, hzR]
      field_simp
    have heR : cap r * ((A \ F).card : ℝ) * h = ((A \ F).card : ℝ) * C := by rw [hcap]; ring
    rw [heL, heR] at hwm
    have hh : (hz : ℝ) ≤ ∑ i ∈ A, (z i : ℝ) := by linarith
    exact_mod_cast hh
  obtain ⟨large, hlarge⟩ := exact_ranked_sampled_routing (h := hz) z F r (r + 1) hrn
    hzTotal hzBound hzZero hzWindow
  let large' := widenRoute large (subset_union_right : rankedWrites n r (r + 1) ⊆ mixedWrites n r)
  let small : Routing (mixedWrites n r) univ F := {
    quorums := {q}
    subset := by intro a ha; rw [mem_singleton.mp ha]; exact mem_union_left _ hq
    live := by intro a ha; simpa only [mem_singleton.mp ha] using hqlive
    p := fun _ => 1
    nonnegative := by intros; norm_num
    normalized := by simp }
  have hsmall : ∀ i, incidence small.quorums small.p i = if i ∈ q then 1 else 0 := by
    intro i
    change (∑ a ∈ {q}, if i ∈ a then (1 : ℝ) else 0) = _
    rw [sum_singleton]
  let write := GeneralF.mixed_route small large' (mixture r) hm0 (le_of_lt hm1)
  refine ⟨write, ?_⟩
  intro i hi
  have hbig : (1 - mixture r) * ((z i : ℝ) / hz) = (z i : ℝ) / h := by
    rw [hzR]
    field_simp [ne_of_gt (by linarith : 0 < 1 - mixture r)]
  have hsmall' : mixture r * (if i ∈ q then (1 : ℝ) else 0) = (Y i : ℝ) / h := by
    dsimp [Y]
    split_ifs <;> simp
    rw [hmix]
    field_simp
  have hnodeR : (X i : ℝ) + Y i + z i = (C : ℝ) := by
    have hh := hnode i
    rw [GeneralF.uniformWeight, ite_eq_right (mem_sdiff.mp hi).2] at hh
    exact_mod_cast hh
  unfold combined
  have hwriteInc := GeneralF.mixed_incidence small large' (mixture r) hm0 (le_of_lt hm1) i
  change incidence write.quorums write.p i = _ at hwriteInc
  have hlarge' : incidence large'.quorums large'.p i = (z i : ℝ) / hz := hlarge i
  rw [hwriteInc, hread, hsmall, hlarge', hbig, hsmall']
  calc
    _ = ((X i : ℝ) + Y i + z i) / (2 * h) := by ring
    _ = (C : ℝ) / (2 * h) := by rw [hnodeR]
    _ = cap r / 2 := by rw [hcap]; field_simp

#print axioms compensation_attains
end
end QuorumAudit.MixedCircle
