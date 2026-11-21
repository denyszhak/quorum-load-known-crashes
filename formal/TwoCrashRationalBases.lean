import TwoCrashExpansion
import TwoCrashBases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Int.Interval

namespace QuorumAudit.TwoCrash
open Finset

def rationalRead (g : Gadget) (j : Nat) (i : ℤ) : Bool :=
  (g.reads.getD j []).contains ((i%(nodes g:ℤ)).toNat)
def rationalFlow (g : Gadget) (flow : List Nat) (e : Nat) (i : ℤ) : ℚ :=
  (flow.getD (2*(i%(nodes g:ℤ)).toNat+e) 0:ℚ)/g.scale
def degreeQ (w₁ w₂ : ℤ → ℚ) (i : ℤ) : ℚ :=
  w₁ i+w₁ (i-1)+w₁ (i-2)+w₂ i+w₂ (i-2)+w₂ (i-4)
def countQ (r : Nat → ℤ → Bool) (i : ℤ) : ℚ :=
  ∑ j ∈ range 3, if r j i then 1 else 0
def massQ (n : Nat) (f : ℤ → ℚ) : ℚ := ∑ i ∈ range n, f i
def residueQ (w₁ w₂ : ℤ → ℚ) (p : ℤ) : ℚ :=
  w₁ p+w₁ (p+1)+w₁ (p+2)+w₂ p+w₂ (p+1)+w₂ (p+2)

def RationalReady (g : Gadget) : Prop :=
  3 ≤ rankParameter g ∧ nodes g=3*rankParameter g+2 ∧
  0 < g.a+1 ∧ g.a+1 < nodes g ∧
  (∀ j ∈ range 3,
    massQ (nodes g) (fun i => if rationalRead g j i then 1 else 0)=rankParameter g+2 ∧
    rationalRead g j 0=false ∧ rationalRead g j (g.a+1:Nat)=false ∧
    ∀ i ∈ Ico (0:ℤ) (nodes g), ∀ e ∈ ({1,2}:Finset ℤ),
      rationalRead g j i=true ∨ rationalRead g j (i+e)=true ∨
        rationalRead g j (i+2*e)=true) ∧
  (∀ i ∈ Ico (0:ℤ) (nodes g),
    degreeQ (rationalFlow g g.uniform 0) (rationalFlow g g.uniform 1) i =
      (if i=0 ∨ i=(g.a+1:Nat) then 0 else 1) ∧
    degreeQ (rationalFlow g g.criticalFlow 0) (rationalFlow g g.criticalFlow 1) i =
      if i=0 ∨ i=(g.a+1:Nat) then 0 else rankParameter g+2-countQ (rationalRead g) i) ∧
  massQ (nodes g) (rationalFlow g g.uniform 0)+
    massQ (nodes g) (rationalFlow g g.uniform 1)=rankParameter g ∧
  massQ (nodes g) (rationalFlow g g.criticalFlow 0)+
    massQ (nodes g) (rationalFlow g g.criticalFlow 1)=
      (rankParameter g-1:ℚ)*(rankParameter g+2)

instance (g : Gadget) : Decidable (RationalReady g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def RationalCut (g : Gadget) (p : Nat) : Prop :=
  5 ≤ p ∧ p+7 ≤ nodes g ∧ (p+3 ≤ g.a+1 ∨ g.a+1 < p) ∧
  (∀ j ∈ range 3,
    (∀ i ∈ Icc ((p:ℤ)-4) ((p:ℤ)+3),
      rationalRead g j i=rationalRead g j ((p:ℤ)+(i-p)%3)) ∧
    ((if rationalRead g j p then (1:ℚ) else 0)+
      (if rationalRead g j (p+1) then 1 else 0)+
      (if rationalRead g j (p+2) then 1 else 0)=1)) ∧
  (∀ i ∈ Icc (p:ℤ) ((p:ℤ)+2), countQ (rationalRead g) i=1) ∧
  (∀ i ∈ Ico ((p:ℤ)-4) p,
    rationalFlow g g.uniform 0 i=rationalFlow g g.uniform 0 (i+3) ∧
    rationalFlow g g.uniform 1 i=rationalFlow g g.uniform 1 (i+3) ∧
    rationalFlow g g.criticalFlow 0 i=rationalFlow g g.criticalFlow 0 (i+3) ∧
    rationalFlow g g.criticalFlow 1 i=rationalFlow g g.criticalFlow 1 (i+3)) ∧
  residueQ (rationalFlow g g.uniform 0) (rationalFlow g g.uniform 1) p=1 ∧
  residueQ (rationalFlow g g.criticalFlow 0) (rationalFlow g g.criticalFlow 1) p=
    rankParameter g+1

instance (g : Gadget) (p : Nat) : Decidable (RationalCut g p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def ExpansionReady (g : Gadget) : Prop :=
  RationalReady g ∧ (∀ p ∈ g.cuts, RationalCut g p) ∧
  (15 ≤ g.a → ∃ p ∈ range (nodes g), p ∈ g.cuts ∧ p+7 ≤ g.a+1) ∧
  (15 ≤ g.b → ∃ p ∈ range (nodes g), p ∈ g.cuts ∧ g.a+6 ≤ p) ∧
  (∀ p ∈ g.cuts, ∀ q ∈ g.cuts, p+7 ≤ g.a+1 → g.a+6 ≤ q → p+12 ≤ q)

instance (g : Gadget) : Decidable (ExpansionReady g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

noncomputable section

@[simp] theorem cast_sumQ {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ((∑ i ∈ s, f i:ℚ):ℝ) = ∑ i ∈ s, (f i:ℝ) := map_sum (Rat.castHom ℝ) f s

theorem cast_massQ (n : Nat) (f : ℤ → ℚ) :
    cycleMass n (fun i => (f i:ℝ)) = (massQ n f:ℝ) := by
  simp [cycleMass, massQ]
theorem cast_degreeQ (f g : ℤ → ℚ) (i : ℤ) :
    localDegree (fun j => (f j:ℝ)) (fun j => (g j:ℝ)) i = (degreeQ f g i:ℝ) := by
  simp [localDegree, degreeQ]
theorem cast_countQ (r : Nat → ℤ → Bool) (i : ℤ) :
    readCountReal r i = (countQ r i:ℝ) := by
  simp [readCountReal, countQ, indicator]
theorem cast_residueQ (f g : ℤ → ℚ) (p : ℤ) :
    residueTotal (fun j => (f j:ℝ)) (fun j => (g j:ℝ)) p = (residueQ f g p:ℝ) := by
  simp [residueTotal, residueQ]

def rationalWitness (g : Gadget) (h : RationalReady g) :
    CycleWitness (nodes g) (rankParameter g) (g.a+1) where
  read := rationalRead g
  u₁ := fun i => (rationalFlow g g.uniform 0 i:ℝ)
  u₂ := fun i => (rationalFlow g g.uniform 1 i:ℝ)
  c₁ := fun i => (rationalFlow g g.criticalFlow 0 i:ℝ)
  c₂ := fun i => (rationalFlow g g.criticalFlow 1 i:ℝ)
  size := h.2.1
  rank := h.1
  failure_pos := h.2.2.1
  failure_lt := h.2.2.2.1
  read_period := by intro j i; simp [rationalRead]
  u₁_period := by intro i; simp [rationalFlow]
  u₂_period := by intro i; simp [rationalFlow]
  c₁_period := by intro i; simp [rationalFlow]
  c₂_period := by intro i; simp [rationalFlow]
  u₁_nonneg := by intro i; unfold rationalFlow; positivity
  u₂_nonneg := by intro i; unfold rationalFlow; positivity
  c₁_nonneg := by intro i; unfold rationalFlow; positivity
  c₂_nonneg := by intro i; unfold rationalFlow; positivity
  read_mass := by
    intro j hj
    have hm := (h.2.2.2.2.1 j hj).1
    have hc := congrArg (fun q:ℚ => (q:ℝ)) hm
    simpa [massQ, cycleMass, indicator] using hc
  read_dead := by
    intro j hj
    exact ⟨(h.2.2.2.2.1 j hj).2.1, (h.2.2.2.2.1 j hj).2.2.1⟩
  read_hit := by
    intro j hj i e hi hi2 he
    exact (h.2.2.2.2.1 j hj).2.2.2 i (mem_Ico.mpr ⟨hi,hi2⟩)
      e (by simpa only [mem_insert, mem_singleton] using he)
  u_degree := by
    intro i hi hi2
    rw [cast_degreeQ, (h.2.2.2.2.2.1 i (mem_Ico.mpr ⟨hi,hi2⟩)).1]
    split_ifs <;> norm_num
  c_degree := by
    intro i hi hi2
    rw [cast_degreeQ, (h.2.2.2.2.2.1 i (mem_Ico.mpr ⟨hi,hi2⟩)).2, cast_countQ]
    split_ifs <;> push_cast <;> rfl
  u_mass := by
    unfold flowTotal
    rw [cast_massQ, cast_massQ, ← Rat.cast_add, h.2.2.2.2.2.2.1]
    norm_cast
  c_mass := by
    unfold flowTotal
    rw [cast_massQ, cast_massQ, ← Rat.cast_add, h.2.2.2.2.2.2.2]
    push_cast
    rfl

theorem rational_cut_sound (g : Gadget) (h : RationalReady g) (p : Nat)
    (hc : RationalCut g p) : Cut (rationalWitness g h) p := by
  obtain ⟨hleft,hright,ha,hr,hcount,hflow,hu,hc⟩ := hc
  refine ⟨hleft,hright,ha,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj i hi hi2
    exact (hr j hj).1 i (mem_Icc.mpr ⟨hi,hi2⟩)
  · intro j hj
    have hh := congrArg (fun q:ℚ => (q:ℝ)) (hr j hj).2
    change indicator (rationalRead g j p)+indicator (rationalRead g j (p+1))+
      indicator (rationalRead g j (p+2))=1
    cases h₀ : rationalRead g j p <;> cases h₁ : rationalRead g j (p+1) <;>
      cases h₂ : rationalRead g j (p+2)
    all_goals norm_num [h₀,h₁,h₂,indicator] at hh
    all_goals norm_num [h₀,h₁,h₂,indicator]
  · intro i hi hi2
    change readCountReal (rationalRead g) i=1
    rw [cast_countQ, hcount i (mem_Icc.mpr ⟨hi,hi2⟩)]
    norm_num
  · intro i hi hi2
    exact congrArg (fun q:ℚ => (q:ℝ)) (hflow i (mem_Ico.mpr ⟨hi,hi2⟩)).1
  · intro i hi hi2
    exact congrArg (fun q:ℚ => (q:ℝ)) (hflow i (mem_Ico.mpr ⟨hi,hi2⟩)).2.1
  · intro i hi hi2
    exact congrArg (fun q:ℚ => (q:ℝ)) (hflow i (mem_Ico.mpr ⟨hi,hi2⟩)).2.2.1
  · intro i hi hi2
    exact congrArg (fun q:ℚ => (q:ℝ)) (hflow i (mem_Ico.mpr ⟨hi,hi2⟩)).2.2.2
  · change residueTotal (fun i => (rationalFlow g g.uniform 0 i:ℝ))
      (fun i => (rationalFlow g g.uniform 1 i:ℝ)) p=1
    rw [cast_residueQ, hu]
    norm_num
  · change residueTotal (fun i => (rationalFlow g g.criticalFlow 0 i:ℝ))
      (fun i => (rationalFlow g g.criticalFlow 1 i:ℝ)) p=rankParameter g+1
    rw [cast_residueQ, hc]
    norm_cast

#print axioms rationalWitness
#print axioms rational_cut_sound
end
end QuorumAudit.TwoCrash
