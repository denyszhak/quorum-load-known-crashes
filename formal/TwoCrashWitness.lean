import ConstructiveRouting
import CertificateChecker

/-! Semantic interpretation of the two-crash integer witnesses.
The families below are fixed globally. Reads meet every write, including
writes that are unavailable in the particular failure scenario. -/
namespace QuorumAudit
namespace TwoCrash
open scoped BigOperators
open Finset

def writeSet (n j : Nat) : Finset Nat := (triple n j).toFinset
def writes (n : Nat) : Finset (Finset Nat) := (range (2*n)).image (writeSet n)
def reads (n k : Nat) : Finset (Finset Nat) :=
  (range n).powerset.filter fun r => r.card = k+2 ∧
    ∀ w ∈ writes n, (r ∩ w).Nonempty
def failures (g : Gadget) : Finset Nat := {0, g.a+1}
def readSet (g : Gadget) (j : Nat) : Finset Nat := (g.reads.getD j []).toFinset
def support (g : Gadget) : Finset Nat :=
  (range (2*nodes g)).filter fun j =>
    0 < g.uniform.getD j 0 + g.criticalFlow.getD j 0
def multiplicity (g : Gadget) (i : Nat) : Nat :=
  ∑ j ∈ range 3, if i ∈ readSet g j then 1 else 0
def flowMass (g : Gadget) (flow : List Nat) : Nat :=
  ∑ j ∈ support g, flow.getD j 0
def flowDegree (g : Gadget) (flow : List Nat) (i : Nat) : Nat :=
  ∑ j ∈ support g, if i ∈ writeSet (nodes g) j then flow.getD j 0 else 0

def ReadValid (n k : Nat) (r : Finset Nat) : Prop :=
  r ⊆ range n ∧ r.card = k+2 ∧
    ∀ j ∈ range (2*n), (r ∩ writeSet n j).Nonempty

instance (n k : Nat) (r : Finset Nat) : Decidable (ReadValid n k r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem ReadValid.mem {n k : Nat} {r : Finset Nat} (h : ReadValid n k r) :
    r ∈ reads n k := by
  refine mem_filter.mpr ⟨mem_powerset.mpr h.1, h.2.1, ?_⟩
  intro w hw
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
  exact h.2.2 j hj

/-- Direct, decidable semantic conditions, rechecked in the Lean kernel.
The positive-flow support permits zero entries on unavailable writes. -/
def Valid (g : Gadget) : Prop :=
  3 ≤ rankParameter g ∧ nodes g = 3*rankParameter g+2 ∧ 0 < g.scale ∧
  failures g ⊆ range (nodes g) ∧ (failures g).card = 2 ∧
  (∀ j ∈ range 3,
    ReadValid (nodes g) (rankParameter g) (readSet g j) ∧
    readSet g j ⊆ range (nodes g) \ failures g) ∧
  (∀ j ∈ support g, writeSet (nodes g) j ⊆ range (nodes g) \ failures g) ∧
  flowMass g g.uniform = rankParameter g*g.scale ∧
  flowMass g g.criticalFlow = (rankParameter g-1)*(rankParameter g+2)*g.scale ∧
  (∀ i ∈ range (nodes g) \ failures g,
    flowDegree g g.uniform i = g.scale ∧
    flowDegree g g.criticalFlow i + multiplicity g i*g.scale =
      (rankParameter g+2)*g.scale)

instance (g : Gadget) : Decidable (Valid g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem read_family_safe (n k : Nat) :
    ∀ r ∈ reads n k, ∀ w ∈ writes n, (r ∩ w).Nonempty := by
  intro r hr w hw
  exact (mem_filter.mp hr).2.2 w hw

noncomputable section

def coefficient (g : Gadget) (flow : List Nat) (j : Nat) : ℝ :=
  (flow.getD j 0 : ℝ) / g.scale

theorem coefficient_mass (g : Gadget) (flow : List Nat) :
    (∑ j ∈ support g, coefficient g flow j) = (flowMass g flow : ℝ)/g.scale := by
  unfold coefficient flowMass
  rw [← sum_div]
  congr 1
  simp

theorem coefficient_degree (g : Gadget) (flow : List Nat) (i : Nat) :
    (∑ j ∈ support g, if i ∈ writeSet (nodes g) j then coefficient g flow j else 0) =
      (flowDegree g flow i : ℝ)/g.scale := by
  unfold coefficient flowDegree
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [sum_div]
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem multiplicity_real (g : Gadget) (i : Nat) :
    (multiplicity g i : ℝ) = readMultiplicity (readSet g) i := by
  simp [multiplicity, readMultiplicity]

/-- A checked integer witness supplies actual normalized real-valued
read and write routings throughout the complete workload interval. -/
theorem sound (g : Gadget) (h : Valid g) (a : ℝ)
    (ha : 0 ≤ a) (haReg : a ≤ critical (rankParameter g)) :
    ∃ r : Routing (reads (nodes g) (rankParameter g)) (range (nodes g)) (failures g),
    ∃ w : Routing (writes (nodes g)) (range (nodes g)) (failures g),
      ∀ i ∈ range (nodes g), combined r w a i ≤ target (rankParameter g) a := by
  obtain ⟨hk, _, hs, _, _, hr, hw, huMass, hcMass, hdeg⟩ := h
  have hkR : (3 : ℝ) ≤ rankParameter g := by exact_mod_cast hk
  have hsR : (g.scale : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  apply upper_routing_from_witnesses _ _ _ _ (readSet g) (support g)
    (writeSet (nodes g)) (coefficient g g.criticalFlow) (coefficient g g.uniform)
    (rankParameter g) a hkR ha haReg
  · intro j hj; exact (hr j hj).1.mem
  · intro j hj; exact (hr j hj).2
  · intro j hj
    exact mem_image_of_mem _ (mem_filter.mp hj).1
  · exact hw
  · intro j _; unfold coefficient; positivity
  · intro j _; unfold coefficient; positivity
  · rw [coefficient_mass, hcMass]
    push_cast [Nat.cast_sub (by omega : 1 ≤ rankParameter g)]
    field_simp
  · rw [coefficient_mass, huMass]
    push_cast
    exact mul_div_cancel_right₀ _ hsR
  · intro i hi
    rw [coefficient_degree]
    have hd : (flowDegree g g.criticalFlow i : ℝ) +
        (multiplicity g i : ℝ)*g.scale = (rankParameter g+2 : ℝ)*g.scale := by
      exact_mod_cast (hdeg i hi).2
    rw [multiplicity_real] at hd
    apply (div_eq_iff hsR).mpr
    linarith
  · intro i hi
    rw [coefficient_degree, (hdeg i hi).1, div_self hsR]

#print axioms sound
end
end TwoCrash
end QuorumAudit
