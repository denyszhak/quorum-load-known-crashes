import TwoCrashWitness

/-! Relabeling actual routing objects. Injectivity is required only on
the finite server universe; no global permutation of natural numbers is
silently assumed. All load identities refer to normalized real routing. -/
namespace QuorumAudit
namespace TwoCrash
noncomputable section
open scoped BigOperators
open Finset
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem image_live (V F q : Finset ι) (f : ι → κ)
    (hF : F ⊆ V) (hinj : Set.InjOn f V) (hq : q ⊆ V \ F) :
    q.image f ⊆ V.image f \ F.image f := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  have hiV := (mem_sdiff.mp (hq hi)).1
  refine mem_sdiff.mpr ⟨mem_image_of_mem f hiV, ?_⟩
  intro hbad
  obtain ⟨j, hj, heq⟩ := mem_image.mp hbad
  have hji : j=i := hinj (hF hj) hiV heq
  exact (mem_sdiff.mp (hq hi)).2 (hji ▸ hj)

def imageRouting {family : Finset (Finset ι)} {V F : Finset ι}
    (r : Routing family V F) (f : ι → κ) (hF : F ⊆ V)
    (hinj : Set.InjOn f V) :
    Routing (family.image (fun q => q.image f)) (V.image f) (F.image f) :=
  routing_from_indexed r.quorums (fun q => q.image f) r.p _ _ _
    (by intro q hq; exact mem_image_of_mem _ (r.subset hq))
    (by intro q hq; exact image_live V F q f hF hinj (r.live q hq))
    r.nonnegative r.normalized

theorem imageRouting_incidence {family : Finset (Finset ι)} {V F : Finset ι}
    (r : Routing family V F) (f : ι → κ) (hF : F ⊆ V)
    (hinj : Set.InjOn f V) (i : ι) (hi : i∈V) :
    incidence (imageRouting r f hF hinj).quorums (imageRouting r f hF hinj).p (f i) =
      incidence r.quorums r.p i := by
  change incidence (r.quorums.image (fun q => q.image f))
    (mergedProbability r.quorums (fun q => q.image f) r.p) (f i) = _
  rw [merged_incidence]
  unfold incidence
  apply sum_congr rfl
  intro q hq
  have he : f i∈q.image f ↔ i∈q := by
    constructor
    · intro hm
      obtain ⟨j, hj, heq⟩ := mem_image.mp hm
      have hjV := (mem_sdiff.mp (r.live q hq hj)).1
      have hji : j=i := hinj hjV hi heq
      exact hji ▸ hj
    · exact mem_image_of_mem f
  simp only [he]

theorem imageRouting_combined {R W : Finset (Finset ι)} {V F : Finset ι}
    (r : Routing R V F) (w : Routing W V F)
    (f : ι → κ) (hF : F ⊆ V) (hinj : Set.InjOn f V)
    (a : ℝ) (i : ι) (hi : i∈V) :
    combined (imageRouting r f hF hinj) (imageRouting w f hF hinj) a (f i) =
      combined r w a i := by
  unfold combined
  rw [imageRouting_incidence r f hF hinj i hi,
    imageRouting_incidence w f hF hinj i hi]

theorem imageRouting_bound {R W : Finset (Finset ι)} {V F : Finset ι}
    (r : Routing R V F) (w : Routing W V F)
    (f : ι → κ) (hF : F ⊆ V) (hinj : Set.InjOn f V)
    (a L : ℝ) (hL : ∀ i∈V, combined r w a i≤L) :
    ∀ x∈V.image f,
      combined (imageRouting r f hF hinj) (imageRouting w f hF hinj) a x≤L := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  rw [imageRouting_combined r w f hF hinj a i hi]
  exact hL i hi

theorem image_safety (R W : Finset (Finset ι)) (f : ι → κ)
    (h : ∀ r∈R, ∀ w∈W, (r∩w).Nonempty) :
    ∀ r∈R.image (fun q => q.image f),
      ∀ w∈W.image (fun q => q.image f), (r∩w).Nonempty := by
  intro r hr w hw
  obtain ⟨r0, hr0, rfl⟩ := mem_image.mp hr
  obtain ⟨w0, hw0, rfl⟩ := mem_image.mp hw
  obtain ⟨i, hi⟩ := h r0 hr0 w0 hw0
  exact ⟨f i, mem_inter.mpr ⟨mem_image_of_mem f (mem_inter.mp hi).1,
    mem_image_of_mem f (mem_inter.mp hi).2⟩⟩

#print axioms imageRouting
#print axioms imageRouting_combined
#print axioms imageRouting_bound
#print axioms image_safety
end
end TwoCrash
end QuorumAudit
