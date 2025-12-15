import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.ProperAction.ProperlyDiscontinuous
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering

open Topology Manifold

noncomputable section

-- See `DifferentialGeometry.lean` for a quick overview to differential geometry in Lean.

-- `M` be a smooth manifold, modelled over the pair `(E, H)`
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}
  [IsManifold I n M]

-- Let `G` be a group acting properly discontinuously on `M`.
variable {G : Type*} [Group G] [MulAction G M] [ProperlyDiscontinuousSMul G M]

-- Consider the quotient space `M / G`. For now, let's give this a special name.
variable (G M) in
abbrev OrbitSpace := MulAction.orbitRel.Quotient G M

-- This is the quotient map from `M` to the orbit space `M / G`.
example : M → OrbitSpace M G := Quotient.mk _

section prerequisites

-- Mathlib already knows this is a topological space,
example : TopologicalSpace (OrbitSpace M G) := by infer_instance

-- and that the quotient map is continuous.
example : Continuous (Quotient.mk _ : M → (OrbitSpace M G)) := { isOpen_preimage := fun _s a ↦ a }

omit [ProperlyDiscontinuousSMul G M] in
example : IsQuotientMap (Quotient.mk _ : M → OrbitSpace M G) := isQuotientMap_quotient_mk'

variable [ContinuousConstSMul G M]
omit [ProperlyDiscontinuousSMul G M] in
example : IsOpenQuotientMap (Quotient.mk _ : M → OrbitSpace M G) :=
  MulAction.isOpenQuotientMap_quotientMk

open Pointwise

-- TODO: give this a proper name!
-- This follows from mathlib's definition of a properly discontinuous action.
-- No need to work on this; it's proven in mathlib PR #7596.
variable (G) in
lemma baz (p : M) :
    ∃ (U : Set M), IsOpen U ∧ p ∈ U ∧ ∀ g h : G, g • U ≠ h • U → Disjoint (g • U) (h • U)  := by
  sorry

-- This follows from mathlib's definition of a properly discontinuous action.
-- No need to work on this; it's proven in mathlib PR #7596.
lemma isCoveringMap_quotientMk : IsCoveringMap (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry -- use `baz`

lemma isLocalHomeomorph : IsLocalHomeomorph (Quotient.mk _ : M → OrbitSpace M G) :=
  isCoveringMap_quotientMk.isLocalHomeomorph

variable (G) in
def aux (p : M) : OpenPartialHomeomorph M (OrbitSpace M G) :=
  Classical.choose (isLocalHomeomorph (G := G) (M := M) p)

variable (G) in
lemma aux_prop (p : M) : p ∈ (aux G p).source :=
  (Classical.choose_spec (isLocalHomeomorph (G := G) (M := M) p)).1

variable (G) in
lemma aux_eq (p : M) : aux G p = (Quotient.mk _ : M → (OrbitSpace M G)) :=
  (Classical.choose_spec (isLocalHomeomorph (G := G) (M := M) p)).2.symm

lemma mem_aux_target (p : M) : ⟦p⟧ ∈ (aux G p).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  refine ⟨p, aux_prop G p, ?_⟩
  rw [aux_eq]

variable (G) in
def localInverseAt (p : M) : OpenPartialHomeomorph (OrbitSpace M G) M := (aux G p).symm

lemma localInverseAt_apply_self {p : M} (hq : ⟦p⟧ ∈ (localInverseAt G p).source) :
    (localInverseAt G p) ⟦p⟧ = p := by
  apply (aux G p).injOn ((localInverseAt G p).map_source hq) (aux_prop G p)
  simp only [localInverseAt, (aux G p).right_inv hq, aux_eq]

variable (G) in -- XXX: is there a nice shorter name?
lemma quotientMk_mem_localInverseAt_source {p : M} : ⟦p⟧ ∈ (localInverseAt G p).source := by
  simp only [localInverseAt, OpenPartialHomeomorph.symm_source]
  exact mem_aux_target p

end prerequisites

-- Let's define a charted space structure on the quotient.

variable [ContinuousConstSMul G M]

noncomputable def myChartAt (q : OrbitSpace M G) : OpenPartialHomeomorph (OrbitSpace M G) H :=
  letI p := q.out
  (localInverseAt G p).trans (chartAt H p)

instance : ChartedSpace H (OrbitSpace M G) where
  atlas := {myChartAt p | p : OrbitSpace M G}
  chartAt := myChartAt
  mem_chart_source q := by
    simp [myChartAt]
    set p := q.out
    rw [← q.out_eq, localInverseAt_apply_self (quotientMk_mem_localInverseAt_source G)]
    exact ⟨quotientMk_mem_localInverseAt_source G, mem_chart_source H p⟩
  chart_mem_atlas := by simp


#check (MulAction G M)
#check symm_trans_mem_contDiffGroupoid

-- U_i is the source of some ϕ_i (same for j) ∈ atlas H M


-- Lemma 3.3. The overlap Uᵢ'' ∩ Uⱼ'' is exactly π(Uᵢ'.g0 = Uⱼ')

-- pi = Quotient.mk _
-- '' is simply π of ' -> (Uᵢ'' = π(Uᵢ')) i think
--

lemma lemma1
    {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    : u' ∈ MulAction.orbit G u := by
  refine MulAction.orbitRel_apply.mp ?_
  refine Quotient.exact ?_
  rw [aux_eq G p, aux_eq G p'] at h
  exact h.symm

def g0 {p p' : M} -- this gives us the g0 that the paper talks about
    {u u' : M}
    (h : (aux G p) u = (aux G p') u') : G :=
  Classical.choose (lemma1 h)

lemma g0_prop {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    : g0 h • u = u' := by exact Classical.choose_spec (lemma1 h)


/-
the homeomorphism x→ x.g0
from X onto itself
carries the open set Ui' = Ui ∩ (Uj.g₀⁻¹) around ui
onto the open set Uj' = Uj ∩ (Ui.g₀) around uj
-/



lemma lemma2 {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)
    : (fun x ↦ g0 h • x) '' (U ∩ ((fun x ↦ (g0 h)⁻¹ • x) '' U'))
      = U' ∩ ((fun x ↦ g0 h • x) '' U) := by

  ext x
  constructor
  <;> intro hx

  · obtain ⟨y, hy1, hy2⟩ := hx
    obtain ⟨hy1, hy1'⟩ := hy1
    obtain ⟨z, hz1, hz2⟩ := hy1'
    constructor
    · simp [← hz2] at hy2
      rw [← hy2]
      exact hz1
    · use y
  · obtain ⟨hx, hx'⟩ := hx
    obtain ⟨y, hy1, hy1'⟩ := hx'
    use y
    simp [hy1, hy1']
    use x
    simp [hx]
    simp [← hy1']

example {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (hU : U = (aux G p).source)
    (U' : Set M)
    (hU' : U' = (aux G p').source)
    : IsOpen ((fun x ↦ g0 h • x) '' (U ∩ ((fun x ↦ (g0 h)⁻¹ • x) '' U'))) := by
  rw [lemma2]
  refine IsOpen.inter ?_ ?_
  · rw [hU']
    exact (aux G p').open_source
  · have h1 : IsOpen U := by rw [hU]; exact (aux G p).open_source
    have h2 := isOpenMap_smul (g0 h) (α:=M)
    exact h2 U h1

-- i had to do this bc otherwise lemma3 wouldnt work??
def π (p : M) : OrbitSpace M G := Quotient.mk _ p

example {a : Type} (A B : Set a) (h : A ∩ B = B) : B ⊆ A := by exact Set.inter_eq_right.mp h

example (x y : M) (h : x ∈ MulAction.orbit G y) :
    π (G := G) x = π (G := G) y := by
  unfold π
  exact MulAction.orbitRel.Quotient.mem_orbit.mp h

variable (G) in
lemma lemma3 {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)

    : ((π (G:=G)) '' (U ∩ ((fun x ↦ (g0 h)⁻¹ • x) '' U')))
      ∩ (π (G:=G)) '' (U' ∩ ((fun x ↦ g0 h • x) '' U)) =
      (π (G:=G)) '' ((fun x ↦ g0 h • x) '' (U ∩ ((fun x ↦ (g0 h)⁻¹ • x) '' U'))) := by

  rw [lemma2]
  rw [Set.inter_eq_right]
  simp
  intro x ⟨hx, hx'⟩
  obtain ⟨y, hy, hy'⟩ := hx'
  simp at hy'

  use y
  constructor
  · constructor
    · exact hy
    · use x
      simp [hx]
      rw [← hy']
      exact inv_smul_smul (g0 h) y
  · unfold π
    apply Eq.symm
    apply MulAction.orbitRel.Quotient.mem_orbit.mp
    use g0 h


-- this is something i found at leansearch but then
-- i couldnt find it here
theorem IsManifold.mem_maximalAtlas_iff
    {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u_3} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
    {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M]
    {e : OpenPartialHomeomorph M H} :
    e ∈ maximalAtlas I n M
      ↔ e ∈ StructureGroupoid.maximalAtlas M (contDiffGroupoid n I) := by sorry

lemma give_this_a_name (x y : OrbitSpace M G) :
    (chartAt H (Quotient.out x)).symm ≫ₕ chartAt H (Quotient.out y) ∈ contDiffGroupoid (↑n) I := by
  refine IsManifold.compatible_of_mem_maximalAtlas ?_ ?_
  · -- φ ∈ IsManifold.maximalAtlas I (↑n) M ?
    apply IsManifold.chart_mem_maximalAtlas
  · -- φ' ∈ IsManifold.maximalAtlas I (↑n) M ?
    apply IsManifold.chart_mem_maximalAtlas

-- And let's prove that it's a manifold.
instance : IsManifold I n (OrbitSpace M G) where
   compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    unfold myChartAt

    set φ' := chartAt H (Quotient.out y)
    set φ := chartAt H (Quotient.out x)
    set π := localInverseAt G (Quotient.out x)
    set π' := localInverseAt G (Quotient.out y)

    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

    rw [OpenPartialHomeomorph.trans_assoc]
    nth_rewrite 2 [← OpenPartialHomeomorph.trans_assoc]

    refine IsManifold.compatible_of_mem_maximalAtlas ?_ ?_
    · apply IsManifold.chart_mem_maximalAtlas
    · --#check IsManifold.mem_maximalAtlas_iff (H := H) (M := M) (e : φ')

      sorry


    --- then apply associativity of >>h -> so we will get three components:
    -- φ⁻¹ ∘ (πₚ⁻¹ ∘ πₚ') ∘ φ' (or something like this)

    -- then prove : 1. φ's are differentiable (already true since M is already smooth manifold)
    -- 2. (πₚ⁻¹ ∘ πₚ') is actually the action of 1 element of the group
    -- so then is is differentiable as well ()







-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
