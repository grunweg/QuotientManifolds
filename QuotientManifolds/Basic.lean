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

lemma aux_prop (p : M) : p ∈ (aux G p).source :=
  (Classical.choose_spec (isLocalHomeomorph (G := G) (M := M) p)).1

lemma aux_eq (p : M) : aux G p = (Quotient.mk _ : M → (OrbitSpace M G)) :=
  (Classical.choose_spec (isLocalHomeomorph (G := G) (M := M) p)).2.symm

lemma mem_aux_target (p : M) : ⟦p⟧ ∈ (aux G p).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  use p
  refine ⟨aux_prop p, ?_⟩
  rw [aux_eq]

variable (G) in
def localInverseAt (p : M) : OpenPartialHomeomorph (OrbitSpace M G) M := (aux G p).symm

lemma foo (p : M) : (Quotient.mk _ p) ∈ (localInverseAt G p).source := by
  apply mem_aux_target


end prerequisites



-- Let's define a charted space structure on the quotient.

variable [ContinuousConstSMul G M]

-- lemma bar (p : M) : (aux G p).symm.toPartialEquiv = ((aux G p).toPartialEquiv).symm := by
--   simp_all only [OpenPartialHomeomorph.symm_toPartialEquiv]


noncomputable def myChartAt (q : OrbitSpace M G) : OpenPartialHomeomorph (OrbitSpace M G) H :=
  let p := q.out
  /- choose an element of the equivlence class. For definitions we can do intermediate let
  statements before just stating the definition we want. -/
  (localInverseAt G p).trans (chartAt H p)

-- Need to prove some well-definedness, and use the condition on the group action.

open Function


lemma mem_aux_target' (p : OrbitSpace M G) : p ∈ (aux G (Quotient.out p)).target := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, Set.mem_image]
  use Quotient.out p
  refine ⟨aux_prop (Quotient.out p), ?_⟩
  rw [aux_eq]
  exact Quotient.out_eq p

instance : ChartedSpace H (OrbitSpace M G) where
  atlas := {myChartAt x | x : OrbitSpace M G}
  chartAt := fun x ↦ myChartAt x
  mem_chart_source := by
    intro p
    simp only [myChartAt, OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      OpenPartialHomeomorph.toFun_eq_coe, Set.mem_inter_iff, Set.mem_preimage]
    refine ⟨mem_aux_target' p, ?_⟩
    sorry
  chart_mem_atlas := by
    intro x
    use x




-- And let's prove that it's a manifold.
instance : IsManifold I n (OrbitSpace M G) := sorry

-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
