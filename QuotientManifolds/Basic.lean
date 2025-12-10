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
  use p
  refine ⟨aux_prop G p, ?_⟩
  sorry

variable (G) in
def localInverseAt (p : M) : OpenPartialHomeomorph (OrbitSpace M G) M := (aux G p).symm

lemma foo (p : M) : (Quotient.mk _ p) ∈ (localInverseAt G p).source := by
  sorry

end prerequisites

-- Let's define a charted space structure on the quotient.

variable [ContinuousConstSMul G M]

noncomputable def myChartAt (q : OrbitSpace M G) : OpenPartialHomeomorph (OrbitSpace M G) H :=
  let p := q.out
  (localInverseAt G p).trans (chartAt H p)

#check atlas H M
variable (p : M)
#check mem_chart_source H p

-- Need to prove some well-definedness, and use the condition on the group action.

lemma my_lema : ∀ q : OrbitSpace M G,
  (Quotient.mk _) (Quotient.out q) = q := fun q ↦ Quotient.out_eq q

open Function

lemma req : ∀ q : OrbitSpace M G, (localInverseAt G (Quotient.out q)) q = Quotient.out q := by

  intro q
  by_contra c

  have pi_p := (localInverseAt G (Quotient.out q)).invFun
  have aux : Injective pi_p := by sorry
  have h' : ¬ pi_p ((localInverseAt G (Quotient.out q)) q) = pi_p (Quotient.out q)
    := by exact fun a ↦ c (aux a)

  have aux2 : pi_p ((localInverseAt G (Quotient.out q)) q) = q := by sorry

  have aux3 : pi_p (Quotient.out q) = Quotient.mk _ (Quotient.out q) := by sorry

  rw [aux2] at h'
  have h'' := my_lema q

  rw [← aux3] at h''
  rw [h''] at h'
  simp at h'



instance : ChartedSpace H (OrbitSpace M G) where
  atlas := {myChartAt p | p : OrbitSpace M G}
  chartAt := myChartAt
  mem_chart_source := by
    intro q -- q = [p]
    unfold myChartAt
    simp
    constructor
    · -- q ∈ U

      sorry
    · -- π-1(q) ∈ s_g
      have h1 := mem_chart_source H ((localInverseAt G (Quotient.out q)) q)
      rw [req q] at h1 ⊢
      exact h1
  chart_mem_atlas := by
    intro p
    use p

-- And let's prove that it's a manifold.
instance : IsManifold I n (OrbitSpace M G) := sorry

-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
