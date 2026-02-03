import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Quotient
import Mathlib.Tactic

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

-- Assume G acts freely on M, and that M is Hausdorff and locally compact.
-- (This follows from finite-dimensionality, hence is a harmless assumption to add.)
variable [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

-- This follows from mathlib's definition of a properly discontinuous action.
-- No need to work on this; it's proven in mathlib PR #7596.
lemma isCoveringMap_quotientMk : IsCoveringMap (Quotient.mk _ : M → OrbitSpace M G) := by
  apply IsQuotientCoveringMap.isCoveringMap (G := G)
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

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

/- confused? why do we need the hypothesis hq?
lemma localInverseAt_apply_self {p : M} :
    (localInverseAt G p) ⟦p⟧ = p := by
  have hq : ⟦p⟧ ∈ (localInverseAt G p).source := by exact quotientMk_mem_localInverseAt_source G
  apply (aux G p).injOn ((localInverseAt G p).map_source hq) (aux_prop G p)
  simp only [localInverseAt, (aux G p).right_inv hq, aux_eq]
-/

--Given two points p and k in M s.t. k is in the domain of π_p and [k] is in the domain
-- of (π_p)⁻¹, then (π_p)⁻¹([k]) = k.
lemma localInverseAt_apply_other {p k : M} (hk : k ∈ (aux G p).source)
    (hk' : ⟦k⟧ ∈ (localInverseAt G p).source) :
    (localInverseAt G p) ⟦k⟧ = k := by
  apply (aux G p).injOn
  · simp only [localInverseAt] at hk' ⊢
    exact OpenPartialHomeomorph.map_target (aux G p) hk'
  · exact hk
  · simp only [localInverseAt, (aux G p).right_inv hk', aux_eq]


variable (G) in -- XXX: is there a nice shorter name?
lemma quotientMk_mem_localInverseAt_source {p : M} : ⟦p⟧ ∈ (localInverseAt G p).source := by
  simp only [localInverseAt, OpenPartialHomeomorph.symm_source]
  exact mem_aux_target p

-- For every point `k ∈ M` s.t. k is in the domain of π_p and π_p'(k) is in the
-- domain of(π_p)⁻¹ we have that ((π_p')⁻¹ ∘ π_p) (k) = k, for every p and p'
-- where this makes sense.
lemma aux_trans_localInverseAt_eq {p p' k : M}
    (h : k ∈ (aux G p).source)
    (h' : (aux G p') k ∈ (localInverseAt G p).source) :
    ((aux G p').trans (localInverseAt G p)) k = k := by
  simp only [OpenPartialHomeomorph.coe_trans, aux_eq G p', Function.comp_apply]
  apply localInverseAt_apply_other h
  rwa [aux_eq G p'] at h'

end prerequisites

-- Let's define a charted space structure on the quotient.

variable [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

noncomputable def myChartAt (q : OrbitSpace M G) : OpenPartialHomeomorph (OrbitSpace M G) H :=
  letI p := q.out
  (localInverseAt G p).trans (chartAt H p)

instance : ChartedSpace H (OrbitSpace M G) where
  atlas := {myChartAt p | p : OrbitSpace M G}
  chartAt := myChartAt
  mem_chart_source q := by
    simp only [myChartAt, OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      OpenPartialHomeomorph.toFun_eq_coe, Set.mem_inter_iff, Set.mem_preimage]
    set p := q.out
    rw [← q.out_eq, localInverseAt_apply_self]
    exact ⟨quotientMk_mem_localInverseAt_source G, mem_chart_source H p⟩
  chart_mem_atlas := by simp


/-
        EVERYTHING AFTER THIS NEEDS TO BE CLEANED UP
-/


/--
If two elements are such that `p u = π_p' u'`,
then they are related by `u' = g • u` for some `g ∈ G`.
-/
lemma lemma1
    {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    : u' ∈ MulAction.orbit G u := by
  refine MulAction.orbitRel_apply.mp ?_
  refine Quotient.exact ?_
  rw [aux_eq G p, aux_eq G p'] at h
  exact h.symm


/--
If two elements are such that `p u = π_p' u'`,
then they are related by `u' = g • u` for some `g ∈ G`.
`g0` is such `g`.
-/
def g0 {p p' : M} -- this gives us the g0 that the paper talks about
    {u u' : M}
    (h : (aux G p) u = (aux G p') u') : G :=
  Classical.choose (lemma1 h)

/--
If two elements are such that `p u = π_p' u'`,
then they are related by `u' = g • u` for some `g ∈ G`.
If `g0` is chosen to be such `g`, then `u' = g0 • u`.
-/
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

-- more general version
-- TO-DO: write this with the proper variables and hypothesis for G and M

omit [ProperlyDiscontinuousSMul G M] in
lemma Homeomorph.smul_symm {g : G} :
  (Homeomorph.smul g (α := M)).symm = (Homeomorph.smul g⁻¹) := by
  exact Homeomorph.ext_iff.mpr (congrFun rfl)

omit [ProperlyDiscontinuousSMul G M] in
lemma Homeomorph.smul_image_inter_preimage
    (g : G)
    (U : Set M)
    (U' : Set M)
    : Homeomorph.smul g '' (U ∩ (Homeomorph.smul g⁻¹ '' U'))
      = (Homeomorph.smul g '' U) ∩ U' := by
  rw [← Homeomorph.smul_symm, Homeomorph.image_symm]
  exact Set.image_inter_preimage (⇑(Homeomorph.smul g)) U U'

/--
For any two sets `U` and `V`,
-/
lemma lemma2 {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)
    : Homeomorph.smul (g0 h) '' (U ∩ (Homeomorph.smul (g0 h)⁻¹ '' U'))
      = U' ∩ (Homeomorph.smul (g0 h) '' U) := by
  nth_rw 2 [Set.inter_comm]
  exact Homeomorph.smul_image_inter_preimage (g0 h) U U'

lemma lemma2' {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)
    : Homeomorph.smul (g0 h)⁻¹ '' (U' ∩ (Homeomorph.smul (g0 h) '' U))
      =  (U ∩ (Homeomorph.smul (g0 h)⁻¹ '' U')) := by
  rw [← lemma2 h U U', ← Homeomorph.smul_symm, Homeomorph.image_symm, Homeomorph.preimage_image]

-- i had to do this bc otherwise lemma3 wouldnt work??
def π (p : M) : OrbitSpace M G := Quotient.mk _ p

omit [TopologicalSpace M] [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] in
/--
Applying the projection function to two elements that are
related via the relation yields the same result, namely
`π u = π (g • u)`.
-/
lemma quotient_ignores_smul (g : G) (u : M) : π (G := G) u = π (g • u) := by
  exact Quotient.eq.mpr ⟨g⁻¹, (by exact inv_smul_smul g u)⟩


omit [ProperlyDiscontinuousSMul G M] in
/--
Applying the projection function to two sets that are
related via the relation yields the same result, namely
`π s = π (g • U)`.
-/
lemma quotient_ignores_smul_image (g : G) (U : Set M) : π (G := G) '' U = π '' (Homeomorph.smul g '' U) := by
  ext u
  constructor
  · intro ⟨v, hv⟩
    simp only [Homeomorph.smul_apply, Set.mem_image, exists_exists_and_eq_and]
    use v
    refine ⟨hv.left, ?_⟩
    rw [← hv.right]
    exact Eq.symm (quotient_ignores_smul g v)
  · intro ⟨v, hv⟩
    obtain ⟨u', hu'⟩ := hv.left
    use u'
    refine ⟨hu'.left, ?_⟩
    rw [← hv.right, ← hu'.right, Homeomorph.smul_apply]
    exact quotient_ignores_smul g u'


omit [ProperlyDiscontinuousSMul G M] in
/--
For any group element `g : G` and any sets `U, U' ⊆ M`
it holds that
`π (U ∩ g⁻¹ • U') ∩ π (U' ∩ g • U) = π (g • (U ∩ g⁻¹ • U'))`.
-/
lemma quotient_image_smul_eq
    (g : G)
    (U : Set M)
    (U' : Set M) :
    ((π (G:=G)) '' (U ∩ (Homeomorph.smul g⁻¹ '' U')))
      ∩ (π (G:=G)) '' (U' ∩ (Homeomorph.smul g '' U)) =
      (π (G:=G)) '' (Homeomorph.smul g '' (U ∩ (Homeomorph.smul g⁻¹ '' U'))) := by
  rw [Homeomorph.smul_image_inter_preimage]
  nth_rw 4 [Set.inter_comm]
  rw [Set.inter_eq_right]

  intro x ⟨z, ⟨⟨hz, ⟨y, hy⟩⟩, hx⟩⟩
  use y
  refine ⟨⟨hy.left, ?_⟩, ?_⟩
  · use z
    refine ⟨hz, ?_⟩
    rw [← hy.right]
    simp only [Homeomorph.smul_apply, inv_smul_smul]
  · rw [← hx, ← hy.right, Homeomorph.smul_apply]
    exact quotient_ignores_smul g y

variable (G) in
lemma lemma3 {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)

    : ((π (G:=G)) '' (U ∩ (Homeomorph.smul (g0 h)⁻¹ '' U')))
      ∩ (π (G:=G)) '' (U' ∩ (Homeomorph.smul (g0 h) '' U)) =
      (π (G:=G)) '' (Homeomorph.smul (g0 h) '' (U ∩ (Homeomorph.smul (g0 h)⁻¹ '' U'))) := by

  exact quotient_image_smul_eq (g0 h) U U'

variable (G) in
lemma lemma3' {p p' : M}
    {u u' : M}
    (h : (aux G p) u = (aux G p') u')
    (U : Set M)
    (U' : Set M)

    : ((π (G:=G)) '' (U ∩ (Homeomorph.smul (g0 h)⁻¹ '' U')))
      ∩ (π (G:=G)) '' (U' ∩ (Homeomorph.smul (g0 h) '' U)) =
      (π (G:=G)) '' (Homeomorph.smul (g0 h)⁻¹ '' (U' ∩ (Homeomorph.smul (g0 h) '' U))) := by
  rw [lemma3, lemma2]
  set A := U ∩ ⇑(Homeomorph.smul (g0 h)⁻¹) '' U'
  set B := U' ∩ ⇑(Homeomorph.smul (g0 h)) '' U
  exact quotient_ignores_smul_image (g0 h)⁻¹ B


example (x y : OrbitSpace M G) :
    (chartAt H (Quotient.out x)).symm ≫ₕ chartAt H (Quotient.out y) ∈ contDiffGroupoid (↑n) I := by
  refine IsManifold.compatible_of_mem_maximalAtlas ?_ ?_
  · -- φ ∈ IsManifold.maximalAtlas I (↑n) M ?
    apply IsManifold.chart_mem_maximalAtlas
  · -- φ' ∈ IsManifold.maximalAtlas I (↑n) M ?
    apply IsManifold.chart_mem_maximalAtlas


/-- Note: we have this instance
      instance :
        Membership (OpenPartialHomeomorph H H) (StructureGroupoid H)
        := ⟨fun (G : StructureGroupoid H) (e : OpenPartialHomeomorph H H) ↦ e ∈ G.members⟩

      which means that an open partial homeomorphism can be a member of structured groupoid
      if it is on its members
-/

example (p q : M) : (chartAt H p).symm ≫ₕ (chartAt H q) ∈ contDiffGroupoid (↑n) I := by
  change (chartAt H p).symm ≫ₕ chartAt H q ∈ (contDiffGroupoid (↑n) I).members

  have hp : chartAt H p ∈ atlas H M := by exact ChartedSpace.chart_mem_atlas p
  have hq : chartAt H q ∈ atlas H M := by exact ChartedSpace.chart_mem_atlas q

  have manifold : IsManifold I (↑n) M := by (expose_names; exact inst_6)
  exact manifold.compatible hp hq



lemma Set.inter_subset_if_left_subset {u} (A B C : Set u) (h : A ⊆ C) : A ∩ B ⊆ C := by
  exact fun ⦃a⦄ a_1 ↦ h (Set.inter_subset_left a_1)


lemma confused_on_how_to_use_this (α : Type u)
    [TopologicalSpace α]
    (f g : OpenPartialHomeomorph H H)
    (hfg : f.EqOnSource g)
    (hf : (contDiffPregroupoid n I).property f f.source)
    :
    (contDiffPregroupoid n I).property g g.source
    := by
  exact mem_pregroupoid_of_eqOnSource (contDiffPregroupoid (↑n) I) hfg hf

lemma confused_on_how_to_use_this' (α : Type u)
    [TopologicalSpace α]
    (f g : OpenPartialHomeomorph H H)
    (hfg : f.EqOnSource g)
    (hf : f ∈ (contDiffPregroupoid (↑n) I).groupoid)
    :
    g ∈ (contDiffPregroupoid (↑n) I).groupoid
    := by
  exact (StructureGroupoid.mem_iff_of_eqOnSource hfg).mp hf



-- And let's prove that it's a manifold.
instance : IsManifold I n (OrbitSpace M G) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩


    unfold myChartAt

    --- renaming

    set φy := chartAt H (Quotient.out y)
    set φx := chartAt H (Quotient.out x)
    set πinvx := localInverseAt G (Quotient.out x)
    set πinvy := localInverseAt G (Quotient.out y)

    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    nth_rw 1 [OpenPartialHomeomorph.trans_assoc]
    nth_rw 2 [← OpenPartialHomeomorph.trans_assoc]

    unfold contDiffGroupoid

    apply StructureGroupoid.locality

    intro h hh
    simp at hh
    obtain ⟨hh1, ⟨hh2, hh3⟩, hh4⟩ := hh

    set Up := πinvx.target ∩ φx.source
    set Uq := πinvy.target ∩ φy.source

    have hUp : φx.symm h ∈ Up := by
      refine ⟨hh2, ?_⟩
      exact OpenPartialHomeomorph.map_target φx hh1

    have hUq : πinvy (πinvx.symm (φx.symm h)) ∈ Uq := by
      refine ⟨?_, hh4⟩
      exact OpenPartialHomeomorph.map_source πinvy hh3

    have heq : πinvx.symm (φx.symm h) = πinvy.symm (πinvy (πinvx.symm (φx.symm h))) := by
      rw [OpenPartialHomeomorph.left_inv]
      exact hh3

    have lemma2 := lemma2 heq Up Uq
    have lemma3 := lemma3 G heq Up Uq
    have g0_prop := g0_prop heq

    set ρ : Homeomorph M M := Homeomorph.smul (g0 heq)
    have ρ_prop : ∀ m : M, ρ m = (g0 heq) • m := by exact fun m ↦ rfl
    set ρinv : Homeomorph M M := Homeomorph.smul (g0 heq)⁻¹
    have ρinv_prop : ∀ m : M, ρinv m = (g0 heq)⁻¹ • m := by exact fun m ↦ rfl
    set Up' := Up ∩ ρinv '' Uq
    set Uq' := Uq ∩ ρ '' Up

    have lemma2 : ρ '' Up' = Uq' := by
      exact lemma2

    have lemma2' : ρinv '' Uq' = Up' := by
      exact lemma2' heq Up Uq

    have lemma3 : π (G := G) '' (Up') ∩ π '' (Uq') = π '' (ρ '' Up') :=
      by exact lemma3

    have lemma3' : π (G := G) '' (Up') ∩ π '' (Uq') = π '' (ρinv '' Uq') :=
      by exact lemma3' (G:=G) heq Up Uq

    use ((πinvx ≫ₕ φx) '' ((π (G := G) '' Up') ∩ (π (G := G) '' Uq')))

    have hπx_source : ∀ {u}, u ∈ πinvx.symm.source → π u = πinvx.symm u := by
      intro u hu
      unfold π
      have : πinvx.symm = (aux G x.out) := by rfl
      rw [this] at ⊢ hu
      rw [aux_eq]

    have hπy_source : ∀ {u}, u ∈ πinvy.symm.source → π u = πinvy.symm u := by
      intro u hu
      unfold π
      have : πinvy.symm = (aux G y.out) := by rfl
      rw [this] at ⊢ hu
      rw [aux_eq]

    have hπx : π '' Up' = πinvx.symm '' Up' := by
      apply Set.image_congr
      intro a ha
      apply hπx_source
      exact ha.left.left
    have hπy : π '' Uq' = πinvy.symm '' Uq' := by
      apply Set.image_congr
      intro a ha
      apply hπy_source
      exact ha.left.left

    have is_open_s : IsOpen ((πinvx ≫ₕ φx) '' (π '' Up' ∩ π '' Uq')) := by
      apply OpenPartialHomeomorph.isOpen_image_of_subset_source
      · apply TopologicalSpace.isOpen_inter
        · rw [hπx]
          change IsOpen (πinvx.symm '' Up')
          apply OpenPartialHomeomorph.isOpen_image_of_subset_source
          · apply TopologicalSpace.isOpen_inter
            · apply TopologicalSpace.isOpen_inter
              · apply OpenPartialHomeomorph.open_target
              · apply OpenPartialHomeomorph.open_source
            · change IsOpen (⇑ρinv '' Uq)
              rw [Homeomorph.isOpen_image]
              apply TopologicalSpace.isOpen_inter
              · apply OpenPartialHomeomorph.open_target
              · apply OpenPartialHomeomorph.open_source
          · simp
            apply Set.inter_subset_if_left_subset
            exact Set.inter_subset_left
        · rw [hπy]
          change IsOpen (πinvy.symm '' Uq')
          apply OpenPartialHomeomorph.isOpen_image_of_subset_source
          · apply TopologicalSpace.isOpen_inter
            · apply TopologicalSpace.isOpen_inter
              · apply OpenPartialHomeomorph.open_target
              · apply OpenPartialHomeomorph.open_source
            · change IsOpen (⇑ρ '' Up)
              rw [Homeomorph.isOpen_image]
              apply TopologicalSpace.isOpen_inter
              · apply OpenPartialHomeomorph.open_target
              · apply OpenPartialHomeomorph.open_source
          · simp
            apply Set.inter_subset_if_left_subset
            exact Set.inter_subset_left

      · simp
        constructor
        · apply Set.inter_subset_if_left_subset
          rw [hπx]
          intro u hu
          simp at hu
          obtain ⟨v, ⟨hv1, hv2⟩⟩ := hu
          have : Up' ⊆ πinvx.symm.source := by
            simp
            apply Set.inter_subset_if_left_subset
            exact Set.inter_subset_left
          apply this at hv1
          rw [← hv2]
          exact OpenPartialHomeomorph.map_target πinvx hv1
        · apply Set.inter_subset_if_left_subset
          rw [hπx]
          simp
          intro u hu
          simp
          rw [OpenPartialHomeomorph.right_inv πinvx hu.left.left]
          exact hu.left.right


    constructor
    · -- is open s
      exact is_open_s

    constructor

    · -- h in s
      simp
      use φx.symm h
      constructor
      · constructor
        · constructor
          · exact ⟨hh2, OpenPartialHomeomorph.map_target φx hh1⟩
          · use πinvy (πinvx.symm (φx.symm h))
            constructor
            · exact ⟨OpenPartialHomeomorph.map_source πinvy hh3, hh4⟩
            · apply ρ.injective
              rw [ρ_prop, ρ_prop]
              rw [g0_prop]
              rw [ρinv_prop]
              simp
        · use πinvy (πinvx.symm (φx.symm h))
          constructor
          · constructor
            · exact ⟨OpenPartialHomeomorph.map_source πinvy hh3, hh4⟩
            · use φx.symm h
              constructor
              · exact ⟨hh2, OpenPartialHomeomorph.map_target φx hh1⟩
              · apply ρinv.injective
                rw [ρ_prop]
                rw [g0_prop]
          · rw [hπy_source (Set.mem_of_mem_inter_left hUq)]
            rw [OpenPartialHomeomorph.left_inv πinvy hh3]
            rw [hπx_source]
            exact hh2
      · rw [hπx_source hh2]
        rw [OpenPartialHomeomorph.right_inv πinvx hh2]
        rw [OpenPartialHomeomorph.right_inv φx hh1]

    set f :=  (φx.symm ≫ₕ (πinvx.symm ≫ₕ πinvy) ≫ₕ φy)
    set s := ((πinvx ≫ₕ φx) '' (π '' Up' ∩ π '' Uq'))

    have s_def : s = ((πinvx ≫ₕ φx) '' (π '' Up' ∩ π '' Uq')) := by rfl
    have f_def : f = (φx.symm ≫ₕ (πinvx.symm ≫ₕ πinvy) ≫ₕ φy) := by rfl

    have f_source : (f.restr s).source ⊆ s := by
      rw [OpenPartialHomeomorph.restr_source]
      rw [IsOpen.interior_eq is_open_s]
      exact Set.inter_subset_right

    have f_eq_φρφ :
      ∀ x ∈ (f.restr s).source, f x = φy (ρ (φx.symm x)) := by
      intro z hz
      apply f_source at hz
      rw [s_def] at hz

      rw [lemma3] at hz
      simp at hz
      obtain ⟨u, ⟨hu, hz⟩⟩ := hz
      rw [← hz]
      rw [f_def]
      simp

      rw [hz]

      have hρu :  π (G := G) u = π (ρ u) := by
          exact quotient_ignores_smul (g0 heq) u
      rw [← hρu] at hz
      rw [hπx_source hu.left.left] at hz
      rw [πinvx.right_inv hu.left.left] at hz

      have hz' : φx.symm z = u := by
        rw [← hz, φx.left_inv hu.left.right]

      rw [hz']
      rw [← hπx_source hu.left.left]
      rw [hρu]

      apply Set.mem_image_of_mem (⇑ρ) at hu
      rw [lemma2] at hu
      rw [hπy_source hu.left.left]
      rw [πinvy.right_inv hu.left.left]

    have φρφ_source :
      ((φx.symm.trans ((ρ.toOpenPartialHomeomorph (X := M) (Y := M)).trans φy)).restr s).source
        ⊆ s := by
      rw [OpenPartialHomeomorph.restr_source]
      rw [IsOpen.interior_eq is_open_s]
      exact Set.inter_subset_right

    have φρφ_eq_f :
      ∀ x ∈
        ((φx.symm.trans ((ρ.toOpenPartialHomeomorph (X := M) (Y := M)).trans φy)).restr s).source,
        f x = φy (ρ (φx.symm x)) := by
      intro z hz
      apply φρφ_source at hz
      rw [s_def] at hz

      rw [lemma3] at hz
      simp at hz
      obtain ⟨u, ⟨hu, hz⟩⟩ := hz
      rw [← hz]
      rw [f_def]
      simp

      rw [hz]

      have hρu :  π (G := G) u = π (ρ u) := by
          exact quotient_ignores_smul (g0 heq) u
      rw [← hρu] at hz
      rw [hπx_source hu.left.left] at hz
      rw [πinvx.right_inv hu.left.left] at hz

      have hz' : φx.symm z = u := by
        rw [← hz, φx.left_inv hu.left.right]

      rw [hz']
      rw [← hπx_source hu.left.left]
      rw [hρu]

      apply Set.mem_image_of_mem (⇑ρ) at hu
      rw [lemma2] at hu
      rw [hπy_source hu.left.left]
      rw [πinvy.right_inv hu.left.left]


    have ρ_source := Homeomorph.toOpenPartialHomeomorph_source ρ

    have hfg : OpenPartialHomeomorph.EqOnSource
        ((φx.symm.trans ((ρ.toOpenPartialHomeomorph (X := M) (Y := M)).trans φy)).restr
          (s ∩ f.source))
        (f.restr s)
        := by
      constructor
      · ext z
        have auxiliar : IsOpen (s ∩ f.source) := by
          refine IsOpen.inter is_open_s f.open_source
        have s_prop : s = φx '' (Up') := by
          rw [s_def]
          have : (πinvx ≫ₕ φx) '' (π '' Up' ∩ π '' Uq') =
          φx '' (πinvx '' (π '' Up' ∩ π '' Uq')) := by
            simp [Set.image_image]
          rw [this]
          rw [lemma3']
          rw [lemma2']
          have : π '' (Up') = πinvx.symm '' (Up') := by
            ext m
            constructor
            all_goals intro hm
            all_goals obtain ⟨n, hn⟩ := hm
            · use n
              rw [hπx_source] at hn
              · exact hn
              exact hn.left.left.left
            · use n
              rw [hπx_source]
              · exact hn
              exact hn.left.left.left
          rw [this]
          have : πinvx '' (πinvx.symm '' Up') = Up' := by
            ext m
            constructor
            all_goals intro hm
            · obtain ⟨n, hn⟩ := hm
              obtain ⟨l, ⟨hl1, hl2⟩⟩ := hn.left
              rw [← hl2] at hn
              rw [πinvx.right_inv hl1.left.left] at hn
              rw [← hn.right]
              exact hl1
            · use πinvx.symm m
              simp [πinvx.right_inv hm.left.left]
              use m
          rw [this]

        constructor
        all_goals intro hz
        · obtain ⟨hz, hzs⟩ := hz
          rw [IsOpen.interior_eq auxiliar] at hzs
          simp [IsOpen.interior_eq is_open_s, hzs.left, hzs.right]

        · obtain ⟨hz, hzs⟩ := hz
          simp [hzs]
          rw [IsOpen.interior_eq f.open_source]
          simp [hz]
          constructor
          · obtain ⟨hz1, hz2⟩ := hz
            exact hz1
          · rw [IsOpen.interior_eq is_open_s] at hzs
            rw [s_prop] at hzs
            obtain ⟨r, hr⟩ := hzs
            rw [← hr.right]
            rw [φx.left_inv hr.left.left.right]
            have : ρ r ∈ ρ '' (Up') := by
              use r
              exact ⟨hr.left, by rfl⟩
            rw [lemma2] at this
            exact this.left.right

      · intro z hz
        have hz := hz.right
        have aux : IsOpen (s ∩ f.source) := by
          refine IsOpen.inter is_open_s f.open_source
        rw [IsOpen.interior_eq aux] at hz
        have : z ∈ (f.restr s).source := by
          constructor
          · exact hz.right
          · rw [IsOpen.interior_eq is_open_s]
            exact hz.left
        exact Eq.symm (f_eq_φρφ z this)

    apply confused_on_how_to_use_this' (α := H)
      (f := ((φx.symm.trans ((ρ.toOpenPartialHomeomorph (X := M) (Y := M)).trans φy)).restr
        (s ∩ f.source)))
      (g := (f.restr s))
      (hfg := hfg)





    have aux1 : (φx.symm ≫ₕ φy).restr s ∈ (contDiffPregroupoid (↑n) I).groupoid := by sorry

    let help := IsManifold.toHasGroupoid (M:=M) (n:=n) (I:=I)

    --have aux2 : ρ.toOpenPartialHomeomorph ∈ contDiffGroupoid (↑n) I := by sorry


    constructor
    ·
      simp [contDiffPregroupoid]
      expose_names
      #check ContDiffOn.comp

      have φx_atlas : φx ∈ atlas H M := by
        exact ChartedSpace.chart_mem_atlas (Quotient.out x)

      have φy_atlas : φy ∈ atlas H M := by
        exact ChartedSpace.chart_mem_atlas (Quotient.out y)

      #check inst_6.compatible φx_atlas φy_atlas

      sorry
    ·
      sorry








      sorry
    ·
      sorry


-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
