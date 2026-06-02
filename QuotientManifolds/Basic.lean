import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Quotient
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Instances.Quotient

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
example : TopologicalSpace (OrbitSpace M G) := by exact instTopologicalSpaceQuotient

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
lemma isCoveringMap_quotientMk : IsCoveringMap (Quotient.mk _ : M → OrbitSpace M G) :=
  IsQuotientCoveringMap.isCoveringMap _ G
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

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

lemma localInverseAt_apply_self {p : M}
    --(hq : ⟦p⟧ ∈ (localInverseAt G p).source)
    --- this is not necessary
  :
    (localInverseAt G p) ⟦p⟧ = p := by
  have hq := quotientMk_mem_localInverseAt_source (G:=G) (p:=p)
  apply (aux G p).injOn ((localInverseAt G p).map_source hq) (aux_prop G p)
  simp only [localInverseAt, (aux G p).right_inv hq, aux_eq]

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
    simp only [myChartAt, OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialEquiv.trans_source, OpenPartialHomeomorph.toFun_eq_coe,
      Set.mem_inter_iff, Set.mem_preimage]
    set p := q.out
    rw [← q.out_eq, localInverseAt_apply_self]
    exact ⟨quotientMk_mem_localInverseAt_source G, mem_chart_source H p⟩
  chart_mem_atlas := by simp


/-
        EVERYTHING AFTER THIS NEEDS TO BE CLEANED UP
-/

-- TO-DO: write this with the proper variables and hypothesis for G and M
omit [ProperlyDiscontinuousSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M] in
lemma Homeomorph.smul_symm {g : G} :
  (Homeomorph.smul g (α := M)).symm = (Homeomorph.smul g⁻¹) := by
  exact Homeomorph.ext_iff.mpr (congrFun rfl)

omit [ProperlyDiscontinuousSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M] in
lemma lemma2' (g : G) (U : Set M)
    (U' : Set M) : Homeomorph.smul (α := M) g '' (U ∩ (Homeomorph.smul g⁻¹ '' U'))
      = U' ∩ (Homeomorph.smul g '' U) := by
  nth_rw 2 [Set.inter_comm]
  rw [← Homeomorph.smul_symm, Homeomorph.image_symm]
  exact Set.image_inter_preimage (⇑(Homeomorph.smul g)) U U'

-- to-do: delete this and just use ⟦ ⟧?
def π : M → OrbitSpace M G := fun p ↦ Quotient.mk _ p

omit [TopologicalSpace M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] in
/--
Applying the projection function to two elements that are
related via the relation yields the same result, namely
`π u = π (g • u)`.
-/
lemma quotient_ignores_smul (g : G) (u : M) :
    π (G := G) u = π (g • u) := by
  exact Quotient.eq.mpr ⟨g⁻¹, (by exact inv_smul_smul g u)⟩

omit [T2Space M] [LocallyCompactSpace M] in
lemma mem_contDiffGroupoid_of_contMDiff_chartAt
    (x y : M) {h : OpenPartialHomeomorph M M}
    (hh : ContMDiff I I n h)
    (hhsymm : ContMDiff I I n h.symm)
    :
    (chartAt H x).symm ≫ₕ h ≫ₕ (chartAt H y) ∈ (contDiffGroupoid (↑n) I) := by
  rw [contMDiff_iff] at hh hhsymm
  obtain hh := hh.2 x y
  obtain hhsymm := hhsymm.2 y x
  set f := (chartAt H x).symm ≫ₕ h ≫ₕ (chartAt H y)
  apply mem_groupoid_of_pregroupoid.mpr
  constructor
  · refine hh.mono ?_
    intro v hv
    simp only [extChartAt, OpenPartialHomeomorph.extend,
      PartialEquiv.trans_target, ModelWithCorners.target_eq,
      ModelWithCorners.toPartialEquiv_coe_symm,
      PartialEquiv.coe_trans_symm, PartialEquiv.trans_source,
      ModelWithCorners.source_eq, Set.preimage_univ,
      Set.inter_univ] -- should this just be simp
    refine ⟨⟨hv.2, hv.1.1⟩, hv.1.2.2⟩
  · refine hhsymm.mono ?_
    intro v hv
    simp only [extChartAt, OpenPartialHomeomorph.extend,
      PartialEquiv.trans_target, ModelWithCorners.target_eq,
      ModelWithCorners.toPartialEquiv_coe_symm,
      PartialEquiv.coe_trans_symm, PartialEquiv.trans_source,
      ModelWithCorners.source_eq, Set.preimage_univ,
      Set.inter_univ]
    refine ⟨⟨hv.2, hv.1.1.1⟩, hv.1.2⟩

lemma π_prop (u : M) (z : OrbitSpace M G) :
    π u = (localInverseAt G (Quotient.out z)).symm u := by
  change π u = (aux G z.out) u
  rw [aux_eq]
  rfl

open Homeomorph -- maybe its not the best but it allows me to write smul

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

    apply StructureGroupoid.locality

    intro h hh
    obtain ⟨hh1, ⟨hh2, hh3⟩, hh4⟩ := hh

    set Up := πinvx.target ∩ φx.source -- U H x
    set Uq := πinvy.target ∩ φy.source -- U H y

    have heq : πinvx.symm (φx.symm h) = πinvy.symm (πinvy (πinvx.symm (φx.symm h))) := by
      rw [OpenPartialHomeomorph.left_inv]
      exact hh3
    have heq : (⟦φx.symm h⟧ : OrbitSpace M G) = ⟦πinvy (πinvx.symm (φx.symm h))⟧ := by
      nth_rw 1 [← aux_eq G x.out, ← aux_eq G y.out]
      exact heq

    obtain ⟨g0, hg0⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq.symm)
    simp only at hg0

    set Up' := Up ∩ smul g0⁻¹ '' Uq

    set t := φx '' (Up')

    have is_open_Up' : IsOpen Up' := by
      refine TopologicalSpace.isOpen_inter _ _ ?_ ?_
      · refine TopologicalSpace.isOpen_inter _ _ (OpenPartialHomeomorph.open_target _)
          (OpenPartialHomeomorph.open_source _)
      · change IsOpen (smul g0⁻¹ '' Uq) -- why is this needed?
        rw [Homeomorph.isOpen_image]
        refine TopologicalSpace.isOpen_inter _ _ (OpenPartialHomeomorph.open_target _)
          (OpenPartialHomeomorph.open_source _)

    have is_open_t : IsOpen t :=
      OpenPartialHomeomorph.isOpen_image_of_subset_source _ is_open_Up'
        (Set.Subset.trans Set.inter_subset_left Set.inter_subset_right)

    have h_in_t : h ∈ t := by
      refine ⟨φx.symm h, ?_, OpenPartialHomeomorph.right_inv φx hh1⟩
      refine ⟨⟨hh2, OpenPartialHomeomorph.map_target φx hh1⟩, ?_⟩
      use πinvy (πinvx.symm (φx.symm h))
      refine ⟨⟨OpenPartialHomeomorph.map_source πinvy hh3, hh4⟩, ((smul g0).injective ?_)⟩
      simp only [Homeomorph.smul_apply, smul_inv_smul, hg0]

    refine ⟨t, is_open_t, h_in_t, ?_⟩

    set f := (φx.symm ≫ₕ (πinvx.symm ≫ₕ πinvy) ≫ₕ φy)

    have f_source_t : (f.restr t).source ⊆ t := by
      rw [OpenPartialHomeomorph.restr_source, IsOpen.interior_eq is_open_t]
      exact Set.inter_subset_right

    have f_eq_φρφ_t : ∀ x ∈ (f.restr t).source, f x = φy (smul g0 (φx.symm x)) := by
      intro z hz
      obtain ⟨u, hu, hz⟩ := f_source_t hz
      simp only [f, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [← hz, φx.left_inv hu.left.right, ← π_prop, quotient_ignores_smul g0 u]
      apply Set.mem_image_of_mem (smul g0) at hu
      rw [lemma2' _ _ _] at hu
      rw [π_prop, ← Homeomorph.smul_apply, πinvy.right_inv hu.left.left]

    have hfg_t :OpenPartialHomeomorph.EqOnSource
        ((φx.symm.trans (((smul g0).toOpenPartialHomeomorph (X := M) (Y := M)).trans φy)).restr
          (t ∩ f.source))
        (f.restr t)
        := by
      refine ⟨?_, ?_⟩
      · ext z
        refine ⟨?_, ?_⟩
        · intro ⟨hz, hzt⟩
          rw [IsOpen.interior_eq (IsOpen.inter is_open_t f.open_source)] at hzt
          rw [OpenPartialHomeomorph.restr_source, IsOpen.interior_eq is_open_t, Set.inter_comm]
          exact hzt
        · intro ⟨hzf, hzt⟩
          rw [IsOpen.interior_eq is_open_t] at hzt
          obtain ⟨u, hu, hz⟩ := hzt
          refine ⟨?_, ?_⟩
          · rw [← hz]
            refine ⟨φx.map_source' hu.1.2, ?_⟩
            obtain ⟨u', hu'⟩ := hu.2
            simp only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_source,
              Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_apply,
              Set.univ_inter, Set.mem_preimage]
            rw [φx.left_inv hu.1.2, ← hu'.2]
            simp only [Homeomorph.smul_apply, smul_inv_smul]
            exact hu'.1.2
          · rw [interior_inter, IsOpen.interior_eq is_open_t, IsOpen.interior_eq f.open_source]
            refine ⟨⟨u, by trivial⟩, hzf⟩
      · intro z ⟨_, hz⟩
        refine Eq.symm (f_eq_φρφ_t z ?_)
        rw [interior_inter,IsOpen.interior_eq f.open_source] at hz
        exact hz.symm

    apply (StructureGroupoid.mem_iff_of_eqOnSource hfg_t).mp

    apply closedUnderRestriction'
    · exact mem_contDiffGroupoid_of_contMDiff_chartAt
        I (h:=(smul g0).toOpenPartialHomeomorph)
        x.out y.out (by sorry) (by sorry)
    · exact TopologicalSpace.isOpen_inter _ _
        is_open_t f.open_source

-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
