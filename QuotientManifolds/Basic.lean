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





example (x y : OrbitSpace M G) (p p' : M)
    (hp : p = x.out) (hp' : p' = y.out)
    (u u' : M)
    (h : (aux G p) u = (aux G p') u')
      -- basically h is saying that there is an intersection
    :
    (localInverseAt G (x.out)).symm ≫ₕ (localInverseAt G (y.out))
      = fun m : M ↦ g0 h • m
    := by
  ext a
  simp

  set U := (aux G p).source
  set U' := (aux G p').source
  have h' := lemma3 G h U U'

  -- π ( U ∩ g0⁻¹ (U') ) ∩ π ( U' ∩ g0 (U) ) =
  -- = π ( g0 (U ∩ g0⁻¹ U') )









  sorry



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


example (q : OrbitSpace M G) :
  (localInverseAt G (q.out)).symm = aux G q.out := by
  exact rfl

lemma if_source_of_first_empty_then_composition_empty {α β χ : Type} (f : PartialEquiv α β)
  (g : PartialEquiv β χ) (h : f.source = ∅) : (f.trans g).source = ∅ := by

  refine Set.eq_empty_of_forall_notMem ?_
  intro z
  by_contra c
  obtain ⟨c1, c2⟩ := c
  have aux'' : f.symm.target = f.source := by exact rfl
  rw [aux'', h] at c1
  exact c1



lemma if_no_source_in_target_composition_empty {α β χ : Type} (f : PartialEquiv α β)
  (g : PartialEquiv β χ) (h : g.source ∩ f.target = ∅) : (f.trans g).source = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  intro z
  by_contra c
  obtain ⟨c1, c2⟩ := c
  rw [← Set.not_nonempty_iff_eq_empty, Set.inter_comm] at h
  unfold Set.Nonempty at h
  simp at h
  specialize h (f z) (PartialEquiv.map_source f c1)
  exact h c2


lemma if_no_source_in_target_composition_empty_coerc
    {α : Type u} {β : Type v} {χ : Type w}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace χ]
    (f : OpenPartialHomeomorph α β)
    (g : OpenPartialHomeomorph β χ) (h : g.source ∩ f.target = ∅) : (f.trans g).source = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  intro z
  by_contra c
  obtain ⟨c1, c2⟩ := c
  rw [← Set.not_nonempty_iff_eq_empty, Set.inter_comm] at h
  unfold Set.Nonempty at h
  simp at h
  specialize h (f z) (OpenPartialHomeomorph.map_source f c1)
  exact h c2

lemma if_source_of_first_empty_then_composition_empty_coerc
    {α : Type u} {β : Type v} {χ : Type w}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace χ]
    (f : OpenPartialHomeomorph α β)
    (g : OpenPartialHomeomorph β χ) (h : f.source = ∅) : (f.trans g).source = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  intro z
  by_contra c
  obtain ⟨c1, c2⟩ := c
  have aux'' : f.symm.target = f.source := by exact rfl
  rw [aux'', h] at c1
  exact c1

lemma if_source_of_second_empty_then_composition_empty_coerc
    {α : Type u} {β : Type v} {χ : Type w}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace χ]
    (f : OpenPartialHomeomorph α β)
    (g : OpenPartialHomeomorph β χ) (h : g.source = ∅) : (f.trans g).source = ∅ := by
  apply if_no_source_in_target_composition_empty_coerc
  rw [h]
  simp




#check PartialEquiv.EqOnSource
#check PartialEquiv.trans_source

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

    set ρ : M → M := fun x_1 ↦ g0 heq • x_1
    set ρinv : M → M := fun x_1 ↦ (g0 heq)⁻¹ • x_1
    set Up' := Up ∩ ρinv '' Uq
    set Uq' := Uq ∩ ρ '' Up

    use ((πinvx ≫ₕ φx) '' ((π (G := G) '' Up') ∩ (π (G := G) '' Uq')))

    constructor
    ·
      -- is open s
      sorry

    constructor

    · -- h in s
      sorry

    constructor

    ·
      sorry
    ·
      sorry





/-





    have aux : ∃ g : G, ρ g = (πinvx.symm ≫ₕ πinvy) := by
      sorry

    obtain ⟨g, hρ⟩ := aux





    --rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

    --have def_πinv : (localInverseAt G (x.out)).symm = aux G x.out := by exact rfl

    --rw [def_πinv]
    --set πx := aux G x.out

    by_cases h : (∃ z, z ∈ (πinvx.symm.target ∩ πinvy.source))

    · obtain ⟨u, hu⟩ := h
      obtain ⟨hu1, hu2⟩ := hu
      simp at hu1

      have hu1' := hu1
      apply PartialEquiv.map_target' at hu1'
      have hu2' := hu2
      apply PartialEquiv.map_target' at hu2'
      set πy := aux G (Quotient.out y)

      /-
      Because u is in the source of both πx⁻¹ and πy⁻¹
      we can take
      - u1 = πx⁻¹ (u)
      - u2 = πy⁻¹ (u)
      and this way πx(u1) = πy(u2) = u
      -/

      have huxy : πinvx.symm (πinvx.symm.invFun u) = πy (πy.invFun u) := by
        simp
        rw [OpenPartialHomeomorph.right_inv, OpenPartialHomeomorph.left_inv]
        · exact hu1
        exact hu2

      set Up := πinvx.target ∩ φx.source
      set Uq := πinvy.target ∩ φy.source

      --have lemma1 := lemma1 huxy

      have lemma2 := lemma2 huxy Up Uq
      have lemma3 := lemma3 G huxy Up Uq

      set ρ : M → M := fun x_1 ↦ g0 huxy • x_1
      set ρinv : M → M := fun x_1 ↦ (g0 huxy)⁻¹ • x_1
      set Up' := Up ∩ ρinv '' Uq
      set Uq' := Uq ∩ ρ '' Up

      -- up until here i think im following the paper

      have bigsource : ((πinvx ≫ₕ φx).symm ≫ₕ πinvy ≫ₕ φy).source ⊆
        {u : H | (πinvx ≫ₕ φx).symm u ∈ (πinvx.source ∩ πinvy.source)} := by
        intro t ht
        simp
        obtain ⟨ht1, ht2⟩ := ht
        simp at ht1
        simp at ht2
        have ht1 := ht1.right
        have ht2 := ht2.left
        constructor
        · exact OpenPartialHomeomorph.map_target πinvx ht1
        exact ht2

      have s : ((πinvx ≫ₕ φx).symm ≫ₕ πinvy ≫ₕ φy).source
          ⊆ (πinvx ≫ₕ φx) '' (π '' Up' ∩ π '' Uq') := by
        intro h hh
        simp at hh
        obtain ⟨⟨hh1, hh2⟩, hh3, hh4⟩ := hh
        simp
        use φx.symm h
        constructor
        constructor
        · sorry
        · sorry
        · sorry




      set Vx := πinvx.source
      set Vy := πinvy.source

      set Ux := (πinvx '' Vx)
      set Uy := (πinvy '' Vy)



      have lemma1 := lemma1 huxy


      set G0 := (fun x_1 : M ↦ g0 huxy • x_1)
      set G0inv := (fun x_1 : M ↦ (g0 huxy)⁻¹ • x_1)

      set Ux' := Ux ∩ G0inv '' Uy
      set Uy' := Uy ∩ G0 '' Ux



      set e := (πinvx ≫ₕ φx)

      set v := e u

      have step0 : v ∈ e '' (Vx ∩ Vy) := by
        use u
        exact ⟨⟨hu1, hu2⟩, rfl⟩

      have bigsource' : ((πinvx ≫ₕ φx).symm ≫ₕ πinvy ≫ₕ φy).source ⊆
        e '' (π '' Ux' ∩ π '' Uy') := by
        intro t ht
        apply bigsource at ht
        simp at ht
        use e.symm t
        constructor
        constructor
        · simp
          use πinvx (e.symm t)
          constructor
          · constructor
            · use e.symm t
              exact ⟨ht.left, rfl⟩
            · simp

              sorry
          · sorry
        sorry
        sorry -- should be trivial


      have step2 : v ∈ e '' (π '' (G0 '' Ux)) := by
        --rw [← lemma2]
        sorry

      --set Ux := πx.source
      --set Uy := πy.source

      rw [lemma2] at lemma3


      sorry


    · --- esto me puede servir luego
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

      have def_πinv : (localInverseAt G (x.out)).symm = aux G x.out := by exact rfl

      rw [def_πinv]
      set πx := aux G x.out

      rw [OpenPartialHomeomorph.trans_assoc]
      nth_rewrite 2 [← OpenPartialHomeomorph.trans_assoc]
      apply ContDiffGroupoid.mem_of_source_eq_empty
      apply if_source_of_second_empty_then_composition_empty_coerc φx.symm ((πx ≫ₕ πinvy) ≫ₕ φy)
      apply if_source_of_first_empty_then_composition_empty_coerc (πx ≫ₕ πinvy) φy
      apply if_no_source_in_target_composition_empty_coerc πx πinvy
      rw [Set.inter_comm]
      exact Set.not_nonempty_iff_eq_empty.mp h
-/


-- Once we have done this, let's prove that the projection map is smooth.
lemma contMDiff_quotientMk : ContMDiff I I n (Quotient.mk _ : M → OrbitSpace M G) := by
  sorry
