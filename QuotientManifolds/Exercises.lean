import Mathlib

open Set ENat Manifold Metric Module Bundle Function TopologicalSpace
noncomputable section

-- Here is how to declare a general manifold with boundary and corners. It's a little verbose.
variable {n : ℕ∞} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n M]
  -- Here's a second one.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]

/-
Partial homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.

Define a partial homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def myFirstLocalHomeo : OpenPartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := sorry
  map_source' := by
    sorry
  map_target' := by
    sorry
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry
