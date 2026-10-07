import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A plain (non-module) file, so that the private auxiliaries of the development are in the
environment as well as its exported constants. Walks every constant whose name begins with
`SixConcyclic.`, `_private.SixConcyclic.` or `_private.Solution.` (every declaration of this
development and the private auxiliaries Lean generates for them; `Challenge.lean` is not
imported), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make
it pass vacuously) or if any of the fourteen compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "SixConcyclic." || label.startsWith "_private.SixConcyclic." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 450 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 450"
  for n in [`SixConcyclic.six_concyclic_fieldCriterion,
      `SixConcyclic.at_most_six_concyclic_fieldCriterion,
      `SixConcyclic.at_most_six_spherical_spanning_fieldCriterion,
      `SixConcyclic.at_most_five_spherical_fieldCriterion,
      `SixConcyclic.algebraic_spherical_fieldCriterion,
      `SixConcyclic.fieldCriterion_spherical,
      `SixConcyclic.algebraic_fieldCriterion_iff_spherical,
      `SixConcyclic.at_most_six_spherical_ramsey_of_sufficiency,
      `SixConcyclic.at_most_six_circle_points_ramsey_of_sufficiency,
      `SixConcyclic.algebraic_spherical_ramsey_of_sufficiency,
      `SixConcyclic.algebraic_ramsey_iff_spherical_of_classification,
      `SixConcyclic.spherical_fieldCriterion_of_card_le_finrank_add_four,
      `SixConcyclic.at_most_six_spherical_fieldCriterion,
      `SixConcyclic.spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
