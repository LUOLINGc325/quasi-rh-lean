import QRHShort.DependencyGraph
import Lean.Util.CollectAxioms

/-! Strict audit: every theorem in the three project namespaces is checked.
The standard three axioms and the three explicitly cited external inputs are
the only approved axioms. `sorryAx` is reported separately and makes the audit
fail. Thus a successful `lake build` with placeholders cannot masquerade as a
successful proof audit. This file is intentionally separate from the library. -/

open Lean Elab Command

run_cmd do
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let external : Array Name := #[
    `QRHShort.hecke_continuation,
    `QRHShort.landau_prime_ideal_dyadic_lower_bound,
    `QRHShort.goldmakher_louvel_quadratic_sieve]
  let approved := standard ++ external
  let env ← getEnv
  let mut checked := 0
  let mut incomplete : Array Name := #[]
  let mut forbidden : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    if (`QRHShort).isPrefixOf name || (`QRHLean3).isPrefixOf name || (`QRH).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        checked := checked + 1
        let axioms ← collectAxioms name
        if axioms.contains `sorryAx then
          incomplete := incomplete.push name
        for ax in axioms do
          if ax != `sorryAx && !approved.contains ax then
            forbidden := forbidden.push (name, ax)
      | .axiomInfo _ =>
        if !external.contains name then forbidden := forbidden.push (name, name)
      | _ => pure ()
  let mut finishedLabels := 0
  for entry in QRHShort.manuscriptEntries do
    let axioms ← collectAxioms entry.declaration
    let pending := axioms.contains `sorryAx
    if !pending then finishedLabels := finishedLabels + 1
    logInfo m!"SOURCE {entry.label} line={entry.line} declaration={entry.declaration} sorry={pending} axioms={axioms}"
  logInfo m!"AUDIT checked_theorems={checked} approved_external={external.size} labelled_complete={finishedLabels}/{QRHShort.manuscriptEntries.size} sorry_dependent={incomplete.size} forbidden={forbidden.size}"
  for (decl, ax) in forbidden do
    logError m!"Unapproved axiom {ax} in {decl}"
  if !incomplete.isEmpty then
    logError m!"Incomplete formalization: these declarations still depend on sorryAx: {incomplete}"
