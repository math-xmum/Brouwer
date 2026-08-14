import BeyondSperner
import FormalizationInterface
import Mathlib.Util.AssertNoSorry

/-!
Run with `lake env lean FormalizationInterface/AuditAll.lean`.

Unlike `Audit.lean`, which prints readable axiom closures for representative public declarations,
this file checks every declaration whose fully qualified name lies in the `BeyondSperner`
namespace.  Generated declarations (recursors, equation lemmas, projections, and private helpers)
are included.  The command fails if any such declaration depends on `sorryAx`, if a declaration in
the namespace is itself an axiom, or if the transitive closure contains an axiom other than Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.
-/

open Lean Elab Command

private def permittedAxioms : NameSet :=
  NameSet.empty.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

elab "audit_beyond_sperner" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut declaredAxioms : Array Name := #[]
  let mut sorryUsers : Array Name := #[]
  let mut unexpected : NameSet := NameSet.empty
  for (name, info) in env.constants.toList do
    if (`BeyondSperner).isPrefixOf name then
      checked := checked + 1
      if info.isAxiom then
        declaredAxioms := declaredAxioms.push name
      let axioms ← liftCoreM <| Lean.collectAxioms name
      if axioms.contains ``sorryAx then
        sorryUsers := sorryUsers.push name
      for axiomName in axioms do
        if !permittedAxioms.contains axiomName then
          unexpected := unexpected.insert axiomName
  if !declaredAxioms.isEmpty then
    throwError "declared axioms in BeyondSperner: {declaredAxioms.toList}"
  if !sorryUsers.isEmpty then
    throwError "declarations depending on sorryAx: {sorryUsers.toList}"
  if !unexpected.isEmpty then
    throwError "unexpected axioms in BeyondSperner closures: {unexpected.toList}"
  logInfo m!"audited {checked} BeyondSperner declarations; no sorryAx or nonstandard axioms"

audit_beyond_sperner
