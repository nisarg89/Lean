import Lean

register_option metricDistortion.scopedDeclInfo : Bool := {
  defValue := false
  descr := "Opt in to scoped suppression of nested declaration editor information"
}

namespace MetricDistortion.ScopedInfoPrototype
open Lean Elab Command

@[command_elab Lean.Parser.Command.declaration, incremental]
def delegateOrdinaryDeclaration : CommandElab := fun stx => do
  let opts ← getOptions
  unless metricDistortion.scopedDeclInfo.get opts do
    throwUnsupportedSyntax
  if Lean.Elab.async.get opts then
    throwUnsupportedSyntax
  if (← getScope).isMeta then
    throwUnsupportedSyntax
  unless stx.isOfKind ``Lean.Parser.Command.declaration do
    throwUnsupportedSyntax
  let k := stx[1].getKind
  unless k == ``Lean.Parser.Command.definition ||
      k == ``Lean.Parser.Command.theorem ||
      k == ``Lean.Parser.Command.abbrev do
    throwUnsupportedSyntax
  if (stx[0].find? fun
      | .atom _ value => value == "unsafe" || value == "partial" || value == "meta"
      | _ => false).isSome then
    throwUnsupportedSyntax
  withEnableInfoTree false <| Lean.Elab.Command.elabDeclaration stx

end MetricDistortion.ScopedInfoPrototype
