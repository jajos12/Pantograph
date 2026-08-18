/- Adapted from https://github.com/semorrison/lean-training-data -/
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Elab.InfoTree
import Init.Ext

import Pantograph.Frontend.Basic
import Pantograph.Frontend.MetaTranslate
import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Serial

open Lean

namespace Lean.Elab.Info
/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
protected def stx? : Info → Option Syntax
  | .ofTacticInfo         info => info.stx
  | .ofTermInfo           info => info.stx
  | .ofCommandInfo        info => info.stx
  | .ofMacroExpansionInfo info => info.stx
  | .ofOptionInfo         info => info.stx
  | .ofFieldInfo          info => info.stx
  | .ofCompletionInfo     info => info.stx
  | .ofUserWidgetInfo     info => info.stx
  | .ofCustomInfo         info => info.stx
  | .ofFVarAliasInfo      _    => none
  | .ofFieldRedeclInfo    info => info.stx
  | .ofOmissionInfo       info => info.stx
/-- Is the `Syntax` for this `Lean.Elab.Info` original, or synthetic? -/
protected def isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false
end Lean.Elab.Info

namespace Lean.Elab.TacticInfo

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none
/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

end Lean.Elab.TacticInfo

namespace Lean.Elab.InfoTree

/--
Keep `.node` nodes and `.hole` nodes satisfying predicates.

Returns a `List InfoTree`, although in most situations this will be a singleton.
-/
partial def filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
    InfoTree → List InfoTree
  | .context ctx tree => tree.filter p m |>.map (.context ctx)
  | .node info children =>
    if p info then
      [.node info (children.toList.map (filter p m)).join.toPArray']
    else
      (children.toList.map (filter p m)).join
  | .hole mvar => if m mvar then [.hole mvar] else []

end Lean.Elab.InfoTree


namespace Pantograph.Frontend

-- Info tree filtering functions

structure TacticInvocation where
  info : Elab.TacticInfo
  ctx : Elab.ContextInfo
  children : PersistentArray Elab.InfoTree
namespace TacticInvocation

/-- Return the range of the tactic, as a pair of file positions. -/
@[export pantograph_frontend_tactic_invocation_range]
protected def range (t : TacticInvocation) : Position × Position := t.ctx.fileMap.stxRange t.info.stx

/-- Pretty print a tactic. -/
protected def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

/-- Run a tactic on the goals stored in a `TacticInvocation`. -/
protected def runMetaMGoalsBefore (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxBefore <| x t.info.goalsBefore

/-- Run a tactic on the after goals stored in a `TacticInvocation`. -/
protected def runMetaMGoalsAfter (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxAfter <| x t.info.goalsAfter

/-- Run a tactic on the main goal stored in a `TacticInvocation`. -/
protected def runMetaM (t : TacticInvocation) (x : MVarId → MetaM α) : IO α := do
  match t.info.goalsBefore.head? with
  | none => throw <| IO.userError s!"No goals at {← t.pp}"
  | some g => t.runMetaMGoalsBefore fun _ => do g.withContext <| x g

protected def goalState (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsBefore (fun gs => gs.mapM fun g => do Meta.ppGoal g)

protected def goalStateAfter (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsAfter (fun gs => gs.mapM fun g => do Meta.ppGoal g)

protected def ppExpr (t : TacticInvocation) (e : Expr) : IO Format :=
  t.runMetaM (fun _ => do Meta.ppExpr (← instantiateMVars e))

end TacticInvocation

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : Elab.InfoTree) (context?: Option Elab.ContextInfo) (pred : Elab.Info → Bool) :
    List (Elab.Info × Option Elab.ContextInfo × PersistentArray Elab.InfoTree) :=
  match t with
  | .context inner t => findAllInfo t (inner.mergeIntoOuter? context?) pred
  | .node i children  =>
      (if pred i then [(i, context?, children)] else []) ++ children.toList.bind (fun t => findAllInfo t context? pred)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
private def collectTacticNodes (t : Elab.InfoTree) : List TacticInvocation :=
  let infos := findAllInfo t none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
    | (.ofTacticInfo i, some ctx, children) => .some ⟨i, ctx, children⟩
    | _ => none

def collectTactics (t : Elab.InfoTree) : List TacticInvocation :=
  collectTacticNodes t

/-- Collect elaborated terms below a tactic, including tactic-specific nested info nodes. -/
private partial def collectDescendantTerms : Elab.InfoTree → List Elab.TermInfo
  | .context _ tree => collectDescendantTerms tree
  | .node (.ofTermInfo info) children =>
    info :: children.toList.bind collectDescendantTerms
  | .node _ children => children.toList.bind collectDescendantTerms
  | .hole _ => []

private def termRange (term : Elab.TermInfo) : Option (Nat × Nat) := do
  let start ← term.stx.getPos?
  let stop ← term.stx.getTailPos?
  pure (start.byteIdx, stop.byteIdx)

private def syntaxRange (stx : Syntax) : Option (Nat × Nat) := do
  let start ← stx.getPos?
  let stop ← stx.getTailPos?
  pure (start.byteIdx, stop.byteIdx)

private def jsonObject (fields : List (String × Json)) : Json :=
  Json.mkObj fields

private def semanticReference?
    (actionCtx : Pantograph.ModelSexpContext)
    (termInfos : List Elab.TermInfo)
    (stx : Syntax) : MetaM (List (String × Json)) := do
  let some range := syntaxRange stx | return []
  let some info := termInfos.find? fun info => termRange info == some range
    | return []
  let expression ← instantiateMVars info.expr
  let head := expression.consumeMData.getAppFn.consumeMData
  match head with
  | .fvar fvarId =>
    match actionCtx.fvarIndices.find? fvarId with
    | some index =>
      return [
        ("semanticRole", .str "local"),
        ("contextIndex", .num index),
      ]
    | none =>
      -- This identifier belongs to a nested source scope, not the tactic's
      -- input goal. Preserve its spelling without inventing a pointer target.
      return [("semanticRole", .str "scoped_local")]
  | .const declName _ =>
    let env ← getEnv
    return [
      ("semanticRole", .str (if env.isConstructor declName then "constructor" else "global")),
      ("name", .str declName.toString),
    ]
  | _ => return []

private partial def serializeSourceSyntax
    (actionCtx : Pantograph.ModelSexpContext)
    (termInfos : List Elab.TermInfo)
    (stx : Syntax) : MetaM Json := do
  let source := stx.reprint.getD (toString stx) |>.trim
  let positionFields := match syntaxRange stx with
    | some (start, stop) => [("sourceStart", .num start), ("sourceEnd", .num stop)]
    | none => []
  match stx with
  | .missing =>
    return jsonObject <| [("tag", .str "missing")] ++ positionFields
  | .atom _ value =>
    return jsonObject <| [
      ("tag", .str "atom"),
      ("source", .str value),
    ] ++ positionFields
  | .ident _ rawValue _ _ =>
    let semanticFields ← semanticReference? actionCtx termInfos stx
    return jsonObject <| [
      ("tag", .str "identifier"),
      ("source", .str rawValue.toString),
    ] ++ semanticFields ++ positionFields
  | .node _ kind children =>
    let serializedChildren ← children.mapM (serializeSourceSyntax actionCtx termInfos)
    return jsonObject <| [
      ("tag", .str "node"),
      ("kind", .str kind.toString),
      ("source", .str source),
      ("children", .arr serializedChildren),
    ] ++ positionFields

/-- Keep one outermost elaborated term for each source range. -/
private def outermostOwnedTerms (invocation : TacticInvocation) : List Elab.TermInfo :=
  let terms := invocation.children.toList.bind collectDescendantTerms |>.filter fun term =>
    !term.isBinder && (Elab.Info.ofTermInfo term).isOriginal && (termRange term).isSome
  terms.foldl (init := []) fun selected term =>
    match termRange term with
    | none => selected
    | some (start, stop) =>
      let contained := terms.any fun other =>
        match termRange other with
        | some (otherStart, otherStop) =>
          (otherStart < start || stop < otherStop) &&
            otherStart <= start && stop <= otherStop
        | none => false
      if contained || selected.any (termRange · == some (start, stop)) then
        selected
      else
        selected ++ [term]

private def serializeInvokedTerm
    (invocation : TacticInvocation)
    (term : Elab.TermInfo) : IO Protocol.InvokedTerm := do
  let some (sourceStart, sourceEnd) := termRange term
    | throw <| IO.userError "Elaborated tactic term has no source range"
  invocation.ctx.runMetaM {} <| Meta.withMCtx invocation.info.mctxAfter <|
    Meta.withLCtx term.lctx #[] do
      let some goal := invocation.info.goalsBefore.head?
        | throwError "Tactic invocation has no input goal"
      let goalDecl ← goal.getDecl
      let actionCtx ← Pantograph.mkModelSexpContext goalDecl.lctx
      let actionSexp ← Pantograph.serializeActionExpressionSexp actionCtx term.expr
      pure {
        source := term.stx.reprint.getD (toString term.stx) |>.trim
        syntaxKind := toString term.stx.getKind
        sourceStart
        sourceEnd
        actionSexp
      }

private def serializeInvokedTacticSyntax
    (invocation : TacticInvocation)
    (termInfos : List Elab.TermInfo) : IO String := do
  invocation.ctx.runMetaM {} <| Meta.withMCtx invocation.info.mctxAfter do
    let some goal := invocation.info.goalsBefore.head?
      | throwError "Tactic invocation has no input goal"
    let goalDecl ← goal.getDecl
    Meta.withLCtx goalDecl.lctx #[] do
      let actionCtx ← Pantograph.mkModelSexpContext goalDecl.lctx
      return (← serializeSourceSyntax actionCtx termInfos invocation.info.stx).compress

private def isBinderIntroducingTactic (stx : Syntax) : Bool :=
  let kind := stx.getKind
  kind == ``Lean.Parser.Tactic.intro ||
    kind == ``Lean.Parser.Tactic.intros ||
    kind == ``Lean.Parser.Tactic.rintro ||
    kind.toString == "Lean.Elab.Tactic.Ext.ext"

private partial def collectOriginalIdentifiers : Syntax → List Syntax
  | stx@(.ident _ _ _ _) =>
    match stx.getHeadInfo with
    | .original .. => [stx]
    | _ => []
  | .node _ _ args => args.toList.bind collectOriginalIdentifiers
  | _ => []

private def newlyIntroducedUserNames (invocation : TacticInvocation) : IO (Array Name) := do
  let beforeIds ← invocation.runMetaMGoalsBefore fun goals => do
    let mut ids := #[]
    for goal in goals do
      let decl ← goal.getDecl
      ids := ids ++ decl.lctx.getFVarIds
    pure ids
  invocation.runMetaMGoalsAfter fun goals => do
    let mut names := #[]
    for goal in goals do
      let decl ← goal.getDecl
      for fvarId in decl.lctx.getFVarIds do
        if !beforeIds.contains fvarId then
          names := names.push (decl.lctx.get! fvarId).userName
    pure names

private def collectSyntaxArguments
    (invocation : TacticInvocation) : IO (Array Protocol.InvokedSyntaxArgument) := do
  if !isBinderIntroducingTactic invocation.info.stx then
    return #[]
  let introducedNames ← newlyIntroducedUserNames invocation
  let mut arguments := #[]
  for stx in collectOriginalIdentifiers invocation.info.stx do
    let name := stx.getId.eraseMacroScopes
    if introducedNames.contains name then
      let some start := stx.getPos? | continue
      let some stop := stx.getTailPos? | continue
      arguments := arguments.push {
        role := "fresh_name"
        source := stx.reprint.getD name.toString |>.trim
        syntaxKind := toString stx.getKind
        sourceStart := start.byteIdx
        sourceEnd := stop.byteIdx
      }
  return arguments

@[export pantograph_frontend_collect_tactics_from_compilation_step_m]
def collectTacticsFromCompilationStep (step : CompilationStep)
    (options : Protocol.Options := {}) : IO (List Protocol.InvokedTactic) := do
  let tactics := step.trees.bind collectTactics |>.filter fun invocation =>
    (Elab.Info.ofTacticInfo invocation.info).isOriginal
  tactics.mapM λ invocation => do
    let goalBefore := (Format.joinSep (← invocation.goalState) "\n").pretty
    let goalAfter := (Format.joinSep (← invocation.goalStateAfter) "\n").pretty
    let tactic := invocation.info.stx.reprint.getD (toString invocation.info.stx)
    try
      let termInfos := invocation.children.toList.bind collectDescendantTerms |>.filter fun term =>
        (Elab.Info.ofTermInfo term).isOriginal && (termRange term).isSome
      let terms ← outermostOwnedTerms invocation |>.toArray.mapM
        (serializeInvokedTerm invocation)
      let sourceSyntax ← serializeInvokedTacticSyntax invocation termInfos
      let syntaxArgs ← collectSyntaxArguments invocation
      let goalsBefore ← invocation.runMetaMGoalsBefore fun goals =>
        goals.toArray.mapM fun goal => do
          let decl ← goal.getDecl
          Pantograph.serializeGoal options goal decl
      let goalsAfter ← invocation.runMetaMGoalsAfter fun goals =>
        goals.toArray.mapM fun goal => do
          let decl ← goal.getDecl
          Pantograph.serializeGoal options goal decl
      return {
        goalBefore, goalAfter, goalsBefore, goalsAfter, tactic, sourceSyntax, terms, syntaxArgs
      }
    catch e =>
      let captureError := toString e
      return {
        goalBefore,
        goalAfter,
        goalsBefore := #[],
        goalsAfter := #[],
        captureError? := some captureError,
        tactic,
      }

structure InfoWithContext where
  info: Elab.Info
  context?: Option Elab.ContextInfo := .none

private def collectSorrysInTree (t : Elab.InfoTree) : List InfoWithContext :=
  let infos := findAllInfo t none fun i => match i with
    | .ofTermInfo { expectedType?, expr, stx, .. } =>
      expr.isSorry ∧ expectedType?.isSome ∧ stx.isOfKind `Lean.Parser.Term.sorry
    | .ofTacticInfo { stx, .. } =>
      -- The `sorry` term is distinct from the `sorry` tactic
      stx.isOfKind `Lean.Parser.Tactic.tacticSorry
    | _ => false
  infos.map fun (info, context?, _) => { info, context? }

-- NOTE: Plural deliberately not spelled "sorries"
@[export pantograph_frontend_collect_sorrys_m]
def collectSorrys (step: CompilationStep) : List InfoWithContext :=
  step.trees.bind collectSorrysInTree



/--
Since we cannot directly merge `MetavarContext`s, we have to get creative. This
function duplicates frozen mvars in term and tactic info nodes, and add them to
the current `MetavarContext`.
-/
@[export pantograph_frontend_sorrys_to_goal_state]
def sorrysToGoalState (sorrys : List InfoWithContext) : MetaM GoalState := do
  assert! !sorrys.isEmpty
  let goalsM := sorrys.mapM λ i => do
    match i.info with
    | .ofTermInfo termInfo  => do
      let mvarId ← MetaTranslate.translateMVarFromTermInfo termInfo i.context?
      return [mvarId]
    | .ofTacticInfo tacticInfo => do
      MetaTranslate.translateMVarFromTacticInfoBefore tacticInfo i.context?
    | _ => panic! "Invalid info"
  let goals := (← goalsM.run {} |>.run' {}).bind id
  let root := match goals with
    | [] => panic! "This function cannot be called on an empty list"
    | [g] => g
    | _ => { name := .anonymous }
  GoalState.createFromMVars goals root



end Pantograph.Frontend
