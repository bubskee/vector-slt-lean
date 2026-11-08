import VectorSLT
open Lean Elab Command

elab "#dump_types" : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`VectorSLT).isPrefixOf mod do continue
    if n.isInternal then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    out := out.push s!"{mod} {kind} {n} :: {ci.type.hash} :: {toString ci.type}"
  out := out.qsort (· < ·)
  IO.FS.writeFile (System.FilePath.mk (← IO.getEnv "DUMP_OUT").get!) (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} declarations"

#dump_types
