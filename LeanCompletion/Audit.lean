import LeanCompletion.JSP001022

#check _root_.LeanCompletion.jsp_001022_original_enumeration_chain

example :
∀ a : ℕ+ → ℕ+, StrictMono a →
  0 < Filter.liminf (fun x : ℝ =>
    (∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
      then ((a i : ℕ) : ℝ)⁻¹ else 0) / Real.log x) Filter.atTop →
  ∃ k : ℕ+ → ℕ+, StrictMono k ∧
    (∀ i : ℕ+, (a (k i) : ℕ) ∣ (a (k (i + 1)) : ℕ)) ∧
    Filter.limsup (fun x : ℝ => ENNReal.ofReal
      ((∑' i : ℕ+, if ((a i : ℕ) : ℝ) < x
        then 1 / (((a i : ℕ) : ℝ) * Real.log ((a i : ℕ) : ℝ)) else 0) /
        Real.log (Real.log x))) Filter.atTop ≤
    Filter.limsup (fun x : ℝ => ENNReal.ofReal
      ((Set.ncard {i : ℕ+ | ((a (k i) : ℕ) : ℝ) < x} : ℝ) /
        Real.log (Real.log x))) Filter.atTop :=
  _root_.LeanCompletion.jsp_001022_original_enumeration_chain

namespace JspExtensionAudit
open Lean
private def refs (e : Expr) : List Name := e.getUsedConstants.toList
private def body : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none
private def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"
private def encodeNames (ns : List Name) : Json :=
  Json.arr ((ns.eraseDups.map (fun n => Json.str n.toString)).toArray)
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for text in (["LeanCompletion.jsp_001022_original_enumeration_chain", "LeanCompletion.jsp_001022_eventual_lower_bound", "LeanCompletion.jsp_001022_finite_abel_lower_bound", "LeanCompletion.jsp_001022_reciprocal_weight_specialization", "LeanCompletion.jsp_001022_natural_loglog_lower_bound", "LeanCompletion.jsp_001022_eventual_to_finite_prefix", "LeanCompletion.jsp_001022_density_to_natural_erdos_lower_bound", "LeanCompletion.jsp_001022_density_bridge", "LeanCompletion.erdos_1217_explicit", "LeanCompletion.jsp_001022_chain_strict_cutoff", "LeanCompletion.jsp_001022_reciprocal_strict_cutoff", "LeanCompletion.jsp_001022_erdos_strict_cutoff", "LeanCompletion.jsp_001022_erdos_density_ennreal", "LeanCompletion.jsp_001022_positive_enumeration_sums", "LeanCompletion.jsp_001022_positive_subsequence_indices"] : List String) do
    let n := (text.splitOn ".").foldl Name.str Name.anonymous
    let some info := env.find? n | throwError "Unknown declaration: {text}"
    let term := body info
    rows := rows.push (Json.mkObj [
      ("name", Json.str text), ("kind", Json.str (kind info)),
      ("type_dependencies", encodeNames (refs info.type)),
      ("body_dependencies", encodeNames (term.map refs |>.getD [])),
      ("body_available", Json.bool term.isSome)])
  logInfo m!"B8_DEPENDENCIES:{(Json.arr rows).compress}"
end JspExtensionAudit

#print axioms _root_.LeanCompletion.jsp_001022_original_enumeration_chain

#eval (do
  for n in ([`LeanCompletion.JSP001022, `LeanMarathon.Main, `Mathlib, `Architect] : List Lean.Name) do
    let p <- Lean.findOLean n
    IO.println ("EXTENSION_MODULE:" ++ (Lean.Json.mkObj [
      ("module", Lean.Json.str n.toString),
      ("path", Lean.Json.str p.toString)]).compress)
  : IO Unit)
