import Lean
import Scc.Cert.Gen

/-!
# Tests of the certificate generator

`Scc.Cert.Gen.quote` gives Lean string literals that read back as the string
(Lean's own literal decoder), including leading spaces, tabs, backslashes,
quotes, control characters, non-ASCII text and an empty last line. Whole
certificates are generated and checked by `Scc/Test/run.sh`.
-/

namespace Scc.Test.Cert

open Scc.Cert.Gen

def samples : List String :=
  ["", "a", "\n", "line\n", "  two leading spaces\n\tand a tab\n",
   "back\\slash \"quoted\" \x01 \x7f é ∀ 🙂\r\n", " \n \n", "trailing space \nno newline"]

#guard samples.all fun s => Lean.Syntax.decodeStrLit (quote s) == some s

-- One source line per line of the string.
/--
info: "\
  ab\n\
  \x20c\n\
  "
-/
#guard_msgs in #eval IO.println (quote "ab\n c\n")

-- The configuration term names every field the command line sets.
/-- info: ({ arch := .arm, host := .linux, gc := .none } : Scc.Config) -/
#guard_msgs in #eval IO.println (cfgTerm { arch := .arm })

-- A certificate imports one ISA's support modules, embeds both texts with
-- their digests, and states the lowerability theorem.
#guard
  let c := render { arch := .x64 } "t.w" "src\n" "asm\n" none [] { hasNeed := true }
  c.startsWith "import Scc.Cert.X64\nimport Scc.Cert.OutStageX64\nimport Scc.Cert.SrcTerm\n" &&
  (c.splitOn "-- SHA-256 (UTF-8): ").length == 3 &&
  (c.splitOn "theorem lowerable : Scc.Emit.X64.ProgramWCLowerable prog := by decide +kernel").length == 2 &&
  (c.splitOn "#guard Scc.Cert.X64.reproduces config source asm").length == 2
#guard (render { arch := .arm } "t.w" "" "" none [] { hasNeed := true }).startsWith
  "import Scc.Cert.Arm\nimport Scc.Cert.OutStageA64\nimport Scc.Cert.SrcTerm\n"

-- It states acceptance, placement and both together for an accepted
-- program with a stack need table; for another, its non-acceptance and
-- placement only; without a stack need table, nothing but the source and the
-- reason (no partial certificate).
#guard
  let c := render { arch := .arm } "t.w" "" "" none [] { accepted := true, hasNeed := true }
  (c.splitOn "theorem prog_accepted : Scc.Lower.Accepted0 prog_src = true").length == 2 &&
  (c.splitOn "theorem prog_placeOK : ").length == 2 &&
  (c.splitOn "theorem prog_cert_ready : ").length == 2 &&
  (c.splitOn "#guard Scc.Cert.Link.A64.parsesTo asm out.prog out.secs").length == 2
#guard
  let c := render { arch := .x64 } "t.w" "" "" (some ([], [])) [] { hasNeed := true }
  (c.splitOn "theorem prog_not_accepted : Scc.Lower.Accepted0 prog_src = false").length == 2 &&
  (c.splitOn "theorem prog_placeOK : ").length == 2 &&
  (c.splitOn "theorem prog_cert_ready").length == 1 &&
  (c.splitOn "#guard Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs").length == 2
-- The emitter is checked per function (`emitItemsMaps_of_stages`): one
-- `emit_eq_i` per function of the lowered IR; on x64 each starts at the local
-- label number its predecessor's literal leaves.
#guard
  let c := render { arch := .arm } "t.w" "" "" none [] { hasNeed := true, funcs := 2 }
  (c.splitOn "theorem emit_eq_").length == 3 &&
  (c.splitOn "theorem pre_eq : Scc.Emit.A64.emitPre loweredLit.1").length == 2 &&
  (c.splitOn "Scc.Emit.A64.emitItemsMaps_of_stages pre_eq funcs_eq post_eq").length == 2 &&
  (c.splitOn "mapM_ok_cons emit_eq_0 <|\n    Scc.Cert.OutLit.mapM_ok_cons emit_eq_1 <|\n    rfl").length == 2
#guard
  let c := render { arch := .x64 } "t.w" "" "" (some ([], [])) [] { hasNeed := true, funcs := 2 }
  (c.splitOn "theorem emit_eq_").length == 3 &&
  (c.splitOn "loweredLit.1.funcs[1]! emitLit_0.2.1 = .ok emitLit_1").length == 2 &&
  (c.splitOn "Scc.Emit.X64.emitFuncs_cons emit_eq_1 <|\n    rfl").length == 2 &&
  (c.splitOn "Scc.Emit.X64.emitItemsMaps_of_stages pre_eq funcs_eq post_eq").length == 2
-- The size table's labels are checked `sizesChunk` per kernel run.
#guard
  let offs := (List.range 70).map fun i => (s!"L{i}", i)
  let c := render { arch := .x64 } "t.w" "" "" (some ([], offs)) [] { hasNeed := true }
  (c.splitOn "theorem sizes_offs_").length == 3 &&
  (c.splitOn "Scc.Cert.X64.offsAll_drop 64 sizes_offs_1 <|\n    by decide +kernel").length == 2 &&
  (c.splitOn "Scc.Cert.X64.sizesOkFast_of_chunks walk_eq sizes_end sizes_offs").length == 2
-- With a failing component (`scc --cert-fails 11`) the file proves `placeOK`
-- false at it, and states neither `prog_placeOK` nor `prog_cert_ready`.
#guard
  let c := render { arch := .arm } "t.w" "" "" none [] { accepted := true, hasNeed := true, fails := some 11 }
  (c.splitOn "theorem prog_placeOK_11 : Scc.Cert.PlaceOK.A64.a11 outLit").length == 2 &&
  (c.splitOn "placeOK_eq_false_of_a11 prog_placeOK_11").length == 2 &&
  (c.splitOn "theorem prog_placeOK_1 : ").length == 1 &&
  (c.splitOn "theorem prog_not_placeOK : ").length == 2 &&
  (c.splitOn "theorem prog_placeOK : ").length == 1 &&
  (c.splitOn "theorem prog_cert_ready").length == 1 &&
  (c.splitOn "`prog_cert_ready` states").length == 1
#guard
  let c := render { arch := .x64 } "t.w" "" "" (some ([], [])) [] { hasNeed := true, fails := some 4 }
  (c.splitOn "theorem prog_placeOK_4 : Scc.Cert.PlaceOK.X64.a4 placeCfg outLit").length == 2 &&
  (c.splitOn "theorem prog_not_placeOK : ").length == 2
#guard
  let c := render { arch := .x64 } "t.w" "" "" (some ([], [])) [] { hasNeed := true }
  (c.splitOn "theorem prog_placeOK_11 : Scc.Cert.PlaceOK.X64.a11 outLit").length == 2 &&
  (c.splitOn "prog_placeOK_8 prog_placeOK_9 prog_placeOK_11").length == 2
#guard
  let c := render { arch := .arm } "t.w" "src\n" "" none [] { accepted := true }
  c == renderOutside { arch := .arm } "t.w" "src\n" &&
  (c.splitOn outsideMark).length == 2 && (c.splitOn "theorem").length == 1 &&
  (c.splitOn "import").length == 1

end Scc.Test.Cert
