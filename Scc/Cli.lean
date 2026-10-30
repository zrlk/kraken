import Scc.Config
import Scc.Frontend
import Scc.Lower.Spec
import Scc.Lower.Spec1
import Scc.Cert.Gen
import Scc.Cert.Blocks
import Scc.Cert.Place

/-!
# The scc command line

```
scc [--arch x64|arm] [--host linux|raw] [--gc none] [-o out.s | -o - | -S] [--report] [--cert c.lean] [--blocks b.lean] [--code c.lean] prog.w
scc --check c.lean
```

Defaults: `--arch x64 --host linux --gc none`, output `prog.s` (the input
name with `.w` replaced by `.s`).  `-o -` or `-S` writes the assembly listing
to standard output instead, and then nothing else goes there (so
`scc -S prog.w | as -o prog.o` works).  `--report` prints every `Int` `+` site (each
keeps its overflow check: the places where the program can take the abort
outcome) and whether index facts bound it, on standard output, or on standard error when the listing goes
to standard output.  `--cert c.lean` also writes a certificate
(`Scc.Cert.Gen`) for the compilation to `c.lean`: it checks acceptance and
placement, and is not yet a correctness proof; `--check c.lean` checks one
(`lake env lean c.lean` in the Kraken package, with `lake` from `$LAKE`,
default `lake`): exit status 0 when it checks, 1 when it does not.
`--blocks b.lean` also writes the block data of the assembly
(`Scc.Cert.Blocks`: one `block_spec` command per block) to `b.lean` and its
coverage statistics to `b.lean.json`; on AArch64 also the placement data of
the compiled functions (`Scc.Cert.Place`: nodes, frame slots, and the source
variables and term at each node) to `b.place.lean` (`b` without `.lean`).
`--code c.lean` also writes
a self-contained check that every block is code at its place in the parsed
program, with the layout of its static link (its immediate table from the
lowering's placement trace, `Scc.Cert.Place.renderImms`) and that layout's
well-formedness and loader checks (`Scc.Cert.Blocks.code`), and that the
program writes words only, refusing (status 2) a listing with a memory
write outside the certified one-word fragment (`Scc.Cert.WideCheckA64`,
`Scc.Cert.WideCheckX64`) and a source program with a `newBuf` of zero-word
elements (`Scc.Frontend.codeDiags`); on x64 (`Scc.Cert.Blocks.codeX64`, with
GNU `as`'s instruction sizes) also the runtime code its proofs take as
hypotheses.  `--help`
prints the usage.

Exit status: 0 success; 1 an error in the source program (parse, type,
fragment, or a limit of the lowering), reported on standard error as
`file:line:col: error: message` where the position is known; 2 a usage error
or an option that is not implemented.

**Executables.**  Kraken's x64 and AArch64 syntaxes share names, so no
module may import both emitters.  The compiler is therefore one executable
per architecture, `scc-x64` (`Scc/MainX64.lean`) and `scc-arm`
(`Scc/MainArm.lean`), each `run` with its own emitter, and `scc` (`Scc.lean`)
is a driver that imports neither: it reads `--arch` the way `parseArgs` does
and runs the sibling executable of that architecture with the same arguments,
standard streams and exit status (an argument list `parseArgs` refuses goes
to `scc-x64`, which reports the error).
-/

namespace Scc.Cli

/-- Parsed options. -/
structure Opts where
  cfg : Config := {}
  out : Option String := none
  report : Bool := false
  input : Option String := none
  cert : Option String := none
  blocks : Option String := none
  code : Option String := none
  check : Option String := none
  certFails : Option Nat := none

def usage : String :=
  "usage: scc [--arch x64|arm] [--host linux|raw] [--gc none] [-o out.s | -o - | -S] [--report] [--cert c.lean] [--blocks b.lean] [--code c.lean] prog.w\n       scc --check c.lean"

def help : String := usage ++ "

  --arch x64|arm     target architecture (default x64; arm is AArch64 with FEAT_LSE2)
  --host linux|raw   target host (default linux; raw is not implemented)
  --gc none          memory manager (default none: a bump allocator that never frees)
  -o out.s           write the assembly to out.s (default: prog.s next to prog.w)
  -o -, -S           write the assembly listing to standard output
  --report           list the Int `+` sites (all checked) and which are boundable
  --cert c.lean      also write a certificate to c.lean: checks acceptance and placement;
                     not yet a correctness proof
  --cert-fails N     write the certificate as the failure of placeOK's component AN instead
                     (it checks only when AN fails; see Scc/Test/placediag.sh)
  --blocks b.lean    also write the block data of the assembly (block_spec lines) to b.lean,
                     and its coverage statistics to b.lean.json (arm: placement data to b.place.lean)
  --code c.lean      also write a check that every block is code at its place, and the static link's layout, to c.lean
  --check c.lean     check a certificate (exit 0 when it checks, 1 when it does not)
  --help             print this message

exit status: 0 success, 1 error in the program, 2 usage error or not implemented"

/-- A usage-level failure: message and exit status 2. -/
abbrev CliM := ExceptT String IO

def parseArgs : List String → Opts → Except String Opts
  | [], o => pure o
  | "--arch" :: v :: rest, o =>
      match Arch.ofString? v with
      | some a => parseArgs rest { o with cfg := { o.cfg with arch := a } }
      | none => throw s!"scc: --arch {v}: unknown architecture (available: x64, arm)"
  | "--host" :: v :: rest, o =>
      match Host.ofString? v with
      | some .raw => throw "scc: --host raw: not implemented"
      | some h => parseArgs rest { o with cfg := { o.cfg with host := h } }
      | none => throw s!"scc: --host {v}: unknown host (available: linux, raw)"
  | "--gc" :: v :: rest, o =>
      match Gc.ofString? v with
      | some g => parseArgs rest { o with cfg := { o.cfg with gc := g } }
      | none => throw s!"scc: --gc {v}: unknown collector (available: none)"
  | "-o" :: v :: rest, o => parseArgs rest { o with out := some v }
  | "--report" :: rest, o => parseArgs rest { o with report := true }
  | "--cert" :: v :: rest, o => parseArgs rest { o with cert := some v }
  | "--check" :: v :: rest, o => parseArgs rest { o with check := some v }
  | "--cert-fails" :: v :: rest, o =>
      match v.toNat? with
      | some n => parseArgs rest { o with certFails := some n }
      | none => throw s!"scc: --cert-fails {v}: not a component number"
  | "--blocks" :: v :: rest, o => parseArgs rest { o with blocks := some v }
  | "--code" :: v :: rest, o => parseArgs rest { o with code := some v }
  | "-S" :: rest, o => parseArgs rest { o with out := some "-" }
  | [opt], o =>
      if opt ∈ ["--arch", "--host", "--gc", "-o", "--cert", "--check", "--blocks", "--code", "--cert-fails"] then throw s!"scc: {opt}: missing value\n{usage}"
      else if opt.startsWith "-" then throw s!"scc: {opt}: unknown option\n{usage}"
      else if o.input.isSome then throw s!"scc: more than one input file\n{usage}"
      else pure { o with input := some opt }
  | f :: rest, o =>
      if f.startsWith "-" then throw s!"scc: {f}: unknown option\n{usage}"
      else if o.input.isSome then throw s!"scc: more than one input file\n{usage}"
      else parseArgs rest { o with input := some f }

/-- The default output name: `prog.w` → `prog.s`. -/
def defaultOut (input : String) : String :=
  if input.endsWith ".w" then String.ofList (input.toList.take (input.length - 2)) ++ ".s"
  else input ++ ".s"

/-- The Kraken package root of this executable (`<root>/.lake/build/bin/scc-…`),
or the working directory. -/
def packageRoot : IO System.FilePath := do
  let exe ← IO.appPath
  match exe.parent >>= (·.parent) >>= (·.parent) >>= (·.parent) with
  | some root => if ← (root / "lakefile.toml").pathExists then return root else return "."
  | none => return "."

/-- `scc --check c.lean`: elaborate the certificate with `lake env lean` in the
Kraken package (`lake` from `$LAKE`, default `lake`).  Exit status 0 when it
checks, 1 when it does not, 2 when it cannot be run. -/
def checkCert (file : String) : IO UInt32 := do
  let abs ← match ← (IO.FS.realPath file).toBaseIO with
    | .ok p => pure p
    | .error e => IO.eprintln s!"scc: cannot read {file}: {e}"; return 2
  let root ← packageRoot
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let cfg : IO.Process.SpawnArgs := {
    cmd := lake
    args := #["-d", root.toString, "env", "lean", abs.toString]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit }
  match ← (IO.Process.spawn cfg).toBaseIO with
  | .ok child =>
    let rc ← child.wait
    if rc == 0 then
      IO.println s!"{file}: certificate checks"
      return 0
    IO.eprintln s!"scc: {file}: the certificate does not check"
    return 1
  | .error e =>
    IO.eprintln s!"scc: cannot run {lake}: {e} (set LAKE to the lake command)"
    return 2

/-- Whether the lowered IR takes the thread-id shape (`scc_rt_main` calls
`wc_main(tcb)`) or spawns (a `clone`): a certificate then states `placeOK2`
(`Cert.Gen.Placement.spawn`). The same tests as `Scc.Cert.Spawn.X64.tidOf`
and `spawnsOf` (and their AArch64 twins), on the IR here, so that the driver
imports no ISA; untrusted (a wrong value gives a file that does not check). -/
def spawnShape (ir : IR.Program) : Bool :=
  ir.funcs.any fun f => f.blocks.any fun b => b.insts.any fun
    | .call _ g args => f.name == "scc_rt_main" && g == "wc_main" && args == [.reg "tcb"]
    | .clone .. => true
    | _ => false

/-- The compiler for architecture `arch`, with its emission `emit` (the
ISA's half of `lowerAll`: `Scc.Lower.A64.emitAll`, `Scc.Lower.X64.emitAll`,
with the text and the other outputs, `Scc.Lower.Listing`).  The program is
lowered by `Scc.Lower.lowerIR`, then emitted by `emit`, so that what `scc`
writes is the output of the ISA's `lowerAll` (`Scc/Lower/SpecA64.lean`,
`Scc/Lower/SpecX64.lean`).  Without
`--arch` it compiles for `arch`; with another `--arch` it refuses (status
2). `sizer`, if any, gives a certificate, the block data and the code check the instruction sizes of the text
(`Scc.Cert.Sizes.sizesOf`, on x64), from temporary files at the prefix it is
given. The listing's placement data, if any, gives the frames and labels of
`--blocks`' placement file (`Scc.Cert.Place.FnPlace`, on AArch64). `wide`, if any, is `--code`'s
one-word fragment check of the listing (`Scc.Cert.Blocks.code`). -/
def run (arch : Arch) (emit : Lower.Lowered → Except String Lower.Listing) (args : List String)
    (sizer : Option (String → String → IO (Except String (List Nat × List (String × Nat)))) := none)
    (wide : Option (String → Except String Unit) := none) :
    IO UInt32 := do
  let err (s : String) : IO Unit := IO.eprintln s
  if args.contains "--help" then IO.println help; return 0
  match parseArgs args { cfg := { arch } } with
  | .error m => err m; return 2
  | .ok o =>
    if o.cfg.arch != arch then
      err s!"scc: --arch {o.cfg.arch.name}: this executable emits {arch.name} only (use scc)"
      return 2
    if let some f := o.check then return ← checkCert f
    let toStdout := o.out == some "-"
    let info (s : String) : IO Unit := if toStdout then IO.eprintln s else IO.println s
    let some input := o.input | err s!"scc: no input file\n{usage}"; return 2
    let src ← match ← (IO.FS.readFile input).toBaseIO with
      | .ok s => pure s
      | .error e => err s!"scc: cannot read {input}: {e}"; return 2
    let c ← match Frontend.run src with
      | .ok c => pure c
      | .error ds => do
          for d in ds do err (d.render input)
          return 1
    if o.report then
      let nb := (c.adds.filter (·.boundable)).length
      info s!"{input}: {c.adds.length} checked `+` site(s), {nb} boundable by index facts"
      for s in c.adds do info (s.render input)
    let low ← match Lower.lowerIR o.cfg c.prog with
      | .ok l => pure l
      | .error m => err s!"{input}: error: {m}"; return 1
    let lst ← match emit low with
      | .ok l => pure l
      | .error m => err s!"scc: --arch {o.cfg.arch.name}: {m}"; return 2
    let asm := lst.text
    -- the size table (x64), for a certificate or block data
    let sizes ← match sizer, (o.cert <|> o.blocks <|> o.code) with
      | some f, some pre => match ← f (pre ++ ".scc_sizes") asm with
        | .ok s => pure (some s)
        | .error m => err s!"scc: cannot size the instructions: {m}"; return 2
      | _, _ => pure none
    if let some cf := o.cert then
      let name := (System.FilePath.mk input).fileName.getD input
      -- the label offsets in the text's order, as the code check has them
      -- (`Cert.Blocks.textOrder`): the placement check reads them in that order
      let sizesT := sizes.map fun (s, offs) => (s, Cert.Blocks.textOrder asm offs)
      -- acceptance, and the stack need's configuration as the code check has it
      let pl : Cert.Gen.Placement :=
        { accepted := Lower.Accepted0 c.prog, accepted1 := Lower.Accepted1 c.prog && c.prog.length == 1, hasNeed := lst.need.isSome,
          entries := Lower.threadEntries low.ir,
          budget := o.cfg.layout.stackBytes - IR.Tcb.headroom,
          fails := o.certFails, funcs := low.ir.funcs.length, parts := lst.parts,
          checked := low.ir.funcs.map (·.checkStack), spawn := spawnShape low.ir }
      match ← (IO.FS.writeFile cf (Cert.Gen.render o.cfg name src asm sizesT c.prog pl)).toBaseIO with
      | .ok () => pure ()
      | .error e => err s!"scc: cannot write {cf}: {e}"; return 2
    if let some bf := o.blocks then
      let (lines, stats) ← match Cert.Blocks.run o.cfg.arch asm (sizes.map (·.1)) with
        | .ok r => pure r
        | .error m => err s!"scc: --blocks: {m}"; return 2
      let mut outs := [(bf, lines), (bf ++ ".json", stats)]
      if let some pl := lst.places then
        let name := (System.FilePath.mk input).fileName.getD input
        let t ← match do Cert.Place.render name (← pl) low.marks with
          | .ok t => pure t
          | .error m => err s!"scc: --blocks: placement data: {m}"; return 2
        outs := outs ++ [((if bf.endsWith ".lean" then String.ofList (bf.toList.take (bf.length - 5)) else bf) ++ ".place.lean", t)]
      for (f, t) in outs do
        match ← (IO.FS.writeFile f t).toBaseIO with
        | .ok () => pure ()
        | .error e => err s!"scc: cannot write {f}: {e}"; return 2
    if let some cf := o.code then
      let ds := Frontend.codeDiags src c.prog
      if !ds.isEmpty then
        for d in ds do err ("scc: --code: " ++ d.render input)
        return 2
      let (_, pfx) := Cert.Blocks.codeName input
      let imms ← match Cert.Place.renderImms pfx low.marks with
        | .ok t => pure t
        | .error m => err s!"scc: --code: immediate table: {m}"; return 2
      let frames := low.budget.render pfx
      -- the stack need table (none for a program with non-tail recursion)
      let need := lst.need.map fun rows =>
        Lower.renderNeed o.cfg.arch rows (Lower.threadEntries low.ir)
          (o.cfg.layout.stackBytes - IR.Tcb.headroom) pfx
      let t ← match Cert.Blocks.code o.cfg.arch input asm wide sizes (some imms) (some frames) need with
        | .ok t => pure t
        | .error m => err s!"scc: --code: {m}"; return 2
      match ← (IO.FS.writeFile cf t).toBaseIO with
      | .ok () => pure ()
      | .error e => err s!"scc: cannot write {cf}: {e}"; return 2
    if toStdout then
      IO.print asm
      return 0
    let out := o.out.getD (defaultOut input)
    match ← (IO.FS.writeFile out asm).toBaseIO with
    | .ok () => return 0
    | .error e => err s!"scc: cannot write {out}: {e}"; return 2

/-- The executable of an architecture. -/
def exeOf : Arch → String
  | .x64 => "scc-x64"
  | .arm => "scc-arm"

/-- The `scc` driver: run the executable of the architecture that `--arch`
selects (default x64), next to this one, with the same arguments and
standard streams, and return its exit status. -/
def dispatch (args : List String) : IO UInt32 := do
  let arch := match parseArgs args {} with
    | .ok o => o.cfg.arch
    | .error _ => .x64
  let dir := (← IO.appPath).parent.getD "."
  let exe := dir / exeOf arch
  let cfg : IO.Process.SpawnArgs := {
    cmd := exe.toString
    args := args.toArray
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit }
  match ← (IO.Process.spawn cfg).toBaseIO with
  | .ok child => child.wait
  | .error e =>
    IO.eprintln s!"scc: cannot run {exe}: {e} (`lake build scc scc_x64 scc_arm` builds it)"
    return 2

end Scc.Cli
