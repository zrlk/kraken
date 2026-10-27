/-
# SceCli — `sce`'s command line, as a pure function

`parseArgs` reads the argument list into `Opts`.  A usage error is `.error msg?` (exit 4): `msg?` is a
specific message (`sce: unknown option X`, `sce: --check-only: --live-proof emits a file`) or `none`, and the
usage line with the flag list follows it.  The `--threads`, `--final` and `--watch` values are kept as text
(cldoc's `threads=`/`final=`/`watch=` values); the live stage reads them (M3b).
-/
import WeakCore.SceText

namespace SceCli

inductive Mode
  | emit       -- the whole program as one `.w`
  | checkOnly
  | printElab
  | emitUnit
  deriving Repr, BEq, Inhabited

structure Opts where
  help       : Bool := false
  input      : String := ""
  incl       : List String := []
  out        : Option String := none
  mode       : Mode := .emit
  threads    : Option String := none
  live       : Option Nat := none
  final      : Option String := none
  watch      : Option String := none
  promises   : Option Nat := none
  depth      : Option Nat := none
  crash      : Option Nat := none
  liveStrict : Bool := false
  liveProof  : Bool := false
  /-- `--live-cert[=N]` (item 38): the default certificate budget `N` -/
  liveCert   : Option Nat := none
  deriving Repr, BEq, Inhabited

def Opts.isW (o : Opts) : Bool := o.input.endsWith ".w"

/-- Any of the live options present. -/
def Opts.wantsLive (o : Opts) : Bool :=
  o.threads.isSome || o.live.isSome || o.final.isSome || o.watch.isSome || o.promises.isSome ||
  o.depth.isSome || o.crash.isSome || o.liveStrict || o.liveCert.isSome

abbrev CliM := Except (Option String)

def num (v : String) : CliM Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error none

/-- `--key=value` split; `none` if `a` has no `=`. -/
def splitEq (a : String) : Option (String × String) :=
  match a.splitOn "=" with
  | k :: v :: rest => some (k, "=".intercalate (v :: rest))
  | _ => none

/-- At most one of `--check-only`, `--print-elab`, `--emit-unit`. -/
def setMode (o : Opts) (m : Mode) : CliM Opts :=
  if o.mode == .emit || o.mode == m then .ok { o with mode := m } else .error none

def parseArgsAux : List String → Opts → Bool → CliM Opts
  | [], o, _ => .ok o
  | "--help" :: _, _, _ => .ok { help := true }
  | "-I" :: d :: rest, o, sawInput => parseArgsAux rest { o with incl := o.incl ++ [d] } sawInput
  | "-o" :: f :: rest, o, sawInput => parseArgsAux rest { o with out := some f } sawInput
  | "--check-only" :: rest, o, s => do parseArgsAux rest (← setMode o .checkOnly) s
  | "--print-elab" :: rest, o, s => do parseArgsAux rest (← setMode o .printElab) s
  | "--emit-unit" :: rest, o, s => do parseArgsAux rest (← setMode o .emitUnit) s
  | "--live-strict" :: rest, o, s => parseArgsAux rest { o with liveStrict := true } s
  | "--live-proof" :: rest, o, s => parseArgsAux rest { o with liveProof := true } s
  | "--live-cert" :: rest, o, s => parseArgsAux rest { o with liveCert := some 20000 } s
  | a :: rest, o, sawInput =>
    if a == "-I" || a == "-o" then .error none
    else if a.startsWith "-" then
      match splitEq a with
      | some ("--threads", v) => parseArgsAux rest { o with threads := some v } sawInput
      | some ("--final", v) => parseArgsAux rest { o with final := some v } sawInput
      | some ("--watch", v) => parseArgsAux rest { o with watch := some v } sawInput
      | some ("--live", v) => do parseArgsAux rest { o with live := some (← num v) } sawInput
      | some ("--promises", v) => do parseArgsAux rest { o with promises := some (← num v) } sawInput
      | some ("--depth", v) => do parseArgsAux rest { o with depth := some (← num v) } sawInput
      | some ("--crash", v) => do parseArgsAux rest { o with crash := some (← num v) } sawInput
      | some ("--live-cert", v) => do parseArgsAux rest { o with liveCert := some (← num v) } sawInput
      | _ => .error (some (SceText.unknownOption a))
    else if sawInput then .error none
    else parseArgsAux rest { o with input := a } true

/-- The command line, or a usage error (exit 4). -/
def parseArgs (args : List String) : CliM Opts := do
  let o ← parseArgsAux args {} false
  if o.help then return o
  if o.input.isEmpty then throw none
  unless o.input.endsWith ".u" || o.input.endsWith ".w" do throw none
  if o.isW && (o.mode == .printElab || o.mode == .emitUnit) then throw none
  if o.mode == .checkOnly && o.liveProof then throw (some SceText.checkOnlyProof)
  if o.liveCert.isSome && o.promises.any (· > 0) then throw (some SceText.certOptPromises)
  if o.liveCert.isSome && o.threads.isSome && o.live != some 0 then throw (some SceText.certOptThreads)
  pure o

/-! ## Tests -/

instance : BEq (CliM Opts) :=
  ⟨fun a b => match a, b with | .ok x, .ok y => x == y | .error x, .error y => x == y | _, _ => false⟩

#guard parseArgs ["a.u"] == .ok { input := "a.u" }
#guard parseArgs ["-I", "lib", "-I", "x", "a.u", "-o", "o.w"] ==
  .ok { input := "a.u", incl := ["lib", "x"], out := some "o.w" }
#guard parseArgs ["--check-only", "p.w"] == .ok { input := "p.w", mode := .checkOnly }
#guard parseArgs ["--print-elab", "a.u"] == .ok { input := "a.u", mode := .printElab }
#guard parseArgs ["--live=2", "--depth=40", "--promises=1", "--crash=0", "--live-strict", "a.u"] ==
  .ok { input := "a.u", live := some 2, depth := some 40, promises := some 1, crash := some 0, liveStrict := true }
#guard parseArgs ["--threads={init}{.unit}{[0]}{[(\"w\", .int, [])]}", "a.u"] ==
  .ok { input := "a.u", threads := some "{init}{.unit}{[0]}{[(\"w\", .int, [])]}" }
#guard parseArgs ["--final={[[0, 1]]}", "a.u"] == .ok { input := "a.u", final := some "{[[0, 1]]}" }
#guard parseArgs ["a.u", "--help", "--bogus"] == .ok { help := true }
#guard parseArgs [] == .error none
#guard parseArgs ["a.c"] == .error none
#guard parseArgs ["a.u", "b.u"] == .error none
#guard parseArgs ["--bogus", "a.u"] == .error (some (SceText.unknownOption "--bogus"))
#guard parseArgs ["--live=x", "a.u"] == .error none
#guard parseArgs ["a.u", "-I"] == .error none
#guard parseArgs ["--check-only", "--emit-unit", "a.u"] == .error none
#guard parseArgs ["--print-elab", "p.w"] == .error none
#guard parseArgs ["--live-proof", "a.u"] == .ok { input := "a.u", liveProof := true }
#guard parseArgs ["--check-only", "--live-proof", "a.u"] == .error (some SceText.checkOnlyProof)
#guard parseArgs ["--live-proof", "--check-only", "a.u"] == .error (some SceText.checkOnlyProof)
#guard SceText.help.endsWith "\n\nShare and enjoy!\n"
-- the option lines of the usage block (the --threads entry spans three)
#guard (SceText.flagList.splitOn "\n").length == 13
-- --live-cert (item 38)
#guard parseArgs ["--live-cert", "a.u"] == .ok { input := "a.u", liveCert := some 20000 }
#guard parseArgs ["--live-cert=500", "a.u"] == .ok { input := "a.u", liveCert := some 500 }
#guard parseArgs ["--live-cert=x", "a.u"] == .error none
#guard parseArgs ["--check-only", "--live-cert", "a.u"] == .ok { input := "a.u", mode := .checkOnly, liveCert := some 20000 }
#guard parseArgs ["--live-cert", "--promises=1", "a.u"] == .error (some SceText.certOptPromises)
#guard parseArgs ["--live-cert", "--promises=0", "a.u"] == .ok { input := "a.u", promises := some 0, liveCert := some 20000 }
#guard parseArgs ["--live-cert", "--threads={f}{_}{[]}{[]}", "a.u"] == .error (some SceText.certOptThreads)
#guard parseArgs ["--live-cert", "--threads={f}{_}{[]}{[]}", "--live=0", "a.u"] ==
  .ok { input := "a.u", threads := some "{f}{_}{[]}{[]}", live := some 0, liveCert := some 20000 }

end SceCli
