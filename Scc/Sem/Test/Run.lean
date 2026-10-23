/-
Test support: running emitted `scc` programs on the canonical targets.

Not part of the statement and not trusted: a check that real compiler output
runs on the model (`Scc/Sem/Test/RunA64.lean`, `Scc/Sem/Test/RunX64.lean`).

- `layoutOf`: a realistic layout for an emitted text. Its `.rodata` gets
  its own region (the loader lays its image out there; only its labels are
  symbols). Its other data sections (`.data`, `.bss`, `.section`) are laid
  out from a base address the way a linker would: `.balign`/`.p2align`,
  labels, `.zero`, `.byte`, `.quad` (numbers, or code labels resolved by
  the target). The heap arena, the stack pool and the pinned region symbols
  get their own regions. The result has the data symbols as
  `Layout.symbols`, the non-zero data bytes as the image (8-byte words), and
  the labelled `exit_group` of each of the runtime's abort routines as the
  abort labels.
- `run`: a deterministic scheduler for the kernel model's machine.
  - Threads take turns, one step each.
  - An instruction step takes Kraken's last successor; for a load that is
    the newest write the thread may read.
  - A system call takes the kernel's first useful answer: `write` transfers
    every byte, then returns the full count (or, if asked, refuses a
    `write` to fd 1 with `-EPIPE`); `futex`, `rt_sigaction` and
    `arch_prctl` return 0; `clone` takes the first dormant slot;
    `exit_group(101)` is `abort k` only at the resolved abort label of `k`.
  - A thread at a resolved transfer site takes the transfer.
  - A run stops at the process's exit, at a fault (the kernel model's
    `faultAt`, an unmapped access `rootUnmapped`, or a faulting Kraken
    step), at a step the model does not admit, or when the fuel runs out.
-/
import Scc.Sem.Kernel

namespace Scc.Sem.Test

open Kraken.Promising

/-! ## Layout of an emitted text -/

/-- A number in assembler syntax: decimal or `0x` hexadecimal, maybe negative. -/
def parseInt (s : String) : Option Int :=
  let s := s.trimAscii.toString
  if s.startsWith "-" then (parseInt' (s.drop 1).toString).map (- ·) else parseInt' s
where
  parseInt' (s : String) : Option Int :=
    if s.startsWith "0x" || s.startsWith "0X" then
      (s.drop 2).toString.foldl (fun acc ch => acc.bind fun n =>
        if ch.isDigit then some (16 * n + (ch.toNat - '0'.toNat))
        else if 'a' ≤ ch ∧ ch ≤ 'f' then some (16 * n + (ch.toNat - 'a'.toNat + 10))
        else if 'A' ≤ ch ∧ ch ≤ 'F' then some (16 * n + (ch.toNat - 'A'.toNat + 10))
        else none) (some (0 : Int))
    else s.toNat?.map Int.ofNat

/-- The state of the data-section walk. -/
structure DataWalk where
  inData : Bool := false
  /-- In `.rodata`, laid out from `roCur` (the loader builds its image). -/
  inRo : Bool := false
  cur : Nat
  roCur : Nat := 0
  /-- The region the next `.zero` fills: the heap (0), the pool (1) or the
  pinned region (2). -/
  special : Option Nat := none
  syms : List (String × Nat) := []
  bytes : List (Nat × Nat) := []
  heap : Range := ⟨0, 0⟩
  pool : Range := ⟨0, 0⟩
  pinned : Range := ⟨0, 0⟩
  errors : List String := []

/-- Round `n` up to a multiple of `k`. -/
def alignUp (n k : Nat) : Nat := if k = 0 then n else (n + k - 1) / k * k

/-- One line of the text in the walk; `resolve` gives code labels. -/
def walkLine (heapSym poolSym pinnedSym : String) (heapLo poolLo pinnedLo : Nat) (resolve : String → Option Nat)
    (w : DataWalk) (line : String) : DataWalk :=
  let l := ((line.splitOn "//").headD "").trimAscii.toString
  let l := if l.startsWith "#" then "" else l
  if l.startsWith ".text" then { w with inData := false, inRo := false }
  else if l.startsWith ".section .rodata" then { w with inData := true, inRo := true }
  else if l.startsWith ".data" || l.startsWith ".bss" || l.startsWith ".section" then
    { w with inData := true, inRo := false }
  else if !w.inData then w
  else if w.inRo then roLine w l
  else if l.endsWith ":" then
    let nm := (l.dropEnd 1).toString
    if nm = heapSym then { w with special := some 0, syms := (nm, heapLo) :: w.syms }
    else if nm = poolSym then { w with special := some 1, syms := (nm, poolLo) :: w.syms }
    else if nm = pinnedSym then { w with special := some 2, syms := (nm, pinnedLo) :: w.syms }
    else { w with special := none, syms := (nm, w.cur) :: w.syms }
  else
    let ws := l.splitOn " "
    let dir := ws.headD ""
    let args := ((" ".intercalate (ws.drop 1)).splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")
    match dir with
    | ".balign" => { w with cur := alignUp w.cur ((parseInt (args.headD "1")).getD 1).toNat }
    | ".p2align" => { w with cur := alignUp w.cur (2 ^ ((parseInt (args.headD "0")).getD 0).toNat) }
    | ".zero" =>
      let n := ((parseInt (args.headD "0")).getD 0).toNat
      match w.special with
      | some 0 => { w with heap := ⟨heapLo, n⟩, special := none }
      | some 1 => { w with pool := ⟨poolLo, n⟩, special := none }
      | some _ => { w with pinned := ⟨pinnedLo, n⟩, special := none }
      | none => { w with cur := w.cur + n }
    | ".byte" =>
      let bs := args.map fun a => ((parseInt a).getD 0).toNat % 256
      { w with cur := w.cur + bs.length,
               bytes := (bs.zipIdx.map fun (b, i) => (w.cur + i, b)).reverse ++ w.bytes }
    | ".quad" =>
      let vs := args.map fun a =>
        match parseInt a with
        | some n => some (toNat' n % 2 ^ 64)
        | none => resolve a
      let errs := (args.zip vs).filterMap fun (a, v) => if v.isNone then some s!"unresolved .quad {a}" else none
      let bs := (vs.map (·.getD 0)).zipIdx.flatMap fun (v, i) =>
        (List.range 8).map fun j => (w.cur + 8 * i + j, v / 2 ^ (8 * j) % 256)
      { w with cur := w.cur + 8 * vs.length, bytes := bs.reverse ++ w.bytes, errors := errs ++ w.errors }
    | ".globl" | ".type" | ".size" | ".arch" | "" => w
    | d => { w with errors := s!"unknown data directive {d}" :: w.errors }
where
  toNat' (n : Int) : Nat := if n < 0 then (n + 2 ^ 64).toNat else n.toNat
  /-- A line of `.rodata`: labels at `roCur`, which the directives advance. -/
  roLine (w : DataWalk) (l : String) : DataWalk :=
    if l.endsWith ":" then { w with syms := ((l.dropEnd 1).toString, w.roCur) :: w.syms } else
    let ws := l.splitOn " "
    let args := ((" ".intercalate (ws.drop 1)).splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")
    let num (d : Nat) := ((parseInt (args.headD "")).getD d).toNat
    match ws.headD "" with
    | ".balign" => { w with roCur := alignUp w.roCur (num 1) }
    | ".p2align" => { w with roCur := alignUp w.roCur (2 ^ num 0) }
    | ".zero" => { w with roCur := w.roCur + num 0 }
    | ".byte" => { w with roCur := w.roCur + args.length }
    | ".quad" => { w with roCur := w.roCur + 8 * args.length }
    | ".globl" | ".type" | ".size" | "" => w
    | d => { w with errors := s!"unknown .rodata directive {d}" :: w.errors }

/-- The 8-byte image words of a list of (address, byte), the non-zero ones. -/
def imageWords (bytes : List (Nat × Nat)) : List (Nat × Nat) :=
  let words := bytes.foldl (fun (m : Std.HashMap Nat Nat) (a, b) =>
    m.insert (a / 8 * 8) ((m.getD (a / 8 * 8) 0) + b * 2 ^ (8 * (a % 8)))) {}
  (words.toList.filter (·.2 ≠ 0)).mergeSort (fun x y => x.1 ≤ y.1)

/-- The labelled `exit_group` of the runtime's abort routine of each kind
(`scc_rt_abort_<kind>_exit`). -/
def abortName : AbortKind → String
  | .overflow => "scc_rt_abort_overflow_exit"
  | .heap => "scc_rt_abort_heap_exit"
  | .stack => "scc_rt_abort_stack_exit"
  | .threads => "scc_rt_abort_threads_exit"
  | .writeErr => "scc_rt_abort_write_exit"

/-- **A realistic layout for the emitted text `asm`**: code at `codeLo`
(`codeSize` bytes), `.rodata` from `roLo` (its labels as symbols; the
loader builds its image), the other data sections from `dataLo`, the heap
arena (`scc_rt_heap`) at `heapLo`, the stack pool (`scc_rt_stacks`) at
`poolLo` and the pinned region (`scc_rt_pinned`) at `pinnedLo`, with the
sizes of their `.zero`. `resolve` gives code labels
(the target's, under any layout with the same code base). The second
component lists what the walk could not handle. -/
def layoutOf (asm : String) (codeLo codeSize roLo dataLo heapLo poolLo pinnedLo : Nat)
    (resolve : String → Option Nat) : Layout × List String :=
  let w := (asm.splitOn "\n").foldl
    (walkLine "scc_rt_heap" "scc_rt_stacks" "scc_rt_pinned" heapLo poolLo pinnedLo resolve)
    { cur := dataLo, roCur := roLo }
  ({ code := ⟨codeLo, codeSize⟩
     rodata := ⟨roLo, alignUp (w.roCur - roLo) 16⟩
     data := ⟨dataLo, alignUp (w.cur - dataLo) 16⟩
     heap := w.heap
     stackPool := w.pool
     pinned := w.pinned
     static _ := none
     image := imageWords w.bytes
     symbols := w.syms.reverse
     abortLbl := abortName }, w.errors.reverse)

/-! ## A deterministic run -/

variable {I : ISA} (K : Kernel.Abi I) (A : Arch)

/-- The result of a run. -/
structure RunResult (I : ISA) where
  /-- The events, in order. -/
  events : List Ev := []
  /-- Steps taken. -/
  steps : Nat := 0
  /-- Why the run stopped. -/
  stop : String := "out of fuel"
  /-- The last configuration. -/
  cfg : Config I × Kernel.KState

/-- The bytes of the `out` events, as text. -/
def RunResult.outText (r : RunResult I) : String :=
  String.ofList (r.events.filterMap fun | .out b => some (Char.ofNat b.val) | _ => none)

/-- The events other than `out`. -/
def RunResult.other (r : RunResult I) : List String :=
  r.events.filterMap fun
    | .out _ => none
    | .exit v => some s!"exit {v.val}"
    | .abort k => some s!"abort {k.idx}"
    | .writeErr => some "writeErr"
    | .cloneErr => some "cloneErr"

/-- Shared messages in the range `g` (`InLayout` forbids shared writes
outside `.data`, the heap and the pinned region; the stack pool is private
memory only). -/
def msgsIn (c : Config I × Kernel.KState) (g : Range) : Nat :=
  (c.1.mem.msgs.toList.filter fun m => g.lo ≤ m.loc.addr.toNat ∧ m.loc.addr.toNat < g.lo + g.size).length

/-- The marks the run uses: the transfer sites and the abort sites; and
whether the kernel refuses every `write` to fd 1 (`-EPIPE`), to exercise the
runtime's write abort. -/
structure RunMarks where
  take : Option Nat
  release : Option Nat
  abortAt : AbortKind → Option Nat
  refuseOut : Bool := false

/-- The kernel's byte read of a `write` taking the newest write the thread
may read (the highest `rd` that works; `rd` indexes the readable writes, of
which there are at most as many as messages, plus the initial one). -/
def writeByte (tid : Nat) (c : Config I × Kernel.KState) : Option (List Ev × (Config I × Kernel.KState)) :=
  ((List.range (c.1.mem.msgs.size + 2)).reverse.findSome? fun rd => Kernel.sysStep K A tid c (.byte rd))

/-- One step of thread `tid`: the events and the next configuration, or
why there is none. -/
def stepOf (pcf : I.State → Nat) (μ : RunMarks) (tid : Nat) (c : Config I × Kernel.KState) :
    Except String (List Ev × (Config I × Kernel.KState)) :=
  match c.1.threads[tid]? with
  | none => .error s!"t{tid}: no thread"
  | some t =>
    let pc := pcf t.st
    let at_ := s!"t{tid} pc={pc}"
    if Kernel.faultAt K c tid then .error s!"fault (kernel model) {at_}"
    else if Kernel.rootUnmapped K c tid then
      .error s!"fault (unmapped access) {at_}: {repr ((I.exec t.st).bind Kernel.rootAccess)}"
    else if μ.take = some pc then
      match Kernel.takeStep K tid c with
      | some c' => .ok ([], c')
      | none => .error s!"stuck at the take site {at_} range {repr (Kernel.siteRange K t.st)}"
    else if μ.release = some pc then
      match Kernel.releaseStep K tid c with
      | some c' => .ok ([], c')
      | none => .error s!"stuck at the release site {at_} range {repr (Kernel.siteRange K t.st)}"
    else if K.atSys t.st then
      let none' (what : String) : Except String (List Ev × (Config I × Kernel.KState)) :=
        .error s!"no kernel step: {what} {at_}"
      match Kernel.callOf K t with
      | some (.clone stack tls) =>
        match c.2.dormants with
        | j :: _ =>
          match Kernel.spawnStep K tid c j (BitVec.ofNat 64 (1000 + j)) with
          | some c' => .ok ([], c')
          | none => none' s!"clone({stack}, {tls})"
        | [] => none' "clone with no dormant slot"
      | some (.write fd buf n) =>
        let r := if μ.refuseOut && fd = 1 then Kernel.sysStep K A tid c (.ret (Kernel.neg 32))
          else if c.2.wr tid < n then writeByte K A tid c
          else Kernel.sysStep K A tid c (.ret (BitVec.ofNat 64 n))
        match r with
        | some x => .ok x
        | none => none' s!"write({fd}, {buf}, {n})"
      | some (.exitGroup v) =>
        if v % 256 = Kernel.abortStatus then
          match [AbortKind.overflow, .heap, .stack, .threads, .writeErr].find? (μ.abortAt · = some pc) with
          | some k =>
            match Kernel.sysStep K A tid c (.abort k) with
            | some x => .ok x
            | none => none' "exit_group(101)"
          | none => .error s!"exit_group({v}) at no abort label {at_}"
        else
          match Kernel.sysStep K A tid c (.ret 0) with
          | some x => .ok x
          | none => none' s!"exit_group({v})"
      | some call =>
        match Kernel.sysStep K A tid c (.ret 0) with
        | some x => .ok x
        | none => none' (reprStr call)
      | none => none' "unsupported call"
    else
      match stepThread A c.1 tid with
      | none => .error s!"halted {at_}"
      | some os =>
        match (os.filterMap fun | .ok o => some o | .error _ => none).getLast? with
        | some o => .ok ([], (c.1.withThread tid o.thread o.mem, c.2))
        | none => .error s!"fault (instruction) {at_}: {(os.filterMap fun | .error m => some m | .ok _ => none).headD ""}"

/-- **The deterministic run**: at most `fuel` steps, the running threads
taking turns from `tid`. -/
def run (pcf : I.State → Nat) (μ : RunMarks) : Nat → Nat → RunResult I → RunResult I
  | 0, _, r => r
  | fuel + 1, tid, r =>
    let c := r.cfg
    if c.2.exited.isSome then { r with stop := "exited" } else
    let n := c.1.threads.size
    match (List.range n).map (fun i => (tid + i) % n) |>.find? (c.2.runs ·) with
    | none => { r with stop := "no running thread" }
    | some t =>
      match stepOf K A pcf μ t c with
      | .ok (es, c') => run pcf μ fuel (t + 1) { r with events := r.events ++ es, steps := r.steps + 1, cfg := c' }
      | .error m => { r with stop := m }

/-- `run` that stops before the first step at whose configuration `stop`
holds (with `stop` = `"condition"`). -/
def runUntil (pcf : I.State → Nat) (μ : RunMarks) (cond : Config I × Kernel.KState → Bool) :
    Nat → Nat → RunResult I → RunResult I
  | 0, _, r => r
  | fuel + 1, tid, r =>
    let c := r.cfg
    if cond c then { r with stop := "condition" } else
    if c.2.exited.isSome then { r with stop := "exited" } else
    let n := c.1.threads.size
    match (List.range n).map (fun i => (tid + i) % n) |>.find? (c.2.runs ·) with
    | none => { r with stop := "no running thread" }
    | some t =>
      match stepOf K A pcf μ t c with
      | .ok (es, c') => runUntil pcf μ cond fuel (t + 1) { r with events := r.events ++ es, steps := r.steps + 1, cfg := c' }
      | .error m => { r with stop := m }

/-- The model's code marks of the run marks. -/
def RunMarks.marks (μ : RunMarks) : Marks where
  site | .take => μ.take | .release => μ.release
  abortAt := μ.abortAt

/-- Kraken's `certifyWith` (no cache), stepping with `CertSem.step cs`:
whether thread `t` certifies, the writes it promised on the way, whether
the bound was hit, and the faults. -/
def certifySem (cs : CertSem I) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) : CertResult I :=
  (go tid fuel ({}, {}) (t, mem, [], false)).2
where
  go (tid : Nat) : Nat → Std.HashSet (Thread I × Memory) × CertResult I →
      Thread I × Memory × List (Msg × View) × Bool → Std.HashSet (Thread I × Memory) × CertResult I
    | n, (visited, acc), (t, mem, ws, done) =>
      if visited.contains (t, mem) then (visited, acc) else
      let visited := visited.insert (t, mem)
      if t.hasDeadPromise mem then (visited, acc) else
      let (acc, done) :=
        if !done && t.prom.isEmpty then ({ acc with certified := true, writes := acc.writes ++ ws }, true)
        else (acc, done)
      if t.halted then (visited, acc)
      else
        match n with
        | 0 => (visited, { acc with boundHit := true })
        | n + 1 =>
          match cs.step A t tid mem with
          | none => (visited, acc)
          | some outs =>
            let (next, acc) := outs.foldl (init := ([], acc)) fun (next, acc) o =>
              match o with
              | .error m => (next, { acc with faults := acc.faults ++ [m] })
              | .ok o =>
                if done then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
                else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
            next.foldl (go tid n) (visited, acc)

/-- The writes thread `tid` of `c` may promise now (each the address and
value of a certified write it can still place, `certifiedPromisesWith`'s
filter), whether the bound was hit, under the certification semantics
`cs`. -/
def promisable (cs : CertSem I) (c : Config I) (tid : Nat) (fuel : Nat) : Option (List (Nat × Nat) × Bool) :=
  (c.threads[tid]?).map fun t =>
    let r := certifySem A cs t tid c.mem fuel
    (((r.writes.filter fun (_, ν) => ν ≤ c.mem.last).map fun (m, _) => (m.loc.addr.toNat, m.val.toNat)).eraseDups,
      r.boundHit)

/-- The initial value of the shared 8-byte word at `a`, if the memory's
initial image has one and no message has written it. -/
def sharedWord (c : Config I) (a : Nat) : Option Nat :=
  if c.mem.msgs.toList.any (fun m => m.loc.addr.toNat = a) then none else
  (c.mem.init.find? fun p => p.1.addr.toNat = a && p.1.bytes = 8).map (·.2.toNat)

end Scc.Sem.Test
