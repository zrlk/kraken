/-
**`mp_relay3.kl` whole image, part 3: a concrete
instance of `mp_relay3_envG_whole`** — the `.kl` runner's own executable
for `mp_relay3.kl`.

- `codeMatchesW`: the `.kl`'s `code` block parses to exactly `relay3Img`,
  the executable of the three threads.
- `runnerMatchesW`: the runner's prepared threads
  (`Kraken.Litmus.AArch64.prepareProgram`) run exactly `relay3Img` laid out
  by `wLayoutY` (text at `0x100000`, each directive its `fakeSize`: the
  runner's layout), thread `0` from `writer` (`0x100000`) to `wdone`
  (`0x100014`) with `X0 = f1`, `X1 = d`, thread `1` from `relay`
  (`0x100018`) to `rdone` (`0x100034`) with `X0 = f1`, `X1 = d`, `X2 = f2`,
  thread `2` from `reader` (`0x100038`) to `ddone` (`0x100048`) with
  `X0 = f2`, `X1 = d`, all with the runner's whole register file and empty
  private memory (`d = 0x1000`, `f1 = 0x1100`, `f2 = 0x1200`: the runner's
  placement). (Not compared: the runner's `decls`; the theorem assumes no
  declarations.)
- `mp_relay3_envG_whole_concrete`: the theorem at that layout and those
  threads; every hypothesis by `decide`/`rfl`/`simp`. No `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeRelayPublic
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-! ## The runner's layout and threads -/

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayoutY : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize relay3Img

instance wValidY : Executable.ValidLayout (wLayoutY relay3Img) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The data word's address (the runner's placement). -/
def dAddrY : BitVec 64 := 0x1000
/-- The first flag's address. -/
def f1AddrY : BitVec 64 := 0x1100
/-- The second flag's address. -/
def f2AddrY : BitVec 64 := 0x1200

/-- The initial memory: the three words at `0`. -/
def relay3InitMem : List (Loc × Val) := [(⟨dAddrY, 4⟩, 0), (⟨f1AddrY, 4⟩, 0), (⟨f2AddrY, 4⟩, 0)]

/-- The writer as the runner prepares it: the image, from `writer` to
`wdone`, `X0 = f1`, `X1 = d`, empty private memory, no declarations. -/
def writerW0 : AArch64.State where
  exe := wLayoutY relay3Img
  endPc := 0x100000 + 20
  st := ({ regs := { X0 := 0x1100, X1 := 0x1000 } }, 0x100000)

/-- The relay as the runner prepares it: from `relay` to `rdone`,
`X0 = f1`, `X1 = d`, `X2 = f2`. -/
def relayW1 : AArch64.State where
  exe := wLayoutY relay3Img
  endPc := 0x100000 + 52
  st := ({ regs := { X0 := 0x1100, X1 := 0x1000, X2 := 0x1200 } }, 0x100000 + 24)

/-- The reader as the runner prepares it: from `reader` to `ddone`,
`X0 = f2`, `X1 = d`. -/
def readerW2 : AArch64.State where
  exe := wLayoutY relay3Img
  endPc := 0x100000 + 72
  st := ({ regs := { X0 := 0x1200, X1 := 0x1000 } }, 0x100000 + 56)

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` file. -/
def relay3Kl : String := include_str "../../../Examples/LockFree/AArch64/mp_relay3.kl"

/-- The `code` block of the `.kl` parses to `relay3Img`. -/
def codeMatchesW (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == relay3Img
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesW relay3Kl

/-- The runner's threads run `writerW0`'s, `relayW1`'s and `readerW2`'s
executable, pc, end, registers and private memory. -/
def runnerMatchesW (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1, t2] => same t0 writerW0 && same t1 relayW1 && same t2 readerW2
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatchesW relay3Kl

/-! ## The instance -/

section
attribute [local instance] wLayoutY

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labY3_at {x : Label} (i : Nat) (hd : relay3Img.drop i = Program.fromLabel relay3Img x := by decide)
    (hne : Program.fromLabel relay3Img x ≠ [] := by decide) : labY3 x = (wLayoutY relay3Img).addrOf i :=
  Program.label_addrOf_drop relay3Img_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem writerW0_start : StartW3 f1AddrY dAddrY writerW0 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · show (0x100000 : Int64) = labY3 "writer"; rw [labY3_at 0]; decide
  · show (0x100000 + 20 : Int64) = labY3 "wdone"; rw [labY3_at 6]; decide
  all_goals simp [writerW0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, f1AddrY, dAddrY]

set_option maxRecDepth 8192 in
theorem relayW1_start : StartY3 f1AddrY f2AddrY dAddrY relayW1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · show (0x100000 + 24 : Int64) = labY3 "relay"; rw [labY3_at 8]; decide
  · show (0x100000 + 52 : Int64) = labY3 "rdone"; rw [labY3_at 16]; decide
  all_goals simp [relayW1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, f1AddrY, f2AddrY, dAddrY]

set_option maxRecDepth 8192 in
theorem readerW2_start : StartD3 f2AddrY dAddrY readerW2 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · show (0x100000 + 56 : Int64) = labY3 "reader"; rw [labY3_at 18]; decide
  · show (0x100000 + 72 : Int64) = labY3 "ddone"; rw [labY3_at 23]; decide
  all_goals simp [readerW2, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, f2AddrY, dAddrY]

end

/-- **`2:X4 = 43 ∧ [d] = 43`** for `mp_relay3.kl` under `Arch.armv8`, the
three threads running the runner's executable (the whole `code` block at
`0x100000`): concrete instance of `mp_relay3_envG_whole`. -/
theorem mp_relay3_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writerW0, relayW1, readerW2] relay3InitMem) c)
    (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨dAddrY, 4⟩ = 43#128 :=
  mp_relay3_envG_whole wLayoutY f1AddrY f2AddrY dAddrY ⟨by decide, by decide, by decide⟩ writerW0_start
    relayW1_start readerW2_start (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_whole_concrete
