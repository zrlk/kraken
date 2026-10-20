/-
**Concrete instance of
`MsQueueX.x64_msqueue2_envG_verbatim`**: the `.kl` runner's own executable
for `msqueue2.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `msq2CodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `msq2ImageV` laid out by `msq2LayoutV` (text at `0x100000`,
  one byte per instruction, the symbols at `0x1000000` (`s`), `0x1000100`
  (`n1`), `0x1000200` (`n2`), `0x1000300` (`head`), `0x1000400` (`tail`)),
  thread `0` from `enqueuer` to `edone`, thread `1` from `dequeuer` to
  `ddone`, both with zeroed registers and empty private memory.
- `initMemMatches`: the runner's initial memory has `msq2InitMemV`'s
  addresses and values in order (`s = n1 = n2 = 0`, `head = tail = s`). The
  runner records them unsized (`Loc.bytes = 0`); the theorem reads them as
  the 8-byte words the code accesses (as `X64Treiber2Concrete` does for
  `top`; the model's mixed-size gap).
- `x64_msqueue2_envG_verbatim_concrete`: the theorem at that layout, those
  threads and that memory; every hypothesis by `decide`/`rfl`/`simp`.
  (Not compared: the runner's `decls`; the theorem assumes none.)
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.MsQueueX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `msqueue2.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x10002a`: the 42 instructions), the
padding up to `s` at `0x1000000`, and the 256-byte slots of `s`, `n1`, `n2`,
`head`. -/
def msq2SizesV : List Nat :=
  (msq2CodeV.map fun d => match d with | .label _ => 0 | _ => 1) ++
    [0x1000000 - 0x10002a, 0, 0x100, 0, 0x100, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def msq2LayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => msq2SizesV[i]?.getD 0 }

instance msq2ValidV : Executable.ValidLayout (msq2LayoutV msq2ImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: the image, pc at `enqueuer`
(`0x100000`), end at `edone` (`0x100014`), zeroed registers, empty private
memory, no declarations. -/
def msq2P0 : X64.State where
  exe := msq2LayoutV msq2ImageV
  endPc := 0x100000 + 20
  st := ({}, 0x100000)

/-- Thread `1`: pc at `dequeuer` (`0x100014`), end at `ddone`
(`0x10002a`). -/
def msq2P1 : X64.State where
  exe := msq2LayoutV msq2ImageV
  endPc := 0x100000 + 42
  st := ({}, 0x100000 + 20)

/-- The initial memory: `s`, `n1`, `n2` zero, `head` and `tail` at `s`
(8-byte words). -/
def msq2InitMemV : List (Loc × Val) :=
  [(⟨0x1000000, 8⟩, 0), (⟨0x1000100, 8⟩, 0), (⟨0x1000200, 8⟩, 0), (⟨0x1000300, 8⟩, 0x1000000),
    (⟨0x1000400, 8⟩, 0x1000000)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def msq2Kl : String := include_str "../../../Examples/LockFree/X64/msqueue2.kl"

/-- The `code` block of the `.kl` parses to `msq2CodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == msq2CodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches msq2Kl

/-- The runner's threads run `msq2P0`'s and `msq2P1`'s executable, pc, end,
registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 msq2P0 && same t1 msq2P1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches msq2Kl

/-- The runner's initial memory has `msq2InitMemV`'s addresses and values,
in order (the runner's locations are unsized). -/
def initMemMatches (src : String) : Bool :=
  let strip (L : List (Loc × Val)) : List (BitVec 64 × Val) := L.map fun p => (p.1.addr, p.2)
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => strip pr.config.mem.init == strip msq2InitMemV

/-- info: true -/
#guard_msgs in
#eval initMemMatches msq2Kl

/-! ## The instance -/

section
attribute [local instance] msq2LayoutV

/-- A label's address from its position in the image. -/
theorem labV_at {x : Label} (i : Nat) (hd : msq2ImageV.drop i = Program.fromLabel msq2ImageV x := by decide)
    (hne : Program.fromLabel msq2ImageV x ≠ [] := by decide) :
    labV x = (msq2LayoutV msq2ImageV).addrOf i :=
  Program.label_addrOf_drop msq2ImageV_wf.nodup hd hne

set_option maxRecDepth 8000

theorem symV_s : symV "s" = 0x1000000 := by
  show (labV "s").toBitVec = _; rw [labV_at 52]; decide
theorem symV_n1 : symV "n1" = 0x1000100 := by
  show (labV "n1").toBitVec = _; rw [labV_at 54]; decide
theorem symV_n2 : symV "n2" = 0x1000200 := by
  show (labV "n2").toBitVec = _; rw [labV_at 56]; decide
theorem symV_head : symV "head" = 0x1000300 := by
  show (labV "head").toBitVec = _; rw [labV_at 58]; decide
theorem symV_tail : symV "tail" = 0x1000400 := by
  show (labV "tail").toBitVec = _; rw [labV_at 60]; decide

theorem msq2P0_start : StartEV msq2P0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labV "enqueuer"; rw [labV_at 0]; decide,
    by show (0x100000 + 20 : Int64) = labV "edone"; rw [labV_at 23]; decide,
    fun _ => by simp [msq2P0]⟩

theorem msq2P1_start : StartDV msq2P1 :=
  ⟨rfl, rfl, by show (0x100000 + 20 : Int64) = labV "dequeuer"; rw [labV_at 24]; decide,
    by show (0x100000 + 42 : Int64) = labV "ddone"; rw [labV_at 50]; decide,
    by simp [msq2P1, Reg64s.get64], fun _ => by simp [msq2P1]⟩

theorem msq2_initV : InitV (Config.init (I := isa) [msq2P0, msq2P1] msq2InitMemV).mem paramsV := by
  simp only [paramsV, symV_s, symV_n1, symV_n2, symV_head, symV_tail]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

end

/-- **The two-node Michael–Scott queue, `msqueue2.kl`'s code verbatim, in the
runner's executable**: in every final configuration under `Arch.tso` the
dequeuer got `n1` (`r12`), then `n2` (`r13`). -/
theorem x64_msqueue2_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [msq2P0, msq2P1] msq2InitMemV) c)
    (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100 ∧
      th1.st.st.1.regs.get64 .r13 = 0x1000200 := by
  have h := x64_msqueue2_envG_verbatim (layout := msq2LayoutV)
    (by rw [symV_head, symV_tail]; decide) (by rw [symV_head, symV_s]; decide)
    (by rw [symV_head, symV_n1]; decide) (by rw [symV_head, symV_n2]; decide)
    (by rw [symV_tail, symV_s]; decide) (by rw [symV_tail, symV_n1]; decide)
    (by rw [symV_tail, symV_n2]; decide) (by rw [symV_s, symV_n1]; decide)
    (by rw [symV_s, symV_n2]; decide) (by rw [symV_n1, symV_n2]; decide)
    (by rw [symV_n1]; decide) (by rw [symV_n2]; decide)
    msq2P0_start msq2P1_start msq2_initV hc hf
  rwa [symV_n1, symV_n2] at h

end Kraken.Promising.X64.EnvG.MsQueueX.Concrete

#print axioms Kraken.Promising.X64.EnvG.MsQueueX.Concrete.x64_msqueue2_envG_verbatim_concrete
