/-
**Msqueue3 part 6: concrete instance of
`MsQueue3X.x64_msqueue3_envG_verbatim`**: the `.kl` runner's own executable
for `msqueue3.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `msq3CodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `msq3ImageV` laid out by `msq3LayoutV` (text at `0x100000`,
  one byte per instruction, the symbols at `0x1000000` (`s`), `0x1000100`
  (`n1`), `0x1000200` (`n2`), `0x1000300` (`head`), `0x1000400` (`tail`)),
  thread `0` from `enqueuer` to `edone`, threads `1` and `2` from `dequeuer`
  to `ddone`, all with zeroed registers and empty private memory.
- `initMemMatches`: the runner's initial memory has `msq3InitMemV`'s
  addresses and values in order (`s = n1 = n2 = 0`, `head = tail = s`). The
  runner records them unsized (`Loc.bytes = 0`); the theorem reads them as
  the 8-byte words the code accesses (as `X64Treiber2Concrete` does for
  `top`; the model's mixed-size gap).
- `x64_msqueue3_envG_verbatim_concrete`: the theorem at that layout, those
  threads and that memory; every hypothesis by `decide`/`rfl`/`simp`.
  (Not compared: the runner's `decls`; the theorem assumes none.)
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX Kraken.Promising.X64.EnvG.MsQueue3X Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `msqueue3.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x100027`: the 39 instructions), the
padding up to `s` at `0x1000000`, and the 256-byte slots of `s`, `n1`, `n2`,
`head`. -/
def msq3SizesV : List Nat :=
  (msq3CodeV.map fun d => match d with | .label _ => 0 | _ => 1) ++
    [0x1000000 - 0x100027, 0, 0x100, 0, 0x100, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def msq3LayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => msq3SizesV[i]?.getD 0 }

instance msq3ValidV : Executable.ValidLayout (msq3LayoutV msq3ImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: the image, pc at `enqueuer`
(`0x100000`), end at `edone` (`0x100014`), zeroed registers, empty private
memory, no declarations. -/
def msq3P0 : X64.State where
  exe := msq3LayoutV msq3ImageV
  endPc := 0x100000 + 20
  st := ({}, 0x100000)

/-- Threads `1` and `2`: pc at `dequeuer` (`0x100014`), end at `ddone`
(`0x100027`). -/
def msq3PD : X64.State where
  exe := msq3LayoutV msq3ImageV
  endPc := 0x100000 + 39
  st := ({}, 0x100000 + 20)

/-- The initial memory: `s`, `n1`, `n2` zero, `head` and `tail` at `s`
(8-byte words). -/
def msq3InitMemV : List (Loc × Val) :=
  [(⟨0x1000000, 8⟩, 0), (⟨0x1000100, 8⟩, 0), (⟨0x1000200, 8⟩, 0), (⟨0x1000300, 8⟩, 0x1000000),
    (⟨0x1000400, 8⟩, 0x1000000)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def msq3Kl : String := include_str "../../../Examples/LockFree/X64/msqueue3.kl"

/-- The `code` block of the `.kl` parses to `msq3CodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == msq3CodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches msq3Kl

/-- The runner's threads run `msq3P0`'s, `msq3PD`'s and `msq3PD`'s executable, pc, end,
registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1, t2] => same t0 msq3P0 && same t1 msq3PD && same t2 msq3PD
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches msq3Kl

/-- The runner's initial memory has `msq3InitMemV`'s addresses and values,
in order (the runner's locations are unsized). -/
def initMemMatches (src : String) : Bool :=
  let strip (L : List (Loc × Val)) : List (BitVec 64 × Val) := L.map fun p => (p.1.addr, p.2)
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => strip pr.config.mem.init == strip msq3InitMemV

/-- info: true -/
#guard_msgs in
#eval initMemMatches msq3Kl

/-! ## The instance -/

section
attribute [local instance] msq3LayoutV

/-- A label's address from its position in the image. -/
theorem labV3_at {x : Label} (i : Nat) (hd : msq3ImageV.drop i = Program.fromLabel msq3ImageV x := by decide)
    (hne : Program.fromLabel msq3ImageV x ≠ [] := by decide) :
    labV3 x = (msq3LayoutV msq3ImageV).addrOf i :=
  Program.label_addrOf_drop msq3ImageV_wf.nodup hd hne

set_option maxRecDepth 8000

theorem symV3_s : symV3 "s" = 0x1000000 := by
  show (labV3 "s").toBitVec = _; rw [labV3_at 49]; decide
theorem symV3_n1 : symV3 "n1" = 0x1000100 := by
  show (labV3 "n1").toBitVec = _; rw [labV3_at 51]; decide
theorem symV3_n2 : symV3 "n2" = 0x1000200 := by
  show (labV3 "n2").toBitVec = _; rw [labV3_at 53]; decide
theorem symV3_head : symV3 "head" = 0x1000300 := by
  show (labV3 "head").toBitVec = _; rw [labV3_at 55]; decide
theorem symV3_tail : symV3 "tail" = 0x1000400 := by
  show (labV3 "tail").toBitVec = _; rw [labV3_at 57]; decide

theorem msq3P0_start : StartEV3 msq3P0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labV3 "enqueuer"; rw [labV3_at 0]; decide,
    by show (0x100000 + 20 : Int64) = labV3 "edone"; rw [labV3_at 23]; decide,
    fun _ => by simp [msq3P0]⟩

theorem msq3PD_start : StartDV3 msq3PD :=
  ⟨rfl, rfl, by show (0x100000 + 20 : Int64) = labV3 "dequeuer"; rw [labV3_at 24]; decide,
    by show (0x100000 + 39 : Int64) = labV3 "ddone"; rw [labV3_at 47]; decide,
    fun _ => by simp [msq3PD]⟩

theorem msq3_initV : InitV (Config.init (I := isa) [msq3P0, msq3PD, msq3PD] msq3InitMemV).mem params3V := by
  simp only [params3V, symV3_s, symV3_n1, symV3_n2, symV3_head, symV3_tail]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

end

/-- **The two-node Michael–Scott queue, `msqueue3.kl`'s code verbatim, in the
runner's executable**: in every final configuration under `Arch.tso` the
dequeuers' results `(1:r12, 2:r12)` are among the five outcomes. -/
theorem x64_msqueue3_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [msq3P0, msq3PD, msq3PD] msq3InitMemV) c)
    (hf : c.final = true) :
    MsQueue3FinalX 0x1000100 0x1000200 c := by
  have h := x64_msqueue3_envG_verbatim (layout := msq3LayoutV)
    (by rw [symV3_head, symV3_tail]; decide) (by rw [symV3_head, symV3_s]; decide)
    (by rw [symV3_head, symV3_n1]; decide) (by rw [symV3_head, symV3_n2]; decide)
    (by rw [symV3_tail, symV3_s]; decide) (by rw [symV3_tail, symV3_n1]; decide)
    (by rw [symV3_tail, symV3_n2]; decide) (by rw [symV3_s, symV3_n1]; decide)
    (by rw [symV3_s, symV3_n2]; decide) (by rw [symV3_n1, symV3_n2]; decide)
    (by rw [symV3_n1]; decide) (by rw [symV3_n2]; decide)
    msq3P0_start msq3PD_start msq3PD_start msq3_initV hc hf
  rwa [symV3_n1, symV3_n2] at h

end Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.Concrete.x64_msqueue3_envG_verbatim_concrete
