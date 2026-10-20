/-
**Part 10: concrete instance of
`Treiber2X.x64_treiber2_envG_verbatim`**: the `.kl` runner's own executable
for `treiber2.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `treiber2CodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `treiber2ImageV` laid out by `treiber2LayoutV` (text at
  `0x100000`, one byte per instruction, the symbols at `0x1000000` (`top`),
  `0x1000100` (`n1`) and `0x1000200` (`n2`)), both threads from `worker` to
  `done`, thread `0` with `%rbx = n1`, thread `1` with `%rbx = n2`, both with
  empty private memory. (Not compared: the runner's `decls` and
  initial-memory locations; the theorem assumes no declarations and an
  8-byte `top` at `0`.)
- `x64_treiber2_envG_verbatim_concrete`: the theorem at that layout and those
  threads; every hypothesis by `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.Treiber2X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.Treiber2X Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `treiber2.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x10000c`: the 12 instructions), the
padding up to `top` at `0x1000000`, and the 256-byte slots of `top` and `n1`. -/
def treiber2SizesV : List Nat :=
  [0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x10000c, 0, 0x100, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def treiber2LayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => treiber2SizesV[i]?.getD 0 }

instance treiber2ValidV : Executable.ValidLayout (treiber2LayoutV treiber2ImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: the image, pc at `worker`
(`0x100000`), end at `done` (`0x10000c`), `%rbx = n1`, empty private memory,
no declarations. -/
def treiber2P0 : X64.State where
  exe := treiber2LayoutV treiber2ImageV
  endPc := 0x100000 + 12
  st := ({ ({} : MachineData) with regs := (({} : MachineData).regs.set64 .rbx 0x1000100) }, 0x100000)

/-- Thread `1`: as thread `0`, with `%rbx = n2`. -/
def treiber2P1 : X64.State where
  exe := treiber2LayoutV treiber2ImageV
  endPc := 0x100000 + 12
  st := ({ ({} : MachineData) with regs := (({} : MachineData).regs.set64 .rbx 0x1000200) }, 0x100000)

/-- The initial memory: `top`, `n1`, `n2` all `0` (8-byte words). -/
def treiber2InitMemV : List (Loc × Val) := [(⟨0x1000000, 8⟩, 0), (⟨0x1000100, 8⟩, 0), (⟨0x1000200, 8⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def treiber2Kl : String := include_str "../../../Examples/LockFree/X64/treiber2.kl"

/-- The `code` block of the `.kl` parses to `treiber2CodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiber2CodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches treiber2Kl

/-- The runner's threads run `treiber2P0`'s and `treiber2P1`'s executable,
pc, end, registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 treiber2P0 && same t1 treiber2P1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches treiber2Kl

/-! ## The instance -/

section
attribute [local instance] treiber2LayoutV

/-- A label's address from its position in the image. -/
theorem labT2_at {x : Label} (i : Nat) (hd : treiber2ImageV.drop i = Program.fromLabel treiber2ImageV x := by decide)
    (hne : Program.fromLabel treiber2ImageV x ≠ [] := by decide) :
    labT2 x = (treiber2LayoutV treiber2ImageV).addrOf i :=
  Program.label_addrOf_drop treiber2ImageV_wf.nodup hd hne

theorem symT2_top : symT2 "top" = 0x1000000 := by
  show (labT2 "top").toBitVec = _; rw [labT2_at 17]; decide
theorem symT2_n1 : symT2 "n1" = 0x1000100 := by
  show (labT2 "n1").toBitVec = _; rw [labT2_at 19]; decide
theorem symT2_n2 : symT2 "n2" = 0x1000200 := by
  show (labT2 "n2").toBitVec = _; rw [labT2_at 21]; decide

theorem treiber2P0_start : StartWV (symT2 "n1") treiber2P0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT2 "worker"; rw [labT2_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labT2 "done"; rw [labT2_at 15]; decide,
    by rw [symT2_n1]; simp [treiber2P0, Reg64s.get64, Reg64s.set64], fun _ => by simp [treiber2P0]⟩

theorem treiber2P1_start : StartWV (symT2 "n2") treiber2P1 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT2 "worker"; rw [labT2_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labT2 "done"; rw [labT2_at 15]; decide,
    by rw [symT2_n2]; simp [treiber2P1, Reg64s.get64, Reg64s.set64], fun _ => by simp [treiber2P1]⟩

end

/-- **The two-thread Treiber stack, `treiber2.kl`'s code verbatim, in the
runner's executable**: in every final configuration under `Arch.tso` the two
threads popped the two nodes (`r12`). -/
theorem x64_treiber2_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [treiber2P0, treiber2P1] treiber2InitMemV) c)
    (hf : c.final = true) :
    ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.get64 .r12 = 0x1000100 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000200) ∨
        (th0.st.st.1.regs.get64 .r12 = 0x1000200 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100)) := by
  have h := x64_treiber2_envG_verbatim (layout := treiber2LayoutV)
    (by rw [symT2_top, symT2_n1]; decide) (by rw [symT2_top, symT2_n2]; decide)
    (by rw [symT2_n1, symT2_n2]; decide) (by rw [symT2_n1]; decide) (by rw [symT2_n2]; decide)
    treiber2P0_start treiber2P1_start (by rw [symT2_top]; simp only [Config.init_mem]; decide) hc hf
  rwa [symT2_n1, symT2_n2] at h

end Kraken.Promising.X64.EnvG.Treiber2X.Concrete

#print axioms Kraken.Promising.X64.EnvG.Treiber2X.Concrete.x64_treiber2_envG_verbatim_concrete
