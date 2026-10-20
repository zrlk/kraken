/-
**Concrete instance of `TreiberAbs.x64_treiber_pp_envG_verbatim`**: the `.kl`
runner's own executable for `treiber_pp.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `treiberCodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `treiberImageV` laid out by `treiberLayoutV` (text at
  `0x100000`, one byte per instruction, the symbols at `0x1000000` (`top`)
  and `0x1000100` (`n1`)), thread `0` from `pusher` to `pdone` with
  `%rdi = top`, `%rbx = n1`, thread `1` from `popper` to `qdone` with
  `%rdi = top`, both with empty private memory. (Not compared: the runner's
  `decls` and initial-memory locations; the theorem assumes no declarations
  and an 8-byte `top` at `0`, as `x64_treiber_pp_envG`.)
- `x64_treiber_pp_envG_verbatim_concrete`: the theorem at that layout and
  those threads; every hypothesis by `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `treiber_pp.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x100010`: the pusher's 6
instructions, `pdone: nop`, the popper's 9), the padding up to `top` at
`0x1000000`, and the 256-byte slot of `top` up to `n1`. -/
def treiberSizesV : List Nat :=
  [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x100010, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def treiberLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => treiberSizesV[i]?.getD 0 }

instance treiberValidV : Executable.ValidLayout (treiberLayoutV treiberImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The pusher as the runner prepares it: the image, pc at `pusher`
(`0x100000`), end at `pdone` (`0x100006`), `%rdi = top`, `%rbx = n1`, empty
private memory, no declarations. -/
def treiberP0 : X64.State where
  exe := treiberLayoutV treiberImageV
  endPc := 0x100000 + 6
  st := ({ ({} : MachineData) with
    regs := ((({} : MachineData).regs.set64 .rdi 0x1000000).set64 .rbx 0x1000100) }, 0x100000)

/-- The popper as the runner prepares it: pc at `popper` (`0x100007`), end at
`qdone` (`0x100010`), `%rdi = top`. -/
def treiberP1 : X64.State where
  exe := treiberLayoutV treiberImageV
  endPc := 0x100000 + 16
  st := ({ ({} : MachineData) with regs := (({} : MachineData).regs.set64 .rdi 0x1000000) }, 0x100000 + 7)

/-- The initial memory: `top = 0` (an 8-byte word), `n1`'s data word `0`. -/
def treiberInitMemV : List (Loc × Val) := [(⟨0x1000000, 8⟩, 0), (⟨0x1000100, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def treiberKl : String := include_str "../../../Examples/LockFree/X64/treiber_pp.kl"

/-- The `code` block of the `.kl` parses to `treiberCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiberCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches treiberKl

/-- The runner's threads run `treiberP0`'s and `treiberP1`'s executable, pc,
end, registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 treiberP0 && same t1 treiberP1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches treiberKl

/-! ## The instance -/

section
attribute [local instance] treiberLayoutV

/-- A label's address from its position in the image. -/
theorem labT_at {x : Label} (i : Nat) (hd : treiberImageV.drop i = Program.fromLabel treiberImageV x := by decide)
    (hne : Program.fromLabel treiberImageV x ≠ [] := by decide) : labT x = (treiberLayoutV treiberImageV).addrOf i :=
  Program.label_addrOf_drop treiberImageV_wf.nodup hd hne

theorem symT_top : symT "top" = 0x1000000 := by
  show (labT "top").toBitVec = _; rw [labT_at 22]; decide
theorem symT_n1 : symT "n1" = 0x1000100 := by
  show (labT "n1").toBitVec = _; rw [labT_at 24]; decide

theorem treiberP0_start : StartPushV treiberP0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labT "pusher"; rw [labT_at 0]; decide,
    by show (0x100000 + 6 : Int64) = labT "pdone"; rw [labT_at 8]; decide,
    by rw [symT_top]; simp [treiberP0, Reg64s.get64, Reg64s.set64],
    by rw [symT_n1]; simp [treiberP0, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem treiberP1_start : StartPopV treiberP1 :=
  ⟨rfl, rfl, by show (0x100000 + 7 : Int64) = labT "popper"; rw [labT_at 10]; decide,
    by show (0x100000 + 16 : Int64) = labT "qdone"; rw [labT_at 20]; decide,
    by rw [symT_top]; simp [treiberP1, Reg64s.get64, Reg64s.set64], fun _ => by simp [treiberP1]⟩

end

/-- **Treiber push/pop, `treiber_pp.kl`'s code verbatim, in the runner's
executable**: in every final configuration under `Arch.tso` the popper holds
`n1` in `%r10` and its data `1` in `%r11d`. -/
theorem x64_treiber_pp_envG_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [treiberP0, treiberP1] treiberInitMemV) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = 0x1000100 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 := by
  have h := x64_treiber_pp_envG_verbatim (layout := treiberLayoutV) (by rw [symT_top, symT_n1]; decide)
    treiberP0_start treiberP1_start (by rw [symT_top]; simp only [Config.init_mem]; decide) hc hf
  rwa [symT_n1] at h

end Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.Concrete.x64_treiber_pp_envG_verbatim_concrete
