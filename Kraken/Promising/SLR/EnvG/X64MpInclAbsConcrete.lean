/-
**Concrete instance of `MpInclAbs.x64_mp_incl_envGV_verbatim`**: the `.kl`
runner's own executable for `mp_incl.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `mpInclCodeV`.
- `runnerMatches`: the runner's prepared threads (`Kraken.Litmus.X64.prepareProgram`)
  run exactly `mpInclImageV` laid out by `mpInclLayoutV` (text at
  `0x100000`, one byte per instruction, the symbols at `0x1000000` (`d`) and
  `0x1000100` (`f`)), thread `0` from `writer` to `wdone`, thread `1` from
  `reader` to `rdone`, both with `%rdi = f`, `%rsi = d` and empty private
  memory. (Not compared: the runner's `decls` and initial-memory locations;
  the theorem assumes no declarations and a 4-byte `f` at `0`.)
- `x64_mp_incl_envGV_verbatim_concrete`: the theorem at that layout and
  those threads; every hypothesis by `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64MpInclAbsPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MpInclAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout -/

/-- The cell sizes of the runner's executable for `mp_incl.kl`: labels 0,
instructions 1 (text from `0x100000` to `0x100009`: the writer's 3
instructions, `wdone: nop`, the reader's 5), the padding up to `d` at
`0x1000000`, and the 256-byte slot of `d` up to `f`. -/
def mpInclSizesV : List Nat :=
  [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x100009, 0, 0x100, 0]

/-- The runner's layout of the image. -/
@[reducible] def mpInclLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => mpInclSizesV[i]?.getD 0 }

instance mpInclValidV : Executable.ValidLayout (mpInclLayoutV mpInclImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- A thread as the runner prepares it: the image, pc `pc`, end `endPc`,
`%rdi = f`, `%rsi = d`, empty private memory, no declarations. -/
def mpInclThreadV (pc endPc : Int64) : X64.State where
  exe := mpInclLayoutV mpInclImageV
  endPc := endPc
  st := ({ ({} : MachineData) with
    regs := ((({} : MachineData).regs.set64 .rdi 0x1000100).set64 .rsi 0x1000000) }, pc)

/-- The writer: from `writer` (`0x100000`) to `wdone` (`0x100003`). -/
def mpInclW0 : X64.State := mpInclThreadV 0x100000 (0x100000 + 3)

/-- The reader: from `reader` (`0x100004`) to `rdone` (`0x100009`). -/
def mpInclR1 : X64.State := mpInclThreadV (0x100000 + 4) (0x100000 + 9)

/-- The initial memory: `d = 0`, `f = 0` (4-byte words). -/
def mpInclInitMemV : List (Loc × Val) := [(⟨0x1000000, 4⟩, 0), (⟨0x1000100, 4⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def mpInclKl : String := include_str "../../../Examples/LockFree/X64/mp_incl.kl"

/-- The `code` block of the `.kl` parses to `mpInclCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == mpInclCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches mpInclKl

/-- The runner's threads run `mpInclW0`'s and `mpInclR1`'s executable, pc,
end, registers and private memory. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 mpInclW0 && same t1 mpInclR1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatches mpInclKl

/-! ## The instance -/

section
attribute [local instance] mpInclLayoutV

/-- A label's address from its position in the image. -/
theorem labM_at {x : Label} (i : Nat) (hd : mpInclImageV.drop i = Program.fromLabel mpInclImageV x := by decide)
    (hne : Program.fromLabel mpInclImageV x ≠ [] := by decide) : labM x = (mpInclLayoutV mpInclImageV).addrOf i :=
  Program.label_addrOf_drop mpInclImageV_wf.nodup hd hne

theorem symM_d : symM "d" = 0x1000000 := by
  show (labM "d").toBitVec = _; rw [labM_at 14]; decide
theorem symM_f : symM "f" = 0x1000100 := by
  show (labM "f").toBitVec = _; rw [labM_at 16]; decide

theorem mpInclW0_start : StartWM mpInclW0 :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labM "writer"; rw [labM_at 0]; decide,
    by show (0x100000 + 3 : Int64) = labM "wdone"; rw [labM_at 4]; decide,
    by rw [symM_f]; simp [mpInclW0, mpInclThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symM_d]; simp [mpInclW0, mpInclThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

theorem mpInclR1_start : StartRM mpInclR1 :=
  ⟨rfl, rfl, by show (0x100000 + 4 : Int64) = labM "reader"; rw [labM_at 6]; decide,
    by show (0x100000 + 9 : Int64) = labM "rdone"; rw [labM_at 12]; decide,
    by rw [symM_f]; simp [mpInclR1, mpInclThreadV, Reg64s.get64, Reg64s.set64],
    by rw [symM_d]; simp [mpInclR1, mpInclThreadV, Reg64s.get64, Reg64s.set64], Split.empty _⟩

end

/-- **MP with an unlocked `incl`, `mp_incl.kl`'s code verbatim, in the
runner's executable**: in every final configuration under `Arch.tso` the
reader's `ebx` is `42`, `[d] = 42` and `[f] = 1`. -/
theorem x64_mp_incl_envGV_verbatim_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [mpInclW0, mpInclR1] mpInclInitMemV) c)
    (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨0x1000000, 4⟩ = 42#128 ∧ c.mem.finalVal ⟨0x1000100, 4⟩ = 1#128 := by
  have h := x64_mp_incl_envGV_verbatim (layout := mpInclLayoutV) (by rw [symM_f, symM_d]; decide)
    mpInclW0_start mpInclR1_start (by rw [symM_f]; simp only [Config.init_mem]; decide) hc hf
  rwa [symM_d, symM_f] at h

end Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.Concrete.x64_mp_incl_envGV_verbatim_concrete
