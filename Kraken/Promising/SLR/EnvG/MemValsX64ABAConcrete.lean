/-
**Concrete instance of `VecABA.x64_treiber_aba_tagged_runner_faultFree`**
The `.kl` runner's own configuration for
`treiber_aba_tagged.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `abaCodeV`.
- `runnerMatches`: the runner's prepared configuration
  (`Kraken.Litmus.X64.prepareProgram`) is `Config.init [abaP0V, abaP1V]
  abaInitMemV` in everything the theorem reads: both threads run
  `abaImageV` laid out by `abaLayoutV` (text at `0x100000`, one byte per
  instruction, `head`, `A`, `B` at `0x1000000`, `0x1000100`, `0x1000200`),
  thread `0` from `p0` and thread `1` from `p1` to `done`, each on its
  64-byte private stack at `0x200000 + tid * 0x10000` (`rsp` at its top),
  with the runner's declarations (`head` 16 bytes, `A` and `B` 8 bytes); the
  initial memory is `head = {A, 0}`, `A = B`, `B = 0`.
- `x64_treiber_aba_tagged_runner_faultFree_concrete`: no reachable
  configuration has a faulting step.
-/
import Kraken.Promising.SLR.EnvG.MemValsX64ABA
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.VecABA.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.VecABA Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout and configuration -/

/-- The cell sizes of the runner's executable for `treiber_aba_tagged.kl`:
labels 0, instructions 1 (text from `0x100000` to `0x100031`), then the
padding up to `head` (`0x1000000`), `A` (`+ 0x100`) and `B` (`+ 0x200`). -/
def abaSizesV : List Nat :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0x1000000 - 0x100031, 0, 256, 0, 256, 0]

/-- The runner's layout of the image. -/
@[reducible] def abaLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => abaSizesV[i]?.getD 0 }

instance abaValidV : Executable.ValidLayout (abaLayoutV abaImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The runner's declarations: `head` 16 bytes (`__int128`), `A` and `B` 8
bytes (`uint64_t`). -/
def abaDeclsV : Decls :=
  { locs := [⟨0x1000000, 16⟩, ⟨0x1000100, 8⟩, ⟨0x1000200, 8⟩], unsizedDefault := false }

theorem abaDeclsV_sized : abaDeclsV.Sized := ⟨rfl, by decide⟩

/-- Thread `tid`'s stack bottom. -/
def abaStackV (tid : Nat) : BitVec 64 := BitVec.ofNat 64 (0x200000 + tid * 0x10000)

/-- A thread as the runner prepares it: the image, pc `pc`, end `done`
(`0x100031`), its 64-byte zeroed stack with `rsp` at the top, the runner's
declarations. -/
def abaThreadV (tid : Nat) (pc : Int64) : X64.State where
  exe := abaLayoutV abaImageV
  endPc := 0x100000 + 49
  st := ({ ({} : MachineData) with
      dmem := Mem.storeBytes ({} : MachineData).dmem (abaStackV tid) (List.replicate 64 0),
      regs := ({} : MachineData).regs.set64 .rsp (abaStackV tid + BitVec.ofNat 64 64) }, pc)
  decls := abaDeclsV

/-- Thread `0`: from `p0` (`0x100000`). -/
def abaP0V : X64.State := abaThreadV 0 0x100000

/-- Thread `1`: from `p1` (`0x10000d`). -/
def abaP1V : X64.State := abaThreadV 1 (0x100000 + 13)

/-- The initial memory: `head = {A, 0}`, `A = B`, `B = 0`. -/
def abaInitMemV : List (Loc × Val) :=
  [(⟨0x1000000, 16⟩, 0x1000100), (⟨0x1000100, 8⟩, 0x1000200), (⟨0x1000200, 8⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def abaKl : String := include_str "../../../Examples/LockFree/X64/treiber_aba_tagged.kl"

/-- The `code` block of the `.kl` parses to `abaCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == abaCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches abaKl

/-- The runner's configuration: threads `abaP0V` and `abaP1V` (executable,
pc, end, registers, vector registers, private memory, declarations, no
promise) and the initial memory `abaInitMemV` with no message. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.zmms == s.st.1.zmms && t.st.st.1.dmem == s.st.1.dmem &&
      t.st.decls == s.decls && t.prom.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => (match pr.config.threads.toList with
    | [t0, t1] => same t0 abaP0V && same t1 abaP1V
    | _ => false) && pr.config.mem.init == abaInitMemV && pr.config.mem.msgs.isEmpty

/-- info: true -/
#guard_msgs in
#eval runnerMatches abaKl

/-! ## The instance -/

section
attribute [local instance] abaLayoutV

set_option maxRecDepth 20000

/-- A label's address from its position in the image. -/
theorem labV_at {x : Label} (i : Nat) (hd : abaImageV.drop i = Program.fromLabel abaImageV x := by decide)
    (hne : Program.fromLabel abaImageV x ≠ [] := by decide) :
    labV x = (abaLayoutV abaImageV).addrOf i :=
  Program.label_addrOf_drop abaImageV_wf.nodup hd hne

theorem symV_head : symV "head" = 0x1000000 := by
  show (labV "head").toBitVec = _; rw [labV_at 57]; decide

theorem symV_A : symV "A" = 0x1000100 := by
  show (labV "A").toBitVec = _; rw [labV_at 59]; decide

theorem symV_B : symV "B" = 0x1000200 := by
  show (labV "B").toBitVec = _; rw [labV_at 61]; decide

/-- No stack byte lies in `[0x1000000, 0x2000000)`. -/
theorem stk_get_none {tid : Nat} (htid : tid < 2) {k : BitVec 64} (hk : 0x1000000 ≤ k.toNat) :
    (Mem.storeBytes ({} : MachineData).dmem (abaStackV tid) (List.replicate 64 0)).get? k = none := by
  rw [Mem.get?_storeBytes_of_not_mem]
  · simp
  · rw [mem_At_iff]
    rintro ⟨i, hi, rfl⟩
    simp only [List.length_replicate] at hi
    simp only [abaStackV, BitVec.toNat_add, BitVec.toNat_ofNat] at hk
    omega

/-- The runner's stack is split from the declared layout. -/
theorem stk_split {tid : Nat} (htid : tid < 2) :
    Split abaS (Mem.storeBytes ({} : MachineData).dmem (abaStackV tid) (List.replicate 64 0)) := by
  refine Split.of_get fun a n hm i hi => stk_get_none htid ?_
  simp only [abaS, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rw [symV_head, symV_A, symV_B] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] <;> omega

/-- The runner's start: the slot at `-16(%rsp)` mapped and aligned, `head`
off the stack. -/
theorem abaThreadV_start {tid : Nat} (htid : tid < 2) (lab : Label) (pc : Int64) (hpc : pc = labV lab) :
    StartV abaDeclsV lab (abaThreadV tid pc) := by
  have hrsp : (({} : MachineData).regs.set64 .rsp (abaStackV tid + BitVec.ofNat 64 64)).get64 .rsp +
      (-16 : Int64).toBitVec = abaStackV tid + BitVec.ofNat 64 48 := by
    rw [Reg64s.get64_set64]; simp only [↓reduceIte, BitVec.add_assoc]; rfl
  refine ⟨rfl, rfl, hpc, ?_, ?_, ?_, stk_get_none htid (by rw [symV_head]; decide)⟩
  · show (0x100000 + 49 : Int64) = labV "done"; rw [labV_at 55]; decide
  · simp only [abaThreadV]
    rw [hrsp]; unfold Mem.loadInt
    rw [loadBytes_storeBytes_off _ _ _ 48 16 (by simp) (by simp)]; rfl
  · simp only [abaThreadV]
    rw [hrsp]; rcases tid with _ | _ | _
    · decide
    · decide
    · omega

/-- **`treiber_aba_tagged.kl` never faults**, from the runner's exact
configuration (threads `abaP0V`, `abaP1V` on their stacks with the runner's
declarations `abaDeclsV`, initial memory `abaInitMemV`). -/
theorem x64_treiber_aba_tagged_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [abaP0V, abaP1V] abaInitMemV) :=
  x64_treiber_aba_tagged_runner_faultFree (layout := abaLayoutV) abaDeclsV_sized
    (by rw [symV_head]; decide)
    (by
      show abaDeclsV.AgreesOn [(symV "head", 16), (symV "A", 8), (symV "B", 8)]
      rw [symV_head, symV_A, symV_B]; decls_agrees_on)
    (abaThreadV_start (by decide) "p0" _ (by rw [labV_at 0]; decide))
    (abaThreadV_start (by decide) "p1" _ (by rw [labV_at 14]; decide))
    (stk_split (by decide)) (stk_split (by decide))
    (by
      show IV ⟨symV "head", symV "A", symV "B"⟩ _
      rw [symV_head, symV_A, symV_B]; simp only [Config.init_mem]
      exact ⟨by decide, by decide, by decide⟩)

end

end Kraken.Promising.X64.EnvG.VecABA.Concrete

#print axioms Kraken.Promising.X64.EnvG.VecABA.Concrete.x64_treiber_aba_tagged_runner_faultFree_concrete
