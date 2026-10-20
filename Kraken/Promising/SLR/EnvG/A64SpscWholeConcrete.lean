/-
**Whole image, part 3: a concrete instance of
`a64_spsc_envG_whole`** — the `.kl` runner's own executable for
`spsc_queue.kl`.

- `codeMatchesW`: the `.kl`'s `code` block parses to exactly `spscImageA`,
  the executable of both threads.
- `runnerMatchesW`: the runner's prepared threads
  (`Kraken.Litmus.AArch64.prepareProgram`) run exactly `spscImageA` laid out
  by `wLayoutA` (text at `0x100000`, each directive its `fakeSize`: the
  runner's layout), thread `0` from `prod` (`0x100000`) to `pdone`
  (`0x10003c`), thread `1` from `cons` (`0x100040`) to `cdone`
  (`0x1000a0`), both with `X0 = buf`, `X1 = head`, `X2 = tail` and empty
  private memory. (Not compared: the runner's `decls`; the theorem assumes
  no declarations.)
- `a64_spsc_envG_whole_concrete`: the theorem at that layout and those
  threads (`buf = 0x1000`, `head = 0x1100`, `tail = 0x1200`, all initially
  `0`, as `A64SpscConcrete`); every hypothesis by `decide`/`rfl`/`simp`. No
  `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64SpscWholePublic
import Kraken.Promising.SLR.EnvG.A64SpscConcrete

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-! ## The runner's layout and threads -/

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayoutA : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize spscImageA

instance wValidA : Executable.ValidLayout (wLayoutA spscImageA) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- A thread as the runner prepares it: the image, pc `pc`, end `endPc`,
`X0 = buf`, `X1 = head`, `X2 = tail`, empty private memory, no
declarations. -/
def spscThreadW (pc endPc : Int64) : AArch64.State where
  exe := wLayoutA spscImageA
  endPc := endPc
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X2 := 0x1200 } }, pc)

/-- The producer: from `prod` to `pdone`. -/
def spscProdW0 : AArch64.State := spscThreadW 0x100000 (0x100000 + 60)

/-- The consumer: from `cons` to `cdone`. -/
def spscConsW1 : AArch64.State := spscThreadW (0x100000 + 64) (0x100000 + 160)

/-! ## The `.kl` file runs these threads -/

/-- The `code` block of the `.kl` parses to `spscImageA`. -/
def codeMatchesW (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == spscImageA
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesW spscKl

/-- The runner's threads run `spscProdW0`'s and `spscConsW1`'s executable,
pc, end, base registers and private memory. -/
def runnerMatchesW (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs.X0 == s.st.1.regs.X0 && t.st.st.1.regs.X1 == s.st.1.regs.X1 &&
      t.st.st.1.regs.X2 == s.st.1.regs.X2 && t.st.st.1.dmem == s.st.1.dmem
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 spscProdW0 && same t1 spscConsW1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatchesW spscKl

/-! ## The instance -/

section
attribute [local instance] wLayoutA

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labA_at {x : Label} (i : Nat) (hd : spscImageA.drop i = Program.fromLabel spscImageA x := by decide)
    (hne : Program.fromLabel spscImageA x ≠ [] := by decide) : labA x = (wLayoutA spscImageA).addrOf i :=
  Program.label_addrOf_drop spscImageA_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem spscProdW0_start : StartPW ⟨bufA, headA, tailA⟩ spscProdW0 := by
  refine ⟨rfl, rfl, ?_, ?_, ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩⟩
  · show (0x100000 : Int64) = labA "prod"; rw [labA_at 0]; decide
  · show (0x100000 + 60 : Int64) = labA "pdone"; rw [labA_at 17]; decide
  all_goals simp [spscProdW0, spscThreadW, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem spscConsW1_start : StartCW ⟨bufA, headA, tailA⟩ spscConsW1 := by
  refine ⟨rfl, rfl, ?_, ?_, ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩⟩
  · show (0x100000 + 64 : Int64) = labA "cons"; rw [labA_at 19]; decide
  · show (0x100000 + 160 : Int64) = labA "cdone"; rw [labA_at 47]; decide
  all_goals simp [spscConsW1, spscThreadW, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`forall (1:X10=1 /\ 1:X11=2 /\ 1:X12=3)`** for `spsc_queue.kl` under
`Arch.armv8`, both threads running the runner's executable (the whole
`code` block at `0x100000`): concrete instance of `a64_spsc_envG_whole`. -/
theorem a64_spsc_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [spscProdW0, spscConsW1] spscInitMemA) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  a64_spsc_envG_whole wLayoutA bufA headA tailA spscLocsA spscProdW0_start spscConsW1_start
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_whole_concrete
