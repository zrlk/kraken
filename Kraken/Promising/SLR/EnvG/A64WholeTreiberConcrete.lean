/-
**`treiber_pp.kl` whole image, part 3: a concrete
instance of `treiber_pp_envG_whole`** — the `.kl` runner's own executable
for `treiber_pp.kl`.

- `codeMatchesW`: the `.kl`'s `code` block parses to exactly
  `treiberImageA`, the executable of both threads.
- `runnerMatchesW`: the runner's prepared threads
  (`Kraken.Litmus.AArch64.prepareProgram`) run exactly `treiberImageA` laid
  out by `wLayoutT` (text at `0x100000`, each directive its `fakeSize`: the
  runner's layout), thread `0` from `pusher` (`0x100000`) to `pdone`
  (`0x100020`) with `X0 = top`, `X1 = n1`, `X9 = 1`, thread `1` from
  `popper` (`0x100024`) to `qdone` (`0x10004c`) with `X0 = top`, both with
  the runner's whole register file and empty private memory. (Not
  compared: the runner's `decls`; the theorem assumes no declarations.)
- `treiber_pp_envG_whole_concrete`: the theorem at that layout and those
  threads (`top = 0x1000`, `n1 = 0x1100`, as `ConcreteTreiber`); every
  hypothesis by `decide`/`rfl`/`simp`. No `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiberPublic
import Kraken.Promising.SLR.EnvG.ConcreteTreiber

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.ConcreteTreiber

/-! ## The runner's layout and threads -/

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayoutT : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiberImageA

instance wValidT : Executable.ValidLayout (wLayoutT treiberImageA) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The pusher as the runner prepares it: the image, from `pusher` to
`pdone`, `X0 = top`, `X1 = n1`, `X9 = 1`, empty private memory, no
declarations. -/
def pusherW0 : AArch64.State where
  exe := wLayoutT treiberImageA
  endPc := 0x100000 + 32
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X9 := 1 } }, 0x100000)

/-- The popper as the runner prepares it: the image, from `popper` to
`qdone`, `X0 = top`. -/
def popperW1 : AArch64.State where
  exe := wLayoutT treiberImageA
  endPc := 0x100000 + 76
  st := ({ regs := { X0 := 0x1000 } }, 0x100000 + 36)

/-! ## The `.kl` file runs these threads -/

/-- The `code` block of the `.kl` parses to `treiberImageA`. -/
def codeMatchesW (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiberImageA
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesW treiberPpKl

/-- The runner's threads run `pusherW0`'s and `popperW1`'s executable, pc,
end, registers and private memory. -/
def runnerMatchesW (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 pusherW0 && same t1 popperW1
    | _ => false

/-- info: true -/
#guard_msgs in
#eval runnerMatchesW treiberPpKl

/-! ## The instance -/

section
attribute [local instance] wLayoutT

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labT_at {x : Label} (i : Nat) (hd : treiberImageA.drop i = Program.fromLabel treiberImageA x := by decide)
    (hne : Program.fromLabel treiberImageA x ≠ [] := by decide) : labT x = (wLayoutT treiberImageA).addrOf i :=
  Program.label_addrOf_drop treiberImageA_wf.nodup hd hne

set_option maxRecDepth 8192 in
theorem pusherW0_start : StartPushW topAddr n1Addr pusherW0 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · show (0x100000 : Int64) = labT "pusher"; rw [labT_at 0]; decide
  · show (0x100000 + 32 : Int64) = labT "pdone"; rw [labT_at 10]; decide
  all_goals simp [pusherW0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr, n1Addr]

set_option maxRecDepth 8192 in
theorem popperW1_start : StartPopW topAddr popperW1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, ?_, fun a => ?_⟩
  · show (0x100000 + 36 : Int64) = labT "popper"; rw [labT_at 12]; decide
  · show (0x100000 + 76 : Int64) = labT "qdone"; rw [labT_at 23]; decide
  all_goals simp [popperW1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr]

end

/-- **`1:X10 = n1 ∧ 1:X11 = 1`** for `treiber_pp.kl` under `Arch.armv8`,
both threads running the runner's executable (the whole `code` block at
`0x100000`): concrete instance of `treiber_pp_envG_whole`. -/
theorem treiber_pp_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [pusherW0, popperW1] treiberInitMem) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n1Addr ∧ th.st.st.1.regs.X11.toBitVec = 1 :=
  treiber_pp_envG_whole wLayoutT topAddr n1Addr (by decide) pusherW0_start popperW1_start
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber

#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_whole_concrete
