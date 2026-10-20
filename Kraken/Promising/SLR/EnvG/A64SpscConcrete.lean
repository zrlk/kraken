/-
**Part 8: a concrete instance of
`a64_spsc_envG`** (the `ConcreteTreiber2Data` pattern): non-vacuity of its
start hypotheses (`StartA` for both threads) and of `SpscLocs`, and the
`.kl` check `codeMatches`.

The symbols are laid out as the `.kl` runner lays them out, `0x100` bytes
apart in the order of the init block: `buf = 0x1000` (slot `1` at
`0x1008`), `head = 0x1100`, `tail = 0x1200`, all initially `0`
(`spscInitMemA`). The producer's text is at `0x100000`, the consumer's at
`0x200000` (`Layout.ofSize … Directive.fakeSize`). No `native_decide`.

`codeMatches`: the `.kl`'s `code` block parses to
`spscProdA ++ spscNop ++ spscConsA` — the per-thread images of
`a64_spsc_envG` are exactly the block's parts (the deviation documented
there).
-/
import Kraken.Promising.SLR.EnvG.A64SpscPublic
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- `buf`, `head`, `tail` as the `.kl` runner lays them out. -/
abbrev bufA : BitVec 64 := 0x1000
abbrev headA : BitVec 64 := 0x1100
abbrev tailA : BitVec 64 := 0x1200

theorem spscLocsA : SpscLocs ⟨bufA, headA, tailA⟩ := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The `.kl`'s initial memory: both slots, `head` and `tail` `0`. -/
def spscInitMemA : List (Loc × Val) :=
  [(⟨bufA, 4⟩, 0), (⟨bufA + 8, 4⟩, 0), (⟨headA, 8⟩, 0), (⟨tailA, 8⟩, 0)]

/-! ## The layouts -/

/-- The producer's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def pLayoutA : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize spscProdA

/-- The consumer's layout: text at `0x200000`. -/
@[reducible] def cLayoutA : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize spscConsA

instance pValidA : Executable.ValidLayout (pLayoutA spscProdA) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance cValidA : Executable.ValidLayout (cLayoutA spscConsA) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The initial states -/

/-- The producer's initial state (`0:X0=buf; 0:X1=head; 0:X2=tail`), halting
at the end of its text; no declarations, empty private memory. -/
def spscProd0 : AArch64.State where
  exe := pLayoutA spscProdA
  endPc := 0x100000 + 60
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X2 := 0x1200 } }, 0x100000)

/-- The consumer's initial state (`1:X0=buf; 1:X1=head; 1:X2=tail`). -/
def spscCons0 : AArch64.State where
  exe := cLayoutA spscConsA
  endPc := 0x200000 + 96
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X2 := 0x1200 } }, 0x200000)

section
attribute [local instance] pLayoutA

theorem spscProd0_start : StartA spscProdA ⟨bufA, headA, tailA⟩ spscProd0 := by
  refine ⟨rfl, rfl, by decide, by decide, ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [spscProd0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] cLayoutA

theorem spscCons0_start : StartA spscConsA ⟨bufA, headA, tailA⟩ spscCons0 := by
  refine ⟨rfl, rfl, by decide, by decide, ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [spscCons0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def spscKl : String := include_str "../../../Examples/LockFree/AArch64/spsc_queue.kl"

/-- The `code` block of the `.kl` parses to the producer's text, the dead
`NOP` at `pdone`, and the consumer's text. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == spscProdA ++ spscNop ++ spscConsA
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches spscKl

/-! ## The instance -/

/-- **`forall (1:X10=1 /\ 1:X11=2 /\ 1:X12=3)`** for `spsc_queue.kl` under
`Arch.armv8` (per-thread images), concrete instance of `a64_spsc_envG`. -/
theorem a64_spsc_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [spscProd0, spscCons0] spscInitMemA) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  a64_spsc_envG pLayoutA cLayoutA bufA headA tailA spscLocsA spscProd0_start spscCons0_start
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_concrete
