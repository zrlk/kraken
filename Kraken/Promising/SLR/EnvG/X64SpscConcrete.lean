/-
**Part 8: a concrete instance of
`x64_spsc_envG`** (the `X64TakeMpConcrete` pattern): non-vacuity of its start
hypotheses (`StartPX`/`StartCX`, each with an empty private memory) and of
`SpscLocs`.

The symbols are laid out as the `.kl` runner lays them out, `0x100` bytes
apart in the order of the init block: `buf0 = 0x1000`, `buf1 = 0x1100`,
`head = 0x1200`, `tail = 0x1300`, all initially `0` (`spscInitMemX`). The
producer's text is at `0x200000`, the consumer's at `0x300000` (`klLayout`:
labels 0 bytes, every other directive 1). Every hypothesis is discharged by
`decide`, `rfl` or `simp` (no `native_decide`).
-/
import Kraken.Promising.SLR.EnvG.X64SpscPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG.Concrete

/-- `buf0`, `head`, `tail` as the `.kl` runner lays them out. -/
abbrev bufX : BitVec 64 := 0x1000
abbrev headX : BitVec 64 := 0x1200
abbrev tailX : BitVec 64 := 0x1300

theorem spscLocsX : SpscLocs ⟨bufX, headX, tailX⟩ := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The `.kl`'s initial memory: `buf0 = buf1 = head = tail = 0`. -/
def spscInitMemX : List (Loc × Val) :=
  [(⟨bufX, 4⟩, 0), (⟨bufX + 256, 4⟩, 0), (⟨headX, 4⟩, 0), (⟨tailX, 4⟩, 0)]

/-- The producer's layout: text at `0x200000`. -/
@[reducible] def pLayoutX : _root_.Layout := klLayout spscProducerX 0x200000

instance pValidX : Executable.ValidLayout (pLayoutX spscProducerX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The consumer's layout: text at `0x300000`. -/
@[reducible] def cLayoutX : _root_.Layout := klLayout spscConsumerX 0x300000

instance cValidX : Executable.ValidLayout (cLayoutX spscConsumerX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The producer's initial state (`0:rbx=buf0`, `rdi = tail`, `rsi = head`),
halting at the end of its text (16 instructions); empty private memory. -/
def spscProducerX0 : X64.State where
  exe := pLayoutX spscProducerX
  endPc := 0x200000 + 16
  st := ({ regs := ((({} : Reg64s).set64 .rbx bufX).set64 .rdi tailX).set64 .rsi headX }, 0x200000)

/-- The consumer's initial state (`1:rbx=buf0`, `rdi = tail`, `rsi = head`),
halting at the end of its text (29 instructions); empty private memory. -/
def spscConsumerX0 : X64.State where
  exe := cLayoutX spscConsumerX
  endPc := 0x300000 + 29
  st := ({ regs := ((({} : Reg64s).set64 .rbx bufX).set64 .rdi tailX).set64 .rsi headX }, 0x300000)

section
attribute [local instance] pLayoutX

theorem spscProducerX0_start : StartPX bufX headX tailX spscProducerX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun _ => by simp [spscProducerX0]⟩

end

section
attribute [local instance] cLayoutX

theorem spscConsumerX0_start : StartCX bufX headX tailX spscConsumerX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun _ => by simp [spscConsumerX0]⟩

end

/-- **The x64 SPSC queue under `Arch.tso`**, concrete instance of
`x64_spsc_envG`: every reachable final configuration has the consumer's
`r12d = 1`, `r13d = 2`, `r14d = 3`. -/
theorem x64_spsc_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spscProducerX0, spscConsumerX0] spscInitMemX) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  x64_spsc_envG pLayoutX cLayoutX bufX headX tailX spscLocsX spscProducerX0_start spscConsumerX0_start
    (by decide) (by decide) hc hf

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.x64_spsc_envG_concrete
