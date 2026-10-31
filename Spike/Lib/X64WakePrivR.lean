/-
**wake.w on x86-64: the private-memory invariant through the pre-spawn
relation** (`X64WakeSpawnR.PreR`'s `hpv`): the x86-64 twin of
`Spike/Lib/WakePrivR.lean` (same names, in `Spike.Lib.X64WakePrivR`).

- `VPriv Λ E d`: the entry stack clear of the layout and
  `DmemPriv.PrivInv abi WideSt Λ E d` (`X64DmemPriv`'s invariant).
- `clear_of_load`: the target loads only with a clear entry stack.
- `Pre1T.priv`: any `Pre1T … R1` strengthened to `R1 ∧ VPriv`, by
  `X64WakePreInv.Pre1T.inv` with `VPriv` at the load
  (`X64WakeRunInv.runInv_load`'s `PrivInv`, `clear_of_load`) and along each
  one-slot step (`X64DmemPriv.privInv_step`).
- `priv_of_R1`: `hMainR_I`'s `hpv` statement from a relation `R1 ∧ VPriv`;
  at `fun d s => R1 d s ∧ VPriv Λ E d` the field is
  `fun _ _ h => priv_of_R1 h`.

**Where this differs from AArch64**: texts are `Asm` records, so the load
reads the code cells by `cellsOf asm` and the data by
`dataSections asm.text`, and the fragment premise of `Pre1T.priv` is on the
cells (`wideIn (cells.map (·.1))`, `X64WakeWide.hwide_of`'s shape) rather
than on a parsed `textProgram`.
-/
import Spike.Lib.X64WakePreInv
import Spike.Lib.X64WakeRunInv

namespace Spike.Lib.X64WakePrivR

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Scc.Cert.WideX64 Spike.Lib.DmemPriv
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi

/-- **The private-memory invariant at a configuration**: the entry stack
clear of `Λ` and `PrivInv` from `E`. -/
def VPriv (Λ : Scc.Sem.Layout) (E : Entry) (d : Cfg) : Prop :=
  E.clear Λ = true ∧ PrivInv abi WideSt Λ E d

/-- **The target loads only with a clear entry stack.** -/
theorem clear_of_load {n : Nat} {E : Entry} {Λ : Scc.Sem.Layout} {asm : Asm} {t : (machine (kernel n)).Cfg}
    (h : (target (kernel n) E).load asm Λ = some t) : E.clear Λ = true := by
  simp only [target] at h
  rcases hp : cellsOf asm with _ | cells
  · simp [hp] at h
  rcases hs : dataSections asm.text with _ | secs
  · simp [hp, hs] at h
  simp only [hp, hs, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · cases h

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- **`Pre1T` with the private-memory invariant**, for a text whose code
cells are `wideIn`. -/
theorem priv (O : Pre1T arch Λ B asm E R1 Ab Ac)
    (hw : ∀ cells, cellsOf asm = some cells → wideIn (cells.map (·.1)) = true) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPriv Λ E d) Ab Ac :=
  Spike.Lib.X64WakePreInv.Pre1T.inv O (fun d _ => VPriv Λ E d)
    (fun _ _ hd _ _ => ⟨clear_of_load hd, (Spike.Lib.X64WakeRunInv.runInv_load hw hd).1⟩)
    (fun _ _ _ _ _ _ _ hV _ hs _ _ => ⟨hV.1, Spike.Lib.X64DmemPriv.privInv_step hV.2 hs⟩)

end Pre1T

/-- **`hpv` from the relation** `R1 ∧ VPriv`. -/
theorem priv_of_R1 {Λ : Scc.Sem.Layout} {E : Entry} {R1 : Cfg → TermRun.Cfg → Prop} {d : Cfg}
    {s : TermRun.Cfg} (h : R1 d s ∧ VPriv Λ E d) :
    ∃ (Ent : Entry) (P : State → Prop), Ent.clear Λ = true ∧ PrivInv abi P Λ Ent d :=
  ⟨E, WideSt, h.2.1, h.2.2⟩

end Spike.Lib.X64WakePrivR

/-- info: 'Spike.Lib.X64WakePrivR.clear_of_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakePrivR.clear_of_load

/-- info: 'Spike.Lib.X64WakePrivR.Pre1T.priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakePrivR.Pre1T.priv

/-- info: 'Spike.Lib.X64WakePrivR.priv_of_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakePrivR.priv_of_R1
