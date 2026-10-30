/-
**wake.w on AArch64: the private-memory invariant through the pre-spawn
relation** (`WakeSpawnR.PreR.priv`).

- `VPriv Λ E d`: the entry stack clear of the layout and
  `DmemPriv.PrivInv abi WideSt Λ E d` (`A64DmemPriv`'s invariant).
- `Pre1T.priv`: any `Pre1T … R1` strengthened to `R1 ∧ VPriv`, by
  `WakePreInv.Pre1T.inv` with `VPriv` at the load
  (`WakeRunInv.runInv_load`'s `PrivInv`, `clear_of_load`) and along each
  one-slot step (`A64DmemPriv.privInv_step`).
- `priv_of_R1`: `PreR.priv`'s statement from a relation `R1 ∧ VPriv`, so at
  `SpawnPrem (QG … (fun d s => R1 d s ∧ VPriv Λ E d) …)` the field is
  `priv_of_R1 hP.1`.

The combined adapter with the source invariant `VPre`
(`WakeSpawnLt.pre1T_vpre`) is `Pre1T.priv (pre1T_vpre O)`, at
`fun d s => (R1 d s ∧ VPre s) ∧ VPriv Λ E d`; `hlt0_of` reads its `.1`.
-/
import Spike.Lib.WakePreInv
import Spike.Lib.WakeRunInv

namespace Spike.Lib.WakePrivR

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Scc.Cert.WideA64 Spike.Lib.DmemPriv
open Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePreTi

/-- **The private-memory invariant at a configuration**: the entry stack
clear of `Λ` and `PrivInv` from `E`. -/
def VPriv (Λ : Scc.Sem.Layout) (E : Entry) (d : Cfg) : Prop :=
  E.clear Λ = true ∧ PrivInv abi WideSt Λ E d

/-- **The target loads only with a clear entry stack.** -/
theorem clear_of_load {n : Nat} {E : Entry} {Λ : Scc.Sem.Layout} {asm : String} {t : (machine (kernel n)).Cfg}
    (h : (target (kernel n) E).load asm Λ = some t) : E.clear Λ = true := by
  simp only [target] at h
  rcases hp : (textProgram asm).toOption with _ | prog
  · simp [hp] at h
  rcases hs : dataSections asm with _ | secs
  · simp [hp, hs] at h
  simp only [hp, hs, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · cases h

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- **`Pre1T` with the private-memory invariant**, for a text of `wideIn`
instructions. -/
theorem priv (O : Pre1T arch Λ B asm E R1 Ab Ac)
    (hw : ∀ prog, (textProgram asm).toOption = some prog → wideIn prog = true) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPriv Λ E d) Ab Ac :=
  Spike.Lib.WakePreInv.Pre1T.inv O (fun d _ => VPriv Λ E d)
    (fun _ _ hd _ _ => ⟨clear_of_load hd, (Spike.Lib.WakeRunInv.runInv_load hw hd).1⟩)
    (fun _ _ _ _ _ _ _ hV _ hs _ _ => ⟨hV.1, Spike.Lib.A64DmemPriv.privInv_step hV.2 hs⟩)

end Pre1T

/-- **`PreR.priv` from the relation** `R1 ∧ VPriv`. -/
theorem priv_of_R1 {Λ : Scc.Sem.Layout} {E : Entry} {R1 : Cfg → TermRun.Cfg → Prop} {d : Cfg}
    {s : TermRun.Cfg} (h : R1 d s ∧ VPriv Λ E d) :
    ∃ (Ent : Entry) (P : State → Prop), Ent.clear Λ = true ∧ PrivInv abi P Λ Ent d :=
  ⟨E, WideSt, h.2.1, h.2.2⟩

/-- info: 'Spike.Lib.WakePrivR.clear_of_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clear_of_load

/-- info: 'Spike.Lib.WakePrivR.Pre1T.priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Pre1T.priv

/-- info: 'Spike.Lib.WakePrivR.priv_of_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms priv_of_R1

end Spike.Lib.WakePrivR
