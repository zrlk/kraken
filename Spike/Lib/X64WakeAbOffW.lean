/-
**wake.w's worker off the `writeErr` and `threads` abort exits** (x86-64,
the twin of `Spike/Lib/A64WakeAbOffW.lean`, same names): the canonical
target's marks are the phase record's (`marks_target`), and a worker side
whose states are `AbOffL` of the placed layout's labels is off the
`writeErr` and `threads` abort sites of the loaded program's marks: the
`WakeAssembly` checklist item `hab1` (`hab1_of`).

- `marks_target`: the target's marks at any hooks and entry, of a text whose
  cells are the layout's, are `PhRec.μ L`.
- `hab1_of`: `hab1` from `AbOffL` at `RuntimeLayout.ofPlaceWX`.

**Unlike AArch64**: only the `hab1` half is twinned. The per-node half
(`wakeZ`, `nodeZ_and`, `thrZ_and`, `nodeZ_ab`, `pro_ab`, `head_ab`, `wk_ab`,
`unpk_ab`, `tail_ab`, `thrZ_ab`, `cZ_ab`, `childThrZW`, `cZW`) needs the
x86-64 `NodeZ`/`ThrZ` (`A64WakeNN`, `A64WakeWorkerLabelsNN`), the worker's
node families and `wakePass` (`A64WakePass`), which are not twinned yet; it
belongs with them, from `X64WakeAbOffL.abOff_at` (byte pcs). So `hab1_of`'s
`hZ` reads `∃ c, AbOffL … t1.st c` (A64: `∃ c, wakeZ … t1.st c`, whose
second conjunct this is). The text is an `Scc.Sem.X64.Asm` whose cells are
the layout's (`cellsOf asm = some L.prog`; A64: `textProgram asm = .ok
L.prog`); the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`.
-/
import Spike.Lib.X64AbOffL
import Spike.Lib.X64PhRec

namespace Spike.Lib.X64.Flow.Worker.Wake.AbOffW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64AbOffL (AbOffL)
open Spike.Lib (PlaceWX)

/-- **The canonical target's marks** at any hooks and entry, of a text whose
cells are the layout's (`hpa`), are the record's (`PhRec.marks_eq` at any
`H`, `E`). -/
theorem marks_target (L : RuntimeLayout) {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}
    (hpa : Scc.Sem.X64.cellsOf asm = some L.prog) :
    (Scc.Sem.X64.target H E).marks asm L.Λ = Spike.Lib.X64.PhRec.μ L := by
  have hr := Scc.Sem.X64.resolve_of_parsed H E L.Λ hpa
  unfold Scc.Sem.Target.marks Spike.Lib.X64.PhRec.μ
  congr 1
  · funext k; exact hr _
  · funext k; exact hr _

/-- **`hab1`** (`WakeAssembly.wake_obligations`): at the layout of a placed
output, a worker relation whose states are `AbOffL` of the layout's labels
(`hZ`) puts the worker off the `writeErr` and `threads` abort sites of the
loaded program's marks. -/
theorem hab1_of {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (h : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) {ι : Type}
    {PT1 : ι → Memory → WeakMem.Memory → Thread isa → TermRun.TTh → Prop}
    (hZ : ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 →
      ∃ c, AbOffL (RuntimeLayout.ofPlaceWX h i).lab t1.st c) :
    ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 → ∀ k a,
      ((Scc.Sem.X64.target H E).marks asm (RuntimeLayout.ofPlaceWX h i).Λ).abortAt k = some a →
        Scc.Sem.X64.pcOf t1.st = a → k ≠ .writeErr ∧ k ≠ .threads := by
  intro w tm sm t1 s1 hP k a ha hpc
  obtain ⟨c, hL⟩ := hZ w tm sm t1 s1 hP
  rw [marks_target (RuntimeLayout.ofPlaceWX h i) hpa] at ha
  exact Spike.Lib.X64AbOffL.abOff_of_L_ofPlaceOK h i hL k a ha hpc

end Spike.Lib.X64.Flow.Worker.Wake.AbOffW

/--
info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffW.hab1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffW.hab1_of
