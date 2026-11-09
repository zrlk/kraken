/-
**`H1G`'s "unmapped under `F`" premises** (wake.w, x86-64; the twin of
`Spike/Lib/A64WakeHun.lean`): `scc_rt_nthreads`, `scc_rt_pinned_next`, the
second TCB's header `pinA + 96` and id word `t2 + 56` load none in every
memory of `F`, a frame whose every word of `.data` or `pinned` loads none
(`HunB`; A13's `spawnWords`/`ntA`, A8's `words_mapped`).

- `HunB`: every word of `.data` or `pinned` loads none under `F`.
- `hunN_W`, `hunP_W`, `hunH_W`, `hunT_W`: the four.
- `h1GA_of`: `WakeH1A.H1GA` from `HunB F`, `BoxPure` and the callee, with the
  runtime words by `WakeH1Rt` and the second TCB's band by `OwnMid.bandSp3`.

**Unlike AArch64**: the root's use of `F ⊆ wFU` (A64's `wF (swR v (-384) 0)
336`, x86-64's at `MainGlue.RS`) is factored through `HunB`, which the root
discharges from `FS`'s `WordsNoneP`, and `h1GA_of`, which also
supplies `tcbA_W`'s band from `BoxPure` (`band_of_box`, `bandSp3`); the
assembly is a parameter `asm`.
-/
import Spike.Lib.X64WakeH1Rt
import Spike.Lib.X64WakeH1A
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.WakePh.Hun

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (cellsOf)
open SccCode (wakeCells)
open Spike.Lib (PlaceWX Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.HeapLand (AllocLand)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **Every word of `.data` or `pinned` loads none under `F`.** -/
def HunB (F : MachineData → Prop) : Prop :=
  ∀ a : BitVec 64, (∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j)) →
    ∀ m, F m → Mem.loadInt m.dmem a 8 = none

section Four

variable {F : MachineData → Prop} (hF : HunB hp i F)
include hF

omit hF in
/-- `t2 + 56` is `pinA + 192`. -/
theorem t2_56 : Spike.Lib.X64.Flow.WakeWc.t2 (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 192 := by
  show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 136#64 + 56#64 = _
  rw [(Ly).lab_pin, BitVec.add_assoc]; rfl

/-- **`hunN`**: `scc_rt_nthreads`. -/
theorem hunN_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) 8 = none :=
  hF _ (H1Rt.a13_facts hp i hA13).1

/-- **`hunP`**: `scc_rt_pinned_next`. -/
theorem hunP_W : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none :=
  hF _ ((Ly).words_mapped _ (Ly).pn_mem).2.2

/-- **`hunH`**: the second TCB's header `pinA + 96`. -/
theorem hunH_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 128#64) 8 = none :=
  hF _ ((H1Rt.a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨2, List.mem_range.2 (by decide), rfl⟩))

/-- **`hunT`**: the second TCB's id word `t2 + 56 = pinA + 192`. -/
theorem hunT_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.WakeWc.t2 (Ly).lab + 56#64) 8 = none := by
  rw [t2_56 hp i]
  exact hF _ ((H1Rt.a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨10, List.mem_range.2 (by decide), rfl⟩))

end Four

/-- **`H1GA` from `HunB` and the callee**: the unmapped words by
`hunN_W` … `hunT_W`, the runtime words by `WakeH1Rt` (the second TCB's band
from `BoxPure`), the callee `ti` given. -/
theorem h1GA_of (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop)
    (Ctx : Spike.Lib.FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat}
    (hland : AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n)
    {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64}
    (hB : BoxPure (Ly) F0 n R F J0 t) (hF : HunB hp i F)
    (ti : Spike.Lib.X64.WakeH1GOf.TiG asm hp i E cT Dt Ctx ls0 l b n R F t) :
    Spike.Lib.X64.WakeH1A.H1GA asm hp i E cT Dt Ctx ls0 l b n R F t :=
  have hN := hunN_W hp i hF hA13
  have hP := hunP_W hp i hF
  have hH := hunH_W hp i hF hA13
  { hunN := hN
    hunP := hP
    hunH := hH
    resA := H1Rt.resA_W asm hp i E cT ls0 hpa hwp hlo0 hstat hA13 hland hN
    hdrA := H1Rt.hdrA_W asm hp i E cT ls0 hstat hA13 hland hH
    tcbA := H1Rt.tcbA_W asm hp i E cT ls0 hpa hwp hlo0 hstat hA13 hland
      (OwnMid.bandSp3 (OwnMid.bandOnP_mono (Spike.Lib.X64.WakeH1GOf.band_of_box hB) (Int.le_refl _) (by decide)))
      hP
    tid := H1Rt.tid_W asm hp i E cT ls0 hstat hA13 hland (hunT_W hp i hF hA13)
    ti := ti }

end Spike.Lib.X64.WakePh.Hun

/-- info: 'Spike.Lib.X64.WakePh.Hun.hunN_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hun.hunN_W

/-- info: 'Spike.Lib.X64.WakePh.Hun.hunP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hun.hunP_W

/-- info: 'Spike.Lib.X64.WakePh.Hun.hunH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hun.hunH_W

/-- info: 'Spike.Lib.X64.WakePh.Hun.hunT_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hun.hunT_W

/-- info: 'Spike.Lib.X64.WakePh.Hun.h1GA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hun.h1GA_of
