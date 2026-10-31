/-
**`X64WakeO.OPrem`'s placement-side fields** (x86-64, the twin of
`Spike/Lib/WakeOSide.lean`, same names): at the runtime's layout
`L := RuntimeLayout.ofPlaceWX hp i` of an output with wake's placement
facts and a text whose cells are the output's (`hpa`), the fields of
`OPrem` read off the placement.

- `aW`, `ha_W`: the take site's address, the take label of the loaded thread
  (`OData.a`), and `OPrem.ha` there (`AbOffW.marks_target`,
  `PlaceWX.site_ofPlaceWX`).
- `hro_W`: `OPrem.hro` (A1's `layoutOk`, `rodata_stackPool_of_layoutOk`).
- `hwf_W`: `OPrem.hwf` (A1, `wf_link_of_placeWX`).
- `hti0_W`: `OPrem.hti0` (`X64WakePreTi.ti0_of`) from the loaded thread off
  the two abort phases `Ab` and `Ac`.
- `r0W`, `r1W`, `ranges_W`: the two takes' ranges (`OData.r0`, `OData.r1`:
  the first two 16 KiB stacks at `scc_rt_stacks`, `Ti2.r0Of`,
  `PreChild.r1Of`) and `OPrem`'s range fields `hs0`, `hs1`, `hz0`, `hz1`,
  `hd`, `hw0`, `hw1`, given the second stack in the pool (`hsub1`, a fact
  of the concrete layout like `hpin2`).

**Unlike AArch64**: the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`; the
text is an `Scc.Sem.X64.Asm` whose cells are the output's (`hpa : cellsOf
asm = some o.prog`, data `hd : dataSections asm.text = some o.secs`; A64:
`textProgram SccCertificate.asm = .ok o.prog` and `= .ok wakeProg`), so
`aW` is the take label in the loaded thread of `o.prog` and `ha_W` needs no
`hwp`: it is `AbOffW.marks_target` with `PlaceWX.site_ofPlaceWX` (A64:
`WorkerSide.wake_hμ`, which `X64WakeOSide` does not import, the x86-64
`WakeWorkerSide`/`WakeAssemblyR` not being twinned yet).
-/
import Spike.Lib.X64WakeOG
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64SiteOfPlaceW
import Spike.Lib.Rt.X64RtTi2

namespace Spike.Lib.X64WakeOSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi
open Spike.Lib.X64.Rt (RuntimeLayout)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The take site's address** at entry `E`: the take label in the loaded
thread. -/
def aW (E : Entry) : Int64 :=
  (_root_.Executable.labels (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata)).exe).label
    Scc.Lower.Names.takeSite

include hp

/-- **`OPrem.ha`**: the entry's marks put the take site at `aW`. -/
theorem ha_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (E : Entry) :
    ((target (kernel 2) E).marks asm (Ly).Λ).site .take = some (aW hp i E).toBitVec.toNat := by
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact PlaceWX.site_ofPlaceWX hp i

/-- **`OPrem.hro`**: `.rodata` off the stack pool (A1). -/
theorem hro_W : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool :=
  Scc.Cert.PlaceOK.rodata_stackPool_of_layoutOk (PlaceWX.layoutOk_of_placeWX (PlaceWX.link i hp))

/-- **`OPrem.hwf`**: the link is well-formed (A1). -/
theorem hwf_W : (Ly).Λ.WF := PlaceWX.wf_link_of_placeWX i hp

/-- **`OPrem.hti0`**: `TIC` at the one-slot load, the loaded thread off
both abort phases. -/
theorem hti0_W {Ab Ac : State → Prop} {asm : Asm} (hpa : cellsOf asm = some o.prog)
    (hd : dataSections asm.text = some o.secs) (E : Entry)
    (hab0 : ¬ Ab (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata)))
    (hac0 : ¬ Ac (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))) :
    ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d → Spike.Lib.X64ConsumerA.TIC Ab Ac [] d :=
  ti0_of hpa hd hab0 hac0

/-- **main's take's range**: the first stack. -/
abbrev r0W : Range := Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab

/-- **The child's take's range**: the second stack. -/
abbrev r1W : Range := Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- `scc_rt_stacks`'s first stack ends below `2 ^ 32` (A1: the stack pool
below `2 ^ 32`). -/
theorem stacks_lt : Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab |>.toNat |> (· + 16384 ≤ 2 ^ 32) := by
  have hb := PlaceWX.below32_of_placeWX hp Λ0.stackPool (by simp [Scc.Sem.Layout.regions])
  have hs := (Ly).stacks_sub
  rw [show Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks]
  obtain ⟨-, h2⟩ := hs
  change _ ≤ Λ0.stackPool.lo + Λ0.stackPool.size at h2
  simp only at h2 ⊢
  omega

/-- **`OPrem`'s range fields** at `r0W`, `r1W`. -/
theorem ranges_W (hsub1 : (r1W hp i).Sub (Ly).Λ.stackPool) :
    (r0W hp i).Sub (Ly).Λ.stackPool ∧ (r1W hp i).Sub (Ly).Λ.stackPool ∧ 0 < (r0W hp i).size ∧
      0 < (r1W hp i).size ∧ (r1W hp i).Disjoint (r0W hp i) ∧ (r0W hp i).lo + (r0W hp i).size ≤ 2 ^ 64 ∧
      (r1W hp i).lo + (r1W hp i).size ≤ 2 ^ 64 := by
  have hlt := stacks_lt hp i
  simp only at hlt
  have hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by omega
  obtain ⟨h0l, h0s⟩ := Spike.Lib.X64.Rt.Ti2.r0Of_eq (Ly).lab
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd
  have hs := (Ly).stacks_sub
  rw [show (Ly).stacksA = Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only at hs1 hs2
  refine ⟨?_, hsub1, ?_, ?_, Spike.Lib.X64.Rt.Ti2.r01_disj hbd, ?_, ?_⟩ <;>
    simp only [r0W, r1W, Scc.Sem.Range.Sub, h0l, h0s, h1l, h1s] <;> omega

end Place

end Spike.Lib.X64WakeOSide

/-- info: 'Spike.Lib.X64WakeOSide.ha_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.ha_W

/-- info: 'Spike.Lib.X64WakeOSide.hro_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.hro_W

/-- info: 'Spike.Lib.X64WakeOSide.hwf_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.hwf_W

/-- info: 'Spike.Lib.X64WakeOSide.hti0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.hti0_W

/-- info: 'Spike.Lib.X64WakeOSide.stacks_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.stacks_lt

/-- info: 'Spike.Lib.X64WakeOSide.ranges_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOSide.ranges_W
