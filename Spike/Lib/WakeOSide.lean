/-
**`WakeO.OPrem`'s placement-side fields** (AArch64): at the
runtime's layout `L := RuntimeLayout.ofPlaceW hp i` of an output with wake's
placement facts and wake's listing `SccCertificate.asm` (parsing to
`o.prog` and to `wakeProg`, `hpa`/`hwp`), the fields of `OPrem` read off
the placement.

- `aW`, `ha_W`: the take site's address, the take label of the loaded thread
  (`OData.a`), and `OPrem.ha` there (`WorkerSide.wake_hμ`).
- `hro_W`: `OPrem.hro` (A1's `layoutOk`, `rodata_stackPool_of_layoutOk`).
- `hwf_W`: `OPrem.hwf` (A1, `wf_link_of_placeW`).
- `hti0_W`: `OPrem.hti0` (`WakePreTi.ti0_of`) from the loaded thread off the
  two abort phases `Ab` and `Ac`.
- `r0W`, `r1W`, `ranges_W`: the two takes' ranges (`OData.r0`, `OData.r1`:
  the first two 16 KiB stacks at `scc_rt_stacks`, `Ti2.r0Of`,
  `PreChild.r1Of`) and `OPrem`'s range fields `hs0`, `hs1`, `hz0`, `hz1`,
  `hd`, `hw0`, `hw1`, given the second stack in the pool (`hsub1`, a fact
  of the concrete layout like `hpin2`).
-/
import Spike.Lib.WakeOG
import Spike.Lib.WakeAssemblyR
import Spike.Lib.Rt.A64RtTi2

namespace Spike.Lib.WakeOSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakePreTi
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The take site's address** at entry `E`: the take label in the loaded
thread. -/
def aW (E : Entry) : Int64 :=
  (_root_.Executable.labels (threadAt E (Ly).Λ.code.lo wakeProg (loadSyms (Ly).Λ o.secs.rodata)).exe).label
    Scc.Lower.Names.takeSite

include hp

/-- **`OPrem.ha`**: the entry's marks put the take site at `aW`. -/
theorem ha_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (E : Entry) :
    ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ).site .take = some (aW hp i E).toBitVec.toNat := by
  have ho : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  have hlo : Scc.Cert.Link.A64.loadOk (Ly).Λ wakeProg o.secs = true := by
    rw [← ho]; exact PlaceW.loadOk_link_of_placeW i hp
  exact (WorkerSide.wake_hμ (H := kernel 2) (E := E) hwp hlo).1

/-- **`OPrem.hro`**: `.rodata` off the stack pool (A1). -/
theorem hro_W : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool :=
  Scc.Cert.PlaceOK.rodata_stackPool_of_layoutOk (PlaceW.layoutOk_of_placeW (PlaceW.link i hp))

/-- **`OPrem.hwf`**: the link is well-formed (A1). -/
theorem hwf_W : (Ly).Λ.WF := PlaceW.wf_link_of_placeW i hp

/-- **`OPrem.hti0`**: `TIC` at the one-slot load, the loaded thread off
both abort phases. -/
theorem hti0_W {Ab Ac : State → Prop} (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hd : dataSections SccCertificate.asm = some o.secs) (E : Entry)
    (hab0 : ¬ Ab (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata)))
    (hac0 : ¬ Ac (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))) :
    ∀ d : Cfg, (target (kernel 1) E).load SccCertificate.asm (Ly).Λ = some d → Spike.Lib.A64ConsumerA.TIC Ab Ac [] d :=
  ti0_of hpa hd hab0 hac0

/-- **main's take's range**: the first stack. -/
abbrev r0W : Range := Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab

/-- **The child's take's range**: the second stack. -/
abbrev r1W : Range := Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- `scc_rt_stacks`'s first stack ends below `2 ^ 32` (A1: the stack pool
below `2 ^ 32`). -/
theorem stacks_lt : Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab |>.toNat |> (· + 16384 ≤ 2 ^ 32) := by
  have hb := PlaceW.below32_of_placeW hp Λ0.stackPool (by simp [Scc.Sem.Layout.regions])
  have hs := (Ly).stacks_sub
  rw [show Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks]
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
  have hbd : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by omega
  obtain ⟨h0l, h0s⟩ := Spike.Lib.A64.Rt.Ti2.r0Of_eq (Ly).lab
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd
  have hs := (Ly).stacks_sub
  rw [show (Ly).stacksA = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only at hs1 hs2
  refine ⟨?_, hsub1, ?_, ?_, Spike.Lib.A64.Rt.Ti2.r01_disj hbd, ?_, ?_⟩ <;>
    simp only [r0W, r1W, Scc.Sem.Range.Sub, h0l, h0s, h1l, h1s] <;> omega

end Place

/-- info: 'Spike.Lib.WakeOSide.ranges_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ranges_W

/-- info: 'Spike.Lib.WakeOSide.ha_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ha_W

/-- info: 'Spike.Lib.WakeOSide.hro_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hro_W

end Spike.Lib.WakeOSide
