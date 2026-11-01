/-
**The clone state's facts for main's segment after the clone** (AArch64; the clone-state conjunct hello's
level-2 fence carries for `HelloMainHRI.hMainRH_ofI`'s segment end `MainSegH`).

`MainSegH` reads main's thread at the clone in the region `⟨Rm.base, -144, 48⟩`: `wc_main`'s frame and the 48
bytes of `scc_rt_main`'s frame above it, which `scc_rt_main` reads after `wc_main` returns. The level's fragment
states the clone in `wc_main`'s region alone (`HelloHMid.CloneMidH`'s `At` of `wcNSH` in `R`, whose top is `R.hi =
0`), so the cells above come from the frame condition: at the root's ghost (`RootHP.GJ1RH`) `R` is `wcR R' helloD`
and `F` is `wcF R' helloD … m1 σm`, which keeps the caller's cells outside `R` (`CKept`) as they were at the call
(`Abs R' ⟨-80, []⟩ m1 σm`). The saved return address at `-8` is the caller's `x30` at `wc_main`'s entry (`FrMGH`
at `J1 = wcJ0 (mWC …)`), the label `.L1_scc_rt_main.sp1`.

- `CloneSegH`: the facts: `At` of the clone's node with `JS` in the widened region, its base 144 above `sp`,
  the region not wrapping, the base 16-aligned, the return address `mainSp1`'s, `x13` the cell (an `abbrev` of
  `HelloCloneSegD.CloneSegD`).
- `cloneSegH_of_mid`: `CloneSegH` from `CloneMidH` at the pinned ghost `GJ1RH` (the widening and the return
  address as above; the first stack in the address space, `hbd`). The return address is
  `SegEndRa.fr_ra_mainSp1`.
- `cloneSegH_region_ok`: a widened region at a concrete base is a region (non-vacuity of the `OK` conjunct).
-/
import Spike.Lib.A64HelloRootHP
import Spike.Lib.A64HelloParent
import Spike.Lib.A64HelloMainPost
import Spike.Lib.A64HelloSegEndRa
import Spike.Lib.A64HelloCloneSegD

namespace Spike.Lib.HelloCloneSeg

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib (Region FragS Frag Ctl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (At Abs SORel)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow (CKept)
open Spike.Lib.HelloPreA (cloneAtH pfxM)
open Spike.Lib.HelloHMid (CloneMidH BoxPureH)
open Spike.Lib.A64.Flow.HelloWc (FrMGH)
open Spike.Lib.A64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.HelloH2G (GJ1H)

/-- **The clone state's facts for `MainSegH`** (module doc): `At` of the clone's node with `JS` in the region
`⟨Rm.base, -144, 48⟩`, `Rm.base` 144 above `sp`, the region not wrapping, its base 16-aligned, the saved return
address `mainSp1`'s, `x13` the cell `cA`. The body is `HelloCloneSegD.CloneSegD`'s (stated there, below
`HelloH2Inv.X2H` in the import graph); this name is kept for its users. -/
abbrev CloneSegH : RuntimeLayout → Int64 → State → Ctl → Prop := Spike.Lib.HelloCloneSegD.CloneSegD

/-- **A widened region at a concrete base is a region** (`CloneSegH`'s `OK` conjunct is satisfiable). -/
example : (⟨4096#64, -144, 48⟩ : Region).OK := ⟨by decide, by decide⟩

/-- **`CloneSegH` from the level's clone invariant at the root's ghost** (module doc): `CloneMidH` at
`G := GJ1RH L lbl1 lr`, the first stack in the address space (`hbd`). -/
theorem cloneSegH_of_mid {L : RuntimeLayout} {F0 : MachineData → Prop} {lbl1 : Spike.Lib.A64Consumer.Lbl}
    {lr : WeakMem.AllocLabel} {W : FragS isaLSE2} {Wc : Frag isaLSE2} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hbd : L.stacksA.toNat + 32768 < 2 ^ 64) (h : CloneMidH L F0 (GJ1RH L lbl1 lr) W Wc l b ws n s c fs) :
    CloneSegH L L.endPc s c := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, ⟨hROK, hal, -, hRlo, -, hbase, -, -⟩, hG, hFr, -, -, hAt, hRb, -⟩ :=
    h
  obtain ⟨⟨σC, σ1, Jr, -, -, rfl⟩, v, m1, σm, rfl, rfl⟩ := hG
  -- the saved return address is `mWC`'s `x30`
  have hra : Int64.ofBitVec fr.2 = L.lab mainSp1 := Spike.Lib.A64.HelloPh.SegEndRa.fr_ra_mainSp1 hFr
  -- the clone's node
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := hAt
  obtain ⟨hc, -, -, -, -, -, -, -, -, -, -, h13, -, -, -, -, -, -, h104, h16, h8⟩ := hJ
  obtain ⟨hF0', hCK, hAbsC⟩ := hF
  have hD : Spike.Lib.A64.HelloPh.StartH0G.helloD = 400 := rfl
  have hLsw : Spike.Lib.A64.HelloPh.StartH0G.helloLsw = 480 := rfl
  have hlo' := hROK.lo
  simp only [Spike.Lib.A64.Flow.HelloM.wcR, Region.callee, hD] at hlo' hRlo
  -- the widened abstract state: `wc_main`'s slots below, the caller's cells above
  let σ' : Spike.Lib.A64.Flow.AS := { σ with slot := fun k => if k < 0 then σ.slot k else σm.slot (k - 80) }
  refine ⟨wcR (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0)
      Spike.Lib.A64.HelloPh.StartH0G.helloD,
    wcF (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0)
      Spike.Lib.A64.HelloPh.StartH0G.helloD
      (Spike.Lib.A64.WakePh.MainGlue.FS L (Spike.Lib.A64.Rt.rS0 L) Spike.Lib.A64.HelloPh.StartH0G.helloLsw 0#64 v)
      m1 σm, cA, fr.1, fr.2, σ.regs.TPIDR_EL0.toBitVec,
    ⟨he, hn, hd, hpc, σ', ⟨hA.regs, hA.status, fun r k hk => hA.so r k hk, ?_⟩, ⟨hF0', hCK, hAbsC⟩,
      hc, ?_, ?_, ?_, rfl⟩, hRb, ⟨by dsimp only; omega, by dsimp only; omega⟩, hal, hra, by rw [hA.regs]; exact h13⟩
  · intro k hk
    obtain ⟨hk8, hklo, hkhi⟩ := hk
    dsimp only at hklo hkhi
    by_cases hneg : k < 0
    · obtain ⟨j, hj, hσ⟩ := hA.slot k ⟨hk8, by
        simp only [Spike.Lib.A64.Flow.HelloM.wcR, Region.callee, hD]; omega, by
        simp only [Spike.Lib.A64.Flow.HelloM.wcR, Region.callee]; omega⟩
      refine ⟨j, hj, ?_⟩
      show BitVec.ofInt 64 j = if k < 0 then σ.slot k else σm.slot (k - 80)
      simp only [hneg, ↓reduceIte]; exact hσ
    · have hk' : Region.Off (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0) (-80 + k) :=
        ⟨by omega, by simp only [Spike.Lib.A64.Flow.swR, hLsw]; omega, by simp only [Spike.Lib.A64.Flow.swR]; omega⟩
      have hkeep := hCK (-80 + k) hk' fun h' => by
        simp only [Region.Off, Region.callee] at h'; omega
      obtain ⟨j, hj, hσ⟩ := hAbsC.slot (-80 + k) hk'
      have e : (⟨(wcR (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0)
            Spike.Lib.A64.HelloPh.StartH0G.helloD).base, -144, 48⟩ : Region).addr k =
          (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0).addr (-80 + k) := by
        rw [Region.addr_add]; rfl
      refine ⟨j, by rw [e, hkeep, hj], ?_⟩
      show BitVec.ofInt 64 j = if k < 0 then σ.slot k else σm.slot (k - 80)
      simp only [hneg, ↓reduceIte]
      rw [show k - 80 = -80 + k by omega]; exact hσ
  · show σ'.slot (-104) = cA; simp [σ', h104]
  · show σ'.slot (-16) = fr.1; simp [σ', h16]
  · show σ'.slot (-8) = fr.2; simp [σ', h8]

end Spike.Lib.HelloCloneSeg

/-- info: 'Spike.Lib.HelloCloneSeg.cloneSegH_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCloneSeg.cloneSegH_of_mid
