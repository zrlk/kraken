/-
**The clone state's facts for main's segment after the clone** (x86-64; the twin of
`Spike/Lib/A64HelloCloneSeg.lean`: the clone-state conjunct hello's level-2 fence carries for main's segment end
`MainSegH`).

`MainSegH` reads main's thread at the clone in the region `⟨Rm.base, -128, 40⟩`: `wc_main`'s frame below its
`%rbp`, the saved `%rbp` and return address, and `scc_rt_main`'s cells above them up to its spill, which
`scc_rt_main` reads after `wc_main` returns. The level's fragment states the clone in `wc_main`'s region alone
(`X64HelloHMid.CloneMidH`'s `At` of `wcNSH` in `R`, whose top is `R.hi = 16`), so the cells above come from the
frame condition: at the root's ghost (`RootHP.GJ1RH`) `R` is `(wcR R' helloD).fp (-8)` and `F` is
`wcF R' helloD … m1 σm`, which keeps the caller's cells outside `wc_main`'s region (`CKept`) as they were at the
call (`Abs R' ⟨-80, []⟩ m1 σm`). The saved return address at `8` is the one `scc_rt_main`'s `call` pushed
(`FrMGH` at `J1 = wcJ0 (mWC …)`), the label `.Lscc_rt_main.x3`.

- `CloneSegH`: the facts (an `abbrev` of `X64HelloCloneSegD.CloneSegD`).
- `cloneSegH_of_mid`: `CloneSegH` from `CloneMidH` at the pinned ghost `GJ1RH` (the widening and the return
  address as above; the first stack in the address space, `hbd`). The return address is
  `SegEndRa.fr_ra_mainX3`.

## Differences from the AArch64 version

- The widened region is `⟨Rm.base, -128, 40⟩` based at `wc_main`'s `%rbp` (AArch64: `⟨Rm.base, -144, 48⟩` at the
  entry `sp`). `wc_main`'s own cells are those below `16` (the frame, the saved `%rbp` at `0` and the return
  address at `8`; AArch64: below `0`), and a cell `k ≥ 16` is the caller's cell `k - 88` of
  `RS helloLsw v` (`R.base = RS.addr (-88)`: the callee's region at `-80` rebased by `-8`; AArch64: `k - 80` of
  `swR v (-helloLsw) 0`).
- The node's caller words are `JS`'s `fp` (slot `0`) and `ra` (slot `8`), read from the frame facts at `wcNSH`;
  the cell is in `%r15` (AArch64: `x13`); the return address is `mainX3`'s (AArch64: `mainSp1`).
-/
import Spike.Lib.X64HelloRootHPD
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64HelloSegEndRa
import Spike.Lib.X64HelloCloneSegD

namespace Spike.Lib.X64HelloCloneSeg

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region FragS Frag Ctl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (At Abs)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.X64HelloHMid (CloneMidH)
open Spike.Lib.X64.HelloPh.RootHP (GJ1RH)

/-- **The clone state's facts for `MainSegH`** (module doc): `At` of the clone's node with `JS` in the region
`⟨Rm.base, -128, 40⟩`, `Rm.base` 128 above `%rsp`, the region not wrapping, its base 16-aligned, the saved
return address `mainX3`'s, `%r15` the cell `cA`. The body is `X64HelloCloneSegD.CloneSegD`'s (stated there,
below `X64HelloH2Inv` in the import graph); this name is kept for its users. -/
abbrev CloneSegH : RuntimeLayout → Int64 → State → Ctl → Prop := Spike.Lib.X64HelloCloneSegD.CloneSegD

/-- **A widened region at a concrete base is a region** (`CloneSegH`'s `OK` conjunct is satisfiable). -/
example : (⟨4096#64, -128, 40⟩ : Region).OK := ⟨by decide, by decide⟩

/-- **`CloneSegH` from the level's clone invariant at the root's ghost** (module doc): `CloneMidH` at
`G := GJ1RH L lbl1 lr`, the first stack in the address space (`hbd`). -/
theorem cloneSegH_of_mid {L : RuntimeLayout} {F0 : MachineData → Prop} {lbl1 : Spike.Lib.X64Consumer.Lbl}
    {lr : WeakMem.AllocLabel} {W : FragS isa} {Wc : Frag isa} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hbd : L.stacksA.toNat + 32768 < 2 ^ 64) (h : CloneMidH L F0 (GJ1RH L lbl1 lr) W Wc l b ws n s c fs) :
    CloneSegH L L.endPc s c := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, ⟨hROK, hal, -, hRlo, -, hbase, -, -⟩, hG, hFr, -, -, hAt, hRb, -⟩ :=
    h
  obtain ⟨⟨σC, σ1, Jr, -, -, rfl⟩, v, m1, σm, rfl, rfl, -⟩ := hG
  -- the saved return address is the one `scc_rt_main`'s `call` pushed
  have hra : Int64.ofBitVec fr.2 = L.lab Spike.Lib.X64.Flow.Worker.Hello.MainPost.mainX3 :=
    Spike.Lib.X64.HelloPh.SegEndRa.fr_ra_mainX3 hFr
  -- the clone's node
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := hAt
  obtain ⟨⟨⟨hc, -, -, -, -, -, -, -, -, h48, h0, h8⟩, -, -, -, -, h15, -⟩, -⟩ := hJ
  obtain ⟨hF0', hCK, hAbsC⟩ := hF
  have hD : Spike.Lib.X64.HelloPh.StartH0G.helloD = 400 := rfl
  have hLsw : Spike.Lib.X64.HelloPh.StartH0G.helloLsw = 488 := rfl
  have hlo' := hROK.lo
  simp only [Spike.Lib.Region.fp, Spike.Lib.X64.Flow.HelloM.wcR, Region.callee, hD] at hlo' hRlo
  -- the widened abstract state: `wc_main`'s cells below `16`, the caller's cells above
  let σ' : Spike.Lib.X64.AS := { σ with slot := fun k => if k < 16 then σ.slot k else σm.slot (k - 88) }
  refine ⟨(wcR (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
      Spike.Lib.X64.HelloPh.StartH0G.helloD).fp (-8),
    wcF (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
      Spike.Lib.X64.HelloPh.StartH0G.helloD
      (Spike.Lib.X64.WakePh.MainGlue.FS L (Spike.Lib.X64.Rt.rS0 L) Spike.Lib.X64.HelloPh.StartH0G.helloLsw 0#64 v)
      m1 σm, cA, fr.1, fr.2, σ.regs.fsBase.toBitVec,
    ⟨he, hn, hd, hpc, σ', ⟨hA.regs, hA.zmms, hA.status, fun r k hk => hA.so r k hk, ?_⟩, ⟨hF0', hCK, hAbsC⟩,
      hc ▸ rfl, ?_, ?_, ?_, rfl⟩, hRb, ⟨by dsimp only; omega, by dsimp only; omega⟩, hal, hra,
    by rw [hA.regs]; exact h15⟩
  · intro k hk
    obtain ⟨hk8, hklo, hkhi⟩ := hk
    dsimp only at hklo hkhi
    by_cases hlt : k < 16
    · obtain ⟨j, hj, hσ⟩ := hA.slot k ⟨hk8, by
        simp only [Spike.Lib.Region.fp, Spike.Lib.X64.Flow.HelloM.wcR, Region.callee, hD]; omega, by
        simp only [Spike.Lib.Region.fp, Spike.Lib.X64.Flow.HelloM.wcR, Region.callee]; omega⟩
      refine ⟨j, hj, ?_⟩
      show BitVec.ofInt 64 j = if k < 16 then σ.slot k else σm.slot (k - 88)
      simp only [hlt, ↓reduceIte]; exact hσ
    · have hk' : Region.Off (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
          (-80 + (-8 + k)) :=
        ⟨by omega, by simp only [Region.callee, Spike.Lib.X64.swR, hLsw]; omega, by
          simp only [Region.callee, Spike.Lib.X64.swR]; omega⟩
      have hkeep := hCK (-80 + (-8 + k)) hk' fun h' => by
        simp only [Region.Off, Region.callee] at h'; omega
      obtain ⟨j, hj, hσ⟩ := hAbsC.slot (-80 + (-8 + k)) hk'
      have e : (⟨((wcR (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
            Spike.Lib.X64.HelloPh.StartH0G.helloD).fp (-8)).base, -128, 40⟩ : Region).addr k =
          (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v).addr (-80 + (-8 + k)) := by
        show ((wcR (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
          Spike.Lib.X64.HelloPh.StartH0G.helloD).fp (-8)).addr k = _
        rw [Region.fp_addr, Spike.Lib.X64.Flow.HelloM.wcR, Region.callee_addr]
      refine ⟨j, by rw [e, hkeep, hj], ?_⟩
      show BitVec.ofInt 64 j = if k < 16 then σ.slot k else σm.slot (k - 88)
      simp only [hlt, ↓reduceIte]
      rw [show k - 88 = -80 + (-8 + k) by omega]; exact hσ
  · show σ'.slot (-48) = cA; simp [σ', h48]
  · show σ'.slot 0 = fr.1; simp [σ', h0]
  · show σ'.slot 8 = fr.2; simp [σ', h8]

end Spike.Lib.X64HelloCloneSeg

/-- info: 'Spike.Lib.X64HelloCloneSeg.cloneSegH_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCloneSeg.cloneSegH_of_mid
