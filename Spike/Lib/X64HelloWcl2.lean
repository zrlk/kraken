/-
**hello.w's `wc_main` at its `clone`'s `syscall` inside the root's third level `RootWX.W2H`** (x86-64; the twin
of `Spike/Lib/A64HelloWcl2.lean`, the hello twin of `Spike/Lib/X64WakeWcl.lean` at `helloCells`, frame 128):
`H1GAH.wcl` at the root's level `W2H L (ntA L.lab) ar helloSrc Dt (ClH L) Ctx lbl lsize` and the clone fact
`StackM (r1Of L.lab)`.

The `syscall` is at `.Lwc_main.x25 + 94` (`WcSp6.wcNSH`), its resumption at `.x25 + 96`. Its source
`SpawnSrcH l ws c` is placed at `wc_main`'s slots (`WcSp6.FrWH` in `wcNSH`, `slots_absH`), given the frame's
cell is the box's (`cA.toNat = b`) and the slice and main's word are an entry state's (`FrMGH`), as wake's
`WclA` (`cA.toNat = b`, `m.toNat = tcb0`).

- `svc_factsH`: the `syscall`'s pc at the canonical base, off the sites; the resumption's `ph2bH` phase `0`.
- `svcInH`: the `syscall` cell in `helloCells`.
- `ab_offH`: the resumption is off the write abort's pcs (`HelloWf.siAbH`).
- `own_svc4H`: `ownGH` at the resumption's pc.
- `svc_clH`: a state at `wcNSH` is at the `syscall` cell and on the clone path (`ClH`).
- `slots_absH`: the five slots read an abstract state's words at its machine data.
- `wcl_W2H`: `W2H` and `StackM` at `wcNSH` from the placement at the slots (`Hs`).
- `wcl_W2GJ1H`: the same at a ghost of `GJ1H` (`SpawnPl.hpl_GJ1H`).

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.

## Differences from the AArch64 version

- The `syscall` is two bytes at a byte offset of `.x25` (AArch64: the `svc` word at `.sp6 + 4 · 25`), so the
  resumption is at `+ 96`; the cell's `CodeAt` is `code_field` at `svcInH` (AArch64: `WcW.cell1H`).
- The write abort's and the clone's phases come from wake's `nodeW_abSt_svc` / `nodeW_acSt_svc` (as
  `X64WakeWcl.wcl_W1`) rather than inline; the resumption's check is `HelloWf.siAbH` (AArch64:
  `ab_resH`/`ab_offH` through `lab_labCH`, a private lemma on x86-64).
- The slots are `wc_main`'s spills from `%rbp`: the slice at `-8`, `-24`, `-32`, main's word at `-40`, the cell
  at `-48` (AArch64: `-144`, `-128`, `-120`, `-112`, `-104` from the frame's base), so `slots_absH` is stated
  here (x86-64 has no `WcPl2`) and the bounds are `R.lo ≤ -48`, `0 ≤ R.hi` (AArch64: `R.lo ≤ -144`).
- `W2H` takes `ownGH` directly; no `Lft2` lift is needed (wake's `wcl_W1` lifts to `ownGXW`).
-/
import Spike.Lib.X64HelloRootWX
import Spike.Lib.X64HelloSpawnPl
import Spike.Lib.X64HelloH1ASrc
import Spike.Lib.X64HelloRefAbT
import Spike.Lib.X64HelloWcMidW
import Spike.Lib.X64HelloWcSp4W
import Spike.Lib.X64HelloClH
import Spike.Lib.X64WakeWfN
import Spike.Lib.X64WakeOwnGNode

namespace Spike.Lib.X64.HelloPh.Wcl2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.X64 (At CodeAt)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.HelloWc (FrMGH)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH x25L)
open Spike.Lib.X64.HelloPh.RootWX (W2H)
open Spike.Lib.X64.HelloPh.Ti2 (SlotPH SlotSlH)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib.X64HelloHMid (SBH slWsH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Kraken.Promising.Lower.X64 (CellAt op64)

/-- **The `syscall`'s pc** at the canonical base: its value, off the sites; the resumption's `ph2bH` `0`. -/
theorem svc_factsH : (Int64.ofNat 4203774 + Int64.ofNat 94).toBitVec.toNat = 4203868 ∧
    Spike.Lib.X64.HelloPh.okC 4203868 = true ∧ Spike.Lib.X64.HelloPh.ph2bHC 4203870 = 0 := by decide +kernel

/-- The clone's `syscall` in hello's cells. -/
theorem svcInH : blockAtB helloCells x25L 94 [(op64 .syscall, 2)] = true := by decide +kernel

/-- **The clone's resumption is off the write abort's pcs** at the code labels. -/
theorem ab_offH : Spike.Lib.X64.HelloWf.siAbH x25L 94 2 = true := by decide +kernel

variable {L : RuntimeLayout}

/-- **`ownGH` at the clone's resumption** (`.x25 + 96`) is `own2bH L a 0`. -/
theorem own_svc4H {a : BitVec 64}
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hs : s.st.2 = L.lab x25L + 94 + Int64.ofNat 2) :
    Spike.Lib.X64.HelloPh.ownGH L a s = Spike.Lib.X64.HelloPh.own2bH L a 0 := by
  have hp : pcOf s = 4203870 := by
    unfold pcOf
    rw [hs, show L.lab x25L = Int64.ofNat 4203774 from Spike.Lib.X64.HelloPh.WcSp4W.lab_x25H hlab]; rfl
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := Spike.Lib.X64.HelloPh.labs_eqH hlab (L := L)
  have hg : Spike.Lib.X64.HelloPh.Good2bH L s :=
    .inr (.inl (by unfold Spike.Lib.X64.WakePh.inPc; rw [e6, e7, hp]; omega))
  rw [Spike.Lib.X64.HelloPh.ownGH_2b hlab hg, hp, Spike.Lib.X64.HelloPh.ph2bH_eq, svc_factsH.2.2]

/-- **A state at `wcNSH` is at the `syscall` cell and on the clone path** (`ClH`: the clone's pc, a system call,
a `clone`). -/
theorem svc_clH (hp : L.prog = helloCells) {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (hA : At L.exe L.endPc R F (wcNSH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c) :
    CellAt s (op64 .syscall) 2 ∧ Spike.Lib.X64.HelloPh.ClH L s := by
  obtain ⟨hs, hn, -, hpc, σ, hAb, -, hJ⟩ := id hA
  have hc : CellAt s (op64 .syscall) 2 :=
    (Scc.Cert.Rt.X64.code_field L.lays rfl (Spike.Lib.X64.HelloPh.WcSp4W.onProgH hp svcInH) rfl s hs
      hn).cell0 rfl rfl hpc
  have hd := Spike.Lib.X64.HelloPh.WcSp6.wcNSH_call hJ
  rw [← hAb.regs] at hd
  exact ⟨hc, Spike.Lib.X64.Flow.HelloWc.wcNSH_clonePc hA, Scc.Sem.X64.atSyscall_of_cellAt hc, _, _, hd⟩

/-- **The five slots read an abstract state's words**: the cell at `-48`, main's word at `-40`, the slice's at
`-8`, `-24`, `-32`. -/
theorem slots_absH {R : Region} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {o : Spike.Lib.X64.SO} {m : MachineData}
    {σ : Spike.Lib.X64.AS} (hA : Spike.Lib.X64.Abs R o m σ) :
    SlotPH R (σ.slot (-48)).toNat (σ.slot (-40)).toNat m ∧
      SlotSlH R (σ.slot (-8)).toNat (σ.slot (-24)).toNat (σ.slot (-32)).toNat m := by
  obtain ⟨j48, e48, v48⟩ := hA.slot (-48) ⟨by decide, by omega, by omega⟩
  obtain ⟨j40, e40, v40⟩ := hA.slot (-40) ⟨by decide, by omega, by omega⟩
  obtain ⟨j8, e8, v8⟩ := hA.slot (-8) ⟨by decide, by omega, by omega⟩
  obtain ⟨j24, e24, v24⟩ := hA.slot (-24) ⟨by decide, by omega, by omega⟩
  obtain ⟨j32, e32, v32⟩ := hA.slot (-32) ⟨by decide, by omega, by omega⟩
  exact ⟨⟨j48, j40, e48, by rw [v48], e40, by rw [v40]⟩, ⟨j8, e8, by rw [v8]⟩,
    ⟨j24, e24, by rw [v24]⟩, ⟨j32, e32, by rw [v32]⟩⟩

section Wcl

variable {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {R : Region}
  {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel} {b : Nat}
  {ws : List TermRun.Word}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

set_option maxHeartbeats 1600000 in
/-- **`H1GAH.wcl` at the root's level** (wake's `wcl_W1`): at the clone's `syscall` (`wcNSH`), the frame's cell
the box's (`hcA`) and its slice and main's word an entry state's (`hFr`), the source at `SpawnSrcH l ws`, `W2H`
at no frames (its placement by `Hs` at the slots, as `SpawnPl.hpl_GJ1H`) and the clone fact `StackM`. -/
theorem wcl_W2H (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ lbl s c0 [])
    {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c [] ∧
        StackM (r1Of L.lab) s.st.1 := by
  intro s c sl me cA fr hA hsrc hcA hFr hSM
  obtain ⟨hc, hCl⟩ := svc_clH hp hA
  have hsys : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt hc
  have hpc : s.st.2 = L.lab x25L + 94 := hA.2.2.2.1
  have e25 : L.lab x25L = Int64.ofNat 4203774 := Spike.Lib.X64.HelloPh.WcSp4W.lab_x25H hlab
  have hP : pcOf s = 4203868 := by unfold pcOf; rw [hpc, e25]; exact svc_factsH.1
  have hpo := ((Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)).off s
    (by rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ, hP]; exact svc_factsH.2.1)).1
  -- the state's facts at `ownGH`
  have hS := Spike.Lib.X64Consumer.sfacts_syscallAt (Λ := L.Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.X64.PhRec.μ L) (own := fun _ => Spike.Lib.X64.HelloPh.own2bH L (ntA L.lab) 0)
    (Tk := fun _ => False) (Dt := Dt) (c := Spike.Lib.X64Consumer.c0) (s := s)
    Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hpo.noSite hpo.noTake hc (fun _ => ⟨rfl, Iff.rfl⟩) (fun h => h.elim)
    (fun k a ha e => (hpo.noAbort k a ha e).elim)
    (fun _ _ _ hw => by obtain ⟨_, _, hd⟩ := hCl.2.2; rw [hd] at hw; cases hw)
  have hst := hS.toSt.toSt2.congr (own' := Spike.Lib.X64.HelloPh.ownGH L (ntA L.lab))
    (Spike.Lib.X64.HelloPh.WcSp4W.own_x25H hlab (k := 94) (by decide) hpc)
    (fun s' h => own_svc4H hlab (by
      rw [Spike.Lib.X64.WakePh.keep_pc hc (Spike.Lib.X64.WakePh.keep_syscall hsys h), hpc]))
  -- the phases
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc →
      CodeAt s (L.lab x25L + 94) [(op64 .syscall, 2)] :=
    Scc.Cert.Rt.X64.code_field L.lays rfl (Spike.Lib.X64.HelloPh.WcSp4W.onProgH hp svcInH) rfl
  have htk : ∀ a, (Spike.Lib.X64.PhRec.μ L).site .take = some a → (L.lab x25L + 94).toBitVec.toNat ≠ a :=
    fun a ha e => hpo.noTake a ha (by unfold pcOf; rw [hpc]; exact e)
  have hna : ∀ s c', At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c' →
      ∀ a, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.archSetFs a) := fun s c' h a he => by
    obtain ⟨_, _, hd⟩ := (svc_clH hp h).2.2.2; rw [hd] at he; cases he
  have hsiA : L.lab x25L + Int64.ofNat 94 + Int64.ofNat 2 ∉ Spike.Lib.X64.WriteAb.abPcs L.lab :=
    Spike.Lib.X64.HelloWf.siAbH_sound hlab ab_offH
  have hab := (Spike.Lib.X64.WakeWf.nodeW_abSt_svc (Ab := Spike.Lib.X64.WriteAb.Ab L.lab) hcode htk hna
    (fun s c' h r hab => Spike.Lib.X64.WriteAb.not_ab_of_pc
      (show s.st.2 + Int64.ofNat 2 ∉ _ by rw [h.2.2.2.1]; exact hsiA) hab) s c hA).1
  have hac := (Spike.Lib.X64.WakeWf.nodeW_acSt_svc (Cl := Spike.Lib.X64.HelloPh.ClH L)
    (Ac := Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) hcode htk hna
    (fun s c' h => .inl (svc_clH hp h).2) s c hA).1
  -- the control, its placement, the writes and the abort sites
  have hctl := Spike.Lib.X64.HelloH1A.spawnSrcH_ctl (p := helloSrc) hsrc
  have hpl : PlacedSE L.Λ lbl s c [] := by
    obtain ⟨-, -, -, -, σ, hAb, -, hJ⟩ := id hA
    have hs := slots_absH hRlo hhi hAb
    obtain ⟨h8, -, h24, h32, h40, h48, -, -⟩ := hJ.1.1.2.2.2.2
    rw [h8, h24, h32, h40, h48, hcA] at hs
    exact Hs c sl me cA fr ⟨⟨l, b, ⟨rfl, rfl, hsrc⟩, hcA⟩, hFr⟩ s hs
  have hnw : ∀ L', ¬ Spike.Lib.X64ConsumerA.WrAt s L' := fun L' hL => by
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [Kraken.Promising.Lower.X64.exec_syscall hc] at h <;> cases h
  have hwr := Spike.Lib.X64.WakeWf.noWrC_of_noWr (ar := ar) (p := helloSrc) (lbl := lbl) (lsize := lsize)
    (Ctx := Ctx) (c := c) hnw []
  exact ⟨⟨rfl, Spike.Lib.X64.WakeWf.Wf.intro hst hab hac (fun _ h => h.2) (fun _ => hctl.1) hpl hwr.1 hwr.2
    hctl.2 (Spike.Lib.X64.WakeWf.abortWf_of_off hpo.noAbort)⟩, hSM⟩

/-- **`H1GAH.wcl` at a ghost of `GJ1H`** (rodata's label `lr`, the box's `l'` fresh at `lbl1`, main's id at the
TCB): `wcl_W2H` at the twice extended placement `upd lbl1 l' b'` (`SpawnPl.hpl_GJ1H`). -/
theorem wcl_W2GJ1H (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F' : MachineData → Prop} {tp : UInt64} (hl' : lbl1 l' = none)
    (hmt : lbl1 (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.X64HelloH2G.GJ1H L lbl1 lr R F' J1 tp) {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l' (slWsH lr) c → cA.toNat = b' → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx (Spike.Lib.X64ConsumerA.upd lbl1 l' b')
        lsize s c [] ∧ StackM (r1Of L.lab) s.st.1 :=
  wcl_W2H hp hlo hΛ hlab hsite hRlo hhi (Spike.Lib.X64.HelloPh.SpawnPl.hpl_GJ1H hl' hmt hG)

end Wcl

end Spike.Lib.X64.HelloPh.Wcl2

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2.own_svc4H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2.own_svc4H

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2.svc_clH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2.svc_clH

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2.slots_absH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2.slots_absH

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2.wcl_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2.wcl_W2H

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2.wcl_W2GJ1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2.wcl_W2GJ1H
