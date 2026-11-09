/-
**`W1W` at the clone's `syscall`** (x86-64, the twin of
`Spike/Lib/A64WakeWcl.lean`): `HMidPA.wcl` (`H1G.wcl`) at `ofPlaceWX`'s
layout.

At `wcNS` (`.Lwc_main.x3 + 46`, `syscall`) the state's facts are
`sfacts_syscallAt` at the constant instance `own2b … 0`, moved to `ownG`
(which is `own2b … 0` at the pc and the resumption's, `own_x21`,
`own_res`) and then to `ownG`'s extension `ownGXW` (`Lft2` at the node,
`nodeL2`: both TCB words held on the pool, `cls_poolW`). The call is a
`clone` (`WcClone.wcNS_call`), so the state is on the clone path
(`WakeOD.ClW`) and the threads abort's phase holds there; the write abort's
is off at the resumption (`ab_off`). The source at `SpawnSrc l` is placed at
`%r12 = cA` (the cell `b`) and `%rbx = m` (main's id at `tcb0`), `l` fresh
at the start.

- `svcIn`: the `syscall` cell in wake's cells.
- `ab_res`, `ab_off`: the write abort's pcs at the code labels, the
  resumption off them.
- `own_res`: `ownG` at the resumption's pc.
- `svc_cl`: a state at `wcNS` at the `syscall` cell and on the clone path.
- `wcl_W1`: `W1W` at `wcNS` (`H1GOf.WclG`).

**Unlike AArch64**: the level owns `ownGXW`, so the state facts are lifted
from `ownG` by `Lft2` at the node (`nodeL2`), which reads `wc_main`'s frame
on the pool (`hb : BandOnP R (-80) 8`, from `BoxPure` by
`H1GOf.band_of_box`; A64 has no band premise), and A13's data part
(`hA13`, `ownGXW`'s separations); `ab_off` is at x86-64's code labels and
`abPcs` (the threads abort's pcs are not checked: the clone path `ClW`
covers `AcSt`); the source's two
places are `%r12`/`%rbx` (A64: `x9`/`x10`); the loader's facts are taken as
`hpa`, `hwp`, `hlo0` (A64: `WakeWcW1I.Ld`); the assembly is a parameter
`asm`. No absolute address appears in a statement.
-/
import Spike.Lib.X64WakeH1GOf
import Spike.Lib.X64StubFacts

namespace Spike.Lib.X64.WakeWcl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi Asm cellsOf)
open SccCode (wakeCells)
open Spike.Lib (Region FragS PlaceWX)
open Spike.Lib.X64 (At CodeAt)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Flow.WakeWc (t2 kOf)
open Spike.Lib.X64.WakePh (ownG own2b ownGXW labs_eq Good2b ownG_2b ph2b_eq ph2bC keep_syscall keep_pc
  BandOnP lo)
open Spike.Lib.X64.WakePh.WcClone (wcNS x21L)
open Spike.Lib.X64.WakePh.WcSp4W (lab_x21 own_x21)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2 WrAt)
open Spike.Lib.X64.WakeBoxW (SpawnSrc)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Kraken.Promising.Lower.X64 (CellAt op64)

/-- The clone's `syscall` in wake's cells. -/
theorem svcIn : Scc.Cert.Rt.X64.blockAtB wakeCells x21L 46 [(op64 .syscall, 2)] = true := by decide +kernel

/-- The labels of the write abort's pcs resolve in wake's cells. -/
theorem ab_res : Spike.Lib.X64.AllocG.abLabs.all (fun x => (codeLabel lo wakeCells x).isSome) = true := by
  decide +kernel

/-- **The clone's resumption is off the write abort's pcs** at the code labels. -/
theorem ab_off : List.elem (Int64.ofNat 4203435 + Int64.ofNat 46 + Int64.ofNat 2)
    (Spike.Lib.X64.WriteAb.abPcs (Spike.Lib.LowerX64.labC lo wakeCells)) = false := by decide +kernel

/-- **`ownG` at the clone's resumption** (`.x21 + 48`) is `own2b L a 0`. -/
theorem own_res {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hs : s.st.2 = L.lab x21L + 46 + Int64.ofNat 2) : ownG L a s = own2b L a 0 := by
  have e21 : L.lab x21L = Int64.ofNat 4203435 := lab_x21 hlab
  have hp : pcOf s = 4203483 := by unfold pcOf; rw [hs, e21]; rfl
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inr (.inl (by unfold Spike.Lib.X64.WakePh.inPc; rw [e6, e7, hp]; omega))
  rw [ownG_2b hlab hg, hp, ph2b_eq, show ph2bC 4203483 = 0 by decide +kernel]

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **A state at `wcNS` is at the `syscall` cell and on the clone path**
(`WakeOD.ClW`: the clone's pc, a system call, a `clone`). -/
theorem svc_cl (hpg : o.prog = wakeCells) {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (hA : At (Ly).exe (Ly).endPc R F (wcNS (Ly).lab c0 t k cA m fr) s c) :
    CellAt s (op64 .syscall) 2 ∧ WakeOD.ClW hp i s := by
  have hpL : (Ly).prog = wakeCells := hpg
  obtain ⟨hs, hn, -, hpc, σ, hAb, -, hJ⟩ := id hA
  have hc : CellAt s (op64 .syscall) 2 :=
    (Scc.Cert.Rt.X64.code_field (Ly).lays rfl (Spike.Lib.X64.WakePh.WcSp4W.onProg hpL svcIn) rfl s hs hn).cell0 rfl rfl hpc
  have hd := Spike.Lib.X64.WakePh.WcClone.wcNS_call hJ
  rw [← hAb.regs] at hd
  exact ⟨hc, Spike.Lib.X64.Flow.WakeWc.wcNS_clonePc hA, Scc.Sem.X64.atSyscall_of_cellAt hc, _, _, hd⟩

set_option maxHeartbeats 1600000 in
/-- **`W1W` at the clone's `syscall`** (`HMidPA.wcl`): at `wcNS` with the
frame's cell `cA` the box's base `b` and main's word `m` its id `tcb0`, the
source at `SpawnSrc l`, `l` fresh at the start (`hl`), `wc_main`'s frame on
the pool (`hb`). -/
theorem wcl_W1 (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    (hl : L0T (Ly).Λ l = none) (hb : BandOnP (Ly) R (-80) 8) :
    WakeH1GOf.WclG asm hp i E Dt Ctx ls0 l b n R F := by
  intro s c cA m fr hA hcA hm hsrc
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hpL : (Ly).prog = wakeCells := hpg
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hsite := PlaceWX.site_ofPlaceWX hp i
  have hE : (Ly).endPc = WakeH1Inv.endR hp i := by
    show Scc.Cert.Rt.X64.endOf _ (Ly).prog _ = _; rw [hpL]
  rw [← hE] at hA
  -- the node's code, pc and step
  have hcode : ∀ s : State, s.exe = (Ly).exe → s.endPc = (Ly).endPc →
      CodeAt s ((Ly).lab x21L + 46) [(op64 .syscall, 2)] :=
    Scc.Cert.Rt.X64.code_field (Ly).lays rfl (Spike.Lib.X64.WakePh.WcSp4W.onProg hpL svcIn) rfl
  have e21 : (Ly).lab x21L = Int64.ofNat 4203435 := lab_x21 hlab
  have hokpc : Spike.Lib.X64.WakePh.okC ((Ly).lab x21L + 46).toBitVec.toNat = true := by
    rw [e21]; decide +kernel
  have hcell : ∀ s c', At (Ly).exe (Ly).endPc R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c' →
      CellAt s (op64 .syscall) 2 := fun s c' h => (svc_cl hp i hpg h).1
  have hk : ∀ s c', At (Ly).exe (Ly).endPc R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c' →
      ∀ s', StSucc (Spike.Lib.X64.PhRec.μ (Ly)) s s' → Spike.Lib.X64.WakePh.Keep s s' ∧
        s'.st.2 = (Ly).lab x21L + 46 + Int64.ofNat 2 := fun s c' h s' hs' => by
    have hc := hcell s c' h
    have hK := keep_syscall (Scc.Sem.X64.atSyscall_of_cellAt hc) hs'
    exact ⟨hK, by rw [keep_pc hc hK, h.2.2.2.1]; rfl⟩
  -- the state's facts at `ownGXW`
  obtain ⟨hc, hCl⟩ := svc_cl hp i hpg hA
  have hsys : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt hc
  have hpc : s.st.2 = (Ly).lab x21L + 46 := hA.2.2.2.1
  have hP := ((Spike.Lib.X64.WakePh.instOkW hpL hlo (ntA (Ly).lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)).off s
    (by unfold pcOf; rw [hpc, Spike.Lib.X64.WakePh.okPc_eq hΛ]; exact hokpc)).1
  have hS := Spike.Lib.X64Consumer.sfacts_syscallAt (Λ := (Ly).Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.X64.PhRec.μ (Ly)) (own := fun _ => own2b (Ly) (ntA (Ly).lab) 0) (Tk := fun _ => False)
    (Dt := Dt) (c := Spike.Lib.X64Consumer.c0) (s := s) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hP.noSite
    hP.noTake hc (fun _ => ⟨rfl, Iff.rfl⟩) (fun h => h.elim) (fun k a ha e => (hP.noAbort k a ha e).elim)
    (fun _ _ _ hw => by obtain ⟨_, _, hd⟩ := hCl.2.2; rw [hd] at hw; cases hw)
  have hG : SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s Dt :=
    hS.toSt.toSt2.congr (own_x21 hlab (k := 46) (by decide) hpc)
      (fun s' hs' => own_res hlab (hk s c hA s' hs').2)
  have hL := (Spike.Lib.X64.WakePh.nodeL2 (Λ := (Ly).Λ) (Dt := Dt) hlab (Spike.Lib.X64.WakePh.tcbSep_W hp i)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13) (sz := 2)
    (P := Spike.Lib.X64.WakePh.OwnTi2.QW) (Spike.Lib.X64.WakePh.cls_poolW hlab hb) hk
    (by show Spike.Lib.X64.WakePh.OwnTi2.QW ((Ly).lab x21L + 46).toBitVec.toNat ∧
        Spike.Lib.X64.WakePh.OwnTi2.QW ((Ly).lab x21L + 46 + Int64.ofNat 2).toBitVec.toNat
        rw [e21]; decide +kernel)
    (by dsimp only [wcNS]; decide)
    (fun s c' h hns => by
      have h2 : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt (hcell s c' h)
      rw [h2] at hns; cases hns)
    s c hA).1
  have hX : SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s Dt := hL hG
  -- the phases
  have hsiA : (Ly).lab x21L + Int64.ofNat 46 + Int64.ofNat 2 ∉ Spike.Lib.X64.WriteAb.abPcs (Ly).lab := fun hm => by
    rw [e21, Spike.Lib.X64.AllocG.abPcs_congr (Spike.Lib.X64.WakeWf.lab_labC hlab ab_res)] at hm
    have h := List.elem_iff.mpr hm
    rw [ab_off] at h; cases h
  have hna : ∀ s c', At (Ly).exe (Ly).endPc R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c' →
      ∀ a, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.archSetFs a) := fun s c' h a he => by
    obtain ⟨_, _, hd⟩ := (svc_cl hp i hpg h).2.2.2; rw [hd] at he; cases he
  have htk := Spike.Lib.X64.WakePh.CalWf.htkC hlab hsite hokpc
  have hab := (Spike.Lib.X64.WakeWf.nodeW_abSt_svc (Ab := Spike.Lib.X64.WriteAb.Ab (Ly).lab) hcode htk hna
    (fun s c' h r hab => Spike.Lib.X64.WriteAb.not_ab_of_pc
      (show s.st.2 + Int64.ofNat 2 ∉ _ by rw [h.2.2.2.1]; exact hsiA) hab) s c hA).1
  have hac := (Spike.Lib.X64.WakeWf.nodeW_acSt_svc (Cl := WakeOD.ClW hp i)
    (Ac := Spike.Lib.X64.ThreadsAb.Ac (Ly).lab pfxM) hcode htk hna
    (fun s c' h => .inl (svc_cl hp i hpg h).2) s c hA).1
  -- the control, its placement, the writes and the abort sites
  have hctl := WakeSrcCtl.spawnSrc_ctl hsrc
  obtain ⟨-, -, -, -, σ, hAb, -, ⟨-, h12, hbx, -⟩, -⟩ := hA
  have e12 : (s.st.1.regs.get64 .r12).toNat = b := by rw [hAb.regs, h12, hcA]
  have ebx : (s.st.1.regs.get64 .rbx).toNat = tcb0 (Ly).Λ := by rw [hAb.regs, hbx, hm]
  have hpl := WakeSrcCtl.placedSE_spawn (Λ := (Ly).Λ) (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) hsrc
    (by show _ = some (s.st.1.regs.get64 .r12).toNat
        rw [e12]; exact Spike.Lib.X64.WakePh.PlacedLy.lbl_l _ l b)
    (by show _ = some (s.st.1.regs.get64 .rbx).toNat
        rw [ebx]; exact Spike.Lib.X64.WakePh.PlacedLy.lbl_me b (Spike.Lib.X64.WakePh.PlacedLy.ne_of_fresh hl))
  have hnw : ∀ L, ¬ WrAt s L := fun L hL => by
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [Kraken.Promising.Lower.X64.exec_syscall hc] at h <;> cases h
  have hwr := Spike.Lib.X64.WakeWf.noWrC_of_noWr (ar := WakeOD.arW hp i) (p := X64WakeT1.wakeSrc)
    (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) (Ctx := fun _ _ _ => False)
    (c := c) hnw []
  unfold WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact Spike.Lib.X64.WakeWf.Wf.intro hX hab hac (fun _ h => h.2) (fun _ => hctl.1) hpl hwr.1 hwr.2 hctl.2
    (Spike.Lib.X64.WakeWf.abortWf_of_off hP.noAbort)

end Spike.Lib.X64.WakeWcl

/-- info: 'Spike.Lib.X64.WakeWcl.svcIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.svcIn

/-- info: 'Spike.Lib.X64.WakeWcl.ab_res' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.ab_res

/-- info: 'Spike.Lib.X64.WakeWcl.ab_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.ab_off

/-- info: 'Spike.Lib.X64.WakeWcl.own_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.own_res

/-- info: 'Spike.Lib.X64.WakeWcl.svc_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.svc_cl

/-- info: 'Spike.Lib.X64.WakeWcl.wcl_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcl.wcl_W1
