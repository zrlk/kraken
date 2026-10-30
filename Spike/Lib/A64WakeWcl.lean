/-
**`W1W` at the clone's `svc`** (AArch64): `HMidPA.wcl` (`H1G.wcl`'s
`W1W` half) at `ofPlaceW`'s layout.

At `wcNS` (`.L21_wc_main.sp6 + 4 * 13`, `svc #0`) the state's facts are
`sfacts_svcAt` at the constant instance `own2b … 0` moved to `ownG` (which is
`own2b … 0` at the pc and the resumption's, `own_sp6`, `own_svc4`); the call
is a `clone` (`WakeBoxW.clone_decode` at `wcNS`'s `x0`, `x2`, `x4`, `x8`), so
the state is on the clone path (`WakeOD.ClW`) and the threads abort's phase
holds there; the write abort's is off at the resumption (`ab_off`). The source
at `SpawnSrc l` is placed at `x9 = cA` (the cell `b`) and `x10 = m` (main's
id at `tcb0`), `l` fresh at the start.

- `ab_res`, `ab_off`: the write abort's pcs at the code labels, the
  resumption off them.
- `own_svc4`: `ownG` at the resumption's pc.
- `svc_cl`: a state at `wcNS` at the `svc` cell and on the clone path.
- `wcl_W1`: `W1W` at `wcNS`.
-/
import Spike.Lib.A64WakeWcW1I
import Spike.Lib.A64StubFacts
import Spike.Lib.A64WakeOwnGNode

namespace Spike.Lib.WakeWcl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (t2 kOf wcNS_clonePc)
open Spike.Lib.A64.WakePh.WcSp4 (wcNS)
open Spike.Lib.A64.WakePh (ownG own2b labs_eq Good2b inPc ownG_2b ph2b_eq ph2bC keep_svc keep_pc instOkW okPc_eq)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeBoxW (SpawnSrc)
open Spike.Lib.WakeLoadT (L0T tcb0)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- The labels of the write abort's pcs resolve in wake's program. -/
theorem ab_res : Spike.Lib.A64.AllocG.abLabs.all
    (fun x => (Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo wakeProg x).isSome) = true := by decide +kernel

/-- **The clone's resumption is off the write abort's pcs** at the code labels. -/
theorem ab_off : Int64.ofNat 2169292 + Int64.ofNat (4 * 13) + Int64.ofNat 4 ∉
    Spike.Lib.A64.WriteAb.abPcs (Spike.Lib.LowerA64.labC Spike.Lib.A64.WakePh.lo wakeProg) := by decide +kernel

/-- **`ownG` at the clone's resumption** is `own2b L a 0`. -/
theorem own_svc4 {L : Spike.Lib.A64.Rt.RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hs : s.st.2 = L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13) + Int64.ofNat 4) :
    ownG L a s = own2b L a 0 := by
  have hp : pcOf s = 2169348 := by unfold pcOf; rw [hs, Spike.Lib.A64.WakePh.WcSp4W.lab_sp6 hlab]; rfl
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inr (.inl (by unfold inPc; rw [e6, e7, hp]; omega))
  rw [ownG_2b hlab hg, hp, ph2b_eq, show ph2bC 2169348 = 0 by decide +kernel]

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

/-- **A state at `wcNS` is at the `svc` cell and on the clone path**
(`WakeOD.ClW`: the clone's pc, a system call, a `clone`). -/
theorem svc_cl (hd : WakeWcW1I.Ld hp i) {R : Region} {F : MachineData → Prop} {c0 : Ctl} {t k cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (hA : At (Ly).exe (Ly).endPc R F (wcNS (Ly).lab c0 t k cA m fr) s c) :
    Kraken.Promising.Lower.A64.CellAt s svcDir 4 ∧ WakeOD.ClW hp i s := by
  obtain ⟨hs, hn, -, hpc, σ, hAb, -, -, h0, -, h2, -, h4, h8, -⟩ := id hA
  have hc : Kraken.Promising.Lower.A64.CellAt s svcDir 4 :=
    Spike.Lib.A64.WakePh.WcW.cell1 (L := Ly) hd.pg (by decide +kernel) hs hn hpc
  exact ⟨hc, wcNS_clonePc hA, Scc.Sem.A64.atSvc_of_cellAt hc,
    WakeBoxW.clone_decode (by rw [hAb.regs]; exact h8) (by rw [hAb.regs]; exact h0) (by rw [hAb.regs]; exact h2)
      (by rw [hAb.regs]; exact h4)⟩

/-- **`W1W` at the clone's `svc`** (`HMidPA.wcl`): at `wcNS` with the frame's
cell `cA` the box's base `b` and main's word `m` its id `tcb0`, the source at
`SpawnSrc l`, `l` fresh at the start (`hl`). -/
theorem wcl_W1 (hd : WakeWcW1I.Ld hp i) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    (hl : L0T (Ly).Λ l = none) :
    ∀ s c cA m fr,
      At (Ly).exe (WakeSpawnR.endR hp i) R F (wcNS (Ly).lab c (t2 (Ly).lab) (kOf (Ly).lab) cA m fr) s c →
      cA.toNat = b → m.toNat = tcb0 (Ly).Λ → SpawnSrc l c → W1W hp i E Dt Ctx ls0 l b n s c [] := by
  intro s c cA m fr hA hcA hm hsrc
  rw [← hd.E] at hA
  obtain ⟨hc, hCl⟩ := svc_cl hp i hd hA
  obtain ⟨-, -, -, hpc, σ, hAb, -, -, -, -, -, -, -, -, h9, h10, -⟩ := id hA
  change s.st.2 = (Ly).lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13) at hpc
  have e6 := Spike.Lib.A64.WakePh.WcSp4W.lab_sp6 hd.lab
  have h13 := Spike.Lib.A64.WakePh.WcSp4W.sp6_facts 13 (by decide)
  have hP : pcOf s = 2169344 := by unfold pcOf; rw [hpc, e6, h13.1]
  have hpo := ((instOkW (L := Ly) hd.pg hd.lo (ntA (Ly).lab) (fun _ => False) hd.site (rS := ⟨0, 0⟩)).off s
    (by rw [okPc_eq hd.Λ, hP]; exact h13.2.2)).1
  have hsys := hCl.2.1
  have hS := Spike.Lib.A64Consumer.sfacts_svcAt (Λ := (Ly).Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.A64.PhRec.μ (Ly)) (own := fun _ => own2b (Ly) (ntA (Ly).lab) 0) (Tk := fun _ => False)
    (Dt := Dt) (c := Spike.Lib.A64Consumer.c0) (s := s) Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hpo.noSite
    hpo.noTake hc (fun _ => ⟨rfl, Iff.rfl⟩) (fun h => h.elim) (fun k a ha e => (hpo.noAbort k a ha e).elim)
    (fun _ _ _ hw => by obtain ⟨_, _, hd'⟩ := hCl.2.2; rw [hd'] at hw; cases hw)
  have hst := hS.toSt.toSt2.congr (own' := ownG (Ly) (ntA (Ly).lab))
    (Spike.Lib.A64.WakePh.WcSp4W.own_sp6 hd.lab (k := 13) (by decide) hpc)
    (fun s' h => own_svc4 hd.lab (by rw [keep_pc hc (keep_svc hsys h), hpc]))
  have hab4 : (Ly).lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13) + Int64.ofNat 4 ∉
      Spike.Lib.A64.WriteAb.abPcs (Ly).lab := by
    rw [Spike.Lib.A64.AllocG.abPcs_congr (Spike.Lib.A64.WakeWf.lab_labC hd.lab ab_res), e6]; exact ab_off
  have hnw : ∀ L, ¬ A64ConsumerA.WrAt s L := fun L hL => by
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [Kraken.Promising.Lower.A64.exec_svc hc] at h <;> cases h
  have hctl := WakeSrcCtl.spawnSrc_ctl hsrc
  unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hd.pa]
  refine Spike.Lib.A64.WakeWf.Wf.intro hst ⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ call hdc s' hs' hab => ?_,
      fun _ a ha e => (hpo.noTake a ha e).elim⟩
    ⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ hncl => (hncl hCl).elim, fun _ a ha e => (hpo.noTake a ha e).elim⟩
    (fun _ h => h.2) (fun _ => hctl.1) ?_ (fun _ _ _ L hL => (hnw L hL).elim)
    (fun hL => (hnw _ hL).elim) hctl.2 (Spike.Lib.A64.WakeWf.abortWf_of_off hpo.noAbort)
  · obtain ⟨r, -, rfl⟩ := (Scc.Sem.A64.mem_certSuccs_svc hc hdc).mp hs'
    exact (Spike.Lib.A64.WriteAb.not_ab_of_pc (show s.st.2 + Int64.ofNat 4 ∉ _ by rw [hpc]; exact hab4) hab).elim
  · refine WakeSrcCtl.placedSE_spawn hsrc ?_ ?_
    · show _ = some s.st.1.regs.X9.toBitVec.toNat
      rw [show A64ConsumerA.upd (L0T (Ly).Λ) l b l = some b from Spike.Lib.A64.WakePh.PlacedLy.lbl_l _ l b,
        hAb.regs, h9, hcA]
    · show _ = some s.st.1.regs.X10.toBitVec.toNat
      rw [show A64ConsumerA.upd (L0T (Ly).Λ) l b (WakeT1.mainTidLbl 2) = some (tcb0 (Ly).Λ) from
        Spike.Lib.A64.WakePh.PlacedLy.lbl_me b (Spike.Lib.A64.WakePh.PlacedLy.ne_of_fresh hl), hAb.regs, h10, hm]

end Spike.Lib.WakeWcl

/-- info: 'Spike.Lib.WakeWcl.ab_res' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcl.ab_res

/-- info: 'Spike.Lib.WakeWcl.ab_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcl.ab_off

/-- info: 'Spike.Lib.WakeWcl.own_svc4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcl.own_svc4

/-- info: 'Spike.Lib.WakeWcl.svc_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcl.svc_cl

/-- info: 'Spike.Lib.WakeWcl.wcl_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcl.wcl_W1
