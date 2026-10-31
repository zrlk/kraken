/-
**`wake_start_wc_segW`'s `hti` at the root's frame `Pz rS0`** (x86-64;
twin of `Spike/Lib/A64WakeStartH0Ti.lean`):
`StartTi.startTi_WSP` at `scc_rt_start`'s entry region `R := entryR E`,
the first stack `rS := Rt.rS0 L` (`k0 := 0`), the first TCB, the level's
per-state facts `X0 := WakeWf.X0W L ax` at the take pc `ax`, and the site
frame `P := Pz rS0`.

Discharged here: the callee's region (`callee_ok`), its frames off the pool
(`bandI_entry`, the entry stack clear of the pool), the stack's stability
(`stackM_entry`: `outS_of_sub` moved into the callees), the TCB's words as
runtime words (`tcb_rtWord`), the labels and the take site.

`X0W` across `scc_rt_thread_init … scc_rt_stack_release` (`x0W_ti`): off
the take site below the clone (`clonePc_eq`); at the site the range
`rS0 = r0Of` (`RootP.r0Of_rS0`), not yet in private memory from the site
frame `Pz rS0` (`RootP.x0W_sitePz`, the site off the clone).

- `clonePc_eq`, `siteL_eq`: the clone's and the take site's pcs at the
  canonical base;
- `bandI_entry`: `[-248, 8]` of `thread_init`'s region below the entry `sp`
  is off the pool;
- `stackM_entry`: `StackM rS0` kept by `thread_init`'s and
  `stack_take`'s regions;
- `tcb_rtWord`: a word of the first TCB is a runtime word;
- `x0W_ti`: `startTi_WSP`'s `hX0` (off the site) and `hXs` (at the site);
- `hti_root`: `hti` in `MainGlue.wake_start_wc_segW`'s shape.

**Unlike AArch64**: stated at any `RuntimeLayout` (A64's `htiW_place` at
`ofPlaceW`); the arena's offsets are the premise `hoff` on the runtime's
words (A64's `offW_arW` from `ctrSep_of_rtWordsOk`; at a placed output
`LowerX64.rtWords_offArena` and `hctr_of_placeOKAt` give it). The region is
`((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8` (x86-64's
return-address word: `scc_rt_start` itself a callee of the entry); the
off-site `X0W` is decided from `labs_eq`'s literals (A64's `freeLabs`/`cv`).
-/
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeRootP
import Spike.Lib.X64WakeStartTiP
import Spike.Lib.X64WakeStartPlaceB

namespace Spike.Lib.X64.WakePh.RootTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rS0 rS0_sub)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts Pz)
open Spike.Lib.X64.WakeWf (RunWf X0W)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTi (BandI)
open Spike.Lib.X64.WakePh.MainGlue (tcbS)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib (Arena FragS Region)

variable {L : RuntimeLayout}

/-- **The clone's pc** at the canonical base (`.Lwc_main.x21 + 46`). -/
theorem clonePc_eq (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    Spike.Lib.X64.Flow.WakeWc.clonePc L = 4203443 := by
  show (L.lab ".Lwc_main.x21" + 46).toBitVec.toNat = _
  rw [hlab ".Lwc_main.x21" 4203397 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **The take site's pc** at the canonical base (`Tcb2W.tcb_labs`). -/
theorem siteL_eq (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 4200277 := by
  rw [show L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 from
    (Spike.Lib.X64.WakePh.Tcb2W.tcb_labs hlab).2.2.2.2.2]
  decide

/-- **`thread_init`'s frame `[-248, 8]` below the entry `sp` is off the
pool** (`StartPlace.offE`: offsets `[-304, -48]` of the entry region). -/
theorem bandI_entry {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    BandI L (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) (-248) := by
  intro k h1 h2
  rw [Region.callee_addr, Region.callee_addr]
  exact Spike.Lib.X64.WakePh.StartPlace.offE hE (by omega) (by omega)

/-- **`StackM rS0` is kept by `thread_init`'s and `stack_take`'s regions**:
`rS0` is off the entry region (`outS_of_sub`), so off its callees
(`out_callee`). -/
theorem stackM_entry {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    Spike.Lib.X64.FStable (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) (StackM (rS0 L)) ∧
      Spike.Lib.X64.FStable
        ((((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8)
        (StackM (rS0 L)) := by
  have hR := Spike.Lib.X64.Rt.entryR_ok hE
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub L (rS0_sub L)
  have ho0 := Spike.Lib.X64.Rt.outS_of_sub L hE (rS0_sub L)
  have hR1 := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR
    (by show (-65536 : Int) ≤ _; decide) (by decide) (by show (-8 : Int) < 0; decide)
    (by show (-8 : Int) + 8 ≤ 0; decide)
  have hR2 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR1
    (by show (-296 : Int) ≤ _; decide) (by decide) (by show (-48 - 0 : Int) < 8; decide)
    (by show (-48 - 0 : Int) + 8 ≤ 8; decide)
  have ho1 := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR (kc := -8) (lo' := -296) (hi' := 8)
    (by show (-65536 : Int) ≤ _; decide) (by decide) (by show (-8 : Int) < 0; decide)
    (by show (-8 : Int) + 8 ≤ 0; decide) ho0
  have ho2 := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -248) (hi' := 8)
    (by show (-296 : Int) ≤ _; decide) (by decide) (by show (-48 - 0 : Int) < 8; decide)
    (by show (-48 - 0 : Int) + 8 ≤ 8; decide) ho1
  have ho3 := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR2 (kc := -48 - 0) (lo' := -200) (hi' := 8)
    (by show (-248 : Int) ≤ _; decide) (by decide) (by show (-48 - 0 : Int) < 8; decide)
    (by show (-48 - 0 : Int) + 8 ≤ 8; decide) ho2
  exact ⟨Spike.Lib.X64.Flow.Ret0.stackM_stable hfit ho2, Spike.Lib.X64.Flow.Ret0.stackM_stable hfit ho3⟩

/-- **A word of the first TCB is a runtime word** (`StartU.tcb_fld`). -/
theorem tcb_rtWord {b : BitVec 64} (hb : b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tcbS L)) : b ∈ L.rtWords := by
  obtain ⟨j, hj, rfl⟩ := Spike.Lib.X64.Rt.StartU.tcb_fld hb
  rcases j with _ | j
  · simpa using L.pin_mem
  · exact L.fld_mem (by omega)

/-- **`X0W` in `scc_rt_thread_init … scc_rt_stack_release`**: off the take
site, below the clone (`startTi_WSP`'s `hX0`); at the site, from the site's
range `rS0` and its first word unmapped (`Pz`, `startTi_WSP`'s `hXs` at any
frame `F`). -/
theorem x0W_ti {ax : Int64}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    (∀ s, Spike.Lib.X64.WakePh.inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0W L ax s) ∧
    (∀ (F : MachineData → Prop) s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS0 L → F s.st.1 → Pz (rS0 L) s.st.1 → X0W L ax s) := by
  have hc := clonePc_eq hlab
  have hst := siteL_eq hlab
  have hrel := (Spike.Lib.X64.WakePh.labs_eq hlab (L := L)).2.2.2.1
  refine ⟨fun s h hne => ⟨?_, fun he => absurd (he.trans hax) hne⟩, fun _ s hp hr _ hz => ?_⟩
  · unfold Spike.Lib.X64.WakePh.inPc at h
    rw [hc]; omega
  · refine Spike.Lib.X64.WakePh.RootP.x0W_sitePz (by rw [hc, hst]; decide) s hp
      (hr.trans Spike.Lib.X64.WakePh.RootP.r0Of_rS0.symm) ?_
    rw [Spike.Lib.X64.WakePh.RootP.r0Of_rS0]; exact hz

section Gen

variable {a : BitVec 64} {lbl' : Lbl} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64}

set_option maxHeartbeats 800000 in
/-- **`wake_start_wc_segW`'s `hti`** at `R := entryR E`, `rS := rS0`,
`k0 := 0`, `X0 := X0W L ax` and `P := Pz rS0`: `startTi_WSP` with the
region, stack, word, label and site premises discharged, for every frame
`F'` inside `F`. -/
theorem hti_root (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : Spike.Lib.X64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m)
    (hoff : ∀ w ∈ L.rtWords, ¬ (ar.heap ≤ w.toNat ∧ w.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨w, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable ((entryR E).callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L (rS0 L)) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WS L a ar p Dt Cl Ctx lbl lsize frM (X0W L ax)) (Spike.Lib.X64.PhRec.K L (rS0 L))
        L.exe L.endPc (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (StackM (rS0 L))
        ⟨g, tcbS L, 0#64, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L (Pz (rS0 L)) i := by
  intro F' _ _ hF' g hra
  have hR := Spike.Lib.X64.Rt.entryR_ok hE
  have hR1 := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR
    (by show (-65536 : Int) ≤ _; decide) (by decide) (by show (-8 : Int) < 0; decide)
    (by show (-8 : Int) + 8 ≤ 0; decide)
  have hR2 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR1
    (by show (-296 : Int) ≤ _; decide) (by decide) (by show (-48 - 0 : Int) < 8; decide)
    (by show (-48 - 0 : Int) + 8 ≤ 8; decide)
  have hSM := stackM_entry hE
  have hX := x0W_ti hlab hax
  exact Spike.Lib.X64.WakePh.StartTi.startTi_WSP hp hlo hlab hsite hcl hc0 hpl0 hX.1 (bandI_entry hE) hΛ hs hro
    hC0 hR2 (show (-248 : Int) ≤ -248 by decide) (show (8 : Int) ≤ 8 by decide) (fun m h => hFr m (hF' m h))
    ⟨g, tcbS L, 0#64, c0⟩ rfl rfl hra
    (by show rS0 L = _; rw [Spike.Lib.X64.Rt.stacksA_lab0]) (rS0_sub L) hSM.1 hSM.2
    (fun b hb => hoff b (tcb_rtWord hb)) (hoff _ L.lock_mem) (hoff _ L.next_mem) (hX.2 F')

end Gen

end Spike.Lib.X64.WakePh.RootTi

/-- info: 'Spike.Lib.X64.WakePh.RootTi.clonePc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.clonePc_eq

/-- info: 'Spike.Lib.X64.WakePh.RootTi.siteL_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.siteL_eq

/-- info: 'Spike.Lib.X64.WakePh.RootTi.bandI_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.bandI_entry

/-- info: 'Spike.Lib.X64.WakePh.RootTi.stackM_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.stackM_entry

/-- info: 'Spike.Lib.X64.WakePh.RootTi.tcb_rtWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.tcb_rtWord

/-- info: 'Spike.Lib.X64.WakePh.RootTi.x0W_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.x0W_ti

/-- info: 'Spike.Lib.X64.WakePh.RootTi.hti_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootTi.hti_root
