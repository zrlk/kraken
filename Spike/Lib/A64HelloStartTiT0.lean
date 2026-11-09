/-
**hello.w's `scc_rt_stack_take` call (from `scc_rt_thread_init`) at the
first instance** (AArch64, the `hti` chain; twin of
`Spike/Lib/A64WakeStartTiT0.lean` at helloProg): the facts
`StartTi.takeA_WSH` / `takeB_WSH` move inside `WSH`. `Rt.takeW_gen` at `phH`
(`instOkHS`, `takePhH`) with the runtime's words mapped and unmapped under
`rtF` (`takeTH`), and the labels the call's pcs are decided from
(`take_labsH`). The program-independent pieces (`takeA`, `okPc_of_blkPh`,
`nrB`, `swp_eq`, `ldr_eq`, `stlr_eq`, `ldadd_eq`, `nop_eq`) are wake's.

- `take_labsH`: the labels at hello's canonical base (wake's `+ 36`).
- `takeTH`: the call's node obligations inside `SFacts` at `phH`.
-/
import Spike.Lib.A64HelloStartTiL
import Spike.Lib.A64WakeStartTiT0

namespace Spike.Lib.A64.HelloPh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (codeT_eq)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl SFacts)
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)
open Spike.Lib.A64.Flow.Ret0.StackTake
open Spike.Lib.A64.WakePh (WSep)

variable {P : MachineData → Prop}
variable {L : RuntimeLayout}

/-- The labels the take's pcs are decided from, at hello's canonical base. -/
theorem take_labsH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 2165440 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 2165460 ∧
    (_root_.Executable.labels L.exe).label clsL = Int64.ofNat 2165496 ∧
    (_root_.Executable.labels L.exe).label doneL = Int64.ofNat 2165600 ∧
    (_root_.Executable.labels L.exe).label spinL = Int64.ofNat 2165672 ∧
    (_root_.Executable.labels L.exe).label lockedL = Int64.ofNat 2165708 ∧
    (_root_.Executable.labels L.exe).label bumpL = Int64.ofNat 2165840 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 2165940 ∧
    (_root_.Executable.labels L.exe).label takenL = Int64.ofNat 2165972 ∧
    (_root_.Executable.labels L.exe).label siteL = Int64.ofNat 2165980 ∧
    (_root_.Executable.labels L.exe).label ".L6_scc_rt_stack_take.8_full" = Int64.ofNat 2165928 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = Int64.ofNat 2165312 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- The take's code in helloProg. -/
theorem hello_takeIn : stackTakeIn SccCode.helloProg = true := hello_rtCodeIn0.take

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFacts` at `phH`** (`takeW_gen`
at `instOkHS`, `takePhH`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.sp0` (`hra`). -/
theorem takeTH {a : BitVec 64} {rS : Range} {lbl' : Lbl} {c0 : Ctl} {R : Spike.Lib.Region} {F : MachineData → Prop}
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
      (fun s => phH (pcOf s) / 8 % 2 = 0) lbl' s c) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F (StackM rS)
      q i P := by
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.A64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  exact Spike.Lib.A64.Rt.takeW_gen (instOkHS (a := a) (rS := rS) hp hlo hlab) (fun _ => rfl) (hp ▸ hello_takeIn)
    hC0 hR hal hRlo hhi q hq hra (takePhH hp hlo hΛ hlab hs)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

end Spike.Lib.A64.HelloPh.StartTi

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.take_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.take_labsH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.takeTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.takeTH
