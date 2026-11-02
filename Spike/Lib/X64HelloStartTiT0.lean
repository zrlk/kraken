/-
**hello.w's `scc_rt_stack_take` call (from `scc_rt_thread_init`) at the
first instance** (x86-64; twin of `Spike/Lib/A64HelloStartTiT0.lean`,
wake's `X64WakeStartTiT0` at `SccCode.helloCells`): `Rt.takeW_gen` at `phH`
(`instOkHS`, `takePhH`) with the runtime's words mapped and unmapped under
`rtF` (`takeTH`), and the labels the call's pcs are decided from
(`take_labsH`). The program-independent pieces (`StartTi.takeA`,
`okPc_of_blkPh`, `nrB`, and `Flow.Ret0`'s / `Rt.Take`'s parser
equalities) are wake's.

- `take_labsH`: the labels at hello's canonical base (wake's `+ 37`).
- `hello_takeIn`: the take's code in `helloCells`.
- `takeTH`: the call's node obligations inside `SFacts` at `phH`.

## Differences from the AArch64 version

As wake's x86-64 `StartTiT0`: no `P` (x86-64's `TakeW` has none); no
`hal`; `hRlo : R.lo ≤ -200`, `hhi : 8 ≤ R.hi` (A64's `-208`, `0`);
`takePhH` takes the counters' distinctness `c1`-`c8` (from `WSep`'s fields)
rather than `WSep`. The call returns to `scc_rt_thread_init`'s `.x8`
(`Rt.x8L`; A64's `.sp0`, wake's x86-64 `.x7`: hello's `scc_rt_main` has a
setup block). hello's x86-64 addresses (`scc_rt_stack_take` at `4199732`,
the take site at `4200314`) are wake's `+ 37` (A64's `+ 36`).
-/
import Spike.Lib.X64HelloStartTiL
import Spike.Lib.X64WakeStartTiT0

namespace Spike.Lib.X64.HelloPh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl SFacts CFacts)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)
open Spike.Lib.X64.Flow.Ret0.StackTake
open Spike.Lib.X64.WakePh (WSep)

variable {L : RuntimeLayout}

/-- The labels the take's pcs are decided from, at hello's canonical base. -/
theorem take_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199732 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199747 ∧
    (_root_.Executable.labels L.exe).label clsL = Int64.ofNat 4199793 ∧
    (_root_.Executable.labels L.exe).label doneL = Int64.ofNat 4199897 ∧
    (_root_.Executable.labels L.exe).label spinL = Int64.ofNat 4199962 ∧
    (_root_.Executable.labels L.exe).label lockedL = Int64.ofNat 4199998 ∧
    (_root_.Executable.labels L.exe).label bumpL = Int64.ofNat 4200139 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4200263 ∧
    (_root_.Executable.labels L.exe).label takenL = Int64.ofNat 4200303 ∧
    (_root_.Executable.labels L.exe).label siteL = Int64.ofNat 4200314 ∧
    (_root_.Executable.labels L.exe).label ".Lscc_rt_stack_take.full" = Int64.ofNat 4200249 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Rt.x8L = Int64.ofNat 4199606 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- The take's code in helloCells. -/
theorem hello_takeIn : stackTakeIn helloCells = true := hello_rtCodeIn0.take

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFacts` at `phH`** (`takeW_gen`
at `instOkHS`, `takePhH`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.x8` (`hra`). -/
theorem takeTH {a : BitVec 64} {rS : Range} {lbl' : Lbl} {c0 : Spike.Lib.Ctl} {R : Spike.Lib.Region}
    {F : MachineData → Prop}
    (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
      (fun s => phH (pcOf s) / 8 % 2 = 0) lbl' s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  exact Spike.Lib.X64.Rt.takeW_gen (instOkHS (a := a) (rS := rS) hp hlo hlab) (fun _ => rfl) (hp ▸ hello_takeIn) hC0
    hR hRlo hhi q hq hra
    (takePhH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
      hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

end Spike.Lib.X64.HelloPh.StartTi

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.take_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.take_labsH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.hello_takeIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.hello_takeIn

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.takeTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.takeTH
