/-
**hello.w's second `scc_rt_stack_take` call (from the second
`scc_rt_thread_init`) at the second instance** (x86-64; twin of
`Spike/Lib/A64HelloTi2T0.lean`, the `hatA` ti discharger, and of wake's
`X64WakeTi2T0` at `SccCode.helloCells`): `Rt.takeW_gen` at `ph2bH`
(`instOk2bPH`, `takePh2bH`) with the runtime's words mapped and unmapped
under `rtF`, as `StartTi.takeTH`.

- `take2TH`: the call's node obligations inside `SFactsSt` at `own2bH`, at
  any source control (`Rt.takeW_gen` at the dummy control `X64Consumer.c0`,
  moved by `Ti2C0.takeW_c0`; no `CFacts` of the real control is asked).

**Unlike AArch64**: as `StartTi.takeTH` (`Spike/Lib/X64HelloStartTiT0.lean`):
no `P` (x86-64's `TakeW` has none), no `hal`; `hRlo : R.lo ≤ -200`,
`hhi : 8 ≤ R.hi` (A64's `-208`, `0`); the return is to `Rt.x8L` (A64's
`ThreadInit.spL`, wake's x86-64 `Code.Ti.x7L`).
-/
import Spike.Lib.X64HelloTi2L
import Spike.Lib.X64HelloStartTiT0
import Spike.Lib.X64HelloTake2
import Spike.Lib.X64WakeTi2C0

namespace Spike.Lib.X64.HelloPh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl SFacts)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)
open Spike.Lib.X64.WakePh (WSep)

variable {L : RuntimeLayout}

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFactsSt` at `own2bH`** (`takeW_gen`
at `instOk2bPH`, `takePh2bH`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.x8` (`hra`), at any source
control: proved at the dummy control `X64Consumer.c0` (`cfacts_c0`) and moved
by `Ti2C0.takeW_c0`, so the frag keeps only the state's facts. The real
control's facts (placement included) enter later, at `blk2_WSH` /
`node2_WSH` / `site2_WSH` from `hc0`/`hpl0`. -/
theorem take2TH {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
    (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
      (fun s => own2bH L a (ph2bH (pcOf s))) rS (fun s => ph2bH (pcOf s) / 8 % 2 = 0) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  refine Spike.Lib.X64.WakePh.Ti2C0.takeW_c0 (c0' := Spike.Lib.X64Consumer.c0)
    (fun s _ c' (h : SFacts L.Λ _ _ rS _ (fun _ => none) s c') => h.toSt) ?_
  exact Spike.Lib.X64.Rt.takeW_gen (lbl := fun _ => none) (instOk2bPH (rS := rS) hp hlo a hsite) (fun _ => rfl)
    (hp ▸ hello_takeIn) Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hR hRlo hhi _ rfl hra
    (takePh2bH hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN
      hs.lock_freeN hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

end Spike.Lib.X64.HelloPh.StartTi

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.take2TH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.take2TH
