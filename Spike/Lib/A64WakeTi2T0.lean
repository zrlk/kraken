/-
**wake.w's second `scc_rt_stack_take` call (from the second
`scc_rt_thread_init`) at the second instance** (AArch64; the `hatA` ti
discharger): `Rt.takeW_gen` at `ph2b` (`instOk2bP`, `takePh2b`) with the
runtime's words mapped and unmapped under `rtF`, as `StartTi.takeT`.

- `take2T`: the call's node obligations inside `SFactsSt` at `own2b`, at any
  source control (`Rt.takeW_gen` at the dummy control `A64Consumer.c0`, moved
  by `Ti2C0.takeW_c0`; no `CFacts` of the real control is asked).
-/
import Spike.Lib.A64WakeTi2L2
import Spike.Lib.A64WakeStartTiT0
import Spike.Lib.A64WakeTi2C0

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl SFacts)
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)

variable {P : MachineData → Prop}
variable {L : RuntimeLayout}

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFactsSt` at `own2b`** (`takeW_gen`
at `instOk2bP`, `takePh2b`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.sp0` (`hra`), at any source
control: proved at the dummy control `A64Consumer.c0` (`cfacts_c0`) and moved
by `Ti2C0.takeW_c0`, so the frag keeps only the state's facts. The real
control's facts (placement included) enter later, at `blk2_WS` / `node2_WS` /
`site2_WS` from `hc0`/`hpl0`. -/
theorem take2T {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s _ => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L)
      (fun s => own2b L a (ph2b (pcOf s))) rS (fun s => ph2b (pcOf s) / 8 % 2 = 0) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i P := by
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.A64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  refine Spike.Lib.A64.WakePh.Ti2C0.takeW_c0 (c0' := Spike.Lib.A64Consumer.c0) (fun s _ c' (h : Spike.Lib.A64Consumer.SFacts L.Λ _ _ rS _ (fun _ => none) s c') => h.toSt) ?_
  exact Spike.Lib.A64.Rt.takeW_gen (lbl := fun _ => none) (instOk2bP (rS := rS) hp hlo a hsite) (fun _ => rfl)
    (hp ▸ wake_takeIn) Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hR hal hRlo hhi _ rfl hra (takePh2b hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN
      hs.lock_freeN hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

/-- info: 'Spike.Lib.A64.WakePh.StartTi.take2T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms take2T

end Spike.Lib.A64.WakePh.StartTi
