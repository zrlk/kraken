/-
**wake.w's `scc_rt_stack_take` call (from `scc_rt_thread_init`) at the
first instance** (AArch64): the facts `StartTi.takeA_WS` / `takeB_WS` move
inside `WS`. `Rt.takeW_gen` at `phW` (`instOkWS`, `takePhW`) with the
runtime's words mapped and unmapped under `rtF` (`takeT`), the labels the
call's pcs are decided from (`take_labs`), and the code's instructions.

- `take_labs`: the labels at the canonical base.
- `takeA`: the nodes `takeA_WS` covers (up to the free count's load).
- `okPc_of_blkPh`, `nrB`: a covered block's pcs off the sites; a block
  without `ret` meets any `hret`.
- `swp_eq`, `ldr_eq`, `stlr_eq`, `ldadd_eq`, `nop_eq`: the single
  instructions' code.
- `takeT`: the call's node obligations inside `SFacts` at `phW`.
-/
import Spike.Lib.A64WakeStartTiL2

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (codeT_eq)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl SFacts)
open Spike.Lib.A64.Flow (ND)
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)
open Spike.Lib.A64.Flow.Ret0.StackTake

variable {P : MachineData → Prop}
variable {L : RuntimeLayout}

/-- The labels the take's pcs are decided from, at the canonical base. -/
theorem take_labs (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 2165400 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 2165420 ∧
    (_root_.Executable.labels L.exe).label clsL = Int64.ofNat 2165456 ∧
    (_root_.Executable.labels L.exe).label doneL = Int64.ofNat 2165560 ∧
    (_root_.Executable.labels L.exe).label spinL = Int64.ofNat 2165632 ∧
    (_root_.Executable.labels L.exe).label lockedL = Int64.ofNat 2165668 ∧
    (_root_.Executable.labels L.exe).label bumpL = Int64.ofNat 2165800 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 2165900 ∧
    (_root_.Executable.labels L.exe).label takenL = Int64.ofNat 2165932 ∧
    (_root_.Executable.labels L.exe).label siteL = Int64.ofNat 2165940 ∧
    (_root_.Executable.labels L.exe).label ".L6_scc_rt_stack_take.8_full" = Int64.ofNat 2165888 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.ThreadInit.spL = Int64.ofNat 2165272 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **The nodes `takeA_WS` covers**: up to the free count's load. -/
def takeA : TK → Bool
  | .e | .entry | .cls | .j1 | .d0 | .d2 | .d7 | .d9 | .d14 | .d16 | .sp0 | .swp | .sp3 | .lk0 | .ldn => true
  | _ => false

/-- A covered block's pcs are off the sites (`blkPh`'s first conjunct). -/
theorem okPc_of_blkPh {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (h : Spike.Lib.A64Consumer.blkPh okP phf d lab pc ra blk = true) :
    ∀ j < blk.length, okP (pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- A block without `ret` meets any `hret`. -/
theorem nrB {blk : List Directive} (hb : Spike.Lib.A64Consumer.noRetBlk blk = true) {n : ND} {lb : Label → Int64}
    {ra' : Int64} : ∀ σ (c : Ctl), n.J σ c → ∀ j (hj : j < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
  fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hb j hj r hr).elim

theorem swp_eq : parseAArch64("swpal x9, x11, [x10]") = [Spike.Lib.A64.WakeWf.swpDir .acqRel .X9 .X11 .X10] := by
  decide
theorem ldr_eq : parseAArch64("ldr x9, [x10]") = [Spike.Lib.A64.Flow.ldrDir .X9 .X10 0] := by decide
theorem stlr_eq : parseAArch64("stlr x9, [x10]") = [Spike.Lib.A64.WakeWf.stlrDir .X9 .X10] := by decide
theorem ldadd_eq : parseAArch64("ldaddal x9, x11, [x10]") = [Spike.Lib.A64.Flow.Ret0.AllocTcb.rmwDir] := by decide
theorem nop_eq : parseAArch64("nop") = [.instr ⟨.W64, .NOP⟩] := by decide

/-- The take's code in wakeProg. -/
theorem wake_takeIn : stackTakeIn wakeProg = true := Spike.Lib.A64.WakePh.wake_rtCodeIn0.take

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFacts` at `phW`** (`takeW_gen`
at `instOkWS`, `takePhW`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.sp0` (`hra`). -/
theorem takeT {a : BitVec 64} {rS : Range} {lbl' : Lbl} {c0 : Ctl} {R : Spike.Lib.Region} {F : MachineData → Prop}
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.ThreadInit.spL).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
      (fun s => phW (pcOf s) / 8 % 2 = 0) lbl' s c) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i P := by
  have hlk : Spike.Lib.A64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.A64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.A64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  exact Spike.Lib.A64.Rt.takeW_gen (instOkWS (a := a) (rS := rS) hp hlo hlab) (fun _ => rfl) (hp ▸ wake_takeIn) hC0
    hR hal hRlo hhi q hq hra (takePhW hp hlo hΛ hlab hs)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

/-- info: 'Spike.Lib.A64.WakePh.StartTi.take_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms take_labs

/-- info: 'Spike.Lib.A64.WakePh.StartTi.okPc_of_blkPh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms okPc_of_blkPh

/-- info: 'Spike.Lib.A64.WakePh.StartTi.nrB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nrB

/-- info: 'Spike.Lib.A64.WakePh.StartTi.takeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms takeT

end Spike.Lib.A64.WakePh.StartTi
