/-
**wake.w's `scc_rt_stack_take` call (from `scc_rt_thread_init`) at the
first instance** (x86-64; twin of `Spike/Lib/A64WakeStartTiT0.lean`): the
facts `StartTi.takeA_WS` / `takeB_WS` move inside `WS`. `Rt.takeW_gen` at
`phW` (`instOkWS`, `takePhW`) with the runtime's words mapped and unmapped
under `rtF` (`takeT`), the labels the call's pcs are decided from
(`take_labs`).

- `take_labs`: the labels at the canonical base.
- `takeA`: the nodes `takeA_WS` covers (up to the free count's load).
- `okPc_of_blkPh`, `nrB`: a covered block's pcs off the sites; a block
  without `ret` meets any `hret`.
- `wake_takeIn`: the take's code in `wakeCells`.
- `takeT`: the call's node obligations inside `SFacts` at `phW`.

**Unlike AArch64**: no `P` (x86-64's `TakeW` has none); no `hal`;
`hRlo : R.lo ≤ -200`, `hhi : 8 ≤ R.hi` (A64's `-208`, `0`); the call
returns to `scc_rt_thread_init`'s `.x7` (`Code.Ti.x7L`, A64's `.sp0`);
`takePhW` takes the counters' distinctness `c1`-`c8` (from `WSep`'s
fields) rather than `WSep`; `okPc_of_blkPh` is at `cellOff` offsets and
`nrB`'s return address is the slot at `%rsp`; A64's single-instruction
parser equalities (`swp_eq`, `ldr_eq`, `stlr_eq`, `ldadd_eq`, `nop_eq`) are
`Flow.Ret0`'s `swpBlk_eq`, `ldnBlk_eq`, `unlBlk_eq`, `nxtBlk_eq`
(`Spike/Lib/X64Ret0.lean`) and `Rt.Take.nopBlk_eq`
(`Spike/Lib/Rt/X64RtTake.lean`), reused, not restated. `takeA`
lists x86-64's nodes up to `.ldn` (`.d0` … `.d59`, `.sp0`, `.swp`,
`.sp14`, `.lk0`, `.ldn`).
-/
import Spike.Lib.X64WakeStartTiK

namespace Spike.Lib.X64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl SFacts CFacts)
open Spike.Lib.X64 (ND)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA)
open Spike.Lib.X64.Flow.Ret0.StackTake

variable {L : RuntimeLayout}

/-- The labels the take's pcs are decided from, at the canonical base. -/
theorem take_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199695 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199710 ∧
    (_root_.Executable.labels L.exe).label clsL = Int64.ofNat 4199756 ∧
    (_root_.Executable.labels L.exe).label doneL = Int64.ofNat 4199860 ∧
    (_root_.Executable.labels L.exe).label spinL = Int64.ofNat 4199925 ∧
    (_root_.Executable.labels L.exe).label lockedL = Int64.ofNat 4199961 ∧
    (_root_.Executable.labels L.exe).label bumpL = Int64.ofNat 4200102 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4200226 ∧
    (_root_.Executable.labels L.exe).label takenL = Int64.ofNat 4200266 ∧
    (_root_.Executable.labels L.exe).label siteL = Int64.ofNat 4200277 ∧
    (_root_.Executable.labels L.exe).label ".Lscc_rt_stack_take.full" = Int64.ofNat 4200212 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Rt.Code.Ti.x7L = Int64.ofNat 4199569 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **The nodes `takeA_WS` covers**: up to the free count's load. -/
def takeA : TK → Bool
  | .e | .entry | .cls | .j1 | .d0 | .d7 | .d26 | .d33 | .d52 | .d59 | .sp0 | .swp | .sp14 | .lk0 | .ldn => true
  | _ => false

/-- A covered block's pcs are off the sites (`blkPh`'s first conjunct). -/
theorem okPc_of_blkPh {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List (Directive × Nat)} (h : Spike.Lib.X64Consumer.blkPh okP phf d lab pc ra blk = true) :
    ∀ j < blk.length, okP (pc + Int64.ofNat (Spike.Lib.X64.cellOff blk j)).toBitVec.toNat = true := fun j hj => by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- A block without `ret` meets any `hret`. -/
theorem nrB {blk : List (Directive × Nat)} (hb : Spike.Lib.X64Consumer.noRetBlk blk = true) {n : ND}
    {lb : Label → Int64} {ra' : Int64} : ∀ σ (c : Spike.Lib.Ctl), n.J σ c → ∀ j (hj : j < blk.length),
      Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((Spike.Lib.X64.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (Spike.Lib.X64.arun lb (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp) = ra' :=
  fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hb j hj hr).elim

/-- The take's code in wakeCells. -/
theorem wake_takeIn : stackTakeIn wakeCells = true := Spike.Lib.X64.WakePh.wake_rtCodeIn0.take

set_option maxHeartbeats 800000 in
/-- **The take's node obligations inside `SFacts` at `phW`** (`takeW_gen`
at `instOkWS`, `takePhW`), its words mapped and unmapped under `rtF`
(`hFr`), returning to `scc_rt_thread_init`'s `.x7` (`hra`). -/
theorem takeT {a : BitVec 64} {rS : Range} {lbl' : Lbl} {c0 : Spike.Lib.Ctl} {R : Region} {F : MachineData → Prop}
    (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, TakeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
      (fun s => phW (pcOf s) / 8 % 2 = 0) lbl' s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  exact Spike.Lib.X64.Rt.takeW_gen (instOkWS (a := a) (rS := rS) hp hlo hlab) (fun _ => rfl) (hp ▸ wake_takeIn) hC0
    hR hRlo hhi q hq hra
    (takePhW hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
      hs.lock_a hs.next_a)
    (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
    (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
    (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
    (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm)) hrS hsub hro hSM

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.take_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.take_labs

/-- info: 'Spike.Lib.X64.WakePh.StartTi.okPc_of_blkPh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.okPc_of_blkPh

/-- info: 'Spike.Lib.X64.WakePh.StartTi.nrB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.nrB

/-- info: 'Spike.Lib.X64.WakePh.StartTi.wake_takeIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.wake_takeIn

/-- info: 'Spike.Lib.X64.WakePh.StartTi.takeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.takeT
