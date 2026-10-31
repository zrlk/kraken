/-
**`scc_rt_alloc`'s writes at any allocation site** (AArch64): `allocArena`
and `allocCtr` (`Spike/Lib/A64AllocG.lean`) for a call's premises at any
site (`Call.OKS`: a buffer allocation `newBuf` or, where the memory side
allows it, a box allocation `new` of one cell), the header's address by
`hdr_addrS`. At a box the header's store is below the held count's cell
(`ArenaW`'s `new` case, the arena allowing boxes, `hnew`).

- `allocArenaS`: every node allows `ArenaWr0` at every frame list.
- `allocCtrS`: only the counter's add writes the counter.
-/
import Spike.Lib.A64AllocG
import Spike.Lib.FrameNew

namespace Spike.Lib.A64.AllocG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide FrameRun FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64ConsumerA (WrAt FrameRun.eq_of_newBuf)
open Spike.Lib.A64.W0G (ArenaWr0)
open Spike.Lib.A64.Alloc (Call AllocW N iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call} {ar : Arena}

set_option hygiene false in
/-- A block of `scc_rt_alloc` writing nothing, as `W`'s component `C`. -/
local macro "nab " hb:term:max ok:term:max C:term : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR hal (by omega) (by omega))
    Spike.Lib.A64.Flow.BlkW.triv $C)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event, as `W`'s
component `C`. -/
local macro "nsi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac)) Spike.Lib.A64.Flow.NodeW.triv $C)

set_option hygiene false in
/-- The allocator's `ret`, writing nothing, as `W`'s component `C`. -/
local macro "nret " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr hI (blk := [iRet.toDir]) (lo := -160) (hi := 0)
    $hb (by pc_tac) (by dsimp only [N]; decide) hR hal (by omega) (by omega)) (List.cons_ne_nil _ _))
    Spike.Lib.A64.Flow.NodeW.triv $C)

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list and
any placement `lbl` (as `allocArena`), at any allocation site (`hq`), the
arena allowing boxes where the memory side does (`hnew`). -/
theorem allocArenaS (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) {lbl : Lbl} {p : Prog}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 ar lbl p s c fs) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → ∀ fs, ArenaWr0 ar lbl p s c fs :=
    fun _ _ h _ => arenaWr0_of_noWr h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 b0_ok C
  · nab h1 b1_ok C
  · nab h2 b2_ok C
  · nsi h3 C
  · nsi h4 C
  · nab h5 b3_ok C
  · refine NodeW.imp (nodeW_wr_ldop hI (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) h6 rfl
      (by pc_tac) fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨-, h10, -⟩ := hJ
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      rw [h10']
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, h10, -⟩, hL⟩ - fs c' fs' - L hW hne
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      exact (hne (by rw [hL L hW, h10', hctr]; rfl)).elim
  · nab h7 b4_ok C
  · nab h8 b5_ok C
  · nab h9 b6_ok C
  · nab h10 b7_ok C
  · nab h11 b9_ok C
  · nab h12 b11_ok C
  · nsi h13 C
  · nsi h14 C
  · nab h15 b12_ok C
  · refine NodeW.imp (nodeW_wr_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pc_tac)
      fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 h10⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -, -⟩, -, -, h10⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      have ha := hdr_addrS hq' hle hn28 h10
      rw [hL L hW]
      rcases hq'.site with ⟨a, ta, ws, ht, hev, hnum⟩ | ⟨hN, a, ws, ⟨_, ht⟩, hev, h1⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf hr ht hev hnum)
        refine .inr (.inr (.inr (.inl ⟨o.toNat, q.x, a, q.τ, q.e, ta, ws, q.n, by rw [← hctr]; rfl, ht,
          hev, hnum, ?_⟩)))
        show (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
        rw [ha, Spike.Lib.A64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
        omega
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht)
        refine .inr (.inr (.inr (.inr ⟨hnew hN, o.toNat, q.x, a, q.e, q.τ, ws, by rw [← hctr]; rfl, ⟨_, ht⟩, hev, ?_⟩)))
        show (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat < ar.heap + 16 * o.toNat + ar.off 1 q.τ
        rw [ha, Spike.Lib.A64.Alloc.Call.hdrAt, ← hheap, ← hoff, ← h1, hq'.off]
        omega
  · nab h17 b13_ok C
  · nret h18 C

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`** (as
`allocCtr`), at any allocation site (`hq`). -/
theorem allocCtrS (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) {Ctx : Frag isaLSE2}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → WrAt s ar.ctrLoc → Ctx s c :=
    fun _ _ h _ hW => (h _ hW).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c (by rw [← hI.labOk]; exact hA), fun _ h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 b0_ok C
  · nab h1 b1_ok C
  · nab h2 b2_ok C
  · nsi h3 C
  · nsi h4 C
  · nab h5 b3_ok C
  · nab h7 b4_ok C
  · nab h8 b5_ok C
  · nab h9 b6_ok C
  · nab h10 b7_ok C
  · nab h11 b9_ok C
  · nab h12 b11_ok C
  · nsi h13 C
  · nsi h14 C
  · nab h15 b12_ok C
  · refine NodeW.imp (nodeW_wr_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pc_tac)
      fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 h10⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -, -⟩, -, -, h10⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addrS hq' hle hn28 h10, Spike.Lib.A64.Alloc.Call.hdrAt, hheap] at ha
      have : ar.ctrLoc.addr.toNat = ar.ctr := by
        simp only [Arena.ctrLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
      omega
  · nab h17 b13_ok C
  · nret h18 C

end Spike.Lib.A64.AllocG

/-- info: 'Spike.Lib.A64.AllocG.allocArenaS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.AllocG.allocArenaS

/-- info: 'Spike.Lib.A64.AllocG.allocCtrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.AllocG.allocCtrS
