/-
**`scc_rt_alloc`'s writes at any allocation site** (x86-64; the twin of
`Spike/Lib/A64AllocGS.lean`, name for name): `allocArena` and `allocCtr`
(`Spike/Lib/X64AllocG.lean`) for a call's premises at any site
(`Call.OKS`, `Spike/Lib/X64AllocSite.lean`: a buffer allocation `newBuf`
or, where the memory side allows it, a box allocation `new` of one cell),
the header's address by `hdr_addrS` (`Spike/Lib/X64AllocGSite.lean`). At a
box the header's store is below the held count's cell (`ArenaW`'s `new`
case, the arena allowing boxes, `hnew`).

- `allocArenaS`: every node allows `ArenaWr0` at every frame list.
- `allocCtrS`: only the counter's add writes the counter.

Where x86-64 differs from AArch64 (as in `allocArena`/`allocCtr`): the
counter's add is a `lock xaddq` through `%rcx` (`ctr_addrS`), A64's `ldadd`
through `x10`; the header's store is through `%rcx`; there are `FI` nodes
(undefined flags); the region is `[-160, 8)` (the return address at `0`),
with no alignment premise (`hal`).
-/
import Spike.Lib.X64AllocGSite
import Spike.Lib.FrameNew

namespace Spike.Lib.X64.AllocG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FrameRun FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND At bAddr)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64ConsumerA (WrAt)
open Spike.Lib.X64.W0G (ArenaWr0)
open Spike.Lib.X64.Alloc (Call AllocW N iRet bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok
  bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call} {ar : Arena}

set_option hygiene false in
/-- A block of `scc_rt_alloc` writing nothing, as `W`'s component `C`. -/
local macro "nab " hb:term:max ok:term:max C:term : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR (by omega) (by omega)) Spike.Lib.X64.BlkW.triv $C)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event, as `W`'s
component `C`. -/
local macro "nsi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac)) Spike.Lib.X64.NodeW.triv $C)

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags, as `W`'s
component `C`. -/
local macro "nfi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_fi hI $hb rfl (by pc_tac)) Spike.Lib.X64.NodeW.triv $C)

set_option hygiene false in
/-- The allocator's `ret`, writing nothing, as `W`'s component `C`. -/
local macro "nret " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (Spike.Lib.LowerX64.BlkW.nodeW (blkW_noWr hI (blk := [(iRet.toDir, 1)]) (lo := -160)
    (hi := 8) $hb rfl (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide)
    hR (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv $C)

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list and
any placement `lbl` (as `allocArena`), at any allocation site (`hq`), the
arena allowing boxes where the memory side does (`hnew`). -/
theorem allocArenaS (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) {lbl : Lbl} {p : Prog}
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 ar lbl p s c fs) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → ∀ fs, ArenaWr0 ar lbl p s c fs :=
    fun _ _ h _ => arenaWr0_of_noWr h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 bPro_ok C
  · nab h1 bChk_ok C
  · nab h2 bJ1_ok C
  · nsi h3 C
  · nab h4 bC1_ok C
  · refine NodeW.imp (nodeW_wr_xadd hI (b := .rcx) (k := 0) (r := .rax) h5 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨-, hcx, -⟩ := hJ
      rw [ctr_addrS (hq m hF) hcx]
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, hcx, -⟩, hF, hL⟩ - fs c' fs' - L hW hne
      exact (hne (by rw [hL L hW, ctr_addrS (hq _ hF) hcx, hctr]; rfl)).elim
  · nab h6 bC2_ok C
  · nab h7 bJ2_ok C
  · nab h8 bSlow_ok C
  · nab h9 bJ3_ok C
  · nab h10 bFull_ok C
  · nab h11 bO0_ok C
  · nfi h12 C
  · nab h13 bO1_ok C
  · nfi h14 C
  · nab h15 bO2_ok C
  · nsi h16 C
  · nab h17 bO3_ok C
  · nfi h18 C
  · nab h19 bO4_ok C
  · nfi h20 C
  · nab h21 bO5_ok C
  · nfi h22 C
  · nab h23 bO6_ok C
  · nfi h24 C
  · nab h25 bO7_ok C
  · nfi h26 C
  · nab h27 bO8_ok C
  · refine NodeW.imp (nodeW_wr_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 hcx⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      have ha := hdr_addrS hq' hle hn28 hcx
      rw [hL L hW]
      rcases hq'.site with ⟨a, ta, ws, ht, hev, hnum⟩ | ⟨hN, a, ws, ⟨_, ht⟩, hev, h1⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Spike.Lib.X64ConsumerA.FrameRun.eq_of_newBuf hr ht hev hnum)
        refine .inr (.inr (.inr (.inl ⟨o.toNat, q.x, a, q.τ, q.e, ta, ws, q.n, by rw [← hctr]; rfl, ht,
          hev, hnum, ?_⟩)))
        show (bAddr σ.regs .rcx 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
        rw [ha, Spike.Lib.X64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
        omega
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht)
        refine .inr (.inr (.inr (.inr ⟨hnew hN, o.toNat, q.x, a, q.e, q.τ, ws, by rw [← hctr]; rfl, ⟨_, ht⟩, hev, ?_⟩)))
        show (bAddr σ.regs .rcx 0).toNat < ar.heap + 16 * o.toNat + ar.off 1 q.τ
        rw [ha, Spike.Lib.X64.Alloc.Call.hdrAt, ← hheap, ← hoff, ← h1, hq'.off]
        omega
  · nab h29 bO9_ok C
  · nret h30 C

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`** (as
`allocCtr`), at any allocation site (`hq`). -/
theorem allocCtrS (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) {Ctx : Frag isa}
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → WrAt s ar.ctrLoc → Ctx s c :=
    fun _ _ h _ hW => (h _ hW).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c (by rw [← hI.labOk]; exact hA), fun _ h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hI.labOk]
  · nab h0 bPro_ok C
  · nab h1 bChk_ok C
  · nab h2 bJ1_ok C
  · nsi h3 C
  · nab h4 bC1_ok C
  · nab h6 bC2_ok C
  · nab h7 bJ2_ok C
  · nab h8 bSlow_ok C
  · nab h9 bJ3_ok C
  · nab h10 bFull_ok C
  · nab h11 bO0_ok C
  · nfi h12 C
  · nab h13 bO1_ok C
  · nfi h14 C
  · nab h15 bO2_ok C
  · nsi h16 C
  · nab h17 bO3_ok C
  · nfi h18 C
  · nab h19 bO4_ok C
  · nfi h20 C
  · nab h21 bO5_ok C
  · nfi h22 C
  · nab h23 bO6_ok C
  · nfi h24 C
  · nab h25 bO7_ok C
  · nfi h26 C
  · nab h27 bO8_ok C
  · refine NodeW.imp (nodeW_wr_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 hcx⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addrS hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, hheap] at ha
      have : ar.ctrLoc.addr.toNat = ar.ctr := by
        simp only [Arena.ctrLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
      omega
  · nab h29 bO9_ok C
  · nret h30 C

end Spike.Lib.X64.AllocG

/-- info: 'Spike.Lib.X64.AllocG.allocArenaS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.AllocG.allocArenaS

/-- info: 'Spike.Lib.X64.AllocG.allocCtrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.AllocG.allocCtrS
