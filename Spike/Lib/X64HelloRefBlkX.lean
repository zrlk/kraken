/-
**The refusal path's test and three blocks hold both TCB self words, at hello's level 2** (x86-64 only; the
`ownGHXW` companion of `Spike/Lib/X64HelloRefBlk.lean`, as `Spike/Lib/X64HelloRefAbX.lean` is of
`Spike/Lib/X64HelloRefAb.lean`): the `testq` row at `.x25 + 96`, the `je` block at `.x25 + 99`, `.x26`'s block
and `.spawnfail5`'s, inside main's 128-byte frame on the first stack (`PreH`'s region). Their pcs are in `[.x25,
.stk)` (`InCH`), where main holds both words (`OwnSp4.cls_cH`); `.spawnfail5`'s run ends at `scc_rt_abort` with
the return address `.Lwc_main.x5` pushed at `-136`, where it holds both too (`selfOwnH` on the pool, `selfOwnWH`'s
abort disjunct). So both appended maps may be appended at every node (`CstOkH`).

- `bandOn_preH`: main's band `[-144, 8]` of `PreH`'s region lies in the first stack.
- `fin_cH`: `CstH` where a block's run ends inside `InCH` with its static `%rsp` offset in the band.
- `fl_cstH`: `CstH` where `.spawnfail5`'s run ends (`scc_rt_abort`, `.x27` at `-136`).
- `refCstBlkH`: `CstOkH` at the row and the three blocks, in `BlkH`'s shape.

No absolute address appears in a statement here.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. The row and blocks are `RefBlkH.refBlkH`'s (`ts`, `je`,
`x26`, `fl`); the classes are `OwnCstX`'s (`blkW_cstOkHB`, `nodeW_cstOkHK`).
-/
import Spike.Lib.X64HelloRefBlk
import Spike.Lib.X64HelloOwnWcSp4X

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (ND BlkW NodeW Abs At arun)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerA (rsp_of_abs)
open Spike.Lib.X64.WakePh (inPc spPool raAddr raSp abFns BandOnP tcbM tM)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64.HelloPh (lo CstH CstOkH InCH selfOwnH_iffC ownSH_of_self ownSWH_of_self tWH blkW_cstOkHB
  nodeW_cstOkHK)
open Spike.Lib.X64.HelloPh.RefBlkH (clH refRangeH refPcH lab_clH lab_clNH ref_ne_site)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (fNS flB flL)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP jeB x26B x26L)
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L)
open Spike.Lib.X64.ThreadsAb (raT)
open Scc.Cert.Rt.X64 (blockAtB codeT_eq code_field)
open Scc.Sem.X64 (privLoad)
open SccCode (helloCells)
open Kraken.Promising.Lower.X64 (CellAt)

variable {L : RuntimeLayout}

/-- **Main's band on the first stack** from `PreH`'s region: `R.base + 96` at the first stack's top, `[-144, 8]`
inside it. -/
theorem bandOn_preH {R : Region} (hR : R.OK) (hlo : R.lo ≤ -384) (hhi : 16 ≤ R.hi)
    (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) : BandOnP L R (-144) 8 := by
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have e := Region.addr_toNat_of hR (k := k) (by omega) (by omega)
  omega

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)

include hlab in
/-- **`CstH` where a block's run ends** inside `InCH` (`hpc`), its static `%rsp` offset in `[-144, 8]` (`hso`). -/
theorem fin_cH {R : Region} (hb : BandOnP L R (-144) 8) {nd : ND} {blk : List (Directive × Nat)}
    (hso : -144 ≤ (soRun blk nd.o).sp ∧ (soRun blk nd.o).sp ≤ 8)
    (hpc : ∀ σ c, nd.J σ c → InCH (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).pc.toBitVec.toNat) :
    ∀ σ c, nd.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).so m (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).pc) →
      CstH L (tM L) (tWH L) s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso
  rw [← arun_so L.lab blk ⟨nd.pc, nd.o, σ⟩] at ho
  refine Spike.Lib.X64.HelloPh.OwnSp4.cls_cH hlab hb s (by unfold pcOf; rw [hs]; exact hpc σ c hJ)
    ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact rsp_of_abs hA

include hlab in
/-- **`CstH` where `.spawnfail5`'s run ends**: at `scc_rt_abort` on the pool (`selfOwnH`), the return address
`.Lwc_main.x5` pushed at `-136` (`selfOwnWH`'s abort disjunct). -/
theorem fl_cstH {R : Region} (hb : BandOnP L R (-144) 8) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    {cP : Spike.Lib.Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    (σ : Spike.Lib.X64.AS) (s : State) (m : MachineData)
    (hA : Abs R (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).so m
      (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).σ)
    (hs : s.st = (m, (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).pc)) :
    CstH L (tM L) (tWH L) s := by
  have hoE : (fNS L.lab cP sl cA me .fl).o = oP := rfl
  have hpE : (fNS L.lab cP sl cA me .fl).pc = L.lab flL := rfl
  have hm : s.st.1 = m := by rw [hs]
  have hsp : spPool L s := by
    have hr : m.regs.rsp.toBitVec = R.addr (soRun flB oP).sp := by
      have := rsp_of_abs hA; rwa [arun_so] at this
    unfold spPool; rw [hm, hr]
    exact hb _ (by decide +kernel) (by decide +kernel)
  rw [hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.flB_run] at hA hs
  obtain ⟨-, -, -, oAb, oTw, -⟩ := refRangeH
  have e8 := lab_clNH hlab oAb (L := L)
  have e9 := lab_clNH hlab oTw (L := L)
  have hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat := by unfold pcOf; rw [hs]
  have hin : pcOf s ∈ raSp L := by rw [hpc]; simp [raSp, abFns]
  have hrA : raAddr L s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
  have hld : privLoad s (raAddr L s) = some (L.lab ".Lwc_main.x5").toBitVec := by
    rw [hrA, hm, rsp_of_abs hA]
    obtain ⟨j, hj1, hj2⟩ := hA.slot (-136) ⟨by decide, by omega, by omega⟩
    unfold privLoad
    rw [hm, hj1, Option.map_some, hj2, ← raT_x27H hlab]
    simp only [Spike.Lib.upd_apply, ↓reduceIte, raT, Int64.toBitVec_add]; rfl
  have hinP : inPc L "scc_rt_abort" "scc_rt_thr_worker" s := by
    unfold inPc; rw [hpc, e8, e9]; exact ⟨Nat.le_refl _, refRangeH.2.2.2.2.2.2.2.2.2.1⟩
  have hge : 4198500 ≤ pcOf s := by
    rw [hpc, e8]; have : clH "scc_rt_abort" = 4202524 := by decide +kernel
    omega
  exact ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inl ⟨hsp, hge⟩)), ownSWH_of_self (.inr (.inr ⟨hinP, hld⟩))⟩

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)

include hp hlo hlab in
set_option maxHeartbeats 1600000 in
/-- **`CstOkH` at the refusal path's test and three blocks** (`RefBlkH.refBlkH`'s row and blocks): their pcs in
`InCH` on main's frame (`bandOn_preH`, `OwnSp4.cls_cH`), `.spawnfail5`'s end at `scc_rt_abort` (`fl_cstH`), no
write of the two words (the `testq` flag-only, the blocks covered); `tcbM` off `ownGH`'s words (`hs`, `ha`) and
`tcbWH` off `ownGHX`'s (`hW`). -/
theorem refCstBlkH (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab]) (lbl : Lbl) (l : WeakMem.AllocLabel)
    (ws : List TermRun.Word) :
    BlkH L lbl l ws (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L (ntA L.lab) s) (fun _ _ => False) := by
  intro R m0 cP sl cA me hpre
  obtain ⟨-, -, -, -, hR, -, hRlo, hhi, hbase⟩ := hpre
  have hb := bandOn_preH hR hRlo hhi hbase
  have hsite := Spike.Lib.X64.HelloPh.siteH hp hlo hlab
  have hcls := Spike.Lib.X64.HelloPh.OwnSp4.cls_cH hlab hb
  have e25 := lab_clH hlab refRangeH.1 (L := L)
  have e26 : L.lab x26L = Int64.ofNat (clH x26L) := lab_clH hlab (by decide +kernel)
  have efl : L.lab flL = Int64.ofNat (clH flL) := lab_clH hlab (by decide +kernel)
  have hin := Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failInB
  simp only [Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hts, hje⟩, hx26⟩, hfl⟩ := hin
  have hns : ∀ {nd : ND} {blk : List (Directive × Nat)},
      (∀ j < blk.length, refPcH (nd.pc + Int64.ofNat (Spike.Lib.X64.cellOff blk j)).toBitVec.toNat = true) →
      ∀ a, (Spike.Lib.X64.PhRec.μ L).site .take = some a → ∀ k < blk.length,
        (nd.pc + Int64.ofNat (Spike.Lib.X64.cellOff blk k)).toBitVec.toNat ≠ a := by
    intro nd blk hq a h k hk
    rw [hsite] at h; cases h
    exact ref_ne_site hlab (hq k hk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `testq`
    have hbP : blockAtB L.prog x25L 96 [(Spike.Lib.X64.FI.toDir (.test_rr .rax .rax), 3)] = true := by
      rw [hp]; exact hts
    have hpcE : (fNS L.lab cP sl cA me .ts).pc = L.lab x25L + Int64.ofNat 96 := rfl
    have hC : ∀ s c, At L.exe L.endPc R (Spike.Lib.X64.DFrame R m0) (fNS L.lab cP sl cA me .ts) s c →
        CellAt s (Spike.Lib.X64.FI.toDir (.test_rr .rax .rax)) 3 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl hbP rfl s he hn).cell0 rfl rfl hp'
    refine nodeW_cstOkHK hs ha hW (sz := 3) hcls (fun s c hAt s' h => ?_) ⟨?_, ?_⟩
      (show -144 ≤ oP.sp ∧ oP.sp ≤ 8 by decide) (Spike.Lib.X64.WakePh.hw_fi hC)
    · have hc := hC s c hAt
      have hK := Spike.Lib.X64.WakeRefStub.keep_test hc h
      exact ⟨hK, by rw [Spike.Lib.X64.WakePh.keep_pc hc hK, hAt.2.2.2.1]⟩
    · rw [hpcE, e25]; decide +kernel
    · rw [hpcE, e25]; decide +kernel
  · -- the `je`, not taken
    have hpE : (fNS L.lab cP sl cA me .je).pc = L.lab x25L + 99 := rfl
    have hoE : (fNS L.lab cP sl cA me .je).o = oP := rfl
    refine blkW_cstOkHB hs ha hW (code_field L.lays rfl (by rw [hp]; exact hje) rfl) (blo := -128) (bhi := 16)
      (by rw [hoE]; decide) hR (by omega) hhi
      (hns (fun j hj => by rw [hpE, e25]; revert j; decide +kernel)) hcls
      (fun j hj => by rw [hpE, e25]; revert j; decide +kernel)
      (fun k hk => by rw [hoE]; revert k; decide +kernel)
      (fin_cH hlab hb (by rw [hoE]; decide +kernel) fun σ c hJ => ?_)
    rw [hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.Parent.jeB_run]
    simp only [hJ.2.2.2, Bool.false_eq_true, ite_false]
    rw [e25]
    decide +kernel
  · -- `.x26`, the `jl` taken
    have hpE : (fNS L.lab cP sl cA me .x26).pc = L.lab x26L := rfl
    have hoE : (fNS L.lab cP sl cA me .x26).o = oP := rfl
    refine blkW_cstOkHB hs ha hW (code_field L.lays rfl (by rw [hp]; exact hx26)
        (Spike.Lib.X64.Flow.ofNat_zero' _)) (blo := -128) (bhi := 16)
      (by rw [hoE]; decide) hR (by omega) hhi
      (hns (fun j hj => by rw [hpE, e26]; revert j; decide +kernel)) hcls
      (fun j hj => by rw [hpE, e26]; revert j; decide +kernel)
      (fun k hk => by rw [hoE]; revert k; decide +kernel)
      (fin_cH hlab hb (by rw [hoE]; decide +kernel) fun σ c hJ => ?_)
    have hmsb : σ.regs.rax.toBitVec.msb = true := by
      have := hJ.2.1.slt; simpa [BitVec.slt_zero_eq_msb] using this
    rw [hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.Parent.x26B_run]
    simp only [hmsb, ite_true]
    rw [efl]
    decide +kernel
  · -- `.spawnfail5`: the call of `scc_rt_abort(5)`
    have hpE : (fNS L.lab cP sl cA me .fl).pc = L.lab flL := rfl
    have hoE : (fNS L.lab cP sl cA me .fl).o = oP := rfl
    refine blkW_cstOkHB hs ha hW (code_field L.lays rfl (by rw [hp]; exact hfl)
        (Spike.Lib.X64.Flow.ofNat_zero' _)) (blo := -136) (bhi := 16)
      (by rw [hoE]; decide) hR (by omega) hhi
      (hns (fun j hj => by rw [hpE, efl]; revert j; decide +kernel)) hcls
      (fun j hj => by rw [hpE, efl]; revert j; decide +kernel)
      (fun k hk => by rw [hoE]; revert k; decide +kernel) ?_
    intro σ c _ s m hA _ _ hs'
    exact fl_cstH hlab hb (by omega) hhi σ s m hA hs'

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.bandOn_preH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.bandOn_preH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.fin_cH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.fin_cH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.fl_cstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.fl_cstH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refCstBlkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refCstBlkH
