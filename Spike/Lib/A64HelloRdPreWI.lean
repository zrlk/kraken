/-
**hello.w's `wc_rodata` up to the allocator's return inside `SFactsSt2` at `ownGH`**
(AArch64): the `SFactsSt2` component of the pre-spawn chain's
`W` for `HelloRd.RdPreW`: the prologue (frame 48, nothing spilled), the entry block,
and `scc_rt_alloc` at the allocator's region `aR R` returning to `.L19_wc_rodata.sp0`
(`allocW_wcGH` at `AllocRetH`'s first return point). The twin of `A64HelloWcPreWI`'s
`proW_wcGH`/`eW_wcGH` and `A64HelloWcPreG.wcPreW_wcGH` at `wc_rodata`, with its own
phase table (`rdTabH`). The checks are decided by the kernel against helloProg's
labels.

- `rdTabH`, `rdFactsH`, `rdW_factH`: `wc_rodata`'s blocks' phase facts.
- `blkW_rdGH`: a covered `ret`-free block of `rdTabH` inside `SFactsSt2` at `ownGH`
  (`blkW_wcGH` at `rdTabH`).
- `proW_rdGH`, `eW_rdGH`: the prologue and the entry block.
- `aRH_ok`: the allocator's region at the call is a region, 16-aligned.
- `rdPreW_wcGH`: `RdPreW` at `SFactsSt2`/`ownGH`.
-/
import Spike.Lib.A64HelloWcPreG
import Spike.Lib.A64HelloRodata

namespace Spike.Lib.A64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero)
open Spike.Lib.A64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.WakePh.WcW (blkW_mapC c0N_cfacts)
open Spike.Lib.A64.Flow.HelloRd (rN RdPreW hello_rdPro hello_rdEIn rdEIn)
open Spike.Lib.A64.Flow.Hello1 (rdE rdE_ok rdE_run aR)
open Spike.Lib.A64.Alloc (Call AllocW)

/-! ## The blocks' phase facts -/

/-- **`wc_rodata`'s blocks up to the call**: the prologue's three blocks and its load,
the entry block. -/
def rdTabH : List PhFact :=
  [.blk ".L19_wc_rodata.stack_check" 0 (Spike.Lib.A64.Flow.chkHead 48) none none,
   .step ".L19_wc_rodata.stack_check" 2,
   .blk ".L19_wc_rodata.stack_check" 3 (Spike.Lib.A64.Flow.chkBr ".L19_wc_rodata.stack_grow") none none,
   .blk ".L19_wc_rodata.stack_check" 5 (Spike.Lib.A64.Flow.frameSet 48 []) none none,
   .blk ".L19_wc_rodata.0_entry" 0 rdE none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem rdFactsH : rdTabH.all (factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `rdTabH` at `phH`.** -/
theorem rdW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ rdTabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) phH f = true := by
  have := List.all_eq_true.mp rdFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A covered `ret`-free block of `wc_rodata` inside `SFactsSt2` at `ownGH`**
(`blkW_wcGH` at `rdTabH`): `blkW_pre` at `instOkH`, the control replaced by `c0`,
moved to `ownGH` at its free pcs (`hfree`) and free end (`hlast`). -/
theorem blkW_rdGH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ rdTabH) (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hfree : freeAtH l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rdW_factH hΛ hf)
  have hW := Spike.Lib.A64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hal hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hal hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeAt_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **The allocator's region at `wc_rodata`'s call** is a region, 16-aligned, its
bounds `-160` and `0`. -/
theorem aRH_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) :
    (aR R).OK ∧ (aR R).base.toNat % 16 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -160 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((aR R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_rodata`'s prologue inside `SFactsSt2` at `ownGH`**: the thread pointer `tp`
at every entry state (`htp`), its limit word mapped for reading (`hmr`) and unmapped
in private memory under `F` (`hun`). -/
theorem proW_rdGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.A64.Flow.ProW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms (L.lab "wc_rodata") 48 8 ".L19_wc_rodata.stack_grow"
      [] J0 := by
  have h := hello_rdPro
  simp only [Spike.Lib.A64.Flow.HelloRd.rdPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L19_wc_rodata.stack_check" = L.lab "wc_rodata" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [ofNat4_zero] at esc
  have f2 := freeKH hlab (l := ".L19_wc_rodata.stack_check") (k := 2) (by free_decH)
  have f3 := freeKH hlab (l := ".L19_wc_rodata.stack_check") (k := 3) (by free_decH)
  have f5 := freeKH hlab (l := ".L19_wc_rodata.stack_check") (k := 5) (by free_decH)
  have f9 := freeKH hlab (l := ".L19_wc_rodata.stack_check") (k := 9) (by free_decH)
  rw [Spike.Lib.A64.Rt.MainU.pc2, esc] at f2
  rw [Spike.Lib.A64.Rt.MainU.pc3, esc] at f3
  rw [Spike.Lib.A64.Rt.MainU.pc5, esc] at f5
  rw [esc, show ∀ x : Int64, x + Int64.ofNat (4 * 9) = x + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * 0)
    from fun x => by simp only [Int64.add_assoc]; rfl] at f9
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".L19_wc_rodata.stack_check") (k := 0) bHd
      (by rw [ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-48) 0 48) hR hal hRlo hhi (by decide)
      (Spike.Lib.A64.Rt.MainU.chkHead_noRet 48) (by free_decH) (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkHead 48) ⟨_, ⟨0, []⟩, σ⟩).pc.toBitVec.toNat
          = true
        rw [Spike.Lib.A64.Flow.chkHead_run]; exact f2)
  · have hf := step_of_factOk hlab (rdW_factH hΛ (f := .step ".L19_wc_rodata.stack_check" 2) (by decide))
    refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
      (Spike.Lib.A64.Rt.nodeW_ldr_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
        (lbl := fun _ => none) (by rw [hp]; exact bLd) rfl
        (by show L.lab "wc_rodata" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc]) c0N_cfacts hf.1
        (fun _ _ h => h) hf.2 ?_ hmr hun) f2 f3 ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    · rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      have hc := cell1H hp bLd h1 h2
        (by rw [h4']; show L.lab "wc_rodata" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc])
      have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp := by
        rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
      refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldr hc ha' (hun _ hF), fun s' hu => ?_⟩
      · cases h
      · rw [h3', EvTree.access_empty] at hu
        obtain ⟨_, hu⟩ := hu
        simp only [TreeLeaf] at hu
        subst hu; rfl
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".L19_wc_rodata.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-48) 0 48 _) hR hal hRlo hhi
      (by decide) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_decH) (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkBr ".L19_wc_rodata.stack_grow")
          ⟨L.lab "wc_rodata" + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 48, σ⟩).pc.toBitVec.toNat = true
        rw [(Spike.Lib.A64.Flow.chkBr_run _ _ _ _ _).1]
        split
        · exact f5
        · exact freeAt_labH hlab (by free_decH))
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".L19_wc_rodata.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -48) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi (by decide)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_decH)
      (fun σ c _ => by
        show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.frameSet 48 [])
          ⟨L.lab "wc_rodata" + 4 + 4 + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 48, σ⟩).pc.toBitVec.toNat = true
        rw [Spike.Lib.A64.Flow.frameSet_run _ _ _ (by decide)]
        exact f9)

/-- **`wc_rodata`'s entry block inside `SFactsSt2` at `ownGH`.** -/
theorem eW_rdGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (rN L.lab J0 J1 .e) rdE :=
  blkW_rdGH hp hlo hΛ hlab a hsite (l := ".L19_wc_rodata.0_entry") (k := 0)
    (by have := hello_rdEIn; simp only [rdEIn, Bool.and_eq_true] at this; exact this.1)
    (Int64.add_zero _) rdE_ok hR hal hRlo hhi (by decide) (by decide) (by free_decH)
    (fun σ c _ => by
      show freeNH (Spike.Lib.A64.Flow.arun L.lab rdE ⟨_, ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat = true
      rw [rdE_run]
      exact freeAt_labH hlab (by free_decH))

/-- **`RdPreW` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved by the
take: `proW_rdGH` (the thread pointer `tp` at every entry state, `htp`; its limit
word mapped and unmapped, `hmr`, `hun`), `eW_rdGH`, and `allocW_wcGH` at the
allocator's region for every buffer allocation returning to `.sp0` (the stack pool's
base fits, `hpool`; the memory side's writable words mapped, `hmp`; the counter and
the headers unmapped under `F`, `hmem`, and off the owned words, `hno`). -/
theorem rdPreW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208)
    (hhi : 0 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j) :
    RdPreW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 J1 := by
  obtain ⟨hR', hal'⟩ := aRH_ok hR hal hRlo hhi
  refine ⟨proW_rdGH hp hlo hΛ hlab hsite a hR hal (by omega) hhi htp hmr hun,
    eW_rdGH hp hlo hΛ hlab hsite a hR hal hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcGH hp hlo hΛ hlab hsite a hR' hal' (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) hpool (Or.inl rfl) hra (fun _ _ => hq.toS) hmp
    (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

end Inst

end Spike.Lib.A64.HelloPh.WcW

/-- info: 'Spike.Lib.A64.HelloPh.WcW.proW_rdGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.proW_rdGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.eW_rdGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.eW_rdGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.rdPreW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.rdPreW_wcGH
