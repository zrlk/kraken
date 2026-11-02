/-
**hello.w's `wc_rodata` up to the allocator's return inside `SFactsSt2` at
`ownGH`** (x86-64; twin of `Spike/Lib/A64HelloRdPreWI.lean`): the
`SFactsSt2` component of the pre-spawn chain's `W` for `HelloRd.RdPreW`:
the prologue (frame 32, nothing spilled), the entry block, and
`scc_rt_alloc` at the allocator's region `aR R` returning to
`.Lwc_rodata.x15` (`allocW_wcGH` at `AllocRetH`'s first return point). The
twin of `X64HelloWcPreWI`'s `proW_wcGH`/`eW_wcGH` and
`X64HelloWcPreG.wcPreW_wcGH` at `wc_rodata`, with its own phase table
(`rdTabH`). The checks are decided by the kernel against helloCells'
labels.

- `rdTabH`, `rdFactsH`, `rdW_factH`: `wc_rodata`'s blocks' phase facts.
- `blkW_rdGH`: a covered `ret`-free block of `rdTabH` inside `SFactsSt2` at
  `ownGH` (`blkW_wcGH` at `rdTabH`).
- `proW_rdGH`, `eW_rdGH`: the prologue and the entry block.
- `aRH_ok`: the allocator's region at the call is a region, 8-aligned.
- `rdPreW_wcGH`: `RdPreW` at `SFactsSt2`/`ownGH`.

## Differences from the AArch64 version

The prologue is x86-64's five nodes (`XProW`: `xHead`, the check's `xLea`,
the limit's `%fs` load, `xCmp`, `xFr`; AArch64's four-node `ProW`), so
`rdTabH` has five prologue rows at `.Lwc_rodata.chk`'s byte offsets and the
load is `WakePh.WcW.nodeW_fsld_pre` (AArch64's `Rt.nodeW_ldr_pre`). Offsets
are bytes (`freeBlkH`, `freeAtH l [o]`). No 16-alignment (`hR8`, `aRH_ok`
8-aligned); `call` pushes its return address, so the allocator's region is
`aR R = R.callee (-48) (-160) 8` (AArch64's `hi' = 0`) and the entry block
needs `8 ≤ R.hi`. The frame is 32 under the saved `%rbp` (AArch64: 48 with
the pair); the bounds `R.lo ≤ -208` (`rdE_ok`) and `-40` for the prologue.
-/
import Spike.Lib.X64HelloWcPreG
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk blockAtB code_field label_labelGapB)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun fsDir okBlk agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok xHead_run xLea_run xCmp_run
  xFr_run xS2 xS1 hdRegs ofNat_zero' ofNat_add')
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh.WcW (blkW_mapC c0N_cfacts nodeW_fsld_pre)
open Spike.Lib.X64.Flow.HelloRd (rN RdPreW hello_rdPro hello_rdEIn rdEIn rdPro)
open Spike.Lib.X64.Flow.Hello1 (rdE rdE_ok rdE_run aR)
open Spike.Lib.X64.Alloc (Call AllocW)

/-! ## The blocks' phase facts -/

/-- **`wc_rodata`'s blocks up to the call**: the prologue's four blocks and
its load, the entry block. -/
def rdTabH : List PhFact :=
  [.blk "wc_rodata" 0 xHead none none,
   .blk ".Lwc_rodata.chk" 0 (xLea 32 5) none none,
   .step ".Lwc_rodata.chk" 5 9,
   .blk ".Lwc_rodata.chk" 14 (xCmp ".Lwc_rodata.stk" 3 2) none none,
   .blk ".Lwc_rodata.chk" 19 (xFr 32 4 []) none none,
   .blk ".Lwc_rodata.entry" 0 rdE none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem rdFactsH : rdTabH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

/-- **A fact of `rdTabH` at `phH`.** -/
theorem rdW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ rdTabH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp rdFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A covered `ret`-free block of `wc_rodata` inside `SFactsSt2` at
`ownGH`** (`blkW_wcGH` at `rdTabH`): `blkW_pre` at `instOkH`, the control
replaced by `c0`, moved to `ownGH` at its free pcs (`hfree`) and free end
(`hlast`). -/
theorem blkW_rdGH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ rdTabH) (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hfree : freeBlkH l k blk = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.X64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (rdW_factH hΛ hf)
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := code_field L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeBlk_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **The allocator's region at `wc_rodata`'s call** is a region, its base
8-aligned, its bounds `-160` and `8`. -/
theorem aRH_ok (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi) :
    (aR R).OK ∧ (aR R).base.toNat % 8 = 0 := by
  have hb := Spike.Lib.Region.callee_base (hi' := 8) hR (show R.lo ≤ -48 + -160 by omega) (by decide)
    (show (-48 : Int) < R.hi by omega)
  refine ⟨Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_⟩
  have : (((aR R).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
  omega

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **`wc_rodata`'s prologue inside `SFactsSt2` at `ownGH`**: the thread
pointer `tp` at every entry state (`htp`), its limit word mapped for
reading (`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem proW_rdGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_rodata") 32 8 ".Lwc_rodata.stk" 5 9 3 2 4 [] J0 := by
  have h := hello_rdPro
  simp only [rdPro, Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have esc : L.lab ".Lwc_rodata.chk" = L.lab "wc_rodata" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_rodata" + 1 + 3 = L.lab ".Lwc_rodata.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e19 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 19 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hfr : freeAtH ".Lwc_rodata.chk" [0, 5, 5 + 9, 19, 23] = true := by wcfreeH_dec
  have f0 := freeAt_pcH hlab hfr (o := 0) (by simp)
  have f5 := freeAt_pcH hlab hfr (o := 5) (by simp)
  have f14 := freeAt_pcH hlab hfr (o := 5 + 9) (by simp)
  have f19 := freeAt_pcH hlab hfr (o := 19) (by simp)
  have f23 := freeAt_pcH hlab hfr (o := 23) (by simp)
  rw [ofNat_zero'] at f0
  have hxs : (xS2 32 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := "wc_rodata") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -40) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (by decide) xHead_noRet
      (by wcfreeBH_dec) (fun σ c _ => by
        show freeNH (arun L.lab xHead ⟨L.lab "wc_rodata", ⟨0, []⟩, σ⟩).pc.toBitVec.toNat = true
        rw [xHead_run]
        show freeNH (L.lab "wc_rodata" + 1 + 3).toBitVec.toNat = true
        rw [h4]; exact f0)
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".Lwc_rodata.chk") (k := 0) bLea
      (by show _ = L.lab "wc_rodata" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -40) (hi := 0) _ _) hR hRlo hhi (by decide) (xLea_noRet _ _) (by wcfreeBH_dec)
      (fun σ c _ => by
        show freeNH (arun L.lab (xLea 32 5) ⟨L.lab "wc_rodata" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
          = true
        rw [xLea_run (Z := 32) _ _ _ (by decide)]
        show freeNH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true
        rw [h4]; exact f5)
  · have hf := step_of_factOk hlab (rdW_factH hΛ (f := .step ".Lwc_rodata.chk" 5 9) (by decide))
    have hbL : blockAtB L.prog ".Lwc_rodata.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
      (nodeW_fsld_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) hbL rfl
        (by show L.lab "wc_rodata" + 1 + 3 + _ = _; rw [h4]) c0N_cfacts hf.1 (fun _ _ h => h) hf.2 ?_ hmr hun)
      (by show freeNH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat = true; rw [h4]; exact f5)
      (by show freeNH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat = true
          rw [e14]; exact f14) ?_
    · rintro σ c ⟨-, c', σ0, hJ0, rfl⟩
      rw [congrFun hxs σ0, htp _ _ hJ0]; rfl
    · rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      have hc := Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_rodata" + 1 + 3 + _ = _; rw [h4])
      have ha' : fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp := by
        rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 32 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
          rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
        simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
      refine ⟨_, _, hc, fun w w' h => (by cases h),
        exec_movfs_load_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _), fun s' hu => ?_⟩
      simp only [TreeLeaf] at hu
      obtain ⟨_, rfl⟩ := hu; rfl
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".Lwc_rodata.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -40) (hi := 0) _ _ _ _) hR hRlo hhi (by decide) (xCmp_noRet _ _ _) (by wcfreeBH_dec)
      (fun σ c _ => by
        show freeNH (arun L.lab (xCmp ".Lwc_rodata.stk" 3 2)
          ⟨L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat
          = true
        rw [(xCmp_run _ _ _ _ _ _ _).1]
        split
        · rw [e19]; exact f19
        · exact freeAt_labH hlab (by wcfreeH_dec))
  · exact blkW_rdGH hp hlo hΛ hlab a hsite (l := ".Lwc_rodata.chk") (k := 19) bFr
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _ + _ + _; rw [e19])
      (xFr_ok (lo := -40) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (by decide) (xFr_noRet _ _ _)
      (by wcfreeBH_dec) (fun σ c _ => by
        show freeNH (arun L.lab (xFr 32 4 [])
          ⟨L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2,
            Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat = true
        rw [(xFr_run _ _ _ _ _ _).1, e19, ← ofNat_add', ← ofNat_add']
        exact f23)

/-- **`wc_rodata`'s entry block inside `SFactsSt2` at `ownGH`.** -/
theorem eW_rdGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rN L.lab R J0 J1 .e) rdE :=
  blkW_rdGH hp hlo hΛ hlab a hsite (l := ".Lwc_rodata.entry") (k := 0)
    (by have := hello_rdEIn; simp only [rdEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) rdE_ok hR hRlo hhi (by decide) (by decide) (by wcfreeBH_dec)
    (fun σ c _ => by
      show freeNH (arun L.lab rdE ⟨_, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat = true
      rw [rdE_run]
      exact freeAt_labH hlab (by wcfreeH_dec))

/-- **`RdPreW` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved
by the take: `proW_rdGH` (the thread pointer `tp` at every entry state,
`htp`; its limit word mapped and unmapped, `hmr`, `hun`), `eW_rdGH`, and
`allocW_wcGH` at the allocator's region for every buffer allocation
returning to `.x15` (the stack pool's base fits, `hpool`; the memory side's
writable words mapped, `hmp`; the counter and the headers unmapped under
`F`, `hmem`, and off the owned words, `hno`). -/
theorem rdPreW_wcGH (a : BitVec 64) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -208)
    (hhi : 8 ≤ R.hi) (hpool : Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (K0 Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j) :
    RdPreW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 J1 := by
  obtain ⟨hR', hR8'⟩ := aRH_ok hR hR8 hRlo hhi
  refine ⟨proW_rdGH hp hlo hΛ hlab hsite a hR (by omega) (by omega) htp hmr hun,
    eW_rdGH hp hlo hΛ hlab hsite a hR hRlo hhi, fun q hq hra => ?_⟩
  exact allocW_wcGH hp hlo hΛ hlab hsite a hR' hR8' (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) hpool (Or.inl rfl) hra (fun _ _ => hq.toS) hmp
    (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq)

end Inst

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.proW_rdGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.proW_rdGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.eW_rdGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.eW_rdGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.rdPreW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.rdPreW_wcGH
