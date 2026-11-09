/-
**hello.w's `wc_rodata` up to the allocator's return at `ownGHXW`** (x86-64 only; the `ownGHXW` instance of
`Spike/Lib/X64HelloRdPreWI.lean`, as `X64HelloOwnWcPreX` is `X64HelloWcPreWI`'s): `WcW.proW_rdGH`, `eW_rdGH` and
`rdPreW_wcGH` (inside `SFactsSt2` at `ownGH`) moved to `SFactsSt2` at `ownGHXW` (`Lft2H`), from outside
(`XProW.imp`, `BlkW.imp`; the allocator `OwnAlloc.allocW_wcGHX`). `wc_rodata`'s pcs up to the allocator's call
and the blocks' ends (`.Lwc_rodata.stk`, `scc_rt_alloc`) are `QPH` pcs (off the take site: `PPH`), and its frame
with the allocator's, the band `[-208, 8]`, is on the pool (`hb`), so every state holds `tcbM` only
(`cls_poolH`). The limit's `%fs` load writes nothing.

- `rd_labsH`: the labels the pcs are decided from.
- `proRLH`, `eRLH`: the nodes inside `Lft2H`.
- `bandOnP_aR`: the allocator's band `[-160, 8]` at `aR R` from `wc_rodata`'s.
- `proW_rdGHX`, `eW_rdGHX`, `rdPreW_wcGHX`: the producers at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (`A64HelloRdPreWI` at `ownGH` is the whole chain). Against
`X64HelloOwnWcPreX` (`wc_main`'s): `wc_rodata`'s frame is 32 bytes (`wc_main` 128) with nothing spilled, its body
and the call's return address down to `-48` and the allocator's frame below it (`aR R = R.callee (-48) (-160) 8`),
so the band is `[-208, 8]` (`wc_main`'s `[-144, 8]`, its allocator's own `hb`); the allocator's counter and headers
are also off `tcbM` (`hnoM`, `allocW_wcGHX`'s).
-/
import Spike.Lib.X64HelloRdPreWI
import Spike.Lib.X64HelloOwnAllocX
import Spike.Lib.X64HelloOwnWcPreX

namespace Spike.Lib.X64.HelloPh.OwnRd

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq code_field label_labelGapB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW At fsDir)
open Spike.Lib.X64.Flow (XProW xProN2 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok xHead_run xLea_run
  xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.HelloRd (rN RdPreW hello_rdPro hello_rdEIn rdEIn rdPro)
open Spike.Lib.X64.Flow.Hello1 (rdE rdE_ok rdE_run aR)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.WakePh (tcbM Keep BandOnP keep_pc)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.OwnWc (keep_fsld hw_fsld)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Region} {F : MachineData → Prop}

/-- The labels `wc_rodata`'s pcs are decided from, at the canonical base. -/
theorem rd_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "wc_rodata" = Int64.ofNat 4203169 ∧ L.lab ".Lwc_rodata.chk" = Int64.ofNat 4203173 ∧
    L.lab ".Lwc_rodata.entry" = Int64.ofNat 4203196 ∧ L.lab ".Lwc_rodata.stk" = Int64.ofNat 4203314 ∧
    L.lab "scc_rt_alloc" = Int64.ofNat 4198666 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soRH " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -208 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

/-- **The allocator's band at `wc_rodata`'s call**: `aR R`'s `[-160, 8]` is `R`'s `[-208, -40]`. -/
theorem bandOnP_aR (hb : BandOnP L R (-208) 8) : BandOnP L (aR R) (-160) 8 := by
  intro k h1 h2
  have e : (aR R).addr k = R.addr (-48 + k) := Region.callee_addr R (-48) (-160) 8 k
  rw [e]; exact hb _ (by omega) (by omega)

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

set_option maxHeartbeats 1600000 in
/-- **`wc_rodata`'s prologue inside `Lft2H`**: the limit's load at the thread pointer `tp` (`htp`), its word
unmapped under `F` (`hun`). -/
theorem proRLH (hb : BandOnP L R (-208) 8) (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F ms (L.lab "wc_rodata") 32 8 ".Lwc_rodata.stk"
      5 9 3 2 4 [] J0 := by
  obtain ⟨eW, -, -, eK, -⟩ := rd_labsH hlab (L := L)
  have h := hello_rdPro
  simp only [rdPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".Lwc_rodata.chk" = L.lab "wc_rodata" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_rodata" + 1 + 3 = L.lab ".Lwc_rodata.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e19 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 19 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 32 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bHd (ofNat_zero' _)
      (xHead_ok (lo := -40) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRH xHead (⟨0, []⟩ : Spike.Lib.X64.SO))
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_rodata" + Int64.ofNat (Spike.Lib.X64.cellOff xHead k)).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · rw [xHead_run]; show QPH (L.lab "wc_rodata" + 1 + 3).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bLea
      (by show _ = L.lab "wc_rodata" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -40) (hi := 0) _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRH (xLea 32 5) Spike.Lib.X64.Flow.oH)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_rodata" + 1 + 3 + _).toBitVec.toNat; rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xLea 32 5)
        ⟨L.lab "wc_rodata" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
      rw [xLea_run (Z := 32) _ _ _ (by decide)]
      show QPH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
  · have hE : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_rodata") 5 32 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨he, hn, hd, hp', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨(code_field L.lays rfl (hp ▸ bLd) (by show _ = L.lab "wc_rodata" + 1 + 3 + _; rw [h4]) s he
        hn).cell0 rfl rfl hp', ?_, hun _ hF, hd⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 32 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeL2H hsep ha hW (sz := 9) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [xProN2]; decide) (hw_fsld hE)
    · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_fsld hc hd hea hun' hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QPH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eW]; decide +kernel
    · show QPH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat; rw [eW]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bCmp
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -40) (hi := 0) _ _ _ _) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soRH (xCmp ".Lwc_rodata.stk" 3 2) (Spike.Lib.X64.Flow.oL 32)) (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xCmp ".Lwc_rodata.stk" 3 2)
        ⟨L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat
      rw [(xCmp_run _ _ _ _ _ _ _).1]
      split
      · rw [eW]; decide +kernel
      · show QPH (L.lab ".Lwc_rodata.stk").toBitVec.toNat; rw [eK]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bFr
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _ + _ + _; rw [e19])
      (xFr_ok (lo := -40) (hi := 0) _ _ _ (by decide)) hR hRlo hhi (fun _ h => h.2)
      (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
      (soRH (xFr 32 4 []) (Spike.Lib.X64.Flow.oL 32)) (fun σ c _ => ?_)
    · intro k hk
      show PPH (L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 +
        _).toBitVec.toNat
      rw [eW]; revert k; decide +kernel
    · show QPH (Spike.Lib.X64.arun _ (xFr 32 4 [])
        ⟨L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2,
          Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat
      rw [(xFr_run _ _ _ _ _ _).1, eW]; decide +kernel

/-- **`wc_rodata`'s entry block inside `Lft2H`** (its call to `scc_rt_alloc`). -/
theorem eRLH (hb : BandOnP L R (-208) 8) (hR : R.OK) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (rN L.lab R J0 J1 .e) rdE := by
  obtain ⟨-, -, eE, -, eA⟩ := rd_labsH hlab (L := L)
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (l := ".Lwc_rodata.entry") (k := 0)
    (by have := hello_rdEIn; simp only [rdEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) rdE_ok hR hRlo hhi (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_
    (soRH rdE Spike.Lib.X64.Flow.Hello1.oR) (fun σ c _ => ?_)
  · intro k hk; show PPH (L.lab ".Lwc_rodata.entry" + _).toBitVec.toNat; rw [eE]; revert k; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ rdE ⟨_, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat
    rw [rdE_run]; show QPH (L.lab "scc_rt_alloc").toBitVec.toNat; rw [eA]; decide +kernel

end L

/-! ## The producers at `ownGHXW` -/

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-208) 8)
include hp hlo hΛ hlab hsite hsep ha hW hb

/-- **`WcW.proW_rdGH` at `ownGHXW`.** -/
theorem proW_rdGHX (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms (L.lab "wc_rodata") 32 8 ".Lwc_rodata.stk" 5 9 3 2 4 [] J0 :=
  Spike.Lib.X64.Flow.XProW.imp (WcW.proW_rdGH hp hlo hΛ hlab hsite a hR hRlo hhi htp hmr hun)
    (proRLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi htp hun)
    fun _ _ h1 h2 => h2 h1

/-- **`WcW.eW_rdGH` at `ownGHXW`.** -/
theorem eW_rdGHX (hR : R.OK) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (rN L.lab R J0 J1 .e) rdE :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.eW_rdGH hp hlo hΛ hlab hsite a hR hRlo hhi)
    (eRLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

/-- **`WcW.rdPreW_wcGH` at `ownGHXW`** (owned word `a`): `rdPreW_wcGH`'s premises, `ownGHXW`'s separation
(`hsep`, `ha`, `hW`), the band `[-208, 8]` on the pool (`hb`), and the allocator's counter and headers off `tcbM`
(`hnoM`). -/
theorem rdPreW_wcGHX (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -208)
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
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L) :
    RdPreW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F ms J0 J1 := by
  obtain ⟨hR', hR8'⟩ := WcW.aRH_ok hR hR8 hRlo hhi
  refine ⟨proW_rdGHX hp hlo hΛ hlab hsite hsep ha hW hb hR (by omega) (by omega) htp hmr hun,
    eW_rdGHX hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi, fun q hq hra => ?_⟩
  exact OwnAlloc.allocW_wcGHX hp hlab hsite hsep ha hW (bandOnP_aR hb) hlo hΛ hR' hR8'
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee]) hpool (Or.inl rfl) hra
    (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq) (hnoM q hq)

end Inst

end Spike.Lib.X64.HelloPh.OwnRd

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.proRLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.proRLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.eRLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.eRLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.rdPreW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.rdPreW_wcGHX
