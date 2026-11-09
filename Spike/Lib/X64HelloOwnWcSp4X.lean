/-
**hello.w's `wc_main` from `.x24` to its `clone` at `ownGHXW`** (x86-64 only; the hello counterpart of
`X64WakeOwnWcSp4X`): `X64HelloWcSp4W`'s producers at `SFactsSt2`/`ownGH` (`wcSp4W_wcGH`, `nIH_wcGH`,
`wcSp6W_wcGH`) moved to `SFactsSt2` at `ownGHXW` (`Lft2H`), from outside (`BlkW.imp`, `NodeW.imp`).
`wc_main`'s frame is on the pool (`hb : BandOnP L R (-144) 8`):

- `.x24` to the call and `scc_rt_thread_init`'s first instruction (pcs in `[.x24, .x25)`, `scc_rt_thread_init`'s
  entry: `QPH`) hold `tcbM` only (`cls_poolH`); the tid store at `t + 56` misses it (`htM`);
- `.x25` to the `syscall` (`InCH`) hold both words (`cls_poolWH`); the fence and the clone's loads and flags write
  nothing.

- `bandTiH_of`: `BandTiH` from `hb`.
- `n4LH`, `n4sLH`, `n5LH`, `nILH`, `cloneLH`: the nodes inside `Lft2H`.
- `wcSp4W_wcGHX`, `nIH_wcGHX`, `wcSp6W_wcGHX`: the producers at `ownGHXW`.

The rows' `keep_mfence`, `hw_mfence`, `keep_xor` and the store's `hw_stK`, `notIn_tM`, `notIn_nil` are x86-64
wake's (`X64WakeOwnWcSp4X`, `X64WakeOwnTi2X`), generic in the code.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `OwnSp4`: hello's frame is 128
bytes (wake 64), so the band is `[-144, 8]` (wake `[-80, 8]`); the call is at `.x24` (`4203787`, wake `.x20`) and
the clone at `.x25` (`4203812`, wake `.x21`), whose pcs to `.stk` are exactly `InCH`, so the clone's class is
`InCH` itself (wake `PW`/`QW`); `WcSp4WH` has no `nI` field, so `nIH_wcGHX` and `wcSp6W_wcGHX` are separate
results (wake's `clone` field); the producers take `hW` about the worker's word `tcbWH L` (`pinA + 144`).
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloWcSp4W
import Spike.Lib.X64WakeOwnWcSp4X

namespace Spike.Lib.X64.HelloPh.OwnSp4

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At FI stDir mB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh (tcbM Keep BandOnP keep_pc hw_fi)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.WcSp4W (tiPush)
open Spike.Lib.X64.WakePh.WcClone (nrB)
open Spike.Lib.X64.WakePh.OwnTi2 (hw_stK notIn_tM notIn_nil)
open Spike.Lib.X64.WakePh.OwnSp4 (keep_mfence hw_mfence keep_xor)
open Spike.Lib.X64.Flow.HelloWc (oCH x24L aNH wcNIH sp4AH initCallH sp4AH_ok initCallH_ok sp4AH_run initCallH_run
  WcSp4WH)
open Spike.Lib.X64.HelloPh.WcSp6 (oWH x25L sp6AH cloneLdH sp6AH_ok cloneLdH_ok nrBH_ok sp6AH_run cloneLdH_run
  nrBH_run wcN6H wcN6fH wcN6aH wcNdH wcN10H wcNrH WcSp6W)
open Spike.Lib.X64.HelloPh.WcSp4W (BandTiH tiPushH_ok tiPushH_run hello_tiPush sp4InH lab_x24H lab_x25H lab_tiH)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt eaddr op64)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Region} {F : MachineData → Prop}

/-- **`WcSp4W`'s `BandTiH`** from the frame's band on the pool. -/
theorem bandTiH_of (hb : BandOnP L R (-144) 8) : BandTiH L R := fun k h1 h2 => hb k h1 (by omega)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soSH " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -144 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

/-- `InCH` is off the take site. -/
theorem inCH_site : ∀ q, InCH q → q ≠ 4200314 := fun q h => by unfold InCH at h; omega

/-- **The `InCH` class**: both words at `.x25` to `.stk` on the pool. -/
theorem cls_cH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandOnP L R (-144) 8) : ∀ s : State, InCH (pcOf s) → Spike.Lib.X64ConsumerA.SpAt R (-144) 8 s →
    CstH L (Spike.Lib.X64.WakePh.tM L) (tWH L) s :=
  fun s h => cls_poolWH hlab hb s ⟨.inr h, by unfold InCH at h; unfold InAbH; omega⟩

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-144) 8)
include hp hlab hsite hsep ha hW hb

variable {c0 : Spike.Lib.Ctl} {t cA me : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {fr : BitVec 64 × BitVec 64}

/-- **`.x24`'s block inside `Lft2H`.** -/
theorem n4LH (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aNH (_root_.Executable.labels L.exe).label c0 t sl me cA fr .n20) sp4AH := by
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) sp4InH.1 (ofNat_zero' _) sp4AH_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soSH sp4AH oWH) (fun σ c _ => ?_)
  · intro j hj
    show PPH ((_root_.Executable.labels L.exe).label x24L + Int64.ofNat (Spike.Lib.X64.cellOff sp4AH j)).toBitVec.toNat
    rw [lab_x24H hlab]; revert j; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ sp4AH ⟨(_root_.Executable.labels L.exe).label x24L, oWH, σ⟩).pc.toBitVec.toNat
    rw [sp4AH_run, lab_x24H hlab]; dsimp only; decide +kernel

omit hsite in
/-- **The tid store inside `Lft2H`**: `t + 56` off `tcbM` (`htM`), unmapped under `F` (`hun`). -/
theorem n4sLH (htM : t + 56#64 ≠ tcbM L) (hun : ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aNH (_root_.Executable.labels L.exe).label c0 t sl me cA fr .n20s) := by
  have hE : ∀ s c, At L.exe L.endPc R F (aNH (_root_.Executable.labels L.exe).label c0 t sl me cA fr .n20s) s c →
      CellAt s (stDir .rcx 56 .rax) 4 ∧ eaddr s 4 (mB .rcx 56) = t + 56#64 ∧
      Mem.loadInt s.st.1.dmem (t + 56#64) 8 = none ∧ s.decls = {} := by
    rintro s c ⟨he, hn, hd, hp', σ, hA, hF, -, hcx, -⟩
    exact ⟨(code_field L.lays rfl (hp ▸ sp4InH.2.1) rfl s he hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s 4 .rcx 56).trans (by rw [hA.regs, hcx]; rfl), hun _ hF, hd⟩
  refine nodeL2H hsep ha hW (sz := 4) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
    (by dsimp only [aNH]; decide) (hw_stK hE ⟨notIn_tM htM, notIn_nil⟩)
  · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
    have hK : Keep s s' := Spike.Lib.X64.WakePh.StartTi.keep_st hc hd hea hun' hs
    exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
  · show QPH ((_root_.Executable.labels L.exe).label x24L + 12).toBitVec.toNat; rw [lab_x24H hlab]; decide +kernel
  · show QPH ((_root_.Executable.labels L.exe).label x24L + 12 + Int64.ofNat 4).toBitVec.toNat
    rw [lab_x24H hlab]; decide +kernel

/-- **The call block inside `Lft2H`** (its end at `scc_rt_thread_init`). -/
theorem n5LH (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi) :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aNH (_root_.Executable.labels L.exe).label c0 t sl me cA fr .n20p) initCallH := by
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) sp4InH.2.2.1 rfl initCallH_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soSH initCallH oWH)
    (fun σ c _ => ?_)
  · intro j hj
    show PPH ((_root_.Executable.labels L.exe).label x24L + 16 +
      Int64.ofNat (Spike.Lib.X64.cellOff initCallH j)).toBitVec.toNat
    rw [lab_x24H hlab]; revert j; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ initCallH
      ⟨(_root_.Executable.labels L.exe).label x24L + 16, oWH, σ⟩).pc.toBitVec.toNat
    rw [initCallH_run]; show QPH ((_root_.Executable.labels L.exe).label "scc_rt_thread_init").toBitVec.toNat
    rw [lab_tiH hlab]; decide +kernel

/-- **`scc_rt_thread_init`'s entry inside `Lft2H`** (its `pushq %rbp`). -/
theorem nILH (hR : R.OK) (hRlo : R.lo ≤ -144) (hhi : 16 ≤ R.hi) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (wcNIH (_root_.Executable.labels L.exe).label c0 t sl me cA fr) := by
  refine Spike.Lib.LowerX64.BlkW.nodeW (blk := tiPush) ?_ (by decide)
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) hello_tiPush (ofNat_zero' _) tiPushH_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soSH tiPush oCH)
    (fun σ c _ => ?_)
  · intro j hj
    show PPH ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (Spike.Lib.X64.cellOff tiPush j)).toBitVec.toNat
    rw [lab_tiH hlab]; revert j; decide +kernel
  · show QPH (Spike.Lib.X64.arun _ tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oCH, σ⟩).pc.toBitVec.toNat
    rw [tiPushH_run, lab_tiH hlab]; dsimp only; decide +kernel

/-- **`.x25` to the `syscall` inside `Lft2H`**, at any stack top `k`: both words held (`InCH`), the fence and the
flags writing nothing. -/
theorem cloneLH (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) {k : BitVec 64} :
    WcSp6W (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F c0 t k sl me cA fr := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2H hp hlab hsite hsep ha hW (P := InCH) (Q := InCH) sp4InH.2.2.2.1 (ofNat_zero' _) sp6AH_ok hR hRlo
      hhi inCH_site (cls_cH hlab hb) (cls_cH hlab hb) ?_ (soSH sp6AH oWH)
      (fun σ c _ => ?_)
    · intro j hj
      show InCH ((_root_.Executable.labels L.exe).label x25L +
        Int64.ofNat (Spike.Lib.X64.cellOff sp6AH j)).toBitVec.toNat
      rw [lab_x25H hlab]; revert j; decide +kernel
    · show InCH (Spike.Lib.X64.arun _ sp6AH ⟨(_root_.Executable.labels L.exe).label x25L, oWH, σ⟩).pc.toBitVec.toNat
      rw [sp6AH_run, lab_x25H hlab]; dsimp only; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcN6fH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c →
        CellAt s (op64 .mfence) 3 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4InH.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2H hsep ha hW (sz := 3) (P := InCH) (cls_cH hlab hb)
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [wcN6fH]; decide) (hw_mfence hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_mfence hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 44).toBitVec.toNat; rw [lab_x25H hlab]
      decide +kernel
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 44 + Int64.ofNat 3).toBitVec.toNat
      rw [lab_x25H hlab]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := InCH) (Q := InCH) sp4InH.2.2.2.2.2.1 rfl cloneLdH_ok hR hRlo hhi
      inCH_site (cls_cH hlab hb) (cls_cH hlab hb) ?_ (soSH cloneLdH oWH)
      (fun σ c _ => ?_)
    · intro j hj
      show InCH ((_root_.Executable.labels L.exe).label x25L + 47 +
        Int64.ofNat (Spike.Lib.X64.cellOff cloneLdH j)).toBitVec.toNat
      rw [lab_x25H hlab]; revert j; decide +kernel
    · show InCH (Spike.Lib.X64.arun _ cloneLdH
        ⟨(_root_.Executable.labels L.exe).label x25L + 47, oWH, σ⟩).pc.toBitVec.toNat
      rw [cloneLdH_run, lab_x25H hlab]; dsimp only; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcNdH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c →
        CellAt s (FI.toDir (.xor_rr32_self .rdx)) 2 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4InH.2.2.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2H hsep ha hW (sz := 2) (P := InCH) (cls_cH hlab hb)
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [wcNdH]; decide) (hw_fi hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_xor hc ⟨by decide, by decide⟩ hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 84).toBitVec.toNat; rw [lab_x25H hlab]
      decide +kernel
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 84 + Int64.ofNat 2).toBitVec.toNat
      rw [lab_x25H hlab]; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcN10H (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c →
        CellAt s (FI.toDir (.xor_rr32_self .r10)) 3 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4InH.2.2.2.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2H hsep ha hW (sz := 3) (P := InCH) (cls_cH hlab hb)
      (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [wcN10H]; decide) (hw_fi hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_xor hc ⟨by decide, by decide⟩ hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 86).toBitVec.toNat; rw [lab_x25H hlab]
      decide +kernel
    · show InCH ((_root_.Executable.labels L.exe).label x25L + 86 + Int64.ofNat 3).toBitVec.toNat
      rw [lab_x25H hlab]; decide +kernel
  · refine blkL2H hp hlab hsite hsep ha hW (P := InCH) (Q := InCH) sp4InH.2.2.2.2.2.2.2.2 rfl nrBH_ok hR hRlo hhi
      inCH_site (cls_cH hlab hb) (cls_cH hlab hb) ?_ (soSH nrB oWH)
      (fun σ c _ => ?_)
    · intro j hj
      show InCH ((_root_.Executable.labels L.exe).label x25L + 89 +
        Int64.ofNat (Spike.Lib.X64.cellOff nrB j)).toBitVec.toNat
      rw [lab_x25H hlab]; revert j; decide +kernel
    · show InCH (Spike.Lib.X64.arun _ nrB ⟨(_root_.Executable.labels L.exe).label x25L + 89, oWH, σ⟩).pc.toBitVec.toNat
      rw [nrBH_run, lab_x25H hlab]; dsimp only; decide +kernel

end L

/-! ## The producers at `ownGHXW` -/

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-144) 8)
include hp hlo hΛ hlab hsite hsep ha hW hb

variable {c0 : Spike.Lib.Ctl} {t cA me : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {fr : BitVec 64 × BitVec 64}

/-- **`WcSp4W.wcSp4W_wcGH` at `ownGHXW`**: the band `hband` from `hb`; the tid word also off `tcbM` (`htM`). -/
theorem wcSp4W_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2aH L a 0)
    (htM : t + 56#64 ≠ tcbM L) :
    WcSp4WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 t sl me cA fr :=
  have h := WcSp4W.wcSp4W_wcGH hp hlo hΛ hlab hsite (rS := rS) (c0 := c0) (sl := sl) (me := me) (cA := cA)
    (fr := fr) a hR hRlo hhi (bandTiH_of hb) htidW
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h.n4
      (n4LH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR (by omega) hhi) fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.n4s
      (n4sLH (Λ := Λ) (Dt := fun _ => False) hp hlab hsep ha hW hb htM htidW.2.1) fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.n5
      (n5LH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1⟩

/-- **`WcSp4W.nIH_wcGH` at `ownGHXW`**: `scc_rt_thread_init`'s entry. -/
theorem nIH_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -144) (hhi : 16 ≤ R.hi) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNIH (_root_.Executable.labels L.exe).label c0 t sl me cA fr) :=
  Spike.Lib.X64.AllocG.NodeW.imp (WcSp4W.nIH_wcGH hp hlo hΛ hlab hsite (rS := rS) a hR hRlo hhi (bandTiH_of hb))
    (nILH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1

/-- **`WcSp4W.wcSp6W_wcGH` at `ownGHXW`**: `.x25` to the `syscall`, at any stack top and frame. -/
theorem wcSp6W_wcGHX (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) {k : BitVec 64} :
    WcSp6W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 t k sl me cA fr :=
  have h := WcSp4W.wcSp6W_wcGH hp hlo hΛ hlab hsite (rS := rS) (F := F) (c0 := c0) (t := t) (k := k) (sl := sl)
    (me := me) (cA := cA) (fr := fr) a hR hRlo hhi
  have hc := cloneLH (Λ := Λ) (Dt := fun _ => False) (F := F) (c0 := c0) (t := t) (k := k) (sl := sl) (me := me)
    (cA := cA) (fr := fr) hp hlab hsite hsep ha hW hb hR hRlo hhi
  ⟨Spike.Lib.X64.AllocG.BlkW.imp h.n6 hc.n6 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.n6f hc.n6f fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.n6a hc.n6a fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.nd hc.nd fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.n10 hc.n10 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.nr hc.nr fun _ _ h1 h2 => h2 h1⟩

end Inst

end Spike.Lib.X64.HelloPh.OwnSp4

/-- info: 'Spike.Lib.X64.HelloPh.OwnSp4.cloneLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSp4.cloneLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnSp4.wcSp4W_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSp4.wcSp4W_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnSp4.nIH_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSp4.nIH_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnSp4.wcSp6W_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSp4.wcSp6W_wcGHX
