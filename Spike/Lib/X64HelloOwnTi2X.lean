/-
**wc_main's second `scc_rt_thread_init` call lifted to `ownGHXW`** (x86-64 only; the hello twin of
`Spike/Lib/X64WakeOwnTi2X.lean`): the call from `wc_main` (returning to `.Lwc_main.x3`) on the worker's TCB
(`q.tcb = tcbWH`), its frames `[-248, 8]` on the pool. Before the take store (`.st0`, `.x8 + 48`) every state owns
`tcbM` only (`QPH`, `cls_poolH`), the nested `scc_rt_stack_take` call too (`takeL2H`, its shared writes off
`tcbM`); `.st0` takes the worker's word (`st0WH`: `W0.appendS` of the constant `tM`, then `W0.takeS` of `tWH`);
from `.x8 + 51` on (`InTH`) and at the return to `.x25` (`InCH`) states own both words (`cls_poolWH`), the field
stores `st1`–`st5` writing the TCB's other words. So `Ti2.ti2_WSPH`'s obligations inside `StartWf.WSH` are inside
`WSHX` (`ti2LH` with wake's `TiWAtP.imp`). The nodes mirror `OwnSt.takeLH` / `OwnSt.tiLH`.

- `notIn_tWH`: a word off `tcbWH` is not `tWH`'s.
- `takeL2H`: the second take's nodes inside `LftH`.
- `QWH`, `PWH`: the classes of both words (`InTH` or `InCH`, off `InAbH`; `PWH` off the take site).
- `st0WH`: `.st0` inside `LftH`; `ti2LH`: the call's nodes inside `LftH` (`TiWAt … x8L`).

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`OwnTi2`: the code is helloCells (`hello_tiIn`, `hello_takeIn`, `ti_labsH`, `take_labsH`); `scc_rt_thread_init`
returns to `.x8` (`Rt.x8L`, `4199606`; wake `.x7`), so its nodes are `Rt.tiNAt … x8L` and its obligations
`Rt.TiWAt … x8L` (wake: `Ret0.TiW`), `.st0` at `4199654`, `InTH` from `4199657`; the call returns to `.x25`
(`4203812`, wake `.x21`); the take site is at `4200314`; the classes are `CstH`, `QPH`/`PPH`, `QWH`/`PWH`; the
worker's word is `tcbWH L` (`pinA + 144`, wake `tcb2 L = pinA + 136`). Wake's write conditions (`hw_st`, `hw_stK`,
`hw_xchg`, `hw_ld`, `hw_rmw`, `hw_nop`) and `notIn_tM`, `notIn_nil` read no program and are used as they are;
wake's `TiW.imp` / `ti2X` have no twins (hello's consumer takes `TiWAtP`, as wake's `Ti2Hat` does, from `ti2LH`
and `TiWAtP.imp`).
-/
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64HelloOwnStartTi
import Spike.Lib.X64WakeOwnTi2X

namespace Spike.Lib.X64.HelloPh.OwnTi2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout x8L)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64 (ND bAddr At NodeW BlkW)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh (tcbM tM Keep keep_pc keep_nop hw_lea BandOnP)
open Spike.Lib.X64.WakePh.StartTi (keep_xchg keep_ld keep_st)
open Spike.Lib.X64.WakePh.StartTi
open Spike.Lib.X64.WakePh.Ti2 (BandP bandP_mono bandP_callee)
open Spike.Lib.X64.WakePh.OwnTi2 (notIn_tM notIn_nil hw_st hw_stK hw_xchg hw_ld hw_rmw hw_nop)
open Spike.Lib.X64.HelloPh.StartTi (ti_labsH take_labsH hello_takeIn)
open Spike.Lib.X64.HelloPh.OwnSt (st0_atH)
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG swpBlk_eq ldnBlk_eq unlBlk_eq nxtBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib.X64HelloOwnLift (tcbWH tcbM_ne_tcbWH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- **A word off `tcbWH` is not `tWH`'s.** -/
theorem notIn_tWH {A : BitVec 64} (h : A ≠ tcbWH L) : ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ tWH L := by
  intro w hw
  simp only [tWH, List.mem_singleton, Prod.mk.injEq] at hw
  obtain ⟨hl, -⟩ := hw
  injection hl with h1
  exact h h1

section Take

open Spike.Lib.X64.Flow.Ret0.StackTake

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -200 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A `leaq L(%rip), %rax` node of the take inside `Lft` (`bb` its code
check, `el` its label's value). -/
local macro "tsiL " bb:term:max el:term:max : tactic =>
  `(tactic| (
    refine nodeLH hsep ha hW (sz := 7) (P := QPH) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_lea fun s c hAt => by
        obtain ⟨he, hn, -, hp', -⟩ := hAt
        exact (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp')
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $bb) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_lea hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [$el:term]; decide +kernel))

set_option maxHeartbeats 3200000 in
/-- **The second take's nodes inside `Lft`**: every state owns `tcbM` only
(its pcs `QPH`, its frame `[-200, 8]` on the pool, `hbd`); its shared writes
(the lock, the next offset) miss `tcbM` (`PhRec.TcbSep`). -/
theorem takeL2H (hp : L.prog = helloCells)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandOnP L R (-200) 8) (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.x8L).toBitVec) :
    ∀ i, TakeW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hLk : L.lockA ≠ tcbM L := fun h => hsep 1 (by decide)
    (by rw [show L.pinA + BitVec.ofNat 64 (8 * 1) = tcbM L from rfl, ← h]; simp)
  have hNx : L.nextA ≠ tcbM L := fun h => hsep 1 (by decide)
    (by rw [show L.pinA + BitVec.ofNat 64 (8 * 1) = tcbM L from rfl, ← h]; simp)
  obtain ⟨eFn, eEn, eCls, eDone, eSpin, eLk, eBump, eOk, eTk, eSite, eFull, eX8⟩ := take_labsH hlab (L := L)
  have hin := hello_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, sD0⟩, bD7⟩, sD26⟩, bD33⟩, sD52⟩, bD59⟩,
    bSp0⟩, bSwp⟩, bSp14⟩, bLk0⟩, bLdn⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [swpBlk_eq] at bSwp; rw [ldnBlk_eq] at bLdn
  rw [unlBlk_eq] at bUnl; rw [nxtBlk_eq] at bNxt; rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  intro i
  cases i <;> dsimp only [TakeW]
  case e =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bE (ofNat_zero' _) stPro_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stPro oE) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eFn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bEn (ofNat_zero' _) stInit_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stInit oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eEn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stInit_walk _ _ hJ.2).1, eCls]; decide +kernel
  case cls =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bCls (ofNat_zero' _) stCls_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stCls oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stCls_walk _ _ hJ.2).1, eCls]; decide +kernel
  case j1 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bJ1 rfl stJ1_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stJ1 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ1_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d0 => tsiL sD0 eDone
  case d7 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bD7 rfl stFreeN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stFreeN oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFreeN_walk _ _ hJ.2.1 hJ.2.2).1, eDone]; decide +kernel
  case d26 => tsiL sD26 eDone
  case d33 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bD33 rfl stFree_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stFree oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFree_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d52 => tsiL sD52 eDone
  case d59 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bD59 rfl stLock_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stLock oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLock_walk _ _ hJ.2.1 hJ.2.2).1, eSpin]; decide +kernel
  case sp0 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bSp0 (ofNat_zero' _) stSwp_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stSwp oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSwp_walk _ _ hJ.2).1, eSpin]; decide +kernel
  case swp =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F (takeNG (_root_.Executable.labels L.exe).label q true .swp) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.xchgDir .rcx 0 .rax) 3 ∧
        Kraken.Promising.Lower.X64.eaddr s 3 (Spike.Lib.X64.mB .rcx 0) = L.lockA ∧
        Mem.loadInt s.st.1.dmem L.lockA 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ bSwp) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp',
        ?_, Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF), hd⟩
      dsimp only [takeNG] at hJ
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs]
      simp [Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeLH hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_xchg hE ⟨notIn_tM hLk, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_xchg hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, swpPc]; rw [eSpin]; decide +kernel
  case sp14 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bSp14 rfl stSpin_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stSpin oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSpin_walk _ _ hJ.2.1 hJ.2.2).1, eLk]; decide +kernel
  case lk0 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bLk0 (ofNat_zero' _) stLdN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stLdN oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLdN_walk _ _ hJ.2).1, eLk]; decide +kernel
  case ldn =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F (takeNG (_root_.Executable.labels L.exe).label q true .ldn) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.ldDir .rcx 0 .rax) 3 ∧
        Kraken.Promising.Lower.X64.eaddr s 3 (Spike.Lib.X64.mB .rcx 0) = L.freeNA ∧
        Mem.loadInt s.st.1.dmem L.freeNA 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ bLdn) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp',
        ?_, Spike.Lib.X64.PhRec.rtF_freeN (hFr _ hF), hd⟩
      dsimp only [takeNG] at hJ
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs]
      simp [Reg64s.get64, hJ.2.2, hfr]
    refine nodeLH hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_ld hE)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_ld ⟨by decide, by decide⟩ hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, freeNPc]; rw [eLk]; decide +kernel
  case lk7 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bLk7 rfl stEmpty_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stEmpty oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case b0 => tsiL sB0 eBump
  case b7 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bB7 rfl stUnl_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stUnl oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stUnl_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case unl =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F (takeNG (_root_.Executable.labels L.exe).label q true .unl) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.stDir .rcx 0 .rax) 3 ∧
        Kraken.Promising.Lower.X64.eaddr s 3 (Spike.Lib.X64.mB .rcx 0) = L.lockA ∧
        Mem.loadInt s.st.1.dmem L.lockA 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ bUnl) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp',
        ?_, Spike.Lib.X64.PhRec.rtF_lock (hFr _ hF), hd⟩
      dsimp only [takeNG] at hJ
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs]
      simp [Reg64s.get64, hJ.2.2.1, hlk]
    refine nodeLH hsep ha hW (sz := 3) (P := QPH) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_st hE ⟨notIn_tM hLk, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_st hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, unlPc]; rw [eBump]; decide +kernel
  case b31 => tsiL sB31 eBump
  case b38 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bB38 rfl stAdd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stAdd oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stAdd_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case nxt =>
    have hE : ∀ s c, Spike.Lib.X64.At L.exe L.endPc R F (takeNG (_root_.Executable.labels L.exe).label q true .nxt) s c →
        Kraken.Promising.Lower.X64.CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) 5 ∧
        Kraken.Promising.Lower.X64.eaddr s 5 (Spike.Lib.X64.mB .rcx 0) = L.nextA ∧
        Mem.loadInt s.st.1.dmem L.nextA 8 = none ∧ s.decls = {} := fun s c hAt => by
      obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      refine ⟨(code_field L.lays rfl (hp ▸ bNxt) (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp',
        ?_, Spike.Lib.X64.PhRec.rtF_next (hFr _ hF), hd⟩
      dsimp only [takeNG] at hJ
      refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
      rw [hA.regs]
      simp [Reg64s.get64, hJ.2.2.1, hnx]
    refine nodeLH hsep ha hW (sz := 5) (P := QPH) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_rmw hE ⟨notIn_tM hNx, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, nextPc]; rw [eBump]; decide +kernel
  case b61 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bB61 rfl stBnd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stBnd oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [eFull]; decide +kernel
      · rw [eBump]; decide +kernel
  case b108 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bB108 rfl stJ2_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stJ2 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ2_walk _ _ hJ.2).1, eOk]; decide +kernel
  case ok0 => tsiL sOk0 eOk
  case ok7 =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bOk7 rfl stOk_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stOk oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide +kernel
  case tk =>
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bTk (ofNat_zero' _) stSite_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stSite oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide +kernel
  case site =>
    refine fun s c hAt => (nodeLH hsep ha hW (P := QPH) (sz := 1) (cls_poolH hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) ?_ s c hAt).1
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ bSite) (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_nop hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [takeNG]; rw [eSite]; decide +kernel
    · exact hw_nop fun s c hAt => by
        obtain ⟨he, hn, -, hp', -⟩ := hAt
        exact (code_field L.lays rfl (hp ▸ bSite) (ofNat_zero' _) s he hn).cell0 rfl rfl hp'
  case ret =>
    have eX8' : L.lab Spike.Lib.X64.Rt.x8L = Int64.ofNat 4199606 := eX8
    refine blkLHA hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) bRet rfl stRet_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_poolH hlab hbd s h.1) (cls_poolH hlab hbd) ?_ (soT stRet oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eX8']; decide +kernel

end Take

/-! ## The call -/

/-- **Both words' class**: `InT` or `InC`, off `InAb`. -/
def QWH (q : Nat) : Prop := (InTH q ∨ InCH q) ∧ ¬ InAbH q

instance (q : Nat) : Decidable (QWH q) := by unfold QWH InTH InCH InAbH; infer_instance

/-- `QWH` off the take site. -/
def PWH (q : Nat) : Prop := QWH q ∧ q ≠ 4200314

instance (q : Nat) : Decidable (PWH q) := by unfold PWH; infer_instance

section Ti

open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW tiN tiX7 tiTake tiCall tiCall_ok bAddr_rcx storeBlks_eq)
open Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib.X64ConsumerA (StSucc rsp_of_abs)

/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block before `.st0` (main's word only, `PPH`/`QPH`). -/
local macro "tblkM " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkLH hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolH hlab hbd48 s h.1) (cls_poolH hlab hbd48) ?_
      (soI $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt, Spike.Lib.X64.Rt.tiX7At]; rw [$el:term]; revert k; decide +kernel
    dsimp only [Spike.Lib.X64.Rt.tiNAt, Spike.Lib.X64.Rt.tiX7At] at hJ ⊢))

set_option hygiene false in
/-- A block after `.st0` (both words, `PWH`/`QWH`). -/
local macro "tblkW " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkLH hp hlab hsite hsep ha hW (P := PWH) (Q := QWH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolWH hlab hbd48 s h.1) (cls_poolWH hlab hbd48) ?_
      (soI $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [$el:term]; revert k; decide +kernel
    dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢))

set_option hygiene false in
/-- `tblkW` on a block split by a return label (`blkLHA`). -/
local macro "tblkWA " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkLHA hp hlab hsite hsep ha hW (P := PWH) (Q := QWH) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolWH hlab hbd48 s h.1) (cls_poolWH hlab hbd48) ?_
      (soI $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [$el:term]; revert k; decide +kernel
    dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ ⊢))

set_option hygiene false in
/-- A store of the worker's TCB field `j ≥ 1` (`movq %rax, k(%rcx)`, `z`
bytes, block `b`) inside `Lft`: off both held words. -/
local macro "tstX " b:term:max x:term:max j:term:max k:term:max z:term:max : tactic =>
  `(tactic| focus
    have ha' : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.X64.Rt.Ti.tiAddrs]
    have hA' : ∀ σ c, (Spike.Lib.X64.Rt.tiNAt (_root_.Executable.labels L.exe).label q Spike.Lib.X64.Rt.x8L $x).J σ c →
        bAddr σ.regs .rcx $k = q.tcb + BitVec.ofNat 64 (8 * $j) := fun σ c hJ => by
      dsimp only [Spike.Lib.X64.Rt.tiNAt] at hJ
      rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide)
    have hne : q.tcb + BitVec.ofNat 64 (8 * $j) ≠ tcbM L ∧ q.tcb + BitVec.ofNat 64 (8 * $j) ≠ tcbWH L := by
      rw [htcb]; constructor <;> (intro h; simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] at h; bv_omega)
    refine nodeLH hsep ha hW (sz := $z) (P := QWH) (cls_poolWH hlab hbd48) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [Spike.Lib.X64.Rt.tiNAt]; decide) (hw_stK (k := $k) (z := $z) (A := q.tcb + BitVec.ofNat 64 (8 * $j))
        (fun s c hAt => ?_) ⟨notIn_tM hne.1, notIn_tWH hne.2⟩)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := q.tcb + BitVec.ofNat 64 (8 * $j))
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ)) (hunT _ ha' _ hF.1) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [Spike.Lib.X64.Rt.tiNAt]; rw [eX8]; decide +kernel
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      exact ⟨(code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp',
        (Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ), hunT _ ha' _ hF.1, hd⟩)

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`.st0` inside `Lft`**: the worker takes its TCB word (`W0.takeS` of
`tW`, after `W0.appendS` of main's constant `tM`); both states on the pool
(`hbd`), the store at `.x8 + 48` (`QPH`) and its successor at `.x8 + 51`
(`InT`). -/
theorem st0WH {q : TiG} (htcb : q.tcb = tcbWH L) (hun : ∀ m, F m → Mem.loadInt m.dmem (tcbWH L) 8 = none)
    (hbd : BandOnP L R (-48) 8) :
    NodeW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F
      (Spike.Lib.X64.Rt.tiNAt (_root_.Executable.labels L.exe).label q Spike.Lib.X64.Rt.x8L .st0) := by
  intro s c hAt
  refine ⟨fun hws => ?_, fun _ h => h⟩
  obtain ⟨hpc', hc, ha'⟩ := st0_atH hp hlab (q := q) (R := R) (F := F) (s := s) (c := c) hAt
  rw [htcb] at ha'
  obtain ⟨-, -, hdc, -, σ, hA, hD, hJ⟩ := hAt
  have hex := Kraken.Promising.Lower.X64.exec_store_agrees hc ha' (hun _ hD)
    (Spike.Lib.X64.agrees_of_decls hdc _ _)
  have hV : (s.st.1.regs.get (.low .rax .W64)).setWidth 128 = (tcbWH L).setWidth 128 := by
    rw [Spike.Lib.X64.Reg64s.get_low64, hA.regs, Reg64s.get64_rax, hJ.2.2.1, htcb]
  rw [hV] at hex
  have hsp := rsp_of_abs hA
  dsimp only [Spike.Lib.X64.Rt.tiNAt] at hsp
  have hc0 : CstH L (tM L) [] s :=
    cls_poolH hlab hbd s (by unfold pcOf; rw [hpc']; decide) ⟨-40, by decide, by decide, hsp⟩
  have hpc1 : pcOf (Kraken.Promising.Lower.X64.after s 3 s.st.1) = 4199657 := by
    show (s.st.2 + Int64.ofNat 3).toBitVec.toNat = _; rw [hpc']; decide
  have hc1 : CstH L (tM L) (tWH L) (Kraken.Promising.Lower.X64.after s 3 s.st.1) :=
    cls_poolWH hlab hbd _ (by rw [hpc1]; decide) ⟨-40, by decide, by decide, hsp⟩
  have hsys : abi.atSys s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  have htk : ∀ a', (Spike.Lib.X64.PhRec.μ L).site .take = some a' → pcOf s ≠ a' := by
    intro a' ha2 hpcs
    rw [hsite] at ha2
    cases ha2
    unfold pcOf at hpcs
    rw [hpc', siteVH hlab] at hpcs
    exact absurd hpcs (by decide)
  have h1 := Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownSH L) hws ⟨?_, ?_, ownSH_disj hsep ha⟩
  · exact Spike.Lib.X64.WakeWf.W0.takeS (ownS := ownSWH L) (own := ownGHX L a) h1 hex rfl hc0.2 hc1.2
      (tcbWH_notGHX hW s) hsys htk
  · intro s' hs'
    rcases hs' with ⟨-, tree, htr, hl⟩ | ⟨hs2, -⟩ | ⟨a', ha2, hpcs, -⟩
    · rw [hex] at htr
      cases htr
      obtain ⟨b, rfl⟩ := hl
      rw [hc1.1, hc0.1]
    · rw [hsys] at hs2; cases hs2
    · exact absurd hpcs (htk a' ha2)
  · intro _ tree htr
    rw [hex] at htr
    cases htr
    rw [hc0.1]
    exact ⟨notIn_tM ((tcbM_ne_tcbWH L).symm), fun _ => trivial⟩

set_option maxHeartbeats 3200000 in
/-- **The second `scc_rt_thread_init` call's nodes inside `Lft`**, called
from `wc_main` returning to `.x25` (`hra`) on the worker's TCB (`htcb`), its
frames `[-248, 8]` on the pool (`hbdI`), the TCB's words unmapped in
private memory under `F` (`hunT`). -/
theorem ti2LH (hbdI : BandP L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TiG)
    (htcb : q.tcb = tcbWH L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab ".Lwc_main.x3").toBitVec) :
    ∀ i, Spike.Lib.X64.Rt.TiWAt (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M
      q Spike.Lib.X64.Rt.x8L i := by
  have hbd48 : BandOnP L R (-48) 8 := bandP_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labsH hlab (L := L)
  obtain ⟨eT, -, -, -, -, -, -, -, -, -, -, eX8⟩ := take_labsH hlab (L := L)
  have e25 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203812 :=
    hlab _ _ (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
  have hin := hello_tiIn
  simp only [threadInitInAt, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bC⟩, -⟩, bSp⟩, bF1⟩, bF2⟩, bF3⟩, bF4⟩, bF5⟩, bRet⟩,
    bS0, bS1, bS2, bS3, bS4, bS5⟩ := hin
  rw [show callBlk = tiCall from rfl] at bC
  intro i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TiWAt]
  case e =>
    tblkM bE tiPro_ok tiPro oE eFn
    rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblkM bEn tiArg_ok tiArg oI eEn
    rw [(tiArg_walk _ _ hJ.2).1, eEn]; decide +kernel
  case c7 =>
    tblkM bC tiCall_ok tiCall oI eEn
    rw [Spike.Lib.X64.Flow.Ret0.tiCall_run]
    show QPH ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.fnL).toBitVec.toNat
    rw [eT]; decide +kernel
  case call =>
    intro g hg j
    have hR' := Spike.Lib.Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide)
      (by omega) (by omega)
    exact takeL2H hp hlab hsite hsep ha hW
      (bandP_callee hbdI (by show (-248 : Int) ≤ -48 - 0 + -200; omega) (by decide))
      hR' (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr (tiTake q g) hg j
  case x7 =>
    tblkM bSp tiSp_ok tiSp oI eX8
    rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eX8]; decide +kernel
  case st0 =>
    exact st0WH hp hlab hsite hsep ha hW htcb
      (fun m hm => hunT _ (by rw [htcb]; simp [Spike.Lib.X64.Rt.Ti.tiAddrs]) m hm.1) hbd48
  case f1 =>
    tblkW bF1 tiF1_ok tiF1 oI eX8
    rw [(tiF1_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st1 => tstX bS1 TI.st1 1 8 4
  case f2 =>
    tblkW bF2 tiZ_ok tiZ oI eX8
    rw [(tiZ_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st2 => tstX bS2 TI.st2 2 16 4
  case f3 =>
    tblkW bF3 tiZ_ok tiZ oI eX8
    rw [(tiZ_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st3 => tstX bS3 TI.st3 3 24 4
  case f4 =>
    tblkW bF4 tiF4_ok tiF4 oI eX8
    rw [(tiF4_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st4 => tstX bS4 TI.st4 4 32 4
  case f5 =>
    tblkW bF5 tiF5_ok tiF5 oI eX8
    rw [(tiF5_walk _ _ hJ.2).1, eX8]; decide +kernel
  case st5 => tstX bS5 TI.st5 5 40 4
  case ret =>
    tblkWA bRet tiRet_ok tiRet oI eX8
    rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec, e25]; decide +kernel

end Ti

end Spike.Lib.X64.HelloPh.OwnTi2

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.notIn_tWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.notIn_tWH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.takeL2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.takeL2H

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.QWH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.QWH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.PWH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.PWH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.st0WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.st0WH

/-- info: 'Spike.Lib.X64.HelloPh.OwnTi2.ti2LH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnTi2.ti2LH
