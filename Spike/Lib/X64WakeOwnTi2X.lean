/-
**wc_main's second `scc_rt_thread_init` call lifted to `ownGXW`** (x86-64;
X64-OwnW Ti2 group): the call from `wc_main` (returning to
`.Lwc_main.x21`) on the worker's TCB (`q.tcb = tcb2`), its frames `[-248,
8]` on the pool. Before the take store (`.st0`, `.x7 + 48`) every state
owns `tcbM` only (`QP`, `cls_pool`), the nested `scc_rt_stack_take` call
too (`takeL2`, its shared writes off `tcbM`); `.st0` takes the worker's word
(`st0W`: `W0.appendS` of the constant `tM`, then `W0.takeS` of `tW`); from
`.x7 + 51` on (`InT`) and at the return to `.x21` (`InC`) states own both
words (`cls_poolW`), the field stores `st1`–`st5` writing the TCB's other
words. So `StartTi.ti2_WS`'s obligations inside `StartWf.WS` are inside
`WSX` (`ti2X`). The nodes mirror `OwnSt.takeL` / `OwnSt.tiL`.

- `notIn_tM`, `notIn_tW`, `notIn_nil`; `hw_st`, `hw_xchg`, `hw_ld`,
  `hw_rmw`, `hw_nop`: the write conditions of a memory instruction at a word
  off the held words.
- `takeL2`: the second take's nodes inside `Lft`.
- `PW`, `QW`: the classes of both words (`InT` or `InC`, off `InAb`; `PW`
  off the take site).
- `st0W`, `ti2L`, `TiW.imp`, `ti2X`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeStartTiT3
import Spike.Lib.X64WakeTi2T1

namespace Spike.Lib.X64.WakePh.OwnTi2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64 (ND bAddr At NodeW BlkW)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTi
open Spike.Lib.X64.WakePh.Tcb2W (soRun keep_lea keep_rmw)
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW StackM stacksA takeNG swpBlk_eq ldnBlk_eq unlBlk_eq nxtBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-! ## Write conditions -/

theorem notIn_tM {A : BitVec 64} (h : A ≠ tcbM L) : ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ tM L := by
  intro w hw
  simp only [tM, List.mem_singleton, Prod.mk.injEq] at hw
  obtain ⟨hl, -⟩ := hw
  injection hl with h1
  exact h h1

theorem notIn_tW {A : BitVec 64} (h : A ≠ tcb2 L) : ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ tW L := by
  intro w hw
  simp only [tW, List.mem_singleton, Prod.mk.injEq] at hw
  obtain ⟨hl, -⟩ := hw
  injection hl with h1
  exact h h1

theorem notIn_nil {A : BitVec 64} : ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ ([] : List (Loc × Val)) := by simp

section HW

variable {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)} {z : Nat} {A : BitVec 64}

/-- **A plain store `movq %rax, (%rcx)`** at a word off `c1`, `c2`. -/
theorem hw_st
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.stDir .rcx 0 .rax) z ∧
      eaddr s z (Spike.Lib.X64.mB .rcx 0) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : (∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c1) ∧ ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c2) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_store_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact ⟨hA, fun _ => trivial⟩

/-- **A store `movq %rax, k(%rcx)`** at a word off `c1`, `c2`. -/
theorem hw_stK {k : Int64}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.stDir .rcx k .rax) z ∧
      eaddr s z (Spike.Lib.X64.mB .rcx k) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : (∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c1) ∧ ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c2) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_store_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact ⟨hA, fun _ => trivial⟩

/-- **A `xchgq %rax, (%rcx)`** at a word off `c1`, `c2`. -/
theorem hw_xchg
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.xchgDir .rcx 0 .rax) z ∧
      eaddr s z (Spike.Lib.X64.mB .rcx 0) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : (∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c1) ∧ ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c2) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_xchg hc ha hd] at he
  cases he
  rw [hdc, EvTree.access_empty]
  exact ⟨fun _ _ _ => hA, fun _ => trivial⟩

/-- **A load `movq (%rcx), %rax`** writes nothing. -/
theorem hw_ld
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.ldDir .rcx 0 .rax) z ∧
      eaddr s z (Spike.Lib.X64.mB .rcx 0) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {}) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_load_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact fun _ => trivial

/-- **A `lock xaddq %rax, (%rcx)`** at a word off `c1`, `c2`. -/
theorem hw_rmw
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) z ∧
      eaddr s z (Spike.Lib.X64.mB .rcx 0) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : (∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c1) ∧ ∀ w, ((⟨A, 8⟩ : Loc), w) ∉ c2) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_xaddG_agrees (w := .W64) hc ha hd
    (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact ⟨fun _ _ _ => hA, fun _ => trivial⟩

/-- **A `nop`** writes nothing. -/
theorem hw_nop {k : Nat}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Kraken.Promising.Lower.X64.op64 (.nop k)) z) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  rw [Kraken.Promising.Lower.X64.exec_nop (h s c hAt)] at he
  cases he
  trivial

end HW

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
    refine nodeL hlab hsep ha hW (sz := 7) (P := QP) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
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
(its pcs `QP`, its frame `[-200, 8]` on the pool, `hbd`); its shared writes
(the lock, the next offset) miss `tcbM` (`PhRec.TcbSep`). -/
theorem takeL2 (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbd : BandOnP L R (-200) 8) (hR : R.OK) (hRlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TakeG)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Rt.Code.Ti.x7L).toBitVec) :
    ∀ i, TakeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M q i := by
  have hlk : Spike.Lib.X64.Flow.Ret0.lockA L.lab = L.lockA := L.lab_lock
  have hfr : Spike.Lib.X64.Flow.Ret0.freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : Spike.Lib.X64.Flow.Ret0.nextA L.lab = L.nextA := L.lab_next
  have hLk : L.lockA ≠ tcbM L := fun h => hsep 1 (by decide)
    (by rw [show L.pinA + BitVec.ofNat 64 (8 * 1) = tcbM L from rfl, ← h]; simp)
  have hNx : L.nextA ≠ tcbM L := fun h => hsep 1 (by decide)
    (by rw [show L.pinA + BitVec.ofNat 64 (8 * 1) = tcbM L from rfl, ← h]; simp)
  obtain ⟨eFn, eEn, eCls, eDone, eSpin, eLk, eBump, eOk, eTk, eSite, eFull, eX7⟩ := take_labs hlab (L := L)
  have hin := wake_takeIn
  simp only [stackTakeIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bCls⟩, bJ1⟩, sD0⟩, bD7⟩, sD26⟩, bD33⟩, sD52⟩, bD59⟩,
    bSp0⟩, bSwp⟩, bSp14⟩, bLk0⟩, bLdn⟩, bLk7⟩,
    sB0⟩, bB7⟩, bUnl⟩, sB31⟩, bB38⟩, bNxt⟩, bB61⟩, bB108⟩, sOk0⟩, bOk7⟩, bTk⟩, -⟩, bSite⟩, bRet⟩ := hin
  rw [swpBlk_eq] at bSwp; rw [ldnBlk_eq] at bLdn
  rw [unlBlk_eq] at bUnl; rw [nxtBlk_eq] at bNxt; rw [Spike.Lib.X64.Rt.Take.nopBlk_eq] at bSite
  intro i
  cases i <;> dsimp only [TakeW]
  case e =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bE (ofNat_zero' _) stPro_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stPro oE) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eFn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bEn (ofNat_zero' _) stInit_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stInit oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eEn]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stInit_walk _ _ hJ.2).1, eCls]; decide +kernel
  case cls =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bCls (ofNat_zero' _) stCls_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stCls oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stCls_walk _ _ hJ.2).1, eCls]; decide +kernel
  case j1 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bJ1 rfl stJ1_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stJ1 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eCls]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ1_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d0 => tsiL sD0 eDone
  case d7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bD7 rfl stFreeN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stFreeN oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFreeN_walk _ _ hJ.2.1 hJ.2.2).1, eDone]; decide +kernel
  case d26 => tsiL sD26 eDone
  case d33 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bD33 rfl stFree_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stFree oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stFree_walk _ _ hJ.2).1, eDone]; decide +kernel
  case d52 => tsiL sD52 eDone
  case d59 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bD59 rfl stLock_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stLock oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eDone]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stLock_walk _ _ hJ.2.1 hJ.2.2).1, eSpin]; decide +kernel
  case sp0 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bSp0 (ofNat_zero' _) stSwp_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stSwp oI) (fun σ c hJ => ?_)
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
    refine nodeL hlab hsep ha hW (sz := 3) (P := QP) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_xchg hE ⟨notIn_tM hLk, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_xchg hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, swpPc]; rw [eSpin]; decide +kernel
  case sp14 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bSp14 rfl stSpin_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stSpin oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSpin]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSpin_walk _ _ hJ.2.1 hJ.2.2).1, eLk]; decide +kernel
  case lk0 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bLk0 (ofNat_zero' _) stLdN_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stLdN oI) (fun σ c hJ => ?_)
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
    refine nodeL hlab hsep ha hW (sz := 3) (P := QP) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_ld hE)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_ld ⟨by decide, by decide⟩ hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, freeNPc]; rw [eLk]; decide +kernel
  case lk7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bLk7 rfl stEmpty_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stEmpty oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eLk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stEmpty_walk _ _ hJ.2.1 hJ.2.2).1, eBump]; decide +kernel
  case b0 => tsiL sB0 eBump
  case b7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bB7 rfl stUnl_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stUnl oI) (fun σ c hJ => ?_)
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
    refine nodeL hlab hsep ha hW (sz := 3) (P := QP) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_st hE ⟨notIn_tM hLk, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_st hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, unlPc]; rw [eBump]; decide +kernel
  case b31 => tsiL sB31 eBump
  case b38 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bB38 rfl stAdd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stAdd oI) (fun σ c hJ => ?_)
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
    refine nodeL hlab hsep ha hW (sz := 5) (P := QP) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [takeNG]; decide) (hw_rmw hE ⟨notIn_tM hNx, notIn_nil⟩)
    · obtain ⟨hc, hea, hun, hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_rmw hc hd hea hun hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · dsimp only [takeNG, nextPc]; rw [eBump]; decide +kernel
  case b61 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bB61 rfl stBnd_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stBnd oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG]; rw [stBnd_run]; dsimp only
      split
      · rw [eFull]; decide +kernel
      · rw [eBump]; decide +kernel
  case b108 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bB108 rfl stJ2_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stJ2 oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eBump]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stJ2_walk _ _ hJ.2).1, eOk]; decide +kernel
  case ok0 => tsiL sOk0 eOk
  case ok7 =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bOk7 rfl stOk_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stOk oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eOk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stOk_walk _ _ hJ.2.1 hJ.2.2).1, eTk]; decide +kernel
  case tk =>
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bTk (ofNat_zero' _) stSite_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stSite oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eTk]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢; rw [(stSite_walk _ _ hJ.2).1, eTk]; decide +kernel
  case site =>
    refine fun s c hAt => (nodeL hlab hsep ha hW (P := QP) (sz := 1) (cls_pool hlab hbd) (fun s c hAt s' hs => ?_) ?_
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
    have eX7' : L.lab Spike.Lib.X64.Rt.Code.Ti.x7L = Int64.ofNat 4199569 := eX7
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) bRet rfl stRet_ok hR (by omega) (by omega)
      (fun _ h => h.2) (fun s h => cls_pool hlab hbd s h.1) (cls_pool hlab hbd) ?_ (soT stRet oI) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [takeNG]; rw [eSite]; revert k; decide +kernel
    · dsimp only [takeNG] at hJ ⊢
      rw [(stRet_walk _ _ hJ.2.2).1, hra, Int64.ofBitVec_toBitVec, eX7']; decide +kernel

end Take

/-! ## The call -/

/-- **Both words' class**: `InT` or `InC`, off `InAb`. -/
def QW (q : Nat) : Prop := (InT q ∨ InC q) ∧ ¬ InAb q

instance (q : Nat) : Decidable (QW q) := by unfold QW InT InC InAb; infer_instance

/-- `QW` off the take site. -/
def PW (q : Nat) : Prop := QW q ∧ q ≠ 4200277

instance (q : Nat) : Decidable (PW q) := by unfold PW; infer_instance

section Ti

open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW tiN tiX7 tiTake tiCall tiCall_ok bAddr_rcx storeBlks_eq)
open Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib.X64ConsumerA (StSucc rsp_of_abs)

/-- **`scc_rt_thread_init`'s node obligations from two** (`TiWAt.imp` at
`.x7`). -/
theorem TiW.imp {W W1 W2 : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {M : MachineData → Prop} {q : TiG} {i : TI}
    (h1 : TiW W1 K exe endPc R F M q i) (h2 : TiW W2 (fun _ _ => False) exe endPc R F M q i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : TiW W K exe endPc R F M q i := by
  rw [← Spike.Lib.X64.Rt.tiWAt_x7] at h1 h2 ⊢
  exact Spike.Lib.X64.WakePh.TiWAt.imp h1 h2 hw

/-- `hso` of a block of `scc_rt_thread_init` at offsets `o`, decided. -/
local macro "soI " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block before `.st0` (main's word only, `PP`/`QP`). -/
local macro "tblkM " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL hp hlab hsite hsep ha hW (P := PP) (Q := QP) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_pool hlab hbd48 s h.1) (cls_pool hlab hbd48) ?_
      (soI $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [tiN, tiX7]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tiN, tiX7] at hJ ⊢))

set_option hygiene false in
/-- A block after `.st0` (both words, `PW`/`QW`). -/
local macro "tblkW " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkL hp hlab hsite hsep ha hW (P := PW) (Q := QW) $bb (by first | rfl | exact ofNat_zero' _) $ok hR
      (by omega) (by omega) (fun _ h => h.2) (fun s h => cls_poolW hlab hbd48 s h.1) (cls_poolW hlab hbd48) ?_
      (soI $blk $oo) (fun σ c hJ => ?_)
    · intro k hk; dsimp only [tiN]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tiN] at hJ ⊢))

set_option hygiene false in
/-- A store of the worker's TCB field `j ≥ 1` (`movq %rax, k(%rcx)`, `z`
bytes, block `b`) inside `Lft`: off both held words. -/
local macro "tstX " b:term:max x:term:max j:term:max k:term:max z:term:max : tactic =>
  `(tactic| focus
    have ha' : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb := by
      simp [Spike.Lib.X64.Rt.Ti.tiAddrs]
    have hA' : ∀ σ c, (tiN (_root_.Executable.labels L.exe).label q $x).J σ c →
        bAddr σ.regs .rcx $k = q.tcb + BitVec.ofNat 64 (8 * $j) := fun σ c hJ => by
      dsimp only [tiN] at hJ
      rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide)
    have hne : q.tcb + BitVec.ofNat 64 (8 * $j) ≠ tcbM L ∧ q.tcb + BitVec.ofNat 64 (8 * $j) ≠ tcb2 L := by
      rw [htcb]; constructor <;> (intro h; simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] at h; bv_omega)
    refine nodeL hlab hsep ha hW (sz := $z) (P := QW) (cls_poolW hlab hbd48) (fun s c hAt s' hs => ?_) ?_
      (by dsimp only [tiN]; decide) (hw_stK (k := $k) (z := $z) (A := q.tcb + BitVec.ofNat 64 (8 * $j))
        (fun s c hAt => ?_) ⟨notIn_tM hne.1, notIn_tW hne.2⟩)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := keep_st hc hd (a := q.tcb + BitVec.ofNat 64 (8 * $j))
        ((Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ)) (hunT _ ha' _ hF.1) hs
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tiN]; rw [eX7]; decide +kernel
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      exact ⟨(code_field L.lays rfl (hp ▸ $b) rfl s he hn).cell0 rfl rfl hp',
        (Spike.Lib.X64.eaddr_mB s _ _ _).trans (by rw [hA.regs]; exact hA' σ c hJ), hunT _ ha' _ hF.1, hd⟩)

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`.st0` inside `Lft`**: the worker takes its TCB word (`W0.takeS` of
`tW`, after `W0.appendS` of main's constant `tM`); both states on the pool
(`hbd`), the store at `.x7 + 48` (`QP`) and its successor at `.x7 + 51`
(`InT`). -/
theorem st0W {q : TiG} (htcb : q.tcb = tcb2 L) (hun : ∀ m, F m → Mem.loadInt m.dmem (tcb2 L) 8 = none)
    (hbd : BandOnP L R (-48) 8) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F
      (tiN (_root_.Executable.labels L.exe).label q .st0) := by
  intro s c hAt
  refine ⟨fun hws => ?_, fun _ h => h⟩
  obtain ⟨hpc', hc, ha'⟩ := st0_at hp hlab (q := q) (R := R) (F := F) (s := s) (c := c) hAt
  rw [htcb] at ha'
  obtain ⟨-, -, hdc, -, σ, hA, hD, hJ⟩ := hAt
  have hex := Kraken.Promising.Lower.X64.exec_store_agrees hc ha' (hun _ hD)
    (Spike.Lib.X64.agrees_of_decls hdc _ _)
  have hV : (s.st.1.regs.get (.low .rax .W64)).setWidth 128 = (tcb2 L).setWidth 128 := by
    rw [Spike.Lib.X64.Reg64s.get_low64, hA.regs, Reg64s.get64_rax, hJ.2.2.1, htcb]
  rw [hV] at hex
  have hsp := rsp_of_abs hA
  dsimp only [tiN] at hsp
  have hc0 : Cst L (tM L) [] s :=
    cls_pool hlab hbd s (by unfold pcOf; rw [hpc']; decide) ⟨-40, by decide, by decide, hsp⟩
  have hpc1 : pcOf (Kraken.Promising.Lower.X64.after s 3 s.st.1) = 4199620 := by
    show (s.st.2 + Int64.ofNat 3).toBitVec.toNat = _; rw [hpc']; decide
  have hc1 : Cst L (tM L) (tW L) (Kraken.Promising.Lower.X64.after s 3 s.st.1) :=
    cls_poolW hlab hbd _ (by rw [hpc1]; decide) ⟨-40, by decide, by decide, hsp⟩
  have hsys : abi.atSys s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  have htk : ∀ a', (Spike.Lib.X64.PhRec.μ L).site .take = some a' → pcOf s ≠ a' := by
    intro a' ha2 hpcs
    rw [hsite] at ha2
    cases ha2
    unfold pcOf at hpcs
    rw [hpc', siteV hlab] at hpcs
    exact absurd hpcs (by decide)
  have h1 := Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownS L) hws ⟨?_, ?_, ownS_disj hsep ha⟩
  · exact Spike.Lib.X64.WakeWf.W0.takeS (ownS := ownSW L) (own := ownGX L a) h1 hex rfl hc0.2 hc1.2
      (tcb2_notGX hW s) hsys htk
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
    exact ⟨notIn_tM (tcb2_ne_tcbM L), fun _ => trivial⟩

set_option maxHeartbeats 3200000 in
/-- **The second `scc_rt_thread_init` call's nodes inside `Lft`**, called
from `wc_main` returning to `.x21` (`hra`) on the worker's TCB (`htcb`), its
frames `[-248, 8]` on the pool (`hbdI`), the TCB's words unmapped in
private memory under `F` (`hunT`). -/
theorem ti2L (hbdI : Spike.Lib.X64.WakePh.Ti2.BandP L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {M : MachineData → Prop} (q : TiG)
    (htcb : q.tcb = tcb2 L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab ".Lwc_main.x21").toBitVec) :
    ∀ i, TiW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F M q i := by
  have hbd48 : BandOnP L R (-48) 8 := Spike.Lib.X64.WakePh.Ti2.bandP_mono hbdI (by decide)
  obtain ⟨eFn, eEn⟩ := ti_labs hlab (L := L)
  obtain ⟨eT, -, -, -, -, -, -, -, -, -, -, eX7⟩ := take_labs hlab (L := L)
  have e21 : L.lab ".Lwc_main.x21" = Int64.ofNat 4203397 :=
    hlab _ _ (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
  have hin := wake_tiIn
  simp only [threadInitIn, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bC⟩, -⟩, bSp⟩, bF1⟩, bF2⟩, bF3⟩, bF4⟩, bF5⟩, bRet⟩,
    bS0, bS1, bS2, bS3, bS4, bS5⟩ := hin
  rw [show callBlk = tiCall from rfl] at bC
  intro i
  cases i <;> dsimp only [TiW]
  case e =>
    tblkM bE tiPro_ok tiPro oE eFn
    rw [(tiPro_walk _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblkM bEn tiArg_ok tiArg oI eEn
    rw [(tiArg_walk _ _ hJ.2).1, eEn]; decide +kernel
  case c7 =>
    tblkM bC tiCall_ok tiCall oI eEn
    rw [Spike.Lib.X64.Flow.Ret0.tiCall_run]
    show QP ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.fnL).toBitVec.toNat
    rw [eT]; decide +kernel
  case call =>
    intro g hg j
    have hR' := Spike.Lib.Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide)
      (by omega) (by omega)
    exact takeL2 hp hlab hsite hsep ha hW
      (Spike.Lib.X64.WakePh.Ti2.bandP_callee hbdI (by show (-248 : Int) ≤ -48 - 0 + -200; omega) (by decide))
      hR' (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr (tiTake q g) hg j
  case x7 =>
    tblkM bSp tiSp_ok tiSp oI eX7
    rw [(tiSp_walk _ _ hJ.2.1 hJ.2.2).1, eX7]; decide +kernel
  case st0 =>
    exact st0W hp hlab hsite hsep ha hW htcb
      (fun m hm => hunT _ (by rw [htcb]; simp [Spike.Lib.X64.Rt.Ti.tiAddrs]) m hm.1) hbd48
  case f1 =>
    tblkW bF1 tiF1_ok tiF1 oI eX7
    rw [(tiF1_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st1 => tstX bS1 TI.st1 1 8 4
  case f2 =>
    tblkW bF2 tiZ_ok tiZ oI eX7
    rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st2 => tstX bS2 TI.st2 2 16 4
  case f3 =>
    tblkW bF3 tiZ_ok tiZ oI eX7
    rw [(tiZ_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st3 => tstX bS3 TI.st3 3 24 4
  case f4 =>
    tblkW bF4 tiF4_ok tiF4 oI eX7
    rw [(tiF4_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st4 => tstX bS4 TI.st4 4 32 4
  case f5 =>
    tblkW bF5 tiF5_ok tiF5 oI eX7
    rw [(tiF5_walk _ _ hJ.2).1, eX7]; decide +kernel
  case st5 => tstX bS5 TI.st5 5 40 4
  case ret =>
    tblkW bRet tiRet_ok tiRet oI eX7
    rw [(tiRet_walk _ _ hJ.2).1, hra, Int64.ofBitVec_toBitVec, e21]; decide +kernel

/-- **`StartTi.ti2_WS`'s obligations inside `WS` are inside `WSX`** at the
second `scc_rt_thread_init` call (`ti2L`). -/
theorem ti2X (hbdI : Spike.Lib.X64.WakePh.Ti2.BandP L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop}
    {M : MachineData → Prop} (q : TiG) (htcb : q.tcb = tcb2 L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab ".Lwc_main.x21").toBitVec)
    (h : ∀ i, TiW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M q i) :
    ∀ i, TiW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M q i := fun i =>
  TiW.imp (h i) (ti2L hp hlab hsite hsep ha hW hbdI hR hRlo hhi hFr q htcb hunT hra i) fun _ _ h1 h2 => h2 h1

end Ti

end Spike.Lib.X64.WakePh.OwnTi2

/-- info: 'Spike.Lib.X64.WakePh.OwnTi2.takeL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnTi2.takeL2

/-- info: 'Spike.Lib.X64.WakePh.OwnTi2.st0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnTi2.st0W

/-- info: 'Spike.Lib.X64.WakePh.OwnTi2.ti2X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnTi2.ti2X
