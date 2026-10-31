/-
**`wc_main` from `.x20` to its `clone` at `ownGXW`** (x86-64; X64-OwnW Wc
group): `WcSp4W.wcSp4W_wcG` moved from `SFactsSt2` at `ownG` to
`SFactsSt2` at `ownGXW` (`Lft2`), from outside (`BlkW.imp`, `NodeW.imp`).
`wc_main`'s frame is on the pool (`hb : BandOnP L R (-80) 8`):
- `.x20` to the call and `scc_rt_thread_init`'s first instruction (pcs in
  `[.x20, .x21)`, `scc_rt_thread_init`'s entry: `QP`) hold `tcbM` only
  (`cls_pool`); the tid store at `t + 56` misses it (`htM`);
- `.x21` to the `syscall` (`InC`, `QW`) hold both words (`cls_poolW`); the
  fence and the clone's loads and flags write nothing.

- `keep_mfence`, `hw_mfence`, `keep_xor`: the clone's rows keep `%rsp` and
  `%rbp` and write nothing.
- `bandTi_of`: `WcSp4W`'s `BandTi` from `hb`.
- `n20L`, `n20sL`, `n20pL`, `nIL`, `cloneL`: the nodes inside `Lft2`.
- `wcSp4W_wcGX`: `wcSp4W_wcG` at `ownGXW`.

**Deviations.** None: new lemmas. `wcSp4W_wcGX` takes `ownGXW`'s separation
premises (`hsep`, `ha`, `hW`), the frame's band `hb` (from which `hband` is
derived, so it is dropped) and `htM : t + 56#64 ≠ tcbM L` (carried: the tid
word of the second TCB is not main's TCB word) besides `wcSp4W_wcG`'s.
-/
import Spike.Lib.X64WakeOwnTi2X
import Spike.Lib.X64WakeWcSp4W

namespace Spike.Lib.X64.WakePh.OwnSp4

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (code_field)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At FI stDir mB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.WakePh.Tcb2W (soRun silent_leaf)
open Spike.Lib.X64.WakePh.WcSp4 (x20L x20A initCall x20A_ok initCall_ok x20A_run initCall_run wcN20p wcNI oC)
open Spike.Lib.X64.WakePh.WcClone (oW x21L x21A cloneLd nrB x21A_ok cloneLd_ok nrB_ok x21A_run cloneLd_run
  nrB_run wcN21 wcNf wcNa wcNd wcN10 wcNr WcCloneW)
open Spike.Lib.X64.WakePh.WcSp4W (BandTi tiPush wake_tiPush tiPush_ok tiPush_run sp4In lab_x20 lab_x21 lab_ti)
open Spike.Lib.X64.WakePh.OwnTi2 (PW QW hw_stK notIn_tM notIn_nil)
open Spike.Lib.X64.Flow.WakeWc (WcSp4W aN kOf)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_mfence op64)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Region} {F : MachineData → Prop}

section Rows

variable {μ : Marks} {s s' : State} {z : Nat}

/-- **`mfence`** keeps `%rsp` and `%rbp`. -/
theorem keep_mfence (hc : CellAt s (op64 .mfence) z) (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [exec_mfence hc] at htr
    cases htr
    obtain ⟨_, hl⟩ := hl
    simp only [TreeLeaf] at hl
    subst hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **`mfence`** writes nothing. -/
theorem hw_mfence {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (op64 .mfence) z) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  rw [exec_mfence (h s c hAt)] at he
  cases he
  exact fun _ => trivial

/-- **`xorl %r, %r`** (`%r` neither `%rsp` nor `%rbp`) keeps `%rsp` and
`%rbp`. -/
theorem keep_xor {r : Reg64} (hc : CellAt s (FI.toDir (.xor_rr32_self r)) z) (hr : r ≠ .rsp ∧ r ≠ .rbp)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · obtain ⟨t, ht, hsil⟩ := Spike.Lib.X64.exec_fi hc
    rw [ht] at htr
    cases htr
    obtain ⟨fl, rfl⟩ := silent_leaf hsil hl
    obtain ⟨h1, h2⟩ := hr
    refine ⟨?_, ?_, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩ <;> cases r <;>
      first | rfl | exact (h1 rfl).elim | exact (h2 rfl).elim
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

end Rows

/-- **`WcSp4W`'s `BandTi`** from the frame's band on the pool. -/
theorem bandTi_of (hb : BandOnP L R (-80) 8) : BandTi L R := fun k h1 h2 => hb k h1 (by omega)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soS " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -80 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-80) 8)
include hp hlab hsite hsep ha hW hb

variable {c0 : Spike.Lib.Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}

/-- **`.x20`'s block inside `Lft2`.** -/
theorem n20L (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aN (_root_.Executable.labels L.exe).label c0 t cA m fr .n20) x20A := by
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) sp4In.1 (ofNat_zero' _) x20A_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soS x20A oW) (fun σ c _ => ?_)
  · intro j hj
    show PP ((_root_.Executable.labels L.exe).label x20L + Int64.ofNat (Spike.Lib.X64.cellOff x20A j)).toBitVec.toNat
    rw [lab_x20 hlab]; revert j; decide +kernel
  · show QP (Spike.Lib.X64.arun _ x20A ⟨(_root_.Executable.labels L.exe).label x20L, oW, σ⟩).pc.toBitVec.toNat
    rw [x20A_run, lab_x20 hlab]; dsimp only; decide +kernel

omit hsite in
/-- **The tid store inside `Lft2`**: `t + 56` off `tcbM` (`htM`), unmapped
under `F` (`hun`). -/
theorem n20sL (htM : t + 56#64 ≠ tcbM L) (hun : ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    NodeW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aN (_root_.Executable.labels L.exe).label c0 t cA m fr .n20s) := by
  have hE : ∀ s c, At L.exe L.endPc R F (aN (_root_.Executable.labels L.exe).label c0 t cA m fr .n20s) s c →
      CellAt s (stDir .rcx 56 .rax) 4 ∧ eaddr s 4 (mB .rcx 56) = t + 56#64 ∧
      Mem.loadInt s.st.1.dmem (t + 56#64) 8 = none ∧ s.decls = {} := by
    rintro s c ⟨he, hn, hd, hp', σ, hA, hF, ⟨-, hcx, -⟩, -⟩
    exact ⟨(code_field L.lays rfl (hp ▸ sp4In.2.1) rfl s he hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s 4 .rcx 56).trans (by rw [hA.regs, hcx]; rfl), hun _ hF, hd⟩
  refine nodeL2 hlab hsep ha hW (sz := 4) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
    (by dsimp only [aN]; decide) (hw_stK hE ⟨notIn_tM htM, notIn_nil⟩)
  · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
    have hK : Keep s s' := StartTi.keep_st hc hd hea hun' hs
    exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
  · show QP ((_root_.Executable.labels L.exe).label x20L + 12).toBitVec.toNat; rw [lab_x20 hlab]; decide +kernel
  · show QP ((_root_.Executable.labels L.exe).label x20L + 12 + Int64.ofNat 4).toBitVec.toNat
    rw [lab_x20 hlab]; decide +kernel

/-- **The call block inside `Lft2`** (its end at `scc_rt_thread_init`). -/
theorem n20pL (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi) :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (aN (_root_.Executable.labels L.exe).label c0 t cA m fr .n20p) initCall := by
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) sp4In.2.2.1 rfl initCall_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soS initCall oW) (fun σ c _ => ?_)
  · intro j hj
    show PP ((_root_.Executable.labels L.exe).label x20L + 16 +
      Int64.ofNat (Spike.Lib.X64.cellOff initCall j)).toBitVec.toNat
    rw [lab_x20 hlab]; revert j; decide +kernel
  · show QP (Spike.Lib.X64.arun _ initCall ⟨(_root_.Executable.labels L.exe).label x20L + 16, oW, σ⟩).pc.toBitVec.toNat
    rw [initCall_run]; show QP ((_root_.Executable.labels L.exe).label "scc_rt_thread_init").toBitVec.toNat
    rw [lab_ti hlab]; decide +kernel

/-- **`scc_rt_thread_init`'s entry inside `Lft2`** (its `pushq %rbp`). -/
theorem nIL (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) :
    NodeW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F
      (wcNI (_root_.Executable.labels L.exe).label c0 t cA m fr) := by
  refine Spike.Lib.LowerX64.BlkW.nodeW (blk := tiPush) ?_ (by decide)
  refine blkL2 hp hlab hsite hsep ha hW (P := PP) (Q := QP) wake_tiPush (ofNat_zero' _) tiPush_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soS tiPush oC) (fun σ c _ => ?_)
  · intro j hj
    show PP ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (Spike.Lib.X64.cellOff tiPush j)).toBitVec.toNat
    rw [lab_ti hlab]; revert j; decide +kernel
  · show QP (Spike.Lib.X64.arun _ tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oC, σ⟩).pc.toBitVec.toNat
    rw [tiPush_run, lab_ti hlab]; dsimp only; decide +kernel

/-- **`.x21` to the `syscall` inside `Lft2`**, at any stack top `k`: both
words held (`InC`), the fence and the flags writing nothing. -/
theorem cloneL (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) {k : BitVec 64} :
    WcCloneW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F c0 t k cA m fr := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2 hp hlab hsite hsep ha hW (P := PW) (Q := QW) sp4In.2.2.2.1 (ofNat_zero' _) x21A_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolW hlab hb s h.1) (cls_poolW hlab hb) ?_ (soS x21A oW) (fun σ c _ => ?_)
    · intro j hj
      show PW ((_root_.Executable.labels L.exe).label x21L + Int64.ofNat (Spike.Lib.X64.cellOff x21A j)).toBitVec.toNat
      rw [lab_x21 hlab]; revert j; decide +kernel
    · show QW (Spike.Lib.X64.arun _ x21A ⟨(_root_.Executable.labels L.exe).label x21L, oW, σ⟩).pc.toBitVec.toNat
      rw [x21A_run, lab_x21 hlab]; dsimp only; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcNf (_root_.Executable.labels L.exe).label c0 t k cA m fr) s c →
        CellAt s (op64 .mfence) 3 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4In.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2 hlab hsep ha hW (sz := 3) (P := QW) (cls_poolW hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [wcNf]; decide) (hw_mfence hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_mfence hc hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QW ((_root_.Executable.labels L.exe).label x21L + 12).toBitVec.toNat; rw [lab_x21 hlab]; decide +kernel
    · show QW ((_root_.Executable.labels L.exe).label x21L + 12 + Int64.ofNat 3).toBitVec.toNat
      rw [lab_x21 hlab]; decide +kernel
  · refine blkL2 hp hlab hsite hsep ha hW (P := PW) (Q := QW) sp4In.2.2.2.2.2.1 rfl cloneLd_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolW hlab hb s h.1) (cls_poolW hlab hb) ?_ (soS cloneLd oW)
      (fun σ c _ => ?_)
    · intro j hj
      show PW ((_root_.Executable.labels L.exe).label x21L + 15 +
        Int64.ofNat (Spike.Lib.X64.cellOff cloneLd j)).toBitVec.toNat
      rw [lab_x21 hlab]; revert j; decide +kernel
    · show QW (Spike.Lib.X64.arun _ cloneLd
        ⟨(_root_.Executable.labels L.exe).label x21L + 15, oW, σ⟩).pc.toBitVec.toNat
      rw [cloneLd_run, lab_x21 hlab]; dsimp only; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcNd (_root_.Executable.labels L.exe).label c0 t k cA m fr) s c →
        CellAt s (FI.toDir (.xor_rr32_self .rdx)) 2 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4In.2.2.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2 hlab hsep ha hW (sz := 2) (P := QW) (cls_poolW hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [wcNd]; decide) (hw_fi hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_xor hc ⟨by decide, by decide⟩ hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QW ((_root_.Executable.labels L.exe).label x21L + 36).toBitVec.toNat; rw [lab_x21 hlab]; decide +kernel
    · show QW ((_root_.Executable.labels L.exe).label x21L + 36 + Int64.ofNat 2).toBitVec.toNat
      rw [lab_x21 hlab]; decide +kernel
  · have hC : ∀ s c, At L.exe L.endPc R F (wcN10 (_root_.Executable.labels L.exe).label c0 t k cA m fr) s c →
        CellAt s (FI.toDir (.xor_rr32_self .r10)) 3 := fun s c hAt => by
      obtain ⟨he, hn, -, hp', -⟩ := hAt
      exact (code_field L.lays rfl (hp ▸ sp4In.2.2.2.2.2.2.2.1) rfl s he hn).cell0 rfl rfl hp'
    refine nodeL2 hlab hsep ha hW (sz := 3) (P := QW) (cls_poolW hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [wcN10]; decide) (hw_fi hC)
    · have hc := hC s c hAt
      have hK : Keep s s' := keep_xor hc ⟨by decide, by decide⟩ hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QW ((_root_.Executable.labels L.exe).label x21L + 38).toBitVec.toNat; rw [lab_x21 hlab]; decide +kernel
    · show QW ((_root_.Executable.labels L.exe).label x21L + 38 + Int64.ofNat 3).toBitVec.toNat
      rw [lab_x21 hlab]; decide +kernel
  · refine blkL2 hp hlab hsite hsep ha hW (P := PW) (Q := QW) sp4In.2.2.2.2.2.2.2.2 rfl nrB_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolW hlab hb s h.1) (cls_poolW hlab hb) ?_ (soS nrB oW) (fun σ c _ => ?_)
    · intro j hj
      show PW ((_root_.Executable.labels L.exe).label x21L + 41 +
        Int64.ofNat (Spike.Lib.X64.cellOff nrB j)).toBitVec.toNat
      rw [lab_x21 hlab]; revert j; decide +kernel
    · show QW (Spike.Lib.X64.arun _ nrB ⟨(_root_.Executable.labels L.exe).label x21L + 41, oW, σ⟩).pc.toBitVec.toNat
      rw [nrB_run, lab_x21 hlab]; dsimp only; decide +kernel

end L

/-! ## The producer at `ownGXW` -/

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
  (hb : BandOnP L R (-80) 8)
include hp hlo hΛ hlab hsite hsep ha hW hb

/-- **`WcSp4W.wcSp4W_wcG` at `ownGXW`**: the band `hband` from `hb`; the
tid word also off `tcbM` (`htM`). -/
theorem wcSp4W_wcGX (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) {F₂ : MachineData → Prop}
    {c0 : Spike.Lib.Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0)
    (htM : t + 56#64 ≠ tcbM L) :
    WcSp4W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F F₂ c0 t cA m fr :=
  have h := WcSp4W.wcSp4W_wcG hp hlo hΛ hlab hsite a (rS := rS) (F₂ := F₂) (c0 := c0) (cA := cA) (m := m)
    (fr := fr) hR hRlo hhi (bandTi_of hb) htidW
  { n20 := Spike.Lib.X64.AllocG.BlkW.imp h.n20
      (n20L (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR (by omega) hhi) fun _ _ h1 h2 => h2 h1
    n20s := Spike.Lib.X64.AllocG.NodeW.imp h.n20s
      (n20sL (Λ := Λ) (Dt := fun _ => False) hp hlab hsep ha hW hb htM htidW.2.1) fun _ _ h1 h2 => h2 h1
    n20p := Spike.Lib.X64.AllocG.BlkW.imp h.n20p
      (n20pL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR (by omega) hhi) fun _ _ h1 h2 => h2 h1
    nI := Spike.Lib.X64.AllocG.NodeW.imp h.nI
      (nIL (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hb hR hRlo hhi) fun _ _ h1 h2 => h2 h1
    clone :=
      have hc := cloneL (Λ := Λ) (Dt := fun _ => False) (F := F₂) (c0 := c0) (t := t) (cA := cA) (m := m)
        (fr := fr) (k := kOf (_root_.Executable.labels L.exe).label) hp hlab hsite hsep ha hW hb hR (by omega) hhi
      ⟨Spike.Lib.X64.AllocG.BlkW.imp h.clone.n21 hc.n21 fun _ _ h1 h2 => h2 h1,
        Spike.Lib.X64.AllocG.NodeW.imp h.clone.nf hc.nf fun _ _ h1 h2 => h2 h1,
        Spike.Lib.X64.AllocG.BlkW.imp h.clone.na hc.na fun _ _ h1 h2 => h2 h1,
        Spike.Lib.X64.AllocG.NodeW.imp h.clone.nd hc.nd fun _ _ h1 h2 => h2 h1,
        Spike.Lib.X64.AllocG.NodeW.imp h.clone.n10 hc.n10 fun _ _ h1 h2 => h2 h1,
        Spike.Lib.X64.AllocG.BlkW.imp h.clone.nr hc.nr fun _ _ h1 h2 => h2 h1⟩ }

end Inst

end Spike.Lib.X64.WakePh.OwnSp4

/-- info: 'Spike.Lib.X64.WakePh.OwnSp4.cloneL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSp4.cloneL

/-- info: 'Spike.Lib.X64.WakePh.OwnSp4.wcSp4W_wcGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSp4.wcSp4W_wcGX
