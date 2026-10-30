/-
**wake's load with main's `ThreadId` placed** (AArch64): the
start's relation at the labels `L0T Λ`, `Λ.static` (none) with main's
`ThreadId` box label `mainTidLbl 2` placed at its control block
`tcb0 Λ = Λ.pinned.lo + 8` with no cells (`MemRelP.lbl_range`'s pinned
disjunct: a thread's `ThreadId` box at its TCB, the word the start's
`scc_rt_alloc_tcb` returns at the first slot and `wc_main` passes to the
clone in `x10`), for `tidStartT` programs whose `main` reads `me`.

- `tcb0`, `L0T`, `ls0T`: the address, the labels, the sizes.
- `inv1_startT`: `Inv1` at the start at `L0T` (`Inv1.start`'s fields, the
  box's range in `Λ.pinned`).
- `arenaOK_initT`, `ctrOff_T`, `freshT`: the arena's contract at load (the
  box off the heap), the counter off every placed label (the box has no
  cells), `tidStartT 2`'s next label fresh past the box.
- `pre_loadAHT`, `init_of_loadAHT`: `A64ConsumerA.pre_loadAH` and
  `WakePreAsm.init_of_loadAH` at `L0T`/`ls0T` (no static label: `hstat`).
- `wake_initT`: `WakePreAsm.wake_init` at `L0T`/`ls0T`.
-/
import Spike.Lib.WakePreAsm

namespace Spike.Lib.WakeLoadT

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.WakePreTi Spike.Lib.WakePreAsm
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

/-! ## The labels -/

/-- **Main's control block**, where its `ThreadId` box is placed. -/
def tcb0 (Λ : Scc.Sem.Layout) : Nat := Λ.pinned.lo + 8

/-- **The start's labels**: the static ones, main's `ThreadId` box at
`tcb0`. -/
def L0T (Λ : Scc.Sem.Layout) : Lbl := Spike.Lib.A64ConsumerA.upd Λ.static (mainTidLbl 2) (tcb0 Λ)

/-- **The start's sizes**: main's `ThreadId` box has no cells. -/
def ls0T (ls : Lsize) : Lsize := Spike.Lib.A64ConsumerA.updN ls (mainTidLbl 2) 0

variable {Λ : Scc.Sem.Layout}

/-- A placed label of `L0T` at no static label is the box at `tcb0`. -/
theorem l0T_some (hstat : Λ.static = fun _ => none) {l : WeakMem.AllocLabel} {b : Nat} (h : L0T Λ l = some b) :
    l = mainTidLbl 2 ∧ b = tcb0 Λ := by
  unfold L0T Spike.Lib.A64ConsumerA.upd at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · rw [hstat] at h; cases h

/-- The box's range: no word, inside `Λ.pinned`, aligned. -/
theorem tcb0_range (hwf : Λ.WF) (hpz : 8 ≤ Λ.pinned.size) {ls : Lsize} :
    tcb0 Λ % 8 = 0 ∧ ls0T ls (mainTidLbl 2) = 0 ∧ (lrange (ls0T ls) (mainTidLbl 2) (tcb0 Λ)).Sub Λ.pinned := by
  have hal : Λ.pinned.lo % 16 = 0 := hwf.aligned _ (by simp [Scc.Sem.Layout.regions])
  have h0 : ls0T ls (mainTidLbl 2) = 0 := by simp [ls0T, Spike.Lib.A64ConsumerA.updN]
  refine ⟨by unfold tcb0; omega, h0, ?_⟩
  simp only [lrange, h0, Range.Sub, tcb0]
  omega

/-- **`Inv1` at the start at `L0T`.** -/
theorem inv1_startT {I : ISA} {ls : Lsize} (hwf : Λ.WF) (hpz : 8 ≤ Λ.pinned.size) (hstat : Λ.static = fun _ => none)
    {t : Thread I} {tm : Memory} (hp : t.prom = []) (htm : tm.msgs = #[]) :
    Inv1 Λ (L0T Λ) (ls0T ls) (fun _ => none) t tm #[] where
  mem := by
    rw [hp]
    exact {
      lbl_static := fun l b h => by rw [hstat] at h; cases h
      lbl_range := fun l b h => by
        obtain ⟨rfl, rfl⟩ := l0T_some hstat h
        obtain ⟨h8, h0, hs⟩ := tcb0_range hwf hpz (ls := ls)
        exact ⟨h8, .inr (.inr ⟨h0, hs⟩)⟩
      lbl_disj := fun l l' b b' hne h h' => by
        obtain ⟨rfl, -⟩ := l0T_some hstat h
        obtain ⟨rfl, -⟩ := l0T_some hstat h'
        exact absurd rfl hne
      lbl_mem := fun m hm => by simp at hm
      mem_rep := fun k m hk => by simp at hk
      ts_first := fun k m hk => by simp at hk
      ts_mono := fun k1 _ _ _ m1 _ hm1 => by simp at hm1
      mem_onto := fun k' m' hg => by simp [Memory.get?, htm] at hg
      ts_dom := fun _ _ => rfl
      tp_nodup := List.nodup_nil
      sp_nodup := List.nodup_nil
      tp_le := fun _ hp => absurd hp List.not_mem_nil
      sp_lt := fun _ hk => absurd hk List.not_mem_nil
      prom_corr := fun _ _ h => by cases h
      tq_nodup := List.nodup_nil
      tq_le := fun _ hp => absurd hp List.not_mem_nil
      tq_img := fun _ _ _ => List.not_mem_nil
      tp_tq := fun _ hp => absurd hp List.not_mem_nil }
  coh k w hg := by simp [Memory.get?, htm] at hg
  narrow k w hg := by simp [Memory.get?, htm] at hg

/-- **The arena's contract at load at `L0T`**: the box lies in `Λ.pinned`,
off the heap. -/
theorem arenaOK_initT {I : ISA} {ls : Lsize} {t : Thread I} {tm : Memory} {heap cells : Nat} (hwf : Λ.WF)
    (hpz : 8 ≤ Λ.pinned.size) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk heap (16 * cells)).Sub Λ.heap) (hal : heap % 16 = 0)
    (hz : ∀ a, (AllocRow.freeR heap cells 0).contains a → tm.initVal (wordLoc a) = 0)
    (hm : ∀ k', tm.get? k' = none) :
    AllocRow.ArenaOK Λ (L0T Λ) (ls0T ls) t tm heap cells 0 (fun _ => False) := by
  have hd : Λ.heap.Disjoint Λ.pinned := hwf.disjoint.2.2.2.2.2.2.2.2.1
  obtain ⟨-, h0, hs⟩ := tcb0_range hwf hpz (ls := ls)
  refine ⟨Nat.zero_le _, hsub, hal, fun l b h => ?_, fun l b h => ?_, hz, fun k' w h => by rw [hm k'] at h; cases h⟩
  · obtain ⟨rfl, rfl⟩ := l0T_some hstat h
    simp only [AllocRow.freeR, lrange, h0, Range.Disjoint, Range.Sub] at hsub hs hd ⊢
    omega
  · obtain ⟨rfl, rfl⟩ := l0T_some hstat h
    simp only [lrange, h0, Range.Disjoint, Range.Sub] at hsub hs hd
    omega

/-- **The counter is off every placed label** at `L0T`: the box has no
cells. -/
theorem ctrOff_T {ar : Arena} {ls : Lsize} (hstat : Λ.static = fun _ => none) : CtrOff ar (L0T Λ) (ls0T ls) := by
  intro l b h hc
  obtain ⟨rfl, rfl⟩ := l0T_some hstat h
  simp [lrange, ls0T, Spike.Lib.A64ConsumerA.updN, Range.contains] at hc
  omega

/-- **`tidStartT 2`'s labels past the box are unplaced** at `L0T`. -/
theorem freshT (hstat : Λ.static = fun _ => none) :
    AllocInv.FreshInv (L0T Λ) (tidStartT 2).lbase (tidStartT 2).n 0 wakeTh0.nalloc := by
  intro k hk
  cases h : L0T Λ (TermRun.freshLabel (tidStartT 2).lbase (tidStartT 2).n 0 k) with
  | none => rfl
  | some b =>
    obtain ⟨he, -⟩ := l0T_some hstat h
    have hn : (tidStartT 2).n = 2 := by decide
    have hl : (tidStartT 2).lbase = 0 := rfl
    have hna : wakeTh0.nalloc = 1 := rfl
    rw [hn, hl] at he
    rw [hna] at hk
    have hm : mainTidLbl 2 = 0 := rfl
    rw [hm] at he
    simp only [TermRun.freshLabel] at he
    exfalso
    simp at he
    rcases k with _ | k
    · exact absurd hk (by decide)
    · exact absurd he (by simp [Nat.mul_succ])

/-! ## The load -/

section Load

variable {P : SrcSem.SrcParams} {p : Prog} {I : InvS} {μ : Marks}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry} {H : State → List (Nat × Range) → Prop}

open Scc.Cert.Link in
/-- **The start is related at `L0T`, over a held predicate**
(`A64ConsumerA.pre_loadAH` with main's `ThreadId` box placed at `tcb0`; no
static label, `hstat`). -/
theorem pre_loadAHT {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize}
    {s₀ : TermRun.Cfg} {th₀ : TermRun.TTh}
    (hwf : Λ.WF) (hpz : 8 ≤ Λ.pinned.size) (hw : wideIn prog = true)
    (hinit : P.init s₀) (hs0 : s₀.ths = #[th₀]) (hσ : th₀.σs = []) (hp : th₀.promises = [])
    (hsm : s₀.mem = #[]) (hhu : heapUse s₀ = 0)
    (hst : I (L0T Λ) (ls0T lsize) (threadAt E Λ.code.lo prog syms) ⟨th₀.term, th₀.env, none⟩ th₀.stack)
    (hfr0 : AllocInv.FreshInv (L0T Λ) s₀.lbase s₀.n 0 th₀.nalloc)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64)
    (hH0 : H (threadAt E Λ.code.lo prog syms) [])
    (hown0 : OwnInit (own (threadAt E Λ.code.lo prog syms) th₀.stack)
      (loadProg (kernel 1) E Λ prog syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ prog syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSAH Λ P p G own I H μ ar (loadProg (kernel 1) E Λ prog syms mem) s₀ := by
  have hinv : Inv1 Λ (L0T Λ) (ls0T lsize) (fun _ => none)
      (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2) (loadProg (kernel 1) E Λ prog syms mem).1.mem
      s₀.mem := by
    rw [hsm]; exact inv1_startT hwf hpz hstat rfl rfl
  refine ⟨Thread.init (threadAt E Λ.code.lo prog syms), th₀, 0, L0T Λ, ls0T lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    hH0, .inl rfl, certOkC_of_prom_nil rfl, hs0, hσ, hp, hst, .inl trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    hinv, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, ?_, hfr0, ?_,
    [], s₀, hinit, .refl _⟩
  · exact ⟨E, rfl⟩
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · have hnm : ∀ k', (loadProg (kernel 1) E Λ prog syms mem).1.mem.get? k' = none := fun k' => by
      cases hk : (loadProg (kernel 1) E Λ prog syms mem).1.mem.get? k' with
      | none => rfl
      | some m =>
        unfold Memory.get? at hk; split at hk
        · cases hk
        · simp [loadProg, Config.init] at hk
    have har : AllocRow.ArenaOK Λ (L0T Λ) (ls0T lsize) (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2)
        (loadProg (kernel 1) E Λ prog syms mem).1.mem ar.heap ar.cells 0 (fun _ => False) :=
      arenaOK_initT hwf hpz hstat hsub hal hz0 hnm
    have hct := AllocInv.CtrAt.init (prom := (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2).prom)
      (ctr := ar.ctr) (fun k' _ => hnm k')
    rw [hc0] at hct
    rw [hhu]
    exact .inr ⟨(fun w h => by cases h), by simpa using hct, har⟩
  · exact ctrOff_T hstat

open Scc.Cert.Link in
/-- **The relation at the target's load at `L0T`** (`WakePreAsm.init_of_loadAH`
by `pre_loadAHT`). -/
theorem init_of_loadAHT {E : Entry} {prog : Program} {secs : DataSecs} {lsize : Lsize}
    {s₀ : TermRun.Cfg} {th₀ : TermRun.TTh} (hwf : Λ.WF)
    (hpz : 8 ≤ Λ.pinned.size) (hw : wideIn prog = true)
    (hinit : P.init s₀) (hs0 : s₀.ths = #[th₀]) (hσ : th₀.σs = []) (hp : th₀.promises = [])
    (hsm : s₀.mem = #[]) (hhu : heapUse s₀ = 0)
    (hst : I (L0T Λ) (ls0T lsize) (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th₀.term, th₀.env, none⟩
      th₀.stack)
    (hfr0 : AllocInv.FreshInv (L0T Λ) s₀.lbase s₀.n 0 th₀.nalloc)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) th₀.stack) t0.1.mem)
    (hg : MemInv G t0.1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : t0.1.mem.initVal (wordLoc ar.ctr) = 0) (h : loadParsed (kernel 1) E Λ prog secs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RSAH Λ P p G own I H μ ar t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s₀, hinit, .inl (pre_loadAHT hwf hpz hw hinit hs0 hσ hp hsm hhu hst hfr0
      (loadMem_in hwf hc.1.1.1.1) ?_ hH0 hown0 hg hstat hsub hal hz0 hc0)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

open Scc.Cert.Link in
/-- **wake.w's load is related at `L0T`** (`WakePreAsm.wake_init` by
`init_of_loadAHT`): main's `ThreadId` box placed at `tcb0`, the next label
fresh (`freshT`). -/
theorem wake_initT {arch : WeakMem.Arch} {E : Entry} {asm : String} {prog : Program} {secs : DataSecs}
    {lsize : Lsize}
    (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs) (hwf : Λ.WF)
    (hpz : 8 ≤ Λ.pinned.size) (hw : wideIn prog = true)
    (hbox0 : heapUse (tidStartT 2) = 0)
    (hst : I (L0T Λ) (ls0T lsize) (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨wakeTh0.term, wakeTh0.env, none⟩ wakeTh0.stack)
    (hH0 : H (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
    (hown0 : ∀ t0 : T.M.Cfg, loadParsed (kernel 1) E Λ prog secs = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) wakeTh0.stack) t0.1.mem ∧
      MemInv G t0.1.mem ∧ (∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0) ∧
      t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0) :
    ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧ RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc G own I H μ ar d s0 := by
  intro d h
  have hl : loadParsed (kernel 1) E Λ prog secs = some d := (load_of_parsed (kernel 1) E Λ hpa hd).symm.trans h
  obtain ⟨ho, hg, hz0, hc0⟩ := hown0 d hl
  exact init_of_loadAHT (P := srcPo 2 arch wakeSrc) (th₀ := wakeTh0) hwf hpz hw
    (show progInitT wakeSrc 2 (tidStartT 2) by rw [wake_start]) rfl rfl rfl rfl hbox0 hst (freshT hstat) hH0 ho hg
    hstat hsub hal hz0 hc0 hl

end Load

end Spike.Lib.WakeLoadT

/-- info: 'Spike.Lib.WakeLoadT.wake_initT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeLoadT.wake_initT
