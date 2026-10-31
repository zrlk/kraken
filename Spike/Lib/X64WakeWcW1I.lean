/-
**`wc_main`'s own nodes inside `h1`'s level `W1W`** (x86-64; the twin of
`Spike/Lib/A64WakeWcW1I.lean`): the `hwcWf` premise of
`WakeWc.wcMidW_w1`.

- `boxT_run`, `boxT_runWf`, `ctl_box`: main's source from the box to the
  spawn runs only through `BoxT`, at no frame; at the box and past its
  publication it is not at a `ret` and its runs are well formed.
- `nodeCg`: a single instruction stepping to `pc + z` inside `Wf` at any
  owned words, its pc `okC`, its writes' obligations given.
- `nodeCfence`, `nodeCpush`: the `mfence` and `scc_rt_thread_init`'s
  `pushq %rbp` inside `Wf` (`nodeCg`; neither writes shared memory).
- `blk_W1`, `node_W1`: a node inside `Wf` at `W1W`'s parameters is inside
  `W1W` (`AbOffW.marks_target`), at no outside move.
- `wcMainW_wf`: `hwcWf`, from the nodes' `SFactsSt2` at `ownGXW` (`hst`, at
  any move) and placement (`hpl`), the tid word unmapped under `F` (`htid`)
  and off wake's arena and its counter word (`hoffT`).
- `wcMainW_wfB`: `wcMainW_wf` at one ghost of `Box` (`hB`, `l` fresh in the
  start's labels, `hl`), `hpl` from `PlacedLy.wcMainW_placed`.

The proofs decide pcs at the certificate's labels; no absolute address
appears in a statement.

**Where this differs from AArch64** (forced by the x86-64 shape): x86-64's
`WcMainW` has four fields (`bl`, `sp3`, `pre`, `clone`: no fence node
before the reserve, `.x20`'s nodes and the clone's six, the source past the
`mfence` at `boxPubCtl c0 ty l`), so `BoxT`'s controls cover the published
source as well (`boxT_runWf` at `boxTerm` or past the publication; A64: at
`boxTerm` and `SpawnSrc`). The level owns `ownGXW` (`ownG` with the TCB self
words), so the blocks go through `CalWf.blkCn` and the nodes through
`CalWf.nodeC`/`nodeCfi`/`nodeCst` and `nodeCg` at any owned words (A64:
`WcWf.blkW_wfC`/`nodeW_wfC` at `ownG`). The call node `wcNI` is
`scc_rt_thread_init`'s `pushq %rbp` (A64: a `sub`), a store into the frame
covered by the abstract step (`nodeCpush`, `Block.exec_ai`); the fence is
an `mfence` (`nodeCfence`; A64's `dmb_cell`). The nodes' `SFactsSt2` are
the premise `hst` at any move (A64 builds them in `wcMidW_st` from
`WcMidWG.wcMidW_wcG`; x86-64's are `OwnMid.wcMidW_wcGX`), and the tid
word's arena facts the premise `hoffT` (A64: `CalWf.hoffT_W`). The loader's
facts are taken as `WfCalW1.reserveW_wf` takes them (`hpg`, `hlo`, `hpa`;
A64: `Ld`, `ld_of`); the end pc is the layout's (A64: `WakeSpawnR.endR`).
There are no stack-band premises (A64's `BandSp3`, `BandTi`,
`bands_of_box`): they enter only through `hst`.
-/
import Spike.Lib.X64WakeWfCalW1
import Spike.Lib.X64WakePlacedLy
import Spike.Lib.X64WakeWcSp4W
import Spike.Lib.Hello1Runs

namespace Spike.Lib.X64.WakeWcW1I

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2 WrAt noWr_done)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At AI)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (Wf RunWf NoWrC)
open Spike.Lib.X64.WakePh (okC ownGXW lo)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Flow.WakeWc (rN aN WcMidW WcMainW t2 resB resB_ok)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI x20A initCall x20A_ok initCall_ok oC)
open Spike.Lib.X64.WakePh.WcClone (wcN21 wcNf wcNa wcNd wcN10 wcNr x21A cloneLd nrB x21A_ok cloneLd_ok
  nrB_ok)
open Spike.Lib.X64.WakePh.Tcb2Call (wcN3 tcb2Call tcb2Call_ok)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeSrcDefs (spawnTerm)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Spike.Lib.X64.WakeHMid (BoxPure QB)
open Spike.Lib (Region FragS PlaceWX FrameRun Arena)
open Kraken.Promising.Lower.X64 (CellAt exec_mfence op64)

/-! ## Main's source from the box to the spawn -/

section Box

/-- The three terms of main's source from the box to the spawn. -/
def BoxT (t : Expr) : Prop :=
  t = boxTerm ∨ t = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm ∨ t = spawnTerm

/-- Main's source runs from the box only through `BoxT`, at no frame. -/
theorem boxT_run {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') (ht : BoxT q.1.term)
    (hf : q.2 = []) : BoxT q'.1.term ∧ q'.2 = [] := by
  induction h with
  | refl => exact ⟨ht, hf⟩
  | step hs _ ih =>
    refine ih ?_ ?_
    all_goals cases hs with
    | loc hl =>
      first
      | exact hf
      | rcases ht with ht | ht | ht
        · exact .inr (.inl (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp)))
        · exact .inr (.inr (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp)))
        · have e := Spike.Lib.X64.WakeSrcCtl.frameRun_spawn ht (.single (.loc hl (fs := [])))
          cases e; exact .inr (.inr ht)
    | call hc => rcases ht with ht | ht | ht <;> rw [ht] at hc <;> simp [boxTerm, spawnTerm] at hc
    | ret hc => simp at hf

/-- **The box's control and the published one** are not at a `ret` and
their runs are well formed. -/
theorem boxT_runWf {p : Prog} {c : Ctl}
    (ht : c.term = boxTerm ∨ c.term = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  have hB : BoxT c.term := ht.elim .inl fun h => .inr (.inl h)
  refine ⟨fun a e => by rcases ht with ht | ht <;> rw [ht] at e <;> simp [boxTerm] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    have h := (boxT_run hr hB rfl).1
    rcases hc with hc | ⟨b, hc⟩ <;> rcases h with h | h | h <;> rw [hc] at h <;>
      simp [boxTerm, spawnTerm] at h
  · intro c' fs' hr x a τ e hc
    have h := (boxT_run hr hB rfl).1
    rcases h with h | h | h <;> rw [hc] at h <;> simp [boxTerm, spawnTerm] at h

/-- `boxT_runWf` in the shape of the node lemmas' `hJ` at no frames. -/
theorem ctl_box {c : Ctl}
    (ht : c.term = boxTerm ∨ c.term = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm) :
    (([] : List TermRun.Frame) = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [] :=
  ⟨fun _ => (boxT_runWf (p := wakeSrc) ht).1, (boxT_runWf ht).2⟩

end Box

/-! ## Single instructions inside `Wf` at any owned words -/

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {K : State → State → Prop}
  {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Spike.Lib.X64Consumer.Lbl}
  {lsize : Spike.Lib.X64Consumer.Lsize} {fs : List TermRun.Frame}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))

include hp hlo hΛ hlab hsite hcl

/-- **A single instruction stepping to `pc + z` inside `Wf`** at the owned
words `own` (`WcWf.nodeW_wfC` at any `own`, its pc `okC`): its
`SFactsSt2` at `Dt = False` (`hst`, moved by `K`), its next pc off both
abort phases' pcs (`hph`), its step (`hstep`), its controls' facts (`hJ`),
its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeCg {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hP := Spike.Lib.X64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.X64.PhRec.μ L)
    (exe := L.exe) (endPc := L.endPc) he (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph)
    (WakePh.CalWf.htkC hlab hsite hokpc) hstep
  exact Spike.Lib.X64.WakeWf.nodeW_wf (WakePh.CalWf.nodeW_dt hst) (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨(Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.1, (hpl s c hA).1,
      (Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.2⟩, fun _ h => h⟩) hwr
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off (WakePh.CalWf.habtC hp hlo hΛ hokpc))

/-- **An `mfence` of wakeCells inside `Wf`** (`nodeCg`): its tree is one
fence, writing nothing. -/
theorem nodeCfence {n : ND} {l : Label} {k : Nat}
    (hb : blockAtB wakeCells l k [(op64 .mfence, 3)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k 3 = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hI := WakePh.instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hc : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (op64 .mfence) 3 :=
    fun s c ⟨h1, h2, _, h4, _⟩ => Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he h1 h2 h4
  have hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d 3 ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 3 := by
    intro s c hA
    refine ⟨_, _, hc s c hA, (fun w w' h => by cases h), exec_mfence (hc s c hA), fun s' hu => ?_⟩
    obtain ⟨_, hu⟩ := hu
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl
  have hnw : NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hA
    refine ⟨?_, fun _ h => h⟩
    rintro L' (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [exec_mfence (hc s c hA)] at h <;> cases h
  exact nodeCg hp hlo hΛ hlab hsite hcl he hst hokpc hph hstep hJ hpl (Spike.Lib.X64.WakeWf.nodeW_noWrC hnw)

/-- **A `pushq %rbp` of wakeCells inside `Wf`** (`nodeCg`): the abstract
step covers it (`hok`, in the region `R`), so it steps to `pc + 1` and
writes no shared memory (`Block.exec_ai`). -/
theorem nodeCpush {n : ND} {l : Label} {k : Nat} {lo' hi' : Int}
    (hb : blockAtB wakeCells l k [((AI.push .rbp).toDir, 1)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : (AI.push .rbp).ok lo' hi' n.o = true) (hR : R.OK) (hlo' : R.lo ≤ lo') (hhi : hi' ≤ R.hi)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k 1 = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hI := WakePh.instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hx : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (AI.push .rbp).toDir 1 ∧
      ∃ m', isa.exec s = some (.done { s with st := (m', s.st.2 + Int64.ofNat 1) }) := by
    rintro s c ⟨h1, h2, -, h4, σ, hA, -, -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he h1 h2 h4
    obtain ⟨m', hex, -, -⟩ := Spike.Lib.X64.exec_ai hok hR hlo' hhi hc (fun w op h => by cases h) hA
    exact ⟨hc, m', hex⟩
  have hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d 1 ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 1 := by
    intro s c hA
    obtain ⟨hc, m', hex⟩ := hx s c hA
    refine ⟨_, _, hc, (fun w w' h => by cases h), hex, fun s' hu => ?_⟩
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl
  have hnw : NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) L.exe L.endPc R F n := fun s c hA =>
    ⟨noWr_done (hx s c hA).2.choose_spec, fun _ h => h⟩
  exact nodeCg hp hlo hΛ hlab hsite hcl he hst hokpc hph hstep hJ hpl (Spike.Lib.X64.WakeWf.nodeW_noWrC hnw)

end Gen

/-! ## Inside `W1W` -/

section W1

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (Dt : State → Prop) (Ctx : FragS isa)
  (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
/-- `W1W`'s `Wf` at no frames, its marks `PhRec.μ`. -/
local notation "WfL" => fun s c => Wf (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab))
  (WakeOD.arW hpw i) wakeSrc Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (WakeOD.ClW hpw i)
  (Spike.Lib.X64.ThreadsAb.Ac (Ly).lab pfxM) (fun _ _ _ => False)
  (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
  (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c []

set_option hygiene false in
/-- `h1`'s level at no frames. -/
local notation "Wq" => fun s c => WakeOPremW.W1W asm hpw i E Dt Ctx ls0 l b n s c []

/-- **A block inside `Wf` at `W1W`'s parameters is inside `W1W`**, at no
outside move (the target's marks are `PhRec.μ`, `AbOffW.marks_target`). -/
theorem blk_W1 (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) {R : Region} {F : MachineData → Prop}
    {K' : State → State → Prop} {nd : ND} {blk : List (Directive × Nat)}
    (h : BlkW WfL K' (Ly).exe (Ly).endPc R F nd blk) :
    BlkW Wq (fun _ _ => False) (Ly).exe (Ly).endPc R F nd blk := by
  unfold WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact WakePh.CalWf.blkW_noK h fun _ _ h => h

/-- **A node inside `Wf` at `W1W`'s parameters is inside `W1W`** (as
`blk_W1`). -/
theorem node_W1 (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) {R : Region} {F : MachineData → Prop}
    {K' : State → State → Prop} {nd : ND} (h : NodeW WfL K' (Ly).exe (Ly).endPc R F nd) :
    NodeW Wq (fun _ _ => False) (Ly).exe (Ly).endPc R F nd := by
  unfold WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact WakePh.CalWf.nodeW_noK h fun _ _ h => h

set_option maxHeartbeats 6400000 in
/-- **`wcMidW_w1`'s `hwcWf`**: `wc_main`'s own nodes inside `W1W asm … l b
n` at no frames and no outside move, at `Q := QB l b`, in a region with the
frame `[-80, 16]`: the nodes' `SFactsSt2` at `ownGXW` (`hst`, at any move,
e.g. `OwnMid.wcMidW_wcGX`) and placement (`hpl`, e.g.
`PlacedLy.wcMainW_placed`), the second TCB's tid word unmapped under `F`
(`htid`) and off wake's arena and not its counter word (`hoffT`). -/
theorem wcMainW_wf (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    {R : Region} {F F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    {K' : State → State → Prop} (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi)
    (htid : ∀ m, F m → Mem.loadInt m.dmem (t2 (Ly).lab + 56#64) 8 = none)
    (hoffT : ¬ ((WakeOD.arW hpw i).heap ≤ (t2 (Ly).lab + 56#64).toNat ∧
        (t2 (Ly).lab + 56#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨t2 (Ly).lab + 56#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hst : WcMidW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s) K'
      (Ly).exe (Ly).endPc R F F₂ ms J0 (QB l b))
    (hpl : WcMainW (fun s c => PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
      s c []) (fun _ _ => False) (Ly).exe (Ly).endPc R F F₂ ms J0 (QB l b)) :
    WcMainW Wq (fun _ _ => False) (Ly).exe (Ly).endPc R F F₂ ms J0 (QB l b) := by
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hpw)
  have hsite := PlaceWX.site_ofPlaceWX hpw i
  have hpL : (Ly).prog = wakeCells := hpg
  have hcl : ∀ s, WakeOD.ClW hpw i s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl) := fun _ h => h.2
  have e18 : (_root_.Executable.labels (Ly).exe).label ".Lwc_main.x18" = Int64.ofNat 4203326 :=
    hlab _ _ (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
  have e19 : (_root_.Executable.labels (Ly).exe).label ".Lwc_main.x19" = Int64.ofNat 4203349 :=
    hlab _ _ (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
  have e20 := WakePh.WcSp4W.lab_x20 hlab
  have e21 := WakePh.WcSp4W.lab_x21 hlab
  have eti := WakePh.WcSp4W.lab_ti hlab
  have hin := WakePh.WcSp4W.sp4In
  have hr := Spike.Lib.X64.Flow.WakeWc.wake_wcResIn
  simp only [Spike.Lib.X64.Flow.WakeWc.wcResIn, Bool.and_eq_true] at hr
  have h3 := WakePh.Tcb2Call.wake_tcb2CallIn
  simp only [WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at h3
  have hpush : blockAtB wakeCells "scc_rt_thread_init" 0 [((AI.push .rbp).toDir, 1)] = true := by
    have e : WakePh.WcSp4W.tiPush = [((AI.push .rbp).toDir, 1)] := by decide
    rw [← e]; exact WakePh.WcSp4W.wake_tiPush
  refine ⟨?_, fun c0 cA m fr hM => ?_, fun c0 ty l' cA m fr hM => ⟨?_, ?_, ?_, ?_⟩,
    fun c0 ty l' cA m fr hM => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- `bl`: the reserve's call block
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl hr.1 rfl
      resB_ok hR (by omega) (by omega) hst.res.bl ?_ (by decide +kernel) (by decide)
      (fun σ c h => by obtain ⟨⟨_, _, _, hq⟩, _⟩ := h; exact ctl_box (.inl hq.2.2.1)) hpl.bl)
    intro j hj; dsimp only [rN]; rw [e18]; revert j; decide +kernel
  -- `sp3`: `.x19`'s block to the second TCB's call
  · obtain ⟨_, _, hq, -⟩ := hM.1
    refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl h3.1
      (ofNat_zero' _) tcb2Call_ok hR (by omega) (by omega) (hst.sp3 c0 cA m fr hM).blk ?_ (by decide +kernel)
      (by decide) (fun σ c h => by rw [h.1]; exact ctl_box (.inl hq.2.2.1)) (hpl.sp3 c0 cA m fr hM))
    intro j hj; dsimp only [wcN3]; rw [e19]; revert j; decide +kernel
  -- `pre`: `.x20`'s nodes up to `scc_rt_thread_init`'s entry
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl hin.1
      (ofNat_zero' _) x20A_ok hR (by omega) (by omega) (hst.sp4 c0 ty l' cA m fr hM).n20 ?_ (by decide +kernel)
      (by decide) (fun σ c h => by rw [h.1.1]; exact ctl_box (.inl hM.1.2.1)) (hpl.pre c0 ty l' cA m fr hM).n20)
    intro j hj; dsimp only [aN]; rw [e20]; revert j; decide +kernel
  · refine node_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.nodeCst hpL hlo hΛ hlab hsite hcl hin.2.1 rfl
      (hst.sp4 c0 ty l' cA m fr hM).n20s ?_ (by decide +kernel)
      (fun σ c h => by rw [h.1.1]; exact ctl_box (.inl hM.1.2.1)) (hpl.pre c0 ty l' cA m fr hM).n20s
      (fun σ c m' h hm => by
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx h.1.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact htid m' hm)
      (fun σ c m' h _ => by
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx h.1.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact hoffT))
    dsimp only [aN]; rw [e20]; decide +kernel
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl hin.2.2.1 rfl
      initCall_ok hR (by omega) (by omega) (hst.sp4 c0 ty l' cA m fr hM).n20p ?_ (by decide +kernel)
      (by decide) (fun σ c h => by rw [h.1]; exact ctl_box (.inl hM.1.2.1)) (hpl.pre c0 ty l' cA m fr hM).n20p)
    intro j hj; dsimp only [aN, WakePh.WcSp4.wcN20p]; rw [e20]; revert j; decide +kernel
  · refine node_W1 hpw i asm E Dt Ctx ls0 l b n hpa (nodeCpush hpL hlo hΛ hlab hsite hcl (lo' := -80) (hi' := 16)
      hpush (ofNat_zero' _) (show (AI.push .rbp).ok (-80) 16 oC = true by decide) hR (by omega) hhi
      (hst.sp4 c0 ty l' cA m fr hM).nI ?_ (by decide +kernel)
      (fun σ c h => by rw [h.1]; exact ctl_box (.inl hM.1.2.1)) (hpl.pre c0 ty l' cA m fr hM).nI)
    dsimp only [wcNI]; rw [eti]; decide +kernel
  -- `clone`: `.x21`'s nodes to the `syscall`, the source published past the `mfence`
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl hin.2.2.2.1
      (ofNat_zero' _) x21A_ok hR (by omega) (by omega) (hst.sp4 c0 ty l' cA m fr hM).clone.n21 ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctl_box (.inl hM.1.2.1))
      (hpl.clone c0 ty l' cA m fr hM).n21)
    intro j hj; dsimp only [wcN21]; rw [e21]; revert j; decide +kernel
  · refine node_W1 hpw i asm E Dt Ctx ls0 l b n hpa (nodeCfence hpL hlo hΛ hlab hsite hcl hin.2.2.2.2.1 rfl
      (hst.sp4 c0 ty l' cA m fr hM).clone.nf ?_ (by decide +kernel)
      (fun σ c h => by rw [h.1]; exact ctl_box (.inl hM.1.2.1)) (hpl.clone c0 ty l' cA m fr hM).nf)
    dsimp only [wcNf]; rw [e21]; decide +kernel
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl
      hin.2.2.2.2.2.1 rfl cloneLd_ok hR (by omega) (by omega) (hst.sp4 c0 ty l' cA m fr hM).clone.na ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctl_box (.inr rfl))
      (hpl.clone c0 ty l' cA m fr hM).na)
    intro j hj; dsimp only [wcNa]; rw [e21]; revert j; decide +kernel
  · refine node_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.nodeCfi hpL hlo hΛ hlab hsite hcl
      hin.2.2.2.2.2.2.1 rfl (hst.sp4 c0 ty l' cA m fr hM).clone.nd ?_ (by decide +kernel)
      (fun σ c h => by rw [h.1.1]; exact ctl_box (.inr rfl)) (hpl.clone c0 ty l' cA m fr hM).nd)
    dsimp only [wcNd]; rw [e21]; decide +kernel
  · refine node_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.nodeCfi hpL hlo hΛ hlab hsite hcl
      hin.2.2.2.2.2.2.2.1 rfl (hst.sp4 c0 ty l' cA m fr hM).clone.n10 ?_ (by decide +kernel)
      (fun σ c h => by rw [h.1.1.1]; exact ctl_box (.inr rfl)) (hpl.clone c0 ty l' cA m fr hM).n10)
    dsimp only [wcN10]; rw [e21]; decide +kernel
  · refine blk_W1 hpw i asm E Dt Ctx ls0 l b n hpa (WakePh.CalWf.blkCn hpL hlo hΛ hlab hsite hcl
      hin.2.2.2.2.2.2.2.2 rfl nrB_ok hR (by omega) (by omega) (hst.sp4 c0 ty l' cA m fr hM).clone.nr ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1.1.1]; exact ctl_box (.inr rfl))
      (hpl.clone c0 ty l' cA m fr hM).nr)
    intro j hj; dsimp only [wcNr]; rw [e21]; revert j; decide +kernel

/-- **`wcMainW_wf` at one ghost of `Box`** (`hB`, `l` fresh in the start's
labels, `hl`): the region's bounds from `BoxPure`, the placement from
`PlacedLy.wcMainW_placed`. -/
theorem wcMainW_wfB (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    {F0 : MachineData → Prop} {R : Region} {F F₂ : MachineData → Prop} {ms : Spike.Lib.MemSide isa}
    {J0 : Spike.Lib.X64.AS → Ctl → Prop} {t : UInt64} {K' : State → State → Prop}
    (hB : BoxPure (Ly) F0 n R F J0 t) (hl : Spike.Lib.X64WakeLoadT.L0T (Ly).Λ l = none)
    (htid : ∀ m, F m → Mem.loadInt m.dmem (t2 (Ly).lab + 56#64) 8 = none)
    (hoffT : ¬ ((WakeOD.arW hpw i).heap ≤ (t2 (Ly).lab + 56#64).toNat ∧
        (t2 (Ly).lab + 56#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨t2 (Ly).lab + 56#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc)
    (hst : WcMidW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) (ntA (Ly).lab)) s) K'
      (Ly).exe (Ly).endPc R F F₂ ms J0 (QB l b)) :
    WcMainW Wq (fun _ _ => False) (Ly).exe (Ly).endPc R F F₂ ms J0 (QB l b) := by
  have hpl := WakePh.PlacedLy.wcMainW_placed (F₂ := F₂) (exe := (Ly).exe) (endPc := (Ly).endPc) (ms := ms)
    (b := b) hB hl
  obtain ⟨⟨hR, -, -, hRlo, hhi⟩, -⟩ := hB
  exact wcMainW_wf hpw i asm E Dt Ctx ls0 l b n hpg hlo hpa hR (by omega) hhi htid hoffT hst hpl

end W1

end Spike.Lib.X64.WakeWcW1I

/-- info: 'Spike.Lib.X64.WakeWcW1I.boxT_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.boxT_run

/-- info: 'Spike.Lib.X64.WakeWcW1I.boxT_runWf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.boxT_runWf

/-- info: 'Spike.Lib.X64.WakeWcW1I.ctl_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.ctl_box

/-- info: 'Spike.Lib.X64.WakeWcW1I.nodeCg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.nodeCg

/-- info: 'Spike.Lib.X64.WakeWcW1I.nodeCfence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.nodeCfence

/-- info: 'Spike.Lib.X64.WakeWcW1I.nodeCpush' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.nodeCpush

/-- info: 'Spike.Lib.X64.WakeWcW1I.blk_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.blk_W1

/-- info: 'Spike.Lib.X64.WakeWcW1I.node_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.node_W1

/-- info: 'Spike.Lib.X64.WakeWcW1I.wcMainW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.wcMainW_wf

/-- info: 'Spike.Lib.X64.WakeWcW1I.wcMainW_wfB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWcW1I.wcMainW_wfB
