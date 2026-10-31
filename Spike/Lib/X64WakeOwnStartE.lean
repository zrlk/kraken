/-
**wake.w's `scc_rt_start` lifted to `ownGXW`** (x86-64; X64-OwnW lift
layer): `StartWf.startEW_W0S`'s `StartEW` inside `StartWf.WS`
(at `ownG`) is inside `WSX` (at `ownGXW`), given the two callees' states
inside `WSX` (`htcbX`: `scc_rt_alloc_tcb`, the StartTcb twins;
`htiX`: `scc_rt_thread_init`, `OwnSt.tiX`). The start's own nodes classify by
the pc alone (`selfOwn` reads `spPool` only from `.x1` on), except where a
call block ends at a callee's entry (`%rsp` then off the pool, `hoffP`, or on
it, `pool_m8`):

| nodes | pcs | words |
|---|---|---|
| `_start`, `scc_rt_start` up to `.x1` (`EntryW`, `XStartW`, the two call blocks) | `< .x1` (`cst_lowS`) | `[]`, `[]` |
| the call blocks' ends (`scc_rt_alloc_tcb`, `scc_rt_thread_init`) | off the pool (`cst_off`, `hoffP`) | `[]`, `[]` |
| `.x1` to `call scc_rt_main` (`X0WAt.fs`/`sys`/`sw`, `SwEW`) | `InA` (`cst_A`) | `tM`, `[]` |
| `call scc_rt_main`'s end | on the pool (`cst_pool`, `pool_m8`) | `tM`, `[]` |

- `writeTree_silent`: a silent tree writes nothing.
- `blkLP`: `Lft` on a covered block of wakeCells, its pcs in a pc-only class,
  `Cst` at its run's end.
- `nodeLP`: `Lft` at a node, every successor `sz` bytes on, its pc and the
  next in a pc-only class; `nodeLP_step` (the successors from an `hstep`
  fact, as `StartWf.nodeW_W0S_step`), `nodeLP_svc` (a `syscall`).
- `pool_m8`: the new stack's `-8` word on the pool.
- `StartLft`, `startL`: the own nodes (all but the two callees') inside
  `Lft`.
- `startEX`: `StartEW` inside `WSX` (`startL` and the callees').

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartTi
import Spike.Lib.X64WakeStartWf

namespace Spike.Lib.X64.WakePh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.Rt.X64 (code_field codeT_eq blockAtB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt okBlk arun cellOff Abs SI FI swR)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64ConsumerA (StSucc rsp_of_abs)
open Kraken.Promising.Lower.X64 (CellAt op64)
open Spike.Lib (Arena FragS)

/-- **A silent tree writes nothing.** -/
theorem writeTree_silent {σ : Type} {P : σ → Prop} {G : Loc → Val → Prop} :
    ∀ {t : EvTree σ}, Kraken.Promising.Lower.SilentTree P t → WriteTree G t
  | .done _, _ => trivial
  | .choose _ _, h => fun i => writeTree_silent (h.2 i)
  | .fault .., h => h.elim
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim
  | .fence .., h => h.elim

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- **`scc_rt_start`'s own nodes inside `W`** (no outside moves): every
node of `Rt.StartEW` but the two callees' (`St0W.tcb`, `X0WAt.ti`), at any
frame condition `F'` past `_start`. `startL` proves it inside `Lft`; `startEX`
and `startEXP` (`X64WakeOwnStartEP`) combine it with the callees'. -/
structure StartLft (W : Frag isa) (L : RuntimeLayout) (R : Spike.Lib.Region) (F : MachineData → Prop)
    (rS : Range) (n0 k0 : BitVec 64) (c0 : Spike.Lib.Ctl) (D : Int) : Prop where
  e : Spike.Lib.X64.Rt.EntryW W (fun _ _ => False) L.exe L.endPc R F (_root_.Executable.labels L.exe).label c0
  start : ∀ F' : MachineData → Prop, Spike.Lib.X64.Flow.XStartW W (fun _ _ => False) L.exe L.endPc
    (R.callee (-8) (-296) 8) F' (Spike.Lib.X64.Flow.Ret0.startN0 (_root_.Executable.labels L.exe).label c0).J
  blk : ∀ F' : MachineData → Prop, BlkW W (fun _ _ => False) L.exe L.endPc (R.callee (-8) (-296) 8) F'
    (Spike.Lib.X64.Flow.Ret0.startN1R (_root_.Executable.labels L.exe).label c0) Spike.Lib.X64.Flow.Ret0.startCall
  b0 : ∀ F' : MachineData → Prop, BlkW W (fun _ _ => False) L.exe L.endPc (R.callee (-8) (-296) 8) F'
    (Spike.Lib.X64.Flow.Ret0.startN2R (_root_.Executable.labels L.exe).label n0 c0)
    Spike.Lib.X64.Flow.Ret0.startCall2
  fs : ∀ F' : MachineData → Prop, BlkW W (fun _ _ => False) L.exe L.endPc (R.callee (-8) (-296) 8)
    (fun m => F' m ∧ Spike.Lib.X64.Flow.Ret0.StackM rS m)
    (Spike.Lib.X64.Flow.Ret0.startN3 (_root_.Executable.labels L.exe).label n0 k0 c0)
    Spike.Lib.X64.Flow.Ret0.startFs
  sys : ∀ F' : MachineData → Prop, NodeW W (fun _ _ => False) L.exe L.endPc (R.callee (-8) (-296) 8)
    (fun m => F' m ∧ Spike.Lib.X64.Flow.Ret0.StackM rS m)
    (Spike.Lib.X64.Flow.Ret0.startN4 (_root_.Executable.labels L.exe).label
      (Spike.Lib.X64.Flow.Ret0.pinA (_root_.Executable.labels L.exe).label + n0 + 8#64)
      (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels L.exe).label + k0 + 16384#64) c0)
  sw : ∀ F' : MachineData → Prop, BlkW W (fun _ _ => False) L.exe L.endPc (R.callee (-8) (-296) 8)
    (fun m => F' m ∧ Spike.Lib.X64.Flow.Ret0.StackM rS m)
    (Spike.Lib.X64.Flow.Ret0.startN5 (_root_.Executable.labels L.exe).label
      (Spike.Lib.X64.Flow.Ret0.pinA (_root_.Executable.labels L.exe).label + n0 + 8#64)
      (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels L.exe).label + k0 + 16384#64) c0)
    Spike.Lib.X64.Flow.Ret0.startSw
  s3 : ∀ F' : MachineData → Prop, Spike.Lib.X64.Rt.SwEW W (fun _ _ => False) L.exe L.endPc
    (R.callee (-8) (-296) 8) (fun m => F' m ∧ Spike.Lib.X64.Flow.Ret0.StackM rS m) rS
    (Spike.Lib.X64.Flow.Ret0.pinA (_root_.Executable.labels L.exe).label + n0 + 8#64)
    (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels L.exe).label + k0 + 16384#64) c0 D

section P

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`Lft` on a covered block of wakeCells, by the pc**: its pcs in `P`
(off the take site, `hP`; `Cst` there by the pc alone, `hcls`), `Cst` where
its run ends (`hfin`). -/
theorem blkLP {n : ND} {blk : List (Directive × Nat)} {l : Label} {k N : Nat} {blo bhi : Int}
    {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (el : L.lab l = Int64.ofNat N)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → Cst L c1 c2 s)
    (h1 : ∀ j < blk.length, P (Int64.ofNat N + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) → Cst L c1 c2 s) :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n blk := by
  have h1' : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat := by
    rw [← he, el]; exact h1
  have hQ : ∀ σ c, n.J σ c → ∀ j < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk j)) → Cst L c1 c2 s :=
    fun σ c _ j hj s m _ _ _ hs' => hcls s (by unfold pcOf; rw [hs']; exact h1' j hj)
  refine BlkW.lft (blkW_cstOk hsep ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
    hhi ?_ hQ ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1' j hj)
  · intro σ c hJ j hj s m hA he' hn hs'
    rcases Nat.lt_or_ge (j + 1) blk.length with hj1 | hj1
    · rw [Spike.Lib.X64.arun_pc _ hok hj1] at hs'
      exact hQ σ c hJ (j + 1) hj1 s m hA he' hn hs'
    · rw [List.take_of_length_le (by omega)] at hA hs'
      exact hfin σ c hJ s m hA he' hn hs'

omit hp hlab hsite in
/-- **`Lft` at a node, by the pc**: every successor `sz` bytes on (`hk`),
its pc and the next in `P` (`Cst` there by the pc alone), its write
condition (`hw`). -/
theorem nodeLP {n : ND} {sz : Nat} {l : Label} {k N : Nat} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (he : L.lab l + Int64.ofNat k = n.pc) (el : L.lab l = Int64.ofNat N)
    (hcls : ∀ s : State, P (pcOf s) → Cst L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P (Int64.ofNat N + Int64.ofNat k).toBitVec.toNat ∧
      P (Int64.ofNat N + Int64.ofNat k + Int64.ofNat sz).toBitVec.toNat)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n := by
  rw [← el, he] at hpc
  refine NodeW.lft (nodeW_cstOk hsep ha hW (fun s c hAt => ⟨hcls s ?_, fun s' h => hcls s' ?_⟩) hw)
  · unfold pcOf; rw [hAt.2.2.2.1]; exact hpc.1
  · unfold pcOf; rw [hk s c hAt s' h]; exact hpc.2

omit hp in
/-- `nodeLP` with the successors from an `hstep` fact (a cell of size `sz`
off `syscall`, its leaves `sz` bytes on), the pc off the take site. -/
theorem nodeLP_step {n : ND} {sz : Nat} {l : Label} {k N : Nat} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (he : L.lab l + Int64.ofNat k = n.pc) (el : L.lab l = Int64.ofNat N)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → Cst L c1 c2 s)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d sz ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat sz)
    (hpc : P (Int64.ofNat N + Int64.ofNat k).toBitVec.toNat ∧
      P (Int64.ofNat N + Int64.ofNat k + Int64.ofNat sz).toBitVec.toNat)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n := by
  have hpc0 : P n.pc.toBitVec.toNat := by rw [← he, el]; exact hpc.1
  refine nodeLP hsep ha hW he el hcls (fun s c hAt s' h => ?_) hpc hw
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hAt
  have hpc' : s.st.2 = n.pc := hAt.2.2.2.1
  have hns : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pcOf s ≠ x := by
    intro x hx; rw [hsite] at hx; cases hx; rw [siteV hlab]; unfold pcOf; rw [hpc']; exact hP _ hpc0
  rw [Spike.Lib.X64.WakePh.WcW.succ_pc hc hd hex hl hns h, hpc']

omit hlab hsite in
/-- `nodeLP` at a `syscall` (every successor `sz` bytes on, `keep_syscall`;
no write condition: the node is at a system call). -/
theorem nodeLP_svc {n : ND} {sz : Nat} {l : Label} {k N : Nat} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hb : blockAtB wakeCells l k [(op64 .syscall, sz)] = true)
    (he : L.lab l + Int64.ofNat k = n.pc) (el : L.lab l = Int64.ofNat N)
    (hcls : ∀ s : State, P (pcOf s) → Cst L c1 c2 s)
    (hpc : P (Int64.ofNat N + Int64.ofNat k).toBitVec.toNat ∧
      P (Int64.ofNat N + Int64.ofNat k + Int64.ofNat sz).toBitVec.toNat) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n := by
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc [(op64 .syscall, sz)] :=
    fun s hs hn => code_field L.lays rfl (hp ▸ hb) he s hs hn
  have hcell : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (op64 .syscall) sz :=
    fun s c ⟨hs, hn, _, hpc', _⟩ => (hcode s hs hn).cell0 rfl rfl hpc'
  refine nodeLP hsep ha hW he el hcls (fun s c hAt s' h => ?_) hpc
    (fun s c hAt hns => by
      have h' : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt (hcell s c hAt)
      rw [hns] at h'; cases h')
  have hc := hcell s c hAt
  rw [keep_pc hc (keep_syscall (Scc.Sem.X64.atSyscall_of_cellAt hc) h), hAt.2.2.2.1]

omit hp hlab hsite hsep ha hW in
/-- **The new stack's `-8` word is on the pool**: the stack `[b, b + 16384)`
inside the pool (`hsub`), the pool fitting the address space. -/
theorem pool_m8 {b : BitVec 64} {D : Int} (hsub : (⟨b.toNat, 16384⟩ : Range).Sub L.Λ.stackPool) :
    L.Λ.stackPool.lo < ((swR (b + 16384#64) (-D) 0).addr (-8)).toNat ∧
      ((swR (b + 16384#64) (-D) 0).addr (-8)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size := by
  have hf := L.pool_fit
  obtain ⟨h1, h2⟩ := hsub
  simp only at h1 h2
  have hb : b.toNat + 16384 < 2 ^ 64 := by omega
  have e : ((swR (b + 16384#64) (-D) 0).addr (-8)).toNat = b.toNat + 16376 := by
    simp only [swR, Spike.Lib.Region.addr]
    have : BitVec.ofInt 64 (-8) = 18446744073709551608#64 := by decide
    rw [this]; bv_omega
  rw [e]; omega

/-- A label of wakeCells through `L.exe`'s labels, decided. -/
local macro "elab_dec" : term => `(hlab _ _ (by rw [← codeT_eq]; decide +kernel))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6400000 in
/-- **`scc_rt_start`'s own nodes inside `Lft`** (`StartLft`): every node
of `StartEW` but the two callees', by the pc (`blkLP`, `nodeLP_step`,
`nodeLP_svc`). The two call blocks end at the callees' entries on a stack
whose `-48` word in `scc_rt_start`'s region is off the pool (`hoffP`, as
`startEW_W0S`); `call scc_rt_main` ends at the new stack's `-8` word, on the
pool (`pool_m8`, from `hrS`, `hsub` as `startEW_W0S`). -/
theorem startL (hlo : L.Λ.code.lo = lo) {rS : Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {D : Int}
    (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hL : 8 ≤ D)
    (hok : (swR (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool) :
    StartLft (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) L R F rS n0 k0 c0 D := by
  have hI := Spike.Lib.X64.WakePh.instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  -- The labels.
  have eSt : L.lab "_start" = Int64.ofNat 4198400 := elab_dec
  have eS : L.lab "scc_rt_start" = Int64.ofNat 4198413 := elab_dec
  have eE : L.lab Spike.Lib.X64.Flow.startE = Int64.ofNat 4198421 := elab_dec
  have eX0 : L.lab Spike.Lib.X64.Flow.Ret0.x0L = Int64.ofNat 4198487 := elab_dec
  have eX1 : L.lab Spike.Lib.X64.Flow.Ret0.x1L = Int64.ofNat 4198500 := elab_dec
  have eSt' : (_root_.Executable.labels L.exe).label "_start" = Int64.ofNat 4198400 := eSt
  have eS' : (_root_.Executable.labels L.exe).label "scc_rt_start" = Int64.ofNat 4198413 := eS
  have eE' : (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.startE = Int64.ofNat 4198421 := eE
  have eX0' : (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.x0L = Int64.ofNat 4198487 := eX0
  have eX1' : (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.x1L = Int64.ofNat 4198500 := eX1
  have eAT' : (_root_.Executable.labels L.exe).label "scc_rt_alloc_tcb" = Int64.ofNat 4198992 := elab_dec
  have eTI' : (_root_.Executable.labels L.exe).label "scc_rt_thread_init" = Int64.ofNat 4199545 := elab_dec
  have eM' : (_root_.Executable.labels L.exe).label "scc_rt_main" = Int64.ofNat 4198540 := elab_dec
  -- The code.
  have hrc := wake_rtCodeIn0
  have hs0 := hrc.start0
  simp only [Spike.Lib.X64.Rt.Code.Start.entryIn, Bool.and_eq_true] at hs0
  obtain ⟨⟨e0, e2⟩, e6⟩ := hs0
  have hst := hrc.start
  simp only [Spike.Lib.X64.Flow.startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl' := hrc.call
  simp only [Spike.Lib.X64.Flow.Ret0.startCallIn, Bool.and_eq_true] at hcl'
  obtain ⟨cc, -⟩ := hcl'
  have hcl2 := hrc.call2
  simp only [Spike.Lib.X64.Flow.Ret0.startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [Spike.Lib.X64.Flow.Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, tSwDir⟩, tXor⟩, tMain⟩ := htl
  have hR' := Spike.Lib.Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide)
    (by omega) (by omega)
  -- The classes.
  have hPL : ∀ q : Nat, q < 4198500 → q ≠ 4200277 := fun q hq => by omega
  have hPA : ∀ q : Nat, InA q → q ≠ 4200277 := fun q hq => by unfold InA at hq; omega
  have hcL : ∀ s : State, pcOf s < 4198500 → Cst L [] [] s := fun s h => cst_lowS hlab h
  have hcA : ∀ s : State, InA (pcOf s) → Cst L (tM L) [] s := fun s h => cst_A hlab h
  refine ⟨⟨?_, ?_, ?_⟩, fun F' => ⟨?_, ?_, ?_, ?_⟩, fun F' => ?_, fun F' => ?_, fun F' => ?_, fun F' => ?_,
    fun F' => ?_, fun F' => ⟨?_, fun v => ?_, fun v => ?_⟩⟩
  · -- `_start`'s `xorl %ebp, %ebp`.
    exact nodeLP_step hlab hsite hsep ha hW (ofNat_zero' _) eSt hPL hcL
      (Spike.Lib.X64.WakeWf.fi_step hI (hp ▸ e0) (ofNat_zero' _)) (by decide +kernel) hw_nil
  · -- `_start`'s `andq $-16, %rsp`.
    refine nodeLP_step hlab hsite hsep ha hW (k := 2) (sz := 4) rfl eSt hPL hcL (fun s c hA => ?_)
      (by decide +kernel) hw_nil
    have hc : CellAt s (Spike.Lib.X64.andRsp (-16)) 4 :=
      Spike.Lib.X64.Rt.cellOf hI (hp ▸ e2) rfl hA.1 hA.2.1 hA.2.2.2.1
    obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_andRsp hc
    refine ⟨_, t, hc, (by intro w w' h; cases h), hex, fun s' hu => ?_⟩
    obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakeWf.silentLeaf hst hu
    rfl
  · -- `_start`'s call.
    refine blkLP hp hlab hsite hsep ha hW (k := 6) e6
      (by show _ = L.lab "_start" + Int64.ofNat 2 + Int64.ofNat 4; rw [Int64.add_assoc]; rfl) eSt
      Spike.Lib.X64.Rt.entryCallB_ok hR (by omega) hhi hPL hcL (by decide +kernel) ?_
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Rt.entryN2] at hs'
    rw [Spike.Lib.X64.Rt.entryCallB_run] at hs'
    exact cst_lowS hlab (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
  · -- The frame's setup.
    refine blkLP hp hlab hsite hsep ha hW (k := 0) cb0 (ofNat_zero' _) eS Spike.Lib.X64.Flow.xStart0_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPL hcL (by decide +kernel) ?_
    intro σ c _ s m _ _ _ hs'
    rw [Spike.Lib.X64.Flow.xStart0_run] at hs'
    exact cst_lowS hlab (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
  · -- The handler's `lea`.
    exact nodeLP_step hlab hsite hsep ha hW (k := 0) (sz := 7) (ofNat_zero' _) eE hPL hcL
      (Spike.Lib.X64.WakeWf.si_step hI (hp ▸ cbSi) (ofNat_zero' _)) (by decide +kernel) hw_nil
  · -- The arguments.
    refine blkLP hp hlab hsite hsep ha hW (k := 7) cbArgs rfl eE Spike.Lib.X64.Flow.xStartArgs_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPL hcL (by decide +kernel) ?_
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.xStartN2] at hs'
    rw [Spike.Lib.X64.Flow.xStartArgs_run, Spike.Lib.X64.Rt.StartU.startE41] at hs'
    exact cst_lowS hlab (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
  · -- `rt_sigaction`'s `syscall`.
    exact nodeLP_svc hp hsep ha hW (P := fun q => q < 4198500) (k := 41) (sz := 2) cbSys (Spike.Lib.X64.Rt.StartU.startE41 _).symm eE hcL
      (by decide +kernel)
  · -- The call block of `scc_rt_alloc_tcb`: ends off the pool (`hoffP`).
    refine blkLP hp hlab hsite hsep ha hW (k := 43) cc rfl eE Spike.Lib.X64.Flow.Ret0.startCall_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPL hcL (by decide +kernel) ?_
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN1R] at hA hs'
    rw [Spike.Lib.X64.Flow.Ret0.startCall_run] at hA hs'
    have hm : s.st.1 = m := by rw [hs']
    refine cst_off hlab (fun hsp => hoffP ?_) (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
    unfold spPool at hsp; rw [hm, rsp_of_abs hA] at hsp; exact hsp
  · -- `.x0`'s block, the call of `scc_rt_thread_init`: ends off the pool.
    refine blkLP hp hlab hsite hsep ha hW (k := 0) cc2 (ofNat_zero' _) eX0 Spike.Lib.X64.Flow.Ret0.startCall2_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPL hcL (by decide +kernel) ?_
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN2R] at hA hs'
    rw [Spike.Lib.X64.Flow.Ret0.startCall2_run] at hA hs'
    have hm : s.st.1 = m := by rw [hs']
    refine cst_off hlab (fun hsp => hoffP ?_) (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
    unfold spPool at hsp; rw [hm, rsp_of_abs hA] at hsp; exact hsp
  · -- `.x1`'s block.
    refine blkLP hp hlab hsite hsep ha hW (k := 0) tFs (ofNat_zero' _) eX1 Spike.Lib.X64.Flow.Ret0.startFs_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPA hcA (by decide +kernel) ?_
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN3] at hs'
    rw [Spike.Lib.X64.Flow.Ret0.startFs_run] at hs'
    exact cst_A hlab (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
  · -- `arch_prctl`'s `syscall`.
    exact nodeLP_svc hp hsep ha hW (P := InA) (k := 18) (sz := 2) tSys rfl eX1 hcA (by decide +kernel)
  · -- The block before the switch.
    refine blkLP hp hlab hsite hsep ha hW (k := 20) tSw rfl eX1 Spike.Lib.X64.Flow.Ret0.startSw_ok hR'
      (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) hPA hcA (by decide +kernel) ?_
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN5] at hs'
    rw [Spike.Lib.X64.Flow.Ret0.startSw_run, Int64.add_assoc] at hs'
    exact cst_A hlab (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
  · -- The switch.
    have hop : Spike.Lib.X64.RegOnly
        (Operation.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))) : Operation .W64) = true := rfl
    refine nodeLP_step hlab hsite hsep ha hW (k := 28) (sz := 3) rfl eX1 hPA hcA (fun s c hA => ?_)
      (by decide +kernel) (fun s c hA _ tree hex => ?_)
    · have hc := Spike.Lib.X64.Rt.cellOf hI (hp ▸ tSwDir) rfl hA.1 hA.2.1 hA.2.2.2.1
      refine ⟨_, _, hc, fun w' w'' h => ?_, Spike.Lib.X64.exec_reg hop hc, fun s' hl => by cases hl; rfl⟩
      cases h
    · have hc := Spike.Lib.X64.Rt.cellOf hI (hp ▸ tSwDir) rfl hA.1 hA.2.1 hA.2.2.2.1
      rw [Spike.Lib.X64.exec_reg hop hc] at hex; cases hex; trivial
  · -- After the switch: `xorl %ebp, %ebp` in the new region.
    by_cases hv : v = Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64
    · subst hv
      refine nodeLP_step hlab hsite hsep ha hW (k := 31) (sz := 2) rfl eX1 hPA hcA
        (Spike.Lib.X64.WakeWf.fi_step hI (hp ▸ tXor) rfl) (by decide +kernel) (fun s c hA _ tree hex => ?_)
      have hc := Spike.Lib.X64.Rt.cellOf hI (hp ▸ tXor) rfl hA.1 hA.2.1 hA.2.2.2.1
      obtain ⟨t, hex', hst⟩ := Spike.Lib.X64.exec_fi hc
      rw [hex'] at hex; cases hex
      exact writeTree_silent hst
    · exact Spike.Lib.X64.Rt.nodeW_ofFalse fun _ h => hv h.1.1
  · -- `call scc_rt_main` in the new region: ends on the pool (`pool_m8`).
    by_cases hv : v = Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64
    · subst hv
      refine blkLP hp hlab hsite hsep ha hW (k := 33) tMain rfl eX1 (Spike.Lib.X64.Rt.startMain_okL hL) hok
        (Int.le_refl _) (Int.le_refl _) hPA hcA (by decide +kernel) ?_
      intro σ c _ s m hA _ _ hs'
      dsimp only [Spike.Lib.X64.Flow.Ret0.startN8] at hA hs'
      rw [Spike.Lib.X64.Flow.Ret0.startMain_run] at hA hs'
      have hm : s.st.1 = m := by rw [hs']
      refine cst_pool hlab ?_ (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel) (by unfold pcOf; rw [hs']; simp only [eSt', eS', eE', eX0', eX1', eAT', eTI', eM']; decide +kernel)
      unfold spPool; rw [hm, rsp_of_abs hA]; exact pool_m8 (hrS ▸ hsub)
    · exact Spike.Lib.X64.Rt.blkW_ofFalse fun _ h => hv h.1.1


/-- **wake.w's `scc_rt_start` inside `WSX`** (`StartEW`, from `_start` to
`call scc_rt_main`, `scc_rt_thread_init` returning to `.x7`): `h` (inside
`WS`, `StartWf.startEW_W0S`) and every own node inside `Lft` (`blkLP`,
`nodeLP_step`, `nodeLP_svc`), the two callees' states inside `WSX` (`htcbX`,
`htiX`). The two call blocks end at the callees' entries on a stack whose
`-48` word in `scc_rt_start`'s region is off the pool (`hoffP`, as
`startEW_W0S`); `call scc_rt_main` ends at the new stack's `-8` word, on the
pool (`pool_m8`, from `hrS`, `hsub` as `startEW_W0S`). -/
theorem startEX (hlo : L.Λ.code.lo = lo) {rS : Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {D : Int}
    (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hL : 8 ≤ D)
    (hok : (swR (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (h : Spike.Lib.X64.Rt.StartEW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F rS n0 k0 c0 D Spike.Lib.X64.Rt.Code.Ti.x7L)
    (htcbX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i)
    (htiX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAt (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, Spike.Lib.X64.Flow.Ret0.pinA L.lab + n0 + 8#64, k0, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L i) :
    Spike.Lib.X64.Rt.StartEW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F rS n0 k0 c0 D Spike.Lib.X64.Rt.Code.Ti.x7L := by
  have hw : ∀ s c, WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c → Lft L a ar p Dt Cl Ctx lbl lsize frM X0 s c →
      WSX L a ar p Dt Cl Ctx lbl lsize frM X0 s c := fun _ _ h1 h2 => h2 h1
  have hL' := startL (ar := ar) (p := p) (Dt := Dt) (Cl := Cl) (Ctx := Ctx) (lbl := lbl) (lsize := lsize)
    (frM := frM) (X0 := X0) (F := F) (n0 := n0) (c0 := c0) hp hlab hsite hsep ha hW hlo hR hRlo hhi hL hok hoffP hrS hsub
  exact ⟨Spike.Lib.X64.WakePh.EntryW.imp h.e hL'.e hw, fun F' hFs hKs hF' =>
    ⟨⟨Spike.Lib.X64.WakePh.XStartW.imp (h.s F' hFs hKs hF').s1.start (hL'.start F') hw,
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s1.blk (hL'.blk F') hw, htcbX F' hFs hKs hF'⟩,
    ⟨Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.b0 (hL'.b0 F') hw, htiX F' hFs hKs hF',
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.fs (hL'.fs F') hw,
      Spike.Lib.X64.AllocG.NodeW.imp (h.s F' hFs hKs hF').s2.sys (hL'.sys F') hw,
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.sw (hL'.sw F') hw⟩,
    Spike.Lib.X64.WakePh.SwEW.imp (h.s F' hFs hKs hF').s3 (hL'.s3 F') hw⟩⟩

end P

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.blkLP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.blkLP

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.nodeLP_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.nodeLP_step

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.nodeLP_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.nodeLP_svc

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.startEX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.startEX

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.pool_m8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.pool_m8

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.startL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.startL
