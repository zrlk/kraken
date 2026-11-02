/-
**`print`'s abort with a fact at every node of the path** (x86-64): the x64 twin of
`Spike/Lib/A64HelloAbortObl.lean`. The write abort path's obligations
inside `NNZXH` (`Spike/Lib/X64HelloAbortX.lean`) with `Z` asked node by node
(`AbortObl`). A pc-only `Z` cannot carry facts of the path's states (the
write abort's phase `WriteAb.Ab`: `%rdi = 4` at the dispatcher's prologue,
`4` at `-8(%rbp)` at its tests), which the nodes' invariants
(`Abort.Disp.DN.nd4`) hold.

- `AbortObl Z … c0`: `Z` at every node of `Abort.Disp.StubWW`'s write abort
  path for the source control `c0` (the `write` call's node `sys` included).
- `AbortObl.and`, `AbortObl.mono`, `AbortObl.triv`.
- `blkZA_ofPc`, `nodeW_ofPc`: `Z` at a node's states from a fact of the pc
  in `abortRuns` given `RelWS` there; `AbortObl.ofPc`: the pc-only form gives
  `AbortObl`, with no new premise (each node's `RelWS` proved: the path's
  blocks covered, the `leaq` runs to `.done`, the `syscall`s fault).
- `blkW_nnzXA`, `nodeW_nnzXA`, `nodeW_nnzXSvcA`: a node's states `NNZXH`
  from `Z` at the node.
- `stubWW_nnzXA`, `seg_jabort4XA`: `StubWW` inside `NNZXH`, and a jump to
  `scc_rt_abort` with `%rdi = 4` inside `NNZXH` does not return, from
  `AbortObl`; `jabort_callee`: the callee region's facts.

**Unlike AArch64** (forced by the x64 shape, `Spike/Lib/X64AbortWriteW.lean`,
`Spike/Lib/X64AbortStubCode.lean`):
- the stub's nodes are `e`, `n1` (the `leaq`), `n2`, `sys` (the `write`
  call), `n5`, `ex`: there is no `n1b` (AArch64's `adrp`/`add` pair is one
  `leaq`), and the system-call field is `sys` (AArch64: `svc`), the node
  `stubWW_of_code` turns into the `write` call's segment;
- the dispatcher is entered with `%rdi = 4` (AArch64: `x0`) and runs in the
  callee's region `[-24, 16)` at the frame base `nC.o.sp - 8`, the return
  address pushed (AArch64: `[-48, 0)` at `nC.o.sp`); the region needs no
  alignment premise (x86-64's `blk_exec_done` takes none), so `ofPc` and
  `jabort_callee` have none (AArch64: `hal`, `h16`), and `seg_jabort4XA`
  takes `seg_jabort4W`'s `hhi : nC.o.sp + 8 ≤ R.hi`, `h8 : nC.o.sp % 8 = 0`;
- the fact given at the path's states is `RelWS` (`Spike/Lib/X64RelWS.lean`,
  x86-64's `RelZ`), and the pcs are byte offsets after `abortRuns`'s labels.
-/
import Spike.Lib.X64HelloAbortX
import Spike.Lib.X64AbortStubCode
import Spike.Lib.X64RelWS

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.PcRuns (PcIn)

/-- **`Z` at every node of the write abort path** for the source control
`c0` (`Abort.Disp.StubWW`'s node fields, in its region `R` and frame
condition `F`; the `write` call's node `sys`, `stubWW_of_code`'s `hsys`). -/
structure AbortObl (Z : Frag isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0
  dt1 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1
  dj1 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j1) Abort.Disp.j1
  dt2 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t2) Abort.Disp.t2
  dj2 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j2) Abort.Disp.j2
  dt3 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t3) Abort.Disp.t3
  dj3 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j3) Abort.Disp.j3
  dt4 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t4) Abort.Disp.t4
  dg4 : NodeZA Z exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .g4) Abort.Disp.g4
  se : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .e) Abort.x0
  sn1 : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1)
  sn2 : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n2) Abort.x1Write
  sys : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys)
  sn5 : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n5) Abort.x2
  sex : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex)

section AbortObl

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {Z Z' : Frag isa}

/-- **Two `AbortObl`s combine.** -/
theorem AbortObl.and (h : AbortObl Z exe endPc R F c0) (h' : AbortObl Z' exe endPc R F c0) :
    AbortObl (fun s c => Z s c ∧ Z' s c) exe endPc R F c0 where
  de := NodeZA.and h.de h'.de
  dt1 := NodeZA.and h.dt1 h'.dt1
  dj1 := NodeZA.and h.dj1 h'.dj1
  dt2 := NodeZA.and h.dt2 h'.dt2
  dj2 := NodeZA.and h.dj2 h'.dj2
  dt3 := NodeZA.and h.dt3 h'.dt3
  dj3 := NodeZA.and h.dj3 h'.dj3
  dt4 := NodeZA.and h.dt4 h'.dt4
  dg4 := NodeZA.and h.dg4 h'.dg4
  se := NodeZA.and h.se h'.se
  sn1 := fun s c hA => ⟨⟨(h.sn1 s c hA).1, (h'.sn1 s c hA).1⟩, fun _ h => h⟩
  sn2 := NodeZA.and h.sn2 h'.sn2
  sys := fun s c hA => ⟨⟨(h.sys s c hA).1, (h'.sys s c hA).1⟩, fun _ h => h⟩
  sn5 := NodeZA.and h.sn5 h'.sn5
  sex := fun s c hA => ⟨⟨(h.sex s c hA).1, (h'.sex s c hA).1⟩, fun _ h => h⟩

/-- **A weaker fact.** -/
theorem AbortObl.mono (h : AbortObl Z exe endPc R F c0) (hZ : ∀ s c, Z s c → Z' s c) :
    AbortObl Z' exe endPc R F c0 where
  de := h.de.mono hZ
  dt1 := h.dt1.mono hZ
  dj1 := h.dj1.mono hZ
  dt2 := h.dt2.mono hZ
  dj2 := h.dj2.mono hZ
  dt3 := h.dt3.mono hZ
  dj3 := h.dj3.mono hZ
  dt4 := h.dt4.mono hZ
  dg4 := h.dg4.mono hZ
  se := h.se.mono hZ
  sn1 := fun s c hA => ⟨hZ s c (h.sn1 s c hA).1, fun _ h => h⟩
  sn2 := h.sn2.mono hZ
  sys := fun s c hA => ⟨hZ s c (h.sys s c hA).1, fun _ h => h⟩
  sn5 := h.sn5.mono hZ
  sex := fun s c hA => ⟨hZ s c (h.sex s c hA).1, fun _ h => h⟩

/-- **`AbortObl` at `True`.** -/
theorem AbortObl.triv : AbortObl (fun _ _ => True) exe endPc R F c0 :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

/-- `Z` at a block node's states from `RelWS` there and a fact of the pc in
`abortRuns` (the node at `off` bytes after the label `l` of a run, its
cells' offsets within the run, `hb`; its invariant pinning the control to
`c0`, `hc`). -/
theorem blkZA_ofPc {n : ND} {blk : List (Directive × Nat)} {l : Label} {off hi : Nat} (hF : FStable R F)
    (hq : (l, 0, hi) ∈ abortRuns) (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hb : (List.range blk.length).all (fun k => decide (off + cellOff blk k < hi)) = true)
    (hc : ∀ σ c, n.J σ c → c = c0) (hrel : NodeZA (fun s _ => RelWS s) exe endPc R F n blk)
    (hZ : ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelWS s → Z s c0) :
    NodeZA Z exe endPc R F n blk := by
  intro s σ c he hn hdc hpc' hA hD hJ k hk m hA' hDm
  have hr := (hrel s σ c he hn hdc hpc' hA hD hJ k hk m hA' hDm).1
  obtain rfl := hc σ c hJ
  have hlt : off + cellOff blk k < hi := by
    have := List.all_eq_true.mp hb k (List.mem_range.mpr hk)
    simpa using this
  exact ⟨hZ _ he (abPc_of hq off (cellOff blk k) (Nat.zero_le _) hlt he rfl hpc) (hF _ _ hD hDm) hr,
    fun _ h => h⟩

/-- `Z` at a single node's states from `RelWS` at its cell (`hd`) and a fact
of the pc in `abortRuns` (the node at `off` bytes after the label `l` of a
run). -/
theorem nodeW_ofPc {n : ND} {d : Directive} {z : Nat} {l : Label} {off hi : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (hd : ∀ s : State, CellAt s d z → RelWS s)
    (hq : (l, 0, hi) ∈ abortRuns) (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat off)
    (hlt : off < hi) (hc : ∀ σ c, n.J σ c → c = c0)
    (hZ : ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelWS s → Z s c0) :
    NodeW Z (fun _ _ => False) exe endPc R F n :=
  fun s c hAt => by
    obtain ⟨he, hn, -, hpc', σ, -, hD, hJ⟩ := id hAt
    have hr := (nodeW_relW (F := F) (R := R) hcode hd s c hAt).1
    obtain rfl := hc σ c hJ
    exact ⟨hZ s he (abPc_of hq off 0 (Nat.zero_le _) (by omega) he (by rw [hpc', ofNat_zero']) hpc) hD hr,
      fun _ h => h⟩

/-- The pc of a node of the path as a label of `abortRuns` and a byte offset. -/
local macro "pcq" : tactic =>
  `(tactic| first
    | exact (ofNat_zero' _).symm
    | rfl
    | (simp only [Abort.Disp.DN.nd4, Abort.N, Abort.pcSys, Abort.write]
       first | exact (ofNat_zero' _).symm | rfl | (congr 1)))

/-- **`AbortObl` from the pc-only form**: every node's `RelWS` is proved (the
path's blocks covered, the `leaq` runs to `.done`, the `syscall`s fault), so
`Z` may include `RelWS`. The region holds the stub's frame (`hlo`, `hhi`). -/
theorem AbortObl.ofPc [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hF : FStable R F)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hZ : ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelWS s → Z s c0) :
    AbortObl Z exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.X64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.x1Write exe endPc :=
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend hprog .write
  exact
    { de := blkZA_ofPc hF (l := "scc_rt_abort") (off := 0) (hi := 12) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.d0_ok hR (by omega) hhi fun s he hn => dc.e s he hn) hZ
      dt1 := blkZA_ofPc hF (l := ".Lscc_rt_abort.entry") (off := 0) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.t1_ok hR (by omega) hhi fun s he hn => dc.t1 s he hn) hZ
      dj1 := blkZA_ofPc hF (l := ".Lscc_rt_abort.entry") (off := 16) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.j1_ok hR (by omega) hhi fun s he hn => dc.j1 s he hn) hZ
      dt2 := blkZA_ofPc hF (l := ".Lscc_rt_abort.next1") (off := 0) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.t2_ok hR (by omega) hhi fun s he hn => dc.t2 s he hn) hZ
      dj2 := blkZA_ofPc hF (l := ".Lscc_rt_abort.next1") (off := 16) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.j2_ok hR (by omega) hhi fun s he hn => dc.j2 s he hn) hZ
      dt3 := blkZA_ofPc hF (l := ".Lscc_rt_abort.next3") (off := 0) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.t3_ok hR (by omega) hhi fun s he hn => dc.t3 s he hn) hZ
      dj3 := blkZA_ofPc hF (l := ".Lscc_rt_abort.next3") (off := 16) (hi := 18) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.j3_ok hR (by omega) hhi fun s he hn => dc.j3 s he hn) hZ
      dt4 := blkZA_ofPc hF (l := ".Lscc_rt_abort.next5") (off := 0) (hi := 16) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h.1)
        (blkW_relW Abort.Disp.t4_ok hR (by omega) hhi fun s he hn => dc.t4 s he hn) hZ
      dg4 := blkZA_ofPc hF (l := ".Lscc_rt_abort.is6") (off := 0) (hi := 9) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h)
        (blkW_relW Abort.Disp.g4_ok hR (by omega) hhi fun s he hn => dc.g4 s he hn) hZ
      se := blkZA_ofPc hF (l := "scc_rt_abort_write") (off := 0) (hi := 8) (by simp [abortRuns]) (by pcq)
        (by decide +kernel) (fun _ _ h => h)
        (blkW_relW Abort.x0_ok hR hlo hhi fun s he hn => sc.e s he hn) hZ
      sn1 := nodeW_ofPc (l := ".Lscc_rt_abort_write.entry") (off := 0) (hi := 52) (fun s he hn => sc.n1 s he hn)
        (fun _ hc => relWS_done ⟨_, exec_si hc⟩) (by simp [abortRuns]) (by pcq) (by decide) (fun _ _ h => h) hZ
      sn2 := blkZA_ofPc hF (l := ".Lscc_rt_abort_write.entry") (off := 7) (hi := 52) (by simp [abortRuns])
        (by pcq) (by decide +kernel) (fun _ _ h => h)
        (blkW_relW Abort.x1Write_ok hR hlo hhi fun s he hn => sc.n2 s he hn) hZ
      sys := nodeW_ofPc (l := ".Lscc_rt_abort_write.entry") (off := 34) (hi := 52) (fun s he hn => sc.sys s he hn)
        (fun _ hc => relWS_syscall hc) (by simp [abortRuns]) (by pcq) (by decide) (fun _ _ h => h.1) hZ
      sn5 := blkZA_ofPc hF (l := ".Lscc_rt_abort_write.entry") (off := 36) (hi := 52) (by simp [abortRuns])
        (by pcq) (by decide +kernel) (fun _ _ h => h)
        (blkW_relW Abort.x2_ok hR hlo hhi fun s he hn => sc.n5 s he hn) hZ
      sex := nodeW_ofPc (l := "scc_rt_abort_write_exit") (off := 0) (hi := 2) (fun s he hn => sc.ex s he hn)
        (fun _ hc => relWS_syscall hc) (by simp [abortRuns]) (by pcq) (by decide) (fun _ _ h => h.1) hZ }

end AbortObl

section AbortXA

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isa} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

/-- **A block node's states are `NNZXH`** from `Z` at the node: its block
has no `nop` or `syscall`. -/
theorem blkW_nnzXA {n : ND} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hb : blk.all (fun c => notNop c.1) = true)
    (hz : NodeZA Z exe endPc R F n blk) :
    BlkW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hD hJ k hk m hA' hD'
  refine ⟨⟨?_, (hz s σ c he hn hd hpc hA hD hJ k hk m hA' hD').1⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZXH`** from `Z` at the node: its first
directive is not a `nop` or a `syscall`. -/
theorem nodeW_nnzXA {n : ND} {d : Directive} {z : Nat} {ds : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ((d, z) :: ds)) (hd : notNop d = true)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hs =>
    ⟨⟨nn_of_cellP ((hcode s hs.1 hs.2.1).cell0 rfl rfl hs.2.2.2.1) hs.1 hs.2.1 hd, (hz s c hs).1⟩,
      fun _ h => h⟩

/-- **A system call's node's states are `NNZXH`** from `Z` at the node:
the call its invariant decodes is `safeH` at the node's pc and not `exit`
(`hsafe`). -/
theorem nodeW_nnzXSvcA {n : ND} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, z)])
    (hsafe : ∀ s σ c, s.st.2 = n.pc → n.J σ c → ∀ call, syscallCall σ.regs = some call →
      safeH (AbC exe s) call ∧ call ≠ .exit)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hAt => by
    obtain ⟨he, hn, _, hpc, σ, hA, _, hJ⟩ := id hAt
    have hc : CellAt s (op64 .syscall) z := (hcode s he hn).cell0 rfl rfl hpc
    refine ⟨⟨⟨he, hn, Scc.Sem.X64.atNop_false_of_cellAt hc (by intro w w' n h; cases h), fun _ call hd => ?_⟩,
      (hz s c hAt).1⟩, fun _ h => h⟩
    exact hsafe s σ c hpc hJ call (by rw [syscallCall, ← hA.regs]; exact hd)

/-- **The write abort path's obligations inside `NNZXH`** from `Z` at
every node (`stubWW_of_code` with `AbortObl`): the stub's `write(2, …)` and
`exit_group(abortStatus)` are `safeH`'s `AbC` branch and not `exit`. -/
theorem stubWW_nnzXA [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat} {c0 : Ctl}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hZ : AbortObl Z exe endPc R F c0)
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubWW (NNZXH exe endPc Z) (fun _ _ => False) p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.X64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.x1Write exe endPc :=
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend hprog .write
  refine StubW.stubWW_of_code hp hend hprog hK hF
    (blkW_nnzXA (fun s he hn => dc.e s he hn) (by decide) hZ.de)
    (blkW_nnzXA (fun s he hn => dc.t1 s he hn) (by decide) hZ.dt1)
    (blkW_nnzXA (fun s he hn => dc.j1 s he hn) (by decide) hZ.dj1)
    (blkW_nnzXA (fun s he hn => dc.t2 s he hn) (by decide) hZ.dt2)
    (blkW_nnzXA (fun s he hn => dc.j2 s he hn) (by decide) hZ.dj2)
    (blkW_nnzXA (fun s he hn => dc.t3 s he hn) (by decide) hZ.dt3)
    (blkW_nnzXA (fun s he hn => dc.j3 s he hn) (by decide) hZ.dj3)
    (blkW_nnzXA (fun s he hn => dc.t4 s he hn) (by decide) hZ.dt4)
    (blkW_nnzXA (fun s he hn => dc.g4 s he hn) (by decide) hZ.dg4)
    (blkW_nnzXA (fun s he hn => sc.e s he hn) (by decide) hZ.se)
    (nodeW_nnzXA (fun s he hn => sc.n1 s he hn) (by decide) hZ.sn1)
    (blkW_nnzXA (fun s he hn => sc.n2 s he hn) (by decide) hZ.sn2)
    (nodeW_nnzXSvcA (fun s he hn => sc.sys s he hn) ?_ hZ.sys)
    (blkW_nnzXA (fun s he hn => sc.n5 s he hn) (by decide) hZ.sn5)
    (nodeW_nnzXSvcA (fun s he hn => sc.ex s he hn) ?_ hZ.sex) hab
  · rintro s σ c hpc ⟨-, h0, ha⟩ call hd
    obtain ⟨buf, n, hw⟩ := StubW.syscallCall_write ha h0
    rw [hw] at hd
    cases hd
    exact ⟨.inr (.inr (.inl (.inl ⟨hpc, buf, n, rfl⟩))), by rintro ⟨⟩⟩
  · rintro s σ c hpc ⟨-, hax, hdi⟩ call hd
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd101 : σ.regs.rdi.toNat = 101 := by
      simp only [Reg64s.get64] at hdi
      rw [← UInt64.toNat_toBitVec, hdi]; rfl
    rw [syscallCall_exitGroup hx231] at hd
    cases hd
    refine ⟨.inr (.inr (.inl (.inr ⟨hpc, ?_⟩))), by rintro ⟨⟩⟩
    rw [hd101]; rfl

/-- **A jump to `scc_rt_abort` with `%rdi = 4` inside `NNZXH` does not
return**, `Z` at every node of the path in the dispatcher's region for each
caller's state and source control of `nC` (`hZ`; `seg_jabort4W` with
`stubWW_nnzXA`). -/
theorem seg_jabort4XA [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    {Q : Frag isa} {nC : ND} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nC.J σ c → σ.regs.get64 .rdi = 4#64)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32) (hhi : nC.o.sp + 8 ≤ R.hi)
    (h8 : nC.o.sp % 8 = 0) (hK : ms.K = some Scc.Sem.X64.abi)
    (hZ : ∀ m0 σC c0, nC.J σC c0 → AbortObl Z exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) c0)
    (hab : ∀ m0 σC c0, nC.J σC c0 → ∀ s c, At exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC)
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c → ms.abortAt s) :
    SegTC (NNZXH exe endPc Z) p lbl ms (At exe endPc R F nC) Q :=
  SegW.toTC (Abort.Disp.seg_jabort4W hpc hrdi hF hR hlo hhi h8 hK fun m0 σC c0 hJ =>
    stubWW_nnzXA hp hend hprog hK
      (fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide))
      (hZ m0 σC c0 hJ) (hab m0 σC c0 hJ))

/-- **The callee region's facts of `seg_jabort4XA`** (as `seg_jabort4W`
derives them): the dispatcher's region at the frame base `nC.o.sp - 8` is
OK, reaching 24 bytes down and 16 up, and its frame condition stable. -/
theorem jabort_callee {nC : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32)
    (hhi : nC.o.sp + 8 ≤ R.hi) (h8 : nC.o.sp % 8 = 0) (m0 : MachineData) (σC : AS) :
    (R.callee (nC.o.sp - 8) (-24) 16).OK ∧ (R.callee (nC.o.sp - 8) (-24) 16).lo ≤ -24 ∧
      16 ≤ (R.callee (nC.o.sp - 8) (-24) 16).hi ∧
      FStable (R.callee (nC.o.sp - 8) (-24) 16)
        (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) :=
  ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), by simp [Region.callee],
    by simp [Region.callee],
    fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide)⟩

end AbortXA

end Spike.Lib.X64.Flow.Worker

/-- info: 'Spike.Lib.X64.Flow.Worker.AbortObl.ofPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.AbortObl.ofPc

/-- info: 'Spike.Lib.X64.Flow.Worker.seg_jabort4XA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.seg_jabort4XA
