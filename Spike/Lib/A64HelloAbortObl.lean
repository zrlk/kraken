/-
**`print`'s abort with a fact at every node of the path** (row 5i-hab1, AArch64): `A64HelloAbortX`'s
`stubWW_nnzX`/`seg_jabort4X`
with `Z` asked node by node (`AbortObl`) instead of at a pc of
`abortRuns` (`hZ`). A pc-only `Z` cannot carry facts of the path's states
(the write abort's phase `WriteAb.Ab`: `x0 = 4` at the dispatcher's
prologue, `4` at `[sp]` at its tests), which the nodes' invariants
(`Abort.Disp.DN.nd4`) hold.

- `AbortObl Z … c0`: `Z` at every node of `Abort.Disp.StubWW`'s write abort
  path for the source control `c0` (the `svc` node included).
- `AbortObl.ofPc`: the pc-only form gives it, with no new premise (each
  node's `RelZ` proved, as `stubWW_nnzX` does); `AbortObl.and`,
  `AbortObl.mono`.
- `blkW_nnzXA`, `nodeW_nnzXA`, `nodeW_nnzXSvcA`: a node's states `NNZXH` from
  `Z` at the node.
- `stubWW_nnzXA`, `seg_jabort4XA`: `stubWW_nnzX`, `seg_jabort4X` from
  `AbortObl`.
-/
import Spike.Lib.A64HelloAbortX

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ relZ_of_done relZ_svc blkZA_done)

/-- **`Z` at every node of the write abort path** for the source control
`c0` (`Abort.Disp.StubWW`'s node fields, in its region `R` and frame
condition `F`). -/
structure AbortObl (Z : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
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
  se : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .e) Abort.b0
  sn1 : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1)
  sn1b : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1b)
  sn2 : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n2) Abort.b1Write
  svc : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .svc)
  sn5 : NodeZA Z exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n5) Abort.b2
  sex : NodeW Z (fun _ _ => False) exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex)

section AbortObl

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {Z Z' : Frag isaLSE2}

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
  sn1b := fun s c hA => ⟨⟨(h.sn1b s c hA).1, (h'.sn1b s c hA).1⟩, fun _ h => h⟩
  sn2 := NodeZA.and h.sn2 h'.sn2
  svc := fun s c hA => ⟨⟨(h.svc s c hA).1, (h'.svc s c hA).1⟩, fun _ h => h⟩
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
  sn1b := fun s c hA => ⟨hZ s c (h.sn1b s c hA).1, fun _ h => h⟩
  sn2 := h.sn2.mono hZ
  svc := fun s c hA => ⟨hZ s c (h.svc s c hA).1, fun _ h => h⟩
  sn5 := h.sn5.mono hZ
  sex := fun s c hA => ⟨hZ s c (h.sex s c hA).1, fun _ h => h⟩

/-- **`AbortObl` at `True`.** -/
theorem AbortObl.triv : AbortObl (fun _ _ => True) exe endPc R F c0 :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

/-- `Z` at a block node's states from `RelZ` there and a fact of the pc
given `RelZ` (`blkW_nnzX`'s `hZ`). -/
theorem blkZA_ofPc {n : ND} {blk : List Directive} (hF : FStable R F)
    (hrel : NodeZA RelZ exe endPc R F n blk)
    (hZ : ∀ s σ c k, k < blk.length → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) → F s.st.1 →
      n.J σ c → RelZ s c → Z s c) :
    NodeZA Z exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm
  exact ⟨hZ _ σ c k hk he rfl (hF _ _ hD hDm) hJ (hrel s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm).1,
    fun _ h => h⟩

/-- `Z` at a single node's states from `RelZ` at its cell (`nodeW_nnzX`'s
`hrel`, `hZ`). -/
theorem nodeW_ofPc {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds))
    (hrel : ∀ s c, CellAt s d 4 → s.decls = {} → RelZ s c)
    (hZ : ∀ s σ c k, k < 1 → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) → F s.st.1 →
      n.J σ c → RelZ s c → Z s c) :
    NodeW Z (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, hdc, hpc, σ, _, hD, hJ⟩ =>
    ⟨hZ s σ c 0 Nat.zero_lt_one he (by rw [hpc, ofNat4_zero]) hD hJ
      (hrel s c ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) hdc), fun _ h => h⟩

set_option hygiene false in
/-- `RelZ` at a covered block's states: its `okBlk`, its code. -/
local macro "rb " ok:term:max cd:term:max : term =>
  `(blkZA_done (fun _ _ _ h => relZ_of_done h) $ok hR hal (Int.le_trans hlo (by decide)) hhi $cd)

set_option hygiene false in
/-- `Z` at a node whose invariant pins the control to `c0`, at the
instructions `j0 .. j0 + n` after the label `l` (in `abortRuns`). -/
local macro "zc " l:term:max j0:term:max n:term:max hi:term:max : term =>
  `(fun s σ c k hk he hs hFm hJn hr => by
      have hk' : k < $n := lt_of_lt_of_eq hk rfl
      have hpc : PcIn abortRuns s :=
        abPc_of (l := $l) (lo := 0) (hi := $hi) (by simp [abortRuns]) $j0 k (by omega) (by omega) he hs
        (by
          simp only [Abort.Disp.DN.nd4, Abort.N, Abort.pcSvc, Abort.write, Int64.add_assoc]
          all_goals first | exact (ofNat4_zero _).symm | (congr 1 <;> decide))
      simp only [Abort.Disp.DN.nd4, Abort.N, Abort.JI] at hJn
      first
        | (obtain rfl := hJn; exact hZ s he hpc hFm hr)
        | (obtain ⟨rfl, -⟩ := hJn; exact hZ s he hpc hFm hr))

/-- **`AbortObl` from the pc-only form** (`stubWW_nnzX`'s `hZ`): every
node's `RelZ` is proved (the path's blocks covered, its single
instructions and `svc`s run to `.done` or fault), so `Z` may include
`RelZ`. No premise beyond `stubWW_nnzX`'s. -/
theorem AbortObl.ofPc [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hZ : ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelZ s c0 → Z s c0) :
    AbortObl Z exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.b1Write exe endPc :=
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .write
  exact
    { de := blkZA_ofPc hF (rb Abort.Disp.d0_ok (fun s he hn => dc.e s he hn)) (zc "scc_rt_abort" 0 5 5)
      dt1 := blkZA_ofPc hF (rb Abort.Disp.t1_ok (fun s he hn => dc.t1 s he hn)) (zc ".L12_scc_rt_abort.0_entry" 0 4 5)
      dj1 := blkZA_ofPc hF (rb Abort.Disp.j1_ok (fun s he hn => dc.j1 s he hn)) (zc ".L12_scc_rt_abort.0_entry" 4 1 5)
      dt2 := blkZA_ofPc hF (rb Abort.Disp.t2_ok (fun s he hn => dc.t2 s he hn)) (zc ".L12_scc_rt_abort.2_next1" 0 4 5)
      dj2 := blkZA_ofPc hF (rb Abort.Disp.j2_ok (fun s he hn => dc.j2 s he hn)) (zc ".L12_scc_rt_abort.2_next1" 4 1 5)
      dt3 := blkZA_ofPc hF (rb Abort.Disp.t3_ok (fun s he hn => dc.t3 s he hn)) (zc ".L12_scc_rt_abort.4_next3" 0 4 5)
      dj3 := blkZA_ofPc hF (rb Abort.Disp.j3_ok (fun s he hn => dc.j3 s he hn)) (zc ".L12_scc_rt_abort.4_next3" 4 1 5)
      dt4 := blkZA_ofPc hF (rb Abort.Disp.t4_ok (fun s he hn => dc.t4 s he hn)) (zc ".L12_scc_rt_abort.6_next5" 0 4 4)
      dg4 := blkZA_ofPc hF (rb Abort.Disp.g4_ok (fun s he hn => dc.g4 s he hn)) (zc ".L12_scc_rt_abort.7_is6" 0 4 4)
      se := blkZA_ofPc hF (rb Abort.b0_ok (fun s he hn => sc.e s he hn)) (zc "scc_rt_abort_write" 0 4 4)
      sn1 := nodeW_ofPc (fun s he hn => sc.n1 s he hn) (fun _ _ hc _ => relZ_of_done (exec_si hc))
        (zc ".L16_scc_rt_abort_write.0_entry" 0 1 11)
      sn1b := nodeW_ofPc (fun s he hn => sc.n1b s he hn) (fun _ _ hc _ => relZ_of_done (exec_si hc))
        (zc ".L16_scc_rt_abort_write.0_entry" 1 1 11)
      sn2 := blkZA_ofPc hF (rb Abort.b1Write_ok (fun s he hn => sc.n2 s he hn))
        (zc ".L16_scc_rt_abort_write.0_entry" 2 5 11)
      svc := nodeW_ofPc (fun s he hn => sc.svc s he hn) (fun _ _ hc _ => relZ_svc hc)
        (zc ".L16_scc_rt_abort_write.0_entry" 7 1 11)
      sn5 := blkZA_ofPc hF (rb Abort.b2_ok (fun s he hn => sc.n5 s he hn))
        (zc ".L16_scc_rt_abort_write.0_entry" 8 3 11)
      sex := nodeW_ofPc (fun s he hn => sc.ex s he hn) (fun _ _ hc _ => relZ_svc hc)
        (zc "scc_rt_abort_write_exit" 0 1 1) }

end AbortObl

section AbortXA

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isaLSE2} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop}

/-- **A block node's states are `NNZXH`** from `Z` at the node. -/
theorem blkW_nnzXA {n : ND} {blk : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true)
    (hz : NodeZA Z exe endPc R F n blk) :
    BlkW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm
  refine ⟨⟨?_, (hz s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm).1⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZXH`** from `Z` at the node. -/
theorem nodeW_nnzXA {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hA => by
    obtain ⟨he, hn, -, hpc, -⟩ := id hA
    exact ⟨⟨nn_of_cellP ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) he hn hd,
      (hz s c hA).1⟩, fun _ h => h⟩

/-- **A system call's node's states are `NNZXH`** from `Z` at the node:
the call its invariant decodes is `safeH` at the node's pc and not `exit`
(`hsafe`). -/
theorem nodeW_nnzXSvcA {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ s σ c, s.st.2 = n.pc → n.J σ c → ∀ call, svcCall σ.regs = some call →
      safeH (AbC exe s) call ∧ call ≠ .exit)
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c hAt => by
    obtain ⟨he, hn, _, hpc, σ, hA, hD, hJ⟩ := id hAt
    have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    refine ⟨⟨⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (by rintro w ⟨⟩), fun _ call hd => ?_⟩,
      (hz s c hAt).1⟩, fun _ h => h⟩
    exact hsafe s σ c hpc hJ call (by rw [svcCall, ← hA.regs]; exact hd)

/-- **The write abort path's obligations inside `NNZXH`** from `Z` at
every node (`stubWW_nnzX` with `AbortObl`). -/
theorem stubWW_nnzXA [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {c0 : Ctl}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hZ : AbortObl Z exe endPc R F c0)
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubWW (NNZXH exe endPc Z) (fun _ _ => False) p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.b1Write exe endPc :=
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .write
  refine StubW.stubWW_of_code hp hend hprog hK hF
    (blkW_nnzXA (fun s he hn => dc.e s he hn) (by simp [Abort.Disp.d0, notNop]) hZ.de)
    (blkW_nnzXA (fun s he hn => dc.t1 s he hn) (by simp [Abort.Disp.t1, notNop]) hZ.dt1)
    (blkW_nnzXA (fun s he hn => dc.j1 s he hn) (by simp [Abort.Disp.j1, notNop]) hZ.dj1)
    (blkW_nnzXA (fun s he hn => dc.t2 s he hn) (by simp [Abort.Disp.t2, notNop]) hZ.dt2)
    (blkW_nnzXA (fun s he hn => dc.j2 s he hn) (by simp [Abort.Disp.j2, notNop]) hZ.dj2)
    (blkW_nnzXA (fun s he hn => dc.t3 s he hn) (by simp [Abort.Disp.t3, notNop]) hZ.dt3)
    (blkW_nnzXA (fun s he hn => dc.j3 s he hn) (by simp [Abort.Disp.j3, notNop]) hZ.dj3)
    (blkW_nnzXA (fun s he hn => dc.t4 s he hn) (by simp [Abort.Disp.t4, notNop]) hZ.dt4)
    (blkW_nnzXA (fun s he hn => dc.g4 s he hn) (by simp [Abort.Disp.g4, notNop]) hZ.dg4)
    (blkW_nnzXA (fun s he hn => sc.e s he hn) (by simp [Abort.b0, notNop]) hZ.se)
    (nodeW_nnzXA (fun s he hn => sc.n1 s he hn) (by simp [SI.toDir, notNop]) hZ.sn1)
    (nodeW_nnzXA (fun s he hn => sc.n1b s he hn) (by simp [SI.toDir, notNop]) hZ.sn1b)
    (blkW_nnzXA (fun s he hn => sc.n2 s he hn) (by simp [Abort.b1Write, notNop]) hZ.sn2)
    (nodeW_nnzXSvcA (fun s he hn => sc.svc s he hn) ?_ hZ.svc)
    (blkW_nnzXA (fun s he hn => sc.n5 s he hn) (by simp [Abort.b2, notNop]) hZ.sn5)
    (nodeW_nnzXSvcA (fun s he hn => sc.ex s he hn) ?_ hZ.sex) hab
  · rintro s σ c hpc ⟨-, h0, h8⟩ call hd
    obtain ⟨buf, n, hw⟩ := StubW.svcCall_write h0 h8
    rw [hw] at hd
    cases hd
    exact ⟨.inr (.inr (.inl (.inl ⟨hpc, buf, n, rfl⟩))), by rintro ⟨⟩⟩
  · rintro s σ c hpc ⟨-, h8, h0⟩ call hd
    rw [svcCall_exitGroup (by rw [h8]; rfl)] at hd
    cases hd
    refine ⟨.inr (.inr (.inl (.inr ⟨hpc, ?_⟩))), by rintro ⟨⟩⟩
    rw [h0]; rfl

/-- **A jump to `scc_rt_abort` with `x0 = 4` inside `NNZXH` does not
return**, `Z` at every node of the path in the dispatcher's region for
each caller's state and source control of `nC` (`hZ`; `seg_jabort4X`
with `AbortObl`). -/
theorem seg_jabort4XA [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {Q : Frag isaLSE2}
    {nC : ND} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 4)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hZ : ∀ m0 σC c0, nC.J σC c0 → AbortObl Z exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0)
    (hab : ∀ m0 σC c0, nC.J σC c0 → ∀ s c, At exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC)
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c → ms.abortAt s) :
    SegTC (NNZXH exe endPc Z) p lbl ms (At exe endPc R F nC) Q :=
  SegW.toTC (Abort.Disp.seg_jabort4W hpc hX0 hF hR hal hlo hkc h16 hK fun m0 σC c0 hJ =>
    stubWW_nnzXA hp hend hprog hK
      (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
      (hZ m0 σC c0 hJ) (hab m0 σC c0 hJ))

/-- **The callee region's facts of `seg_jabort4XA`** (as `seg_jabort4X`
derives them): the dispatcher's region below `nC.o.sp` is OK, aligned,
reaching 48 bytes down, and its frame condition stable. -/
theorem jabort_callee {nC : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp - 48) (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (m0 : MachineData) (σC : AS) :
    (R.callee nC.o.sp (-48) 0).OK ∧ (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 ∧
      (R.callee nC.o.sp (-48) 0).lo ≤ -48 ∧ 0 ≤ (R.callee nC.o.sp (-48) 0).hi ∧
      FStable (R.callee nC.o.sp (-48) 0) (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  refine ⟨Region.callee_ok (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc (by omega),
    ?_, by simp [Region.callee], by simp [Region.callee],
    fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide)⟩
  have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

end AbortXA

end Spike.Lib.A64.Flow.Worker

/-- info: 'Spike.Lib.A64.Flow.Worker.AbortObl.ofPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.AbortObl.ofPc

/-- info: 'Spike.Lib.A64.Flow.Worker.seg_jabort4XA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.seg_jabort4XA
