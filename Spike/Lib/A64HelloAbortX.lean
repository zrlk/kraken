/-
**`print`'s abort off the transfer sites, with no `exit`** (`HelloSegTCS.NoTop`, AArch64): the NNZH abort path of
`Spike/Lib/A64HelloAbortNN.lean` inside the narrower fragment `NNZXH`,
whose system calls are also not a plain `exit`, so the path's flat rows
are `OutTS` rows at `print`'s frames (`HelloSegTCS.SegTCS.liftL` with
`NoTop`; `noTopX`).

The stub's two system calls are `write(2, …)` and
`exit_group(abortStatus)` at `scc_rt_abort_write`'s pinned sites (`AbW`).
**What justifies them is still `safeH`'s `AbC` branch** (each call at its own site) (`WCompatH.sysOkH`,
and the 5i `writeErr`/`EnvJustified` obligation
for the abort's end); `NNXH` only adds that neither is a plain `exit`, the
thread-only row (`OutT.texit`) `NoTop` excludes.

- `NNXH`, `NNZXH`: `NNH` with the call not `exit`; with `Z`.
- `NNXH.toH`, `NNZXH.toH`: into `NNH`, `NNZH`.
- `noTopX`: no thread-only row at an `NNXH` state whose control is at no
  `unpark` binding.
- `abortRuns`, `abPc_of`: the abort path's pcs (the dispatcher's prefix up
  to its fourth test's taken jump and the `write` stub), as
  `Spike.Lib.A64.PcRuns.PcIn` runs; a pc `label l + 4 (j0 + k)` in one.
- `blkW_nnzX`, `nodeW_nnzX`, `nodeW_nnzXSvc`, `stubWW_nnzX`,
  `seg_jabort4X`: `A64HelloAbortNN`'s lemmas inside `NNZXH`; `Z` at the
  path's states is asked at the node's pc (`blkW_nnzX`, `nodeW_nnzX`) and,
  through the path, at a pc in `abortRuns` (`stubWW_nnzX`, `seg_jabort4X`),
  given `RelZ` there (`Spike/Lib/A64RelW1Nodes.lean`: every block of the path
  is covered, the `adrp`/`add` pair and the `svc`s run to `.done` or fault),
  which the lemmas prove (`hrel`; so `Z` may include `RelZ`).
-/
import Spike.Lib.A64HelloAbortNN
import Spike.Lib.A64PcRuns
import Spike.Lib.A64RelW1Nodes

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.HelloSegTCS (NoTop)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ relZ_of_done relZ_svc blkZA_done)

/-- **A hello worker state off the transfer sites, its call not `exit`**
(`NNH`, the call also not a plain `exit`; `safeH`'s `AbC` branch still the
abort's justification). -/
def NNXH (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  NNP (fun call => safeH (AbC exe s) call ∧ call ≠ .exit) exe endPc s

/-- **`NNXH` with `Z`.** -/
def NNZXH (exe : _root_.Executable) (endPc : Int64) (Z : Frag isaLSE2) : Frag isaLSE2 :=
  fun s c => NNXH exe endPc s ∧ Z s c

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isaLSE2}

theorem NNXH.toH {s : State} (h : NNXH exe endPc s) : NNH exe endPc s :=
  h.mono fun _ h => h.1

theorem NNZXH.toH {s : State} {c : Ctl} (h : NNZXH exe endPc Z s c) : NNZH exe endPc Z s c :=
  ⟨h.1.toH, h.2⟩

/-- **No thread-only row at an `NNXH` state** whose control is at no
`unpark` binding (`hu`). -/
theorem noTopX {ms : MemSide isaLSE2} {s : State} {c : Ctl} (hK : ms.K = some Scc.Sem.A64.abi)
    (h : NNXH exe endPc s) (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) : NoTop ms s c := by
  refine ⟨hu, fun K hk ha hd => ?_⟩
  rw [hK] at hk
  cases hk
  exact (h.2.2.2 ha _ hd).2 rfl

/-- **The abort path's pcs**: `scc_rt_abort`'s prologue, its first four
tests with their jumps, the fourth test's taken branch to the `write` stub,
and the stub (prologue, entry block, exit call). -/
def abortRuns : List (Label × Nat × Nat) :=
  [("scc_rt_abort", 0, 5), (".L12_scc_rt_abort.0_entry", 0, 5), (".L12_scc_rt_abort.2_next1", 0, 5),
    (".L12_scc_rt_abort.4_next3", 0, 5), (".L12_scc_rt_abort.6_next5", 0, 4), (".L12_scc_rt_abort.7_is6", 0, 4),
    ("scc_rt_abort_write", 0, 4), (".L16_scc_rt_abort_write.0_entry", 0, 11), ("scc_rt_abort_write_exit", 0, 1)]

/-- **A pc `label l + 4 j0 + 4 k` of a run of `abortRuns`** is in it. -/
theorem abPc_of {s : State} {l : Label} {lo hi : Nat} {q : Int64} (hq : (l, lo, hi) ∈ abortRuns) (j0 k : Nat)
    (h1 : lo ≤ j0 + k) (h2 : j0 + k < hi) (he : s.exe = exe) (hs : s.st.2 = q + Int64.ofNat (4 * k))
    (hl : q = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * j0)) :
    PcIn abortRuns s :=
  ⟨(l, lo, hi), hq, j0 + k, h1, h2, by rw [he, hs, hl, ofNat4_add]⟩

section AbortX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region}
  {F : MachineData → Prop}

/-- **A block node's states are `NNZXH`** (`blkW_nnzH`). -/
theorem blkW_nnzX {n : ND} {blk : List Directive} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true)
    (hrel : NodeZA RelZ exe endPc R F n blk)
    (hZ : ∀ s σ c k, k < blk.length → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) → F s.st.1 →
      n.J σ c → RelZ s c → Z s c) :
    BlkW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm
  refine ⟨⟨?_, hZ _ σ c k hk he rfl (hF _ _ hD hDm) hJ
    (hrel s σ c he hn hdc hpc hA hD hJ k hk m hA' hDm).1⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZXH`** (`nodeW_nnzH`). -/
theorem nodeW_nnzX {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true)
    (hrel : ∀ s c, CellAt s d 4 → s.decls = {} → RelZ s c)
    (hZ : ∀ s σ c k, k < 1 → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) → F s.st.1 →
      n.J σ c → RelZ s c → Z s c) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, hdc, hpc, σ, _, hD, hJ⟩ =>
    ⟨⟨nn_of_cellP ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) he hn hd,
      hZ s σ c 0 Nat.zero_lt_one he (by rw [hpc, ofNat4_zero]) hD hJ
        (hrel s c ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) hdc)⟩,
      fun _ h => h⟩

/-- **A system call's node's states are `NNZXH`**: the call its invariant
decodes is `safeH` at the node's pc and not `exit` (`hsafe`). -/
theorem nodeW_nnzXSvc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ s σ c, s.st.2 = n.pc → n.J σ c → ∀ call, svcCall σ.regs = some call →
      safeH (AbC exe s) call ∧ call ≠ .exit)
    (hZ : ∀ s σ c k, k < 1 → s.exe = exe → s.st.2 = n.pc + Int64.ofNat (4 * k) → F s.st.1 →
      n.J σ c → RelZ s c → Z s c) :
    NodeW (NNZXH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, hD, hJ⟩ => by
    have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    refine ⟨⟨⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (by rintro w ⟨⟩), fun _ call hd => ?_⟩,
      hZ s σ c 0 Nat.zero_lt_one he (by rw [hpc, ofNat4_zero]) hD hJ (relZ_svc hc)⟩, fun _ h => h⟩
    exact hsafe s σ c hpc hJ call (by rw [svcCall, ← hA.regs]; exact hd)

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

/-- **The write abort path's obligations inside `NNZXH`** (`stubWW_nnzH`):
the stub's `write(2, …)` and `exit_group(abortStatus)` are `safeH`'s `AbC`
branch and not `exit`. -/
theorem stubWW_nnzX [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {c0 : Ctl}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hZ : ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelZ s c0 → Z s c0)
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubWW (NNZXH exe endPc Z) (fun _ _ => False) p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.b1Write exe endPc :=
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .write
  refine StubW.stubWW_of_code hp hend hprog hK hF
    (blkW_nnzX hF (fun s he hn => dc.e s he hn) (by simp [Abort.Disp.d0, notNop]) (rb Abort.Disp.d0_ok (fun s he hn => dc.e s he hn)) (zc "scc_rt_abort" 0 5 5))
    (blkW_nnzX hF (fun s he hn => dc.t1 s he hn) (by simp [Abort.Disp.t1, notNop]) (rb Abort.Disp.t1_ok (fun s he hn => dc.t1 s he hn)) (zc ".L12_scc_rt_abort.0_entry" 0 4 5))
    (blkW_nnzX hF (fun s he hn => dc.j1 s he hn) (by simp [Abort.Disp.j1, notNop]) (rb Abort.Disp.j1_ok (fun s he hn => dc.j1 s he hn)) (zc ".L12_scc_rt_abort.0_entry" 4 1 5))
    (blkW_nnzX hF (fun s he hn => dc.t2 s he hn) (by simp [Abort.Disp.t2, notNop]) (rb Abort.Disp.t2_ok (fun s he hn => dc.t2 s he hn)) (zc ".L12_scc_rt_abort.2_next1" 0 4 5))
    (blkW_nnzX hF (fun s he hn => dc.j2 s he hn) (by simp [Abort.Disp.j2, notNop]) (rb Abort.Disp.j2_ok (fun s he hn => dc.j2 s he hn)) (zc ".L12_scc_rt_abort.2_next1" 4 1 5))
    (blkW_nnzX hF (fun s he hn => dc.t3 s he hn) (by simp [Abort.Disp.t3, notNop]) (rb Abort.Disp.t3_ok (fun s he hn => dc.t3 s he hn)) (zc ".L12_scc_rt_abort.4_next3" 0 4 5))
    (blkW_nnzX hF (fun s he hn => dc.j3 s he hn) (by simp [Abort.Disp.j3, notNop]) (rb Abort.Disp.j3_ok (fun s he hn => dc.j3 s he hn)) (zc ".L12_scc_rt_abort.4_next3" 4 1 5))
    (blkW_nnzX hF (fun s he hn => dc.t4 s he hn) (by simp [Abort.Disp.t4, notNop]) (rb Abort.Disp.t4_ok (fun s he hn => dc.t4 s he hn)) (zc ".L12_scc_rt_abort.6_next5" 0 4 4))
    (blkW_nnzX hF (fun s he hn => dc.g4 s he hn) (by simp [Abort.Disp.g4, notNop]) (rb Abort.Disp.g4_ok (fun s he hn => dc.g4 s he hn)) (zc ".L12_scc_rt_abort.7_is6" 0 4 4))
    (blkW_nnzX hF (fun s he hn => sc.e s he hn) (by simp [Abort.b0, notNop]) (rb Abort.b0_ok (fun s he hn => sc.e s he hn)) (zc "scc_rt_abort_write" 0 4 4))
    (nodeW_nnzX (fun s he hn => sc.n1 s he hn) (by simp [SI.toDir, notNop]) (fun _ _ hc _ => relZ_of_done (exec_si hc)) (zc ".L16_scc_rt_abort_write.0_entry" 0 1 11))
    (nodeW_nnzX (fun s he hn => sc.n1b s he hn) (by simp [SI.toDir, notNop]) (fun _ _ hc _ => relZ_of_done (exec_si hc)) (zc ".L16_scc_rt_abort_write.0_entry" 1 1 11))
    (blkW_nnzX hF (fun s he hn => sc.n2 s he hn) (by simp [Abort.b1Write, notNop]) (rb Abort.b1Write_ok (fun s he hn => sc.n2 s he hn)) (zc ".L16_scc_rt_abort_write.0_entry" 2 5 11))
    (nodeW_nnzXSvc (fun s he hn => sc.svc s he hn) ?_ (zc ".L16_scc_rt_abort_write.0_entry" 7 1 11))
    (blkW_nnzX hF (fun s he hn => sc.n5 s he hn) (by simp [Abort.b2, notNop]) (rb Abort.b2_ok (fun s he hn => sc.n5 s he hn)) (zc ".L16_scc_rt_abort_write.0_entry" 8 3 11))
    (nodeW_nnzXSvc (fun s he hn => sc.ex s he hn) ?_ (zc "scc_rt_abort_write_exit" 0 1 1)) hab
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
return** (`seg_jabort4H` at `stubWW_nnzX`). -/
theorem seg_jabort4X [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {Q : Frag isaLSE2}
    {nC : ND} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 4)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hZ : ∀ σC c0, nC.J σC c0 → ∀ s, s.exe = exe → PcIn abortRuns s → F s.st.1 → RelZ s c0 → Z s c0)
    (hab : ∀ m0 σC c0, nC.J σC c0 → ∀ s c, At exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC)
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c → ms.abortAt s) :
    SegTC (NNZXH exe endPc Z) p lbl ms (At exe endPc R F nC) Q := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  have hal' : (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' : (R.callee nC.o.sp (-48) 0).OK := Region.callee_ok (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc (by omega)
  exact SegW.toTC (Abort.Disp.seg_jabort4W hpc hX0 hF hR hal hlo hkc h16 hK fun m0 σC c0 hJ =>
    stubWW_nnzX hp hend hprog hK
      (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
      hR' hal' (by simp [Region.callee]) (by simp [Region.callee])
      (fun s he hpc hFm => hZ σC c0 hJ s he hpc hFm.1) (hab m0 σC c0 hJ))

end AbortX

end Spike.Lib.A64.Flow.Worker

/-- info: 'Spike.Lib.A64.Flow.Worker.seg_jabort4X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.seg_jabort4X
