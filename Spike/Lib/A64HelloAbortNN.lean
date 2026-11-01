/-
**`print`'s abort off the transfer sites** (`WCompatH.noSite`/`sysOkH`, AArch64): a jump to `scc_rt_abort` with
`x0 = 4` (`print`'s refused `write`, `Abort.Disp.seg_jabort4W`) as a segment
inside hello's fragment `NNZH exe endPc Z` (`Spike/Lib/A64HelloNN.lean`).
It is the NNZH twin of `Abort.seg_jabort4T` (`Spike/Lib/A64AbortJT.lean`).

The dispatcher's and the stub's blocks have no `nop` or `svc` (`notNop`).
The stub's two system calls are at `scc_rt_abort_write`'s sites (`AbW`):
its `write` to fd 2 (`x0 = 2`, `x8 = 64`) at `Abort.pcSvc … Abort.write`,
and its `exit_group(101)` (`x8 = 94`, `x0 = 101`, `abortStatus`) at
`Abort.write.exit`. Both are in `safeH`'s `AbC` disjunct (each at its own
site). `Z` is asked at every state of the path with the caller's control
`c0` and the caller's frame condition `F` (`hZ`).

- `blkW_nnzH`, `nodeW_nnzH`, `nodeW_nnzHSvc`: a node's states are `NNZH`.
- `stubWW_nnzH`: the write abort path's obligations (`Abort.Disp.StubWW`)
  inside `NNZH`, from the abort code (`StubW.stubWW_of_code`).
- `seg_jabort4H`: the jump, a `SegTC (NNZH exe endPc Z)` segment to any
  fragment.
-/
import Spike.Lib.A64HelloNN
import Spike.Lib.A64AbortStubCode

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)

section AbortNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **A block node's states are `NNZH`**: its block has no `nop` or `svc`,
`Z` at every state of the frame condition and the node's invariant
(`hZ`). -/
theorem blkW_nnzH {n : ND} {blk : List Directive} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hb : blk.all notNop = true)
    (hZ : ∀ s σ c, s.exe = exe → F s.st.1 → n.J σ c → Z s c) :
    BlkW (NNZH exe endPc Z) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ hD hJ k hk m _ hDm
  refine ⟨⟨?_, hZ _ σ c he (hF _ _ hD hDm) hJ⟩, fun _ h => h⟩
  have hd := List.all_eq_true.mp hb _ (List.getElem_mem hk)
  exact nn_of_cellP ((hcode s he hn).cell (List.getElem?_eq_getElem hk) rfl rfl rfl) he hn hd

/-- **A node's states are `NNZH`**: its first directive is not a `nop` or an
`svc`, `Z` as in `blkW_nnzH`. -/
theorem nodeW_nnzH {n : ND} {d : Directive} {ds : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (d :: ds)) (hd : notNop d = true)
    (hZ : ∀ s σ c, s.exe = exe → F s.st.1 → n.J σ c → Z s c) :
    NodeW (NNZH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, _, hD, hJ⟩ =>
    ⟨⟨nn_of_cellP ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) he hn hd, hZ s σ c he hD hJ⟩,
      fun _ h => h⟩

/-- **A system call's node's states are `NNZH`**: the call its invariant
decodes is `safeH` at the node's pc (`hsafe`), `Z` as in `blkW_nnzH`. -/
theorem nodeW_nnzHSvc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hsafe : ∀ s σ c, s.st.2 = n.pc → n.J σ c → ∀ call, svcCall σ.regs = some call → safeH (AbC exe s) call)
    (hZ : ∀ s σ c, s.exe = exe → F s.st.1 → n.J σ c → Z s c) :
    NodeW (NNZH exe endPc Z) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, _, hpc, σ, hA, hD, hJ⟩ => by
    have hc : CellAt s svcDir 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    refine ⟨⟨⟨he, hn, Scc.Sem.A64.atNop_false_of_cellAt hc (by rintro w ⟨⟩), fun _ call hd => ?_⟩,
      hZ s σ c he hD hJ⟩, fun _ h => h⟩
    exact hsafe s σ c hpc hJ call (by rw [svcCall, ← hA.regs]; exact hd)

set_option hygiene false in
/-- `Z` at a node whose invariant pins the control to `c0`. -/
local macro "zc" : term =>
  `(fun s σ c he hFm hJn => by
      simp only [Abort.Disp.DN.nd4, Abort.N, Abort.JI] at hJn
      first
        | (obtain rfl := hJn; exact hZ s he hFm)
        | (obtain ⟨rfl, -⟩ := hJn; exact hZ s he hFm))

/-- **The write abort path's obligations inside `NNZH`** from the abort
code (`stubWW_of_code`): `Z` at every state with the control `c0` and the
frame condition `F` (`hZ`), the stub's exit at an abort site (`hab`). -/
theorem stubWW_nnzH [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {c0 : Ctl}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hZ : ∀ s, s.exe = exe → F s.st.1 → Z s c0)
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubWW (NNZH exe endPc Z) (fun _ _ => False) p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have dc : Abort.Disp.Code c0 exe endPc := Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2
  have sc : Abort.Code Abort.write c0 Abort.b1Write exe endPc :=
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .write
  refine StubW.stubWW_of_code hp hend hprog hK hF
    (blkW_nnzH hF (fun s he hn => dc.e s he hn) (by simp [Abort.Disp.d0, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.t1 s he hn) (by simp [Abort.Disp.t1, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.j1 s he hn) (by simp [Abort.Disp.j1, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.t2 s he hn) (by simp [Abort.Disp.t2, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.j2 s he hn) (by simp [Abort.Disp.j2, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.t3 s he hn) (by simp [Abort.Disp.t3, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.j3 s he hn) (by simp [Abort.Disp.j3, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.t4 s he hn) (by simp [Abort.Disp.t4, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => dc.g4 s he hn) (by simp [Abort.Disp.g4, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => sc.e s he hn) (by simp [Abort.b0, notNop]) zc)
    (nodeW_nnzH (fun s he hn => sc.n1 s he hn) (by simp [SI.toDir, notNop]) zc)
    (nodeW_nnzH (fun s he hn => sc.n1b s he hn) (by simp [SI.toDir, notNop]) zc)
    (blkW_nnzH hF (fun s he hn => sc.n2 s he hn) (by simp [Abort.b1Write, notNop]) zc)
    (nodeW_nnzHSvc (fun s he hn => sc.svc s he hn) ?_ zc)
    (blkW_nnzH hF (fun s he hn => sc.n5 s he hn) (by simp [Abort.b2, notNop]) zc)
    (nodeW_nnzHSvc (fun s he hn => sc.ex s he hn) ?_ zc) hab
  · rintro s σ c hpc ⟨-, h0, h8⟩ call hd
    obtain ⟨buf, n, hw⟩ := StubW.svcCall_write h0 h8
    rw [hw] at hd
    cases hd
    exact .inr (.inr (.inl (.inl ⟨hpc, buf, n, rfl⟩)))
  · rintro s σ c hpc ⟨-, h8, h0⟩ call hd
    rw [svcCall_exitGroup (by rw [h8]; rfl)] at hd
    cases hd
    refine .inr (.inr (.inl (.inr ⟨hpc, ?_⟩)))
    rw [h0]; rfl

/-- **A jump to `scc_rt_abort` with `x0 = 4` inside `NNZH` does not
return** (`Abort.Disp.seg_jabort4W` with `stubWW_nnzH`, then `SegW.toTC`):
from a node `nC` at `scc_rt_abort` (`sp` at `nC.o.sp` in `R`, `x0 = 4`), a
segment to any fragment, the dispatcher in the region below `nC.o.sp`. `Z`
holds at every state with a control of `nC` and the frame condition `F`
(`hZ`). The stub's exit is at an abort site (`hab`, per caller state). -/
theorem seg_jabort4H [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat} {Q : Frag isaLSE2}
    {nC : ND} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 4)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hZ : ∀ σC c0, nC.J σC c0 → ∀ s, s.exe = exe → F s.st.1 → Z s c0)
    (hab : ∀ m0 σC c0, nC.J σC c0 → ∀ s c, At exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC)
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c → ms.abortAt s) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F nC) Q :=
  SegW.toTC (Abort.Disp.seg_jabort4W hpc hX0 hF hR hal hlo hkc h16 hK fun m0 σC c0 hJ =>
    stubWW_nnzH hp hend hprog hK
      (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
      (fun s he hFm => hZ σC c0 hJ s he hFm.1) (hab m0 σC c0 hJ))

end AbortNN

end Spike.Lib.A64.Flow.Worker

/-- info: 'Spike.Lib.A64.Flow.Worker.seg_jabort4H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.seg_jabort4H
