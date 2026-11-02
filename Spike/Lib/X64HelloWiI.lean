/-
**hello.w's child entry at the placed instance** (x86-64; the twin of `Spike/Lib/HelloWiI.lean`):
`X64HelloAssemblyI.hello_obligations_I`'s `hWi` (`X64HelloSpawnR.HWiH`) at the worker side `DH`.

At main's clone (`SpawnPrem`, the pre side `PreRH`: one thread `th`, the handed range `r1c` ending at the clone's
`stack`, held for main), the child after the clone is at the stub's node (`Hello.Child.child_atH`; region
`childR stack (-272)`, its frame condition the child's first memory outside it, the words main's
`%r12, %rbx, %r13, %r14, %r15, %r9`, the thread pointer `tls`, `%rsp` the top), its source control the spawned
worker's `tail worker` at hello's packet (`PktH`). So it is in the entry fragment `P` once `ChildPrem` holds
there (`hP`), and in `DH.Wi` by `X64HelloWorkerRR.helloDR_entry` (`WideX` from the placed executable's
`wideIn`, `X64HelloMainG.hw_IH`).

- `hWiH_IG`: `HWiH` at any worker fragments `DH … P Z X hseg`, given the entry fragment `P` at the child's data
  (`hP`). Open, each a premise: the handed range's top (`htop`, `hsz`), main's runtime facts at the clone (`hX`:
  executable, end, no declarations) and the child segment's premises `hCP` (`Hello.SegR.ChildPrem`) at the
  clone's data, given the frame fact `Fr` and the packet's words (`PktH`'s value facts, `n = 13`, `m = 2`).
- `r1c_facts`: the handed range's facts when it is the runtime's second stack `PreChild.r1Of L.lab` inside the
  stack pool.

## Unlike AArch64

- The clone's `syscall`'s code is `codeAt_blockAt_lays` at `hello_svcIn` (`.Lwc_main.x25 + 94`, no prefix;
  AArch64 `code_of` at `cloneAtH pfxM`), and the child's words are main's `%r12, %rbx, %r13, %r14, %r15, %r9`
  (AArch64 `x9 .. x14`).
- The region's facts are `Rt.childStub_region`'s (no alignment); `ChildD.ok` asks no alignment either, so there is
  no `hal` premise, and `r1c_facts` gives the top and the size only.
- The child segment's premises `ChildPrem` (in `hP` and `hCP`) are at the self-word memory side
  `X64HelloOwnLift.msWHX` (main's TCB word owned, as `ChildPrem.hown` needs; AArch64 `HelloMsW.msWH`).
- The loader's parses are `cellsOf asm = some …` (AArch64 `textProgram`).
- AArch64's `hWiH_I` (at `HelloSegI`'s `PI`, `ZI`, `XI`) and `stacks_bd` are dead and not twinned.
-/
import Spike.Lib.X64HelloAssemblyI
import Spike.Lib.X64HelloMainG
import Spike.Lib.X64HelloWorkerSegP
import Spike.Lib.X64HelloOkW
import Spike.Lib.X64HelloOwnLift
import Spike.Lib.X64WakeWorkerSide
import Spike.Lib.X64HelloChildAt
import Spike.Lib.X64HelloWorkerSegR
import Spike.Lib.X64WakeChildAt
import Spike.Lib.Rt.X64RtChildPrem
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Handover
open Spike.Lib.X64 (At FStable DFrame)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.X64HelloO (ODataH)
open Spike.Lib.X64HelloSpawnR (HWiH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeW1 (mainTidW)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words childN child_atH hello_svcIn)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (ChildPrem ChildD kidH)
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)
open SccCode (helloCells)

/-- **The handed stack's facts**: the runtime's second stack (`r1Of`, 16 KiB above the first) inside the stack
pool ends below `2 ^ 64` and holds the stub's 272 bytes. -/
theorem r1c_facts (L : Spike.Lib.X64.Rt.RuntimeLayout) {r1c : Range} (hsub : r1c.Sub L.Λ.stackPool)
    (hr1 : r1c = Spike.Lib.X64.Rt.PreChild.r1Of L.lab) :
    r1c.lo + r1c.size < 2 ^ 64 ∧ 272 ≤ r1c.size := by
  have hf := L.pool_fit
  have hs := L.stacks_sub
  have hlab : Spike.Lib.X64.Flow.Ret0.stacksA L.lab = L.stacksA := L.lab_stacks
  obtain ⟨-, h2⟩ := hsub
  obtain ⟨-, h4⟩ := hs
  subst hr1
  simp only [Spike.Lib.X64.Rt.PreChild.r1Of, hlab, BitVec.toNat_add, BitVec.toNat_ofNat] at h2 ⊢
  have hlt : L.stacksA.toNat + 16384 < 2 ^ 64 := by simp only at h4; omega
  rw [Nat.mod_eq_of_lt hlt] at h2 ⊢
  refine ⟨by omega, by decide⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The child's entry at the instance, any worker fragments** (`hello_obligations_I`'s `hWi` at
`DH hp i G0 P Z X hseg`; see the module doc): the entry fragment `P` holding at the child's data whose word 3 is
the record's pointer word (`hP`). -/
theorem hWiH_IG {arch : WeakMem.Arch} {asm : Asm} {E : Entry} {R1 : Cfg → TermRun.Cfg → Prop}
    {passT : State → Prop} {Dd : ODataH} {r1c : Range} {Fr : X64HelloSpawnR.FrP}
    {P Z X : ιH hp i → Spike.Lib.FragS isa}
    {hseg : ∀ w, Spike.Lib.HelloSegTCSX.SegTCSX
      (fun s c fs => Spike.Lib.X64.Flow.Worker.NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w)
      Spike.Lib.X64HelloSrc.helloSrc (SRH hp i w).lbl
      (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False)}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some helloCells)
    /- the handed stack: its top in the address space, at least the stub's 272 bytes -/
    (htop : r1c.lo + r1c.size < 2 ^ 64) (hsz : 272 ≤ r1c.size)
    /- the entry fragment at the child's data (word 3 the record's pointer word) -/
    (hP : ∀ w s c (d : ChildD), d.w3 = w.1.cwW → d.ok →
      ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
        (fun _ => X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2
        d.w3 d.w4 d.n d.m →
      At (LH hp i).exe (endH hp i) d.R d.F
        (childN (_root_.Executable.labels (LH hp i).exe).label (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4)
          d.w d.tp d.sp0) s c →
      P w s c [])
    /- main's runtime facts at the clone, given the frame fact `Fr` -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.X64HelloSrc.helloS arch).Run s [] s' →
      X64HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT)
        (PaH hp i E asm) (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- the child segment's premises (`ChildPrem`'s fields) at the clone's data, given the frame fact and the
    packet -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.X64HelloSrc.helloS arch).Run s [] s' →
      X64HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT)
        (PaH hp i E asm) (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w)
          (DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
            th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2) :
    HWiH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
      (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E Fr := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hl : Lays (LH hp i).exe helloCells (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  have hend : endH hp i = endOf (LH hp i).exe helloCells (LH hp i).pfx := rfl
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hPr hRun hR hFr
  obtain ⟨he, hn, hd⟩ := hX d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hPr hRun hR hFr
  obtain ⟨T, w0, w1, w2, w4, henv, h4, h0, h1, -, h2⟩ := hR.pre.env1
  have hth : d.1.threads = #[th] := hR.pre.threads
  have htop' : r1c.lo + r1c.size = stack := hR.pre.top
  have hheld : d.2.held = [(0, r1c), (0, Dd.r0)] := hR.pre.held
  obtain ⟨X, hC⟩ := hR.clone
  obtain ⟨th', -, -, -, -, -, -, -, -, -, -, -, hth', -, hpc, -⟩ := hC
  have hth'' : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  subst hth'' htop'
  have hh : handed d.2 0 (r1c.lo + r1c.size) = some (0, r1c) := by
    simp [handed, hheld]
  obtain ⟨-, hlo0, hsz', hRok, -, hhi'⟩ :=
    Spike.Lib.X64.Rt.childStub_region (lo := -272) htop (by decide) (by omega)
  have hcode : ∀ s : State, s.exe = (LH hp i).exe → s.endPc = endH hp i →
      Spike.Lib.X64.CodeAt s (X64HelloPreA.cloneAtH (LH hp i).exe) Spike.Lib.X64.WakePh.WcClone.svcB :=
    fun s he' hn' => codeAt_blockAt_lays hl he' (hn'.trans hend) hello_svcIn
  have hA := child_atH (cW := kidH T w0 w1 w2 w.1.cwW w4) (tls := tls) hcode rfl he hn hd (he ▸ hpc) hh htop
    hlo0 hsz'
  have hc : Spike.Lib.Ctl.of s1 = kidH T w0 w1 w2 w.1.cwW w4 := by
    simp only [Spike.Lib.Ctl.of, kidH, hR.pre.term1, henv]
    rfl
  rw [hc]
  refine X64HelloWorkerRR.helloDR_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ w _ _ _
    (hP w _ _ ⟨childR (r1c.lo + r1c.size) (-272), _, _, _, _, T, w0, w1, w2, w.1.cwW, w4, 13, 2⟩ rfl
    ⟨FStable.dframe _ _, hRok, by show (-272 : Int) ≤ -264; decide, hhi'⟩
    (hCP d s th _ tls r s' w s0 s1 lbl lsize ts j own₀ l hPr hRun hR hFr T w0 w1 w2 w4 henv h4 h0 h1 h2) hA) ?_
  exact Spike.Lib.X64WakeW1.WorkerSide.wideX_childAfter
    (Spike.Lib.X64WakeW1.WorkerSide.wideX_of (X64HelloMainG.hw_IH hp i) he hd)

end Inst

end Spike.Lib.X64HelloAssemblyI

/-- info: 'Spike.Lib.X64HelloAssemblyI.hWiH_IG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hWiH_IG

/-- info: 'Spike.Lib.X64HelloAssemblyI.r1c_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.r1c_facts
