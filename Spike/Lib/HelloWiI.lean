/-
**hello.w's child entry at the placed instance** (row
5j-misc, AArch64): `HelloAssemblyI.hello_obligations_I`'s `hWi`
(`HelloSpawnR.HWiH`) at the worker side `DH` with the root parameters `PI`,
`ZI`, `hsegI` (`HelloSegI`).

At main's clone (`SpawnPrem`, the pre side `PreRH`: one thread `th`, the
handed range `r1c` ending at the clone's `stack`, held for main), the child
after the clone is at the stub's node (`Hello.Child.child_atH`; region
`childR stack (-272)`, its frame condition the child's first memory outside
it, the words main's `x9 .. x14`, the thread pointer `tls`, `sp` the top),
its source control the spawned worker's `tail worker` at hello's packet
(`PktH`). So it is in `PI` once `ChildPrem` holds there, and in `DH.Wi` by
`HelloWorkerRR.helloDR_entry` (`WideX` from the placed executable's
`wideIn`, `HelloMainG.hw_IH`).

- `hWiH_I`: `HWiH` at `DH … PI ZI XI hsegXI`. Open, each a premise with its
  row: the handed range's top (`htop`, `hal`, `hsz`), main's runtime facts
  at the clone (`hX`: executable, end, no declarations) and the child
  segment's premises `hCP` (`Hello.SegR.ChildPrem`) at the clone's data,
  given the frame fact `Fr` and the packet's words (`PktH`'s value facts,
  `n = 13`, `m = 2`).
- `hWiH_IG`: the same at any worker fragments `DH … P Z X hseg`, given the
  entry fragment `P` at the child's data (`hP`; the switch's `HelloWorkerDHF.PF`).
- `stacks_bd`: the two stacks end below `2 ^ 64` (same premises).
- `r1c_facts`: the handed range's three facts (row 5j-misc-r1) when it is
  the runtime's second stack `PreChild.r1Of L.lab` inside the stack pool.
-/
import Spike.Lib.HelloSegI
import Spike.Lib.HelloMainG
import Spike.Lib.WakeWorkerSide
import Spike.Lib.Rt.A64RtPreChild

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Handover Spike.Lib.A64.Flow
open Spike.Lib.HelloMs (msH)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.HelloO (ODataH)
open Spike.Lib.HelloSpawnR (HWiH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.WakeW1 (mainTidW)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words childN pfxM child_atH hello_svcIn)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem ChildD kidH)
open Spike.Lib.HelloPreA (cloneAtH)
open SccCode (helloProg)

/-- **The handed stack's facts** (row 5j-misc-r1): the runtime's second
stack (`r1Of`, 16 KiB above the 16-aligned first) inside the stack pool ends
below `2 ^ 64`, at a 16-aligned top, and holds the stub's 272 bytes. -/
theorem r1c_facts (L : Spike.Lib.A64.Rt.RuntimeLayout) {r1c : Range} (hsub : r1c.Sub L.Λ.stackPool)
    (hr1 : r1c = Spike.Lib.A64.Rt.PreChild.r1Of L.lab) :
    r1c.lo + r1c.size < 2 ^ 64 ∧ (r1c.lo + r1c.size) % 16 = 0 ∧ 272 ≤ r1c.size := by
  have hf := L.pool_fit
  have hal := L.stacks_al
  have hs := L.stacks_sub
  have hlab : Spike.Lib.A64.Flow.Ret0.stacksA L.lab = L.stacksA := L.lab_stacks
  obtain ⟨-, h2⟩ := hsub
  obtain ⟨-, h4⟩ := hs
  subst hr1
  simp only [Spike.Lib.A64.Rt.PreChild.r1Of, hlab, BitVec.toNat_add, BitVec.toNat_ofNat] at h2 ⊢
  have hlt : L.stacksA.toNat + 16384 < 2 ^ 64 := by simp only at h4; omega
  rw [Nat.mod_eq_of_lt hlt] at h2 ⊢
  refine ⟨by omega, by omega, by decide⟩

/-- **The two stacks do not wrap** (`tcb_hlim`'s bound; wake's `hbd_W`):
the runtime's second stack inside the stack pool. -/
theorem stacks_bd (L : Spike.Lib.A64.Rt.RuntimeLayout) {r1c : Range} (hsub : r1c.Sub L.Λ.stackPool)
    (hr1 : r1c = Spike.Lib.A64.Rt.PreChild.r1Of L.lab) : L.stacksA.toNat + 32768 < 2 ^ 64 := by
  have hf := L.pool_fit
  have hs := L.stacks_sub
  have hlab : Spike.Lib.A64.Flow.Ret0.stacksA L.lab = L.stacksA := L.lab_stacks
  obtain ⟨-, h2⟩ := hsub
  obtain ⟨-, h4⟩ := hs
  subst hr1
  simp only [Spike.Lib.A64.Rt.PreChild.r1Of, hlab, BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  have hlt : L.stacksA.toNat + 16384 < 2 ^ 64 := by simp only at h4; omega
  rw [Nat.mod_eq_of_lt hlt] at h2
  omega

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The child's entry at the instance, any worker fragments** (`hello_obligations_I`'s `hWi` at
`DH hp i G0 P Z X hseg`; see the module doc): as `hWiH_I`, the entry fragment `P` holding at the child's data
whose word 3 is the record's pointer word (`hP`; `PI` outright, `HelloWorkerDHF.PF` by `cwvH`). -/
theorem hWiH_IG {arch : WeakMem.Arch} {asm : String} {E : Entry} {R1 : Cfg → TermRun.Cfg → Prop}
    {passT : State → Prop} {Dd : ODataH} {r1c : Range} {Fr : HelloSpawnR.FrP}
    {P Z X : ιH hp i → Spike.Lib.FragS isaLSE2}
    {hseg : ∀ w, Spike.Lib.HelloSegTCSX.SegTCSX
      (fun s c fs => Spike.Lib.A64.Flow.Worker.NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w)
      Spike.Lib.HelloSrc.helloSrc (SRH hp i w).lbl
      (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False)}
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    /- row: 5j-misc-r1 (the handed stack: its top in the address space,
    16-aligned, at least the stub's 272 bytes) -/
    (htop : r1c.lo + r1c.size < 2 ^ 64) (hal : (r1c.lo + r1c.size) % 16 = 0) (hsz : 272 ≤ r1c.size)
    /- the entry fragment at the child's data (word 3 the record's pointer word) -/
    (hP : ∀ w s c (d : ChildD), d.w3 = w.1.cwW → d.ok →
      ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
        (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3
        d.w4 d.n d.m →
      At (LH hp i).exe (endH hp i) d.R d.F
        (childN pfxM (_root_.Executable.labels (LH hp i).exe).label (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4)
          d.w d.tp d.sp0) s c →
      P w s c [])
    /- row: 5j-misc-X (main's runtime facts at the clone, given the frame fact `Fr`) -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.HelloSrc.helloS arch).Run s [] s' →
      HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
        (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- rows: the child segment's (`ChildPrem`'s fields) at
    the clone's data, given the frame fact and the packet -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.HelloSrc.helloS arch).Run s [] s' →
      HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
        (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
          (DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
            th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2) :
    HWiH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg)
      (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E Fr := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
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
  obtain ⟨-, hlo0, hsz', hRok, hal', -, hhi'⟩ :=
    Spike.Lib.A64.Rt.childStub_region (lo := -272) htop hal (by decide) (by omega)
  have hcode := code_of hl rfl hello_svcIn (q := cloneAtH pfxM (LH hp i).exe) rfl
  have hA := child_atH (cW := kidH T w0 w1 w2 w.1.cwW w4) (tls := tls) hcode rfl he hn hd (he ▸ hpc) hh htop
    hlo0 hsz'
  have hc : Spike.Lib.Ctl.of s1 = kidH T w0 w1 w2 w.1.cwW w4 := by
    simp only [Spike.Lib.Ctl.of, kidH, hR.pre.term1, henv]
    rfl
  rw [hc]
  refine HelloWorkerRR.helloDR_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ w _ _ _ (hP w _ _ ⟨childR (r1c.lo + r1c.size) (-272),
    _, _, _, _, T, w0, w1, w2, w.1.cwW, w4, 13, 2⟩ rfl
    ⟨FStable.dframe _ _, hRok, hal', by show (-272 : Int) ≤ -272; decide, hhi'⟩
    (hCP d s th _ tls r s' w s0 s1 lbl lsize ts j own₀ l hPr hRun hR hFr T w0 w1 w2 w4 henv h4 h0 h1 h2) hA) ?_
  exact Spike.Lib.WakeW1.WorkerSide.wideX_childAfter
    (Spike.Lib.WakeW1.WorkerSide.wideX_of (HelloMainG.hw_IH hp i) he hd)

/-- **The child's entry at the instance** (`hello_obligations_I`'s `hWi`;
see the module doc): `hWiH_IG` at `PI`, `ZI`, `XI`, `hsegXI`. -/
theorem hWiH_I {arch : WeakMem.Arch} {asm : String} {E : Entry} {R1 : Cfg → TermRun.Cfg → Prop}
    {passT : State → Prop} {Dd : ODataH} {r1c : Range} {Fr : HelloSpawnR.FrP}
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    /- row: 5j-misc-r1 (the handed stack: its top in the address space,
    16-aligned, at least the stub's 272 bytes) -/
    (htop : r1c.lo + r1c.size < 2 ^ 64) (hal : (r1c.lo + r1c.size) % 16 = 0) (hsz : 272 ≤ r1c.size)
    /- row: 5j-misc-X (main's runtime facts at the clone, given the frame fact `Fr`) -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 (PI hp i G0) (ZI hp i) (XI hp i) (hsegXI hp i G0 hpa hhp) arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.HelloSrc.helloS arch).Run s [] s' →
      HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
        (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 (PI hp i G0) (ZI hp i) (XI hp i) (hsegXI hp i G0 hpa hhp))
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- rows: the child segment's (`ChildPrem`'s fields) at
    the clone's data, given the frame fact and the packet -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i G0 (PI hp i G0) (ZI hp i) (XI hp i) (hsegXI hp i G0 hpa hhp) arch R1 E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (Spike.Lib.HelloSrc.helloS arch).Run s [] s' →
      HelloSpawnR.PreRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
        (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 (PI hp i G0) (ZI hp i) (XI hp i) (hsegXI hp i G0 hpa hhp))
        (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
          (DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
            th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2) :
    HWiH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 (PI hp i G0) (ZI hp i) (XI hp i) (hsegXI hp i G0 hpa hhp))
      (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E Fr :=
  hWiH_IG hp i G0 hpa hhp htop hal hsz (fun _ _ _ d _ ho hc ha => ⟨rfl, d, ho, hc, ha⟩) hX hCP

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hWiH_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hWiH_I

/-- info: 'Spike.Lib.HelloAssemblyI.hWiH_IG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hWiH_IG

/-- info: 'Spike.Lib.HelloAssemblyI.r1c_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.r1c_facts
