/-
**The overflow abort path's obligations inside `SFacts`** (AArch64): the
`Local.StubW` of a function's `.abort_overflow` block
(`Spike/Lib/A64AbortW.lean`) at `W := SFacts … Dt`
(`Spike/Lib/A64SegInst.lean`), for any program with the abort code
(`Scc.Cert.Rt.A64.Abort.abortIn`) and an instance's facts (`InstOk`,
`Spike/Lib/Rt/A64RtW.lean`).

The source control `c0` is the one about to overflow (`OvfReady`); its
places hold in the caller's cells only (`hpl`, from the frame condition),
so a node's facts are proved at `noEnv c0` (`Spike/Lib/A64StubFacts.lean`)
and lifted.

* `ND.noEnv`, `BlkW.ofNoEnv`, `NodeW.ofNoEnv`: a node's states inside
  `SFacts` at the controls without their environments give them at the
  controls, with their places and off the abort sites;
* `blkW_ovf`, `nodeW_si_ovf`: a block and a single instruction of the abort
  path after the take (`blkW_postO`, `nodeW_postO`);
* `svcCall_write`, `seg_svcW`: a stub's `write` system call is a segment
  to its next node inside any `W` holding its states;
* `abortPhOk` (`Spike/Lib/A64AbortPh.lean`): the abort path's phase check
  (each block's `blkPh`, each single instruction off the sites and its next
  pc in its phase);
* `stubW_sfacts`: `StubW` inside `SFacts … Dt`, the write tail `Dt` holding
  at the stub's `write` (`hwr`).
-/
import Spike.Lib.A64StubFacts
import Spike.Lib.A64AbortW
import Spike.Lib.Rt.A64RtW
import Scc.Cert.Rt.A64Abort
import Spike.Lib.A64AbortPh

namespace Spike.Lib.A64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib (OvfReady EnvSmall)
open Spike.Lib.A64Consumer
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)

/-! ## Lifting from the controls without their environments -/

/-- **The node at the controls without their environments.** -/
def ND.noEnv (n : ND) : ND := ⟨n.pc, n.o, fun σ c => ∃ c', n.J σ c' ∧ c = A64Consumer.noEnv c'⟩

section Lift

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A block node's states inside `SFacts`** from those at the controls
without their environments: each control about to overflow (`hc`), placed
at every state of the frame condition (`hp`), and the block's pcs off the
abort sites (`hab`). -/
theorem BlkW.ofNoEnv {n : ND} {blk : List Directive} {Dt : State → Prop} (hF : FStable R F)
    (h : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (ND.noEnv n) blk)
    (hc : ∀ σ c, n.J σ c → OvfReady c) (hp : ∀ (s : State) σ c, n.J σ c → F s.st.1 → Placed Λ lbl s c)
    (hab : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      ∀ k' a, μ.abortAt k' = some a → pcOf s ≠ a) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hD hJ k hk m hA' hDF =>
    have ⟨hw, hK⟩ := h s σ (noEnv c) he hn hd hpc hA hD ⟨c, hJ, rfl⟩ k hk m hA' hDF
    ⟨(hw.dt_mono fun _ h => h.elim).ofNoEnv (hc σ c hJ) (hp _ σ c hJ (hF _ _ hD hDF))
      (abortOk_of_ne (hab k hk _ he hn rfl)), hK⟩

/-- **A node's states inside `SFacts`** from those at the controls without
their environments, as `BlkW.ofNoEnv`. -/
theorem NodeW.ofNoEnv {n : ND} {Dt : State → Prop}
    (h : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (ND.noEnv n))
    (hc : ∀ σ c, n.J σ c → OvfReady c) (hp : ∀ (s : State) σ c, n.J σ c → F s.st.1 → Placed Λ lbl s c)
    (hab : ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n :=
  fun s c ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ =>
    have ⟨hw, hK⟩ := h s (noEnv c) ⟨he, hn, hd, hpc, σ, hA, hD, c, hJ, rfl⟩
    ⟨(hw.dt_mono fun _ h => h.elim).ofNoEnv (hc σ c hJ) (hp s σ c hJ hD) (abortOk_of_ne (hab s he hn hpc)), hK⟩

end Lift

/-! ## The abort path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A block of the abort path inside `SFacts`**, after the take
(`blkW_postO`, the words of `rS` off the region from the frame condition,
`hFO`): its code (`hb`), its phase check without dead targets (`hph`), no
`ret` (`hnr`), the source control `c0` about to overflow at every state
(`hJ`, `hc`) and placed at every memory of the frame condition (`hpl`). -/
theorem blkW_ovf {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {l : Label} {k : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : OvfReady c0)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n blk := by
  have h := Spike.Lib.A64.Rt.blkW_postO (Λ := Λ) (rS := rS) (lbl := lbl) (n := ND.noEnv n)
    (dead := fun _ => false) (ra := 0) hI hb he hok hR hal
    hlo hhi (fun σ c ⟨c', hc', e⟩ => by subst e; rw [hJ σ c' hc']; exact cfacts_noEnv hc) hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  refine BlkW.ofNoEnv hF h (fun σ c hj => hJ σ c hj ▸ hc) (fun s σ c hj hD => hJ σ c hj ▸ hpl s hD) ?_
  rw [he, ← hI.labOk] at hph
  have hs := blkPh_sound (μ := μ) (endPc := endPc) (K := K) hI.same hI.off hok hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
  exact fun k hk s hs' hn hpc => (hs.1 k hk s hs' hn hpc).1.noAbort

/-- **A single instruction without an event (`SI`) of the abort path
inside `SFacts`**, after the take (`nodeW_postO`): off the sites (`hok`),
its next pc in its phase (`hph`), the source control as in `blkW_ovf`. -/
theorem nodeW_si_ovf {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {si : SI} {l : Label}
    {k : Nat} {p : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : OvfReady c0) (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n :=
  NodeW.ofNoEnv (Spike.Lib.A64.Rt.nodeW_postO (n := ND.noEnv n) hI hp hok hR hR8 hl hh hsub hFO
      fun s c σ hs hn _ hpc _ _ hj hP hO => by
        obtain ⟨c', hc', rfl⟩ := hj
        rw [hJ σ c' hc']
        exact sfacts_si (cfacts_noEnv hc) hP (Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc)
          (Spike.Lib.A64.Rt.next_same hI hpc hph) hO)
    (fun σ c hj => hJ σ c hj ▸ hc) (fun s σ c hj hD => hJ σ c hj ▸ hpl s hD)
    (fun s _ _ hpc => (hI.off s (by unfold pcOf; rw [hpc, hp]; exact hok)).1.noAbort)

end Nodes

/-! ## A stub's `write` system call -/

/-- **`x0 = 2`, `x8 = 64` decode to a `write` to the error output.** -/
theorem svcCall_write {r : Reg64s} (h0 : r.X0 = 2) (h8 : r.X8 = 64) :
    ∃ buf n, svcCall r = some (.write 2 buf n) := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h0, h8, Scc.Sem.A64.xRegs]

section Svc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A stub's `write` system call inside `W`** is a segment to its next
node, given its code (`hcode`) and its states inside `W` (`hW`): the call
decodes to a `write` to the error output, which the judgement matches, and
every result lands at the next node with the source unmoved. -/
theorem seg_svcW {W : Frag isaLSE2} {K : State → State → Prop} {st : Abort.Stub} {c0 : Ctl}
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (Abort.N (_root_.Executable.labels exe).label st c0 .svc).pc [svcDir])
    (hW : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .svc)) :
    SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .svc))
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .n5)) := by
  refine (svc_ndW (N := fun _ : Unit => Abort.N (_root_.Executable.labels exe).label st c0 .n5)
    (E := fun e : Empty => e.elim) hK hF hcode hW ?_ ?_).mono_post ?_
  · rintro σ c ⟨hJ, h0, h8⟩
    obtain ⟨buf, n, hc⟩ := svcCall_write h0 h8
    exact ⟨_, hc, fun v _ => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩⟩
  · rintro s c σ call - ⟨-, h0, h8⟩ hcall
    obtain ⟨buf, n, hc⟩ := svcCall_write h0 h8
    rw [hc] at hcall
    cases hcall
    exact ⟨nofun, nofun, fun fd b n' h => by cases h; decide, fun _ h => by cases h⟩
  · rintro s c (⟨_, h⟩ | ⟨x, _⟩)
    · exact h
    · exact x.elim

end Svc

/-! ## `StubW` (the phase check `abortPhOk` in `Spike/Lib/A64AbortPh.lean`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop}

/-- **The overflow abort path's obligations inside `SFacts … Dt`**
(`Local.StubW`), for a program with the abort code (`hprog`, the stub's
`write` call among its blocks), an instance's facts (`hI`) and the path's
phase check (`hphs`). The callee's region holds the stub's frame (`hlo`,
`hhi`); the words of `rS` lie off it in the frame condition (`hFO`); the
source control `c0` is about to overflow (`hc`, `hsm`) and placed at every
memory of the frame condition (`hpl`). The exit call is the overflow's
abort site: off the release and take sites (`hrel`, `htk`), no other
kind's (`hk`), no outside move (`hKex`), the memory side's abort
(`hms`). The write tail `Dt` holds at the `write` (`hwr`). -/
theorem stubW_sfacts {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {c0 : Ctl} {Dt : State → Prop}
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.overflow c0 .svc) s c → Dt s) :
    Abort.Local.StubW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p al ms exe endPc R F c0 := by
  have hlab := hI.labOk
  subst hlab
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.1.1.1
  have hdi := hsd.2
  have hscode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) hI.lays hI.endOk hst
  have hdcode := Scc.Cert.Rt.A64.Abort.code_disp (c0 := c0) hI.lays hI.endOk hdi
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, -, hg1, -⟩ := hdi
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pg1, pb0, o1, q1, o1b, q1b, pb1, o7, q7, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Flow.Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => Spike.Lib.A64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he7 : (_root_.Executable.labels exe).label Abort.overflow.entry + Int64.ofNat (4 * 7) =
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .svc).pc := by
    simp only [Abort.N, Abort.pcSvc, add4, add0]
  have hsvcW : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ
    rw [← he7] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
    exact ⟨hc0 ▸ sfacts_svcOvf hc (hpl s hD) hP.1.noSite hP.1.noTake (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc)
      (Spike.Lib.A64.Rt.next_same hI hpc q7) (hown s _ σ hA hD) (abortOk_of_ne hP.1.noAbort)
      (fun _ _ _ _ => hwr s c hAt), hP.2⟩
  refine ⟨hdcode, ?_, ?_, ?_, hscode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_ovf hI hd0 (by simp only [Abort.Disp.DN.nd1, add0]) Abort.Disp.d0_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hpl
  · exact blkW_ovf hI ht1 (by simp only [Abort.Disp.DN.nd1, add0]) Abort.Disp.t1_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hpl
  · exact blkW_ovf hI hg1 (by simp only [Abort.Disp.DN.nd1, add0]) Abort.Disp.g1_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pg1 rfl (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb0 (by simp only [Abort.N, add0]) Abort.b0_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h) hc hpl
  · exact nodeW_si_ovf (si := .adrp .X9 Abort.overflow.msg) hI hn1 rfl (by simp only [Abort.N, add0]) o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h) hc hpl
  · exact nodeW_si_ovf (si := .addLo12 .X9 .X9 Abort.overflow.msg) hI hn1b rfl (by simp only [Abort.N, add4, add0])
      o1b q1b hR hR8 hl hh hsub hFO (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb1 (by simp only [Abort.N, add4, add0]) Abort.b1Overflow_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb2 (by simp only [Abort.N, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h) hc hpl
  · rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h8, h0⟩
    have hc0 : c = c0 := hJ
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.overflow.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ.regs.X0.toNat) := by
      rw [← svcCall_exitGroup (by rw [h8]; rfl), svcCall, ← hA.regs]; rfl
    refine ⟨hc0 ▸ sfacts_svcOvf hc (hpl s hD) (fun a ha => hpcN ▸ hrel a ha) (fun a ha => hpcN ▸ htk a ha)
      (Spike.Lib.A64.Rt.cellOf hI hx (add0 _) hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc qx)
      (hown s _ σ hA hD) (abortOk_ovf (fun k a ha e => hk k a ha (hpcN ▸ e)) hc hsm fun v hv => ?_)
      (fun _ _ _ h => by rw [hd] at h; cases h), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    rw [h0]; rfl
  · exact seg_svcW hK hF (code_field hI.lays hI.endOk hsvcIn he7) hsvcW
  · exact fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc

end Stub

end Spike.Lib.A64.StubW
