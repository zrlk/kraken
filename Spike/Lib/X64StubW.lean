/-
**The overflow abort path's obligations inside `SFacts`** (x86-64): the
`Local.StubW` of a function's `.ovf` block (`Spike/Lib/X64AbortW.lean`) at
`W := SFacts … Dt` (`Spike/Lib/X64SegInst.lean`), for any program with the
abort code (`Scc.Cert.Rt.X64.Abort.abortIn`) and an instance's facts
(`InstOk`, `Spike/Lib/Rt/X64RtW.lean`). The twin of
`Spike/Lib/A64StubW.lean`.

The source control `c0` is the one about to overflow (`OvfReady`); its
places hold in the caller's cells only (`hpl`, from the frame condition),
so a node's facts are proved at `noEnv c0` (`Spike/Lib/X64StubFacts.lean`)
and lifted.

* `ND.noEnv`, `BlkW.ofNoEnv`, `NodeW.ofNoEnv`: a node's states inside
  `SFacts` at the controls without their environments give them at the
  controls, with their places and off the abort sites;
* `blkW_ovf`, `nodeW_si_ovf`: a block and a single instruction of the abort
  path after the take (`blkW_postO`, `nodeW_postO`);
* `syscallCall_write`, `seg_syscallW`: a stub's `write` system call is a
  segment to its next node inside any `W` holding its states;
* `phOne`, `abortPhOk` (`Spike/Lib/X64AbortPh.lean`): the abort path's
  phase check (each block's `blkPh`, each single instruction off the sites
  and its next pc in its phase);
* `stubW_sfacts`: `StubW` inside `SFacts … Dt`, the write tail `Dt` holding
  at the stub's `write` (`hwr`).

**Unlike AArch64**: instructions have sizes (`phOne` takes the size); the
stub's `write` call is not part of `stubIn`, so its cell is a premise
(`hsysIn`, as ARM's `hsvcIn`); the region asks 8-alignment only; the
stub's region is `[-24, 16)` from its frame base, the dispatcher's
`[-8, 16)`.
-/
import Spike.Lib.X64StubFacts
import Spike.Lib.X64AbortW
import Spike.Lib.Rt.X64RtW
import Scc.Cert.Rt.X64Abort
import Spike.Lib.X64AbortPh

namespace Spike.Lib.X64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib (OvfReady EnvSmall)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB code_field)
open Kraken.Promising.Lower.X64 (op64)

/-! ## Lifting from the controls without their environments -/

/-- **The node at the controls without their environments.** -/
def ND.noEnv (n : ND) : ND := ⟨n.pc, n.o, fun σ c => ∃ c', n.J σ c' ∧ c = X64Consumer.noEnv c'⟩

section Lift

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A block node's states inside `SFacts`** from those at the controls
without their environments: each control about to overflow (`hc`), placed
at every state of the frame condition (`hp`), and the block's pcs off the
abort sites (`hab`). -/
theorem BlkW.ofNoEnv {n : ND} {blk : List (Directive × Nat)} {Dt : State → Prop} (hF : FStable R F)
    (h : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (ND.noEnv n) blk)
    (hc : ∀ σ c, n.J σ c → OvfReady c) (hp : ∀ (s : State) σ c, n.J σ c → F s.st.1 → Placed Λ lbl s c)
    (hab : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → ∀ k' a, μ.abortAt k' = some a → pcOf s ≠ a) :
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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A block of the abort path inside `SFacts`**, after the take
(`blkW_postO`, the words of `rS` off the region from the frame condition,
`hFO`): its code (`hb`), its phase check without dead targets (`hph`), no
`ret` (`hnr`), the source control `c0` about to overflow at every state
(`hJ`, `hc`) and placed at every memory of the frame condition (`hpl`). -/
theorem blkW_ovf {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {blk : List
    (Directive × Nat)}
    {lo hi : Int} {l : Label} {off : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat off) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : OvfReady c0)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n blk := by
  have h := Spike.Lib.X64.Rt.blkW_postO (Λ := Λ) (rS := rS) (lbl := lbl) (n := ND.noEnv n)
    (dead := fun _ => false) (ra := 0) hI hb he hok hR hlo hhi hR8 hl hh
    (fun σ c ⟨c', hc', e⟩ => by subst e; rw [hJ σ c' hc']; exact cfacts_noEnv hc) hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  refine BlkW.ofNoEnv hF h (fun σ c hj => hJ σ c hj ▸ hc) (fun s σ c hj hD => hJ σ c hj ▸ hpl s hD) ?_
  rw [he, ← hI.labOk] at hph
  have hs := blkPh_sound (μ := μ) (endPc := endPc) (K := K) hI.same hI.off hok hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
  exact fun k hk s hs' hn hpc => (hs.1 k hk s hs' hn hpc).1.noAbort

/-- **A single instruction without an event (`SI`) of the abort path
inside `SFacts`**, after the take (`nodeW_postO`): off the sites (`hok`),
its next pc in its phase (`hph`), the source control as in `blkW_ovf`. -/
theorem nodeW_si_ovf {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {si : SI} {l : Label}
    {off z : Nat} {p : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off [(si.toDir, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : OvfReady c0) (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n :=
  NodeW.ofNoEnv (Spike.Lib.X64.Rt.nodeW_postO (n := ND.noEnv n) hI hp hok hR hR8 hl hh hsub hFO
      fun s c σ hs hn _ hpc _ _ hj hP hO => by
        obtain ⟨c', hc', rfl⟩ := hj
        rw [hJ σ c' hc']
        exact sfacts_si (cfacts_noEnv hc) hP (Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc)
          (Spike.Lib.X64.Rt.next_same hI hpc hph) hO)
    (fun σ c hj => hJ σ c hj ▸ hc) (fun s σ c hj hD => hJ σ c hj ▸ hpl s hD)
    (fun s _ _ hpc => (hI.off s (by unfold pcOf; rw [hpc, hp]; exact hok)).1.noAbort)

end Nodes

/-! ## A stub's `write` system call -/

/-- **`%rax = 1`, `%rdi = 2` decode to a `write` to the error output.** -/
theorem syscallCall_write {r : Reg64s} (ha : r.get64 .rax = 1) (h0 : r.get64 .rdi = 2) :
    ∃ buf n, syscallCall r = some (.write 2 buf n) := by
  simp only [Reg64s.get64] at ha h0
  have ha' : r.rax.toNat = 1 := by rw [← UInt64.toNat_toBitVec, ha]; rfl
  have h0' : r.rdi.toNat = 2 := by rw [← UInt64.toNat_toBitVec, h0]; rfl
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, ha', h0']

section Svc

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A stub's `write` system call inside `W`** is a segment to its next
node, given its code (`hcode`) and its states inside `W` (`hW`): the call
decodes to a `write` to the error output, which the judgement matches, and
every result lands at the next node with the source unmoved. -/
theorem seg_syscallW {W : Frag isa} {K : State → State → Prop} {st : Abort.Stub} {c0 : Ctl}
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (Abort.N (_root_.Executable.labels exe).label st c0 .sys).pc [(op64 .syscall, 2)])
    (hW : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .sys)) :
    SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .sys))
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .n5)) := by
  refine (syscall_ndW (N := fun _ : Unit => Abort.N (_root_.Executable.labels exe).label st c0 .n5)
    (E := fun e : Empty => e.elim) hK hF hcode hW ?_ ?_).mono_post ?_
  · rintro σ c ⟨hJ, h0, ha⟩
    obtain ⟨buf, n, hc⟩ := syscallCall_write ha h0
    refine ⟨_, hc, nofun, fun v _ => ⟨c, .refl c, .inl ⟨(), ?_, by simp [Abort.N, Abort.oI, syscallSO, SO.le, SO.kill]; decide, hJ⟩⟩⟩
    show _ + 36 = _ + 34 + Int64.ofNat 2
    rw [Int64.add_assoc]; rfl
  · rintro s c σ call - ⟨-, h0, ha⟩ hcall
    obtain ⟨buf, n, hc⟩ := syscallCall_write ha h0
    rw [hc] at hcall
    cases hcall
    exact ⟨nofun, nofun, fun fd b n' h => by cases h; decide, fun _ h => by cases h⟩
  · rintro s c (⟨_, h⟩ | ⟨x, _⟩)
    · exact h
    · exact x.elim

end Svc

/-! ## `StubW` (the phase check `abortPhOk` in `Spike/Lib/X64AbortPh.lean`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **The overflow abort path's obligations inside `SFacts … Dt`**
(`Local.StubW`), for a program with the abort code (`hprog`) and the
stub's `write` call (`hsysIn`), an instance's facts (`hI`) and the path's
phase check (`hphs`). The callee's region holds the stub's frame (`hlo`,
`hhi`); the words of `rS` lie off it in the frame condition (`hFO`); the
source control `c0` is about to overflow (`hc`, `hsm`) and placed at every
memory of the frame condition (`hpl`). The exit call is the overflow's
abort site: off the release and take sites (`hrel`, `htk`), no other
kind's (`hk`), no outside move (`hKex`), the memory side's abort
(`hms`). The write tail `Dt` holds at the `write` (`hwr`). -/
theorem stubW_sfacts {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {c0 : Ctl} {Dt : State → Prop}
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.overflow c0 .sys) s c → Dt s) :
    Abort.Local.StubW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p al ms exe endPc R F c0 := by
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.1.1.1
  have hdi := hsd.2
  have hscode := Scc.Cert.Rt.X64.Abort.code_stub (c0 := c0) hI.lays hI.endOk hst
  have hdcode := Scc.Cert.Rt.X64.Abort.code_disp (c0 := c0) hI.lays hI.endOk hdi
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hb1, -, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, -, hg1, -⟩ := hdi
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pg1, pb0, o1, q1, pb1, o5, q5, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => Spike.Lib.X64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he34 : (_root_.Executable.labels exe).label Abort.overflow.entry + Int64.ofNat 34 =
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys).pc := rfl
  have hsysW : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o5)
    exact ⟨hc0 ▸ sfacts_syscallOvf hc (hpl s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q5)
      (hown s _ σ hA hD) (abortOk_of_ne hP.1.noAbort) (fun _ _ _ _ => hwr s c hAt), hP.2⟩
  refine ⟨hdcode, ?_, ?_, ?_, hscode, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_ovf hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hpl
  · exact blkW_ovf hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hpl
  · exact blkW_ovf hI hg1 (ofNat_zero' _) Abort.Disp.g1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pg1 rfl (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb0 (ofNat_zero' _) Abort.x0_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h) hc hpl
  · exact nodeW_si_ovf (si := Abort.siMsg Abort.overflow) hI hn1 rfl (ofNat_zero' _).symm o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb1 rfl Abort.x1Overflow_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h) hc hpl
  · exact blkW_ovf hI hb2 rfl Abort.x2_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h) hc hpl
  · rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ, hax, hdi⟩
    have hc0 : c = c0 := hJ
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.overflow.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ.regs.rdi.toNat) := by
      rw [← syscallCall_exitGroup hx231, syscallCall, ← hA.regs]; rfl
    refine ⟨hc0 ▸ sfacts_syscallOvf hc (hpl s hD) (fun a ha => hpcN ▸ hrel a ha) (fun a ha => hpcN ▸ htk a ha)
      (Spike.Lib.X64.Rt.cellOf hI hx (ofNat_zero' _) hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc qx)
      (hown s _ σ hA hD) (abortOk_ovf (fun k a ha e => hk k a ha (hpcN ▸ e)) hc hsm fun v hv => ?_)
      (fun _ _ _ h => by rw [hd] at h; cases h), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    simp only [Reg64s.get64] at hdi
    rw [← UInt64.toNat_toBitVec, hdi]; rfl
  · exact seg_syscallW hK hF (code_field hI.lays hI.endOk hsysIn he34) hsysW
  · exact fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc

end Stub

end Spike.Lib.X64.StubW
