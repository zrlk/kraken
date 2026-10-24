/-
**`scc_rt_main`'s and the switch's states inside `W`, for any program**
(`mainUW_gen`, `swUW_gen`): the obligations `MainUW` (`Spike/Lib/Rt/A64Main.lean`)
of `scc_rt_main`'s own nodes (the stack-checked prologue, `bl fn`, the
`exit_group` tail) and `SwUW` (`Spike/Lib/Rt/A64Segs.lean`) of the switch
and the block after it, from an instance's facts (`InstOk`), the code checks
(`mainUIn`, `startTailIn`), the phase facts (`MainPh`, `SwPh`) and the limit
word's facts.

- **The phase facts** (`MainPh`, `SwPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target, no `ret`; the
  limit's load, the `svc` and the switch off the sites and in their next
  pc's phase. All of `scc_rt_main` and the switch run after the take.
- **The limit word** `limA tp` (`tp` the thread pointer): mapped read-only
  in the loaded kernel state, unmapped in private memory under the frame
  condition (after the switch, `swF` says so).
- **The post** `Post` of `MainUW` gives the source control's facts at the
  return point (`hPost`); on `ret0`, `ret0Post c0` keeps `c0`.
- **The user function** stays an interface (`UserCallW`), a premise of
  `swUW_gen`.
- **Oracle**: `ret0.w`'s `mainW`/`swW` (`Spike/Lib/A64Ret0I.lean`) give the
  same `MainUW`/`SwUW` as these at their instance (`Spike/Test/A64RtMainU.lean`).
-/
import Spike.Lib.Rt.A64RtTi
import Spike.Lib.Rt.A64Segs

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (MainG mainN0 limA tcbA_limA StackM StackOff swF startN5 startN6 startMain
  startTailIn sp3L)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)

namespace MainU

/-- **`scc_rt_main`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`: the prologue's blocks, the call's and the tail's at
their pcs, no dead target; the limit's load and the `svc` off the sites and
in their next pc's phase. -/
structure MainPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (mc : MainCode) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat (4 * 0)) 0 (chkHead mc.Z) = true
  ld : okPc (lab mc.sc + Int64.ofNat (4 * 2)).toBitVec.toNat = true ∧
    ph (lab mc.sc + Int64.ofNat (4 * 2) + Int64.ofNat 4).toBitVec.toNat =
      ph (lab mc.sc + Int64.ofNat (4 * 2)).toBitVec.toNat
  br : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat (4 * 3)) 0 (chkBr mc.grow) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat (4 * 5)) 0 (frameSet mc.Z [(.X0, 0)]) = true
  call : blkPh okPc ph (fun _ => false) lab (lab mc.e0 + Int64.ofNat (4 * 0)) 0 [blD mc.fn] = true
  ex : blkPh okPc ph (fun _ => false) lab (lab mc.sp0 + Int64.ofNat (4 * 0)) 0 (exitTail mc.k) = true
  svc : okPc (lab mc.sp0 + Int64.ofNat (4 * 3)).toBitVec.toNat = true ∧
    ph (lab mc.sp0 + Int64.ofNat (4 * 3) + Int64.ofNat 4).toBitVec.toNat =
      ph (lab mc.sp0 + Int64.ofNat (4 * 3)).toBitVec.toNat

/-- **The switch's phase facts**: the switch `mov sp, x9` off the sites and
in its next pc's phase, the block after it (`startMain`) at its pc. -/
structure SwPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Prop where
  sw : okPc (lab sp3L + Int64.ofNat (4 * 5)).toBitVec.toNat = true ∧
    ph (lab sp3L + Int64.ofNat (4 * 5) + Int64.ofNat 4).toBitVec.toNat =
      ph (lab sp3L + Int64.ofNat (4 * 5)).toBitVec.toNat
  main : blkPh okPc ph (fun _ => false) lab (lab sp3L + Int64.ofNat (4 * 6)) 0 startMain = true

theorem chkHead_noRet (Z : Int64) : noRetBlk (chkHead Z) = true := by
  simp [noRetBlk, chkHead, Flow.classify, Flow.RegOnly]
theorem chkBr_noRet (L : Label) : noRetBlk (chkBr L) = true := by simp [noRetBlk, chkBr, Flow.classify, Flow.RegOnly]
theorem frameSet_noRet (Z : Int64) : noRetBlk (frameSet Z [(.X0, 0)]) = true := by
  simp [noRetBlk, frameSet, frSetup, spStr, Flow.classify, Flow.RegOnly]
theorem blD_noRet (fn : Label) : noRetBlk [blD fn] = true := by simp [noRetBlk, blD, Flow.classify, Flow.RegOnly]
theorem exitTail_noRet (k : Int64) : noRetBlk (exitTail k) = true := by
  simp [noRetBlk, exitTail, spStr, RW.dir, Flow.AI.toDir, Flow.classify, Flow.RegOnly]
theorem startMain_noRet : noRetBlk startMain = true := by decide

/-! The prologue's pcs, `n` instructions on. -/

theorem pc2 (a : Int64) : a + Int64.ofNat (4 * 2) = a + 4 + 4 := by rw [ofNat4_succ, ofNat4_succ, ofNat4_zero]
theorem pc3 (a : Int64) : a + Int64.ofNat (4 * 3) = a + 4 + 4 + 4 := by
  rw [ofNat4_succ, ofNat4_succ, ofNat4_succ, ofNat4_zero]
theorem pc5 (a : Int64) : a + Int64.ofNat (4 * 5) = a + 4 + 4 + 4 + 4 + 4 := by
  rw [ofNat4_succ, ofNat4_succ, ofNat4_succ, ofNat4_succ, ofNat4_succ, ofNat4_zero]

end MainU

/-! ## Obligations under an unsatisfiable frame condition -/

section False

variable {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- A block obligation under an unsatisfiable frame condition. -/
theorem blkW_ofFalse {n : ND} {blk : List Directive} (h : ∀ m, ¬ F m) : BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hD _ => (h _ hD).elim

/-- A node obligation under an unsatisfiable frame condition. -/
theorem nodeW_ofFalse {n : ND} (h : ∀ m, ¬ F m) : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hD, _⟩ => (h _ hD).elim

/-- `scc_rt_main`'s own obligations under an unsatisfiable frame condition. -/
theorem mainUW_ofFalse {ms : MemSide isaLSE2} {mc : MainCode} {Post : Ctl → BitVec 64 → Prop} {g : MainG}
    (h : ∀ m, ¬ F m) : MainUW W K exe endPc R F ms mc Post g :=
  ⟨⟨blkW_ofFalse h, nodeW_ofFalse h, blkW_ofFalse h, blkW_ofFalse h⟩, blkW_ofFalse h,
    ⟨blkW_ofFalse h, nodeW_ofFalse h⟩⟩

end False

/-! ## `scc_rt_main` and the switch -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- No `ret` in a block: `hret` of `blkW_postO`, for any return address. -/
private theorem hnr {blk : List Directive} (hb : noRetBlk blk = true) {n : ND} {ra' : Int64} :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
  fun _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim

/-- **A node at a register operation of the flow's class** (`Flow.RegOnly`,
which also writes `sp`, as the switch `mov sp, x9` does) after the take:
as `nodeW_reg_post`. -/
theorem nodeW_flowReg_post {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {R : Region}
    {F : MachineData → Prop} {n : ND} {w : RegWidth} {op : Operation w} {l : Label} {k : Nat} {p : Int64}
    (hop : Flow.RegOnly op = true) (hb : blockAt prog l k [.instr ⟨w, op⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub Λ.stackPool) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hI hp hok hsub fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    exact sfacts_done (hC σ c hJ) hP hc (fun imm h => by cases h; simp [Flow.RegOnly] at hop)
      (Flow.exec_reg hop hc) (next_same hI hpc hph _).1 (next_same hI hpc hph _).2 hO

set_option maxHeartbeats 800000 in
open MainU in
/-- **`scc_rt_main`'s own states are inside `SFacts`** (`MainUW`), for any
program with its code (`hin`), in any 16-aligned region holding its frame of
`Z` with 8-aligned bounds, with the source control's facts at the entry
(`hC0`) and at the return point under `Post` (`hPost`), its phase facts
(`hph`), the limit word `limA g.tp` mapped (`hmr`) and unmapped in private
memory under the frame condition (`hun`), `rS` in the pool (`hsub`) and not
wrapping (`hfit`), and the frame condition giving the words of `rS` off the
region (`hFO`). -/
theorem mainUW_gen {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {mc : MainCode}
    (hin : mainUIn prog mc = true) {Post : Ctl → BitVec 64 → Prop} {g : MainG} (hC0 : CFacts Λ lbl g.c0)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -mc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms mc Post g := by
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩, bCall⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGap hI.lays hgap
  rw [hI.labOk] at esc
  have hR8 : R.base.toNat % 8 = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hI.labOk]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact blkW_postO hI bHd (by rw [esc, ofNat4_zero, ofNat4_zero]) (chkHead_ok _ _ _) hR hal hlo hhi
        (fun _ _ hJ => hJ.1 ▸ hC0) hph.hd (hnr (chkHead_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact nodeW_ldr_postO hI bLd rfl (by show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2])
        (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) hph.ld.1 hph.ld.2
        (fun _ _ ⟨_, hJ, he⟩ => by rw [he, rAddr_chkRegs]; exact tcbA_limA hJ.2.2) hmr hun hR hR8 hl hh hsub hFO
    · exact blkW_postO hI bBr (by rw [esc, ofNat4_zero, pc3]; rfl) (chkBr_ok _ _ _ _) hR hal hlo hhi
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hph.br (hnr (chkBr_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact blkW_postO hI bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
        (frameSet_ok (lo := -mc.Z.toInt) (hi := 0) h16 hZ (by omega) (Int.le_refl _)
          (by simp [Spike.Lib.offOk]; omega)) hR hal hlo hhi
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hph.fr (hnr (frameSet_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit
        hFO
  · rw [hI.labOk]
    exact blkW_postO hI bCall (ofNat4_zero _) (okBlk_blD _ _ _ _) hR hal hlo hhi (fun _ _ hJ => hJ.1 ▸ hC0)
      hph.call (hnr (blD_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  · rw [hI.labOk]
    refine ⟨?_, ?_⟩
    · exact blkW_postO hI bEx (ofNat4_zero _) (exitTail_ok (lo := -mc.Z.toInt) (hi := 0) hk
          (by show (-mc.Z.toInt) % 16 = 0; omega)) hR hal hlo hhi (fun _ _ hJ => hPost _ _ hJ)
        hph.ex (hnr (exitTail_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    · exact nodeW_svc_postO hI bSvc rfl (pc3 _).symm (fun _ _ ⟨_, _, hP, _⟩ => hPost _ _ hP) hph.svc.1
        hph.svc.2 hR hR8 hl hh hsub hFO (fun _ _ h => by rw [h.1]; decide)

set_option maxHeartbeats 800000 in
open MainU in
/-- **The switch's and `scc_rt_main`'s states are inside `SFacts`**
(`SwUW`), for any program with the start's tail (`hin`) and `scc_rt_main`'s
code (`hmain`): the switch in any region with the stack range in private
memory, the block after it and `scc_rt_main`'s own states in the new stack's
region of depth `L` (holding `scc_rt_main`'s frame, 8-aligned) at its top
`top` (16-aligned; vacuous off it), with the source control's facts (`hC0`,
`hPost`), the phase facts (`hph`, `hsw`), the limit word of the TCB `tcb`
mapped (`hmr`), `rS` in the pool (`hsub`) and not wrapping (`hfit`), and the
user function's interface (`hU`). -/
theorem swUW_gen {p : Prog} {lbl' : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hin : startTailIn prog = true) {mc : MainCode}
    (hmain : mainUIn prog mc = true) {Post : Ctl → BitVec 64 → Prop} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc) (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int} {D : Int} {ZU : Int64}
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL : mc.Z.toInt ≤ L) (hL8 : L % 8 = 0)
    (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (UInt64.ofBitVec tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v, UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p lbl' ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)) :
    SwUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p lbl' exe endPc R (fun m => F m ∧ StackM rS m) ms rS tcb
      top c0 L mc D ZU Post := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨-, bSw⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_, hU⟩
  · rw [hI.labOk]
    exact nodeW_flowReg_post hI (by simp [Flow.RegOnly]) bSw rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1 hsw.sw.2
      hsub
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact blkW_postO hI bMain rfl (startMain_okL (-L) 0) hok h16 (Int.le_refl _) (Int.le_refl _)
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main (hnr startMain_noRet) (fun _ _ _ => rfl)
        (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hsub hfit (fun _ h => h.2)
    · exact blkW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      exact mainUW_gen hI hmain hC0 hPost hph hok h16 (by show -L ≤ _; omega) (Int.le_refl _)
        (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hZ16 hZ hk hmr (fun _ h => h.1.2) hsub hfit
        (fun _ h => h.2)
    · exact mainUW_ofFalse fun _ h => hv h.1.1

end Main

end Spike.Lib.A64.Rt
