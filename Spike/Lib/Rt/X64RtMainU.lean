/-
**`scc_rt_main`'s and the switch's states inside `W` on x86-64, for any
program** (`mainUW_gen`, `swUW_gen`): the obligations `MainUW`
(`Spike/Lib/Rt/X64Main.lean`) of `scc_rt_main`'s own nodes (the
stack-checked prologue, `call fn`, the `exit_group` tail) and `SwUW`
(`Spike/Lib/Rt/X64Segs.lean`) of the switch, `xorl %ebp, %ebp` and the block
after it, from an instance's facts (`InstOk`), the code checks (`mainUIn`,
`startTailIn`), the phase facts (`MainPh`, `SwPh`) and the limit word's
facts. The twin of `Spike/Lib/Rt/A64RtMainU.lean`.

- **The phase facts** (`MainPh`, `SwPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target, no `ret`; the
  limit's load, the `syscall`, the switch and `xorl` off the sites and in
  their next pc's phase. All of `scc_rt_main` and the switch run after the
  take.
- **The limit word** `limA tp` (`tp` the thread pointer): mapped read-only
  in the loaded kernel state, unmapped in private memory under the frame
  condition (after the switch, `swF` says so).
- **The post** `Post` of `MainUW` gives the source control's facts at the
  return point (`hPost`); on `ret0`, `ret0Post c0` keeps `c0`.
- **The user function** stays an interface (`UserCallW`), a premise of
  `swUW_gen` (`SwUW.user`'s statement).
- **Unlike AArch64**: the region asks 8-alignment only (no 16-aligned `sp`
  on x86-64); offsets are bytes (`MainCode`'s cell sizes); the call block
  pushes its return address, so the region holds `8` below the frame; the
  switch is followed by `xorl %ebp, %ebp` (`SwPh.xor`).
- **Oracle**: `ret0.x`'s `mainW`/`swW` (`Spike/Lib/X64Ret0I.lean`) give the
  same `MainUW`/`SwUW` as these at their instance (`Spike/Test/X64RtMainU.lean`).
-/
import Spike.Lib.Rt.X64RtTi
import Spike.Lib.Rt.X64Segs

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xHead xLea xCmp xFr xExit xSt xHead_ok xLea_ok xCmp_ok xFr_ok
  xExit_ok xS2 xS1 hdRegs prologueIn exitIn)
open Spike.Lib.X64.Flow.Ret0 (MainG StackM StackOff CallerCells limA swF startN6 startN7 startN8 startMain
  startTailIn x1L tpOf)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)

namespace MainU

/-- **`scc_rt_main`'s phase facts** at labels `lab`, phase index `ph`,
off-site pcs `okPc`: the prologue's blocks, the call's and the tail's at
their pcs, no dead target; the limit's load and the `syscall` off the sites
and in their next pc's phase. -/
structure MainPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (mc : MainCode) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab "scc_rt_main" + Int64.ofNat 0) 0 xHead = true
  lea : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat 0) 0 (xLea mc.Z mc.zl) = true
  ld : okPc (lab mc.sc + Int64.ofNat mc.zl).toBitVec.toNat = true ∧
    ph (lab mc.sc + Int64.ofNat mc.zl + Int64.ofNat mc.zf).toBitVec.toNat =
      ph (lab mc.sc + Int64.ofNat mc.zl).toBitVec.toNat
  cmp : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat (mc.zl + mc.zf)) 0
    (xCmp mc.grow mc.z1 mc.z2) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab mc.sc + Int64.ofNat (mc.zl + mc.zf + mc.z1 + mc.z2)) 0
    (xFr mc.Z mc.zs mc.ps) = true
  call : blkPh okPc ph (fun _ => false) lab (lab mc.e0 + Int64.ofNat 0) 0 (callB mc.fn) = true
  ex : blkPh okPc ph (fun _ => false) lab (lab mc.sp0 + Int64.ofNat 0) 0 (xExit mc.k mc.ze0 mc.ze1 mc.ze2) = true
  svc : okPc (lab mc.sp0 + Int64.ofNat (mc.ze0 + mc.ze1 + mc.ze2)).toBitVec.toNat = true ∧
    ph (lab mc.sp0 + Int64.ofNat (mc.ze0 + mc.ze1 + mc.ze2) + Int64.ofNat 2).toBitVec.toNat =
      ph (lab mc.sp0 + Int64.ofNat (mc.ze0 + mc.ze1 + mc.ze2)).toBitVec.toNat

/-- **The switch's phase facts**: the switch `movq %rax, %rsp` and
`xorl %ebp, %ebp` off the sites and in their next pc's phase, the block
after them (`startMain`) at its pc. -/
structure SwPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) : Prop where
  sw : okPc (lab x1L + Int64.ofNat 28).toBitVec.toNat = true ∧
    ph (lab x1L + Int64.ofNat 28 + Int64.ofNat 3).toBitVec.toNat = ph (lab x1L + Int64.ofNat 28).toBitVec.toNat
  xor : okPc (lab x1L + Int64.ofNat 31).toBitVec.toNat = true ∧
    ph (lab x1L + Int64.ofNat 31 + Int64.ofNat 2).toBitVec.toNat = ph (lab x1L + Int64.ofNat 31).toBitVec.toNat
  main : blkPh okPc ph (fun _ => false) lab (lab x1L + Int64.ofNat 33) 0 startMain = true

theorem xHead_noRet : noRetBlk xHead = true := rfl
theorem xLea_noRet (Z : Int64) (z : Nat) : noRetBlk (xLea Z z) = true := rfl
theorem xCmp_noRet (L : Label) (z1 z2 : Nat) : noRetBlk (xCmp L z1 z2) = true := rfl
theorem xFr_noRet (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) : noRetBlk (xFr Z z ps) = true := by
  have hc : ∀ p, classify (xSt p).1 = some (AI.st .rbp p.2.1 p.1) := fun _ => rfl
  simp only [noRetBlk, xFr, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨rfl, fun p _ => by simp only [Function.comp_apply, hc]⟩
theorem callB_noRet (fn : Label) : noRetBlk (callB fn) = true := rfl
theorem xExit_noRet (k : Int64) (z0 z1 z2 : Nat) : noRetBlk (xExit k z0 z1 z2) = true := rfl
theorem startMain_noRet : noRetBlk startMain = true := rfl

end MainU

/-! ## Obligations under an unsatisfiable frame condition -/

section False

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- A block obligation under an unsatisfiable frame condition. -/
theorem blkW_ofFalse {n : ND} {blk : List (Directive × Nat)} (h : ∀ m, ¬ F m) : BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hD _ => (h _ hD).elim

/-- A node obligation under an unsatisfiable frame condition. -/
theorem nodeW_ofFalse {n : ND} (h : ∀ m, ¬ F m) : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hD, _⟩ => (h _ hD).elim

/-- `scc_rt_main`'s own obligations under an unsatisfiable frame condition. -/
theorem mainUW_ofFalse {ms : MemSide isa} {mc : MainCode} {Post : Ctl → BitVec 64 → Prop} {g : MainG}
    (h : ∀ m, ¬ F m) : MainUW W K exe endPc R F ms mc Post g :=
  ⟨⟨blkW_ofFalse h, blkW_ofFalse h, nodeW_ofFalse h, blkW_ofFalse h, blkW_ofFalse h⟩, blkW_ofFalse h,
    ⟨blkW_ofFalse h, nodeW_ofFalse h⟩⟩

end False

/-! ## `scc_rt_main` and the switch -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- No `ret` in a block: `hret` of `blkW_postO`, for any return address. -/
private theorem hnr {blk : List (Directive × Nat)} (hb : noRetBlk blk = true) {n : ND} {ra' : Int64} :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
  fun _ _ _ k hk hr => (noRet_false hb k hk hr).elim

set_option maxHeartbeats 800000 in
open MainU in
/-- **`scc_rt_main`'s own states are inside `SFacts`** (`MainUW`), for any
program with its code (`hin`), in any 8-aligned region holding its frame of
`Z` (`8`-aligned, `hZ8`) and the return address its call pushes (`hlo`),
with the source control's facts at the entry (`hC0`) and at the return
point under `Post` (`hPost`), its phase facts (`hph`), the parameters'
slots and the exit value's in the frame (`hps`, `hk`), the limit word
`limA g.tp` mapped (`hmr`) and unmapped in private memory under the frame
condition (`hun`), `rS` in the pool (`hsub`) and not wrapping (`hfit`), and
the frame condition giving the words of `rS` off the region (`hFO`). -/
theorem mainUW_gen {ms : MemSide isa} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph) {mc : MainCode}
    (hin : mainUIn cells mc = true) {Post : Ctl → BitVec 64 → Prop} {g : MainG} (hC0 : CFacts Λ lbl g.c0)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - mc.Z.toInt - 8) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms mc Post g := by
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩, bCall⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : lab "scc_rt_main" + 1 + 3 = lab mc.sc := by rw [esc, Int64.add_assoc]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hI.labOk]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact blkW_postO hI bHd (ofNat_zero' _) (xHead_ok (lo := -8 - mc.Z.toInt) (hi := 0) (by omega) (Int.le_refl _))
        hR (by omega) hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ hC0) hph.hd (hnr xHead_noRet) (fun _ _ _ => rfl) hsub hfit
        hFO
    · exact blkW_postO hI bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
        (xLea_ok (lo := -8 - mc.Z.toInt) (hi := 0) _ _) hR (by omega) hhi hR8 hl hh
        (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) hph.lea (hnr (xLea_noRet _ _)) (fun _ _ _ => rfl) hsub hfit hFO
    · exact nodeW_fsld_postO (p := lab mc.sc + Int64.ofNat mc.zl) hI bLd rfl
        (by show _ + 1 + 3 + _ = _; rw [h4]) (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) hph.ld.1 hph.ld.2
        (fun _ _ ⟨σ0, hJ, he⟩ => by
          rw [he, show (xS2 mc.Z σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64],
            hJ.2.2]
          rfl)
        hmr hun hR hR8 hl hh hsub hFO
    · exact blkW_postO hI bCmp (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
        (xCmp_ok (lo := -8 - mc.Z.toInt) (hi := 0) _ _ _ _) hR (by omega) hhi hR8 hl hh
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hph.cmp (hnr (xCmp_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit hFO
    · exact blkW_postO hI bFr (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
        (xFr_ok (lo := -8 - mc.Z.toInt) (hi := 0) _ _ _ hps) hR (by omega) hhi hR8 hl hh
        (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hph.fr (hnr (xFr_noRet _ _ _)) (fun _ _ _ => rfl) hsub hfit hFO
  · rw [hI.labOk]
    exact blkW_postO hI bCall (ofNat_zero' _)
      (okBlk_callB (lo := -8 - mc.Z.toInt - 8) (hi := 0) _ (by simp [Spike.Lib.offOk, mainU1R]; omega)) hR hlo hhi hR8 hl
      hh (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.call (hnr (callB_noRet _)) (fun _ _ _ => rfl) hsub hfit hFO
  · rw [hI.labOk]
    refine ⟨?_, ?_⟩
    · exact blkW_postO hI bEx (ofNat_zero' _) (xExit_ok (lo := -8 - mc.Z.toInt) (hi := 0) _ _ _ _ hk) hR (by omega)
        hhi hR8 hl hh (fun _ _ hJ => hPost _ _ hJ.1) hph.ex (hnr (xExit_noRet _ _ _ _)) (fun _ _ _ => rfl) hsub hfit
        hFO
    · exact nodeW_syscall_postO (p := lab mc.sp0 + Int64.ofNat (mc.ze0 + mc.ze1 + mc.ze2)) hI bSvc rfl
        (by show _ + _ + _ + _ = _; rw [ofNat_add', ofNat_add']; rfl)
        (fun _ _ ⟨_, _, hJ, _⟩ => hPost _ _ hJ.1) hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO
        (fun _ _ h => by rw [h.1]; decide)

set_option maxHeartbeats 800000 in
open MainU in
/-- **The switch's and `scc_rt_main`'s states are inside `SFacts`**
(`SwUW`), for any program with the start's tail (`hin`) and `scc_rt_main`'s
code (`hmain`): the switch in any region with the stack range in private
memory; `xorl %ebp, %ebp`, the block after it and `scc_rt_main`'s own states
in the new stack's region of depth `L` (holding `scc_rt_main`'s frame, the
two return addresses and `8`, 8-aligned) at its top `top` (8-aligned;
vacuous off it), with the source control's facts (`hC0`, `hPost`), the
phase facts (`hph`, `hsw`), the frame's facts (`hZ` to `hk`), the limit word
of the TCB `tcb` mapped (`hmr`), `rS` in the pool (`hsub`) and not wrapping
(`hfit`), and the user function's interface (`hU`, `SwUW.user`). -/
theorem swUW_gen {p : Prog} {lbl' : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph) (hin : startTailIn cells = true) {mc : MainCode}
    (hmain : mainUIn cells mc = true) {Post : Ctl → BitVec 64 → Prop} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc) (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int} {D : Int} {ZU : Int64}
    (h8 : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : mc.Z.toInt + 24 ≤ L) (hL8 : L % 8 = 0)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (tpOf tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p lbl' ms exe endPc
        ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' mc.fn mc.Z D ZU Post
        ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb)) :
    SwUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p lbl' exe endPc R (fun m => F m ∧ StackM rS m) ms rS tcb
      top c0 L mc D ZU Post := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, bSw⟩, bXor⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_, hU⟩
  · rw [hI.labOk]
    exact nodeW_reg_post (p := lab x1L + Int64.ofNat 28) hI (by rfl) bSw rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1
      hsw.sw.2 hsub
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact nodeW_fi_postO (p := lab x1L + Int64.ofNat 31) hI bXor rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hsw.xor.1
        hsw.xor.2 hok h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hsub (fun _ h => h.2)
    · exact nodeW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact blkW_postO hI bMain rfl (startMain_okL (by omega)) hok (Int.le_refl _) (Int.le_refl _) h8
        (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main
        (hnr startMain_noRet) (fun _ _ _ => rfl) hsub hfit (fun _ h => h.2)
    · exact blkW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      have hR := Region.callee_ok (kc := -8 - 0) (lo' := 8 - L) (hi' := 8) hok (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by show _ ≤ (0 : Int); omega)
      have hb0 : (((swR v (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) = v.toNat + (-8 - 0) :=
        Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      exact mainUW_gen hI hmain hC0 hPost hph hR (by omega) (by show 8 - L ≤ _; omega)
        (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide) hZ hZ8 hps hk hmr (fun _ h => h.1.1.2) hsub hfit
        (fun _ h => stackOff_callee hok h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
          (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by decide) h.1.2 h.2)
    · exact mainUW_ofFalse fun _ h => hv h.1.1.1

end Main

end Spike.Lib.X64.Rt
