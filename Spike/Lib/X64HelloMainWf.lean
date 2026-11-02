/-
**hello.w's `scc_rt_main` up to `call wc_rodata` inside `W0`** (x86-64;
twin of `Spike/Lib/A64HelloMainWf.lean`, the hello twin of
`X64WakeMainWf`): the prologue (frame 64) and `.entry`'s call block of
`Hello1.MainPreW` (`pro`, `call`) at the start's level
`HelloPh.StartWf.WSH` (`W0` at the frames `[]` at `ownGH`). They are proved
from each node's `SFacts` at `ownH` (`Rt.blkW_postO`, `Rt.nodeW_fsld_postO`
at `instOkHS`), moved to `ownGH` at free pcs (`StartWf.blkW_W0SH`,
`nodeW_W0S_fsldH`). hello's `scc_rt_main` calls `wc_rodata` first
(`Hello1.mB0`), so the glue goes on through `wc_rodata`'s segment
(`Hello1.MainPreW.rd`) before `wc_main`.

- `mainTabH`, `mainH_fact`: `scc_rt_main`'s phase facts before
  `call wc_rodata`.
- `nodeW_W0S_fsldH`: a thread-pointer load of the start's level inside `W0`.
- `mainPreWH_W0SH`: `MainPreW.pro` and `.call` inside `WSH`.

## Differences from the AArch64 version

As `X64WakeMainWf` against AArch64 wake: the prologue is x86-64's five
nodes (`XProW`: the head `pushq %rbp; movq %rsp, %rbp`, the check's `leaq`,
the limit's load `movq %fs:8, %r11`, the check `cmpq; jb`, the frame's
`subq` and `%rdi`'s store), so `mainTabH` has five prologue rows at
`.Lscc_rt_main.chk`'s byte offsets and the load node is `nodeW_W0S_fsldH`
(AArch64's `nodeW_W0S_ldrH`): its address is `%fs`'s base `+ k`, its free
pcs `freeAtH l [o, o + z]` and phase check `siOffW pfxM l o z` take the
cell's size. No `hal` (no 16-alignment): the region's base is 8-aligned
(`hR8`). The bounds are the call block's (`R.lo ≤ -288`, `8 ≤ R.hi`,
`Hello1.mB0_ok`: `call` pushes its return address below the frame; AArch64:
`-80`, `0`). The frame is `64` under the saved `%rbp` (AArch64: `80` with
the pair). hello's x86-64 `scc_rt_main` is hello1's at the same labels, so
the blocks and nodes are `Hello1`'s (`mB0`, `mN0`), decided on `helloCells`
by `HelloM.hello_mainPro` / `hello_mainIn`. AArch64's `hmfree_dec` is dead
and not twinned; `StartWf.wsfreeH_dec` / `wsfreeBH_dec` are used.
-/
import Spike.Lib.X64HelloStartWf
import Spike.Lib.X64HelloMain

namespace Spike.Lib.X64.HelloPh.MainWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (PhFact blockAtB okPcOf codeT codeT_eq factOk)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts CFacts noRetBlk)
open Spike.Lib.X64 (ND BlkW NodeW At fsDir)
open Spike.Lib.X64.Flow (xHead xLea xCmp xFr)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_labH goodW_of_freeNH)
open Spike.Lib.X64.HelloPh.StartWf (WSH blkW_W0SH nodeW_W0S_stepH pfxM)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt)

/-! ## The phase facts -/

/-- **`scc_rt_main`'s blocks before `call wc_rodata`**: the prologue's four
blocks and its load, `.entry`'s call block. -/
def mainTabH : List PhFact :=
  [.blk "scc_rt_main" 0 xHead none none,
   .blk ".Lscc_rt_main.chk" 0 (xLea 64 5) none none,
   .step ".Lscc_rt_main.chk" 5 9,
   .blk ".Lscc_rt_main.chk" 14 (xCmp ".Lscc_rt_main.stk" 3 2) none none,
   .blk ".Lscc_rt_main.chk" 19 (xFr 64 4 [(.rdi, -8, 4)]) none none,
   .blk ".Lscc_rt_main.entry" 0 Spike.Lib.X64.Flow.Hello1.mB0 none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem mainFactsH : mainTabH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

/-- **A fact of `mainTabH` at `phH`.** -/
theorem mainH_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ mainTabH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp mainFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **A thread-pointer load `movq %fs:k, %d` of the start's level inside
`W0`** at the frames `[]`, as `StartWf.nodeW_W0SH`: its `SFacts` at the
first instance (`hS`), its address `A` (`ha`) unmapped in private memory
(`hun`), its pc off the sites (`hokpc`), its pc and next pc free
(`hfree`), its abort phases' check (`hph`), its controls `c0` (`hJ`). -/
theorem nodeW_W0S_fsldH {n : ND} {d : Reg64} {k : Int64} {l : Label} {o z : Nat} {A : BitVec 64}
    (hb : blockAtB helloCells l o [(fsDir d k, z)] = true) (he : L.lab l + Int64.ofNat o = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = A)
    (hun : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat o).toBitVec.toNat = true)
    (hfree : freeAtH l [o, o + z] = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l o z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hcell : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (fsDir d k) z :=
    fun s c ⟨hs, hn, _, hpc, _⟩ => Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he hs hn hpc
  have hex : ∀ s c, At L.exe L.endPc R F n s c →
      isa.exec s = some (.load .plain false ⟨A, 8⟩ fun v =>
        .done (Kraken.Promising.Lower.X64.after s z
          { s.st.1 with regs := s.st.1.regs.set (.low d .W64) (v.setWidth 64) })) := by
    intro s c hA
    obtain ⟨_, _, hdc, _, σ, hAb, hF, hJ'⟩ := id hA
    have ha' : Kraken.Promising.Lower.X64.fsAddr s z { base := none, idx := none, disp := .int64 k } = A := by
      rw [← ha σ c hJ']
      simp [Kraken.Promising.Lower.X64.fsAddr, Kraken.Promising.Lower.X64.eaddr, AddrExpr.interp,
        ConstExpr.interp, hAb.regs]
    exact Kraken.Promising.Lower.X64.exec_movfs_load_agrees (hcell s c hA) ha' (hun _ hF)
      (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine nodeW_W0S_stepH hp hlo hlab hsite hcl hc0 hpl0 hX0 he hS hokpc hfree hph (fun s c hA => ?_)
    (fun s c hA => ⟨Spike.Lib.X64ConsumerA.noWr_load (hex s c hA), fun _ h => h⟩) hJ
  refine ⟨_, _, hcell s c hA, fun w w' h => ?_, hex s c hA, fun s' hu => ?_⟩
  · obtain ⟨rfl, rfl, h⟩ := h
  · obtain ⟨_, hu⟩ := hu
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl

set_option maxHeartbeats 1600000 in
/-- **hello.w's `scc_rt_main` up to `call wc_rodata` inside `W0`**
(`Hello1.MainPreW`'s `pro` and `call` at `WSH`) at every entry invariant `J`
whose controls are `c0` and whose thread pointer is `tp` (`hJ`): the
prologue's blocks and load and `.entry`'s call block from their `SFacts` at
`ownH` (`Rt.blkW_postO`, `Rt.nodeW_fsld_postO`, in an 8-aligned region
holding the frame of `64` under the saved `%rbp`, the call block's bounds
`[-288, 8]` (`Hello1.mB0_ok`), the words of `rS` off it under `F`, `hFO`),
the limit word `limA tp` mapped (`hmr`) and unmapped in private memory
(`hun`); their pcs free and their phases decided. -/
theorem mainPreWH_W0SH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {ms : Spike.Lib.MemSide isa}
    {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.fsBase = tp)
    (hC0 : CFacts L.Λ lbl' c0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub L.Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.X64.Flow.Ret0.StackOff rS R m)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.X64.Flow.XProW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
        R F ms (L.lab "scc_rt_main") 64 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J ∧
      BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
        (Spike.Lib.X64.Flow.Hello1.mN0 L.lab R J) Spike.Lib.X64.Flow.Hello1.mB0 := by
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hin := Spike.Lib.X64.Flow.HelloM.hello_mainPro
  simp only [Spike.Lib.X64.Flow.HelloM.hMainPro, Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := hin
  have hin2 := Spike.Lib.X64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.X64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin2
  obtain ⟨⟨⟨b0, -⟩, -⟩, -⟩ := hin2
  have esc : L.lab ".Lscc_rt_main.chk" = L.lab "scc_rt_main" + Int64.ofNat 4 :=
    Scc.Cert.Rt.X64.label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "scc_rt_main" + 1 + 3 = L.lab ".Lscc_rt_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have okB : ∀ {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {pc ra : Int64}
      {blk : List (Directive × Nat)},
      Spike.Lib.X64Consumer.blkPh okP phf d L.lab pc ra blk = true →
      ∀ j < blk.length, okP (pc + Int64.ofNat (Spike.Lib.X64.cellOff blk j)).toBitVec.toNat = true :=
    fun h j hj => by
      have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
      simp only [Bool.and_eq_true] at this
      exact this.1.1
  have bph : ∀ {l : Label} {k : Nat} {blk : List (Directive × Nat)}, PhFact.blk l k blk none none ∈ mainTabH →
      Spike.Lib.X64Consumer.blkPh (okPcOf lo helloCells L.Λ) phH (fun _ => false) L.lab
        (L.lab l + Int64.ofNat k) 0 blk = true := fun hf =>
    Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
      (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (mainH_fact hΛ hf)
  have fchk : ∀ o, freeAtH ".Lscc_rt_main.chk" [o] = true →
      freeNH (L.lab ".Lscc_rt_main.chk" + Int64.ofNat o).toBitVec.toNat = true :=
    fun o h => freeAt_pcH hlab h (List.mem_singleton.mpr rfl)
  have hps : ∀ q ∈ ([(.rdi, -8, 4)] : List (Reg64 × Int64 × Nat)),
      Spike.Lib.offOk (-8 - (64 : Int64).toInt) 0 (-8 + q.2.1.toInt) = true := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- The prologue's head.
    have hph := bph (l := "scc_rt_main") (k := 0) (blk := xHead) (by simp [mainTabH])
    have hok := Spike.Lib.X64.Flow.xHead_ok (lo := -72) (hi := 0) (by decide) (Int.le_refl _)
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := "scc_rt_main") (k := 0) bHd
      (Spike.Lib.X64.Flow.ofNat_zero' _) hok hR (by omega) (by omega)
      (Spike.Lib.X64.Rt.blkW_postO hI (hp ▸ bHd) (Spike.Lib.X64.Flow.ofNat_zero' _) hok hR (by omega) (by omega)
        hR8 hl hh
        (fun _ _ hJ' => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r => (Spike.Lib.X64Consumer.noRet_false Spike.Lib.X64.Rt.MainU.xHead_noRet k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit hFO)
      (okB hph) (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.MainU.xHead_noRet
      (fun _ _ hJ' => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    rw [Spike.Lib.X64.Flow.xHead_run] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs', h4]; exact freeAt_labH hlab (by wsfreeH_dec))
  · -- The check's address.
    have hph := bph (l := ".Lscc_rt_main.chk") (k := 0) (blk := xLea 64 5) (by simp [mainTabH])
    have hok := Spike.Lib.X64.Flow.xLea_ok (lo := -72) (hi := 0) 32 5
    have he : L.lab ".Lscc_rt_main.chk" + Int64.ofNat 0 = (Spike.Lib.X64.Flow.xProN1 (L.lab "scc_rt_main") J).pc := by
      rw [Spike.Lib.X64.Flow.ofNat_zero', ← h4]; rfl
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".Lscc_rt_main.chk") (k := 0) bLea he
      hok hR (by omega) (by omega)
      (Spike.Lib.X64.Rt.blkW_postO hI (hp ▸ bLea) he hok hR (by omega) (by omega) hR8 hl hh
        (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r =>
          (Spike.Lib.X64Consumer.noRet_false (Spike.Lib.X64.Rt.MainU.xLea_noRet _ _) k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit hFO)
      (okB hph) (by wsfreeBH_dec) ?_ (by decide +kernel) (Spike.Lib.X64.Rt.MainU.xLea_noRet _ _)
      (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.xProN1] at hs'
    rw [Spike.Lib.X64.Flow.xLea_run _ _ _ (by decide)] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs', h4]; exact fchk 5 (by wsfreeH_dec))
  · -- The limit's load.
    have hf := Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
      (mainH_fact hΛ (f := .step ".Lscc_rt_main.chk" 5 9) (by simp [mainTabH]))
    have hpc : (Spike.Lib.X64.Flow.xProN2 (L.lab "scc_rt_main") 5 64 J).pc =
        L.lab ".Lscc_rt_main.chk" + Int64.ofNat 5 := by
      show L.lab "scc_rt_main" + 1 + 3 + _ = _; rw [h4]
    have ha : ∀ σ c, (Spike.Lib.X64.Flow.xProN2 (L.lab "scc_rt_main") 5 64 J).J σ c →
        σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = Spike.Lib.X64.Flow.Ret0.limA tp :=
      fun _ _ ⟨σ0, hJ', he⟩ => by
        rw [he, show (Spike.Lib.X64.Flow.xS2 64 σ0).regs.fsBase = σ0.regs.fsBase by
          simp [Spike.Lib.X64.Flow.xS2, Spike.Lib.X64.Flow.xS1, Spike.Lib.X64.Flow.hdRegs, Reg64s.set64],
          (hJ _ _ hJ').2]
        rfl
    exact nodeW_W0S_fsldH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".Lscc_rt_main.chk") (o := 5) (z := 9) bLd
      hpc.symm
      (Spike.Lib.X64.Rt.nodeW_fsld_postO (p := L.lab ".Lscc_rt_main.chk" + Int64.ofNat 5) hI
        (by rw [hp]; exact bLd) rfl hpc (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hf.1 hf.2
        ha hmr hun hR hR8 hl hh hsub hFO)
      ha hun hf.1 (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel)
      (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
  · -- The check.
    have hph := bph (l := ".Lscc_rt_main.chk") (k := 14) (blk := xCmp ".Lscc_rt_main.stk" 3 2)
      (by simp [mainTabH])
    have hok := Spike.Lib.X64.Flow.xCmp_ok (lo := -72) (hi := 0)
      (Spike.Lib.X64.Flow.xProN3 ms (L.lab "scc_rt_main") 5 9 64 8 J).o ".Lscc_rt_main.stk" 3 2
    have he : L.lab ".Lscc_rt_main.chk" + Int64.ofNat 14 =
        (Spike.Lib.X64.Flow.xProN3 ms (L.lab "scc_rt_main") 5 9 64 8 J).pc := by
      show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _
      rw [h4, ← Spike.Lib.X64.Flow.ofNat_add']
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".Lscc_rt_main.chk") (k := 14) bCmp he
      hok hR (by omega) (by omega)
      (Spike.Lib.X64.Rt.blkW_postO hI (hp ▸ bCmp) he hok hR (by omega) (by omega) hR8 hl hh
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r =>
          (Spike.Lib.X64Consumer.noRet_false (Spike.Lib.X64.Rt.MainU.xCmp_noRet _ _ _) k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit hFO)
      (okB hph) (by wsfreeBH_dec) ?_ (by decide +kernel) (Spike.Lib.X64.Rt.MainU.xCmp_noRet _ _ _)
      (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs', (Spike.Lib.X64.Flow.xCmp_run _ _ _ _ _ _ _).1]
    split
    · have := fchk 19 (by wsfreeH_dec)
      rw [esc] at this
      rw [show (Spike.Lib.X64.Flow.xProN3 ms (L.lab "scc_rt_main") 5 9 64 8 J).pc + Int64.ofNat 3 + Int64.ofNat 2 =
          L.lab "scc_rt_main" + Int64.ofNat 4 + Int64.ofNat 19 by
        show L.lab "scc_rt_main" + 1 + 3 + _ + _ + _ + _ = _; simp only [Int64.add_assoc]; rfl]
      exact this
    · exact freeAt_labH hlab (by wsfreeH_dec)
  · -- The frame's set-up.
    have hph := bph (l := ".Lscc_rt_main.chk") (k := 19) (blk := xFr 64 4 [(.rdi, -8, 4)]) (by simp [mainTabH])
    have hok := Spike.Lib.X64.Flow.xFr_ok (lo := -8 - (64 : Int64).toInt) (hi := 0) 32 4 _ hps
    have he : L.lab ".Lscc_rt_main.chk" + Int64.ofNat 19 =
        (Spike.Lib.X64.Flow.xProN4 ms (L.lab "scc_rt_main") 5 9 3 2 64 8 J).pc := by
      rw [esc]
      show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _ + _ + _
      simp only [Int64.add_assoc]; rfl
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".Lscc_rt_main.chk") (k := 19) bFr he
      hok hR (by show R.lo ≤ -8 - (64 : Int64).toInt; rw [show (64 : Int64).toInt = 64 from rfl]; omega) (by omega)
      (Spike.Lib.X64.Rt.blkW_postO hI (hp ▸ bFr) he hok hR
        (by show R.lo ≤ -8 - (64 : Int64).toInt; rw [show (64 : Int64).toInt = 64 from rfl]; omega) (by omega) hR8 hl hh
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r =>
          (Spike.Lib.X64Consumer.noRet_false (Spike.Lib.X64.Rt.MainU.xFr_noRet _ _ _) k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit hFO)
      (okB hph) (by wsfreeBH_dec) ?_ (by decide +kernel) (Spike.Lib.X64.Rt.MainU.xFr_noRet _ _ _)
      (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs']
    show freeNH (Spike.Lib.X64.arun L.lab (xFr 64 4 [(.rdi, -8, 4)])
      ⟨L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2,
        Spike.Lib.X64.Flow.oL 64, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.X64.Flow.xFr_run _ _ _ _ _ _).1]
    have := fchk 27 (by wsfreeH_dec)
    rw [esc] at this
    rw [show L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 +
        Int64.ofNat 4 + Int64.ofNat (Spike.Lib.X64.Flow.szSum [(.rdi, -8, 4)]) =
        L.lab "scc_rt_main" + Int64.ofNat 4 + Int64.ofNat 27 by simp only [Int64.add_assoc]; rfl]
    exact this
  · -- `.entry`'s call block.
    have hph := bph (l := ".Lscc_rt_main.entry") (k := 0) (blk := Spike.Lib.X64.Flow.Hello1.mB0)
      (by simp [mainTabH])
    have hnr : noRetBlk Spike.Lib.X64.Flow.Hello1.mB0 = true := by decide
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".Lscc_rt_main.entry") (k := 0) b0
      (Spike.Lib.X64.Flow.ofNat_zero' _) Spike.Lib.X64.Flow.Hello1.mB0_ok hR hRlo hhi
      (Spike.Lib.X64.Rt.blkW_postO hI (hp ▸ b0) (Spike.Lib.X64.Flow.ofNat_zero' _) Spike.Lib.X64.Flow.Hello1.mB0_ok hR
        hRlo hhi hR8 hl hh (fun _ _ ⟨⟨_, hJ', _⟩, _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r => (Spike.Lib.X64Consumer.noRet_false hnr k hk r).elim) (fun _ _ _ => rfl)
        hsub hfit hFO)
      (okB hph) (by wsfreeBH_dec) ?_ (by decide +kernel) hnr (fun _ _ ⟨⟨_, hJ', _⟩, _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Hello1.mN0] at hs'
    rw [Spike.Lib.X64.Flow.Hello1.mB0_run] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by wsfreeH_dec))

end Gen

end Spike.Lib.X64.HelloPh.MainWf

/-- info: 'Spike.Lib.X64.HelloPh.MainWf.mainFactsH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWf.mainFactsH

/-- info: 'Spike.Lib.X64.HelloPh.MainWf.mainH_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWf.mainH_fact

/-- info: 'Spike.Lib.X64.HelloPh.MainWf.nodeW_W0S_fsldH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWf.nodeW_W0S_fsldH

/-- info: 'Spike.Lib.X64.HelloPh.MainWf.mainPreWH_W0SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWf.mainPreWH_W0SH
