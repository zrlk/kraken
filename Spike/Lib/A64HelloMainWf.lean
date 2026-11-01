/-
**hello.w's `scc_rt_main` up to `bl wc_rodata` inside `W0`** (AArch64; hello twin of
`A64WakeMainWf`): the prologue (frame 80) and `.0_entry`'s call block of
`HelloM.MainPreW` (`pro`, `call`) at the start's level `HelloPh.StartWf.WSH` (`W0` at the
frames `[]` at `ownGH`). They are proved from each node's `SFacts` at `ownH`
(`Rt.blkW_postO`, `Rt.nodeW_ldr_postO` at `instOkHS`), moved to `ownGH` at free pcs
(`StartWf.blkW_W0SH`, `nodeW_W0S_ldrH`). hello's `scc_rt_main` differs from wake's: it calls
`wc_rodata` first (`Hello1.mB0`), so the glue goes on through `wc_rodata`'s segment
(`HelloM.MainPreW.rd`, `hello_main_pre_segW`) before `wc_main`.

- `mainTabH`, `mainH_fact`: `scc_rt_main`'s phase facts before `bl wc_rodata`.
- `nodeW_W0S_ldrH`: a load node of the start's level inside `W0`.
- `mainPreWH_W0SH`: `MainPreW.pro` and `.call` inside `WSH`.
-/
import Spike.Lib.A64HelloStartWf
import Spike.Lib.A64HelloMain

namespace Spike.Lib.A64.HelloPh.MainWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H freeAt_labH goodW_of_freeNH site_ne_of_freeNH
  cvH inCvH)
open Spike.Lib.A64.HelloPh.StartWf (WSH blkW_W0SH)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib (Arena FragS)

/-! ## The phase facts -/

/-- **`scc_rt_main`'s blocks before `bl wc_rodata`**: the prologue's three blocks
and its load, `.0_entry`'s call block. -/
def mainTabH : List PhFact :=
  [.blk ".L1_scc_rt_main.stack_check" 0 (Spike.Lib.A64.Flow.chkHead 80) none none,
   .step ".L1_scc_rt_main.stack_check" 2,
   .blk ".L1_scc_rt_main.stack_check" 3 (Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow") none none,
   .blk ".L1_scc_rt_main.stack_check" 5 (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)]) none none,
   .blk ".L1_scc_rt_main.0_entry" 0 Spike.Lib.A64.Flow.Hello1.mB0 none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem mainFactsH : mainTabH.all (factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `mainTabH` at `phH`.** -/
theorem mainH_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ mainTabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) phH f = true := by
  have := List.all_eq_true.mp mainFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-- `freeAt` of SccCode.helloProg, decided. -/
macro "hmfree_dec" : tactic =>
  `(tactic| (unfold freeAtH freeNH inCvH cvH; rw [← codeT_eq]; decide +kernel))

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **A load `ldr Xt, [Xn, #i]` of the start's level inside `W0`** at the
frames `[]`, as `StartWf.nodeW_W0S`: its `SFacts` at the first instance
(`hS`), its address `A` (`ha`) unmapped in private memory (`hun`), its pc
off the sites (`hokpc`), its pc and next pc free (`hfree`), its abort
phases' check (`hph`), its controls `c0` (`hJ`). -/
theorem nodeW_W0S_ldrH {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {A : BitVec 64}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (ha : ∀ σ c, n.J σ c → Spike.Lib.A64.Flow.rAddr σ.regs b i = A)
    (hun : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hfree : freeAtH l k 2 = true)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by
    have := freeAt_pcH hlab hfree (j := 0) (by decide); rwa [Spike.Lib.A64.Flow.ofNat4_zero, he] at this
  have hf4 : freeNH (n.pc + Int64.ofNat 4).toBitVec.toNat = true := by
    have := freeAt_pcH hlab hfree (j := 1) (by decide); rw [he] at this; exact this
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hex : ∀ s c, At L.exe L.endPc R F n s c →
      Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir t b i) 4 ∧
      isaLSE2.exec s = some (.load .plain false ⟨A, 8⟩ fun v =>
        .done (Kraken.Promising.Lower.A64.after s 4
          { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })) := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ'⟩
    have hc : Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir t b i) 4 :=
      (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = A := by rw [hA.regs]; exact ha σ c hJ'
    exact ⟨hc, Kraken.Promising.Lower.A64.exec_ldr_agrees hc ha' (hun _ hF)
      (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)⟩
  have hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
    intro s c hA
    refine ⟨_, _, (hex s c hA).1, ⟨fun imm h => ?_, (hex s c hA).2, fun s' hu => ?_⟩⟩
    · simp [Spike.Lib.A64.Flow.ldrDir] at h
    · obtain ⟨_, hu⟩ := hu
      simp only [Scc.Sem.TreeLeaf] at hu
      subst hu; rfl
  have htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x := fun x hx => by
    rw [hsite] at hx; cases hx; exact site_ne_of_freeNH hlab hf0
  have hag := Spike.Lib.A64.HelloPh.WcW.nodeAgreeWH (a := a) (n := n) (exe := L.exe) (endPc := L.endPc) (R := R)
    (F := F) hlab hsite hf0 hf4 hstep
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS) hag
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hP := Spike.Lib.A64.HelloWf.nodeW_phStH (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.A64.PhRec.μ L) he
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) htk hstep
  have hw := Spike.Lib.A64.WakeWf.nodeW_wf (ar := ar) (p := p) (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (fs := [])
    hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨⟨fun _ => hc0.1, hpl0 _, hc0.2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA =>
      ⟨Spike.Lib.A64ConsumerA.noWr_load (hex s c hA).2, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_abortWf_off fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf
      (by rw [hp, hlo]; exact hokpc) (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main` up to `bl wc_rodata` inside `W0`** (`HelloM.MainPreW`'s `pro` and
`call` at `WSH`) at every entry invariant `J` whose controls are `c0` and whose thread
pointer is `tp` (`hJ`): the prologue's blocks and load and `.0_entry`'s call
block from their `SFacts` at `ownW` (`Rt.blkW_postO`, `Rt.nodeW_ldr_postO`,
in a region holding the frame of `80`, 8-aligned, the words of `rS` off it
under `F`, `hFO`), the limit word `limA tp` mapped (`hmr`) and unmapped in
private memory (`hun`); their pcs free and their phases decided. -/
theorem mainPreWH_W0SH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {ms : Spike.Lib.MemSide isaLSE2}
    {J : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.TPIDR_EL0 = tp)
    (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub L.Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.StackOff rS R m)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.A64.Flow.ProW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
        ms (L.lab "scc_rt_main") 80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J ∧
      BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
        (Spike.Lib.A64.Flow.Hello1.mN0 L.lab J) Spike.Lib.A64.Flow.Hello1.mB0 := by
  have hI := instOkHS (a := a) (rS := rS) hp hlo hlab
  have hin := Spike.Lib.A64.Flow.HelloM.hello_mainPro
  simp only [Spike.Lib.A64.Flow.HelloM.hMainPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := hin
  have hin2 := Spike.Lib.A64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.A64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin2
  obtain ⟨⟨⟨b0, -⟩, -⟩, -⟩ := hin2
  have esc : L.lab ".L1_scc_rt_main.stack_check" = L.lab "scc_rt_main" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at esc
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have okB : ∀ {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {pc ra : Int64} {blk : List Directive},
      Spike.Lib.A64Consumer.blkPh okP phf d L.lab pc ra blk = true →
      ∀ j < blk.length, okP (pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun h j hj => by
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have bph : ∀ {l : Label} {k : Nat} {blk : List Directive}, PhFact.blk l k blk none none ∈ mainTabH →
      Spike.Lib.A64Consumer.blkPh (okPcOf lo SccCode.helloProg L.Λ) phH (fun _ => false) L.lab
        (L.lab l + Int64.ofNat (4 * k)) 0 blk = true := fun hf =>
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
      (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (mainH_fact hΛ hf)
  have f2 := freeAt_pc0H hlab (l := ".L1_scc_rt_main.stack_check") (k := 2) (by hmfree_dec)
  have f5 := freeAt_pc0H hlab (l := ".L1_scc_rt_main.stack_check") (k := 5) (by hmfree_dec)
  rw [Spike.Lib.A64.Rt.MainU.pc2, esc] at f2
  rw [Spike.Lib.A64.Rt.MainU.pc5, esc] at f5
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- The prologue's head.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 0)
      (blk := Spike.Lib.A64.Flow.chkHead 80) (by simp [mainTabH])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 0) = L.lab "scc_rt_main" := by
      rw [Spike.Lib.A64.Flow.ofNat4_zero, esc]
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 0) bHd he
      (Spike.Lib.A64.Flow.chkHead_ok (-80) 0 80) hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bHd) he (Spike.Lib.A64.Flow.chkHead_ok (-80) 0 80) hR hal hRlo hhi
        (fun _ _ hJ' => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false (Spike.Lib.A64.Rt.MainU.chkHead_noRet 80)
          k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO)
      (okB hph) (by hmfree_dec) ?_ (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkHead_noRet 80)
      (fun _ _ hJ' => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    rw [Spike.Lib.A64.Flow.chkHead_run] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact f2)
  · -- The limit's load.
    have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
      (mainH_fact hΛ (f := .step ".L1_scc_rt_main.stack_check" 2) (by simp [mainTabH]))
    have hpc : (Spike.Lib.A64.Flow.proN1 (L.lab "scc_rt_main") 80 J).pc =
        L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 2) := by
      show L.lab "scc_rt_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc]
    have ha : ∀ σ c, (Spike.Lib.A64.Flow.proN1 (L.lab "scc_rt_main") 80 J).J σ c →
        Spike.Lib.A64.Flow.rAddr σ.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp :=
      fun _ _ ⟨_, hJ', he⟩ => by
        rw [he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (hJ _ _ hJ').2
    exact nodeW_W0S_ldrH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 2) bLd
      hpc.symm
      (Spike.Lib.A64.Rt.nodeW_ldr_postO hI (by rw [hp]; exact bLd) rfl hpc
        (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hf.1 hf.2
        ha hmr hun hR hR8 hl hh hsub hFO)
      ha hun hf.1 (by hmfree_dec) (by decide +kernel) (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
  · -- The branch to the grow stub.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 3)
      (blk := Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow") (by simp [mainTabH])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 3) =
        (Spike.Lib.A64.Flow.proN2 ms (L.lab "scc_rt_main") 80 8 J).pc := by
      rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 3) bBr he
      (Spike.Lib.A64.Flow.chkBr_ok (-80) 0 80 _) hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bBr) he (Spike.Lib.A64.Flow.chkBr_ok (-80) 0 80 _) hR hal hRlo hhi
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false (Spike.Lib.A64.Rt.MainU.chkBr_noRet _)
          k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO)
      (okB hph) (by hmfree_dec) ?_ (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _)
      (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs']
    show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow")
      ⟨L.lab "scc_rt_main" + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 80, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.chkBr_run _ _ _ _ _).1]
    split
    · exact f5
    · exact freeAt_labH hlab (by hmfree_dec)
  · -- The frame's set-up.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 5)
      (blk := Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)]) (by simp [mainTabH])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 5) =
        (Spike.Lib.A64.Flow.proN3 ms (L.lab "scc_rt_main") 80 8 J).pc := by
      rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl
    have hok : Spike.Lib.A64.Flow.okBlk (-80) 0 (Spike.Lib.A64.Flow.oChk 80)
        (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)]) = true :=
      Spike.Lib.A64.Flow.frameSet_ok (lo := -80) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)
    have hnr : Spike.Lib.A64Consumer.noRetBlk (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)]) = true := by
      simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]
    have f10 := freeAt_pc0H hlab (l := ".L1_scc_rt_main.stack_check") (k := 10) (by hmfree_dec)
    rw [esc, show ∀ x : Int64, x + Int64.ofNat (4 * 10) = x + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * 1)
      from fun x => by simp only [Int64.add_assoc]; rfl] at f10
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 5) bFr he
      hok hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bFr) he hok hR hal hRlo hhi
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
        hl hh hsub hfit hFO)
      (okB hph) (by hmfree_dec) ?_ (by decide +kernel) hnr (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs']
    show freeNH (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.frameSet 80 [(.X0, 0)])
      ⟨L.lab "scc_rt_main" + 4 + 4 + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 80, _⟩).pc.toBitVec.toNat = true
    rw [Spike.Lib.A64.Flow.frameSet_run _ _ _ (by decide)]
    exact f10
  · -- `.0_entry`'s call block.
    have hph := bph (l := ".L1_scc_rt_main.0_entry") (k := 0)
      (blk := Spike.Lib.A64.Flow.Hello1.mB0) (by simp [mainTabH])
    have hnr : Spike.Lib.A64Consumer.noRetBlk Spike.Lib.A64.Flow.Hello1.mB0 = true := by decide
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.0_entry") (k := 0) b0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.Hello1.mB0_ok hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ b0) (Spike.Lib.A64.Flow.ofNat4_zero _)
        Spike.Lib.A64.Flow.Hello1.mB0_ok hR hal
        hRlo hhi (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
        hl hh hsub hfit hFO)
      (okB hph) (by hmfree_dec) ?_ (by decide +kernel) hnr (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.Hello1.mN0] at hs'
    rw [Spike.Lib.A64.Flow.Hello1.mB0_run] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by hmfree_dec))

end Gen

end Spike.Lib.A64.HelloPh.MainWf

/-- info: 'Spike.Lib.A64.HelloPh.MainWf.mainH_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWf.mainH_fact

/-- info: 'Spike.Lib.A64.HelloPh.MainWf.nodeW_W0S_ldrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWf.nodeW_W0S_ldrH

/-- info: 'Spike.Lib.A64.HelloPh.MainWf.mainPreWH_W0SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWf.mainPreWH_W0SH
