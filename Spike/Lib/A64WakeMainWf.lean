/-
**`scc_rt_main` up to `bl wc_main` inside `W0`** (AArch64):
`WakeM.MainPreWW` at the start's level `StartWf.WS` (`W0` at the frames
`[]` at `ownG`). It is proved from the `SFacts` of each node at `ownW`
(`Rt.blkW_postO`, `Rt.nodeW_ldr_postO` at `instOkWS`), moved to `ownG` at
free pcs (`StartWf.blkW_W0S`, `nodeW_W0S_ldr`). Also `scc_rt_main`'s entry
facts that `WakeWc.wake_wc_entry_segJm` takes at `MainE`'s invariant.

- `mainTabW`, `mainW_fact`: `scc_rt_main`'s phase facts before the call.
- `nodeW_W0S_ldr`: a load node of the start's level inside `W0`.
- `mainPreWW_W0S`: the prologue and `.0_entry`'s call block inside `WS`.
- `limOk_mainE0`, `ctl_mainE0`: `hlim`/`hlimM` and `hq` at `mainE0`'s
  invariant.
-/
import Spike.Lib.A64WakeStartWf
import Spike.Lib.A64WakeMain
import Spike.Lib.A64WakeHtp

namespace Spike.Lib.A64.WakePh.MainWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf codeT codeT_eq factOk)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.WcW (freeN freeAt freeAt_pc freeAt_pc0 freeAt_lab goodW_of_freeN site_ne_of_freeN cv inCv)
open Spike.Lib.A64.WakePh.StartWf (WS blkW_W0S)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)

/-! ## The phase facts -/

/-- **`scc_rt_main`'s blocks before the call**: the prologue's three blocks
and its load, `.0_entry`'s call block. -/
def mainTabW : List PhFact :=
  [.blk ".L1_scc_rt_main.stack_check" 0 (Spike.Lib.A64.Flow.chkHead 48) none none,
   .step ".L1_scc_rt_main.stack_check" 2,
   .blk ".L1_scc_rt_main.stack_check" 3 (Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow") none none,
   .blk ".L1_scc_rt_main.stack_check" 5 (Spike.Lib.A64.Flow.frameSet 48 [(.X0, 0)]) none none,
   .blk ".L1_scc_rt_main.0_entry" 0 Spike.Lib.A64.Flow.WakeM.wB0 none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem mainFactsW : mainTabW.all (factOk (codeT lo wakeProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `mainTabW` at `phW`.** -/
theorem mainW_fact {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ mainTabW) : factOk (codeOf lo wakeProg) (okPcOf lo wakeProg Λ) phW f = true := by
  have := List.all_eq_true.mp mainFactsW f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at this
  exact this

/-- `freeAt` of wakeProg, decided. -/
macro "wmfree_dec" : tactic =>
  `(tactic| (unfold freeAt freeN inCv cv; rw [← codeT_eq]; decide +kernel))

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **A load `ldr Xt, [Xn, #i]` of the start's level inside `W0`** at the
frames `[]`, as `StartWf.nodeW_W0S`: its `SFacts` at the first instance
(`hS`), its address `A` (`ha`) unmapped in private memory (`hun`), its pc
off the sites (`hokpc`), its pc and next pc free (`hfree`), its abort
phases' check (`hph`), its controls `c0` (`hJ`). -/
theorem nodeW_W0S_ldr {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {A : BitVec 64}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (ha : ∀ σ c, n.J σ c → Spike.Lib.A64.Flow.rAddr σ.regs b i = A)
    (hun : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hfree : freeAt l k 2 = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeN n.pc.toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 0) (by decide); rwa [Spike.Lib.A64.Flow.ofNat4_zero, he] at this
  have hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 1) (by decide); rw [he] at this; exact this
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
    rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0
  have hag := Spike.Lib.A64.WakePh.WcW.nodeAgreeW (a := a) (n := n) (exe := L.exe) (endPc := L.endPc) (R := R)
    (F := F) hlab hsite hf0 hf4 hstep
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS) hag
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hP := Spike.Lib.A64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.A64.PhRec.μ L) he
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) htk hstep
  have hw := Spike.Lib.A64.WakeWf.nodeW_wf (ar := ar) (p := p) (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (fs := [])
    hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨⟨fun _ => hc0.1, hpl0 _, hc0.2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA =>
      ⟨Spike.Lib.A64ConsumerA.noWr_load (hex s c hA).2, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_abortWf_off fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf
      (by rw [hp, hlo]; exact hokpc) (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main` up to `bl wc_main` inside `W0`** (`WakeM.MainPreWW` at
`WS`) at every entry invariant `J` whose controls are `c0` and whose thread
pointer is `tp` (`hJ`): the prologue's blocks and load and `.0_entry`'s call
block from their `SFacts` at `ownW` (`Rt.blkW_postO`, `Rt.nodeW_ldr_postO`,
in a region holding the frame of `48`, 8-aligned, the words of `rS` off it
under `F`, `hFO`), the limit word `limA tp` mapped (`hmr`) and unmapped in
private memory (`hun`); their pcs free and their phases decided. -/
theorem mainPreWW_W0S (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) {ms : Spike.Lib.MemSide isaLSE2}
    {J : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.TPIDR_EL0 = tp)
    (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub L.Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.StackOff rS R m)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    Spike.Lib.A64.Flow.WakeM.MainPreWW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F ms J := by
  have hI := instOkWS (a := a) (rS := rS) hp hlo hlab
  have hin := Spike.Lib.A64.Flow.WakeM.wake_mainIn
  simp only [Spike.Lib.A64.Flow.WakeM.wakeMainIn, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩, b0⟩, -⟩ := hin
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
  have bph : ∀ {l : Label} {k : Nat} {blk : List Directive}, PhFact.blk l k blk none none ∈ mainTabW →
      Spike.Lib.A64Consumer.blkPh (okPcOf lo wakeProg L.Λ) phW (fun _ => false) L.lab
        (L.lab l + Int64.ofNat (4 * k)) 0 blk = true := fun hf =>
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
      (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (mainW_fact hΛ hf)
  have f2 := freeAt_pc0 hlab (l := ".L1_scc_rt_main.stack_check") (k := 2) (by wmfree_dec)
  have f5 := freeAt_pc0 hlab (l := ".L1_scc_rt_main.stack_check") (k := 5) (by wmfree_dec)
  rw [Spike.Lib.A64.Rt.MainU.pc2, esc] at f2
  rw [Spike.Lib.A64.Rt.MainU.pc5, esc] at f5
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- The prologue's head.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 0) (blk := Spike.Lib.A64.Flow.chkHead 48) (by simp [mainTabW])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 0) = L.lab "scc_rt_main" := by
      rw [Spike.Lib.A64.Flow.ofNat4_zero, esc]
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 0) bHd he
      (Spike.Lib.A64.Flow.chkHead_ok (-48) 0 48) hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bHd) he (Spike.Lib.A64.Flow.chkHead_ok (-48) 0 48) hR hal hRlo hhi
        (fun _ _ hJ' => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false (Spike.Lib.A64.Rt.MainU.chkHead_noRet 48)
          k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO)
      (okB hph) (by wmfree_dec) ?_ (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkHead_noRet 48)
      (fun _ _ hJ' => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    rw [Spike.Lib.A64.Flow.chkHead_run] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact f2)
  · -- The limit's load.
    have hf := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
      (mainW_fact hΛ (f := .step ".L1_scc_rt_main.stack_check" 2) (by simp [mainTabW]))
    have hpc : (Spike.Lib.A64.Flow.proN1 (L.lab "scc_rt_main") 48 J).pc =
        L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 2) := by
      show L.lab "scc_rt_main" + 4 + 4 = _; rw [Spike.Lib.A64.Rt.MainU.pc2, esc]
    have ha : ∀ σ c, (Spike.Lib.A64.Flow.proN1 (L.lab "scc_rt_main") 48 J).J σ c →
        Spike.Lib.A64.Flow.rAddr σ.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp :=
      fun _ _ ⟨_, hJ', he⟩ => by
        rw [he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (hJ _ _ hJ').2
    exact nodeW_W0S_ldr hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 2) bLd
      hpc.symm
      (Spike.Lib.A64.Rt.nodeW_ldr_postO hI (by rw [hp]; exact bLd) rfl hpc (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hf.1 hf.2
        ha hmr hun hR hR8 hl hh hsub hFO)
      ha hun hf.1 (by wmfree_dec) (by decide +kernel) (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
  · -- The branch to the grow stub.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 3) (blk := Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow") (by simp [mainTabW])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 3) =
        (Spike.Lib.A64.Flow.proN2 ms (L.lab "scc_rt_main") 48 8 J).pc := by
      rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 3) bBr he
      (Spike.Lib.A64.Flow.chkBr_ok (-48) 0 48 _) hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bBr) he (Spike.Lib.A64.Flow.chkBr_ok (-48) 0 48 _) hR hal hRlo hhi
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false (Spike.Lib.A64.Rt.MainU.chkBr_noRet _)
          k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO)
      (okB hph) (by wmfree_dec) ?_ (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _)
      (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeN hlab ?_
    unfold pcOf; rw [hs']
    show freeN (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.chkBr ".L1_scc_rt_main.stack_grow")
      ⟨L.lab "scc_rt_main" + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 48, σ⟩).pc.toBitVec.toNat = true
    rw [(Spike.Lib.A64.Flow.chkBr_run _ _ _ _ _).1]
    split
    · exact f5
    · exact freeAt_lab hlab (by wmfree_dec)
  · -- The frame's set-up.
    have hph := bph (l := ".L1_scc_rt_main.stack_check") (k := 5) (blk := Spike.Lib.A64.Flow.frameSet 48 [(.X0, 0)]) (by simp [mainTabW])
    have he : L.lab ".L1_scc_rt_main.stack_check" + Int64.ofNat (4 * 5) =
        (Spike.Lib.A64.Flow.proN3 ms (L.lab "scc_rt_main") 48 8 J).pc := by
      rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl
    have hok : Spike.Lib.A64.Flow.okBlk (-48) 0 (Spike.Lib.A64.Flow.oChk 48)
        (Spike.Lib.A64.Flow.frameSet 48 [(.X0, 0)]) = true :=
      Spike.Lib.A64.Flow.frameSet_ok (lo := -48) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)
    have hnr : Spike.Lib.A64Consumer.noRetBlk (Spike.Lib.A64.Flow.frameSet 48 [(.X0, 0)]) = true := by
      simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]
    have f10 := freeAt_pc0 hlab (l := ".L1_scc_rt_main.stack_check") (k := 10) (by wmfree_dec)
    rw [esc, show ∀ x : Int64, x + Int64.ofNat (4 * 10) = x + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * 1)
      from fun x => by simp only [Int64.add_assoc]; rfl] at f10
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.stack_check") (k := 5) bFr he
      hok hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ bFr) he hok hR hal hRlo hhi
        (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
        hl hh hsub hfit hFO)
      (okB hph) (by wmfree_dec) ?_ (by decide +kernel) hnr (fun _ _ ⟨_, _, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    refine goodW_of_freeN hlab ?_
    unfold pcOf; rw [hs']
    show freeN (Spike.Lib.A64.Flow.arun L.lab (Spike.Lib.A64.Flow.frameSet 48 [(.X0, 0)])
      ⟨L.lab "scc_rt_main" + 4 + 4 + 4 + 4 + 4, Spike.Lib.A64.Flow.oChk 48, _⟩).pc.toBitVec.toNat = true
    rw [Spike.Lib.A64.Flow.frameSet_run _ _ _ (by decide)]
    exact f10
  · -- `.0_entry`'s call block.
    have hph := bph (l := ".L1_scc_rt_main.0_entry") (k := 0) (blk := Spike.Lib.A64.Flow.WakeM.wB0) (by simp [mainTabW])
    have hnr : Spike.Lib.A64Consumer.noRetBlk Spike.Lib.A64.Flow.WakeM.wB0 = true := by decide
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := ".L1_scc_rt_main.0_entry") (k := 0) b0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.WakeM.wB0_ok hR hal hRlo hhi
      (Spike.Lib.A64.Rt.blkW_postO hI (hp ▸ b0) (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.WakeM.wB0_ok hR hal
        hRlo hhi (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1 ▸ hC0) hph
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
        hl hh hsub hfit hFO)
      (okB hph) (by wmfree_dec) ?_ (by decide +kernel) hnr (fun _ _ ⟨_, hJ', _⟩ => (hJ _ _ hJ').1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.WakeM.wN0] at hs'
    rw [Spike.Lib.A64.Flow.WakeM.wB0_run] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_lab hlab (by wmfree_dec))

end Gen

/-! ## `scc_rt_main`'s entry facts at `MainE`'s invariant -/

/-- **The limit word at `mainE0`'s invariant** (`WakeM.wake_main_pre_segW`'s
`hlimM` at `Z = 48`, `WakeWc.wake_wc_entry_segJm`'s `hlim` at `Z = 128`):
one `LimOk` of the TCB's limit word `limA tcb` bounded by `top - Z`. -/
theorem limOk_mainE0 {ms : Spike.Lib.MemSide isaLSE2} {F0 : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {lab : Label → Int64} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {Z : Int64}
    (h : Spike.Lib.A64.Flow.Ret0.LimOk ms F0 exe endPc (Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec tcb))
      (top - Z.toBitVec)) :
    ∀ σ c, (Spike.Lib.A64.Rt.mainE0 lab ⟨top, UInt64.ofBitVec tcb, c0⟩).J σ c →
      Spike.Lib.A64.Flow.Ret0.LimOk ms F0 exe endPc (Spike.Lib.A64.Flow.tcbA σ.regs 8)
        (σ.regs.SP.toBitVec - Z.toBitVec) := by
  rintro σ c ⟨⟨-, hsp, htp⟩, -⟩
  rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
  exact h

/-- **A fact of the control at `mainE0`'s invariant** (`hq`) from the
fact at its ghost control `c0`. -/
theorem ctl_mainE0 {lab : Label → Int64} {g : Spike.Lib.A64.Flow.Ret0.MainG} {P : Spike.Lib.Ctl → Prop}
    (h : P g.c0) : ∀ σ c, (Spike.Lib.A64.Rt.mainE0 lab g).J σ c → P c :=
  fun _ _ hJ => hJ.1.1 ▸ h

end Spike.Lib.A64.WakePh.MainWf

/-- info: 'Spike.Lib.A64.WakePh.MainWf.mainW_fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.MainWf.mainW_fact

/-- info: 'Spike.Lib.A64.WakePh.MainWf.nodeW_W0S_ldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.MainWf.nodeW_W0S_ldr

/-- info: 'Spike.Lib.A64.WakePh.MainWf.mainPreWW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.MainWf.mainPreWW_W0S

/-- info: 'Spike.Lib.A64.WakePh.MainWf.limOk_mainE0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.MainWf.limOk_mainE0
