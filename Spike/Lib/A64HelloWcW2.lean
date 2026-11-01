/-
**hello.w's `wc_main` own nodes inside the root's third level `RootWX.W2H`** (AArch64; rows hP-wcWf;
the twin of `Spike/Lib/A64WakeWcW1I.lean` at helloProg, frame 144): `H1GAH.wcWf` at the root's level
`W2H L (ntA L.lab) ar helloSrc Dt (ClH L) Ctx lbl lsize`, at no frames and no outside moves.

Each node is `WcWf.blkW_wfCH`/`nodeW_wfCH` (the tid store `HelloWf.nodeW_wfStH`) at its `SFactsSt2` at
`ownGH L (ntA L.lab)` (a field of `WcMidWH`, e.g. `WcMidWG.wcMidW_wcGH`, `hst`) and its frames placed (a field
of `WcMainWH` at `PlacedSE`, `hpl`); the controls' facts are main's source's: `boxTermH` at the fence (`BoxTH`),
`SpawnSrcH` past it (`HelloH1A.spawnSrcH_ctl`).

- `BoxTH`, `boxTH_run`, `boxTH_runWf`: main's source from the box to the `spawn` takes no frame step and reads no
  cell (wake's `boxT_run`, `boxT_runWf`).
- `dmb_cellH`: a fence steps to `pc + 4`, writing nothing.
- `blkW_W2H`, `nodeW_dmbW2H`: a covered `ret`-free block, a fence inside `W2H`.
- `wcMainW_W2H`: `WcMainWH` inside `W2H` from `hst`, `hpl` and the tid word's two facts (`htid`: unmapped under
  `F`, `hoff56`: off the arena).
- `wcWf_W2H`: `H1GAH.wcWf`'s statement, `hst` by `WcMidWG.wcMidW_wcGH` at its word premises.

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.
-/
import Spike.Lib.A64HelloWcMidWG
import Spike.Lib.A64HelloWcWf
import Spike.Lib.A64HelloWfW
import Spike.Lib.A64HelloRootWX
import Spike.Lib.A64HelloClH
import Spike.Lib.Hello1Runs

namespace Spike.Lib.A64.HelloPh.WcW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.HelloWc (WcMainWH WcMidWH FrMGH rNH wcN3H aNH tH resBH tcb2CallH sp4AH initCallH)
open Spike.Lib.A64.HelloPh.WcSp6 (wcN6H wcN6fH wcN6aH sp6AH cloneArgsH)
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H wcTabWH wcW_factH)
open Spike.Lib.A64.HelloPh.RootWX (W2H)
open Spike.Lib.HelloHMid (SBH QBH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH spawnTermH boxTermH p0Term pTerm)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.HelloSrc (helloSrc)

/-! ## Main's source from the box -/

section Box

/-- The four terms of main's source from the box to the spawn. -/
def BoxTH (t : Expr) : Prop := t = boxTermH ∨ t = p0Term ∨ t = pTerm ∨ t = spawnTermH

/-- Main's source runs from the box only through `BoxTH`, at no frame. -/
theorem boxTH_run {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') (ht : BoxTH q.1.term)
    (hf : q.2 = []) : BoxTH q'.1.term ∧ q'.2 = [] := by
  induction h with
  | refl => exact ⟨ht, hf⟩
  | step hs _ ih =>
    refine ih ?_ ?_
    all_goals cases hs with
    | loc hl =>
      first
      | exact hf
      | rcases ht with ht | ht | ht | ht
        · exact .inr (.inl (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp)))
        · exact .inr (.inr (.inl (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp))))
        · exact .inr (.inr (.inr (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp))))
        · have e := Spike.Lib.HelloH1A.frameRun_spawnH ht (.single (.loc hl (fs := [])))
          cases e; exact .inr (.inr (.inr ht))
    | call hc =>
      rcases ht with ht | ht | ht | ht <;> rw [ht] at hc <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at hc
    | ret hc => simp at hf

/-- **The box's control** is not at a `ret` and its runs are well formed. -/
theorem boxTH_runWf {p : Prog} {c : Ctl} (ht : c.term = boxTermH) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  refine ⟨fun a e => by rw [ht] at e; simp [boxTermH] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    have h := (boxTH_run hr (.inl ht) rfl).1
    rcases hc with hc | ⟨b, hc⟩ <;> rcases h with h | h | h | h <;> rw [hc] at h <;>
      simp [boxTermH, p0Term, pTerm, spawnTermH] at h
  · intro c' fs' hr x a τ e hc
    have h := (boxTH_run hr (.inl ht) rfl).1
    rcases h with h | h | h | h <;> rw [hc] at h <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at h

end Box

/-- A fence's cell steps to `pc + 4`, writing nothing. -/
theorem dmb_cellH {fk : FenceKind} (s : State)
    (hc : Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .DMB fk⟩) 4) :
    (∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) ∧
      ∀ L, ¬ Spike.Lib.A64ConsumerA.WrAt s L := by
  refine ⟨⟨_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩, ?_⟩
  · obtain ⟨_, hu⟩ := hu
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl
  · rintro L (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [Kraken.Promising.Lower.A64.exec_dmb hc] at h <;> cases h

section NoK

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W' : Spike.Lib.Frag isaLSE2} {K : State → State → Prop}

/-- A block inside `W` at `K` is inside a weaker `W'` at no move (wake's `CalWf.blkW_noK`). -/
theorem blkW_noKH {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk)
    (hw : ∀ s c, W s c → W' s c) : BlkW W' (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => ⟨hw _ _ (h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, fun _ h => h⟩

/-- A node inside `W` at `K` is inside a weaker `W'` at no move (wake's `CalWf.nodeW_noK`). -/
theorem nodeW_noKH {n : ND} (h : NodeW W K exe endPc R F n) (hw : ∀ s c, W s c → W' s c) :
    NodeW W' (fun _ _ => False) exe endPc R F n := fun s c hA => ⟨hw _ _ (h s c hA).1, fun _ h => h⟩

end NoK

/-- The take site's pc at the canonical base, through `hsite`. -/
theorem htk_ofC {L : RuntimeLayout} (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {pc : Int64}
    (h : pc.toBitVec.toNat ≠ 2165976) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite, Spike.Lib.A64.HelloPh.WcSp4W.lab_siteH hlab, Spike.Lib.A64.HelloPh.WcSp4W.site_toNatH] at hx
  cases hx; exact h

/-! ## A block and a fence inside `W2H` -/

section Gen

variable {L : RuntimeLayout} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {K : State → State → Prop} {R : Region} {F : MachineData → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at no frames. -/
local notation "W2" => fun s c => W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **A covered `ret`-free block of `wc_main` inside `W2H`** at no move (`WcWf.blkW_wfCH`): its `SFactsSt2` at
`ownGH L (ntA L.lab)` (`hst`, at any move), its pcs off the sites (`hokP`, at `okC`), its abort phases' check
(`hph`), its controls not at a `ret` with their runs well formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_W2H {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F
      n blk)
    (hokP : ∀ j < blk.length, Spike.Lib.A64.HelloPh.okC (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW W2 (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hW := Spike.Lib.A64.HelloPh.WcWf.blkW_wfCH (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.A64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab hsite hb he hok hR hal
    hlo' hhi hst (fun j hj => by rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact hokP j hj) hph hnr (fun _ h => h.2)
    (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact blkW_noKH hW fun _ _ h => ⟨rfl, h⟩

omit hsite in
/-- **A fence of `wc_main` inside `W2H`** at no move (`WcWf.nodeW_wfCH` at `dmb_cellH`): `dmb` at `l + 4 k`, its
pc off the take site (`htk`) and `okC` (`hokP`), its next pc off the abort phases' (`hph`). -/
theorem nodeW_dmbW2H {n : ND} {fk : FenceKind} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [.instr ⟨.W64, .DMB fk⟩] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.A64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hc : ∀ s c, At L.exe L.endPc R F n s c → Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .DMB fk⟩) 4 :=
    fun s c ⟨h1, h2, _, h4, _⟩ => Spike.Lib.A64.HelloPh.WcW.cell1H hp hb h1 h2 (by rw [h4, he])
  have hW := Spike.Lib.A64.HelloPh.WcWf.nodeW_wfCH (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.A64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab he hst htk
    (by rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact hokP) hph
    (fun s c hA => by
      obtain ⟨⟨tree, h1, h2⟩, -⟩ := dmb_cellH s (hc s c hA)
      refine ⟨_, tree, hc s c hA, fun imm h => ?_, h1, h2⟩
      cases h)
    (fun _ h => h.2) (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
    (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA => ⟨(dmb_cellH s (hc s c hA)).2, fun _ h => h⟩)
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

end Gen

/-! ## `wc_main`'s own nodes inside `W2H` -/

section Main

variable {L : RuntimeLayout} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {R : Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
  {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at no frames. -/
local notation "W2" => fun s c => W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx lbl lsize s c []

/-- The source at the clone's facts at a ghost of `MidG (SBH …)`. -/
theorem ctl_of_mid {c0 : Ctl} {cA : BitVec 64} (hM : MidG (SBH l b ws) c0 cA) :
    ∀ c, c = c0 → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [] := by
  obtain ⟨_, _, ⟨_, _, hS⟩, _⟩ := hM
  exact fun c e => e ▸ Spike.Lib.HelloH1A.spawnSrcH_ctl hS

include hp hlo hΛ hlab hsite

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s own nodes inside `W2H`** at no frames and no move (`H1GAH.wcWf`'s statement at the root's
level): every node's `SFactsSt2` at `ownGH L (ntA L.lab)` (`hst`, at the move of any range `rK`), its frames
placed (`hpl`), and the tid word `tH + 56` unmapped under `F` (`htid`, `H1GAH.tid`'s last conjunct) and off the
arena (`hoff56`). -/
theorem wcMainW_W2H (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {rK : Scc.Sem.Range}
    (hst : WcMidWH (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s)
      (Spike.Lib.A64.PhRec.K L rK) L.exe L.endPc R F F ms J1 (SBH l b ws) (QBH l b ws))
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (SBH l b ws) (QBH l b ws))
    (htid : ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none)
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2 (fun _ _ => False) L.exe L.endPc R F F ms J1 (SBH l b ws) (QBH l b ws) := by
  have e3 := Spike.Lib.A64.HelloPh.Tcb2CallW.lab_sp3H hlab (L := L)
  have e4 : (_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" = Int64.ofNat 2169716 :=
    Spike.Lib.A64.HelloPh.WcSp4W.lab_sp4H hlab
  have e6 : (_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" = Int64.ofNat 2169740 :=
    Spike.Lib.A64.HelloPh.WcSp4W.lab_sp6H hlab
  have hin := Spike.Lib.A64.HelloPh.WcSp4W.sp4InH
  have h3 := Spike.Lib.A64.Flow.HelloWc.hello_wcSp3InH
  simp only [Spike.Lib.A64.Flow.HelloWc.wcSp3InH, Bool.and_eq_true] at h3
  have hr := Spike.Lib.A64.Flow.HelloWc.hello_wcResInH
  simp only [Spike.Lib.A64.Flow.HelloWc.wcResInH, Bool.and_eq_true] at hr
  obtain ⟨⟨hbf, hbl⟩, -⟩ := hr
  rw [Spike.Lib.A64.Flow.WakeWc.pubF_eq] at hbf
  refine ⟨?_, ?_, fun c0 sl me cA fr hM => ?_, fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩,
    fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩⟩
  -- the fence
  · have hf : PhFact.step ".L22_wc_main.sp0" 4 ∈ wcTabWH := by decide
    have hok := (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_factH hΛ hf)).1
    rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ] at hok
    exact nodeW_dmbW2H hp hlo hΛ hlab hbf rfl hst.res.f
      (Spike.Lib.A64.HelloPh.WcWf.htk_of_freeNH hlab hsite (freeAt_pc0H hlab (by free_decH))) hok
      (by decide +kernel) (fun σ c ⟨_, _, _, hq⟩ => boxTH_runWf hq.2.2.1) hpl.f
  -- the reserve's call
  · have hf : PhFact.blk ".L22_wc_main.sp0" 5 resBH none none ∈ wcTabWH := by decide
    have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
      (fun _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (wcW_factH hΛ hf)
    refine blkW_W2H hp hlo hΛ hlab hsite hbl rfl Spike.Lib.A64.Flow.HelloWc.resBH_ok hR hal hRlo hhi hst.res.bl
      (fun j hj => ?_) (by decide +kernel) (by decide) (fun σ c ⟨_, _, ⟨_, _, hS⟩, _⟩ =>
        Spike.Lib.HelloH1A.spawnSrcH_ctl hS) hpl.bl
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact this.1.1
  -- `.sp3`
  · have hc := ctl_of_mid hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite h3.1.1.1.1.1 (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.HelloWc.tcb2CallH_ok hR hal hRlo hhi (hst.sp3 c0 sl me cA fr hM).blk ?_
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp3 c0 sl me cA fr hM)
    show ∀ j < tcb2CallH.length, Spike.Lib.A64.HelloPh.okC
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp3" + _).toBitVec.toNat = true
    rw [e3]; decide +kernel
  -- `.sp4`'s block
  · have hc := ctl_of_mid hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.1 (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.HelloWc.sp4AH_ok hR hal hRlo hhi (hst.sp4 c0 sl me cA fr hM).n4 ?_
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp4 c0 sl me cA fr hM).n4
    show ∀ j < sp4AH.length, Spike.Lib.A64.HelloPh.okC
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" + _).toBitVec.toNat = true
    rw [e4]; decide +kernel
  -- the tid store
  · have hc := ctl_of_mid hM.1
    have hI := Spike.Lib.A64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
    have hpc : ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat =
        2169716 + 4 * 3 := by
      rw [e4]; exact (Spike.Lib.A64.HelloPh.WcSp4W.sp4_factsH 3 (by decide)).1
    have hok : okPcOf lo SccCode.helloProg L.Λ
        ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat = true := by
      rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ, hpc]
      exact (Spike.Lib.A64.HelloPh.WcSp4W.sp4_factsH 3 (by decide)).2.2
    have hst4 := (hst.sp4 c0 sl me cA fr hM).n4s
    have hW := Spike.Lib.A64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
      (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.A64.HelloPh.ClH L) (lbl := lbl) hI
      (hp ▸ hin.2.1) rfl
      (fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst4 s c hA).1 (fun h => h.elim), (hst4 s c hA).2⟩)
      (htk_ofC hlab hsite (by
        show ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat ≠ _
        rw [hpc]; decide))
      (Spike.Lib.A64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok)
      (Spike.Lib.A64.HelloWf.siOffHC_sound hlab (by decide +kernel)) (fun _ h => h.2)
      (fun σ c h => ⟨fun _ => (hc c h.1).1, (hc c h.1).2⟩) (hpl.sp4 c0 sl me cA fr hM).n4s
      (fun σ c m' h hm => by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h.2.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact htid m' hm)
      (fun σ c m' h _ => by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h.2.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact hoff56)
    exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩
  -- `scc_rt_thread_init`'s call block
  · have hc := ctl_of_mid hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.1 rfl
      Spike.Lib.A64.Flow.HelloWc.initCallH_ok hR hal hRlo hhi (hst.sp4 c0 sl me cA fr hM).n5 ?_
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp4 c0 sl me cA fr hM).n5
    show ∀ j < initCallH.length, Spike.Lib.A64.HelloPh.okC
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp4" + _ + _).toBitVec.toNat = true
    rw [e4]; decide +kernel
  -- `.sp6`'s block
  · have hc := ctl_of_mid hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.2.1 (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.HelloPh.WcSp6.sp6AH_ok hR hal hRlo hhi (hst.sp6 c0 sl me cA fr hM).n6 ?_
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp6 c0 sl me cA fr hM).n6
    show ∀ j < sp6AH.length, Spike.Lib.A64.HelloPh.okC
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" + _).toBitVec.toNat = true
    rw [e6]; decide +kernel
  -- the fence before the clone
  · have hc := ctl_of_mid hM.1
    have hpc : ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" + Int64.ofNat (4 * 11)).toBitVec.toNat =
        2169740 + 4 * 11 := by
      rw [e6]; exact (Spike.Lib.A64.HelloPh.WcSp4W.sp6_factsH 11 (by decide)).1
    exact nodeW_dmbW2H hp hlo hΛ hlab hin.2.2.2.2.1 rfl (hst.sp6 c0 sl me cA fr hM).n6f
      (htk_ofC hlab hsite (by
        show ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" + Int64.ofNat (4 * 11)).toBitVec.toNat ≠ _
        rw [hpc]; decide))
      (by
        show Spike.Lib.A64.HelloPh.okC
          ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" + Int64.ofNat (4 * 11)).toBitVec.toNat = true
        rw [hpc]; exact Spike.Lib.A64.HelloPh.WcSp4W.sp6_okH 11 (by decide))
      (by decide +kernel) (fun _ _ h => hc _ h.1) (hpl.sp6 c0 sl me cA fr hM).n6f
  -- the clone's arguments
  · have hc := ctl_of_mid hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.2.2.2 rfl
      Spike.Lib.A64.HelloPh.WcSp6.cloneArgsH_ok hR hal hRlo hhi (hst.sp6 c0 sl me cA fr hM).n6a ?_
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp6 c0 sl me cA fr hM).n6a
    show ∀ j < cloneArgsH.length, Spike.Lib.A64.HelloPh.okC
      ((_root_.Executable.labels L.exe).label ".L22_wc_main.sp6" + _ + _).toBitVec.toNat = true
    rw [e6]; decide +kernel

/-- **`H1GAH.wcWf` at the root's level** (`wcMainW_W2H`, its `hst` by `WcMidWG.wcMidW_wcGH`): `wc_main`'s own nodes
inside `W2H` from the frames placed (`hpl`), the tid word off the arena (`hoff56`), and `wcMidW_wcGH`'s word
premises (`hsepN`, `hmN`, `hunN`, `hb`, `hsep`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`, `hband`, `htidW`; `htidW`'s
second conjunct is `H1GAH.tid`'s last). -/
theorem wcWf_W2H (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : Spike.Lib.A64.HelloPh.Tcb2CallW.BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hband : Spike.Lib.A64.HelloPh.WcSp4W.BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ own2aH L (ntA L.lab) 0)
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (SBH l b ws) (QBH l b ws))
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2 (fun _ _ => False) L.exe L.endPc R F F ms J1 (SBH l b ws) (QBH l b ws) :=
  wcMainW_W2H hp hlo hΛ hlab hsite hR hal (by omega) hhi
    (Spike.Lib.A64.HelloPh.WcMidWG.wcMidW_wcGH (Λ := L.Λ) hp hlo hΛ hlab hsite hR hal hRlo hhi ⟨0, 0⟩ hsepN hmN
      hunN hb hsep hhdr hmP hmH hunP hunH hband htidW)
    hpl htidW.2.1 hoff56

end Main

end Spike.Lib.A64.HelloPh.WcW2

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.boxTH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.boxTH_run

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.boxTH_runWf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.boxTH_runWf

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.dmb_cellH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.dmb_cellH

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.blkW_noKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.blkW_noKH

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.nodeW_noKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.nodeW_noKH

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.htk_ofC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.htk_ofC

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.blkW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.blkW_W2H

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.nodeW_dmbW2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.nodeW_dmbW2H

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.ctl_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.ctl_of_mid

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.wcMainW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.wcMainW_W2H

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.wcWf_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.wcWf_W2H
