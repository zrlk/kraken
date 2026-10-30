/-
**wake.w's `wc_main` before the spawn inside `Wf`** (AArch64): the generic node and block obligations inside `WakeWf.Wf`
at any frame list `fs`, at wake.w's global owned-words map `ownG`, from a
node's `SFactsSt2` at `ownG` (`Dt` free: the state's facts at `Dt = False`
move to any `Dt`, `SFactsSt2.mono_dt`), its pcs off the sites, its abort
phases' decided checks (`phOffW`, `siOffW`) and its controls' facts.
Generic in the layout `L`, the counter `a`, the move `K`, the arena, the
source, the clone path and the level: no layout constant, no placement.

- `frameRun_hold`, `RunWf.hold`, `PlacedSE.hold`: a control's frame runs,
  run obligations and placement read no hold (the counter's `holdCtr`
  controls of `wc_main`'s allocation keep `c0`'s).
- `blkW_wfC`: a covered `ret`-free block inside `Wf` (`WakeWf.blkW_wfQ` at
  `instOkW`).
- `nodeW_wfC`: a single instruction without an event stepping to `pc + 4`
  inside `Wf`, its writes' obligations given (`hwr`, `NoWrC`), e.g. a load
  (writing nothing) or a store (`AllocG.nodeW_wr_st`).
- `nodeW_wfC_si`: a silent single instruction inside `Wf`
  (`WakeWf.nodeW_wfQ` at `instOkW`).
- `htk_of_freeN`, `habt_of_okPcOf`: a free pc is off the take site, a pc
  `okPcOf` is off the abort sites.
-/
import Spike.Lib.A64WakeStartWf

namespace Spike.Lib.A64.WakePh.WcWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (Wf RunWf NoWrC)
open Spike.Lib.A64.WakePh.WcW (freeN site_ne_of_freeN)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS FrameRun FrameStep)

/-! ## Controls up to the hold -/

section Hold

variable {p : Prog} {c : Ctl} {fs : List TermRun.Frame} {h : Option (Nat × TermRun.Word)}

/-- **A frame run from a held control** is one from the control, or stays
at the held control (a frame step reads only the term and the
environment). -/
theorem frameRun_hold {q : Ctl × List TermRun.Frame} (hr : FrameRun p ({ c with hold := h }, fs) q) :
    FrameRun p (c, fs) q ∨ q = ({ c with hold := h }, fs) := by
  cases hr with
  | refl => exact .inr rfl
  | step hs hr' =>
    refine .inl (.step ?_ hr')
    cases hs with
    | loc hl => exact .loc ⟨hl.1, fun g mem pairs th hg ht he hσ => hl.2 g mem pairs th hg ht he hσ⟩
    | call ht hf hev => exact .call ht hf hev
    | ret ht hσ hev => exact .ret ht hσ hev

/-- **The run obligations read no hold.** -/
theorem RunWf.hold (hw : RunWf p c fs) : RunWf p { c with hold := h } fs where
  cell := fun c' fs' hr => by
    rcases frameRun_hold hr with hr | hq
    · exact hw.cell c' fs' hr
    · cases hq; exact hw.cell c fs (.refl _)
  zero := fun c' fs' hr => by
    rcases frameRun_hold hr with hr | hq
    · exact hw.zero c' fs' hr
    · cases hq; exact hw.zero c fs (.refl _)

/-- **The placement reads no hold.** -/
theorem PlacedSE.hold {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} :
    PlacedSE Λ lbl s { c with hold := h } fs ↔ PlacedSE Λ lbl s c fs :=
  Iff.rfl

end Hold

/-! ## Inside `Wf` -/

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

include hsite hlab in
/-- **A free pc is off the take site.** -/
theorem htk_of_freeN {pc : Int64} (hf : freeN pc.toBitVec.toNat = true) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf

include hp hlo in
/-- **A pc `okPcOf` is off the abort sites.** -/
theorem habt_of_okPcOf {pc : Int64} (hok : okPcOf lo wakeProg L.Λ pc.toBitVec.toNat = true) :
    ∀ k x, (Spike.Lib.A64.PhRec.μ L).abortAt k = some x → pc.toBitVec.toNat ≠ x := fun j _ hx =>
  Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hok) (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx

include hp hlo hlab hsite

/-- **A covered `ret`-free block inside `Wf`** at the frames `fs`, at
`ownG`: its `SFactsSt2` at `Dt = False` (`hst`, moved by `K`), its pcs off
the sites (`hokpc`), its abort phases' check (`hph`), its controls not
`main`'s `ret` at no frame with their runs well formed (`hJ`), its frames
placed (`hpl`). -/
theorem blkW_wfC {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length, okPcOf lo wakeProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  exact Spike.Lib.A64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := fs) hI (hp ▸ hb) he hok hR hal hlo' hhi hst'
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.WakeWf.phOffW_sound hlab hph)
    (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hnr j hj r hr).elim) hcl hJ hpl

omit hsite in
/-- **A single instruction without an event inside `Wf`** at the frames
`fs`, at `ownG`: its `SFactsSt2` at `Dt = False` (`hst`, moved by `K`), its
pc off the take site (`htk`, e.g. `htk_of_freeN`) and `okPcOf` (`hokpc`),
its next pc off both abort phases' pcs (`hph`), its step to `pc + 4`
(`hstep`, e.g. `WakeWf.si_step`, `WakeWf.st_step`), its controls' facts
(`hJ`), its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_wfC {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokpc : okPcOf lo wakeProg L.Λ n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hP := Spike.Lib.A64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.A64.PhRec.μ L)
    (exe := L.exe) (endPc := L.endPc) he (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) htk hstep
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  exact Spike.Lib.A64.WakeWf.nodeW_wf hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨(Spike.Lib.A64.WakeWf.nodeW_ofJ hJ s c hA).1.1, (hpl s c hA).1,
      (Spike.Lib.A64.WakeWf.nodeW_ofJ hJ s c hA).1.2⟩, fun _ h => h⟩) hwr
    (Spike.Lib.A64.WakeWf.nodeW_abortWf_off (habt_of_okPcOf hp hlo hokpc))

/-- **A silent single instruction inside `Wf`** at the frames `fs`, at
`ownG` (`nodeW_wfC` at `WakeWf.si_step`, writing nothing). -/
theorem nodeW_wfC_si {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokpc : okPcOf lo wakeProg L.Λ n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  exact nodeW_wfC hp hlo hlab he hst htk hokpc hph
    (Spike.Lib.A64.WakeWf.si_step (R := R) (F := F) hI (hp ▸ hb) he) hcl hJ hpl
    (Spike.Lib.A64.WakeWf.nodeW_noWrC (Spike.Lib.A64.AllocG.nodeW_noWr_si hI (hp ▸ hb) he rfl))

end Gen

/-! ## Axioms -/

/--
info: 'Spike.Lib.A64.WakePh.WcWf.RunWf.hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RunWf.hold

/--
info: 'Spike.Lib.A64.WakePh.WcWf.blkW_wfC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blkW_wfC

/--
info: 'Spike.Lib.A64.WakePh.WcWf.nodeW_wfC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms nodeW_wfC

/--
info: 'Spike.Lib.A64.WakePh.WcWf.nodeW_wfC_si' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms nodeW_wfC_si

end Spike.Lib.A64.WakePh.WcWf
