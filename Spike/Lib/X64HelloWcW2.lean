/-
**hello.w's `wc_main` own nodes inside the root's third level `RootWX.W2H` on x86-64** (the twin of
`Spike/Lib/A64HelloWcW2.lean`; wake's x86-64 version of the node lemmas is `Spike/Lib/X64WakeWcW1I.lean`):
`H1GAH.wcWf` at the root's level `W2Hg own L ar helloSrc Dt (ClH L) Ctx lbl lsize` at any owned words `own` (`W2H
L (ntA L.lab) …` at `ownGH L (ntA L.lab)`), at no frames and no outside moves.

Each node is `WcWfX.blkW_wfCX`/`nodeW_wfCX` (the tid store `HelloWf.nodeW_wfStH`) at its `SFactsSt2` at
`own` (a field of `WcMidWH`, e.g. `WcMidWG.wcMidW_wcGH`, `hst`) and its frames placed (a field
of `WcMainWH` at `PlacedSE`, `hpl`); the controls' facts are main's source's: `boxTermH` up to `.x25`'s `mfence`,
the published `boxPubCtlH c0 ty l` (at `p0Term`) past it (`ctlH`, by `HelloH1A.boxTH_run`).

- `ctlH`: main's source at the box or past its publication is not at a `ret`, its runs well formed.
- `mfence_cellH`: an `mfence` steps to `pc + 3`, writing nothing.
- `blkW_noKH`, `nodeW_noKH`: a block (a node) inside `W` at `K` is inside a weaker `W'` at no move.
- `htk_ofC`: a pc other than the take site's (`4200314`) is off it.
- `blkW_W2H`, `nodeW_fenceW2H`, `nodeW_fiW2H`: a covered `ret`-free block, an `mfence`, a flag-clobbering
  instruction inside `W2H`.
- `wcMainW_W2H`: `WcMainWH` inside `W2H` from `hst`, `hpl` and the tid word's two facts (`htid`: unmapped under
  `F`, `hoff56`: off the arena).
- `wcWf_W2H`: `H1GAH.wcWf`'s statement (at `ownGH L (ntA L.lab)`), `hst` by `WcMidWG.wcMidW_wcGH` at its word
  premises.

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.

## Unlike AArch64

- x86-64's `WcMainWH` has four fields (`bl`, `sp3`, `sp4`, `sp6`): there is no fence before the reserve's call
  (no `BoxTH`/`boxTH_run`/`boxTH_runWf` twins: `HelloH1A.BoxTH`, `boxTH_run` are reused), and `.x25`'s six nodes
  (`sp6AH`, the `mfence`, `cloneLdH`, two `xorl`s, `nrB`) run past the publication at `boxPubCtlH c0 ty l`, so the
  controls' facts are at `boxTermH` or `p0Term` (`ctlH`; A64: `boxTermH` and `SpawnSrcH`, `ctl_of_mid`). The
  source guard is `QBH` (A64: `SBH` with `QBH`).
- The fence is an `mfence` (`mfence_cellH`, `nodeW_fenceW2H`; A64's `dmb_cellH`, `nodeW_dmbW2H`); the two
  `xorl`s are flag-clobbering single instructions (`nodeW_fiW2H`, `WakeWf.fi_step`), new.
- Blocks sit at a byte offset of a label (`blockAtB`, `lab l + k`), their pcs `cellOff`; no `hal`; the frame is
  `[-136, 16]` (A64: `[-144, 0]`), so `R.lo ≤ -136`, `16 ≤ R.hi`, and `wcWf_W2H` asks `R.lo ≤ -320` and the base's
  8-alignment `hR8` (`WcMidWG.wcMidW_wcGH`'s).
- The node lemmas and `wcMainW_W2H` are generic in the owned words `own` (at `RootWX.W2Hg`; A64: at `ownGH`), so
  that a level whose owned words also carry the threads' own TCB words shares them.
-/
import Spike.Lib.X64HelloWcMidWG
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64HelloWcWfX
import Spike.Lib.X64HelloWfW
import Spike.Lib.X64HelloRootWX
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloH1ASrc
import Spike.Lib.X64HelloSrc

namespace Spike.Lib.X64.HelloPh.WcW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf codeT_eq)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2 WrAt)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At FI cellOff okBlk stDir)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.HelloWc (WcMainWH WcMidWH rNH wcN3H aNH tH resBH tcb2CallH sp4AH initCallH)
open Spike.Lib.X64.HelloPh.WcSp6 (wcN6H wcN6fH wcN6aH wcNdH wcN10H wcNrH sp6AH cloneLdH)
open Spike.Lib.X64.HelloPh.RootWX (W2H W2Hg)
open Spike.Lib.X64HelloHMid (QBH)
open Spike.Lib.X64HelloMainPreSrc (boxTermH p0Term pTerm spawnTermH boxPubCtlH)
open Spike.Lib.X64.HelloH1A (BoxTH boxTH_run)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64HelloSrc (helloSrc)
open Kraken.Promising.Lower.X64 (CellAt exec_mfence op64)

/-! ## Main's source at the box and past its publication -/

/-- **The box's control and the published one** (`p0Term`, `boxPubCtlH`'s) are not at a `ret` and their runs
are well formed: a frame run from either passes only `BoxTH`'s terms (`HelloH1A.boxTH_run`), none of which
loads, stores or allocates. -/
theorem ctlH {p : Prog} {c : Ctl} (ht : c.term = boxTermH ∨ c.term = p0Term) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  have hB : BoxTH c.term := ht.elim .inl fun h => .inr (.inl h)
  refine ⟨fun a e => by rcases ht with ht | ht <;> rw [ht] at e <;> simp [boxTermH, p0Term] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    obtain ⟨-, hb⟩ := boxTH_run hr rfl hB
    rcases hb with hb | hb | hb | hb <;>
      rcases hc with hc | ⟨b, hc⟩ <;> rw [hb] at hc <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at hc
  · intro c' fs' hr x a τ e hc
    obtain ⟨-, hb⟩ := boxTH_run hr rfl hB
    rcases hb with hb | hb | hb | hb <;> rw [hb] at hc <;> simp [boxTermH, p0Term, pTerm, spawnTermH] at hc

/-- An `mfence`'s cell steps to `pc + 3`, writing nothing. -/
theorem mfence_cellH (s : State) (hc : CellAt s (op64 .mfence) 3) :
    (∃ tree, isa.exec s = some tree ∧ ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 3) ∧
      ∀ L, ¬ WrAt s L := by
  refine ⟨⟨_, exec_mfence hc, fun s' hu => ?_⟩, ?_⟩
  · obtain ⟨_, hu⟩ := hu
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl
  · rintro L (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [exec_mfence hc] at h <;> cases h

section NoK

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W' : Spike.Lib.Frag isa} {K : State → State → Prop}

/-- A block inside `W` at `K` is inside a weaker `W'` at no move (wake's `CalWf.blkW_noK`). -/
theorem blkW_noKH {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hw : ∀ s c, W s c → W' s c) : BlkW W' (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => ⟨hw _ _ (h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, fun _ h => h⟩

/-- A node inside `W` at `K` is inside a weaker `W'` at no move (wake's `CalWf.nodeW_noK`). -/
theorem nodeW_noKH {n : ND} (h : NodeW W K exe endPc R F n) (hw : ∀ s c, W s c → W' s c) :
    NodeW W' (fun _ _ => False) exe endPc R F n := fun s c hA => ⟨hw _ _ (h s c hA).1, fun _ h => h⟩

end NoK

/-- The take site's pc at the canonical base, through `hsite`. -/
theorem htk_ofC {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {pc : Int64}
    (h : pc.toBitVec.toNat ≠ 4200314) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite, Spike.Lib.X64.HelloPh.WcSp4W.lab_siteH hlab, Spike.Lib.X64.HelloPh.WcSp4W.site_toNatH] at hx
  cases hx; exact h

/-! ## A block, a fence and a flag-clobbering instruction inside `W2H` -/

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa}
  {lbl : Lbl} {lsize : Lsize} {K : State → State → Prop} {R : Region} {F : MachineData → Prop}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at the owned words `own`, at no frames. -/
local notation "W2" => fun s c => W2Hg own L ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **A covered `ret`-free block of `wc_main` inside `W2H`** at no move (`WcWfX.blkW_wfCX`): its `SFactsSt2` at
`own` (`hst`, at any move), its pcs off the sites (`hokP`, at `okC`), its abort phases' check
(`hph`), its controls not at a `ret` with their runs well formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_W2H {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F
      n blk)
    (hokP : ∀ j < blk.length, Spike.Lib.X64.HelloPh.okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW W2 (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hW := Spike.Lib.X64.HelloPh.WcWfX.blkW_wfCX (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.X64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab hsite hb he hok hR
    hlo' hhi hst (fun j hj => by rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP j hj) hph hnr
    Spike.Lib.X64.HelloPh.ClH.cl (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact blkW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **An `mfence` of `wc_main` inside `W2H`** at no move (`WcWfX.nodeW_wfCX` at `mfence_cellH`): the fence at
`l + k`, its pc off the take site (`htk`) and `okC` (`hokP`), its next pc off the abort phases' (`hph`). -/
theorem nodeW_fenceW2H {n : ND} {l : Label} {k : Nat}
    (hb : blockAtB helloCells l k [(op64 .mfence, 3)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.X64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k 3 = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hc : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (op64 .mfence) 3 :=
    fun s c ⟨h1, h2, _, h4, _⟩ => Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he h1 h2 h4
  have hW := Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.X64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab he hst htk
    (by rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP) hph
    (fun s c hA => by
      obtain ⟨⟨tree, h1, h2⟩, -⟩ := mfence_cellH s (hc s c hA)
      exact ⟨_, tree, hc s c hA, (fun w w' h => by cases h), h1, h2⟩)
    Spike.Lib.X64.HelloPh.ClH.cl (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
    (Spike.Lib.X64.WakeWf.nodeW_noWrC fun s c hA => ⟨(mfence_cellH s (hc s c hA)).2, fun _ h => h⟩)
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **A flag-clobbering single instruction of `wc_main` inside `W2H`** at no move (`WcWfX.nodeW_wfCX` at
`WakeWf.fi_step`, writing nothing): at `l + k`, its pc off the take site (`htk`) and `okC` (`hokP`), its next pc
off the abort phases' (`hph`). -/
theorem nodeW_fiW2H {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.X64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hW := Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.X64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab he hst htk
    (by rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP) hph
    (Spike.Lib.X64.WakeWf.fi_step (R := R) (F := F) hI (hp ▸ hb) he)
    Spike.Lib.X64.HelloPh.ClH.cl (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
    (Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_fi hI (hp ▸ hb) he rfl))
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

end Gen

/-! ## `wc_main`'s own nodes inside `W2H` -/

section Main

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa}
  {lbl : Lbl} {lsize : Lsize} {R : Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa}
  {J1 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at the owned words `own`, at no frames. -/
local notation "W2" => fun s c => W2Hg own L ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c []

set_option hygiene false in
/-- The root's third level at the start's own words, at no frames. -/
local notation "W2c" => fun s c => W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

set_option maxHeartbeats 3200000 in
/-- **`wc_main`'s own nodes inside `W2H`** at no frames and no move (`H1GAH.wcWf`'s statement at the root's
level): every node's `SFactsSt2` at `own` (`hst`, at the move of any range `rK`), its frames
placed (`hpl`), and the tid word `tH + 56` unmapped under `F` (`htid`, `H1GAH.tid`'s last conjunct) and off the
arena (`hoff56`). -/
theorem wcMainW_W2H (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi) {rK : Scc.Sem.Range}
    (hst : WcMidWH (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s)
      (Spike.Lib.X64.PhRec.K L rK) L.exe L.endPc R F F ms J1 (QBH l b ws))
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (QBH l b ws))
    (htid : ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none)
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2 (fun _ _ => False) L.exe L.endPc R F F ms J1 (QBH l b ws) := by
  have e22 : (_root_.Executable.labels L.exe).label ".Lwc_main.x22" = Int64.ofNat 4203703 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e3 := Spike.Lib.X64.HelloPh.Tcb2CallW.lab_sp3H hlab (L := L)
  have e4 := Spike.Lib.X64.HelloPh.WcSp4W.lab_x24H hlab (L := L)
  have e6 := Spike.Lib.X64.HelloPh.WcSp4W.lab_x25H hlab (L := L)
  have hin := Spike.Lib.X64.HelloPh.WcSp4W.sp4InH
  have hbl : blockAtB helloCells ".Lwc_main.x22" 18 resBH = true := by decide +kernel
  have hb3 : blockAtB helloCells ".Lwc_main.x23" 0 tcb2CallH = true := by decide +kernel
  refine ⟨?_, fun c0 sl me cA fr hM => ?_, fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩,
    fun c0 ty l' sl me cA fr hM => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- the reserve's call
  · refine blkW_W2H hp hlo hΛ hlab hsite hbl rfl Spike.Lib.X64.Flow.HelloWc.resBH_ok hR (by omega) (by omega)
      hst.res.bl ?_ (by decide +kernel) (by decide)
      (fun σ c h => by obtain ⟨⟨_, _, _, hq⟩, _⟩ := h; exact ctlH (.inl hq.2.2.1)) hpl.bl
    intro j hj; dsimp only [rNH]; rw [e22]; revert j; decide +kernel
  -- `.x23`
  · obtain ⟨_, _, hq, -⟩ := hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hb3 (ofNat_zero' _)
      Spike.Lib.X64.Flow.HelloWc.tcb2CallH_ok hR (by omega) (by omega) (hst.sp3 c0 sl me cA fr hM).blk ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctlH (.inl hq.2.2.1))
      (hpl.sp3 c0 sl me cA fr hM)
    intro j hj; dsimp only [wcN3H]; rw [e3]; revert j; decide +kernel
  -- `.x24`'s block
  · obtain ⟨_, _, hq, -⟩ := hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.1 (ofNat_zero' _)
      Spike.Lib.X64.Flow.HelloWc.sp4AH_ok hR (by omega) (by omega) (hst.sp4 c0 sl me cA fr hM).n4 ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctlH (.inl hq.2.2.1))
      (hpl.sp4 c0 sl me cA fr hM).n4
    intro j hj; dsimp only [aNH]; rw [e4]; revert j; decide +kernel
  -- the tid store
  · obtain ⟨_, _, hq, -⟩ := hM.1
    have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
    have hpc : ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.HelloWc.x24L + 12).toBitVec.toNat =
        4203749 + 12 := by
      rw [e4]; rfl
    have hok : okPcOf lo helloCells L.Λ
        ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.HelloWc.x24L + 12).toBitVec.toNat = true := by
      rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ, hpc]; decide +kernel
    have hst4 := (hst.sp4 c0 sl me cA fr hM).n4s
    have hW := Spike.Lib.X64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
      (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.X64.HelloPh.ClH L) (lbl := lbl) hI
      (hp ▸ hin.2.1) rfl
      (fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (hst4 s c hA).1 (fun h => h.elim), (hst4 s c hA).2⟩)
      (htk_ofC hlab hsite (by
        show ((_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.HelloWc.x24L + 12).toBitVec.toNat ≠ _
        rw [hpc]; decide))
      (Spike.Lib.X64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok)
      (Spike.Lib.X64.HelloWf.siOffW_sound hlab (by decide +kernel)) Spike.Lib.X64.HelloPh.ClH.cl
      (fun σ c h => by
        rw [h.1]; exact ⟨fun _ => (ctlH (p := helloSrc) (.inl hq.2.2.1)).1, (ctlH (.inl hq.2.2.1)).2⟩)
      (hpl.sp4 c0 sl me cA fr hM).n4s
      (fun σ c m' h hm => by
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx h.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact htid m' hm)
      (fun σ c m' h _ => by
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx h.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact hoff56)
    exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩
  -- `scc_rt_thread_init`'s call block
  · obtain ⟨_, _, hq, -⟩ := hM.1
    refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.1 rfl
      Spike.Lib.X64.Flow.HelloWc.initCallH_ok hR (by omega) (by omega) (hst.sp4 c0 sl me cA fr hM).n5 ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctlH (.inl hq.2.2.1))
      (hpl.sp4 c0 sl me cA fr hM).n5
    intro j hj; dsimp only [aNH]; rw [e4]; revert j; decide +kernel
  -- `.x25`'s block
  · refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.2.1 (ofNat_zero' _)
      Spike.Lib.X64.HelloPh.WcSp6.sp6AH_ok hR (by omega) (by omega) (hst.sp6 c0 ty l' sl me cA fr hM).n6 ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctlH (.inl hM.1.2.1))
      (hpl.sp6 c0 ty l' sl me cA fr hM).n6
    intro j hj; dsimp only [wcN6H]; rw [e6]; revert j; decide +kernel
  -- the `mfence`
  · refine nodeW_fenceW2H hp hlo hΛ hlab hsite hin.2.2.2.2.1 rfl (hst.sp6 c0 ty l' sl me cA fr hM).n6f
      (htk_ofC hlab hsite ?_) ?_ (by decide +kernel) (fun σ c h => by rw [h.1]; exact ctlH (.inl hM.1.2.1))
      (hpl.sp6 c0 ty l' sl me cA fr hM).n6f
    · dsimp only [wcN6fH]; rw [e6]; decide
    · dsimp only [wcN6fH]; rw [e6]; decide +kernel
  -- the clone's loads, past the publication
  · refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.2.2.2.1 rfl
      Spike.Lib.X64.HelloPh.WcSp6.cloneLdH_ok hR (by omega) (by omega) (hst.sp6 c0 ty l' sl me cA fr hM).n6a ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1]; exact ctlH (.inr rfl))
      (hpl.sp6 c0 ty l' sl me cA fr hM).n6a
    intro j hj; dsimp only [wcN6aH]; rw [e6]; revert j; decide +kernel
  -- `xorl %edx, %edx`
  · refine nodeW_fiW2H hp hlo hΛ hlab hsite hin.2.2.2.2.2.2.1 rfl (hst.sp6 c0 ty l' sl me cA fr hM).nd
      (htk_ofC hlab hsite ?_) ?_ (by decide +kernel) (fun σ c h => by rw [h.1.1]; exact ctlH (.inr rfl))
      (hpl.sp6 c0 ty l' sl me cA fr hM).nd
    · dsimp only [wcNdH]; rw [e6]; decide
    · dsimp only [wcNdH]; rw [e6]; decide +kernel
  -- `xorl %r10d, %r10d`
  · refine nodeW_fiW2H hp hlo hΛ hlab hsite hin.2.2.2.2.2.2.2.1 rfl (hst.sp6 c0 ty l' sl me cA fr hM).n10
      (htk_ofC hlab hsite ?_) ?_ (by decide +kernel) (fun σ c h => by rw [h.1.1.1]; exact ctlH (.inr rfl))
      (hpl.sp6 c0 ty l' sl me cA fr hM).n10
    · dsimp only [wcN10H]; rw [e6]; decide
    · dsimp only [wcN10H]; rw [e6]; decide +kernel
  -- the `syscall`'s number
  · refine blkW_W2H hp hlo hΛ hlab hsite hin.2.2.2.2.2.2.2.2 rfl
      Spike.Lib.X64.HelloPh.WcSp6.nrBH_ok hR (by omega) (by omega) (hst.sp6 c0 ty l' sl me cA fr hM).nr ?_
      (by decide +kernel) (by decide) (fun σ c h => by rw [h.1.1.1]; exact ctlH (.inr rfl))
      (hpl.sp6 c0 ty l' sl me cA fr hM).nr
    intro j hj; dsimp only [wcNrH]; rw [e6]; revert j; decide +kernel

/-- **`H1GAH.wcWf` at the root's level** (`wcMainW_W2H`, its `hst` by `WcMidWG.wcMidW_wcGH`): `wc_main`'s own nodes
inside `W2H` from the frames placed (`hpl`), the tid word off the arena (`hoff56`), and `wcMidW_wcGH`'s word
premises (`hsepN`, `hmN`, `hunN`, `hb`, `hsep`, `hhdr`, `hmP`, `hmH`, `hunP`, `hunH`, `hband`, `htidW`; `htidW`'s
second conjunct is `H1GAH.tid`'s last). -/
theorem wcWf_W2H (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : Spike.Lib.X64.HelloPh.Tcb2CallW.BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hband : Spike.Lib.X64.HelloPh.WcSp4W.BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ own2aH L (ntA L.lab) 0)
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (QBH l b ws))
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2c (fun _ _ => False) L.exe L.endPc R F F ms J1 (QBH l b ws) :=
  wcMainW_W2H hp hlo hΛ hlab hsite hR (by omega) hhi
    (Spike.Lib.X64.HelloPh.WcMidWG.wcMidW_wcGH (Λ := L.Λ) hp hlo hΛ hlab hsite hR hR8 hRlo hhi ⟨0, 0⟩ hsepN hmN
      hunN hb hsep hhdr hmP hmH hunP hunH hband htidW)
    hpl htidW.2.1 hoff56

end Main

end Spike.Lib.X64.HelloPh.WcW2

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.ctlH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.ctlH

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.mfence_cellH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.mfence_cellH

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.blkW_noKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.blkW_noKH

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.nodeW_noKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.nodeW_noKH

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.htk_ofC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.htk_ofC

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.blkW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.blkW_W2H

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.nodeW_fenceW2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.nodeW_fenceW2H

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.nodeW_fiW2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.nodeW_fiW2H

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.wcMainW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.wcMainW_W2H

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.wcWf_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.wcWf_W2H
