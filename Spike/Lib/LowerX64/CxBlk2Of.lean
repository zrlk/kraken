/-
**A context's body blocks inside `W2`** (x86-64): `CalleePre2`'s (and
`CalleePre2R`'s) `hW`, `hWp` at the world `W2` for every block of a
construct or of `main`'s many-word `ret` (`Kind2`) of a code predicate
followed by positions off the write abort (`CdCLE`), at a body node
(`bodyN2`) or a checked `+`'s pending store (`pendN2`), the node's term no
bare `ret` at no frames (the guard `fs = [] → ∀ a, t ≠ .ret a`).

- `blkW_abSt_k2`: a `Kind2` block of `CdCLE` keeps the write abort's phase
  (`blkW_abSt_posR` at `hret_kind2`): its fall-throughs by `CdCLE`, its
  `ret`'s return address and its labels' targets positions off the write
  abort (`hraP`, `hTg`);
- `blkW_w2K2`: a `Kind2` block of `CdC` inside `W2` given its abort phase,
  placement and controls (`BlkW.w2` at `blkW_sfacts_k2`, `ret`s allowed);
- `cxBlk2_ofW2`: `CxBlk2`'s two fields (`Spike/Test/X64Hello1HS.lean`)
  unfolded, at `W2` and the immediates `Λ.imms`.

Left to the consumer: the region's facts, the suspended frames placed
(`hfp`), `FrOk2` at the ghosts (`hG0F`), the return address and every label
a `Kind2` block jumps or calls to positions off the write abort (`hraP`,
`hTg`).
-/
import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.RetSFacts2
import Spike.Lib.LowerX64.UserAbR
import Spike.Lib.LowerX64.CdCLE
import Spike.Lib.LowerX64.NoSlotWr

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW ND okBlk cellOff FStable AI CodeAt classify arun)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)

section K2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}

/-- The pc after a cell of a `CdCLE` piece's part, not a `jmp` nor a
`ret`, is a position off the write abort: inside the part by
`posOff_of_subCdL`, at its end by `posOff_end_subCdLE`. -/
theorem posOff_fall_subCdLE {ra' pc : Int64} {blk : List (Directive × Nat)}
    (hcd : SubCd (CdCLE cells okPc ph lab ra') pc blk) {k : Nat} (hk : k < blk.length) {a : AI}
    (ha : classify blk[k].1 = some a) (hj : ∀ L, a ≠ .jmp L) (hr : a ≠ .ret) :
    PosOff cells lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) := by
  rw [show pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 = pc + Int64.ofNat (cellOff blk (k + 1)) by
    rw [Spike.Lib.X64.cellOff_succ hk, Int64.ofNat_add, Int64.add_assoc]]
  rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
  · exact posOff_of_subCdL (hcd.mono fun _ _ h => h.toCdCL) h1
  · have hk1 : k + 1 = blk.length := by omega
    have hne : blk ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [hk1]
    refine posOff_end_subCdLE hcd hne ?_
    have hlast : (blk.map Prod.fst).getLast? = some blk[k].1 := by
      rw [List.getLast?_eq_getElem?]
      simp only [List.length_map, List.getElem?_map]
      rw [show blk.length - 1 = k by omega, List.getElem?_eq_getElem hk]
      rfl
    unfold endJ
    rw [hlast]
    unfold isJR
    simp only [ha]
    cases a <;> simp_all

/-- **A `Kind2` block of `CdCLE` keeps the write abort's phase**
(`blkW_abSt_posR` at `hret_kind2`): at a node with the frame's offsets
whose controls have the saved pair (`hfj`), every fall-through a position
off the write abort (`posOff_fall_subCdLE`), the `ret`'s target the saved
`ra`, a position off the write abort (`hraP`), and every label a `jmp`,
`jcc` or `call` of the block goes to one (`hTg`). -/
theorem blkW_abSt_k2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {n : ND} (hno : n.o = oB fr) (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)}
    (hk : Kind2 fr blk) (hcd : SubCd (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) n.pc blk)
    (hraP : PosOff cells lab (Int64.ofBitVec ra))
    (hTg : ∀ k (hk : k < blk.length) L,
      (classify blk[k].1 = some (.jmp L) ∨ classify blk[k].1 = some (.call L) ∨
        ∃ cc, classify blk[k].1 = some (.jcc cc L)) → PosOff cells lab (lab L)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, post, ⟨⟨-, L0, j, off, -, hpc0, hb, hrun⟩, -⟩, hpc⟩ := hcd'
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ okBlk_kind2 hf h1 hk
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hc, ← hpc] at hph
  have hpc' : lab L0 + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) (blockAt_sub hb)
    rwa [hI.labOk, hpc'] at this
  refine blkW_abSt_posR hI hpr habt hcode hok hR hlo (by omega) hph (hret_kind2 hf h1 hno hfj hk) ?_
  intro σ c hJ k hkl a ha t ht
  refine .inl ?_
  have hfall := fun (hj : ∀ L, a ≠ .jmp L) (hr : a ≠ .ret) => posOff_fall_subCdLE hcd hkl ha hj hr
  cases a with
  | jmp L =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hTg k hkl L (.inl ha)
  | call L =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hTg k hkl L (.inr (.inl ha))
  | jcc cc L =>
    simp only [aiTgts, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hTg k hkl L (.inr (.inr ⟨cc, ha⟩))
    · exact hfall (fun _ h => nomatch h) (fun h => nomatch h)
  | ret =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hraP
  | ld _ _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun h => nomatch h)
  | st _ _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun h => nomatch h)
  | push _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun h => nomatch h)
  | pop _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun h => nomatch h)
  | reg _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun h => nomatch h)

variable {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab' : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A `Kind2` block of the code inside `W2`** at the frames `fs`
(`BlkW.w2` at `blkW_sfacts_k2`, as `blkW_w2BP` but `ret`s allowed): at a
node with the frame's offsets whose controls have the saved pair (`hfj`),
its abort phase (`hab`), placement (`hP`) and controls (`hJ`) given. -/
theorem blkW_w2K2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND} (hno : n.o = oB fr)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List (Directive × Nat)} (hk : Kind2 fr blk)
    (hcd : SubCd (CdC cells okPc ph lab (Int64.ofBitVec ra)) n.pc blk)
    (hab : BlkW (fun s _ => AbSt μ Ab' s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab' lbl lsize s c fs) K exe endPc R F n blk := by
  have hS := blkW_sfacts_k2 (lbl := lbl) hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hno hfj hk hcd
  have hok : okBlk (-(fr.size : Int)) 16 n.o blk = true := hno ▸ okBlk_kind2 hf h1 hk
  obtain ⟨pc0, pre, post, ⟨-, L0, j, off, hpc0, hb, -⟩, hpc⟩ := hcd
  have hpc' : lab L0 + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) (blockAt_sub hb)
    rwa [hI.labOk, hpc'] at this
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    blkW_noWr' hcode hok hR hlo (by omega)
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hW (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2 hp hS ?_ hJ
  exact Spike.Lib.X64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **A context's body blocks inside `W2`** (`CxBlk2`'s `hW`, `hWp`
unfolded, at `W2`, the write abort `Ab lab` and the immediates `Λ.imms`):
every `Kind2` block of a code predicate `Cd` inside `CdCLE` at the saved
`ra` (`hCd`), at a body node and at a checked `+`'s pending store
(`blkW_w2K2` at `blkW_abSt_k2`, the placement `blkW_placedS` /
`blkW_placedS_upd`, the slots inside the frame `rsOf_bounds`), the node's
term no bare `ret` at no frames (the guard), `FrOk2` from the ghost's
(`hG0F`) along the local run. -/
theorem cxBlk2_ofW2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hp : ProgNoS ZBad p) (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hFS : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs)
    {Cd : Int64 → List (Directive × Nat) → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCLE cells okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hraP : PosOff cells lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd Cd pc blk → Kind2 fr blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k].1 = some (.jmp L) ∨ classify blk[k].1 = some (.call L) ∨
        ∃ cc, classify blk[k].1 = some (.jcc cc L)) → PosOff cells lab (lab L)) :
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      (fs = [] → ∀ a, t ≠ .ret a) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs) blk) ∧
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      (fs = [] → ∀ a, t ≠ .ret a) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs k) blk) := by
  have hrs : ∀ r k, rsOf fr r = some k → R.Off k := fun r k hr => by
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    exact ⟨h2, by omega, by omega⟩
  refine ⟨fun c0 hg pc t s lits cs bufs blk hcd hk hg' => ?_,
    fun c0 hg pc t s lits cs bufs k blk hcd hk hb1 hg' => ?_⟩
  · have hcdE := hcd.mono hCd
    refine blkW_w2K2 (n := bodyN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs)
      hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp rfl (fun _ _ h => h.2.1) hk
      (hcdE.mono fun _ _ h => h.toCdC)
      (blkW_abSt_k2 (n := bodyN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs)
        hI hpr habt hf h1 hR hlo hhi rfl (fun _ _ h => h.2.1) hk hcdE hraP (hTg _ _ hcd hk))
      (blkW_placedS hFS slotRepAt_bodyN2 hrs hfp (noSlotWr_kind2 hk)) fun σ c h => ?_
    obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h
    exact ⟨fun h0 => noRet_of_run hr (by rw [hj.1]; exact hg' h0),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hg)⟩
  · have hcdE := hcd.mono hCd
    refine blkW_w2K2 (n := pendN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs k)
      hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp rfl (fun _ _ h => h.2.1) hk
      (hcdE.mono fun _ _ h => h.toCdC)
      (blkW_abSt_k2 (n := pendN2 p lbl lsize Λ.imms fr fp ra c0 pc t s lits cs bufs k)
        hI hpr habt hf h1 hR hlo hhi rfl (fun _ _ h => h.2.1) hk hcdE hraP (hTg _ _ hcd hk))
      (blkW_placedS_upd hFS hb1 slotRepAt_pendN2 hrs hfp) fun σ c h => ?_
    obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h
    exact ⟨fun h0 => noRet_of_run hr (by rw [hj.1]; exact hg' h0),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hg)⟩

end K2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_k2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_abSt_k2

/-- info: 'Spike.Lib.LowerX64.blkW_w2K2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_w2K2

/-- info: 'Spike.Lib.LowerX64.cxBlk2_ofW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxBlk2_ofW2
