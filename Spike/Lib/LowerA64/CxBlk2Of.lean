/-
**A context's body blocks inside `W2`** (AArch64; the twin of
`Spike/Lib/LowerX64/CxBlk2Of.lean`): `CalleePre2`'s (and `CalleePre2R`'s)
`hW`, `hWp` at the world `W2` for every block of a construct or of a
many-word `ret` (`Kind2`) of a code predicate followed by positions off the
write abort (`CdCLE`), at a body node (`bodyN2`) or a checked `+`'s pending
store (`pendN2`), the node's term no bare `ret` at no frames (the guard
`fs = [] → ∀ a, t ≠ .ret a`).

- `posOff_fall_subCdLE`: the pc after an instruction of a `CdCLE` piece's
  part, not a `b` nor a `ret`, is a position off the write abort;
- `blkW_abSt_k2`: a `Kind2` block of `CdCLE` keeps the write abort's phase
  (`blkW_abSt_posR` at `hret_kind2`): its fall-throughs by `CdCLE`, its
  `ret`'s return address and its labels' targets positions off the write
  abort (`hraP`, `hTg`);
- `blkW_w2K2`: a `Kind2` block of `CdC` inside `W2` given its abort phase,
  placement and controls (`BlkW.w2` at `blkW_sfacts_k2`, `ret`s allowed);
- `cxBlk2_ofW2`: `CxBlk2`'s two fields (`Spike/Test/A64Hello1HS.lean`)
  unfolded, at `W2` and the immediates `Λ.imms`.

Left to the consumer: the frame's bounds (`h1`, `h16`), the region's facts,
the suspended frames placed (`hfp`), `FrOk2` at the ghosts (`hG0F`), the
return address and every label a `Kind2` block branches or calls to
positions off the write abort (`hraP`, `hTg`).
-/
import Spike.Lib.LowerA64.Kind2SFacts
import Spike.Lib.LowerA64.UserAbR
import Spike.Lib.LowerA64.CdCLE
import Spike.Lib.LowerA64.NoSlotWr

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW ND okBlk FStable AI classify arun ofNat4_add ofNat4_succ)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Scc.Emit.A64 Scc.Lower.InvA64

section K2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {cx : FnCtx} {fp ra : BitVec 64}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The pc after an instruction of a `CdCLE` piece's part, not a `b`
nor a `ret`, is a position off the write abort**: inside the part by
`posOff_of_subCdL`, at its end by `posOff_end_subCdLE`. -/
theorem posOff_fall_subCdLE {ra' pc : Int64} {blk : List Directive}
    (hcd : SubCd (CdCLE prog okPc ph lab ra') pc blk) {k : Nat} (hk : k < blk.length) {a : AI}
    (ha : classify blk[k] = some a) (hj : ∀ L, a ≠ .b L) (hr : ∀ r, a ≠ .ret r) :
    PosOff prog lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) := by
  rw [show pc + Int64.ofNat (4 * k) + Int64.ofNat 4 = pc + Int64.ofNat (4 * (k + 1)) by
    rw [ofNat4_succ]; rfl]
  rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
  · exact posOff_of_subCdL (hcd.mono fun _ _ h => h.toCdCL) h1
  · have hk1 : k + 1 = blk.length := by omega
    have hne : blk ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [hk1]
    refine posOff_end_subCdLE hcd hne ?_
    have hlast : blk.getLast? = some blk[k] := by
      rw [List.getLast?_eq_getElem?, show blk.length - 1 = k by omega, List.getElem?_eq_getElem hk]
    unfold endJ
    rw [hlast]
    simp only [isJR, ha]
    cases a <;> simp_all

/-- **A `Kind2` block of `CdCLE` keeps the write abort's phase**
(`blkW_abSt_posR` at `hret_kind2`): at a node with the frame's offsets
whose controls have the saved pair (`hfj`), every fall-through a position
off the write abort (`posOff_fall_subCdLE`), the `ret`'s target the saved
`ra`, a position off the write abort (`hraP`), and every label a `b`,
`bl`, `b.cond`, `cbz` or `cbnz` of the block goes to one (`hTg`). -/
theorem blkW_abSt_k2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    {n : ND} (hno : n.o = oF cx) (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive}
    (hk : Kind2 cx blk) (hcd : SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) n.pc blk)
    (hraP : PosOff prog lab (Int64.ofBitVec ra))
    (hTg : ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff prog lab (lab L)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, suf, ⟨⟨-, L0, j, -, hpc0, hb, hrun⟩, -⟩, hpc⟩ := hcd'
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ okBlk_kind2 hf h1 h16 hk
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hpc] at hph
  have he : lab L0 + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, ofNat4_add]
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk (blockAt_sub hb) (q := n.pc)
    (by rw [hI.labOk]; exact he)
  refine blkW_abSt_posR hI hpr habt hcode hok hR hal hlo hhi hph (hret_kind2 hf h1 h16 hno hfj hk) ?_
  intro σ c hJ k hkl a ha t ht
  refine .inl ?_
  have hfall := fun (hj : ∀ L, a ≠ .b L) (hr : ∀ r, a ≠ .ret r) => posOff_fall_subCdLE hcd hkl ha hj hr
  cases a with
  | b L =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hTg k hkl L (.inl ha)
  | bl L =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hTg k hkl L (.inr (.inl ha))
  | bcond cc L =>
    simp only [aiTgts, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hTg k hkl L (.inr (.inr (.inl ⟨cc, ha⟩)))
    · exact hfall (fun _ h => nomatch h) (fun _ h => nomatch h)
  | cbz r L =>
    simp only [aiTgts, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hTg k hkl L (.inr (.inr (.inr (.inl ⟨r, ha⟩))))
    · exact hfall (fun _ h => nomatch h) (fun _ h => nomatch h)
  | cbnz r L =>
    simp only [aiTgts, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hTg k hkl L (.inr (.inr (.inr (.inr ⟨r, ha⟩))))
    · exact hfall (fun _ h => nomatch h) (fun _ h => nomatch h)
  | ret r =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hraP
  | ldr _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun _ h => nomatch h)
  | str _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun _ h => nomatch h)
  | reg _ _ =>
    simp only [aiTgts, List.mem_singleton] at ht
    exact ht ▸ hfall (fun _ h => nomatch h) (fun _ h => nomatch h)

variable {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab' : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A `Kind2` block of the code inside `W2`** at the frames `fs`
(`BlkW.w2` at `blkW_sfacts_k2`, as `blkW_w2BP` but `ret`s allowed): at a
node with the frame's offsets whose controls have the saved pair (`hfj`),
its abort phase (`hab`), placement (`hP`) and controls (`hJ`) given. -/
theorem blkW_w2K2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive} (hk : Kind2 cx blk)
    (hcd : SubCd (CdC prog okPc ph lab (Int64.ofBitVec ra)) n.pc blk)
    (hab : BlkW (fun s _ => AbSt μ Ab' s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab' lbl lsize s c fs) K exe endPc R F n blk := by
  have hS := blkW_sfacts_k2 (lbl := lbl) hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hno hfj hk hcd
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ okBlk_kind2 hf h1 h16 hk
  obtain ⟨pc0, pre, post, ⟨-, L0, j, hpc0, hb, -⟩, hpc⟩ := hcd
  have he : lab L0 + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk :=
    Spike.Lib.A64.Flow.code_of hI.lays hI.endOk (blockAt_sub hb) (by rw [hI.labOk]; exact he)
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    blkW_noWr' hcode hok hR hal hlo hhi
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hW (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2 hp hS ?_ hJ
  exact Spike.Lib.A64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **A context's body blocks inside `W2`** (`CxBlk2`'s `hW`, `hWp`
unfolded, at `W2`, the write abort `Ab lab` and the immediates `Λ.imms`):
every `Kind2` block of a code predicate `Cd` inside `CdCLE` at the saved
`ra` (`hCd`), at a body node and at a checked `+`'s pending store
(`blkW_w2K2` at `blkW_abSt_k2`, the placement `blkW_placedS` /
`blkW_placedS_upd`, the slots inside the frame `slotOff_bounds`), the
node's term no bare `ret` at no frames (the guard), `FrOk2` from the
ghost's (`hG0F`) along the local run. -/
theorem cxBlk2_ofW2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hp : ProgNoS ZBad p) (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hFS : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs)
    {Cd : Int64 → List Directive → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCLE prog okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hraP : PosOff prog lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd Cd pc blk → Kind2 cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff prog lab (lab L)) :
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      (fs = [] → ∀ a, t ≠ .ret a) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs) blk) ∧
    (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      (fs = [] → ∀ a, t ≠ .ret a) →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs k) blk) := by
  have hrs : ∀ r k, rsOf cx r = some k → R.Off k := fun r k hr => by
    unfold rsOf at hr
    split at hr
    · rename_i o ho
      cases hr
      obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
      exact ⟨by omega, by omega, by omega⟩
    · cases hr
  refine ⟨fun c0 hg pc t s lits cs bufs blk hcd hk hg' => ?_,
    fun c0 hg pc t s lits cs bufs k blk hcd hk hb1 hg' => ?_⟩
  · have hcdE := hcd.mono hCd
    refine blkW_w2K2 (n := bodyN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs)
      hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp rfl (fun _ _ h => h.2.1) hk
      (hcdE.mono fun _ _ h => h.toCdC)
      (blkW_abSt_k2 (n := bodyN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs)
        hI hpr habt hf h1 h16 hR hal hlo hhi rfl (fun _ _ h => h.2.1) hk hcdE hraP (hTg _ _ hcd hk))
      (blkW_placedS hFS slotRepAt_bodyN2 hrs hfp (noSlotWr_kind2 hk)) fun σ c h => ?_
    obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h
    exact ⟨fun h0 => noRet_of_run hr (by rw [hj.1]; exact hg' h0),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hg)⟩
  · have hcdE := hcd.mono hCd
    refine blkW_w2K2 (n := pendN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs k)
      hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp rfl (fun _ _ h => h.2.1) hk
      (hcdE.mono fun _ _ h => h.toCdC)
      (blkW_abSt_k2 (n := pendN2 p lbl lsize Λ.imms cx fp ra c0 pc t s lits cs bufs k)
        hI hpr habt hf h1 h16 hR hal hlo hhi rfl (fun _ _ h => h.2.1) hk hcdE hraP (hTg _ _ hcd hk))
      (blkW_placedS_upd hFS hb1 slotRepAt_pendN2 hrs hfp) fun σ c h => ?_
    obtain ⟨⟨L, sm, B, c', hr, hj, -⟩, -, hc0, -⟩ := h
    exact ⟨fun h0 => noRet_of_run hr (by rw [hj.1]; exact hg' h0),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hg)⟩

end K2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_k2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_abSt_k2

/-- info: 'Spike.Lib.LowerA64.blkW_w2K2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_w2K2

/-- info: 'Spike.Lib.LowerA64.cxBlk2_ofW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxBlk2_ofW2
