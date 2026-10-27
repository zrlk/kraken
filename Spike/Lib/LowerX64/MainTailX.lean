/-
**`main`'s held return tail, end to end** (x86-64): `main` ending in a call
continuing with `ret b` (`b` a literal or the call's result), the source
held at the callee's `ret`.

- `mainTailX_segC`: after a plain call, `main`'s `ret b` block at the held
  pair (`heldRN`) is one segment to `ExitC2SLF`, its states inside `W2` at
  the held frames (`retHeld_hW`; `SFacts` by `blkW_sfacts_ret2`, the write
  abort's phase by `retHeld_hab`, `Ret0` from the frame's result cell, `hx`,
  e.g. `hx_held`). The twin of `mainTailX_segP`
  (`Spike/Lib/LowerX64/MainTailP.lean`, after an output call).
- `held_segXU`: `held_segX` at `PrintCallCH`'s held pair with its term
  `ret ()`, to `heldRNU`;
- `heldTailCX_main`: `HeldTailCX`'s instance at `main`'s code (`CdCL`), the
  call's arm by `mainTailX_segC` (`hx_held`), the output call's by
  `mainTailX_segP`.
-/
import Spike.Lib.LowerX64.MainTailP
import Spike.Lib.LowerX64.HeldRes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_call_inv walk2_tail_call walk2_tail_print lowerC2_ret_inv
  lowerC2_fv)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : List TermRun.Frame → MemSide isa} {W : FragS isa}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`main`'s return tail after a plain call is one segment to
`ExitC2SLF`** (`ret_edgeSL` lifted to `heldRN`, the source at the callee's
`ret`): the block's states inside `W2` at the held frames (`retHeld_hW`;
`SFacts` by `blkW_sfacts_ret2`, the write abort's phase by `retHeld_hab`,
`Ret0` from the frame's result cell by `retSlot_bodyN2` at `hx`). The
premises are `mainTailX_segP`'s and the held frame's result in a region
cell (`hx`, e.g. `hx_held`). -/
theorem mainTailX_segC (hp : ProgNoS ZBad p)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL cells okPc ph lab (Int64.ofBitVec ra)) pc ((retDirs lw).zip zs))
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {s : Spike.Lib.Form.SEnv} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {fs : List TermRun.Frame} {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rsOf fr r = some k ∧ R.Off k)
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isa} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRN p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp
        tp))).at fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hl hn hz (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  have hok := he.2.1
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc ((retDirs lw).zip zs) :=
    SubCd.cdOf (fun pc' blk h => by
      have h' := CdCL.toCdC h
      rw [← hI.labOk] at h'
      exact cdOf_cdC hI.lays hI.endOk pc' blk h') hcd
  let n := heldRN p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp tp)
  have hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot := fun _ _ ⟨_, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj
  have hS := blkW_sfacts_ret2 (lbl := lbl) (n := n) hI hf h1 hR hR8 hlo hhi hl8 hh8 hsub hfit hFO rfl hfj hl hn
    hz (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := retHeld_hab (F := F) (n := n) hI hpr habt hl hz hcd hok hR hlo hhi
    (fun _ _ ⟨_, _, _, ⟨hJ, _⟩⟩ => retDirs_pc_bodyN2 hf h1 hl hn hz lab hJ) hpos
  have hW := retHeld_hW (Λ := Λ) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize)
    (n := n) (fs := fs) hp hl
    hcode hok hR hlo hhi hS (fun _ _ h => h.1) (fun _ _ ⟨hH, _, hr', hJ, _⟩ => retSlot_bodyN2 hx hH hr' hJ) hab
  exact (SegWS.liftS fs (((he.heldRN fs).seg hF hR hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀).mono_post
    fun _ _ _ ⟨h, hfs⟩ => hfs ▸ exitC2SLF_of_heldRN hr h

/-- **From a held pair at `ret ()` to the exits**: `held_segX` at
`PrintCallCH`'s post (`HeldC` with the term `ret ()`), the source at
`heldRNU` of the node at `ret b` at the frame. -/
theorem held_segXU {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat} {ty : Ty} {Ab : FragS isa} {x : String} {b : At} {c0 : Ctl}
    {pc' : Int64} {env' : Scc.Lower.Env}
    (hbx : (∃ k, b = .lit k) ∨ b = .var x)
    (hseg : ∀ (f : TermRun.Frame) (c0' : Ctl), FrameRunM p (c0, []) (c0', []) → f.x = x → f.body = .ret b →
      SegWS W K p lbl ms
        ((At exe endPc R F (heldRNU p [f] ((bodyN2 p lbl lsize i fr fp ra c0' pc' (.ret b) (ofEnv2 env') lits cs
          bufs).withTp tp))).at [f])
        (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab)) :
    SegWS W K p lbl ms
      (fun s c fs' => HeldC p (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 [] (fun _ _ _ => False) pc' (.ret b)
        env' lits cs bufs) [] x (.ret b) s c fs' ∧ c.term = .ret .unit)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  refine (SegWS.exists_pre (P := fun g : {q : TermRun.Frame × Ctl //
      FrameRunM p (c0, []) (q.2, []) ∧ q.1.x = x ∧ q.1.body = .ret b} =>
      (At exe endPc R F (heldRNU p [g.1.1] ((bodyN2 p lbl lsize i fr fp ra g.1.2 pc' (.ret b) (ofEnv2 env') lits cs
        bufs).withTp tp))).at [g.1.1])
    fun g => hseg g.1.1 g.1.2 g.2.1 g.2.2.1 g.2.2.2).mono_pre ?_
  rintro s c fs' ⟨⟨a, f, cR, hc, rfl, hfx, hfb, hst, hQ⟩, hu⟩
  rcases hQ with ⟨-, c0', hrun, he, hn, hd, hpc, σ, hA, hFm, hJ⟩ | hQ
  · have hσ : f.σs = [] := by
      cases hst with
      | ret _ hσ _ => exact hσ
    exact ⟨⟨(f, c0'), hrun, hfx, hfb⟩, ⟨he, hn, hd, hpc, σ, hA, hFm, by rw [hu]; rfl,
      heldTail_of_frame hc hσ hfx hfb hbx, cR, .single hst, hJ⟩, rfl⟩
  · exact hQ.elim

/-- **`main`'s held return tail to `ExitC2SLF` at `main`'s code**
(`HeldTailCX`'s instance; `heldTailCX_of` with the tail's segments
discharged): the call's segment held at the callee's `ret` (`CallC2H`,
`PrintCallCH`), then `main`'s `ret b` block at the held pair, after a plain
call by `mainTailX_segC` (the result's cell by `hx_held`), after an output
call by `mainTailX_segP` (`held_segXU`). `main`'s blocks are code at its
return address `ra` (`hCdL`), `ra` off the write abort (`hpos`), `W` from
`W2` (`hW₀`). -/
theorem heldTailCX_main (hp : ProgNoS ZBad p)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCdL : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64} {ty : Ty}
    (hcallH : CallC2H p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab (RetLk ty))
    (hprintH : PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab)
    (hW₀ : ∀ st c fs, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs →
      W st c fs) :
    HeldTailCX p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T (fun _ => True) (RetLk ty)
      (fun c0 => ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  intro c0 pc kk env n x g is a ts b lits cs bufs l k r hG hr hfr hcode hbl hWk hL hC hX hbx
  have hh0 := walk2_head hWk
  have hL0 := (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).1
  have hhi0 : (0 : Int) ≤ R.hi := by omega
  rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
      | ⟨xe, dg, t, bo, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
  · obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append _ [_] kk pc).1 hcode
    have hW' := walk2_tail_call hfrm hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    rcases hrest with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
    rw [hl] at hz hc
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    refine (SegWS.seq_left (hcallH c0 pc pc' kk kk' env n x g is a ts (.ret b) t w lits cs bufs hG hh0.2.1 hfr hL0
        hh0.2.2.2.1 hh0.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi
        (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1 hh.2.2.2.2.2
        ⟨l, k, _, hr, hcode, hbl, fun q hq =>
          ⟨(hWk q hq).1, (hWk q hq).2.1, (hWk q hq).2.2.2.1, (hWk q hq).2.2.2.2.1, (hWk q hq).2.2.2.2.2⟩, hL, hC,
          hX⟩)
      (held_segX hbx fun f c0' hrun hfx hfb => ?_)).mono_post fun s c fs' h => h.elim id .inr
    exact mainTailX_segC hp hI hpr habt hf h1 hF hR hR8 hlo hhi hl8 hh8 hsub hfit hFO hlw hn hz
      (SubCd.whole (hCdL _ _ hc)) hpos hsa hpl (hlb.1.1 b (by simp [headAtoms]))
      (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms])) (hlb.2.2 b rfl) hrun
      (hx_held hf hi hlo hhi0 fun f' h => by cases h; exact hfx) fun st c => hW₀ st c _
  · obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append _ _ kk pc).1 hcode
    have hW' := walk2_tail_print hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    rcases hrest with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
    rw [hl] at hz hc
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    refine (SegWS.seq_left (hprintH c0 pc pc' kk kk' env n x g is a ts (.ret b) xe dg t bo o m cw lits cs bufs hG
        hh0.2.1 hfr hL0 hh0.2.2.2.1 hh0.2.2.2.2.1 hC
        (by
          rw [← argShape_of_find hdg]
          exact (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).2.1 x g is a ts _ rfl)
        hx hdg hrt ha hi (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1
        hh.2.2.2.2.2)
      (held_segXU hbx fun f c0' hrun hfx hfb => ?_)).mono_post fun s c fs' h => h.elim id .inr
    exact mainTailX_segP hp hI hpr habt hf h1 hF hR hR8 hlo hhi hl8 hh8 hsub hfit hFO hlw hn hz
      (SubCd.whole (hCdL _ _ hc)) hpos hsa hpl (hlb.1.1 b (by simp [headAtoms]))
      (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms])) (hlb.2.2 b rfl) hrun fun st c => hW₀ st c _

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.mainTailX_segC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainTailX_segC

/-- info: 'Spike.Lib.LowerX64.held_segXU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.held_segXU

/-- info: 'Spike.Lib.LowerX64.heldTailCX_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.heldTailCX_main
