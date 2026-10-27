/-
**Each `Accepted2` code block's pieces followed by a position off the write
abort** (AArch64): `Spike/Lib/LowerA64/FnCodeLB.lean`'s `CodeC2` and
`BlocksCodeC2` at `CdCL` and `BlC2L` give them at `CdCLE`
(`Spike/Lib/LowerA64/CdCLE.lean`). A piece of an instruction is followed by
the rest of the block's code, which starts with a nonempty piece (a
terminator's is never empty) or a call's `bl` (at a position off the write
abort by `BlC2L`); a terminator's piece ends with a `b` or a `ret`.

- `term2_endJ`: a `TermC2` terminator's code ends with a `b` or a `ret`.
- `cdCLE_of`: a piece at `CdCL` followed by a position off the write abort
  is at `CdCLE`, and starts at one.
- `codeC2_cdCLE`: `CodeC2` at `CdCL` gives it at `CdCLE`, its pc a position
  off the write abort, every call's pc one (`hBl`).
- `blocksCodeC2_cdCLE`: the same for `BlocksCodeC2`.
- `fnCodeC2LE_ofPlaceOK`: `fnCodeC2LB_ofPlaceOK` at `CdCLE`.
-/
import Spike.Lib.LowerA64.FnCodeLB
import Spike.Lib.LowerA64.CdCLE

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.A64.Flow (classify ofNat4_add ofNat4_succ ofNat4_zero)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (blockAt labelGap isIns)
open Scc.Cert.Code1A64 (instsItems segIn blockAt_of_segIn segIn_label labelGap_of_segIn blocksOk ctxOf
  blocksOk_block)
open Scc.Cert.Ph1A64 (runsAux runPhB blkPh_of_runPhB runsAux_label blocksPh blocksPh_blockPh)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.LowerShape (InstC2 TermC2 func2 paramsR BlockC2)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2 lowerAll_accepted2_a64)
open Spike.Lib.A64.AllocG (abLabs)

/-! ## A terminator's last instruction -/

/-- **A `TermC2` terminator's code ends with a `b` or a `ret`.** -/
theorem term2_endJ {cx : FnCtx} {k : Nat} {t : Scc.IR.Term} (ht : TermC2 t) {c2 : List Item}
    (h : cx.term k t = .ok c2) : endJ (directives c2) = true := by
  cases ht with
  | ret ws =>
    obtain ⟨-, ls, -, rfl⟩ := term_retN_inv h
    rw [directives_append]
    exact endJ_snoc _ _ ▸ rfl
  | br p q l l' =>
    obtain ⟨la, lb, T, Fl, -, -, -, -, hd⟩ := term_br_inv h
    rw [hd]
    exact endJ_snoc _ _ ▸ rfl

/-! ## The code at `CdCLE` -/

section Code

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {Bl : Int64 → Label → Nat → Prop}

/-- A piece at `CdCL` followed by a position off the write abort is at
`CdCLE`, and starts at one. -/
theorem cdCLE_of {pc : Int64} {blk : List Directive} (h : CdCL prog okPc ph lab ra pc blk)
    (he : PosOff prog lab (pc + Int64.ofNat (4 * blk.length))) :
    CdCLE prog okPc ph lab ra pc blk ∧ PosOff prog lab pc := by
  refine ⟨⟨h, fun _ => he⟩, ?_⟩
  by_cases hne : blk = []
  · subst hne
    rwa [List.length_nil, ofNat4_zero] at he
  · exact posOff_start h hne

/-- **`CodeC2` at `CdCL` gives it at `CdCLE`**, its pc a position off the
write abort: each call's pc one (`hBl`), the terminator a `TermC2`. -/
theorem codeC2_cdCLE (hBl : ∀ pc g k, Bl pc g k → PosOff prog lab pc) {tm : Scc.IR.Term} (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (pc : Int64), CodeC2 cx (CdCL prog okPc ph lab ra) Bl k pc is tm →
      CodeC2 cx (CdCLE prog okPc ph lab ra) Bl k pc is tm ∧ PosOff prog lab pc
  | [], _, pc, h => by
    rcases h with h | ⟨l, hl, hcd⟩
    · subst h; cases htm
    have hj := term2_endJ htm hl
    have hne : directives l ≠ [] := by
      intro h0; rw [h0] at hj; cases hj
    exact ⟨.inr ⟨l, hl, hcd, fun h => absurd hj (by rw [h]; decide)⟩, posOff_start hcd hne⟩
  | i :: is, k, pc, h => by
    rcases h with ⟨hc, l, hl, hcd, hr⟩ | ⟨d, g, w, lw, ls, hi, hw, hs, hcd, hb, hs2, hr⟩ |
      ⟨p, h, kv, u, la, ls, hi, ha, hs, hcd, hb, hs2, hr⟩ | ⟨a0, a1, la, hi, ha, hcd, hb, hr⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd hp
      exact ⟨.inl ⟨hc, l, hl, hcd', hr'⟩, hp0⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (hBl _ _ _ hb)
      obtain ⟨hs2', -⟩ := cdCLE_of hs2 hp
      exact ⟨.inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, hcd', hb, hs2', hr'⟩), hp0⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (hBl _ _ _ hb)
      obtain ⟨hs2', -⟩ := cdCLE_of hs2 hp
      exact ⟨.inr (.inr (.inl ⟨p, h, kv, u, la, ls, hi, ha, hs, hcd', hb, hs2', hr'⟩)), hp0⟩
    · obtain ⟨hr', -⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (hBl _ _ _ hb)
      exact ⟨.inr (.inr (.inr ⟨a0, a1, la, hi, ha, hcd', hb, hr'⟩)), hp0⟩

/-- **`BlocksCodeC2` at `CdCL` gives it at `CdCLE`**, every block's
terminator a `TermC2`. -/
theorem blocksCodeC2_cdCLE (hBl : ∀ pc g k, Bl pc g k → PosOff prog lab pc) {bs : List Scc.IR.Block}
    (hs : ∀ b ∈ bs, TermC2 b.term) (h : BlocksCodeC2 cx (CdCL prog okPc ph lab ra) Bl lab bs) :
    BlocksCodeC2 cx (CdCLE prog okPc ph lab ra) Bl lab bs := fun b hb hu =>
  let ⟨L, k, hL, hk⟩ := h b hb hu
  ⟨L, k, hL, (codeC2_cdCLE hBl (hs b hb) _ _ _ hk).1⟩

end Code

/-- **Each compiled block's function's code at `CdCLE` from `PlaceOK`**
(`fnCodeC2LB_ofPlaceOK` at `CdCLE`): as there, the entry block at `CodeC2`
and the later blocks at `BlocksCodeC2`, every piece but a terminator's
followed by a position off the write abort, every call at `BlC2L`. -/
theorem fnCodeC2LE_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧ rt.length = 18 ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let cx := ctxOf ir (rt.length + j) f
        LowC2 p cfg.layout.obj d w ∧ cx.maps = true ∧
        ∃ entry : Label, cx.blockLabel "entry" = .ok entry ∧
          ∀ ra' : Int64,
            Spike.Lib.A64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.A64.PhRec.ph Ly ra.toBitVec.toNat →
            CodeC2 cx (CdCLE o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') 0
                (Ly.lab entry) w.r.insts w.r.term ∧
              BlocksCodeC2 cx (CdCLE o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') Ly.lab
                w.r.blocks := by
  intro o ir Ly ra
  obtain ⟨ws, rt, hws, hir, hrt, H⟩ := fnCodeC2LB_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, hrt, fun j d w hd hw => ?_⟩
  obtain ⟨hL, hm, entry, hent, H'⟩ := H j d w hd hw
  have hs := Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2
  refine ⟨hL, hm, entry, hent, fun ra' hra => ?_⟩
  obtain ⟨hc, hb⟩ := H' ra' hra
  exact ⟨(codeC2_cdCLE (fun _ _ _ h => BlC2L.posOff h) hs.2.1 _ _ _ hc).1,
    blocksCodeC2_cdCLE (fun _ _ _ h => BlC2L.posOff h) (fun b hb => (hs.2.2 b hb).2) hb⟩

/-- info: 'Spike.Lib.LowerA64.codeC2_cdCLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_cdCLE

/-- info: 'Spike.Lib.LowerA64.fnCodeC2LE_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2LE_ofPlaceOK

end Spike.Lib.LowerA64
