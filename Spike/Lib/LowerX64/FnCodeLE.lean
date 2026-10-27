/-
**Each `Accepted2` code block's pieces followed by a position off the write
abort** (x86-64): `Spike/Lib/LowerX64/FnCodeLB.lean`'s `CodeC2` and
`BlocksCodeC2` at `CdCL` and `BlC2L` give them at `CdCLE`
(`Spike/Lib/LowerX64/CdCLE.lean`). A piece of an instruction is followed by
the rest of the block's code, which starts with a nonempty piece (a
terminator's is never empty) or a call's `callq` (at a position off the write
abort by `BlC2L`); a terminator's piece ends with a `jmp` or a `ret`.

- `emits_unique`, `emitTerm2_last`: the items a piece of code emits are
  unique; a `TermC2` terminator's last directive is a `jmp` or a `ret`.
- `cellOff_zip`: a piece's size.
- `codeC2_cdCLE`: `CodeC2` at `CdCL` gives it at `CdCLE`, its pc a position
  off the write abort, every call's pc one (`hBl`).
- `blocksCodeC2_cdCLE`: the same for `BlocksCodeC2`.
- `fnCodeC2LE_ofPlaceOK`: `fnCodeC2LB_ofPlaceOK` at `CdCLE`.
-/
import Spike.Lib.LowerX64.FnCodeLB
import Spike.Lib.LowerX64.CdCLE

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (S E Item emitTerm cmpAB labelOf)
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64 (cellOff)
open Spike.Lib.LowerShape (InstC2 TermC2 func2 paramsR)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2)

/-! ## A terminator's last cell -/

/-- **The items a piece of code emits are unique.** -/
theorem emits_unique {x : E Unit} {c c' : List Item} (h : Emits x c) (h' : Emits x c') : c = c' := by
  have e := (h { out := [], next := 0, maps := [] }).symm.trans (h' { out := [], next := 0, maps := [] })
  simp only [Except.ok.injEq, Prod.mk.injEq, S.mk.injEq, List.append_nil, true_and, and_true] at e
  exact List.reverse_inj.mp e

/-- **A `TermC2` terminator's last directive is a `jmp` or a `ret`.** -/
theorem emitTerm2_last {fr : Scc.Emit.X64.Frame} {t : Scc.IR.Term} (ht : TermC2 t) {c : List Item}
    (hc : Emits (emitTerm fr t) c) : ∃ d, (dirs c).getLast? = some d ∧ isJR d = true := by
  have h := hc { out := [], next := 0, maps := [] }
  cases ht with
  | ret ws =>
    by_cases hgt : ws.length > Scc.Emit.X64.retRegs.length
    · simp only [emitTerm, Scc.Emit.X64.loadArgs, hgt, ite_true] at h
      cases h
    have hl : Scc.Emit.X64.loadArgs fr Scc.Emit.X64.retRegs ws "ret" =
        (ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) := by
      simp only [Scc.Emit.X64.loadArgs, hgt, ite_false]
    have he : emitTerm fr (.ret ws) =
        ((ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) >>= fun _ =>
          (do Scc.Emit.X64.epilogue; Scc.Emit.X64.ins (Scc.Emit.X64.i64 .ret))) := by
      simp only [emitTerm, hl]
    rw [he] at h hc
    obtain ⟨u, s1, h1, -⟩ := bind_inv h
    obtain ⟨lw, hlw⟩ := ldsLoop_ok h1
    obtain rfl := emits_unique hc ((ldsLoop_emits hlw).seq emits_retTail)
    simp [epiItems, dirs, isJR, Spike.Lib.X64.classify, Scc.Emit.X64.i64, Scc.Emit.X64.op]
  | br p q l l' =>
    simp only [emitTerm, cmpAB] at h hc
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨u0, s0, h0, h1⟩ := bind_inv h1
    obtain ⟨la, ha⟩ := ld_ok h0
    obtain ⟨u2, s2, h2, h1⟩ := bind_inv h1
    obtain ⟨lb, hb⟩ := ld_ok h2
    obtain rfl := emits_unique hc
      (((emits_ld ha).seq ((emits_ld hb).seq (emits_ins _))).seq ((emits_ins _).seq (emits_ins _)))
    simp [dirs, isJR, Spike.Lib.X64.classify, Scc.Emit.X64.i64, Scc.Emit.X64.op, Scc.Emit.X64.rel]

/-- **A piece's size**: its cells' sizes. -/
theorem cellOff_zip {ds : List Directive} {zs : List Nat} (h : zs.length = ds.length) :
    cellOff (ds.zip zs) (ds.zip zs).length = zs.sum := by
  unfold cellOff
  rw [List.take_of_length_le (Nat.le_refl _), List.map_snd_zip (by omega)]

/-! ## The code at `CdCLE` -/

section Code

variable {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {fr : Scc.Emit.X64.Frame} {Bl : Int64 → Nat → Label → Nat → Prop}

/-- A piece at `CdCL` followed by a position off the write abort is at
`CdCLE`, and starts at one. -/
theorem cdCLE_of {pc : Int64} {blk : List (Directive × Nat)} (h : CdCL cells okPc ph lab ra pc blk)
    (he : PosOff cells lab (pc + Int64.ofNat (cellOff blk blk.length))) :
    CdCLE cells okPc ph lab ra pc blk ∧ PosOff cells lab pc := by
  refine ⟨⟨h, fun _ => he⟩, ?_⟩
  by_cases hne : blk = []
  · subst hne
    simpa [show Int64.ofNat 0 = 0 from rfl] using he
  · exact posOff_start h hne

/-- **`CodeC2` at `CdCL` gives it at `CdCLE`**, its pc a position off the
write abort: each call's pc one (`hBl`), the terminator a `TermC2`. -/
theorem codeC2_cdCLE (hBl : ∀ pc zc g k, Bl pc zc g k → PosOff cells lab pc) {tm : Scc.IR.Term}
    (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (pc : Int64), CodeC2 fr (CdCL cells okPc ph lab ra) Bl k pc is tm →
      CodeC2 fr (CdCLE cells okPc ph lab ra) Bl k pc is tm ∧ PosOff cells lab pc
  | [], _, pc, h => by
    rcases h with h | ⟨l, zs, hE, hz, hcd⟩
    · subst h; cases htm
    obtain ⟨d, hd, hj⟩ := emitTerm2_last htm hE
    have hj' : endJ ((dirs l).zip zs) = true := by
      rw [endJ, List.map_fst_zip (by omega), hd]; exact hj
    have hne : (dirs l).zip zs ≠ [] := by
      intro h0
      have := congrArg List.length h0
      rw [List.length_zip, Nat.min_eq_left (by omega)] at this
      rw [List.length_eq_zero_iff.mp this] at hd
      cases hd
    exact ⟨.inr ⟨l, zs, hE, hz, hcd, fun h => absurd hj' (by rw [h]; decide)⟩, posOff_start hcd hne⟩
  | i :: is, k, pc, h => by
    rcases h with ⟨hc, l, zs, hE, hz, hcd, hr⟩ | ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, hr⟩ |
      ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, hr⟩ | ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, hr⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is k _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (by rw [cellOff_zip hz]; exact hp)
      exact ⟨.inl ⟨hc, l, zs, hE, hz, hcd', hr'⟩, hp0⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (by rw [cellOff_zip hz]; exact hBl _ _ _ _ hb)
      obtain ⟨hs', -⟩ := cdCLE_of hs (by simpa [cellOff] using hp)
      exact ⟨.inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd', hb, hs', hr'⟩), hp0⟩
    · obtain ⟨hr', hp⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (by rw [cellOff_zip hz]; exact hBl _ _ _ _ hb)
      obtain ⟨hs', -⟩ := cdCLE_of hs (by simpa [cellOff] using hp)
      exact ⟨.inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd', hb, hs', hr'⟩)), hp0⟩
    · obtain ⟨hr', -⟩ := codeC2_cdCLE hBl htm is (k + 1) _ hr
      obtain ⟨hcd', hp0⟩ := cdCLE_of hcd (by rw [cellOff_zip hz]; exact hBl _ _ _ _ hb)
      exact ⟨.inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd', hb, hr'⟩)), hp0⟩

/-- **`BlocksCodeC2` at `CdCL` gives it at `CdCLE`**, every block's
terminator a `TermC2`. -/
theorem blocksCodeC2_cdCLE (hBl : ∀ pc zc g k, Bl pc zc g k → PosOff cells lab pc) {bs : List Scc.IR.Block}
    (hs : ∀ b ∈ bs, TermC2 b.term) (h : BlocksCodeC2 fr (CdCL cells okPc ph lab ra) Bl lab bs) :
    BlocksCodeC2 fr (CdCLE cells okPc ph lab ra) Bl lab bs := fun b hb hu =>
  let ⟨k, hk⟩ := h b hb hu
  ⟨k, (codeC2_cdCLE hBl (hs b hb) _ _ _ hk).1⟩

end Code

/-- **Each compiled block's function's code at `CdCLE` from `PlaceOK`**
(`fnCodeC2LB_ofPlaceOK` at `CdCLE`): as there, the entry block at `CodeC2`
and the later blocks at `BlocksCodeC2`, every piece but a terminator's
followed by a position off the write abort, every call at `BlC2L`. -/
theorem fnCodeC2LE_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let fr := frOf ir f
        LowC2 p cfg.layout.obj d w ∧ fr.maps = true ∧
        ∃ n : Nat, ∀ ra' : Int64,
          Spike.Lib.X64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat →
          CodeC2 fr (CdCLE o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') n
              (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
            BlocksCodeC2 fr (CdCLE o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') Ly.lab
              w.r.blocks := by
  intro o ir Ly
  obtain ⟨ws, rt, hws, hir, H⟩ := fnCodeC2LB_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, hm, n, H'⟩ := H j d w hd hw
  have hs := Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2
  refine ⟨hL, hm, n, fun ra' hra => ?_⟩
  obtain ⟨hc, hb⟩ := H' ra' hra
  exact ⟨(codeC2_cdCLE (fun _ _ _ _ h => BlC2L.posOff h) hs.2.1 _ _ _ hc).1,
    blocksCodeC2_cdCLE (fun _ _ _ _ h => BlC2L.posOff h) (fun b hb => (hs.2.2 b hb).2) hb⟩

/-- info: 'Spike.Lib.LowerX64.codeC2_cdCLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_cdCLE

/-- info: 'Spike.Lib.LowerX64.fnCodeC2LE_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2LE_ofPlaceOK

end Spike.Lib.LowerX64
