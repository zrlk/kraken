/-
**Each `Accepted2` code block's code off the write abort's labels**
(x86-64): `Spike/Lib/LowerX64/FnCode2Of.lean`'s `CodeC2` and
`BlocksCodeC2` at `CdCL` (`Spike/Lib/LowerX64/UserAbC.lean`) rather than
`CdC`. Each piece of a block's code is after the block's label or a call's
return label (`codeC2_of_segQ`); a user function's are none of `abLabs`
(`labelOf_user_not_abLabs`, `ret_not_abLabs`,
`Spike/Lib/LowerX64/UserLabs.lean`).

- `cdCL_eq`: `CdCL` is `CdCQ` at the labels off `abLabs` beginning `.Lwc_` (`WcL`).
- `codeC2_of_segL`, `codeC2L_block`: `codeC2_of_seg`, `codeC2_block` at
  `CdCL`, for a label off `abLabs` (`hl`) and return labels off it (`hK`).
- `blocksCodeC2L`, `entryCodeC2L`, `fnCodeC2L`: the function's blocks at
  `CdCL`, its block labels off `abLabs` (`hfn`).
- `fnCodeC2L_of_fnPh2`, `fnCodeC2L_ofPlaceOK`: from `PlaceOK`, the
  function a user one (`frOf`'s `fn` is `Names.user d.name`).
-/
import Spike.Lib.LowerX64.FnCode2Of
import Spike.Lib.LowerX64.UserLabs

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Emit.X64 (Frame S Item emitTerm labelOf directives)
open Scc.Cert.Rt.X64 (after)
open Scc.Cert.Code1X64 (segIn blockItems blocksOk)
open Scc.Cert.Ph1X64 (runsAux runPhB runs runPh blocksPh segCells)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.LowerShape (InstC2 TermC2)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.LowerShape (func2 paramsR BlockC2)
open Scc.Cert.Rt.X64 (labelGap)
open Scc.Cert.Ph1X64 (blocksPh_blockPh)
open Scc.Cert.Code1X64 (blocksOk_block)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2)
open Spike.Lib.X64.AllocG (abLabs)

/-- **`CdCL` is `CdCQ` at the labels off `abLabs`.** -/
theorem cdCL_eq (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (ra : Int64) : CdCL cells okPc ph lab ra = CdCQ (fun L => L ∉ abLabs ∧ WcL L) cells okPc ph lab ra := rfl

section Code

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64} {lo : Nat}

/-- **`codeC2_of_seg` at `CdCL`**: the segment's label `l` and every return
label `.L<fn>.x<k>` off `abLabs` (`hl`, `hK`). -/
theorem codeC2_of_segL (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {tm : Scc.IR.Term} (htm : TermC2 tm) (hK : ∀ k : Nat, (s!".L{fr.fn}.x{k}" ∉ abLabs ∧ WcL s!".L{fr.fn}.x{k}"))
    (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (code : List Item)
    (l : Label) (t : List (Directive × Nat)) (xs zs : List Directive) (hl : l ∉ abLabs ∧ WcL l)
    (hs : ∀ i ∈ is, InstC2 i) (hms : is.length ≤ ms.length)
    (h : (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s')) (hD : s'.out = code.reverse ++ s.out)
    (ht : after l cells = some t) (hseg : segIn cells l (xs ++ directives code ++ zs) = true)
    (hx : xs.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) s.next
      (lab l + Int64.ofNat (cellOff t xs.length)) is tm :=
  codeC2_of_segQ (Q := fun L => L ∉ abLabs ∧ WcL L) hm hgap htm hK is ms s s' code l t xs zs hl hs hms h hD ht
    hseg hx hph hrl

/-- **`codeC2_block` at `CdCL`**: the block's label and every return label
off `abLabs` (`hl`, `hK`). -/
theorem codeC2L_block (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (hK : ∀ k : Nat, (s!".L{fr.fn}.x{k}" ∉ abLabs ∧ WcL s!".L{fr.fn}.x{k}"))
    {b : Scc.IR.Block} (hl : labelOf fr.fn b.label ∉ abLabs ∧ WcL (labelOf fr.fn b.label)) (hs : BlockC2 b)
    {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term :=
  codeC2_blockQ (Q := fun L => L ∉ abLabs ∧ WcL L) hm hgap hlab hK hl hs hms hc hseg hph

/-- **The later blocks' code at `CdCL`** (`blocksCodeC2`'s twin): every
block label and return label of the function off `abLabs` (`hfn`, `hK`). -/
theorem blocksCodeC2L (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (hfn : ∀ l, labelOf fr.fn l ∉ abLabs ∧ WcL (labelOf fr.fn l))
    (hK : ∀ k : Nat, (s!".L{fr.fn}.x{k}" ∉ abLabs ∧ WcL s!".L{fr.fn}.x{k}"))
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {pre bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((pre ++ bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((pre ++ bs).map fun b => (b, G b)) = true)
    (hs : ∀ b ∈ bs, BlockC2 b) :
    BlocksCodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : (pre ++ (s ++ b :: t)).map (fun b => (b, G b)) =
      (pre ++ s).map (fun b => (b, G b)) ++ (b, G b) :: t.map (fun b => (b, G b)) := by simp
  rw [e] at hok hph
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  exact ⟨_, codeC2L_block hm hgap hlab hK (hfn _) (hs b hb) (Nat.le_of_eq (hG b).symm) hc hseg hr⟩

/-- **The entry block's code at `CdCL`** (`entryCodeC2`'s twin). -/
theorem entryCodeC2L (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (hfn : ∀ l, labelOf fr.fn l ∉ abLabs ∧ WcL (labelOf fr.fn l))
    (hK : ∀ k : Nat, (s!".L{fr.fn}.x{k}" ∉ abLabs ∧ WcL s!".L{fr.fn}.x{k}"))
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((b :: bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((b :: bs).map fun b => (b, G b)) = true)
    (hs : BlockC2 b) :
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact codeC2L_block hm hgap hlab hK (hfn _) hs (Nat.le_of_eq (hG b).symm) hc hseg hr

/-- **A compiled block's function's code at `CdCL`** (`fnCodeC2`'s twin):
its block labels and return labels off `abLabs` (`hfn`, `hK`). -/
theorem fnCodeC2L (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    (hfn : ∀ l, labelOf fr.fn l ∉ abLabs ∧ WcL (labelOf fr.fn l))
    (hK : ∀ k : Nat, (s!".L{fr.fn}.x{k}" ∉ abLabs ∧ WcL s!".L{fr.fn}.x{k}"))
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg} {n : Nat}
    (hok : blocksOk cells fr n ((func2 name ps sc hq r).blocks.zip
      (Scc.IR.StackMap.callMaps (func2 name ps sc hq r))) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((func2 name ps sc hq r).blocks.zip (Scc.IR.StackMap.callMaps (func2 name ps sc hq r))) = true) :
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn "entry"))
        r.insts r.term ∧
      BlocksCodeC2 fr (CdCL cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) lab r.blocks := by
  obtain ⟨G, hz, hG⟩ := zip_callMaps (func2 name ps sc hq r)
  rw [hz] at hok hph
  exact ⟨entryCodeC2L (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hfn hK hG hok hph
      ⟨hs.1, hs.2.1⟩,
    blocksCodeC2L (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hfn hK hG hok hph hs.2.2⟩

end Code

/-- **A compiled block's function's code at `CdCL` from `PlaceOK`, at
`fnPh2_ofPlaceOK`'s witnesses** (`fnCodeC2_of_fnPh2`'s twin): the function
is a user one (`frOf`'s `fn` is `Names.user d.name`), so its labels are off
`abLabs`. -/
theorem fnCodeC2L_of_fnPh2 {cfg : Scc.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {ws : List Low2} {rt : List Scc.IR.Func}
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    {d : Decl} {w : Low2} (hL : LowC2 p cfg.layout.obj d w) {n : Nat}
    (hbo : blocksOk (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) n
      ((func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks.zip
        (Scc.IR.StackMap.callMaps (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r))) = true)
    {ra : Int64}
    (hbp : blocksPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i))
      (labC Λ.code.lo (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog)
      (fun l => (codeLabel Λ.code.lo (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog l).isSome)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) ra n
      ((func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks.zip
        (Scc.IR.StackMap.callMaps (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r))) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h i
    let fr := frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)
    fr.maps = true ∧
      CodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) n
          (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
        BlocksCodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) Ly.lab
          w.r.blocks := by
  intro o Ly fr
  have hm : fr.maps = true := by
    show (Scc.Lower.X64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hfn : fr.fn = Scc.Lower.Names.user d.name := rfl
  exact ⟨hm, fnCodeC2L hm (hgap_ofPlaceOK h i) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i)
    (fun l => hfn ▸ labelOf_user_usr d.name l) (hfn ▸ ret_user_usr d.name)
    (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2) hbo hbp⟩

/-- **Each compiled block's function's code at `CdCL` from `PlaceOK`**
(`fnCodeC2_ofPlaceOK`'s twin): as there, the entry block at `CodeC2` and
the later blocks at `BlocksCodeC2`, at `CdCL`. -/
theorem fnCodeC2L_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
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
          CodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') n
              (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
            BlocksCodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') Ly.lab
              w.r.blocks := by
  intro o ir Ly
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, n, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbo, hbp, -⟩ := H j d w hd hw
  have H' := fun ra' hra => fnCodeC2L_of_fnPh2 h i hir hL hbo (hbp ra' hra)
  exact ⟨hL, (H' (Ly.lab raL) rfl).1, n, fun ra' hra => (H' ra' hra).2⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.codeC2_of_segL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_of_segL

/-- info: 'Spike.Lib.LowerX64.fnCodeC2L_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2L_ofPlaceOK

end Spike.Lib.LowerX64
