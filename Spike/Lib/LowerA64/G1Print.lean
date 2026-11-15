/-
**The output calls at a generic base context** (AArch64): `Print2Stmt`
(`Spike/Lib/LowerA64/G1FnSpec.lean`), the `PrintCallC` conjunct of
`bodySpecC2_of`'s `hcon` at every context `CxG2M` of the `j`th compiled
block of an `Accepted2` program, at the assembled theorem's world
`W2At`/`MSAt` and the placement check's code facts `fnCode2OfPMe`, both at
the theorem's immediates `imms2Me Λ p`, given the write tail `Dt` at the
output call's system call.

`printCallC_instAI` (`Spike/Lib/LowerA64/PrintCallInstAI.lean`) at the
record's instance at `imms2Me Λ p`, as `hello1_printCallCA`
(`Spike/Test/A64Hello1Print.lean`) uses it, with every `hello1o` fact
replaced by its generic source:

- an extern called at a point of a compiled block is `print` with no type
  arguments (`extern_call_print`: an extern block makes the program one
  with the output extern, `hasPrint_of_externOf`; its name is then
  reserved, so no ordinary call names it, `body2_of_compiledR`);
- the extern and its loop by name (`printDecl_of_accepted2`, `hd2`);
- the output call's continuation free of `ZBad` (`body2`'s, `noS_zbad_of_body2`);
- the frames below free of `ZBad` from a ghost's `FrOk2` (without a ghost
  the premise is vacuous);
- the nodes' abort `ab2` the write abort (with an output call the program
  has the extern);
- the room below the frame from the stack need table's row (`room2Own`);
- the output calls' abort states one of `AbG2`'s, so in the context's
  aborts.

- `hasPrint_of_externOf`, `extern_call_print`, `noS_cont`;
- `print2`: `Print2Stmt`.
-/
import Spike.Lib.LowerA64.G1LaneBuf
import Spike.Lib.LowerA64.Closed2OfA
import Spike.Lib.Src.CalleePlain2
import Spike.Lib.Rt.A64PrintNoSite

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf IsNum imms2Me ZBad FrOk2)
open Scc.Lower (Cx2 body2 callee2 decl2 decls2 main2 setup2 plain2 reserved hasPrint Accepted2 setupOf)

/-! ## The externs called -/

/-- **An extern block makes the program one with the output extern**: a
block of an `Accepted2` program that the frontend takes for an extern
(named `print` or `printL`, returning `Unit`) passes `decl2` only as the
extern or, with the extern, its loop. -/
theorem hasPrint_of_externOf {p : Prog} (hacc : Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    {x : Scc.Frontend.Extern} (hx : Scc.Frontend.externOf d = some x) : hasPrint p = true := by
  have hr := Spike.Lib.LowerNode.retTy_of_externOf hx
  have hn : d.name = "print" ∨ d.name = "printL" := by
    unfold Scc.Frontend.externOf at hx
    split at hx
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact .inl hc.1.1.1.1
    · split at hx
      · rename_i _ hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact .inr hc.1
      · cases hx
  obtain ⟨hds, -⟩ := Spike.Lib.LowerNode.accepted2_parts hacc
  obtain ⟨E, hE, -⟩ := Spike.Lib.LowerNode.decl2_of_decls2' hds d hd
  unfold decl2 at hE
  split at hE
  · rename_i hpe; exact List.any_eq_true.2 ⟨d, hd, hpe⟩
  split at hE
  · rename_i hl; simp only [Bool.and_eq_true] at hl; exact hl.1
  have hm : d.name ≠ "main" := by rcases hn with h | h <;> rw [h] <;> decide
  have hro : d.name ≠ "rodata" := by rcases hn with h | h <;> rw [h] <;> decide
  simp only [beq_iff_eq, hm, hro, ↓reduceIte] at hE
  exfalso
  split at hE <;>
  · try simp only [plain2, Bool.and_eq_true, beq_iff_eq] at hE
    exact absurd (hr.symm.trans hE.1.1.2) (by simp)

/-- **An extern called at a point of a compiled block is `print`**, with
no type arguments: the extern block makes the program one with the output
extern (`hasPrint_of_externOf`), whose names `print` and `printL` are
reserved (`body2_of_compiledR`, `Spike/Lib/Src/CalleePlain2.lean`), so the call passes `body2` as the output
call. -/
theorem extern_call_print {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e) d.body) {xe : String × Scc.Frontend.Extern}
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = some xe) : g = "print" ∧ ts = [] := by
  -- the extern block
  have hxm := List.mem_of_find?_eq_some hx
  have hxn : xe.1 = g := by simpa using List.find?_some hx
  obtain ⟨dx, hdx, hex⟩ := List.mem_filterMap.1 hxm
  obtain ⟨ex, hex', hxe⟩ := Option.map_eq_some_iff.1 hex
  have hP := hasPrint_of_externOf hacc hdx hex'
  have hgn : g = "print" ∨ g = "printL" := by
    rw [← hxn, ← hxe]
    unfold Scc.Frontend.externOf at hex'
    split at hex'
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact .inl hc.1.1.1.1
    · split at hex'
      · rename_i _ hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact .inr hc.1
      · cases hex'
  -- the caller's body check at the call
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 (List.mem_of_getElem? hj)
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hpe⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, hext, hexc, -⟩ := Spike.Lib.LowerNode.body2_of_compiledR hacc hpe hdc'
  obtain ⟨_, _, _, hb'⟩ := Spike.Lib.LowerNode.body2_tail ht hb
  simp only [body2, Bool.and_eq_true] at hb'
  have hc := hb'.1.1
  revert hc
  split
  · rename_i hh
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hh hc
    exact ⟨hh.2, hc.2⟩
  · intro hc
    simp only [callee2, Bool.and_eq_true, Bool.not_eq_true'] at hc
    exfalso
    have hres : (reserved (setupOf p) (hasPrint p)).contains g = true := by
      rcases hgn with rfl | rfl <;> simp [reserved, hP]
    rw [← hexc, hc.1.1.2] at hres
    cases hres

/-- **A `let`'s continuation at a point of a compiled block is free of
`ZBad`** (`body2`'s, `noS_zbad_of_body2`). -/
theorem noS_cont {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl} (hj : (compiled2 p)[j]? = some d)
    {x : String} {op : Op} {e : Expr} (ht : TailOf (.let_ x op e) d.body) : NoS ZBad e := by
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 (List.mem_of_getElem? hj)
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hpe⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, -, -, -⟩ := Spike.Lib.LowerNode.body2_of_compiledR hacc hpe hdc'
  obtain ⟨_, _, _, hb'⟩ := Spike.Lib.LowerNode.body2_tail ht hb
  obtain ⟨_, _, _, hb''⟩ := Spike.Lib.LowerNode.body2_let_tail hb'
  exact Spike.Lib.LowerNode.noS_zbad_of_body2 e hb''

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

/-- **`Print2Stmt`**: at every context `CxG2M` of the `j`th compiled block
(return address in the code facts' `RaOk`), the output calls
(`printCallC_instAI`), given the write tail at the output call's system
call. -/
theorem print2 (hp : Scc.Lower.Accepted2 p = true) : Print2Stmt h hp := by
  intro Dt hDtP J j d hd R F fs fp ra tp G0 Ab hcx hra
  obtain ⟨H, hAb⟩ := hcx
  have hsp := fnCode2OfPMe_spec hp h Λ j d hd
  have hlo := room2Own h hp j d hd 256 R.lo (H.room d hd)
  have hBl0 : ∀ pc g' k, (fnCode2OfPMe hp h Λ j d hd).Bl ra pc g' k →
      BlC2L OP (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
        (fnCode2OfPMe hp h Λ j d hd).cx (Int64.ofBitVec ra) pc g' k := by
    intro pc g' k hb
    rw [hsp.2.1] at hb
    rw [okPc_imms h]
    exact hb
  intro c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs hc0 hT hfr hlp henv hgrp hcnt hsh hxe hdg
    hret hat hins hfv himm hlb
  have hxe' := hxe
  rw [hsp.1] at hxe'
  obtain ⟨rfl, rfl⟩ := extern_call_print hp hd (hT d hd) hxe'
  have hP : hasPrint p = true := by
    obtain ⟨dx, hdx, hex⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hxe')
    obtain ⟨ex, hex', -⟩ := Option.map_eq_some_iff.1 hex
    exact hasPrint_of_externOf hp hdx hex'
  have hab : ab2 p (Ly).lab = some (Spike.Lib.A64.WriteAb.Ab (Ly).lab) := by
    simp only [ab2, hP, ↓reduceIte]
  simp only [MSAt, hab]
  exact printCallC_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.PrintG.printPhOkF_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1 (fnCode2OfPMe hp h Λ j d hd).h16
    H.hR H.hal (by omega) H.hhi H.hl H.hh
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    H.hFO (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) H.hFS
    (fun _ _ hc => by rw [okPc_imms h]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    (Spike.Lib.LowerNode.printDecl_of_accepted2 hp hP) (hd2 hp h hP) (by rw [hsp.1])
    (fun _ _ hb => by cases hb) (below32_of_placeOKAt h)
    (H.hG0F c0 hc0).2 H.hfp H.hG0F
    (fun _ _ _ _ _ _ _ ht hx => extern_call_print hp hd (ht d hd) (by rw [hsp.1] at hx; exact hx))
    fp ra tp
    (fun _ _ _ _ ht => noS_cont hp hd (ht d hd))
    hDtP
    (fun c0' x' is' a' e' c1 s c hc0' ht hX =>
      hAb s c _ ⟨j, d, hd, R, F, fs, fp, ra, tp, G0, H, .inr (.inr ⟨c0', x', is', a', e', c1, hc0', ht, rfl, hX⟩)⟩)
    (fun _ _ _ _ h' => h') (fun _ _ _ _ _ => rfl)
    c0 pc pc' kk env n x "print" is a [] e xe dg t b o m cw lits cs bufs hc0 hT hfr hlp henv hgrp hcnt hsh hxe hdg
    hret hat hins hfv himm hlb

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hasPrint_of_externOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hasPrint_of_externOf

/-- info: 'Spike.Lib.LowerA64.extern_call_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.extern_call_print

/-- info: 'Spike.Lib.LowerA64.noS_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.noS_cont

/-- info: 'Spike.Lib.LowerA64.print2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.print2
