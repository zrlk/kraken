/-
**Each function's and each call site's placement facts of an `Accepted1`
program from `PlaceOK`** (AArch64): the analogue of `mainPh1_ofPlaceOK`
(`Spike/Lib/LowerA64/MainCode1.lean`) for every code block of a program
of several declarations, and the facts of one `call` in a block.

- `fnPh1_ofPlaceOK`: on an `Accepted1` program that lowers and emits, whose
  output passes `PlaceOK`, the lowered IR is the runtime functions then
  `funcs1 p rs` (each code block's closed form `rs[j]`), and the `j`th code
  block's function `func1 …` at its context `cx` has a valid frame of at
  most 4095 bytes (a multiple of 16), its prologue (with its parameters'
  stores `ps`), its blocks (`blocksOk`), their runs' phase facts at every
  return address of the phase of the one after `scc_rt_main`'s `bl`
  (`blocksPh`, by `blocksPh_ra`), the prologue's `ProPh`, and with a
  checked `+` the local overflow block with its `blkPh`.
- `find_index` (`Spike.Lib.LowerNode`, `Spike/Lib/LowerProgC1.lean`): a
  declaration `find?` finds is one at an index.
- `instsItems_append_cons`, `inst_call_inv`: the code of a block's
  instructions split at one, and the code of a `call` (with the stack maps
  on): the arguments' loads, `bl`, the return label `.spK`, the results'
  stores.
- `callSite1`: from a block's `blocksOk`/`blocksPh`, a `call` in it: the
  run `ys ++ [bl g]` up to it after the last label `L` before it, its
  segment through `.spK`, the run's phase facts, `L` and the runs after
  `.spK` in the phase of the return address.
- `call_blockAt`: with that run's instructions only, the `bl` placed
  (`blockAt`), `.spK` one instruction after it (`labelGap`), and its
  `blkPh`.
-/
import Spike.Lib.LowerA64.MainCode1
import Spike.Lib.LowerProgC1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (blockAt labelGap isIns)
open Scc.Cert.Code1A64 (blocksOk blockItems instsItems kAfter segIn spills hasAddChk ctxOf fnOk1
  fnOk1_of_fnCode1Ok fnOk1_facts segIn_label blockAt_of_segIn labelGap_of_segIn blocksOk_block)
open Scc.Cert.Ph1A64 (runs runPh runPhB blocksPh blocksPh_blockPh blocksPh_ra fnPh1Ok_parts
  fnPhF_of_fnPhAll1 fnPhF_facts runsAux_append_label runsAux_last blkPh_of_runPhB)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 lowerAll_accepted1_a64 mem_progOf_funcs1)

/-! ## Each function -/

/-- **A function passing `fnOk1` stores its parameters** (`spills` is
defined). -/
theorem spills_of_fnOk1 {prog : List Directive} {tbl : List Scc.Cert.NeedA64.Row} {c : FnCtx}
    {f : Scc.IR.Func} (h : fnOk1 prog tbl c f = true) : ∃ ps, spills c f.params = some ps := by
  unfold fnOk1 at h
  split at h
  · exact ⟨_, ‹spills c f.params = some _›⟩
  · cases h

/-- **Each code block's function's code and phase facts from `PlaceOK`**
on an `Accepted1` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`): the `j`th declaration
`d` with its closed form `r` is the function `func1 (user d.name) (params1R
d) r`, the `rt.length + j`th of the IR. -/
theorem fnPh1_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs) ∧
      (∀ l a, codeOf Λ.code.lo o.prog l = some a → Ly.lab l = Int64.ofNat a) ∧
      ∀ (j : Nat) (d : Decl) (r : Res1), p[j]? = some d → rs[j]? = some r →
        LowC p cfg.layout.obj none d r ∧
        (func1 (Scc.Lower.Names.user d.name) (params1R d) r, rt.length + j) ∈ ir.funcs.zipIdx ∧
        FrameOk (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r)) ∧
        (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame ≤ 4095 ∧
        (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame % 16 = 0 ∧
        ∃ (entry : Label) (ps : List (XReg × Int64)),
          let f := func1 (Scc.Lower.Names.user d.name) (params1R d) r
          let cx := ctxOf ir (rt.length + j) f
          cx.blockLabel "entry" = .ok entry ∧ spills cx f.params = some ps ∧
          prologueIn o.prog f.name (cx.local "stack_check") entry (Int64.ofInt cx.frame)
            (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true ∧
          blocksOk o.prog cx 0 f.blocks = true ∧
          (∀ ra' : Int64,
            Spike.Lib.A64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.A64.PhRec.ph Ly ra.toBitVec.toNat →
            blocksPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (labC Λ.code.lo o.prog)
              (fun l => (codeOf Λ.code.lo o.prog l).isSome) cx ra' 0 f.blocks = true) ∧
          ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
            (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) ps ∧
          (hasAddChk f = true →
            blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
            blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly)
              (fun _ => false) Ly.lab (Ly.lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
              A64.Abort.Local.lb = true) := by
  intro o ir Ly ra
  obtain ⟨rs, rt, hrs, -, hir, -⟩ := lowerAll_accepted1_a64 cfg hp hlow
  have hlab := lab_ofPlaceOK h i
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h (lowerAll_place_ir cfg p))
  refine ⟨rs, rt, hrs, hir, hlab, fun j d r hd hr => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  have hmem : (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j], rt.length + j) ∈
      ir.funcs.zipIdx := by
    show _ ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  have hF := fnPhF_of_fnPhAll1 hall hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  obtain ⟨⟨entry, hent, hpro⟩, hle, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl hps
  obtain ⟨-, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF hps
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  refine ⟨hrs.get j hj, hmem, fnCtx_frameOk .., hle, h16, entry, ps, hent, hps, hpro, hbo,
    fun ra' h' => blocksPh_ra h' hbp, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨hd', ld1⟩, ld2⟩, br⟩, frr⟩ := hpp
    have e := fun (blk : List Directive)
        (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt (ctxOf ir (rt.length + j)
          (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j])).frame)
          (proL (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j])))
          ps) =>
      (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
        (blkLabs blk).all (fun l => (codeOf Λ.code.lo o.prog l).isSome) = true)
    refine ⟨⟨⟨⟨?_, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact br
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨hovf ha, hb⟩

/-! ## A call site -/

/-- **The code of a block's instructions split at one**: `is1`'s, the
instruction's (numbered after `is1`), then `is2`'s. -/
theorem instsItems_append_cons {c : FnCtx} {i : Scc.IR.Inst} {is2 : List Scc.IR.Inst} :
    ∀ {k : Nat} {is1 : List Scc.IR.Inst} {code : List Item}, instsItems c k (is1 ++ i :: is2) = .ok code →
      ∃ c1 ci c2, instsItems c k is1 = .ok c1 ∧ c.inst (k + is1.length) i = .ok ci ∧
        instsItems c (k + is1.length + 1) is2 = .ok c2 ∧ code = c1 ++ (ci ++ c2)
  | k, [], code, h => by
    simp only [List.nil_append, instsItems] at h
    cases hci : c.inst k i with
    | error e => simp [hci, bind, Except.bind] at h
    | ok ci =>
      cases hc2 : instsItems c (k + 1) is2 with
      | error e => simp [hci, hc2, bind, Except.bind] at h
      | ok c2 =>
        simp [hci, hc2, bind, Except.bind, pure, Except.pure] at h
        exact ⟨[], ci, c2, rfl, by simp, by simp, by simp [h]⟩
  | k, j :: is1, code, h => by
    simp only [List.cons_append, instsItems] at h
    cases hcj : c.inst k j with
    | error e => simp [hcj, bind, Except.bind] at h
    | ok cj =>
      cases hr : instsItems c (k + 1) (is1 ++ i :: is2) with
      | error e => simp [hcj, hr, bind, Except.bind] at h
      | ok cr =>
        simp [hcj, hr, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨c1, ci, c2, h1, h2, h3, rfl⟩ := instsItems_append_cons hr
        refine ⟨cj ++ c1, ci, c2, ?_, ?_, ?_, ?_⟩
        · simp [instsItems, hcj, h1, bind, Except.bind, pure, Except.pure]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3
        · simp [h]

/-- **The code of a `call`** numbered `k`, with the stack maps on: the
arguments' loads, the `bl`, the return label `.spK`, the results' stores. -/
theorem inst_call_inv {cx : FnCtx} (hm : cx.maps = true) {k : Nat} {ds : List Scc.IR.Reg} {g : Scc.IR.Sym}
    {args : List Scc.IR.Operand} {ci : List Item} (h : cx.inst k (.call ds g args) = .ok ci) :
    ∃ ca sr, cx.callArgs args = .ok ca ∧ cx.setResults ds = .ok sr ∧
      directives ci = directives ca ++ .instr ⟨.W64, .BL (.label g)⟩ ::
        .label (cx.local s!"sp{k}") :: directives sr := by
  simp only [FnCtx.inst] at h
  split at h
  · cases hca : cx.callArgs args with
    | error e => simp [hca, bind, Except.bind] at h
    | ok ca =>
      cases hsr : cx.setResults ds with
      | error e => simp [hca, hsr, bind, Except.bind] at h
      | ok sr =>
        simp [hca, hsr, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨ca, sr, rfl, rfl, by simp [directives, call, lbl, ins]⟩
  · cases h

/-- **A call site's placement and phase facts**, from its block's
`blocksOk` and `blocksPh` (the block `b` after `pre`, its instructions
`is1`, the `call`, then `is2`), with the stack maps on: the arguments'
loads `ca` and the results' stores `sr`; the run of the `bl` is `ys ++ [bl
g]` after the last label `L` before it (the block's label `l` if none):
the code `c1` of `is1` and `ca` are `X ++ ys`, `X` empty or ending with
`label L`; that run and the return label `.spK` after it are a segment of
`L`, the run passes `runPh`, and `L` and the runs after `.spK` are in the
phase of `ra`, those runs passing `runPh`. -/
theorem callSite1 {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {res : String → Bool} {cx : FnCtx} (hm : cx.maps = true) {ra : Int64}
    {k : Nat} {pre post : List Scc.IR.Block} {b : Scc.IR.Block}
    (hok : blocksOk prog cx k (pre ++ b :: post) = true)
    (hph : blocksPh okPc ph lab res cx ra k (pre ++ b :: post) = true)
    {is1 is2 : List Scc.IR.Inst} {ds : List Scc.IR.Reg} {g : Scc.IR.Sym} {args : List Scc.IR.Operand}
    (hb : b.insts = is1 ++ .call ds g args :: is2) :
    ∃ (l : Label) (c1 ca sr : List Item) (L : Label) (X ys rest : List Directive),
      cx.blockLabel b.label = .ok l ∧ instsItems cx (k + kAfter pre) is1 = .ok c1 ∧
      cx.callArgs args = .ok ca ∧ cx.setResults ds = .ok sr ∧
      directives c1 ++ directives ca = X ++ ys ∧ ((X = [] ∧ L = l) ∨ ∃ X', X = X' ++ [.label L]) ∧
      segIn prog L (ys ++ .instr ⟨.W64, .BL (.label g)⟩ ::
        .label (cx.local s!"sp{k + kAfter pre + is1.length}") :: (directives sr ++ rest)) = true ∧
      runPh okPc ph lab res ra (L, ys ++ [.instr ⟨.W64, .BL (.label g)⟩]) = true ∧
      ph (lab L).toBitVec.toNat = ph ra.toBitVec.toNat ∧
      ∀ r ∈ runs (cx.local s!"sp{k + kAfter pre + is1.length}") (directives sr ++ rest),
        runPh okPc ph lab res ra r = true ∧ ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hruns⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  cases hi : instsItems cx (k + kAfter pre) b.insts with
  | error e => simp [blockItems, hi, bind, Except.bind] at hc
  | ok cI =>
    cases ht : cx.term (k + kAfter pre + b.insts.length) b.term with
    | error e => simp [blockItems, hi, ht, bind, Except.bind] at hc
    | ok cT =>
      simp [blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      rw [hb] at hi
      obtain ⟨c1, ci, c2, h1, h2, h3, rfl⟩ := instsItems_append_cons hi
      obtain ⟨ca, sr, hca, hsr, hci⟩ := inst_call_inv hm h2
      have hD : directives (c1 ++ (ci ++ c2) ++ cT) =
          (directives c1 ++ directives ca ++ [.instr ⟨.W64, .BL (.label g)⟩]) ++
            .label (cx.local s!"sp{k + kAfter pre + is1.length}") ::
              (directives sr ++ (directives c2 ++ directives cT)) := by
        simp [directives_append, hci]
      rw [hD] at hseg hruns
      rw [runs, runsAux_append_label] at hruns
      obtain ⟨L, X, ys', hlast, hPX, hX⟩ := runsAux_last l [] (directives c1 ++ directives ca ++
        [.instr ⟨.W64, .BL (.label g)⟩])
      simp only [List.reverse_nil, List.nil_append] at hPX
      -- the last run ends with the `bl`
      obtain ⟨ys, rfl, hXys⟩ : ∃ ys, ys' = ys ++ [Directive.instr ⟨.W64, .BL (.label g)⟩] ∧
          directives c1 ++ directives ca = X ++ ys := by
        rcases List.eq_nil_or_concat ys' with rfl | ⟨ys, z, rfl⟩
        · exfalso
          rcases hX with ⟨rfl, -⟩ | ⟨X', rfl⟩
          · simp at hPX
          · have := List.append_inj' (by simpa using hPX :
              directives c1 ++ directives ca ++ [Directive.instr ⟨.W64, .BL (.label g)⟩] =
                X' ++ [Directive.label L]) rfl
            simp at this
        · rw [List.concat_eq_append] at hPX ⊢
          obtain ⟨h1, h2⟩ := List.append_inj' (hPX.trans (List.append_assoc _ _ _).symm) rfl
          cases h2
          exact ⟨ys, rfl, h1⟩
      have hmemL := List.mem_of_getLast? hlast
      obtain ⟨hrL, hphL⟩ := hruns _ (List.mem_append_left _ hmemL)
      refine ⟨l, c1, ca, sr, L, X, ys, directives c2 ++ directives cT, hl, h1, hca, hsr, hXys, hX,
        ?_, hrL, hphL, fun r hr => hruns r (List.mem_append_right _ hr)⟩
      rcases hX with ⟨rfl, rfl⟩ | ⟨X', rfl⟩
      · rw [hPX] at hseg
        simpa using hseg
      · rw [hPX] at hseg
        exact segIn_label (xs := X') (by simpa using hseg)

/-- **A call site's `bl` placed**: with the run `ys` before the `bl`
instructions only, the run `ys ++ [bl g]` is code at `L`, the return label
`.spK` follows `L` after `ys.length + 1` instructions, and the `bl` at its
pc passes `blkPh` (no dead target). -/
theorem call_blockAt {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {res : String → Bool} {ra : Int64} {L spK g : Label} {ys S : List Directive}
    (hseg : segIn prog L (ys ++ .instr ⟨.W64, .BL (.label g)⟩ :: .label spK :: S) = true)
    (hrun : runPh okPc ph lab res ra (L, ys ++ [.instr ⟨.W64, .BL (.label g)⟩]) = true)
    (hys : ys.all isIns = true) :
    blockAt prog L 0 (ys ++ [.instr ⟨.W64, .BL (.label g)⟩]) = true ∧
    labelGap prog L spK (ys.length + 1) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat (4 * ys.length)) ra
      [.instr ⟨.W64, .BL (.label g)⟩] = true := by
  have hins : (ys ++ [Directive.instr ⟨.W64, .BL (.label g)⟩]).all isIns = true := by
    simp [List.all_append, hys, isIns]
  refine ⟨?_, ?_, ?_⟩
  · have := blockAt_of_segIn (xs := []) (ys := ys ++ [.instr ⟨.W64, .BL (.label g)⟩])
      (zs := .label spK :: S) (by simpa using hseg) rfl hins
    simpa using this
  · have := labelGap_of_segIn (xs := ys ++ [.instr ⟨.W64, .BL (.label g)⟩]) (l' := spK) (ys := S)
      (by simpa using hseg) hins
    simpa using this
  · simp only [runPh, Bool.and_eq_true] at hrun
    exact blkPh_of_runPhB (zs := []) (by simpa using hrun.2) (by simp [Spike.Lib.A64.Flow.classify])

end Spike.Lib.LowerA64
