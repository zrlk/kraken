/-
**Each function's and each call site's placement facts of an `Accepted1`
program from `PlaceOK`** (x86-64): the twin of
`Spike/Lib/LowerA64/CallSite1.lean`, the analogue of `mainPh1_ofPlaceOK`
(`Spike/Lib/LowerX64/MainCode1.lean`) for every code block of a program of
several declarations, and the facts of one `call` in a block.

- `lowerAll_accepted1_x64`: `lowerAll`'s IR on an `Accepted1` program (the
  runtime functions, then `funcs1`).
- `fnPh1_ofPlaceOK`: on an `Accepted1` program that lowers and emits, whose
  output passes `PlaceOK`, the lowered IR is the runtime functions then
  `funcs1 p rs`, and the `j`th code block's function `f := func1 …`,
  numbered from `n` (`starts`), at its frame `fr := frOf ir f` (valid, a
  multiple of 16, below `2^31`), has its prologue (at the listing's cell
  sizes, with its parameters' stores `ps`), its blocks (`blocksOk`), their
  runs' phase facts at every return address of the phase of `raL`
  (`blocksPh`, by `blocksPh_ra`), the prologue's `ProPh`, and with a
  checked `+` the local overflow block with its `blkPh`.
- `segCells_take`, `segCells_label`, `segIn_call_cells`: the cells of a
  segment, of a prefix of it and after an inner label of it.
- `callSite1`: from a block's `blocksOk`/`blocksPh`, with the stack maps on,
  a `call` in it: the code is `Xd ++ ys ++ [callq g, .L<fn>.x<k>:] ++
  rest`, `Xd` empty or ending with the last label `L` before the call (the
  block's label if none); the run `zy ++ [(callq g, zc)]` (`zy`'s
  directives `ys`) up to the call is the run of cells after `L`, its
  segment through the return label, the run passes `runPh`, and `L` and the
  runs after the return label are in the phase of the return address.
- `call_blockAt`: the run placed at `L` (`blockAt`), the return label after
  it (`labelGap`), and the `callq` at its pc passing `blkPh`.

Where x86-64 differs from AArch64: the frame bound A12 checks is `2^31`
(the stack-check segment's 4096 is a separate per-program check, as
`MainFrame1Ok`); cells carry sizes, so a run is a list of cells (its
directives a segment, `segCells` the cells) and offsets are `cellOff`; a
run's directives are label-free by construction (`runsAux_noLabel`), so
`call_blockAt` needs no hypothesis on them; the call's return label is the
safepoint label `.L<fn>.x<k>` (`k` the emitter's counter).
-/
import Spike.Lib.LowerX64.MainCode1
import Spike.Lib.LowerX64.EmitOut
import Spike.Lib.LowerProgC1Core

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Emit.X64 (Frame Item S labelOf directives i64 rel emitInst emitTerm)
open Scc.Cert.Rt.X64 (after after_eq blockAt labelGap labelIdx)
open Scc.Cert.Code1X64 (blocksOk blockItems nAfter segIn segIn_iff segIn_label blockAt_of_segIn
  labelGap_of_segIn blocksOk_block spills hasAddChk chkL starts fnOk1 fnOk1_of_fnCode1Ok fnOk1_facts
  labelsAt labelsAt_append)
open Scc.Cert.Ph1X64 (runs runsAux runPh runPhB segCells segCells_map blocksPh blocksPh_blockPh blocksPh_ra
  fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts runsAux_append_label runsAux_last runsAux_noLabel
  blkPh_of_runPhB)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.X64.Flow (prologueIn)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (blkPh)
open Scc.Lower.Inv (Res1 func1 params1R)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1)

/-! ## Each function -/

/-- **`lowerAll`'s IR on an `Accepted1` program** (x86-64), when the
lowering and emission succeed: the runtime functions, then `funcs1`, each
code block's closed form without the depth counter. -/
theorem lowerAll_accepted1_x64 (cfg : Scc.Config) {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.lowerAll? cfg p = .ok e) :
    ∃ rs rt, Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      Scc.Lower.Inv.rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs) ∧
      (Scc.Lower.X64.lowerAll cfg p).low.marks = Spike.Lib.LowerNode.marksAll1 p rs := by
  obtain ⟨rs, rt, hrs, hrt, hir, hm⟩ := Spike.Lib.LowerNode.lowerIR_accepted1 cfg hp (lowerAll?_low_x64 h)
  refine ⟨rs, rt, hrs, hrt, ?_, ?_⟩ <;> simp only [Scc.Lower.X64.lowerAll, h]
  · exact hir
  · exact hm

/-- **The prologue's cell sizes and parameters' stores of a function
passing `fnOk1`**: five sizes, then one per parameter, at which `spills`
is defined. -/
theorem fnOk1_sizes {cells : List (Directive × Nat)} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true) :
    ∃ zl zf z1 z2 zs zps ps, sizesAt cells (chkL f) 0 (5 + f.params.length) = zl :: zf :: z1 :: z2 :: zs :: zps ∧
      spills (frOf ir f) f.params zps = some ps := by
  unfold fnOk1 at h
  split at h
  · next zl zf z1 z2 zs zps _ hz =>
    split at h
    · next ps hps => exact ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩
    · cases h
  · cases h

/-- **Each code block's function's code and phase facts from `PlaceOK`**
on an `Accepted1` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`): the `j`th declaration
`d` with its closed form `r` is the function `func1 (user d.name) (params1R
d) r`, the `rt.length + j`th of the IR. -/
theorem fnPh1_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    let L := RuntimeLayout.ofPlaceOK h i
    let okPc := Spike.Lib.X64.PhRec.okPc L
    let ph := Spike.Lib.X64.PhRec.ph L
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs) ∧
      (∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a) ∧
      ∀ (j : Nat) (d : Decl) (r : Res1), p[j]? = some d → rs[j]? = some r →
        LowC p cfg.layout.obj none d r ∧
        (func1 (Scc.Lower.Names.user d.name) (params1R d) r, rt.length + j) ∈ ir.funcs.zipIdx ∧
        ∃ (n zl zf z1 z2 zs : Nat) (zps : List Nat) (ps : List (Reg64 × Int64 × Nat)),
          let f := func1 (Scc.Lower.Names.user d.name) (params1R d) r
          let fr := frOf ir f
          (f, n) ∈ starts ir 0 ir.funcs ∧
          FrameOk fr ∧ fr.size < 2 ^ 31 ∧ fr.size % 16 = 0 ∧
          sizesAt o.prog (chkL f) 0 (5 + f.params.length) = zl :: zf :: z1 :: z2 :: zs :: zps ∧
          spills fr f.params zps = some ps ∧
          prologueIn o.prog f.name (chkL f) (labelOf f.name "entry") (Int64.ofInt fr.size)
            (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps = true ∧
          blocksOk o.prog fr n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true ∧
          (∀ ra' : Int64, ph ra'.toBitVec.toNat = ph (L.lab raL).toBitVec.toNat →
            blocksPh okPc ph (labC Λ.code.lo o.prog) (fun l => (codeLabel Λ.code.lo o.prog l).isSome)
              o.prog fr ra' n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true) ∧
          ProPh okPc ph L.lab f.name (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr)
            zl zf z1 z2 zs ps ∧
          (hasAddChk f = true →
            Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
            blkPh okPc ph (fun _ => false) L.lab (L.lab (ovfL fr) + Int64.ofNat 0) 0
              Spike.Lib.X64.Abort.Local.lb = true) := by
  intro o ir L okPc ph
  obtain ⟨rs, rt, hrs, -, hir, -⟩ := lowerAll_accepted1_x64 cfg hp hlow
  have hlab : ∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a :=
    Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i
  have hirP := lowerAll_place_ir cfg p sizes labelOffs
  have hc := fnCode1_of_placeOKAt h hirP
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h hirP)
  refine ⟨rs, rt, hrs, hir, hlab, fun j d r hd hr => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  have hmem : (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j], rt.length + j) ∈
      ir.funcs.zipIdx := by
    show _ ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs.zipIdx
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hmemF : func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j] ∈ ir.funcs := by
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    exact List.mem_of_getElem? hmem
  obtain ⟨n, hn⟩ := mem_starts ir 0 hmemF
  have hc1 := fnOk1_of_fnCode1Ok hc hn rfl
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes hc1
  obtain ⟨-, hpro, hlt, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl hz hps
  have hF := fnPhF_of_fnPhAll1 hall hn rfl
  obtain ⟨rfn, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF hz hps
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  have e := fun (blk : List (Directive × Nat))
      (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt (frOf ir (func1 (Scc.Lower.Names.user p[j].name)
        (params1R p[j]) rs[j])).size) (proL (frOf ir (func1 (Scc.Lower.Names.user p[j].name)
        (params1R p[j]) rs[j]))) zl z1 z2 zs ps) =>
    (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
      (blkLabs blk).all (fun l => (codeLabel Λ.code.lo o.prog l).isSome) = true)
  refine ⟨hrs.get j hj, hmem, n, zl, zf, z1, z2, zs, zps, ps, hn, ⟨_, _, rfl, rfl⟩, hlt, h16, hz, hps,
    hpro, hbo, fun ra' h' => blocksPh_ra h' hbp, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rfn, labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨⟨hd', lea⟩, ld1⟩, ld2⟩, cmp⟩, frr⟩ := hpp
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact lea
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact cmp
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨(hovf ha).2, hb⟩

/-! ## The cells of a segment -/

/-- **The cells of a prefix of a segment** are a prefix of its cells. -/
theorem segCells_take {cells : List (Directive × Nat)} {l : Label} {m N : Nat} (hm : m ≤ N) :
    segCells cells l m = (segCells cells l N).take m := by
  unfold segCells
  cases after l cells with
  | none => simp
  | some t => simp [List.take_take, Nat.min_eq_left hm]

/-- **The cells after an inner label of a segment**: after the `label l'`
of the segment `xs ++ .label l' :: ys` of `l`, the cells of `l'` are the
cells of `l` after it (as many of `l`'s as reach past them). -/
theorem segCells_label {cells : List (Directive × Nat)} {l l' : Label} {xs ys : List Directive}
    (h : segIn cells l (xs ++ .label l' :: ys) = true) {m N : Nat} (hm : xs.length + 1 + m ≤ N) :
    segCells cells l' m = ((segCells cells l N).drop (xs.length + 1)).take m := by
  obtain ⟨i, hi, -, hl⟩ := segIn_iff.mp h
  have hl' := labelsAt_append hl
  simp only [labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  unfold segCells
  rw [after_eq, after_eq, hi, hl'.1]
  simp only [Option.map_some, List.drop_take, List.drop_drop, List.take_take]
  rw [Nat.min_eq_left (by omega), show i + 1 + (xs.length + 1) = i + 1 + xs.length + 1 by omega]

/-- **The cells of a segment through a label**: the segment `P ++ c ::
.label l' :: Q` of `l` has the cells `W1` of `P ++ [c]` (also the cells of
`l` up to them), the label's cell, then `l'`'s cells of `Q`. -/
theorem segIn_call_cells {cells : List (Directive × Nat)} {l l' : Label} {P Q : List Directive}
    {c : Directive} (h : segIn cells l (P ++ c :: .label l' :: Q) = true) :
    ∃ W1 z, segCells cells l (P ++ c :: .label l' :: Q).length = W1 ++ (.label l', z) :: segCells cells l' Q.length ∧
      W1.map (·.1) = P ++ [c] ∧ ∀ m, m ≤ W1.length → segCells cells l m = W1.take m := by
  have hmap := segCells_map h
  have hsl := segCells_label (xs := P ++ [c]) (ys := Q) (m := Q.length)
    (N := (P ++ c :: .label l' :: Q).length) (by simpa using h) (by simp; omega)
  have htk := fun m (hm : m ≤ (P ++ c :: .label l' :: Q).length) =>
    segCells_take (cells := cells) (l := l) (m := m) hm
  generalize segCells cells l (P ++ c :: .label l' :: Q).length = T at hmap hsl htk ⊢
  rw [show P ++ c :: .label l' :: Q = (P ++ [c]) ++ .label l' :: Q by simp] at hmap
  obtain ⟨W1, W2', rfl, h1, h2⟩ := List.map_eq_append_iff.mp hmap
  obtain ⟨d, W2, rfl, hd, h3⟩ := List.map_eq_cons_iff.mp h2
  obtain ⟨d1, z⟩ := d
  simp only at hd
  subst hd
  have hlen : W1.length = P.length + 1 := by simpa using congrArg List.length h1
  have hW2 : W2.length = Q.length := by simpa using congrArg List.length h3
  refine ⟨W1, z, ?_, h1, fun m hm => ?_⟩
  · rw [hsl]
    simp [List.drop_append, hlen, ← hW2, List.drop_eq_nil_of_le (show W1.length ≤ P.length + 1 + 1 by omega)]
  · rw [htk m (by simp; omega), List.take_append_of_le_length hm]

/-! ## A call site -/

/-- A `callq` is not a label. -/
theorem isLabel_callq (g : Label) : (i64 (.call (rel g))).isLabel = false := by
  simp [i64, Scc.Emit.X64.op, Directive.isLabel]

/-- A `callq` to a label is the consumer's call. -/
theorem classify_callq (g : Label) : Spike.Lib.X64.classify (i64 (.call (rel g))) = some (.call g) := by
  simp [i64, Scc.Emit.X64.op, rel, Spike.Lib.X64.classify]

/-- **The last run of cells ending with a non-label**: cells `W1` whose
directives are `P ++ [c]`, `c` not a label: their last run (after `l`, from
no pending cells) is `zy ++ [(c, zc)]` after the last label `L`, `W1` that
run after `X`, `X` empty (`L = l`) or ending with `L`'s cell. -/
theorem runsAux_last_ins {l : Label} {W1 : List (Directive × Nat)} {P : List Directive} {c : Directive}
    (hc : c.isLabel = false) (h : W1.map (·.1) = P ++ [c]) :
    ∃ L X zy zc, (runsAux l [] W1).getLast? = some (L, zy ++ [(c, zc)]) ∧ W1 = X ++ zy ++ [(c, zc)] ∧
      X.map (·.1) ++ zy.map (·.1) = P ∧ ((X = [] ∧ L = l) ∨ ∃ X' z, X = X' ++ [(.label L, z)]) := by
  obtain ⟨L, X, ys', hlast, hW, hX⟩ := runsAux_last l [] W1
  simp only [List.reverse_nil, List.nil_append] at hW
  subst hW
  rcases List.eq_nil_or_concat ys' with rfl | ⟨zy, e, rfl⟩
  · exfalso
    rcases hX with ⟨rfl, -⟩ | ⟨X', z, rfl⟩
    · simp at h
    · simp only [List.append_nil, List.map_append, List.map_cons, List.map_nil] at h
      have := (List.append_inj' h rfl).2
      simp only [List.cons.injEq, and_true] at this
      subst this
      simp [Directive.isLabel] at hc
  · obtain ⟨e1, zc⟩ := e
    rw [List.concat_eq_append] at hlast h ⊢
    simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact ⟨L, X, zy, zc, hlast, by simp, h1, hX⟩

/-- **A call site's placement and phase facts**, from its block's
`blocksOk` and `blocksPh` (the block `b` with its stack maps `ms` after
`pre`, its instructions `is1`, the `call`, then `is2`, a map for each of
`is1` and the call), with the stack maps on: the block's code is `Xd ++ ys
++ [callq g, .L<fn>.x<k>:] ++ rest`, `Xd` empty or ending with the last
label `L` before the call (`L` the block's label if none); the run of the
`callq` is the cells `zy ++ [(callq g, zc)]` after `L` (`zy` label-free,
its directives `ys`), that run and the return label after it a segment of
`L`; the run passes `runPh`, and `L` and the runs after the return label
are in the phase of `ra`, those runs passing `runPh`. -/
theorem callSite1 {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {res : String → Bool} {fr : Frame} (hm : fr.maps = true) {ra : Int64}
    {n : Nat} {pre post : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))} {b : Scc.IR.Block}
    {ms : List (Option Scc.IR.StackMap.Entry)}
    (hok : blocksOk cells fr n (pre ++ (b, ms) :: post) = true)
    (hph : blocksPh okPc ph lab res cells fr ra n (pre ++ (b, ms) :: post) = true)
    {is1 is2 : List Scc.IR.Inst} {ds : List Scc.IR.Reg} {g : Scc.IR.Sym} {args : List Scc.IR.Operand}
    (hb : b.insts = is1 ++ .call ds g args :: is2) (hl : is1.length < ms.length) :
    ∃ (code : List Item) (n' k : Nat) (L : Label) (Xd : List Directive) (zy : List (Directive × Nat))
      (zc : Nat) (rest : List Directive),
      blockItems fr (nAfter fr n pre) b ms = .ok (code, n') ∧
      directives code = Xd ++ zy.map (·.1) ++ i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: rest ∧
      ((Xd = [] ∧ L = labelOf fr.fn b.label) ∨ ∃ X', Xd = X' ++ [.label L]) ∧
      segIn cells L (zy.map (·.1) ++ i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: rest) = true ∧
      segCells cells L (zy.length + 1) = zy ++ [(i64 (.call (rel g)), zc)] ∧
      (∀ d ∈ zy, d.1.isLabel = false) ∧
      runPh okPc ph lab res ra (L, zy ++ [(i64 (.call (rel g)), zc)]) = true ∧
      ph (lab L).toBitVec.toNat = ph ra.toBitVec.toNat ∧
      ∀ r ∈ runs s!".L{fr.fn}.x{k}" (segCells cells s!".L{fr.fn}.x{k}" rest.length),
        runPh okPc ph lab res ra r = true ∧ ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hruns⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  -- the block's code around the call
  obtain ⟨P, k, Q, hD⟩ : ∃ (P : List Directive) (k : Nat) (Q : List Directive),
      directives code = P ++ i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: Q := by
    unfold blockItems at hc
    split at hc
    · rename_i s hrun
      cases hc
      have hrun' : Scc.Cert.Code1X64.blockCode fr b ms { next := nAfter fr n pre } = .ok ((), s) := hrun
      rw [blockCode_eq] at hrun'
      obtain ⟨u, s0, hI, hT⟩ := bind_inv_E hrun'
      rw [hb] at hI
      obtain ⟨s1, s2, h1, h2, h3⟩ := instsCode_split fr _ is2 hl hI
      obtain ⟨ca, sr, k, hk⟩ := emitInst_call_inv hm h2
      obtain ⟨c3, h3o⟩ := (instsCode_pre fr is2 _).out _ _ _ h3
      obtain ⟨cT, hTo⟩ := (emitTerm_pre fr b.term).out _ _ _ hT
      obtain ⟨c1, h1o⟩ := (instsCode_pre fr is1 ms).out _ _ _ h1
      refine ⟨directives (c1.reverse ++ ca), k, directives (sr ++ c3.reverse ++ cT.reverse), ?_⟩
      rw [hTo, h3o, hk, h1o]
      simp [directives]
    · cases hc
  rw [hD] at hseg hruns
  obtain ⟨W1, z, hT, hW1, htk⟩ := segIn_call_cells hseg
  rw [hT, runs, runsAux_append_label] at hruns
  obtain ⟨L, X, zy, zc, hlast, rfl, rfl, hX⟩ :=
    runsAux_last_ins (l := labelOf fr.fn b.label) (isLabel_callq g) hW1
  have hmemL := List.mem_of_getLast? hlast
  obtain ⟨hrL, hphL⟩ := hruns _ (List.mem_append_left _ hmemL)
  have hnl := runsAux_noLabel _ [] _ (by simp) _ hmemL
  refine ⟨code, n', k, L, X.map (·.1), zy, zc, Q, hc, by simp [hD], ?_, ?_, ?_,
    fun d hd => hnl d (List.mem_append_left _ hd), hrL, hphL,
    fun r hr => hruns r (List.mem_append_right _ hr)⟩
  · rcases hX with ⟨rfl, rfl⟩ | ⟨X', z', rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨X'.map (·.1), by simp⟩
  · rcases hX with ⟨rfl, rfl⟩ | ⟨X', z', rfl⟩
    · simpa using hseg
    · exact segIn_label (xs := X'.map (·.1)) (by simpa using hseg)
  · rcases hX with ⟨rfl, rfl⟩ | ⟨X', z', rfl⟩
    · rw [htk _ (by simp), List.take_of_length_le (by simp)]
      simp
    · rw [segCells_label (xs := X'.map (·.1)) (by simpa using hseg) (N := (X' ++ [(Directive.label L, z')] ++ zy ++
          [(i64 (.call (rel g)), zc)]).length) (by simp; omega), htk _ (Nat.le_refl _),
        List.take_of_length_le (Nat.le_refl _)]
      rw [show X' ++ [(Directive.label L, z')] ++ zy ++ [(i64 (.call (rel g)), zc)] =
        (X' ++ [(Directive.label L, z')]) ++ (zy ++ [(i64 (.call (rel g)), zc)]) by simp,
        List.drop_left' (by simp), List.take_of_length_le (by simp)]

/-- **A call site's `callq` placed**: the run `zy ++ [(callq g, zc)]` of
cells after `L` (`zy` label-free) is code at `L` (`blockAt`), the return
label `spK` follows `L` after it (`labelGap`), and the `callq` at its pc
passes `blkPh` (no dead target). -/
theorem call_blockAt {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {res : String → Bool} {ra : Int64} {L spK g : Label}
    {zy : List (Directive × Nat)} {zc : Nat} {S : List Directive}
    (hseg : segIn cells L (zy.map (·.1) ++ i64 (.call (rel g)) :: .label spK :: S) = true)
    (hcells : segCells cells L (zy.length + 1) = zy ++ [(i64 (.call (rel g)), zc)])
    (hzy : ∀ d ∈ zy, d.1.isLabel = false)
    (hrun : runPh okPc ph lab res ra (L, zy ++ [(i64 (.call (rel g)), zc)]) = true) :
    blockAt cells L 0 0 (zy ++ [(i64 (.call (rel g)), zc)]) = true ∧
    labelGap cells L spK (zy.length + 1) (cellOff (zy ++ [(i64 (.call (rel g)), zc)]) (zy.length + 1)) = true ∧
    blkPh okPc ph (fun _ => false) lab
      (lab L + Int64.ofNat (cellOff (zy ++ [(i64 (.call (rel g)), zc)]) zy.length)) ra
      [(i64 (.call (rel g)), zc)] = true := by
  have hins : (zy.map (·.1) ++ [i64 (.call (rel g))]).all (fun d => !d.isLabel) = true := by
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨?_, by simp [isLabel_callq]⟩
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
    simp [hzy d' hd']
  have hseg' : segIn cells L ((zy.map (·.1) ++ [i64 (.call (rel g))]) ++ .label spK :: S) = true := by
    simpa using hseg
  obtain ⟨t, ht, -, hbl⟩ := blockAt_of_segIn (xs := []) (ys := zy.map (·.1) ++ [i64 (.call (rel g))])
    (zs := .label spK :: S) (by simpa using hseg) rfl hins
  have hseg2 : segCells cells L (zy.length + 1) = t.take (zy.length + 1) := by
    simp [segCells, ht]
  obtain ⟨t', ht', hgap⟩ := labelGap_of_segIn hseg' hins
  rw [ht] at ht'; cases ht'
  refine ⟨?_, ?_, ?_⟩
  · simpa [cellOff, ← hseg2, hcells] using hbl
  · have hc : cellOff t (zy.length + 1) = cellOff (zy ++ [(i64 (.call (rel g)), zc)]) (zy.length + 1) := by
      rw [← hcells, hseg2]; simp [cellOff, List.take_take]
    simpa [hc] using hgap
  · simp only [runPh, Bool.and_eq_true] at hrun
    have h2 : runPhB okPc ph lab (lab L) ra (zy ++ [(i64 (.call (rel g)), zc)] ++ []) = true := by
      simpa using hrun.2
    have := blkPh_of_runPhB (xs := zy) (ys := [(i64 (.call (rel g)), zc)]) (zs := []) h2
      (by simp [classify_callq])
    simpa using this

end Spike.Lib.LowerX64
