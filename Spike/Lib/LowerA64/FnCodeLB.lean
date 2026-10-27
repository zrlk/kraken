/-
**Each `Accepted2` code block's calls at a position off the write abort**
(AArch64): `Spike/Lib/LowerA64/FnCodeL.lean`'s `CodeC2` and `BlocksCodeC2`
at `CdCL` with the call predicate `BlC2L` rather than `BlC2`: each call's
`bl` is after a label off `abLabs` (the block's or a return label, the
segment's label of `codeC2L_of_seg`), so its pc is a position off the write
abort (`PosOff`). Additive twins of `FnCodeL.lean`'s producers.

- `BlC2L`, `BlC2L.toBlC2`, `BlC2L.posOff`: `BlC2` with the `bl` at a
  `PosOff`.
- `codeC2L_of_segB`, `codeC2L_blockB`, `blocksCodeC2LB`, `entryCodeC2LB`,
  `fnCodeC2LB`, `fnCodeC2LB_ofPlaceOK`: `FnCodeL.lean`'s chain at `BlC2L`.
-/
import Spike.Lib.LowerA64.FnCodeL

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

set_option linter.unusedSimpArgs false

/-! ## Calls at a position off the write abort -/

/-- **A call's `bl g` at `pc`, a position off the write abort**: `BlC2`
and `PosOff`. -/
def BlC2L (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (cx : FnCtx)
    (ra : Int64) (pc : Int64) (g : Label) (k : Nat) : Prop :=
  BlC2 prog okPc ph lab cx ra pc g k ∧ PosOff prog lab pc

theorem BlC2L.toBlC2 {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat} (h : BlC2L prog okPc ph lab cx ra pc g k) :
    BlC2 prog okPc ph lab cx ra pc g k := h.1

/-- **A `BlC2L` call's `bl` is at a position off the write abort.** -/
theorem BlC2L.posOff {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat} (h : BlC2L prog okPc ph lab cx ra pc g k) :
    PosOff prog lab pc := h.2

/-! ## The producers at `BlC2L` -/

section Code

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **`codeC2L_of_seg` at `BlC2L`**: each call's `bl` after the segment's label
or a return label, both off `abLabs`, so at a position off the write abort. -/
theorem codeC2L_of_segB (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {tm : Scc.IR.Term} (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (l : Label) (c1 c2 : List Item) (xs zs : List Directive),
      l ∉ abLabs ∧ WcL l → (∀ i ∈ is, InstC2 i) → instsItems cx k is = .ok c1 →
      cx.term (k + is.length) tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) k (lab l + Int64.ofNat (4 * xs.length))
        is tm
  | [], k, l, c1, c2, xs, zs, hl, _, hi, ht, hseg, hx, hph, _ => by
    simp only [instsItems] at hi
    cases hi
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hseg hph ht
    exact Or.inr ⟨c2, ht, cdCL_at hl hseg hx (term2_allIns htm ht) hph⟩
  | i :: is, k, l, c1, c2, xs, zs, hl, hs, hi, ht, hseg, hx, hph, hrl => by
    have hs' := List.forall_mem_cons.mp hs
    simp only [instsItems] at hi
    rw [show k + (i :: is).length = k + 1 + is.length by simp; omega] at ht
    cases hci : cx.inst k i with
    | error e => simp [hci, bind, Except.bind] at hi
    | ok ci =>
      cases hc1 : instsItems cx (k + 1) is with
      | error e => simp [hci, hc1, bind, Except.bind] at hi
      | ok c1' =>
        simp [hci, hc1, bind, Except.bind, pure, Except.pure] at hi
        subst hi
        have hD : directives (ci ++ c1' ++ c2) = directives ci ++ directives (c1' ++ c2) := by
          rw [List.append_assoc, directives_append]
        rw [hD] at hseg hph hrl
        -- the rest after a call, from its return label
        have hcall : ∀ {lw ls : List Item} {g : Label}, AllIns lw → AllIns ls →
            directives ci = directives lw ++ blD g :: .label (cx.local s!"sp{k}") :: directives ls →
            CdCL prog okPc ph lab ra (lab l + Int64.ofNat (4 * xs.length)) (directives lw) ∧
            BlC2L prog okPc ph lab cx ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length)) g k ∧
            CdCL prog okPc ph lab ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4)
              (directives ls) ∧
            CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) (k + 1)
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4 +
                Int64.ofNat (4 * (directives ls).length)) is tm := by
          intro lw ls g hAw hAs hd
          rw [hd] at hseg hph hrl
          obtain ⟨-, h2, -, hsp, hseg2, hrs, hrl2⟩ := callSeg (D := directives (c1' ++ c2)) hgap
            (by simpa only [List.append_assoc, List.cons_append] using hseg) hx hAw hAs
            (headIns_append_all hAs (insts2_head hm (term2_head htm ht) is (k + 1) c1' hs'.2 hc1))
            (by simpa only [List.append_assoc, List.cons_append] using hph)
            (by simpa only [List.append_assoc, List.cons_append] using hrl)
          have hAs' : (directives ls).all isIns = true := hAs
          have hK := local_wc hfi hun s!"sp{k}"
          have hb := blockAt_of_segIn (xs := xs ++ directives lw) (ys := [blD g])
            (zs := .label (cx.local s!"sp{k}") :: (directives ls ++ directives (c1' ++ c2) ++ zs))
            (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg)
            (by rw [List.all_append, hx]; exact hAw) rfl
          have hpo := posOff_of_blockAt (lab := lab) hb hl.1 (i := 0) (by simp)
          rw [Nat.add_zero, List.length_append, ofNat4_add] at hpo
          refine ⟨?_, ⟨h2, hpo⟩, ?_, ?_⟩
          · -- the arguments' loads, at `l`
            exact cdCL_at
              (zs := blD g :: .label (cx.local s!"sp{k}") :: (directives ls ++ directives (c1' ++ c2) ++ zs))
              hl (by simpa only [List.append_assoc, List.cons_append] using hseg) hx hAw
              (by simpa only [List.append_assoc, List.cons_append] using hph)
          · -- the results' stores, at the return label
            have := cdCL_at (l := cx.local s!"sp{k}") (xs := []) (zs := directives (c1' ++ c2) ++ zs) hK
              (by simpa only [List.append_assoc, List.nil_append] using hseg2) rfl hAs'
              (by
                intro r hr
                rw [List.reverse_nil, runsAux_shift _ _ _ _ (noLabel_of_isIns hAs'), List.append_nil] at hr
                exact hrs r (by simpa only [List.append_assoc] using hr))
            rwa [List.length_nil, ofNat4_zero, hsp] at this
          · have := codeC2L_of_segB hm hgap hfi hun htm is (k + 1) _ c1' c2 (directives ls) zs hK hs'.2 hc1 ht hseg2 hAs
              hrs hrl2
            rwa [hsp] at this
        by_cases hc : Spike.Lib.LowerShape.isCall i = false
        · -- an instruction other than a call: instructions only
          have hA : (directives ci).all isIns = true := inst2_allIns hs'.1 hc hci
          refine Or.inl ⟨hc, ci, hci, ?_, ?_⟩
          · exact cdCL_at (zs := directives (c1' ++ c2) ++ zs) hl (by simpa only [List.append_assoc] using hseg) hx hA
              (by simpa only [List.append_assoc] using hph)
          · have hxA : (xs ++ directives ci).all isIns = true := by rw [List.all_append, hx, hA]; rfl
            have := codeC2L_of_segB hm hgap hfi hun htm is (k + 1) l c1' c2 (xs ++ directives ci) zs hl hs'.2 hc1 ht
              (by simpa only [List.append_assoc] using hseg) hxA
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hph)
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hrl)
            rwa [List.length_append, ofNat4_add] at this
        · cases hs'.1 with
          | call d g w =>
            obtain ⟨lw, ls, hw, hsr, hAw, hAs, hd⟩ := inst_call1_inv hm hci
            obtain ⟨h1, h2, h3, h4⟩ := hcall hAw hAs hd
            exact .inr (.inl ⟨d, g, w, lw, ls, rfl, hw, hsr, h1, h2, h3, h4⟩)
          | newBuf p h kv u =>
            obtain ⟨ca, sr, hca, hsr, hd⟩ := inst_call_inv hm hci
            rw [callArgs_eq (by simp)] at hca
            rw [setResults_one] at hsr
            have hAa : AllIns ca := by rw [getArgs_eq (by simp)] at hca; exact allIns_getOps hca
            obtain ⟨h1, h2, h3, h4⟩ := hcall hAa (allIns_setReg hsr) hd
            exact .inr (.inr (.inl ⟨p, h, kv, u, ca, sr, rfl, hca, hsr, h1, h2, h3, h4⟩))
          | print a0 a1 =>
            obtain ⟨ca, sr, hca, hsr, hd⟩ := inst_call_inv hm hci
            rw [callArgs_eq (by simp)] at hca
            rw [setResults_nil] at hsr
            cases hsr
            have hAa : AllIns ca := by rw [getArgs_eq (by simp)] at hca; exact allIns_getOps hca
            obtain ⟨h1, h2, -, h4⟩ := hcall hAa allIns_nil hd
            refine .inr (.inr (.inr ⟨a0, a1, ca, rfl, hca, h1, h2, ?_⟩))
            simpa [directives] using h4
          | _ => exact absurd rfl hc

/-- **`codeC2L_block` at `BlC2L`.** -/
theorem codeC2L_blockB (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, Scc.Cert.Link.A64.codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {b : Scc.IR.Block} (hs : Spike.Lib.LowerShape.BlockC2 b) {k : Nat} {l : Label} (hl : l ∉ abLabs ∧ WcL l)
    {code : List Item}
    (hc : Scc.Cert.Code1A64.blockItems cx k b = .ok code) (hseg : segIn prog l (directives code) = true)
    (hph : ∀ r ∈ Scc.Cert.Ph1A64.runs l (directives code),
      Scc.Cert.Ph1A64.runPh okPc ph (labC lo prog)
          (fun l => (Scc.Cert.Link.A64.codeOf lo prog l).isSome) ra r = true ∧
        ph (labC lo prog r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) k (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [Scc.Cert.Code1A64.blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      have := codeC2L_of_segB (okPc := okPc) (ph := ph) (ra := ra) hm hgap hfi hun hs.2 b.insts k l c1 c2 [] []
        hl hs.1 hi ht (by simpa using hseg) rfl
        (fun r hr => by
          have h' := (hph r (by simpa [Scc.Cert.Ph1A64.runs] using hr)).1
          simp only [Scc.Cert.Ph1A64.runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
          rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
          exact hrun)
        (fun r hr => by
          have h' := hph r (by simpa [Scc.Cert.Ph1A64.runs] using hr)
          simp only [Scc.Cert.Ph1A64.runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
          rw [labC_eq hlab hres] at hp
          exact hp)
      simpa [ofNat4_zero] using this

end Code

/-! ## Each function's code -/

section Place

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **`blocksCodeC2L` at `BlC2L`.** -/
theorem blocksCodeC2LB (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, BlockC2 b) :
    BlocksCodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, _, hl, codeC2L_blockB hm hgap hlab hfi hun (hs b hb) (blockLabel_wc hfi hun hl) hc hseg hr⟩

/-- **`entryCodeC2L` at `BlC2L`.** -/
theorem entryCodeC2LB (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label}
    (hent : cx.blockLabel b.label = .ok entry) (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : BlockC2 b) :
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) 0 (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact codeC2L_blockB hm hgap hlab hfi hun hs (blockLabel_wc hfi hun hent) hc hseg hr

/-- **`fnCodeC2L` at `BlC2L`.** -/
theorem fnCodeC2LB (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg}
    {entry : Label} (hent : cx.blockLabel "entry" = .ok entry)
    (hok : blocksOk prog cx 0 (func2 name ps sc hq r).blocks = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0
      (func2 name ps sc hq r).blocks = true) :
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) 0 (lab entry) r.insts r.term ∧
      BlocksCodeC2 cx (CdCL prog okPc ph lab ra) (BlC2L prog okPc ph lab cx ra) lab r.blocks :=
  ⟨entryCodeC2LB (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hfi hun hent hok hph
    ⟨hs.1, hs.2.1⟩,
    blocksCodeC2LB (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hfi hun hok hph hs.2.2⟩

end Place

/-- **`fnCodeC2L_ofPlaceOK` at `BlC2L`**: each call's `bl` at a position off
the write abort. -/
theorem fnCodeC2LB_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
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
            CodeC2 cx (CdCL o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') 0
                (Ly.lab entry) w.r.insts w.r.term ∧
              BlocksCodeC2 cx (CdCL o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') Ly.lab
                w.r.blocks := by
  intro o ir Ly ra
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h i
  have hrt : rt.length = 18 := by
    obtain ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK2 h
    obtain ⟨ws', rt', hws', hrt', -, hir', -⟩ := lowerAll_accepted2_a64 cfg hp hlow
    have e := congrArg (fun q => q.funcs.length) (hir.symm.trans hir')
    simp only [Scc.Lower.Inv.progOf, List.length_append, funcs2, List.length_zipWith, hws.1, hws'.1,
      Nat.min_self] at e
    rw [← rtFuncs_length hrt']
    omega
  refine ⟨ws, rt, hws, hir, hrt, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, -, -, -, entry, -, hent, -, -, hbo, hbp, -⟩ := H j d w hd hw
  intro f cx
  have hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16 := by
    have e : cx.fi = rt.length + j := rfl
    omega
  have hm : cx.maps = true := by
    show (Scc.Lower.A64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.A64.Rt.rS0 Ly)
  have hgap : ∀ a b n, labelGap o.prog a b n = true → Ly.lab b = Ly.lab a + Int64.ofNat (4 * n) :=
    fun _ _ _ hg => by rw [← hI.labOk]; exact Scc.Cert.Rt.A64.label_labelGap hI.lays hg
  exact ⟨hL, hm, entry, hent, fun ra' hra => fnCodeC2LB hm hgap (lab_ofPlaceOK h i) hfi ⟨_, rfl⟩
    (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2) hent hbo (hbp ra' hra)⟩

/-- info: 'Spike.Lib.LowerA64.codeC2L_of_segB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2L_of_segB

/-- info: 'Spike.Lib.LowerA64.fnCodeC2LB_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2LB_ofPlaceOK

end Spike.Lib.LowerA64
