/-
**Each `Accepted2` code block's calls at a position off the write abort**
(x86-64): `Spike/Lib/LowerX64/FnCodeL.lean`'s `CodeC2` and `BlocksCodeC2`
at `CdCL` with the call predicate `BlC2L` rather than `BlC2`: each call's
`callq` is after a label off `abLabs` (the block's or a return label, the
segment's label of `callSegX`), so its pc is a position off the write abort
(`PosOff`). Additive twins of `Spike/Lib/LowerX64/BlocksC2Seg.lean`'s and
`FnCodeL.lean`'s producers.

- `BlC2Q`, `BlC2Q.toBlC2`, `BlC2L`, `BlC2L.posOff`: `BlC2` with the
  `callq` after a label of `Q` (off `abLabs`, so at a `PosOff`).
- `callSegXQ`, `codeC2_of_segQB`, `codeC2_blockQB`: `callSegX`,
  `codeC2_of_segQ`, `codeC2_blockQ` at `BlC2Q Q`.
- `codeC2_of_segLB`, `codeC2L_blockB`, `blocksCodeC2LB`, `entryCodeC2LB`,
  `fnCodeC2LB`, `fnCodeC2LB_of_fnPh2`, `fnCodeC2LB_ofPlaceOK`: `FnCodeL.lean`'s
  chain at `BlC2L`.
-/
import Spike.Lib.LowerX64.FnCodeL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (S E Item Frame emitInst emitTerm ld st ins labelOf cmpAB directives i64 rel argRegs retRegs
  callArgs safepoint)
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Rt.X64 (blockAt labelGap after after_eq InRunB inRunB_of_blockAt)
open Scc.Cert.Code1X64 (segIn segIn_iff segIn_label blockAt_of_segIn labelGap_of_segIn blockItems blocksOk
  blocksOk_block)
open Scc.Cert.Ph1X64 (runsAux runPhB blkPh_of_runPhB runs runPh blocksPh blocksPh_blockPh segCells)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.LowerShape (isCall InstC2 TermC2 newBufCall xchgLoad xchgStore func2 paramsR BlockC2)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2)
open Spike.Lib.X64.AllocG (abLabs)

set_option linter.unusedSimpArgs false

/-! ## Calls after a label of `Q` -/

/-- **A call's `callq` after a label of `Q`**: `BlC2`, the `callq`'s pc
`off` bytes into the run of a label `L` of `Q` (`InRunB`). -/
def BlC2Q (Q : Label → Prop) (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat)
    (lab : Label → Int64) (fr : Scc.Emit.X64.Frame) (ra : Int64) (pc : Int64) (zc : Nat) (g : Label) (k : Nat) :
    Prop :=
  BlC2 cells okPc ph lab fr ra pc zc g k ∧ ∃ L off, Q L ∧ InRunB cells L off ∧ lab L + Int64.ofNat off = pc

theorem BlC2Q.toBlC2 {Q : Label → Prop} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2Q Q cells okPc ph lab fr ra pc zc g k) : BlC2 cells okPc ph lab fr ra pc zc g k := h.1

/-- **A call's `callq` after a label off `abLabs`** (`BlC2Q` at `abLabs`'
complement). -/
abbrev BlC2L (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (fr : Scc.Emit.X64.Frame) (ra : Int64) : Int64 → Nat → Label → Nat → Prop :=
  BlC2Q (fun L => L ∉ abLabs ∧ WcL L) cells okPc ph lab fr ra

/-- **A `BlC2L` call's `callq` is at a position off the write abort.** -/
theorem BlC2L.posOff {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC2L cells okPc ph lab fr ra pc zc g k) : PosOff cells lab pc :=
  let ⟨_, L, off, hL, hr, he⟩ := h
  ⟨L, off, hr, hL.1, he⟩

/-! ## The producers at `BlC2Q` -/

section Code

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64}

/-- **A call in a segment, its `callq` at a label of `Q`** (`callSegX` at `BlC2Q Q`). -/
theorem callSegXQ (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {Q : Label → Prop} {l : Label} (hQ : Q l) {t : List (Directive × Nat)} (ht : after l cells = some t)
    {xs zs R : List Directive}
    {lw : List Item} {g : Label} {k : Nat}
    (hseg : segIn cells l (xs ++ directives lw ++
      (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)) = true)
    (hx : xs.all (fun d => !d.isLabel) = true) (aw : AllIns lw) (hR : HeadIns R)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take
      (directives lw ++ (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take
      (directives lw ++ (i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{k}" :: R ++ zs)).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    ∃ zl zc, zl.length = (directives lw).length ∧
      CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) ((directives lw).zip zl) ∧
      BlC2Q Q cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum) zc g k ∧
      lab s!".L{fr.fn}.x{k}" = lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum + Int64.ofNat zc ∧
      after s!".L{fr.fn}.x{k}" cells = some (t.drop ((xs ++ directives lw).length + 1 + 1)) ∧
      segIn cells s!".L{fr.fn}.x{k}" (R ++ zs) = true ∧
      (∀ r ∈ runsAux s!".L{fr.fn}.x{k}" [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) ∧
      (∀ r ∈ runsAux s!".L{fr.fn}.x{k}" [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) := by
  -- the first run is after `l`, in the phase of `ra`
  have hl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := by
    obtain ⟨y, hy⟩ := runsAux_head l _ _
    exact hrl _ hy
  have aw' : (directives lw).all (fun d => !d.isLabel) = true := aw
  generalize hK : s!".L{fr.fn}.x{k}" = spK at hseg hph hrl ⊢
  generalize hC : i64 (.call (rel g)) = C at hseg hph hrl
  have hCl : C.isLabel = false := by rw [← hC]; exact isLabel_callq _
  -- the arguments' loads
  have hsegA : segIn cells l (xs ++ directives lw ++ (C :: .label spK :: R ++ zs)) = true := hseg
  have hphA := hph
  have hrlA := hrl
  obtain ⟨zl, hzl, hcdl, hpcl⟩ := cdCQ_at hQ ht (c := directives lw)
    (by simpa only [List.append_assoc] using hsegA) hx aw'
    (by simpa only [List.append_assoc] using hphA)
  have hSA := slice_noLabel (seg_slice ht hsegA) aw'
  rw [List.length_append, runs_step hSA, ← List.length_append] at hphA hrlA
  have hx1 : (xs ++ directives lw).all (fun d => !d.isLabel) = true := by
    rw [List.all_append, hx, aw']; rfl
  -- the `callq`
  have hsegB : segIn cells l ((xs ++ directives lw) ++ [C] ++ (.label spK :: R ++ zs)) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
  obtain ⟨t', ht', hY1, hb⟩ := blockAt_of_segIn hsegB hx1 (by simp [hCl])
  rw [ht] at ht'
  cases ht'
  obtain ⟨⟨C', zc⟩, hS1⟩ : ∃ p, (t.drop (xs ++ directives lw).length).take 1 = [p] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hY1)
  rw [List.length_singleton, hS1] at hY1 hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hY1
  subst hY1
  have hx2 : ((xs ++ directives lw) ++ [C']).all (fun d => !d.isLabel) = true := by
    rw [List.all_append, hx1]; simp [hCl]
  have hsegL : segIn cells l (((xs ++ directives lw) ++ [C']) ++ .label spK :: (R ++ zs)) = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
  have hRS : segIn cells spK (R ++ zs) = true := segIn_label hsegL
  have hin := inRunB0_of_segIn hRS hR
  obtain ⟨t'', ht'', hg⟩ := labelGap_of_segIn hsegL hx2
  rw [ht] at ht''
  cases ht''
  have hoff : cellOff t ((xs ++ directives lw) ++ [C']).length = cellOff t (xs ++ directives lw).length + zc := by
    rw [List.length_append, List.length_singleton, cellOff_add, hS1]; simp
  rw [hoff, List.length_append, List.length_singleton] at hg
  -- the runs: the one through the `callq`, then those after the return label
  have hph2 := hphA
  have hrl2 := hrlA
  rw [show (C' :: .label spK :: R ++ zs).length = 1 + (.label spK :: R ++ zs).length by
    simp; omega, runs_step (by rw [hS1]; simp [hCl])] at hph2 hrl2
  have hYL := seg_slice ht (xs := (xs ++ directives lw) ++ [C']) (ys := [.label spK])
    (zs := R ++ zs) (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
      using hsegA)
  obtain ⟨⟨dl, z0⟩, hL1⟩ : ∃ p, (t.drop ((xs ++ directives lw) ++ [C']).length).take 1 = [p] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hYL)
  rw [List.length_singleton, hL1] at hYL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hYL
  subst hYL
  rw [List.length_append, List.length_singleton] at hL1
  have htk : t.take ((xs ++ directives lw).length + 1) = t.take (xs ++ directives lw).length ++ [(C', zc)] := by
    rw [List.take_add, hS1]
  have hsplit : (t.drop ((xs ++ directives lw).length + 1)).take (1 + (R ++ zs).length) =
      (t.drop ((xs ++ directives lw).length + 1)).take 1 ++
        (t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length := by
    rw [List.take_add, List.drop_drop]
  rw [show (Directive.label spK :: R ++ zs).length = 1 + (R ++ zs).length by
    simp; omega, hsplit, hL1, htk] at hph2 hrl2
  simp only [List.singleton_append, runsAux, List.mem_cons, forall_eq_or_imp] at hph2 hrl2
  obtain ⟨hfirst, hafter⟩ := hph2
  obtain ⟨-, hrafter⟩ := hrl2
  simp only [List.reverse_reverse] at hfirst
  have hblk := blkPh_of_runPhB (xs := t.take (xs ++ directives lw).length) (ys := [(C', zc)]) (zs := [])
    (by simpa using hfirst) (by rw [← hC]; simp [classify_callq])
  have e1 : cellOff (t.take (xs ++ directives lw).length ++ [(C', zc)] ++ [])
      (t.take (xs ++ directives lw).length).length = cellOff t (xs ++ directives lw).length := by
    unfold cellOff
    rw [List.append_assoc, List.take_left' rfl]
  rw [e1] at hblk
  -- the `callq`'s pc in the phase of `ra`
  have hpcph : ph (lab l + Int64.ofNat (cellOff t (xs ++ directives lw).length)).toBitVec.toNat =
      ph ra.toBitVec.toNat := by
    have hf : runPhB okPc ph lab (lab l) ra (t.take (xs ++ directives lw).length ++ [(C', zc)]) = true := by
      simpa using hfirst
    have h0 := (Scc.Cert.Ph1X64.runPhB_get (k := (t.take (xs ++ directives lw).length).length) hf (by simp)).2.1
    have e2 : cellOff (t.take (xs ++ directives lw).length ++ [(C', zc)]) (t.take (xs ++ directives lw).length).length =
        cellOff t (xs ++ directives lw).length := by
      unfold cellOff
      rw [List.take_left' rfl]
    rw [e2, hl] at h0
    exact h0
  -- the return label's address
  have hsp : lab spK = lab l + Int64.ofNat (cellOff t (xs ++ directives lw).length) + Int64.ofNat zc := by
    rw [hgap _ _ _ _ hg, Int64.ofNat_add, Int64.add_assoc]
  have ht2 := after_label hsegL ht
  rw [List.length_append, List.length_singleton] at ht2
  -- the return label in the phase of `ra`
  have hrlS : ∀ r ∈ runsAux spK [] ((t.drop ((xs ++ directives lw).length + 1 + 1)).take (R ++ zs).length),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
    simpa [Nat.add_assoc] using hrafter
  have hspk : ph (lab spK).toBitVec.toNat = ph ra.toBitVec.toNat := by
    obtain ⟨y, hy⟩ := runsAux_head spK _ _
    exact hrlS _ hy
  subst hC hK
  rw [← hpcl] at hblk hpcph
  refine ⟨zl, zc, hzl, hcdl, ⟨⟨⟨l, (xs ++ directives lw).length, cellOff t (xs ++ directives lw).length, hpcl.symm,
    hb, hg, hblk, by rw [hpcl, ← hsp]; exact hspk⟩, hpcph, hin⟩, l, cellOff t (xs ++ directives lw).length, hQ,
    by simpa using inRunB_of_blockAt hb (i := 0) (by simp), hpcl.symm⟩, by rw [hpcl]; exact hsp, ht2, hRS,
    by simpa [Nat.add_assoc] using hafter, hrlS⟩


/-- **`codeC2_of_segQ` at `BlC2Q Q`**: each call's `callq` after a label of `Q`. -/
theorem codeC2_of_segQB (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {tm : Scc.IR.Term} (htm : TermC2 tm) {Q : Label → Prop} (hQK : ∀ k : Nat, Q s!".L{fr.fn}.x{k}") :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (code : List Item)
      (l : Label) (t : List (Directive × Nat)) (xs zs : List Directive), Q l →
      (∀ i ∈ is, InstC2 i) → is.length ≤ ms.length →
      (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s') → s'.out = code.reverse ++ s.out →
      after l cells = some t → segIn cells l (xs ++ directives code ++ zs) = true →
      xs.all (fun d => !d.isLabel) = true →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2Q Q cells okPc ph lab fr ra) s.next
        (lab l + Int64.ofNat (cellOff t xs.length)) is tm
  | [], ms, s, s', code, l, t, xs, zs, hQ, _, _, h, hD, ht, hseg, hx, hph, _ => by
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_nil] at hI
    cases hI
    obtain ⟨ct, et, act, -⟩ := emitTerm2_allIns htm hT
    rw [et] at hT
    cases hT
    have hc : code = ct := by
      have h1 : code.reverse ++ s.out = ct.reverse ++ s.out := hD.symm
      have h2 := List.append_cancel_right h1
      rw [← List.reverse_reverse code, h2, List.reverse_reverse]
    subst hc
    obtain ⟨zc, hz, hcd, -⟩ := cdCQ_at hQ ht hseg hx act hph
    exact Or.inr ⟨code, zc, et, hz, hcd⟩
  | i :: is, ms, s, s', code, l, t, xs, zs, hQ, hs, hms, h, hD, ht, hseg, hx, hph, hrl => by
    obtain ⟨m, ms, rfl⟩ : ∃ m ms', ms = m :: ms' := by
      cases ms with
      | nil => simp at hms
      | cons m ms' => exact ⟨m, ms', rfl⟩
    have hs' := List.forall_mem_cons.mp hs
    have hms' : is.length ≤ ms.length := by simp at hms; omega
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_cons] at hI
    obtain ⟨u2, s2, hE, hI⟩ := bind_inv hI
    have hrest : (do instsCode fr is ms; emitTerm fr tm) s2 = .ok ((), s') := by
      rw [bind_ok hI]; exact hT
    obtain ⟨c', hc'⟩ := (Pre.bind' (instsCode_pre fr is ms) fun _ => emitTerm_pre fr tm).out _ _ _ hrest
    have hD' : s'.out = c'.reverse.reverse ++ s2.out := by rw [List.reverse_reverse]; exact hc'
    by_cases hc : isCall i = false
    · -- an instruction other than a call: label-free items
      obtain ⟨ci, ei, ai⟩ := emitInst2_allIns hs'.1 hc hE
      rw [ei] at hE
      cases hE
      have hcode : code = ci ++ c'.reverse := by
        have h1 : code.reverse ++ s.out = (c' ++ ci.reverse) ++ s.out := by
          rw [← hD, hc', List.append_assoc]
        have h2 := List.append_cancel_right h1
        rw [← List.reverse_reverse code, h2]; simp
      subst hcode
      have hdd : directives (ci ++ c'.reverse) = directives ci ++ directives c'.reverse := dirs_append _ _
      rw [hdd] at hseg hph
      have hseg1 : segIn cells l (xs ++ directives ci ++ (directives c'.reverse ++ zs)) = true := by
        simpa only [List.append_assoc] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        rw [hdd] at hrl
        simpa only [List.append_assoc] using hrl
      obtain ⟨zc, hz, hcd, hpc⟩ := cdCQ_at hQ ht hseg1 hx ai hph1
      have hS := slice_noLabel (seg_slice ht hseg1) ai
      rw [List.length_append, runs_step hS] at hph1 hrl1
      have := codeC2_of_segQB hm hgap htm hQK is ms _ s' c'.reverse l t (xs ++ directives ci) zs hQ hs'.2 hms' hrest
        hD' ht
        (by simpa only [List.append_assoc] using hseg1) (by rw [List.all_append, hx, ai]; rfl)
        (by rw [List.length_append]; exact hph1) (by rw [List.length_append]; exact hrl1)
      refine Or.inl ⟨hc, ci, zc, by rw [emitInst_sm hc none m]; exact ei, hz, hcd, ?_⟩
      rw [hpc]
      exact this
    · -- a call: its arguments' loads `lw`, `callq g`, the return label, its stores `sr`
      have hcall : ∀ (lw sr : List Item) (g : Label) (mp : List (String × List Int × List Int)), AllIns lw →
          AllIns sr → s2 = { out := (lw ++ [Item.d (i64 (.call (rel g))),
            Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr).reverse ++ s.out, next := s.next + 1, maps := mp } →
          ∃ zl zc zr, zl.length = (dirs lw).length ∧
            CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) ((dirs lw).zip zl) ∧
            BlC2Q Q cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum) zc g
              s.next ∧
            zr.length = (dirs sr).length ∧
            CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum +
              Int64.ofNat zc) ((dirs sr).zip zr) ∧
            CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2Q Q cells okPc ph lab fr ra) (s.next + 1)
              (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum + Int64.ofNat zc +
                Int64.ofNat zr.sum) is tm := by
        intro lw sr g mp aw asr hs2
        subst hs2
        have hcode : code = (lw ++ [Item.d (i64 (.call (rel g))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr) ++
            c'.reverse := by
          have h1 : code.reverse ++ s.out = (c' ++ (lw ++ [Item.d (i64 (.call (rel g))),
              Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr).reverse) ++ s.out := by
            rw [← hD, hc']; simp
          have h2 := List.append_cancel_right h1
          rw [← List.reverse_reverse code, h2]; simp
        subst hcode
        have hhead : HeadIns (directives sr ++ directives c'.reverse) :=
          headIns_append_all asr (code2_head hm htm is ms _ s' c'.reverse hs'.2 hms' hrest hD')
        have asr' : (directives sr).all (fun d => !d.isLabel) = true := asr
        generalize hDd : directives c'.reverse = D at hseg hph hrl hhead
        have hdd : directives ((lw ++ [Item.d (i64 (.call (rel g))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++ sr) ++
            c'.reverse) = directives lw ++ i64 (.call (rel g)) :: .label s!".L{fr.fn}.x{s.next}" ::
              (directives sr ++ D) := by
          rw [← hDd]
          simp only [directives_eq_dirs, dirs_append, List.append_assoc]
          rfl
        rw [hdd] at hseg hph hrl
        obtain ⟨zl, zc, hzl, hcdl, hbl, hsp, ht2, hRS, hrs, hrls⟩ := callSegXQ (R := directives sr ++ D) hgap hQ ht
          (by simpa only [List.append_assoc, List.cons_append] using hseg) hx aw hhead
          (by simpa only [List.append_assoc, List.cons_append] using hph)
          (by simpa only [List.append_assoc, List.cons_append] using hrl)
        generalize hT2 : t.drop ((xs ++ directives lw).length + 1 + 1) = T at ht2 hrs hrls
        -- the stores
        have hsegS : segIn cells s!".L{fr.fn}.x{s.next}" ([] ++ directives sr ++ (D ++ zs)) = true := by
          simpa only [List.nil_append, List.append_assoc] using hRS
        have hphS : ∀ r ∈ runsAux s!".L{fr.fn}.x{s.next}" (T.take ([] : List Directive).length).reverse
            ((T.drop ([] : List Directive).length).take (directives sr ++ (D ++ zs)).length),
            runPhB okPc ph lab (lab r.1) ra r.2 = true := by
          simpa only [List.append_assoc, List.length_nil, List.take_zero, List.reverse_nil, List.drop_zero]
            using hrs
        have hrlS : ∀ r ∈ runsAux s!".L{fr.fn}.x{s.next}" (T.take ([] : List Directive).length).reverse
            ((T.drop ([] : List Directive).length).take (directives sr ++ (D ++ zs)).length),
            ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
          simpa only [List.append_assoc, List.length_nil, List.take_zero, List.reverse_nil, List.drop_zero]
            using hrls
        obtain ⟨zr, hzr, hcdr, hpcr⟩ := cdCQ_at (hQK s.next) ht2 hsegS rfl asr' hphS
        have hSS := slice_noLabel (seg_slice ht2 hsegS) asr'
        rw [List.length_append, runs_step hSS] at hphS hrlS
        -- the rest of the block, after the stores
        have := codeC2_of_segQB hm hgap htm hQK is ms _ s' c'.reverse _ T (directives sr) zs (hQK s.next) hs'.2 hms'
          hrest hD' ht2
          (by rw [hDd]; simpa using hsegS) asr' (by rw [hDd]; simpa using hphS) (by rw [hDd]; simpa using hrlS)
        simp only [List.length_nil, List.nil_append, Spike.Lib.X64.cellOff_zero] at hpcr hcdr
        refine ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, ?_, ?_⟩
        · rw [← hsp]; simpa [directives_eq_dirs] using hcdr
        · rw [← hsp]; rw [← hpcr] at this; simpa using this
      cases hs'.1 with
      | call d g w =>
        obtain ⟨lw, off, mp, hw, hd, aw, hs2⟩ := emitInst_call1_inv hm hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, hcdr, hcode⟩ := hcall lw [Item.d (stDir off)] _ mp aw
          (allIns_d rfl) hs2
        obtain ⟨z, rfl⟩ := length_one hzr
        exact .inr (.inl ⟨d, g, w, lw, off, zl, zc, z, rfl, hw, hd, hzl, hcdl, hbl, hcdr, by simpa using hcode⟩)
      | newBuf p h' kv u =>
        obtain ⟨lw, off, mp, hw, hd, hs2⟩ := emitInst_callN1_inv hm (newBuf_args_le h' kv u) hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, hcdr, hcode⟩ := hcall lw [Item.d (stDir off)] _ mp
          (allIns_getOps hw) (allIns_d rfl) hs2
        obtain ⟨z, rfl⟩ := length_one hzr
        exact .inr (.inr (.inl ⟨p, _, lw, off, zl, zc, z, rfl, rfl, hw, hd, hzl, hcdl, hbl, hcdr,
          by simpa using hcode⟩))
      | print a0 a1 =>
        obtain ⟨lw, mp, hw, hs2⟩ := emitInst_callN0_inv hm (by simp) hE
        obtain ⟨zl, zc, zr, hzl, hcdl, hbl, hzr, -, hcode⟩ := hcall lw [] Scc.Lower.Names.print mp
          (allIns_getOps hw) allIns_nil (by rw [hs2]; simp)
        obtain rfl : zr = [] := List.eq_nil_of_length_eq_zero hzr
        exact .inr (.inr (.inr ⟨[a0, a1], lw, zl, zc, rfl, rfl, hw, hzl, hcdl, hbl, by simpa using hcode⟩))
      | _ => exact absurd rfl hc


end Code

section Place

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64} {lo : Nat}

/-- **`codeC2_blockQ` at `BlC2Q Q`.** -/
theorem codeC2_blockQB (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {Q : Label → Prop} (hQK : ∀ k : Nat, Q s!".L{fr.fn}.x{k}")
    {b : Scc.IR.Block} (hQ : Q (labelOf fr.fn b.label)) (hs : Spike.Lib.LowerShape.BlockC2 b)
    {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 fr (CdCQ Q cells okPc ph lab ra) (BlC2Q Q cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  unfold blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    obtain ⟨i, hi, -, -⟩ := segIn_iff.mp hseg
    obtain ⟨t, ht⟩ : ∃ t, after (labelOf fr.fn b.label) cells = some t := ⟨_, by rw [after_eq, hi]; rfl⟩
    have hsc : ∀ m, segCells cells (labelOf fr.fn b.label) m = t.take m := by
      intro m; unfold segCells; rw [ht]
    have := codeC2_of_segQB (okPc := okPc) (ph := ph) (ra := ra) (lab := lab) hm hgap hs.2 hQK b.insts ms
      { next := n } s s.out.reverse (labelOf fr.fn b.label) t [] [] hQ hs.1 hms
      (by rw [← blockCode_eq]; exact heq) (by simp) ht (by simpa using hseg) rfl
      (fun r hr => by
        have h' := (hph r (by rw [hsc]; simpa [runs] using hr)).1
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
        rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
        exact hrun)
      (fun r hr => by
        have h' := hph r (by rw [hsc]; simpa [runs] using hr)
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
        rw [labC_eq hlab hres] at hp
        exact hp)
    simpa [Spike.Lib.X64.cellOff_zero] using this
  · cases hc


/-- **`codeC2_of_segL` at `BlC2L`.** -/
theorem codeC2_of_segLB (hm : fr.maps = true)
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
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) s.next
      (lab l + Int64.ofNat (cellOff t xs.length)) is tm :=
  codeC2_of_segQB (Q := fun L => L ∉ abLabs ∧ WcL L) hm hgap htm hK is ms s s' code l t xs zs hl hs hms h hD ht
    hseg hx hph hrl


/-- **`codeC2L_block` at `BlC2L`.** -/
theorem codeC2L_blockB (hm : fr.maps = true)
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
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term :=
  codeC2_blockQB (Q := fun L => L ∉ abLabs ∧ WcL L) hm hgap hlab hK hl hs hms hc hseg hph


/-- **`blocksCodeC2L` at `BlC2L`.** -/
theorem blocksCodeC2LB (hm : fr.maps = true)
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
    BlocksCodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : (pre ++ (s ++ b :: t)).map (fun b => (b, G b)) =
      (pre ++ s).map (fun b => (b, G b)) ++ (b, G b) :: t.map (fun b => (b, G b)) := by simp
  rw [e] at hok hph
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  exact ⟨_, codeC2L_blockB hm hgap hlab hK (hfn _) (hs b hb) (Nat.le_of_eq (hG b).symm) hc hseg hr⟩


/-- **`entryCodeC2L` at `BlC2L`.** -/
theorem entryCodeC2LB (hm : fr.maps = true)
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
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact codeC2L_blockB hm hgap hlab hK (hfn _) hs (Nat.le_of_eq (hG b).symm) hc hseg hr


/-- **`fnCodeC2L` at `BlC2L`.** -/
theorem fnCodeC2LB (hm : fr.maps = true)
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
    CodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) n (lab (labelOf fr.fn "entry"))
        r.insts r.term ∧
      BlocksCodeC2 fr (CdCL cells okPc ph lab ra) (BlC2L cells okPc ph lab fr ra) lab r.blocks := by
  obtain ⟨G, hz, hG⟩ := zip_callMaps (func2 name ps sc hq r)
  rw [hz] at hok hph
  exact ⟨entryCodeC2LB (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hfn hK hG hok hph
      ⟨hs.1, hs.2.1⟩,
    blocksCodeC2LB (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hfn hK hG hok hph hs.2.2⟩


end Place

/-- **`fnCodeC2L_of_fnPh2` at `BlC2L`.** -/
theorem fnCodeC2LB_of_fnPh2 {cfg : Scc.Config} {p : CoreTerm.Prog}
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
          (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) n
          (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
        BlocksCodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) Ly.lab
          w.r.blocks := by
  intro o Ly fr
  have hm : fr.maps = true := by
    show (Scc.Lower.X64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hfn : fr.fn = Scc.Lower.Names.user d.name := rfl
  exact ⟨hm, fnCodeC2LB hm (hgap_ofPlaceOK h i) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i)
    (fun l => hfn ▸ labelOf_user_usr d.name l) (hfn ▸ ret_user_usr d.name)
    (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2) hbo hbp⟩


/-- **`fnCodeC2L_ofPlaceOK` at `BlC2L`**: each call's `callq` at a position off
the write abort. -/
theorem fnCodeC2LB_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
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
              (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') n
              (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
            BlocksCodeC2 fr (CdCL o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') Ly.lab
              w.r.blocks := by
  intro o ir Ly
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, n, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbo, hbp, -⟩ := H j d w hd hw
  have H' := fun ra' hra => fnCodeC2LB_of_fnPh2 h i hir hL hbo (hbp ra' hra)
  exact ⟨hL, (H' (Ly.lab raL) rfl).1, n, fun ra' hra => (H' ra' hra).2⟩


-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.codeC2_of_segQB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_of_segQB

/-- info: 'Spike.Lib.LowerX64.fnCodeC2LB_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2LB_ofPlaceOK

end Spike.Lib.LowerX64
