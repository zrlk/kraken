/-
**An `Accepted2` function's code off the write abort's labels** (AArch64):
the twins of `codeC2_of_seg` (`Spike/Lib/LowerA64/BlocksC2Seg.lean`) and of
`fnCodeC2_ofPlaceOK` (`Spike/Lib/LowerA64/FnCode2Of.lean`) at the code
predicate `CdCL` (`Spike/Lib/LowerA64/UserAbC.lean`): every piece of a user
function's code is after a label none of the write abort's (`abLabs`), so
the `W2` producers get the consumers' `hab` from `blkW_abSt_subCdL`. A user
function's labels (its blocks' `FnCtx.blockLabel`, its return labels
`FnCtx.local`) carry its function index `rt.length + j`, `18 + j` (`rtFuncs`
gives 18 functions), none of the runtime's 9, 12, 16 that `abLabs` carry.

- `cdCL_at`: `cdC_at` at a label off `abLabs`.
- `blockLabel_not_abLabs`: a block label of a function index other than 9,
  12, 16 is off `abLabs`; `local_wc`, `blockLabel_wc`: and a user
  function's (`WcL`) for a user function's context (`hun`).
- `rtFuncs_length`: the runtime has 18 functions.
- `codeC2L_of_seg`, `codeC2L_block`, `blocksCodeC2L`, `entryCodeC2L`,
  `fnCodeC2L`: the twins at `CdCL`, for a function index other than 9, 12,
  16 (`hfi`).
- `fnCodeC2L_ofPlaceOK`: `fnCodeC2_ofPlaceOK` at `CdCL`, with `rt.length =
  18`.
-/
import Spike.Lib.LowerA64.FnCode2Of
import Spike.Lib.LowerA64.UserAbC

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

/-! ## Labels off the write abort's -/

section Code

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **A piece of code after a label off the write abort's is at `CdCL`**
(`cdC_at`). -/
theorem cdCL_at {l : Label} (hl : l ∉ abLabs ∧ WcL l) {xs c zs : List Directive}
    (hseg : segIn prog l (xs ++ c ++ zs) = true) (hx : xs.all isIns = true) (hc : c.all isIns = true)
    (hph : ∀ r ∈ runsAux l xs.reverse (c ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    CdCL prog okPc ph lab ra (lab l + Int64.ofNat (4 * xs.length)) c := by
  obtain ⟨P, hP⟩ := runsAux_run0 l (c.reverse ++ xs.reverse) zs
  rw [← runsAux_shift _ _ _ _ (noLabel_of_isIns hc)] at hP
  have hr := hph _ hP
  simp only [List.reverse_append, List.reverse_reverse] at hr
  exact ⟨hc, l, xs.length, hl, rfl, blockAt_of_segIn hseg hx hc, runPhB_sub hr⟩

/-- **A block label is a local label** of its context (`FnCtx.local`). -/
theorem blockLabel_local {l : Scc.IR.Label} {L : Label} (h : cx.blockLabel l = .ok L) : ∃ s, L = cx.local s := by
  unfold FnCtx.blockLabel at h
  split at h
  · next bi _ =>
    cases h
    exact ⟨s!"{bi}_{sanitize l}", by simp [FnCtx.local, String.append_assoc]; rfl⟩
  · cases h

/-- **A block label of a function index other than the runtime's 9, 12, 16
is none of the write abort's.** -/
theorem blockLabel_not_abLabs (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {l : Scc.IR.Label} {L : Label}
    (h : cx.blockLabel l = .ok L) : L ∉ abLabs := by
  obtain ⟨s, rfl⟩ := blockLabel_local h
  exact local_not_abLabs hfi s

/-- **A user function's local label** of a function index other than the
runtime's 9, 12, 16 is none of the write abort's and a user function's
(`WcL`). -/
theorem local_wc (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    (s : String) : cx.local s ∉ abLabs ∧ WcL (cx.local s) :=
  ⟨local_not_abLabs hfi s, let ⟨_, hn⟩ := hun; wcL_local cx hn s⟩

/-- **A user function's block label** of a function index other than the
runtime's 9, 12, 16 is none of the write abort's and a user function's. -/
theorem blockLabel_wc (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {l : Scc.IR.Label} {L : Label} (h : cx.blockLabel l = .ok L) : L ∉ abLabs ∧ WcL L := by
  obtain ⟨s, rfl⟩ := blockLabel_local h
  exact local_wc hfi hun s

/-- **An `Accepted2` block's code after its label gives `CodeC2`**: the code
`c1` of its instructions numbered from `k` (`instsItems`, `InstC2`) and `c2`
of its terminator (`TermC2`), after the instructions `xs` and before `zs` in
the code after `l` (`segIn`), every run from there passing `runPhB` at `lab`
(`hph`) and in the phase of `ra` (`hrl`); the stack maps on (`hm`), and
`lab` following the labels' gaps (`hgap`).
At `CdCL` (`codeC2_of_seg`'s twin), for a function index other than 9, 12, 16
(`hfi`) and a label off `abLabs` (`hl`). -/
theorem codeC2L_of_seg (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {tm : Scc.IR.Term} (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (l : Label) (c1 c2 : List Item) (xs zs : List Directive),
      l ∉ abLabs ∧ WcL l → (∀ i ∈ is, InstC2 i) → instsItems cx k is = .ok c1 →
      cx.term (k + is.length) tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) k (lab l + Int64.ofNat (4 * xs.length))
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
            BlC2 prog okPc ph lab cx ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length)) g k ∧
            CdCL prog okPc ph lab ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4)
              (directives ls) ∧
            CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) (k + 1)
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
          refine ⟨?_, h2, ?_, ?_⟩
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
          · have := codeC2L_of_seg hm hgap hfi hun htm is (k + 1) _ c1' c2 (directives ls) zs hK hs'.2 hc1 ht hseg2 hAs
              hrs hrl2
            rwa [hsp] at this
        by_cases hc : Spike.Lib.LowerShape.isCall i = false
        · -- an instruction other than a call: instructions only
          have hA : (directives ci).all isIns = true := inst2_allIns hs'.1 hc hci
          refine Or.inl ⟨hc, ci, hci, ?_, ?_⟩
          · exact cdCL_at (zs := directives (c1' ++ c2) ++ zs) hl (by simpa only [List.append_assoc] using hseg) hx hA
              (by simpa only [List.append_assoc] using hph)
          · have hxA : (xs ++ directives ci).all isIns = true := by rw [List.all_append, hx, hA]; rfl
            have := codeC2L_of_seg hm hgap hfi hun htm is (k + 1) l c1' c2 (xs ++ directives ci) zs hl hs'.2 hc1 ht
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


/-- **A placed block of `lowerC2`'s shape gives `CodeC2`** at its label
(`codeC_block`'s twin): its code after the label (`segIn`) and its runs'
phase facts at the code labels (`labC`), every label read resolving, which
`lab` agrees with (`hlab`).
At `CdCL` (`codeC2_block`'s twin), for a function index other than 9, 12, 16
(`hfi`) and a label off `abLabs` (`hl`). -/
theorem codeC2L_block (hm : cx.maps = true)
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
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) k (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [Scc.Cert.Code1A64.blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      have := codeC2L_of_seg (okPc := okPc) (ph := ph) (ra := ra) hm hgap hfi hun hs.2 b.insts k l c1 c2 [] []
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

/-! ## The runtime's functions -/

/-- `mapM` in `Except` keeps the length. -/
theorem mapM_except_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | x :: xs, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok b =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok bs =>
        simp only [hx, hxs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_except_length hxs]

/-- **The runtime has 18 functions** (13 and the 5 abort kinds'), so a user
function's index `rt.length + j` is none of the runtime's 9, 12, 16. -/
theorem rtFuncs_length {arch : Scc.Arch} {lay : Scc.Layout} {e : Scc.Frontend.Entry} {sw : Nat}
    {rt : List Scc.IR.Func}
    (h : Scc.Lower.Inv.rtFuncs arch lay e sw = .ok rt) : rt.length = 18 := by
  unfold Scc.Lower.Inv.rtFuncs at h
  rw [mapM_except_length h]
  simp [Scc.Lower.Runtime.abortKinds]

/-! ## Each function's code -/

section Place

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **The later blocks' code** (`BlocksCodeC2`) at `CdCL` and `BlC2`, from
the function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`), each
of `lowerC2`'s shape (`blocksCodeC`'s twin).
At `CdCL` (`blocksCodeC2`'s twin), for a function index other than 9, 12, 16
(`hfi`). -/
theorem blocksCodeC2L (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, BlockC2 b) :
    BlocksCodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, _, hl, codeC2L_block hm hgap hlab hfi hun (hs b hb) (blockLabel_wc hfi hun hl) hc hseg hr⟩

/-- **The entry block's code** (`CodeC2` at the entry's label, numbered
from 0) from the function's `blocksOk` and `blocksPh`.
At `CdCL` (`entryCodeC2`'s twin), for a function index other than 9, 12, 16
(`hfi`). -/
theorem entryCodeC2L (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label}
    (hent : cx.blockLabel b.label = .ok entry) (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : BlockC2 b) :
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) 0 (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact codeC2L_block hm hgap hlab hfi hun hs (blockLabel_wc hfi hun hent) hc hseg hr

/-- **A compiled block's function's code** (`body2_segS_of`'s two code
premises): the function `func2 name ps sc hq r` of a closed form `r` of
`lowerC2`'s shape (`ResC2`), its entry block at `CodeC2` from 0 and its
later blocks at `BlocksCodeC2`, from its `blocksOk` and `blocksPh`.
At `CdCL` (`fnCodeC2`'s twin), for a function index other than 9, 12, 16
(`hfi`). -/
theorem fnCodeC2L (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) (hun : ∃ n, cx.name = Scc.Lower.Names.user n)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg}
    {entry : Label} (hent : cx.blockLabel "entry" = .ok entry)
    (hok : blocksOk prog cx 0 (func2 name ps sc hq r).blocks = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0
      (func2 name ps sc hq r).blocks = true) :
    CodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) 0 (lab entry) r.insts r.term ∧
      BlocksCodeC2 cx (CdCL prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) lab r.blocks :=
  ⟨entryCodeC2L (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hfi hun hent hok hph
    ⟨hs.1, hs.2.1⟩,
    blocksCodeC2L (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hfi hun hok hph hs.2.2⟩

end Place

/-- **Each compiled block's function's code from `PlaceOK` at `CdCL`**
(`fnCodeC2_ofPlaceOK`'s twin): as `fnCodeC2_ofPlaceOK`, every piece of the
code after a label none of the write abort's, and the runtime's 18
functions before the compiled ones (`rt.length = 18`). -/
theorem fnCodeC2L_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
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
                (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') 0
                (Ly.lab entry) w.r.insts w.r.term ∧
              BlocksCodeC2 cx (CdCL o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') Ly.lab
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
  exact ⟨hL, hm, entry, hent, fun ra' hra => fnCodeC2L hm hgap (lab_ofPlaceOK h i) hfi ⟨_, rfl⟩
    (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2) hent hbo (hbp ra' hra)⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.codeC2L_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2L_of_seg

/-- info: 'Spike.Lib.LowerA64.fnCodeC2L_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2L_ofPlaceOK

end Spike.Lib.LowerA64
