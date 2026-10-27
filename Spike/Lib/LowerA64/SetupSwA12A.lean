/-
**The setup words A11 fixes are the lowering's** (AArch64): on an
`Accepted2` program with a setup block whose output passes `placeOKAt`,
every `sw` with the runtime's code at `setupMC sw` (`rtCodeOkS`, A11) is
`setupWords2 p`, the setup block's value words (the twin of
`Spike/Lib/LowerX64/SetupSwA12.lean`). A12 checks `scc_rt_main`'s code
(the runtime's second function, so its labels are `.L1_scc_rt_main.…`) at
the IR's `mainThread0 (entry2 p) (setupWords2 p)`: after `.0_entry`, the
`bl` of the setup block, its return label `.sp0`, its `setupWords2 p`
result stores, the `setupWords2 p + 1` argument loads of `main`, the `bl`
of `main`, its return label `.sp1`. A11 puts `.sp1` `2 sw + 2` instructions
after `.sp0` (the marshalling block), so the two label gaps agree
(`labelGap_unique`).

- `setResults_eq`, `setOps`: the results' stores, one `setReg` per pair.
- `dirs_setOps`, `dirs_getOps`: one instruction per stored result, per
  loaded register argument.
- `labelGap_unique`: two gaps between the same labels are equal.
- `mainThread0_idx`: `scc_rt_main` is the runtime's second function.
- `sw_eq_setupWords2A`: A11's `sw` is `setupWords2 p`.
- `valWords_of_rtCodeOkSA`: the setup block's result has `sw` value words.
-/
import Spike.Lib.LowerA64.NumQOfPlaceOKA
import Spike.Lib.LowerA64.BlocksC1
import Spike.Lib.LowerProgC2
import Spike.Lib.SetupWords2
import Spike.Lib.RtMainMem
import Spike.Lib.Rt.A64CodeInSetup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Code1A64 (ctxOf segIn segIn_label labelGap_of_segIn blockItems instsItems blocksOk_block kAfter)
open Scc.Cert.Rt.A64 (labelGap isIns)

/-! ## The results' stores and the arguments' loads -/

section Ctx

variable {cx : FnCtx}

/-- **The stores of results into IR registers**, in order: each pair's
`setReg`, concatenated. -/
def setOps (cx : FnCtx) : List (Scc.IR.Reg × XReg) → Except String (List Item)
  | [] => .ok []
  | (d, r) :: rest => do return (← cx.setReg d r) ++ (← setOps cx rest)

/-- `setResults`'s loop body: append the pair's store to the accumulator. -/
def setOpsStep (cx : FnCtx) (x : Scc.IR.Reg × XReg) (out : List Item) :
    Except String (ForInStep (List Item)) := do
  let v ← cx.setReg x.1 x.2
  pure (ForInStep.yield (out ++ v))

theorem forIn_setOps (l : List (Scc.IR.Reg × XReg)) (init : List Item) :
    forIn (m := Except String) l init (setOpsStep cx) =
      (match setOps cx l with
        | .error err => .error err
        | .ok v => .ok (init ++ v)) := by
  induction l generalizing init with
  | nil => simp [setOps, forIn, ForIn.forIn, pure, Except.pure]
  | cons p rest ih =>
    obtain ⟨d, r⟩ := p
    cases ha : cx.setReg d r with
    | error e => simp [setOps, setOpsStep, ha, List.forIn_cons, bind, Except.bind]
    | ok la =>
      simp only [List.forIn_cons, setOpsStep, ha, bind, Except.bind, pure, Except.pure]
      rw [ih]
      simp only [setOps, ha, bind, Except.bind, pure, Except.pure]
      cases hr : setOps cx rest <;> simp

/-- **At most six results**: `setResults` is `setOps` of the results
zipped with `x0`, `x1`, …. -/
theorem setResults_eq {ds : List Scc.IR.Reg} (h : ds.length ≤ Scc.IR.maxRets) :
    cx.setResults ds = setOps cx (ds.zip argRegs) := by
  have hl : ¬ ds.length > Scc.IR.maxRets := by omega
  simp only [FnCtx.setResults, hl, ite_false]
  rw [show (fun (x : Scc.IR.Reg × XReg) (out : List Item) => (do
      let v ← cx.setReg x.fst x.snd
      pure (ForInStep.yield (out ++ v)) : Except String (ForInStep (List Item)))) = setOpsStep cx from rfl,
    forIn_setOps]
  cases setOps cx (ds.zip argRegs) <;> rfl

/-- **One instruction per stored result** in a frame of at most 32 KiB. -/
theorem dirs_setOps (hf : FrameOk cx) (hs : cx.frame ≤ 32768) :
    ∀ {l : List (Scc.IR.Reg × XReg)} {c : List Item}, setOps cx l = .ok c →
      (directives c).length = l.length ∧ (directives c).all isIns = true
  | [], c, h => by cases ok_inj h; exact ⟨rfl, rfl⟩
  | (d, r) :: rest, c, h => by
    simp only [setOps] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lr, hr, h⟩ := bind_eq_ok h
    cases ok_inj h
    obtain ⟨h1, h2⟩ := dirs_setOps hf hs hr
    cases ho : cx.slotOff d with
    | error e => simp [FnCtx.setReg, ho, bind, Except.bind] at ha
    | ok off =>
      rw [setReg_eq hf hs ho] at ha
      cases ok_inj ha
      refine ⟨?_, ?_⟩
      · simp [ins, directives] at h1 ⊢; omega
      · simp only [directives_append, List.all_append, h2, Bool.and_true]; rfl

/-- **One instruction per loaded register argument** in a frame of at most
32 KiB. -/
theorem dirs_getOps (hf : FrameOk cx) (hs : cx.frame ≤ 32768) :
    ∀ {l : List (Scc.IR.Operand × XReg)} {c : List Item}, (∀ x ∈ l, ∃ r, x.1 = .reg r) → getOps cx l = .ok c →
      (directives c).length = l.length
  | [], c, _, h => by cases ok_inj h; rfl
  | (a, t) :: rest, c, hr, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lr, hl, h⟩ := bind_eq_ok h
    cases ok_inj h
    have h1 := dirs_getOps hf hs (fun x hx => hr x (List.mem_cons_of_mem _ hx)) hl
    obtain ⟨r, rfl⟩ := hr (a, t) (List.mem_cons_self ..)
    cases ho : cx.slotOff r with
    | error e => simp [FnCtx.getOp, FnCtx.getReg, ho, bind, Except.bind] at ha
    | ok off =>
      simp only [FnCtx.getOp] at ha
      rw [getReg_eq hf hs ho] at ha
      cases ok_inj ha
      simp [ins, directives] at h1 ⊢; omega

/-- A call without arguments loads nothing. -/
theorem callArgs_nil (base : Nat) : cx.callArgs [] base = .ok [] := by
  rw [callArgs_eq (by simp) base, getArgs_eq (by simp)]
  rfl

end Ctx

/-! ## Label gaps -/

/-- **Two gaps between the same labels are equal.** -/
theorem labelGap_unique {prog : List Directive} {a b : Label} {m n : Nat} (h1 : labelGap prog a b m = true)
    (h2 : labelGap prog a b n = true) : m = n := by
  unfold labelGap at h1 h2
  split at h1
  · rename_i i j hi hj
    rw [hi, hj] at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
    omega
  · cases h1

/-! ## `scc_rt_main`'s code -/

/-- The second entry of a successful `mapM` of results is the second result. -/
theorem mapM_idx1 {α : Type} {a b : Except String α} {l : List (Except String α)} {rt : List α} {y : α}
    (h : (a :: b :: l).mapM id = .ok rt) (hb : b = .ok y) : rt[1]? = some y := by
  subst hb
  cases a with
  | error e => simp [List.mapM_cons, bind, Except.bind] at h
  | ok x =>
    cases hl : l.mapM id with
    | error e => simp [List.mapM_cons, hl, bind, Except.bind] at h
    | ok vs =>
      simp [List.mapM_cons, hl, bind, Except.bind, pure, Except.pure] at h
      subst h
      rfl

/-- **`scc_rt_main` is the runtime's second function.** -/
theorem mainThread0_idx {lay : Scc.Layout} {e : Scc.Frontend.Entry} {sw : Nat} {rt : List Scc.IR.Func}
    (h : Scc.Lower.Inv.rtFuncs lay e sw = .ok rt) : rt[1]? = some (Scc.Lower.Inv.mainThread0 e sw) := by
  unfold Scc.Lower.Inv.rtFuncs at h
  rw [List.cons_append, List.cons_append] at h
  exact mapM_idx1 h (Scc.Lower.Inv.mainThreadF_eq e sw)

/-- **`scc_rt_main`'s local labels**: `.L1_scc_rt_main.…`. -/
theorem mainLocal (ir : Scc.IR.Program) (e : Scc.Frontend.Entry) (sw : Nat) (s : String) :
    (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 e sw)).local s = ".L1_scc_rt_main." ++ s := by
  show s!".L{1}_{sanitize Scc.Lower.Names.mainThread}." ++ s = _
  congr 1
  decide +kernel

/-- `scc_rt_main`'s instructions after a setup block of `sw` words. -/
theorem mainInsts_setupA (sw : Nat) :
    Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ sw =
      [.call (Scc.Lower.Inv.mainDs ⟨.setupTid, true⟩ sw) (Scc.Lower.Names.user "rodata") [],
       .call [Scc.Lower.Inv.regName "v" sw] (Scc.Lower.Names.user "main") (Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw),
       .syscall (Scc.Lower.Inv.regName "r" (sw + 1)) .exitGroup [.reg (Scc.Lower.Inv.regName "v" sw)]] := by
  rfl

/-- **The code of `scc_rt_main`'s block after a setup block of `sw` words**
(stack maps on, a frame of at most 32 KiB): the setup block's `bl`, its
return label `.sp0`, then `2 sw + 1` instructions (`sw` result stores, the
`sw + 1` argument loads of `main`), the `bl` of `main`, its return label
`.sp1`. -/
theorem mainCode_dirsA {c : FnCtx} (hm : c.maps = true) (hf : FrameOk c) (hs : c.frame ≤ 32768) {sw : Nat}
    {code : List Item}
    (h : blockItems c 0 ⟨"entry", Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ sw, .unreachable⟩ = .ok code) :
    ∃ (xs rest : List Directive), directives code =
        .instr ⟨.W64, .BL (.label (Scc.Lower.Names.user "rodata"))⟩ :: .label (c.local "sp0") ::
          (xs ++ .label (c.local "sp1") :: rest) ∧
      xs.length = 2 * sw + 2 ∧ xs.all isIns = true := by
  unfold blockItems at h
  obtain ⟨ci, hci, h⟩ := bind_eq_ok h
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  cases ok_inj h
  rw [mainInsts_setupA] at hci
  simp only [instsItems] at hci
  obtain ⟨c0, h0, hci⟩ := bind_eq_ok hci
  obtain ⟨cr, hcr, hci⟩ := bind_eq_ok hci
  cases ok_inj hci
  obtain ⟨c1, h1, hcr⟩ := bind_eq_ok hcr
  obtain ⟨c2, -, hcr⟩ := bind_eq_ok hcr
  cases ok_inj hcr
  obtain ⟨ca0, sr0, hca0, hsr0, hd0⟩ := inst_call_inv hm h0
  obtain ⟨ca1, sr1, hca1, -, hd1⟩ := inst_call_inv hm h1
  rw [callArgs_nil] at hca0
  cases ok_inj hca0
  -- the results' stores: `sw` of them, at most six
  have hsw : (Scc.Lower.Inv.mainDs ⟨.setupTid, true⟩ sw).length = sw := by
    simp only [Scc.Lower.Inv.mainDs, List.length_map, List.length_range]; rfl
  have hle : (Scc.Lower.Inv.mainDs ⟨.setupTid, true⟩ sw).length ≤ Scc.IR.maxRets := by
    unfold FnCtx.setResults at hsr0
    split at hsr0
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hsr0
    · omega
  rw [setResults_eq hle] at hsr0
  obtain ⟨hl0, hi0⟩ := dirs_setOps hf hs hsr0
  have hz0 : ((Scc.Lower.Inv.mainDs ⟨.setupTid, true⟩ sw).zip argRegs).length = sw := by
    rw [List.length_zip, hsw]
    simp only [Scc.IR.maxRets] at hle
    simp [argRegs, xregs]; omega
  -- the arguments' loads: `sw + 1` registers
  have hal : (Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw).length = sw + 1 := by
    simp [Scc.Lower.Inv.mainArgs, hsw]
  have hle1 : (Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw).length ≤ 8 := by
    simp only [Scc.IR.maxRets] at hle; omega
  rw [callArgs_eq hle1, getArgs_eq hle1] at hca1
  have hregs : ∀ x ∈ (Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw).zip argRegs, ∃ r, x.1 = .reg r := by
    intro x hx
    have := List.of_mem_zip hx
    simp only [Scc.Lower.Inv.mainArgs, List.mem_append, List.mem_map, List.mem_singleton] at this
    rcases this.1 with ⟨r, -, he⟩ | he
    · exact ⟨r, he.symm⟩
    · exact ⟨_, he⟩
  have hl1 := dirs_getOps hf hs hregs hca1
  have hz1 : ((Scc.Lower.Inv.mainArgs ⟨.setupTid, true⟩ sw).zip argRegs).length = sw + 1 := by
    rw [List.length_zip, hal]
    simp [argRegs, xregs]; omega
  have hi1 := allIns_getOps hca1
  refine ⟨directives sr0 ++ directives ca1 ++ [.instr ⟨.W64, .BL (.label (Scc.Lower.Names.user "main"))⟩],
    directives sr1 ++ directives c2 ++ directives ct, ?_, ?_, ?_⟩
  · have q0 : s!"sp{(0 : Nat)}" = "sp0" := by decide +kernel
    have q1 : s!"sp{(0 + 1 : Nat)}" = "sp1" := by decide +kernel
    simp only [directives_append, hd0, hd1, q0, q1]
    simp [directives]
  · simp only [List.length_append, hl0, hz0, hl1, hz1, List.length_singleton]; omega
  · simp only [List.all_append, hi0, Bool.true_and]
    exact Bool.and_eq_true_iff.mpr ⟨hi1, rfl⟩

/-! ## A11's `sw` is the lowering's -/

open Spike.Lib.A64.Rt (rtCodeOkS setupMC) in
/-- **A11's setup words are the lowering's** (AArch64): on an `Accepted2`
program with a setup block whose output passes `placeOKAt`, every `sw`
with the runtime's code at `setupMC sw` is `setupWords2 p`. -/
theorem sw_eq_setupWords2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) {sw : Nat}
    (hc : rtCodeOkS (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (setupMC sw) = true) :
    Spike.Lib.LowerNode.setupWords2 p = sw := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  generalize hir' : (Scc.Lower.A64.lowerAll cfg p).low.ir = ir at hir
  generalize hf0 : Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p) = f0
  have hf : (f0, 1) ∈ ir.funcs.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, hir, ← hf0]
    simp only [Scc.Lower.Inv.progOf]
    have h1 := mainThread0_idx hrt
    have hlt : 1 < rt.length := (List.getElem?_eq_some_iff.mp h1).1
    rw [List.getElem?_append_left hlt, h1]
  have h12 := fnCode1_of_placeOKAt h ((place_ir_ofEmitted _).trans (congrArg some hir'))
  have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok h12 hf (by rw [← hf0]; rfl)
  subst hf0
  have hm : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).maps =
      true := by
    show ir.growth.isSome = true
    rw [hir]; rfl
  have hfo : FrameOk (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))) :=
    fnCtx_frameOk _ _ _ _ _
  unfold Scc.Cert.Code1A64.fnOk1 at hok
  split at hok
  case h_2 => cases hok
  rename_i b0 bs ps hb hps
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hfr : (ctxOf ir 1
      (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).frame ≤ 32768 := by
    have := hok.1.1.1.1.1.2; omega
  have hbl : Scc.Cert.Code1A64.blocksOk (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))) 0
      ([] ++ ⟨"entry", Scc.Lower.Inv.mainInsts ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p),
        .unreachable⟩ :: []) = true := by
    exact hok.1.1.1.2
  obtain ⟨l, code, -, hbi, hseg⟩ := blocksOk_block hbl
  obtain ⟨xs, rest, hdirs, hxl, hxi⟩ := mainCode_dirsA hm hfo hfr hbi
  rw [hdirs] at hseg
  have hseg0 := segIn_label (xs := [_]) hseg
  have hgap := labelGap_of_segIn hseg0 hxi
  have hR := Scc.Cert.Rt.A64.rtIn_sound hc
  unfold Spike.Lib.A64.Rt.rtCodeTabS at hR
  have hM := (Scc.Cert.Rt.A64.RtAll.append (Scc.Cert.Rt.A64.RtAll.append (Scc.Cert.Rt.A64.RtAll.append
    (Scc.Cert.Rt.A64.RtAll.append hR).1).1).1).2
  have hgap' := hM.2.2.2.2.2.2.2.1
  have e0 : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).local "sp0" =
      (setupMC sw).sp0 := by
    rw [mainLocal]; show _ = ".L1_scc_rt_main.sp0"; decide +kernel
  have e1 : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).local "sp1" =
      (setupMC sw).sp1 := by
    rw [mainLocal]; show _ = ".L1_scc_rt_main.sp1"; decide +kernel
  rw [e0, e1] at hgap
  have := labelGap_unique hgap hgap'
  simp only [setupMC] at this
  omega

open Spike.Lib.A64.Rt (rtCodeOkS setupMC) in
/-- **The setup block's result has A11's `sw` value words** (AArch64): the
premise `hw` of `hPlS_ofSPostC` / `hPl_setupArgs` at the setup block's
result type, from the placement check alone. -/
theorem valWords_of_rtCodeOkSA {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) {ty : CoreLang.Ty} (hs : Scc.Lower.setupOf p = some ty) {sw : Nat}
    (hc : rtCodeOkS (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (setupMC sw) = true) :
    Scc.Obj.valWords ty = some sw := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hs]; rfl
  obtain ⟨dr, hfr, hrt⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hs
  obtain ⟨k, hk⟩ := setupValWords_of_placeOK h hp ty hs
  rw [← sw_eq_setupWords2A h hp hs' hc, ← hrt]
  exact Spike.Lib.LowerNode.valWords_setupWords2 hs' hfr (by rw [hrt, hk]; rfl)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.sw_eq_setupWords2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sw_eq_setupWords2A

/-- info: 'Spike.Lib.LowerA64.valWords_of_rtCodeOkSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms valWords_of_rtCodeOkSA

end Spike.Lib.LowerA64
