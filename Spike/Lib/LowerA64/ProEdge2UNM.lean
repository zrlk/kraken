/-
**The prologue's edge into `main`'s body after the setup block**
(AArch64; the twin of `Spike/Lib/LowerX64/ProEdge2UNM.lean`): `ProEdge2`
(`Spike/Lib/LowerA64/ProgC2.lean`) at `scc_rt_main`'s call of `main` (the
interface's entry `uNM`, `Spike/Lib/Rt/A64MainS.lean`, at the arguments
`SetupArgs` of the setup call's post `SPostC`,
`Spike/Lib/LowerA64/SetupCall2.lean`), for a code block whose parameter is
the pair of the setup result's type `S` and the thread pointer, its body
lowered at its parameter's environment (`env2 d na`) and layouts. The
ghost is the entry control `cP` itself: the setup block's continuation
`let a = (r, me); tail main a`, whose two local steps reach `main`'s body.

- `spillsAt_rsOf`: every register of a spill has a cell;
- `argX_eq`: the runtime's `i`th argument register is the lowering's;
- `proEdge2_ofUNM`: `ProEdge2` at `uNM`'s invariant at `SetupArgs` of
  `SPostC` (each entry control `cP` alone), its stack limit's facts from
  `uNM`'s own (as `proEdge2_ofUN0`): the saved pair and the thread pointer
  from `uNM`, the setup result's words carried from the return registers
  to `main`'s parameter registers and the thread word from `x(sw)`
  (`wordsRep_mainArg`), the body's entry node's source facts by
  `entry2G_njB` after the continuation's two steps (`NJB.pre`), its slices
  at a ghost memory (`sliceL_ghost`), and the continuation itself placed
  (`slotRep_setupCont`).
-/
import Spike.Lib.LowerA64.ProEdge2Of
import Spike.Lib.LowerA64.LimOk0
import Spike.Lib.LowerA64.SetupCall2
import Spike.Lib.Src.Entry2M
import Spike.Lib.Src.SliceGhost
import Spike.Lib.Src.NJLS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG limA)

/-- **Every register of a spill has a cell.** -/
theorem spillsAt_rsOf {cx : FnCtx} : ∀ {l : List (Scc.IR.Reg × XReg)} {ps : List (XReg × Int64)},
    SpillsAt cx l ps → ∀ q ∈ l, ∃ k, rsOf cx q.1 = some k
  | [], _, _, _, hq => by cases hq
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, ⟨hq, hl⟩, q', hq' => by
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact ⟨_, hq.2.1⟩
    · exact spillsAt_rsOf hl q' hq'

/-- **The runtime's argument registers are the lowering's.** -/
theorem argX_eq : ∀ k (hk : k < argRegs.length), Spike.Lib.A64.Rt.argX k = argRegs[k]
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | k + 8, hk => absurd hk (by simp [argRegs, xregs])

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}

/-- **The prologue's edge into `main`'s body after the setup block**
(`ProEdge2` at `uNM`'s invariant at the arguments `SetupArgs` of `SPostC`
at the setup result's type `S`, one entry control `cP`, any `J` within
it; the ghost's saved pair and thread pointer, the ghost control `cP`):
for `main`'s code block `d` (`hfd`) whose parameter is the pair of `S` and
the thread pointer (`hd`), its `sw + 1` parameter registers (`hna`,
`sw < 8`), `S`'s layout no locative (`hnl`); the setup call's caller at
`setupTerm` (`hc0t`) binding `me` to one word `meW` (`hme`), a number
(`hmeN`) the ghost `x0` represents (`hmeV`); the room `ZU` the frame
(`hZU`); the limit word's facts `uNM` holds at its memory side `ms0` and
frame condition `F` carried to the edge's `ms1` and `F'` (`hms`, `hFF`). -/
theorem proEdge2_ofUNM {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) {S : Ty} (hd : d.argTy = .prod S (.ptr .pub .void))
    (hfd : p.find? (·.name == "main") = some d) {sw : Nat} (hna : c.na = sw + 1) (hsw8 : sw < 8)
    (hnl : Scc.Lower.shapeOf S ≠ .loc)
    {c0 : Ctl} (hc0t : c0.term = Scc.Sem.SrcSem.setupTerm) {tm : Ty} {meW : TermRun.Word}
    (hme : TermRun.lookupE c0.env "me" = some (tm, [meW])) (hmeN : IsNum meW) {x0 : BitVec 64}
    (hmeV : Scc.Sem.ValRep lbl meW.val x0.toNat)
    {g : WcG} {lab : Label → Int64} {ms0 ms1 : MemSide isaLSE2} {F F' : MachineData → Prop} {fn : Label}
    {ZU : Int64} (hZU : ZU = Int64.ofInt c.cx.frame)
    (hms : ∀ a Z, LimOk ms0 F exe endPc a Z → LimOk ms1 F exe endPc a Z) (hFF : ∀ m, F' m → F m)
    {cP : Ctl} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (Spike.Lib.A64.Rt.uNM lab ms0 F exe endPc fn ZU
      (fun c rs => Spike.Lib.A64.Rt.SetupArgs (SPostC p lbl S c0) sw x0 c rs ∧ c = cP) g).J σ c') :
    ProEdge2 p lbl lsize ms1 F' c g.fp g.ra g.tp cP J := by
  have hW := c.hWk _ (mem_lowerEnvs2_head c.lcx c.env 0 d.body)
  rw [c.henv] at hW
  -- the parameter's type and its grouping
  have hc : Compat d.argTy (Scc.Lower.shapeOf d.argTy) = true := by
    obtain ⟨hs1, hv1, -⟩ := hW.2.2.1 _ List.mem_cons_self
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hv1
    exact compat_shapeOf_self hs1 hk
  have hcS : Compat S (Scc.Lower.shapeOf S) = true := by
    have := hc
    rw [hd] at this
    simp only [Scc.Lower.shapeOf, Compat, Bool.and_eq_true] at this
    exact this.1
  obtain ⟨pls, hg⟩ := Option.isSome_iff_exists.1
    (hW.2.2.2.1 d.arg (d.arg, d.argTy, (Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg)
      (by simp [Spike.Lib.LowerShape.env2]))
  have hlenp : ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length = sw + 1 := by
    simp [Spike.Lib.LowerShape.paramsR, hna]
  have h8 : argRegs.length = 8 := by simp [argRegs, xregs]
  have hrs := spillsAt_rsOf (paramSpillN_of_spills c.hf c.h1 c.h16 c.hsp).2
  refine proEdge2_ofSpills c c.hsp fun σ c' hJσ => ?_
  obtain ⟨⟨⟨hSA, hcP⟩, hfp, hra, hsp, htp⟩, hlim⟩ := hJ σ c' hJσ
  subst hcP
  have hl := (hms _ _ hlim).mono hFF
  have hl' := limOk_tpidr (σ := σ) htp hl
  rw [← hsp, hZU] at hl'
  refine ⟨⟨hl'.rt, hl'.mp, hl'.unmapped, hl'.room⟩, hfp, hra, htp, .refl _, fun sl hsl _ => ?_⟩
  -- the setup call's post: the continuation and the returned words
  obtain ⟨rs, hPC, hargs, hx0⟩ := hSA
  obtain ⟨cE, fr, cr, a, t, ws, hct, ⟨σr, hσr, hRJ, hRL⟩, hra', hev, hc'⟩ := hPC
  obtain ⟨x, f, a0, e, d0, t0, ws0, ht, -, -, -, rfl⟩ := hct
  rw [hc0t] at ht
  simp only [Scc.Sem.SrcSem.setupTerm] at ht
  cases ht
  subst hc'
  obtain ⟨a1, t1, ws1, ops, pls0, val0, hra1, -, hev1, hg0, hn0, hv0, hW0, -, -⟩ := hRJ
  rw [hra'] at hra1
  cases hra1
  rw [hev] at hev1
  cases hev1
  obtain ⟨a2, lc, hra2, hEL, hIn, hlit, hers, ⟨L, sm, hESl⟩, t2, ws2, hev2, hlen2⟩ := hRL
  rw [hra'] at hra2
  cases hra2
  rw [hev] at hev2
  cases hev2
  obtain ⟨hcmp, hnum⟩ := hEL.evalAt' hIn hlit hev
  have hsl0 := (hESl.evalAt hev).of_erase hers
  have hlenS : ws.length = (Scc.Lower.shapeOf S).words.length := by
    rw [hlen2, ← SliceL.words_erase, hers]
  -- the parameter registers' values: the argument registers'
  have hprs : ∀ k (hk : k < ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length),
      Spike.Lib.Form.opdVal (rsOf c.cx) sl ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg)[k] =
        some (σ.regs.getXReg (Spike.Lib.A64.Rt.argX k)).toBitVec.toNat := by
    intro k hk
    have hk' : k < (Spike.Lib.LowerShape.paramsR d c.na).length := by simpa using hk
    have hkr : k < argRegs.length := by rw [h8]; rw [hlenp] at hk; omega
    have hmem : ((Spike.Lib.LowerShape.paramsR d c.na)[k], argRegs[k]) ∈
        (Spike.Lib.LowerShape.paramsR d c.na).zip argRegs := by
      have hz : k < ((Spike.Lib.LowerShape.paramsR d c.na).zip argRegs).length := by
        rw [List.length_zip]; rw [h8] at hkr; omega
      have := List.getElem_mem hz
      rwa [List.getElem_zip] at this
    obtain ⟨j, hj⟩ := hrs _ hmem
    have hsj := hsl _ _ hmem j hj
    simp only [List.getElem_map, Spike.Lib.Form.opdVal, hj, Option.map_some, hsj, argX_eq k hkr]
  have hops : ∀ k (hk : k < ops.length),
      k + 1 < ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length →
      val0 ops[k] = some (σ.regs.getXReg (Spike.Lib.A64.Rt.argX k)).toBitVec.toNat := by
    intro k hk hk1
    rw [hlenp] at hk1
    have hkr : k < argRegs.length := by omega
    rw [hv0 k hk hkr, hargs k (by omega), argX_eq k hkr, hσr]
  have hmeV' : Scc.Sem.ValRep lbl meW.val
      (σ.regs.getXReg (Spike.Lib.A64.Rt.argX
        (((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length - 1))).toBitVec.toNat := by
    rw [hlenp, Nat.add_sub_cancel, hx0]
    simpa using hmeV
  obtain ⟨pu, o, hpls, hprsE, hwu, hwo⟩ := wordsRep_mainArg hd hcS hg hprs hg0 hcmp hers hops hW0 hmeV'
  -- `main`'s entry
  have hrep : Spike.Lib.Form.WordsRep lbl (Spike.Lib.Form.opdVal (rsOf c.cx) sl) (ws ++ [meW])
      ((Spike.Lib.Form.group d.argTy ((Spike.Lib.LowerShape.paramsR d c.na).map .reg)).getD []) := by
    rw [hg, Option.getD_some, hpls]
    exact hwu.append ⟨hwo, trivial⟩
  have hnum' : NumL (Scc.Lower.shapeOf d.argTy) (ws ++ [meW]) := by
    rw [hd]
    exact NumL.pair (hnum.of_erase hers)
      (NumL.of_all fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hmeN) hlenS
  have hslp : SliceL (SlP L sm) (Scc.Lower.shapeOf d.argTy) (ws ++ [meW]) := by
    rw [hd]
    exact SliceL.pair hsl0 trivial hlenS fun h => absurd h hnl
  obtain ⟨L', sm', B, hslg, hmB⟩ := sliceL_ghost hslp
  have hrun : LocalRun p
      ⟨.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a")), ("r", d0.retTy, ws) :: c0.env, none⟩
      ⟨d.body, [(d.arg, d.argTy, ws ++ [meW])], none⟩ :=
    .step (Spike.Lib.Form.localStep_pair (t := d0.retTy) (ws := ws) (u := tm) (us := [meW]) rfl
        (by simp [TermRun.evalAt, TermRun.lookupE])
        (by simpa [TermRun.evalAt, TermRun.lookupE, List.find?] using hme))
      (.single (Spike.Lib.localStepS_tail (t := .prod d0.retTy tm) (ws := ws ++ [meW]) rfl hfd
        (by simp [TermRun.evalAt, TermRun.lookupE])).toLocalStep)
  have hreg : ∀ q ∈ pu.flatMap Spike.Lib.Form.WordPl.opds ++ [o], ∃ r, q = .reg r := by
    rw [← hprsE]
    intro q hq
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨r, rfl⟩
  rw [c.henv, c.hlits]
  exact ⟨⟨L', sm', B, NJB.pre hrun (entry2G_njB rfl rfl rfl hrep hc hnum' hslg hmB (wordsSmall_of_rep hrep))⟩,
    slotRep_setupCont hme hwu hwo hreg⟩

end Edge

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.proEdge2_ofUNM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proEdge2_ofUNM
