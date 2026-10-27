/-
**The prologue's edge into `main`'s body after the setup block**
(x86-64; the twin of `Spike/Lib/LowerA64/ProEdge2UNM.lean`): `ProEdge2`
(`Spike/Lib/LowerX64/ProgC2.lean`) at `scc_rt_main`'s call of `main` (the
interface's entry `uNM`, `Spike/Lib/Rt/X64MainS.lean`, at the arguments
`SetupArgs` of the setup call's post `SPostC`,
`Spike/Lib/LowerX64/SetupCall2.lean`), for a code block whose parameter is
the pair of the setup result's type `S` and the thread pointer, its body
lowered at its parameter's environment (`env2 d na`) and layouts. The
ghost is the entry control `cP` itself: the setup block's continuation
`let a = (r, me); tail main a`, whose two local steps reach `main`'s body.

- `spillsAt_rsOf`: every register of a spill has a cell;
- `paramSpillN_rsOf`: every parameter register of a prologue's spill has a
  cell;
- `argXs_getD`, `retXs_getD`: the runtime's `i`th argument and return
  registers are the lowering's;
- `proEdge2_ofUNM`: `ProEdge2` at `uNM`'s invariant at `SetupArgs` of
  `SPostC` (each entry control `cP` alone), its stack limit's facts from
  `uNM`'s own (as `proEdge2_ofUN0`): the saved `%rbp`, the return address
  and the `%fs` base from `uNM`, the setup result's words carried from the
  return registers to `main`'s parameter registers and the thread word from
  the `sw`th argument register (`wordsRep_mainArg`), the body's entry
  node's source facts by `entry2G_njB` after the continuation's two steps
  (`NJB.pre`), its slices at a ghost memory (`sliceL_ghost`), and the
  continuation itself placed (`slotRep_setupCont`).
-/
import Spike.Lib.LowerX64.ProEdge2Of
import Spike.Lib.LowerX64.LimOk0
import Spike.Lib.LowerX64.SetupCall2
import Spike.Lib.Src.Entry2M
import Spike.Lib.Src.SliceGhost
import Spike.Lib.Src.NJLS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (argRegs)
open Spike.Lib.LowerNode
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG limA)

/-- **Every register of a spill has a cell.** -/
theorem spillsAt_rsOf {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List ((Scc.IR.Reg × Reg64) × Nat)} {ps : List (Reg64 × Int64 × Nat)},
      SpillsAt fr l ps → ∀ q ∈ l, ∃ k, rsOf fr q.1.1 = some k
  | [], _, _, _, hq => by cases hq
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, ⟨hq, hl⟩, q', hq' => by
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact ⟨_, hq.2.1⟩
    · exact spillsAt_rsOf hl q' hq'

/-- **Every parameter register of a prologue's spill has a cell.** -/
theorem paramSpillN_rsOf {fr : Scc.Emit.X64.Frame} {ps : List (Reg64 × Int64 × Nat)} {prs : List Scc.IR.Reg}
    {zs : List Nat} (h : ParamSpillN fr ps prs zs) : ∀ q ∈ prs.zip argRegs, ∃ k, rsOf fr q.1 = some k := by
  intro q hq
  have hl : (prs.zip argRegs).length ≤ zs.length := by
    rw [List.length_zip, h.2.1]; omega
  obtain ⟨z, hz⟩ := mem_zip_of_le hl hq
  exact spillsAt_rsOf h.2.2 _ hz

/-- **The runtime's argument registers are the lowering's.** -/
theorem argXs_getD : ∀ k (hk : k < argRegs.length), Spike.Lib.X64.Rt.argXs.getD k .rdi = argRegs[k]
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | k + 6, hk => absurd hk (by simp [argRegs])

/-- **The runtime's return registers are the lowering's.** -/
theorem retXs_getD :
    ∀ k (hk : k < Scc.Emit.X64.retRegs.length), Spike.Lib.X64.Rt.retXs.getD k .rax = Scc.Emit.X64.retRegs[k]
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | k + 6, hk => absurd hk (by simp [Scc.Emit.X64.retRegs])

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}

/-- **The prologue's edge into `main`'s body after the setup block**
(`ProEdge2` at `uNM`'s invariant at the arguments `SetupArgs` of `SPostC`
at the setup result's type `S`, one entry control `cP`, any `J` within
it; the ghost's saved `%rbp`, return address and thread pointer, the ghost
control `cP`): for `main`'s code block `d` (`hfd`) whose parameter is the
pair of `S` and the thread pointer (`hd`), its `sw + 1` parameter
registers (`hna`, `sw < 6`), `S`'s layout no locative (`hnl`); the setup
call's caller at `setupTerm` (`hc0t`) binding `me` to one word `meW`
(`hme`), a number (`hmeN`) the ghost `x0` represents (`hmeV`); the room
`ZU` the frame (`hZU`); the limit word's facts `uNM` holds at its memory
side `ms0` and frame condition `F` carried to the edge's `ms1` and `F'`
(`hms`, `hFF`). -/
theorem proEdge2_ofUNM {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) {S : Ty} (hd : d.argTy = .prod S (.ptr .pub .void))
    (hfd : p.find? (·.name == "main") = some d) {sw : Nat} (hna : c.na = sw + 1) (hsw6 : sw < 6)
    (hnl : Scc.Lower.shapeOf S ≠ .loc)
    {c0 : Ctl} (hc0t : c0.term = Scc.Sem.SrcSem.setupTerm) {tm : Ty} {meW : TermRun.Word}
    (hme : TermRun.lookupE c0.env "me" = some (tm, [meW])) (hmeN : IsNum meW) {x0 : BitVec 64}
    (hmeV : Scc.Sem.ValRep lbl meW.val x0.toNat)
    {g : WcG} {lab : Label → Int64} {ms0 ms1 : MemSide isa} {F F' : MachineData → Prop} {fn : Label}
    {ZU : Int64} (hZU : ZU = Int64.ofInt c.fr.size)
    (hms : ∀ a Z, LimOk ms0 F a Z → LimOk ms1 F a Z) (hFF : ∀ m, F' m → F m)
    {cP : Ctl} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (Spike.Lib.X64.Rt.uNM lab ms0 F fn ZU
      (fun c rs => Spike.Lib.X64.Rt.SetupArgs (SPostC p lbl S c0) sw x0 c rs ∧ c = cP) g).J σ c') :
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
  have h6 : argRegs.length = 6 := by simp [argRegs]
  have h6r : Scc.Emit.X64.retRegs.length = 6 := by simp [Scc.Emit.X64.retRegs]
  obtain ⟨zs, hsp⟩ := c.hsp
  have hrs := paramSpillN_rsOf (paramSpillN_of_spills c.hf c.h1 hsp)
  refine proEdge2_ofSpills c hsp fun σ c' hJσ => ?_
  obtain ⟨⟨⟨hSA, hcP⟩, hfp, hra, hsp', htp⟩, hlim⟩ := hJ σ c' hJσ
  subst hcP
  have hl := (hms _ _ hlim).mono hFF
  have hl' := limOk_fsBase (σ := σ) htp hl
  rw [← hsp', hZU] at hl'
  refine ⟨⟨hl'.rt, hl'.mp, hl'.unmapped, hl'.room⟩, hfp, hra, htp, .refl _, fun sl hsl _ => ?_⟩
  -- the setup call's post: the continuation and the returned words
  obtain ⟨rs, hPC, hargs, hx0⟩ := hSA
  obtain ⟨cE, fr, cr, a, t, ws, hct, ⟨σr, hσr, hRJ, hRL⟩, hra', hev, hc'⟩ := hPC
  obtain ⟨x, f, a0, e, d0, t0, ws0, ht, -, -, -, rfl⟩ := hct
  rw [hc0t] at ht
  simp only [Scc.Sem.SrcSem.setupTerm] at ht
  cases ht
  subst hc'
  obtain ⟨a1, t1, ws1, ops, pls0, val0, hra1, -, hev1, hg0, hn0, hv0, hW0, -⟩ := hRJ
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
      Spike.Lib.Form.opdVal (rsOf c.fr) sl ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg)[k] =
        some (σ.regs.get64 (Spike.Lib.X64.Rt.argXs.getD k .rdi)).toNat := by
    intro k hk
    have hk' : k < (Spike.Lib.LowerShape.paramsR d c.na).length := by simpa using hk
    have hkr : k < argRegs.length := by rw [h6]; rw [hlenp] at hk; omega
    have hmem : ((Spike.Lib.LowerShape.paramsR d c.na)[k], argRegs[k]) ∈
        (Spike.Lib.LowerShape.paramsR d c.na).zip argRegs := by
      have hz : k < ((Spike.Lib.LowerShape.paramsR d c.na).zip argRegs).length := by
        rw [List.length_zip]; rw [h6] at hkr; omega
      have := List.getElem_mem hz
      rwa [List.getElem_zip] at this
    obtain ⟨j, hj⟩ := hrs _ hmem
    have hsj := hsl _ _ hmem j hj
    simp only [List.getElem_map, Spike.Lib.Form.opdVal, hj, Option.map_some, hsj, argXs_getD k hkr]
  have hops : ∀ k (hk : k < ops.length),
      k + 1 < ((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length →
      val0 ops[k] = some (σ.regs.get64 (Spike.Lib.X64.Rt.argXs.getD k .rdi)).toNat := by
    intro k hk hk1
    rw [hlenp] at hk1
    have hkr : k < Scc.Emit.X64.retRegs.length := by omega
    rw [hv0 k hk hkr, hargs k (by omega), retXs_getD k hkr, hσr]
  have hmeV' : Scc.Sem.ValRep lbl meW.val
      (σ.regs.get64 (Spike.Lib.X64.Rt.argXs.getD
        (((Spike.Lib.LowerShape.paramsR d c.na).map Scc.IR.Operand.reg).length - 1) .rdi)).toNat := by
    rw [hlenp, Nat.add_sub_cancel, hx0]
    exact hmeV
  obtain ⟨pu, o, hpls, hprsE, hwu, hwo⟩ := wordsRep_mainArg hd hcS hg hprs hg0 hcmp hers hops hW0 hmeV'
  -- `main`'s entry
  have hrep : Spike.Lib.Form.WordsRep lbl (Spike.Lib.Form.opdVal (rsOf c.fr) sl) (ws ++ [meW])
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

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofUNM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofUNM
