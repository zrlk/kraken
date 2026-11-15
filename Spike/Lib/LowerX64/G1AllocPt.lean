/-
**Every allocation's premises of `allocW2At_of`, for any `Accepted2`
program** (x86-64; the twin of `Spike/Lib/LowerA64/G1AllocPt.lean`): the
per-allocation bundle without the count's literal leaf, which the node gives
itself.

`AllocPtW.hleaf` (the count's layout in the literal walk a `.leaf`) is not a
consequence of `PtC2`: a `PtC2` constrains the walk's layouts `lits` only
where later constructs read them, so a count variable read by nothing after
the allocation may have any layout there. What `allocHq` uses it for, the
count's word a number, follows instead from the node: the count is one
operand of the grouped lowering environment, and `EnvLit` gives its layout
at a type compatible with it, so the layout's mask is `[true]`
(`litMask_one_of_atomV`).

- `allocHqE`: `allocHq` without `hleaf`;
- `allocW2_w2FullE`: `allocW2_w2Full` without `hleaf`;
- `AllocPtWk`: an allocation's walk fields (the units `hu`, the element's
  accesses `hacc`, no `main` return at no frame `hnr`);
- `AllocPtV`: `AllocPtW` without `hleaf` (the walk fields and the call's
  memory-side and allocator fields); `AllocPtW.toV`;
- `allocW2At_ofV`: `allocW2At_of` from `AllocPtV` at every allocation;
- `AllocPtStmt`: the walk fields at every allocation of every compiled
  block of an `Accepted2` program, at its resumption facts (`PtC2` at the
  theorem's immediates `imms2Me` and the block's tails `TailAt2`);
  `allocPt_of_accepted2` proves it.
-/
import Spike.Lib.LowerX64.AllocW2AtOf
import Spike.Lib.Src.G1LeafMask
import Spike.Lib.Src.Walk2Facts
import Spike.Lib.Src.ImmsMe
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.Src.G1NewBufK

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW At FStable CKept Abs AS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK CallerCells)
open Spike.Lib.X64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.X64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.AllocReach (Reach IN)

/-! ## The call's arguments without the count's leaf -/

section Hq

open Spike.Lib.LowerNode (GrpL InLits EnvLit IsNum sevalAt_ofEnv2G_one)
open Scc.Lower (LitV litAt)
open Scc.Lower.Inv (atomV)

/-- **The call's arguments at the call's source relation**, as `allocHq`
with the count's word a number read off the node: its layout's mask is
`[true]` (`litMask_one_of_atomV`: the count is one operand `kv` of the
grouped environment, and `EnvLit` puts its layout at a type equal to the
lowering's up to `eraseLen`, `compat_of_eraseLen`). -/
theorem allocHqE {ms : MemSide isa} {L : Label → Int64} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {fr : Scc.Emit.X64.Frame} {R : Region} {fp ra : BitVec 64} {tp : UInt64}
    {c0 : Ctl} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {lits : List (String × LitV)}
    {cs bufs : List (String × Nat)} {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {tk : Ty}
    (hg : GrpL env) (hcn : atomV env cn = some (tk, [.imm kv])) (hsc : InLits lits cn)
    (hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u = some (ms.units kv.toNat τ))
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us)
    (hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h → CallMsOK ms L q) :
    ∀ σ c, nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
      (.imm kv) u σ c → ∃ q : Call, q.OK ms L ∧ q.c0 = c ∧
        σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms := by
  rintro σ c ⟨h0, h1, h2, -, -, -, -, L', sm, B, hj, hl, -⟩
  have hs := sevalAt_ofEnv2G_one hg hcn
  obtain ⟨t', ws, hev, het, hwr⟩ := hj.2.2.evalAt (fun _ => rfl) hs
  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
    match ws, hwr with
    | [w], _ => exact ⟨w, rfl⟩
  obtain ⟨⟨v, hv, hvr⟩, -⟩ := hwr
  simp only [Spike.Lib.Form.opdVal_imm, Option.some.injEq] at hv
  subst hv
  obtain ⟨hcp, hnl⟩ := EnvLit.evalAt hl hsc hs hev
  have hmask : Spike.Lib.LowerNode.litMask (litAt lits cn) = [true] :=
    Spike.Lib.LowerNode.litMask_one_of_atomV hg hcn
      (by rw [← Spike.Lib.LowerNode.compat_of_eraseLen het]; exact hcp)
  obtain ⟨n, hn, -⟩ : IsNum w := hnl 0 w rfl (by rw [hmask]; rfl)
  rw [hn] at hvr
  obtain ⟨-, rfl⟩ := hvr
  refine ⟨⟨c, x, cn, τ, e, t', [w], kv.toNat, BitVec.ofNat 64 h, 0, 0⟩,
    Call.OK.ofMs hj.1 hev (by simp [TermRun.numOf, hn]) hj.2.1 (UInt64.toNat_lt _) hacc (hms _ rfl rfl rfl),
    rfl, ?_, ?_, ?_⟩
  · refine BitVec.eq_of_toNat_eq ?_
    simp only [Scc.Lower.imm, Spike.Lib.Form.opdVal_imm, Option.some.injEq] at h0
    rw [show σ.regs.rdi.toBitVec = σ.regs.get64 .rdi from rfl, ← h0]; simp
  · refine BitVec.eq_of_toNat_eq ?_
    simp only [Spike.Lib.Form.opdVal_imm, Option.some.injEq] at h1
    rw [show σ.regs.rsi.toBitVec = σ.regs.get64 .rsi from rfl, ← h1]; simp [Spike.Lib.X64.Alloc.Call.k]
  · refine BitVec.eq_of_toNat_eq ?_
    rw [hu, Option.some.injEq] at h2
    simp only [Spike.Lib.X64.Alloc.Call.u, BitVec.toNat_ofNat]
    have hlt : ms.units kv.toNat τ < 2 ^ 64 := h2 ▸ BitVec.isLt _
    rw [show σ.regs.rdx.toBitVec = σ.regs.get64 .rdx from rfl, ← h2, Nat.mod_eq_of_lt hlt]

end Hq

/-! ## The full premise without the count's leaf -/

section Full

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

/-- **`AllocW2` at `W₀ := W2`** for one allocation, as `allocW2_w2Full`
without the count's leaf `hleaf` (the call's arguments by `allocHqE`). -/
theorem allocW2_w2FullE {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hprA : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (h16 : fr.size % 16 = 0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 + -160 - 32) (hhi : 16 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ra0 : Int64} (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String} {cn : At} {τ : Ty} {e : Expr}
    {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {tk : Ty} {pc : Int64}
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e),
      (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) y).isSome)
    (hlb : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (himm : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (hc0 : FrOk2 c0 fs) (he2 : Scc.Lower.elem2 τ = true) (hfr : Spike.Lib.LowerNode.Fresh env n)
    (hnr : fs = [] → ∀ a, e ≠ .ret a)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlbe : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hg : Spike.Lib.LowerNode.GrpL env) (hcn : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hsc : Spike.Lib.LowerNode.InLits lits cn)
    (hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u =
      some ((msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).units kv.toNat τ))
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us)
    (hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h →
      CallMsOK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label q)
    (hmem : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hxa : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : {q : Call // q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label R fr.size
        (nbJc (_root_.Executable.labels exe).label
          [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum) (oB fr)
          (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
            (.imm kv) u))
        q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F'
        (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q.1 l b w)
        s c → TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).xa l b w s c)
    (hxaF : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
          (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧
            AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
              (_root_.Executable.labels exe).label R fr.size
              (nbJc (_root_.Executable.labels exe).label
                [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum)
                (oB fr)
                (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
                  (.imm kv) u)) q m)
          (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hstub : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R fr.size
        (fun σC => nbJc (_root_.Executable.labels exe).label
          [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum) (oB fr)
          (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
            (.imm kv) u) σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-(fr.size : Int) - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 8 + -160, []⟩ m0 σC) c0')
    (hsz : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).lo old →
      b = ar.heap + 16 * old + ar.off q.n q.τ → old + ar.units q.n q.τ ≤ ar.cells → q.n ≤ lsize l) :
    AllocW2 (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0)
      (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs) (TakeK a rS)
      exe endPc R F (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) lbl lsize tp fr pc
      (Scc.Lower.Inv.regName x n) h kv u
      (laneJ p lbl lsize Λ.imms fr fp ra tp c0 pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
        u) := by
  have hlab := hI.labOk
  subst hlab
  have h8 : (fr.size : Int) % 8 = 0 := by omega
  have hlo1 : R.lo ≤ -(fr.size : Int) := by omega
  intro lw off zs zc z k hlw hoff hz L pcB pcR B Jc hCd hBl hCd'
  have hraAbP : pcB + Int64.ofNat zc ∉ abPcs (_root_.Executable.labels exe).label :=
    notAbPc_of_posOff hI.lays hpr hprA (posOff_start hCd'.1 (by simp))
  have hraP : ph (pcB + Int64.ofNat zc).toBitVec.toNat =
      ph ((_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.fnL).toBitVec.toNat :=
    (blC2_hra hBl.1).symm
  refine ⟨allocArgs_w2 hI hpr hprA hf h1 hR hR8 hlo1 hhi hl hh hsub hfit hFO hFS hp hrs hfp
      (fun _ h => by cases h) hc0 hlw hz hCd,
    allocBl_w2 hI hpr hprA hA h8 hR hR8 (by omega) hhi hl hh hsub hfit hFO hFS hp hBl.1.1 hrs hfp
      (fun _ h => by cases h) hc0 htot hlb himm,
    allocHqE hg hcn hsc hu hacc hms, by cases ab <;> exact hmem, hxa lw zs zc k hlw hz hCd hBl,
    allocW2_field hI hA hph habk hprA hown hf h16 hR hR8 hl hh hlo (by omega) hFS hsub hfit hFO hp hJ hRe hfp
      htot hlb himm hc0 hraP hraAbP hmem hno hlt h64 (hxaF lw zs zc k hlw hz hCd hBl)
      (hstub lw zs zc k hlw hz hCd hBl), by cases ab <;> exact hsz,
    fun lbl' lsize' hl' _ => ?_⟩
  exact allocStore_w2 hI hpr hprA hf h1 hR hR8
    (by simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega) hhi hl hh
    hsub hfit hFO hFS hp hrs (fun s hs => (hfp s hs).imp fun _ hB => framesPlacedInI_mono_lbl hl' hB) he2 hfr hl'
    hnr hc0 hoff hCd' hIt hIc hlbe

end Full

/-! ## The per-allocation bundle without the count's leaf -/

/-- **An allocation's walk fields** at the units `U` (the memory side's), the
frame `fr`, the frames `fs`, the continuation `e`, the element `τ`, the
count `kv` and the units operand `u`: `u` the units of `kv` elements
(`hu`), the element's accesses (`hacc`), and no `main` return at no frame
(`hnr`). -/
structure AllocPtWk (U : Nat → Ty → Nat) (fr : Scc.Emit.X64.Frame) (fs : List TermRun.Frame) (e : Expr) (τ : Ty)
    (kv : UInt64) (u : Scc.IR.Operand) : Prop where
  hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u = some (U kv.toNat τ)
  hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us
  hnr : fs = [] → ∀ a, e ≠ .ret a

section Of

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

set_option hygiene false in
/-- The rows' memory side at the placement `lbl`, `lsize` and frames `fs`
over `IN … J` (`allocW2_w2Full`'s). -/
local notation "MS" J:max => msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs

set_option hygiene false in
/-- The allocation's continuation at the `callq` at `pcB` of size `zc`. -/
local notation "NJ" pcB:max zc:max => nbJc (_root_.Executable.labels exe).label
  [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
  (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u)

/-- **One allocation's premises of `allocW2_w2FullE`**: `AllocPtW` without
the count's leaf, its walk fields as `AllocPtWk` at the rows' units. -/
structure AllocPtV (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (rS : Range) (Tk : State → Prop) (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (S0 : FragS isa)
    (Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (J : InvS) (ab : Option (State → Prop))
    (Dt : State → Prop) (lab : Label → Int64) (a : Int64) (lbl : Lbl) (lsize : Lsize) (fs : List TermRun.Frame)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (pc : Int64) (x : String) (cn : At) (τ : Ty) (e : Expr)
    (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (h : Nat)
    (kv : UInt64) (u : Scc.IR.Operand) : Prop extends AllocPtWk (MS J).units fr fs e τ kv u where
  hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h →
    CallMsOK (MS J) (_root_.Executable.labels exe).label q
  hxa : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : {q : Call // q.OK (MS J) (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (MS J) (_root_.Executable.labels exe).label R fr.size
        (NJ (pc + Int64.ofNat zs.sum) zc) q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F'
        (Spike.Lib.X64.Alloc.Ea (MS J) q.1 l b w) s c → TP tp s → (MS J).xa l b w s c
  hxaF : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
          (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧
            AllocCtx (MS J) (_root_.Executable.labels exe).label R fr.size (NJ (pc + Int64.ofNat zs.sum) zc) q m)
          (Spike.Lib.X64.Alloc.Ea (MS J') q l b w) s c →
        TP tp s → (MS J').xa l b w s c
  hstub : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label (MS J') q lbl R fr.size
        (fun σC => (NJ (pc + Int64.ofNat zs.sum) zc) σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (MS J') exe endPc
        (R.callee (-(fr.size : Int) - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 8 + -160, []⟩ m0 σC) c0'

omit [Kraken.Executable.ValidLayout exe] in
/-- `AllocPtW` gives `AllocPtV` (forgetting the count's leaf). -/
theorem AllocPtW.toV {Λ : Scc.Sem.Layout} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {rS : Range} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa}
    {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {J : InvS} {ab : Option (State → Prop)}
    {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {fr : Scc.Emit.X64.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop} {fp ra : BitVec 64}
    {tp : UInt64} {c0 : Ctl} {pc : Int64} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {h : Nat} {kv : UInt64}
    {u : Scc.IR.Operand}
    (P : AllocPtW Λ μ p rd G own rS Tk ar L0 ls0 S0 Es J ab Dt lab a lbl lsize fs exe endPc R F fr Cd Bl fp ra tp c0
      pc x cn τ e env lits cs bufs h kv u) :
    AllocPtV Λ μ p rd G own rS Tk ar L0 ls0 S0 Es J ab Dt lab a lbl lsize fs exe endPc R F fr Cd Bl fp ra tp c0
      pc x cn τ e env lits cs bufs h kv u :=
  { hu := P.hu, hacc := P.hacc, hnr := P.hnr, hms := P.hms, hxa := P.hxa, hxaF := P.hxaF, hstub := P.hstub }

/-- **`AllocW2At` at `W₀ := W2`** for every allocation of a body, as
`allocW2At_of` from `AllocPtV` (no count's leaf) at each allocation
(`allocW2_w2FullE`). -/
theorem allocW2At_ofV {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hprA : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (h16 : fr.size % 16 = 0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 + -160 - 32) (hhi : 16 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ra0 : Int64} (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    (hmem : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (MS J) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (MS J) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hsz : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      (MS J).lo old → b = ar.heap + 16 * old + ar.off q.n q.τ → old + ar.units q.n q.τ ≤ ar.cells → q.n ≤ lsize l)
    {lcx : Scc.Lower.Ctx} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {T : Expr → Prop}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs)
    (hpt : ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
      (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
      (tk : Ty) (kv : UInt64) (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) →
      Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
      Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) → Scc.Obj.header0 lcx.obj .array en em = some h →
      PtC2 lcx fr (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0) (_root_.Executable.labels exe).label
        Λ.imms T Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e) →
      AllocPtV Λ μ p rd G own rS Tk ar L0 ls0 S0 Es J ab Dt lab a lbl lsize fs exe endPc R F fr
        (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0) fp ra tp c0 pc x cn τ e env lits cs bufs h kv (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)) :
    AllocW2At p lbl lsize lcx fr (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0)
      (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs) (TakeK a rS)
      exe endPc R F (MS J) fp ra tp G0 Λ.imms T Lk := by
  intro c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc
  obtain ⟨htot, hlb, himm, hg, hsc, hIt, hIc, hlbe⟩ := PtC2.newBufW hpc
  have P := hpt c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc
  exact allocW2_w2FullE hI hA hph habk hpr hprA hown hf h1 h16 hR hR8 hl hh hlo hhi hFS hsub hfit hFO hp hJ hRe hfp
    hrs htot hlb himm (hG0F c0 hc0) (hTn x cn τ e hT) hfr P.hnr hIt hIc hlbe hg hat hsc P.hu P.hacc P.hms
    hmem hno hlt h64 P.hxa P.hxaF P.hstub hsz

end Of

/-! ## The walk fields at any `Accepted2` program -/

/-- **The walk fields at every allocation of an `Accepted2` program**: for
every compiled block `j` of an `Accepted2` program `p`, at the resumption
facts of any allocation `let x = newBuf cn τ in e` of its body (`PtC2` at
the theorem's immediates `imms2Me Λ p` and the block's tails `TailAt2 p j`,
any code `Cd`, `Bl`, labels `lab` and walk fact `Lk`), with the count `cn`
the immediate `kv` and the element counts `en`, `em`, at any frames `fs`
other than none (the setup block's call): the walk fields `AllocPtWk` at the
units of the runtime's arena `arOf Λ'` (any layout `Λ'`) and the units
operand `unitsOf … kv`. -/
def AllocPtStmt : Prop :=
  ∀ (Λ Λ' : Scc.Sem.Layout) (p : Prog), Scc.Lower.Accepted2 p = true →
  ∀ (j : Nat) (d : Decl), (Spike.Lib.LowerNode.compiled2 p)[j]? = some d →
  ∀ (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (lab : Label → Int64)
    (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (kk : Nat) (pc : Int64)
    (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (x : String) (cn : At) (τ : Ty) (e : Expr) (tk : Ty) (kv : UInt64) (en em : Nat) (fs : List TermRun.Frame),
    Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
    Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) →
    PtC2 lcx fr Cd Bl lab (Spike.Lib.LowerNode.imms2Me Λ p) (Spike.Lib.LowerNode.TailAt2 p j) Lk kk pc env n lits
      cs bufs (.let_ x (.newBuf cn τ) e) →
    fs ≠ [] →
    AllocPtWk (Spike.Lib.X64.Rt.arOf Λ').units fr fs e τ kv
      (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)

/-- **A one-word element's words and accesses**: an `elem2` type (`Int`,
`fix`, `lanes`) is one word (`Frontend.words`) with one access word. -/
theorem elem2_words_accs {τ : Ty} (h : Scc.Lower.elem2 τ = true) :
    Scc.Frontend.words τ = some 1 ∧
      ∃ us, TermRun.accs (TermRun.close [] τ) = some us ∧ TermRun.nWords us = 1 := by
  cases τ <;> simp [Scc.Lower.elem2] at h <;> exact ⟨rfl, _, rfl, rfl⟩

/-- **The rows' memory side's units are the arena's** (`msOfAX` at either
abort). -/
theorem msOfAX_units {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl}
    {lsize : Lsize} {fs : List TermRun.Frame} :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).units = ar.units := by
  cases ab <;> rfl

/-- **`AllocPtWk` at the rows' memory side** from `AllocPtWk` at the arena's
units (`msOfAX_units`). -/
theorem AllocPtWk.ofAr {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl}
    {lsize : Lsize} {fs : List TermRun.Frame} {fr : Scc.Emit.X64.Frame} {e : Expr} {τ : Ty} {kv : UInt64}
    {u : Scc.IR.Operand} (W : AllocPtWk ar.units fr fs e τ kv u) :
    AllocPtWk (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).units fr fs e τ kv u := by
  rw [msOfAX_units]; exact W

/-- **The walk fields at every allocation of an `Accepted2` program**
(`AllocPtStmt`): the count `kv` is between `1` and `2 ^ 28`
(`newBufKv_of_accepted2`, from the head's immediates `ImmIn` at `imms2Me`
and the block's tail `TailAt2`), the element one word with one access
(`newBufK_of_accepted2`'s `elem2`, `elem2_words_accs`), so the units operand
is the immediate `kv + 1`, the arena's units of `kv` one-word elements
(`Arena.ofWords`, below `2 ^ 63`); no `main` return at frames other than
none. -/
theorem allocPt_of_accepted2 : AllocPtStmt := by
  intro Λ Λ' p hp j d hd lcx fr Cd Bl lab Lk kk pc env n lits cs bufs x cn τ e tk kv en em fs hat _hco hpt hfs
  obtain ⟨-, -, himm, hg, -, -, -, -⟩ := PtC2.newBufW hpt
  have hT : Spike.Lib.LowerNode.TailAt2 p j (.let_ x (.newBuf cn τ) e) := by
    obtain ⟨-, -, -, -, -, -, hWs, -, -, -⟩ := hpt
    exact (Spike.Lib.LowerNode.walk2_head hWs).2.1
  have he2 := (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  obtain ⟨hk1, hk2⟩ := Spike.Lib.LowerNode.newBufKv_of_accepted2 hp hd hT hg himm hat
  obtain ⟨hw, us, hus, hn⟩ := elem2_words_accs he2
  refine ⟨fun sl => ?_, ⟨us, hus⟩, fun h => absurd h hfs⟩
  have hu : (Spike.Lib.X64.Rt.arOf Λ').units kv.toNat τ = kv.toNat + 1 := by
    simp only [Spike.Lib.X64.Rt.arOf, Spike.Lib.Arena.ofWords, hus, hn]
    split <;> omega
  rw [hu, hw]
  have h64 : kv.toNat + 1 < 2 ^ 64 := by omega
  simp [Spike.Lib.LowerShape.unitsOf, Spike.Lib.Form.opdVal, Scc.Lower.imm, Nat.mod_eq_of_lt h64]

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.allocHqE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocHqE

/-- info: 'Spike.Lib.LowerX64.allocW2_w2FullE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2_w2FullE

/-- info: 'Spike.Lib.LowerX64.allocW2At_ofV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2At_ofV

/-- info: 'Spike.Lib.LowerX64.allocPt_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocPt_of_accepted2
