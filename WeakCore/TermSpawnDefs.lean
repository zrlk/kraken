import WeakCore.TermWrSiteA
import WeakCore.TermMain
/-!
# TermSpawnDefs — definitions of the spawn headline (the frozen TermSpawnStmt minus its two theorems)
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The conclusion of `machine_tokens_mainF` at `c` (verbatim). -/
def Headline (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (c : Cfg) : Prop :=
  ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
    (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
    ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
      MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)

/-- **A start state**: the invariant, no promise, `ViewInv`, promise well-formedness. -/
def StartOK (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  SysInvNx p k arch Init MintOK c0 ∧ AllNoProm c0 ∧ TermViewInv.ViewInv c0 ∧ (c0.ths.size = 0 ∨ TermFul.PWFall c0)

theorem startOK_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h0 : InitOK p k arch Init MintOK c0) : StartOK p k arch Init MintOK c0 := by
  have hpw := pwf0_of_initOK h0
  obtain ⟨⟨Eg0, T0, H0, S0, cr0, db0, hw0, hr0, hof0, hu0, hoc0, hbx0, hzw0, hko0, hop0, hni0, hsw0, hlb0, hly0, hmem0, hvi, hvl0, htd0⟩, hn0, hcc, hty0⟩ := h0
  refine ⟨⟨_, _, _, _, _, _, TermMain.SysInvW.toN hw0 hn0 hr0 hof0 hu0 hoc0 hbx0 hko0 hop0 hni0 (TermUndefLow.undefLow_nil hmem0)
    (TermZwIni.zwIni_none hzw0) (TermPredHold.predHold_none hzw0) hvl0
      (fun t m cl hm _ => by rw [hmem0] at hm; simp at hm) hmem0 hzw0 hlb0 hly0 hcc hsw0
      (fun i th h l hl => by rw [htd0 i th h] at hl; cases hl) hty0⟩, hn0, hvi, hpw⟩

theorem toObligationsS {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOK p k arch Init (fun _ => True) c0) :
    Obligations p k arch (fun _ _ => False) Init (fun _ => True) c0 TermPlantF.plantOf TermPlantF.plantN := by
  exact O.toObligationsC hk hS.2.1 hS.2.2.1
    (TermBal.promNodupR_of (fun _ _ hf _ => hf.elim) (fun n th h => by rw [hS.2.1 n th h]; exact List.nodup_nil) hS.2.2.2)


/-- **Headline 1 from any start state.** -/
theorem machine_tokens_mainS {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    Headline p k arch Init c := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN⟩ := sysInv_run (toObligationsS O hk hS) hS.1 hr
  refine ⟨Eg, Tot, HP, HS, cr, db, hN, hN.knet,
    fun hn => ⟨hN.toW hn, fun i j n hi hj h1 h2 => (hN.toW hn).tokUniq hi hj h1 h2⟩, fun i th hth => ?_⟩
  obtain ⟨S, ρ, η, cx, Rf, Rs, hCE, -, hE, hT, -, hFI, hsum, -, hm, -⟩ := (hN.thr i th hth).env hN.clo
  exact ⟨S, ρ, η, cx, Rf, Rs, hCE, hE, hT.1, hFI, hsum, hm⟩

/-- The existing final is a corollary (statement level). -/
theorem machine_tokens_mainF_of_S {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    Headline p k arch Init c :=
  machine_tokens_mainS O hk (startOK_of_initOK h0) hr

/-- `Headline` is exactly `machine_tokens_mainF`'s conclusion. -/
example {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    Headline p k arch Init c := machine_tokens_mainF O hk h0 hr

/-! ## The barrier spawn -/

/-- A spawned thread: `tail f [] (v "a") ts`, `a : ty` bound to (the setup result, if `useRes`) ++ constants. -/
structure Kid where
  f : String
  ts : List Ty
  ty : Ty
  useRes : Bool
  vals : List WeakMem.Val

/-- Kid `kd`'s start thread at the setup thread's views `vs`; every argument word bumped to `vs.vRelSt` (barrier). -/
def kidTh (vs : VState) (res : List Word) (kd : Kid) : TTh where
  term := .tail kd.f [] (.var "a") kd.ts
  env := [("a", kd.ty, ((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW vs.vRelSt))]
  vs := vs

/-- **The spawn reshape**: the setup thread `0` of `cs` ends; the kids start on its memory with its views. -/
def spawnS (cs : Cfg) (res : List Word) (kids : List Kid) : Cfg :=
  match cs.ths[0]? with
  | none => cs
  | some th =>
    { mem := cs.mem
      pairs := cs.pairs
      ths := (kids.map (kidTh th.vs res)).toArray
      lbase := cs.lbase + cs.n * th.nalloc
      boxFence := cs.boxFence }

/-- Constants `vals` are a resource-free laid-out value of `t` (as `TermInit.entryOK_of`'s `hv`, `hlay`). -/
def ConstVal (p : Prog) (t : Ty) (vals : List WeakMem.Val) : Prop :=
  VRR (fun _ => 0) (Cut (TermInit.Eg0 p) 0 TermInit.S0) t (shp t) (vals.map cst) .zero ∧ Lay [] t t (vals.map cst)

/-- What each kid needs: a copyable, region-free argument type, a checked entry, and an argument shape. -/
def KidOK (p : Prog) (rt : Ty) (kd : Kid) : Prop :=
  Ty.affine kd.ty = false ∧ tb 0 kd.ty = true ∧ TermScope.drf kd.ty = true ∧ kd.ts.all TermScope.drf = true ∧
  kd.ts.all TermScope.argOK = true ∧ TermScope.wrapOK kd.ty = true ∧
  (∃ r, check p { vars := [("a", kd.ty, true)], ret := r } (.tail kd.f [] (.var "a") kd.ts) = .ok () ∧
    TvOK { vars := [("a", kd.ty, true)], ret := r }) ∧
  ((kd.useRes = true ∧ ((kd.vals = [] ∧ kd.ty = rt) ∨ ∃ τ, kd.ty = .prod rt τ ∧ ConstVal p τ kd.vals)) ∨
    (kd.useRes = false ∧ ConstVal p kd.ty kd.vals))

/-- The phantom return frame: binds the setup's result as `r` at `R0`, packs it at `R0` (fixing its static
type) and returns it. -/
def f0 (R0 : Ty) : Frame :=
  ⟨"r", .let_ "q" (.packT (.var "r") .unit (.tex Kind.top (R0.shiftT 0))) (.ret (.var "q")), [], [], R0⟩

/-- The phantom start: thread `0` gets `f0 R0` at the bottom of its stack. -/
def phant (R0 : Ty) (c : Cfg) : Cfg :=
  { c with ths := c.ths.modify 0 (fun th => { th with stack := th.stack ++ [f0 R0] }) }

#print axioms TermSpawn.toObligationsS
#print axioms TermSpawn.machine_tokens_mainS
#print axioms TermSpawn.startOK_of_initOK
