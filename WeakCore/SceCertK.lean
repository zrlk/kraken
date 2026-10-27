/-
# SceCertK — the kernel side of `sce --live-proof`'s certificates

The files `sce` writes under `root.cert/S/` import this module.  `start.lean` defines the scenario as data
(`jobK : Job`); `#sce_start` adds its start configuration as a literal (`c0K`), and the file proves by
`decide +kernel` that the start `Doc.spawnStart` computes from the program literal has `c0K`'s key (the probe).
`cert.lean` runs `#sce_cert`: the certificate (`TermLiveCert.certOf`, the untrusted generator, exactly as the
compiled run) as literals `nodeK0 …`, `certK`.  Nothing here is trusted: the chunk files and `main.lean` re-check
everything in the kernel (`TermLiveCertJoin`).  The `ToExpr` instances only produce terms.
-/
import WeakCore.TermLiveCertJoin
import WeakCore.TermLiveCertGen
import WeakCore.Doc

namespace SceCertK
open Lean Elab Command CoreLang CoreTerm TermRun

deriving instance ToExpr for CoreLang.RegAcc
deriving instance ToExpr for CoreLang.Mo
deriving instance ToExpr for CoreLang.Atom
deriving instance ToExpr for CoreLang.Rel2
deriving instance ToExpr for Clause
deriving instance ToExpr for Clause2
deriving instance ToExpr for CoreLang.Idx
deriving instance ToExpr for CoreLang.Wd
deriving instance ToExpr for CoreLang.Mode
deriving instance ToExpr for CoreLang.Cap
deriving instance ToExpr for CoreLang.Proto
deriving instance ToExpr for CoreLang.Proto2
deriving instance ToExpr for CoreLang.ECounter
deriving instance ToExpr for CoreLang.Kind
deriving instance ToExpr for CoreLang.Pred
deriving instance ToExpr for CoreTerm.FetchOp
deriving instance ToExpr for CoreTerm.ExtName
deriving instance ToExpr for CoreTerm.At
deriving instance ToExpr for CoreLang.CodeKind
deriving instance ToExpr for CoreLang.Opq
deriving instance ToExpr for CoreLang.Ty
deriving instance ToExpr for CoreTerm.Fence
deriving instance ToExpr for CoreTerm.BitOp
deriving instance ToExpr for CoreTerm.BitOp1
deriving instance ToExpr for CoreTerm.FOp
deriving instance ToExpr for CoreTerm.FCmp
deriving instance ToExpr for CoreTerm.FOp1
deriving instance ToExpr for CoreTerm.Op
deriving instance ToExpr for WeakMem.Address
deriving instance ToExpr for WeakMem.Val
deriving instance ToExpr for Promises.TVal
deriving instance ToExpr for TermRun.Env
deriving instance ToExpr for CoreTerm.Expr

/-- A coherence function as a finite table (the `ToExpr` of `VState`). -/
def cohL (l : List (WeakMem.Address × Nat)) (b : WeakMem.Address) : Nat :=
  match l.find? (fun p => decide (p.1 = b)) with
  | some p => p.2
  | none => 0

/-- The addresses the table covers (labels 0–63, offsets 0–7).  An entry outside it is lost, so the literal's key
differs and the kernel check fails: never a wrong PROVED line. -/
def cohGrid : List WeakMem.Address :=
  (List.range 64).flatMap fun l => (List.range 8).map fun o => ⟨l, o⟩

instance : ToExpr WeakMem.VState where
  toTypeExpr := mkConst ``WeakMem.VState
  toExpr v :=
    let l := cohGrid.filterMap fun b => if v.coh b = 0 then none else some (b, v.coh b)
    mkAppN (mkConst ``WeakMem.VState.mk)
      #[mkApp (mkConst ``cohL) (toExpr l), toExpr v.vRd, toExpr v.vWr, toExpr v.vCtrl, toExpr v.vPreBase,
        toExpr v.vRelSt, toExpr v.mine, toExpr v.fwd]

deriving instance ToExpr for Frame
deriving instance ToExpr for WeakMem.Msg
deriving instance ToExpr for TTh
deriving instance ToExpr for Event
deriving instance ToExpr for Cfg
deriving instance ToExpr for TermLiveCert.Just

/-- A scenario as `sce` ran it: the program, the setup call, the kids, the crash list, the budget. -/
structure Job where
  prog  : Prog
  f     : String
  argTy : Ty
  args  : List Nat
  kids  : List TermSpawn.Kid
  depth : Nat
  X     : List Nat
  fuel  : Nat

/-- The scenario start (`SceLive.runSpecT`'s, `Doc.spawnStart`'s). -/
def Job.start (j : Job) : Option Cfg := Doc.spawnStart j.prog j.f j.argTy j.args j.kids j.depth

def addDef (n : Name) (ty val : Lean.Expr) : CoreM Unit :=
  addDecl (.defnDecl (mkDefinitionValEx n [] ty val (.regular 0) .safe []))

unsafe def jobOf : CoreM Job := Lean.evalConst Job `jobK

/-- `c0K`: the start of `jobK`, as a literal. -/
elab "#sce_start" : command => do
  let j ← liftCoreM (unsafe jobOf)
  let some c := j.start | throwError "the scenario start does not run"
  liftCoreM <| addDef `c0K (mkConst ``Cfg) (toExpr c)

/-- `nodeK0 …` and `certK`: the certificate of `jobK`, as literals (the nodes canonical, as `check` reads them). -/
elab "#sce_cert" : command => do
  let j ← liftCoreM (unsafe jobOf)
  let some c := j.start | throwError "the scenario start does not run"
  let ct := TermLiveCert.certOf j.prog Promises.Knobs.all .arm j.X [] j.fuel c
  let mut names : Array Lean.Expr := #[]
  for v in [0:ct.nodes.size] do
    let n := Name.mkSimple s!"nodeK{v}"
    liftCoreM <| addDef n (mkConst ``Cfg) (toExpr (TermLiveCert.canon ct.nodes[v]!))
    names := names.push (mkConst n)
  let arr := mkAppN (mkConst ``List.toArray [Level.zero]) #[mkConst ``Cfg,
    names.foldr (fun e acc => mkAppN (mkConst ``List.cons [Level.zero]) #[mkConst ``Cfg, e, acc])
      (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Cfg))]
  let certE := mkAppN (mkConst ``TermLiveCert.Cert.mk) #[arr, toExpr ct.succ, toExpr ct.rank, toExpr ct.just,
    toExpr ct.envs]
  liftCoreM <| addDef `certK (mkConst ``TermLiveCert.Cert) certE

end SceCertK
